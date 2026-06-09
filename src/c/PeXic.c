#include <pebble.h>
#include <time.h> 

// --- CONFIGURATION ---
#define GRID_COLS 6
#define GRID_ROWS 7
#define PIECE_SILVER_PEARL 6

#define SAVE_KEY 1
#define SAVE_VERSION 1

// --- STRUCTS & TYPES ---
typedef struct { int q; int r; } HexCoord;
typedef struct { int pixel_x; int pixel_y; HexCoord hex_a; HexCoord hex_b; HexCoord hex_c; } CursorPos;

// Save State Struct (Packed for flash memory efficiency)
typedef struct {
  uint8_t version;
  uint8_t board[GRID_COLS][GRID_ROWS];
  int8_t bomb_timers[GRID_COLS][GRID_ROWS];
  int score;
  bool game_over;
  bool used_retry;
} __attribute__((__packed__)) SaveState;

// --- GLOBALS ---
static Window *s_splash_window;
static Layer *s_splash_layer;
static int s_splash_selection = 0; // 0 = Play, 1 = Exit

static Window *s_game_window;
static Layer *s_grid_layer;

static GPath *s_hex_path;

static uint8_t s_board[GRID_COLS][GRID_ROWS];
static int8_t s_bomb_timers[GRID_COLS][GRID_ROWS];
static bool s_game_over = false;
static bool s_used_retry = false; 
static bool s_is_cascading = false; 
static int s_score = 0; 

// Timer Tracking
static AppTimer *s_cascade_timer = NULL;

// --- EXCLUSIVE HIGH-RES LAYOUT OFFSETS ---
#if defined(PBL_ROUND)
// Pebble Round 2 (Gabbro) - 260x260
static const int s_hex_w = 32;
static const int s_hex_h = 36;
static const int s_x_off = 42;
static const int s_y_off = 54;
static const int s_destruct_max = 18;
static const GPathInfo HEX_PATH_INFO = {
  .num_points = 6,
  .points = (GPoint []) { {0, -18}, {16, -9}, {16, 9}, {0, 18}, {-16, 9}, {-16, -9} }
};
#else
// Pebble Time 2 (Emery) - 200x228
static const int s_hex_w = 30;
static const int s_hex_h = 34;
static const int s_x_off = 17;
static const int s_y_off = 49;
static const int s_destruct_max = 16;
static const GPathInfo HEX_PATH_INFO = {
  .num_points = 6,
  .points = (GPoint []) { {0, -17}, {15, -8}, {15, 8}, {0, 17}, {-15, 8}, {-15, -8} }
};
#endif

#define MAX_CURSORS 100 
static CursorPos s_cursors[MAX_CURSORS];
static int s_cursor_count = 0;
static int s_active_cursor_idx = 0;

// Rotation Animation State
static Animation *s_rotation_anim = NULL;
static bool s_is_animating = false;
static bool s_anim_clockwise = true;
static int32_t s_current_anim_angle = 0;
static int32_t s_current_anim_pop = 0; 

// Destruction Animation State
static Animation *s_destruct_anim = NULL;
static bool s_is_destructing = false;
static int32_t s_current_destruct_radius = 16;
static bool s_marked_for_deletion[GRID_COLS][GRID_ROWS];
static bool s_spawn_pearl[GRID_COLS][GRID_ROWS];

static const int EVEN_R_OFFSETS[6][2] = {{-1, -1}, {0, -1}, {-1, 0}, {1, 0}, {-1, 1}, {0, 1}};
static const int ODD_R_OFFSETS[6][2]  = {{0, -1}, {1, -1}, {-1, 0}, {1, 0}, {0, 1}, {1, 1}};

// --- FORWARD DECLARATIONS ---
static void trigger_cascade_check_callback(void *data);
static void detect_matches_and_cascade();
static bool has_valid_moves();
static bool board_has_any_match(uint8_t sim_board[GRID_COLS][GRID_ROWS]);
static void game_select_click_handler(ClickRecognizerRef recognizer, void *context);
static void game_back_click_handler(ClickRecognizerRef recognizer, void *context);

// --- UTILITIES & GRAPHICS ---
static bool is_valid_coord(int q, int r) {
  return (q >= 0 && q < GRID_COLS && r >= 0 && r < GRID_ROWS);
}

static int distance_squared(int x1, int y1, int x2, int y2) {
  int dx = x1 - x2; int dy = y1 - y2; return (dx * dx) + (dy * dy);
}

static GColor get_piece_color(uint8_t val) {
  switch(val) {
    case 1: return GColorRed;
    case 2: return GColorMalachite;
    case 3: return GColorElectricBlue;
    case 4: return GColorYellow;
    case 5: return GColorMagenta;
    case PIECE_SILVER_PEARL: return GColorLightGray;
    default: return GColorBlack;
  }
}

static GColor get_dummy_color(int q, int r) {
  int val = ((q * 17) + (r * 31)); 
  if (val < 0) val = -val;
  switch(val % 5) {
    case 0: return GColorDarkCandyAppleRed;
    case 1: return GColorIslamicGreen;
    case 2: return GColorDukeBlue;
    case 3: return GColorWindsorTan;
    case 4: return GColorImperialPurple;
    default: return GColorDarkGray;
  }
}

static void draw_hex(GContext *ctx, int x, int y, uint8_t val) {
  gpath_move_to(s_hex_path, GPoint(x, y));
  graphics_context_set_fill_color(ctx, get_piece_color(val)); 
  gpath_draw_filled(ctx, s_hex_path);
  graphics_context_set_stroke_color(ctx, GColorWhite);
  gpath_draw_outline(ctx, s_hex_path);
  if (val == PIECE_SILVER_PEARL) graphics_fill_circle(ctx, GPoint(x, y), 4);
}

// --- INITIALIZATION ---
static void init_cursors() {
  s_cursor_count = 0;
  for(int r = 0; r < GRID_ROWS - 1; r++) {
    for(int q = 0; q < GRID_COLS; q++) {
      if (r % 2 == 0) {
        if (q + 1 < GRID_COLS && r + 1 < GRID_ROWS) {
          s_cursors[s_cursor_count].hex_a = (HexCoord){q, r}; s_cursors[s_cursor_count].hex_b = (HexCoord){q+1, r}; s_cursors[s_cursor_count].hex_c = (HexCoord){q, r+1};
          s_cursor_count++;
        }
        if (q + 1 < GRID_COLS && r + 1 < GRID_ROWS) {
          s_cursors[s_cursor_count].hex_a = (HexCoord){q+1, r}; s_cursors[s_cursor_count].hex_b = (HexCoord){q+1, r+1}; s_cursors[s_cursor_count].hex_c = (HexCoord){q, r+1};
          s_cursor_count++;
        }
      } else {
        if (q + 1 < GRID_COLS && r + 1 < GRID_ROWS) {
          s_cursors[s_cursor_count].hex_a = (HexCoord){q, r}; s_cursors[s_cursor_count].hex_b = (HexCoord){q+1, r}; s_cursors[s_cursor_count].hex_c = (HexCoord){q+1, r+1};
          s_cursor_count++;
        }
        if (q + 1 < GRID_COLS && r + 1 < GRID_ROWS) {
          s_cursors[s_cursor_count].hex_a = (HexCoord){q, r}; s_cursors[s_cursor_count].hex_b = (HexCoord){q+1, r+1}; s_cursors[s_cursor_count].hex_c = (HexCoord){q, r+1};
          s_cursor_count++;
        }
      }
    }
  }
  
  for (int i = 0; i < s_cursor_count; i++) {
    CursorPos *c = &s_cursors[i];
    int ax = s_x_off + c->hex_a.q * s_hex_w + (c->hex_a.r % 2) * (s_hex_w / 2);
    int ay = s_y_off + c->hex_a.r * (s_hex_h * 3 / 4);
    int bx = s_x_off + c->hex_b.q * s_hex_w + (c->hex_b.r % 2) * (s_hex_w / 2);
    int by = s_y_off + c->hex_b.r * (s_hex_h * 3 / 4);
    int cx = s_x_off + c->hex_c.q * s_hex_w + (c->hex_c.r % 2) * (s_hex_w / 2);
    int cy = s_y_off + c->hex_c.r * (s_hex_h * 3 / 4);
    c->pixel_x = (ax + bx + cx) / 3;
    c->pixel_y = (ay + by + cy) / 3;
  }
}

static void init_board(bool force_reset) {
  if (!force_reset && persist_exists(SAVE_KEY)) {
    SaveState state;
    persist_read_data(SAVE_KEY, &state, sizeof(SaveState));
    if (state.version == SAVE_VERSION && !state.game_over) {
      memcpy(s_board, state.board, sizeof(s_board));
      memcpy(s_bomb_timers, state.bomb_timers, sizeof(s_bomb_timers));
      s_score = state.score;
      s_used_retry = state.used_retry;
      s_is_cascading = false;
      s_is_destructing = false;
      s_game_over = false;
      return;
    }
  }

  s_score = 0; 
  s_used_retry = false; 
  
  do {
    memset(s_board, 0, sizeof(s_board));
    memset(s_bomb_timers, 0, sizeof(s_bomb_timers));

    for(int r = 0; r < GRID_ROWS; r++) {
      for(int q = 0; q < GRID_COLS; q++) {
        int color;
        bool valid;
        
        do {
          valid = true;
          color = (rand() % 5) + 1;
          s_board[q][r] = color;
          
          if (board_has_any_match(s_board)) {
            valid = false;
          }
        } while (!valid);
      }
    }
  } while (!has_valid_moves()); 
  
  s_is_cascading = false;
  s_is_destructing = false;
  s_game_over = false;
}

// --- DESTRUCTION ANIMATION ---
static void anim_destruct_update_callback(Animation *anim, const AnimationProgress progress) {
  s_current_destruct_radius = s_destruct_max - ((progress * s_destruct_max) / ANIMATION_NORMALIZED_MAX);
  layer_mark_dirty(s_grid_layer);
}

static void anim_destruct_teardown_callback(Animation *anim) { }

static const AnimationImplementation s_destruct_anim_impl = { 
  .update = anim_destruct_update_callback, 
  .teardown = anim_destruct_teardown_callback 
};

static void anim_destruct_stopped_callback(Animation *anim, bool finished, void *context) {
  s_is_destructing = false;
  
  if (finished) {
    for (int r = 0; r < GRID_ROWS; r++) {
      for (int q = 0; q < GRID_COLS; q++) {
        if (s_marked_for_deletion[q][r]) {
          s_board[q][r] = 0; 
          s_bomb_timers[q][r] = 0;
          s_marked_for_deletion[q][r] = false;
          s_score += 10; 
        }
        if (s_spawn_pearl[q][r]) {
          s_board[q][r] = PIECE_SILVER_PEARL;
          s_bomb_timers[q][r] = 0;
          s_spawn_pearl[q][r] = false;
          s_score += 50; 
        }
      }
    }
    trigger_cascade_check_callback((void *)(intptr_t)1);
  }
  
  animation_destroy(s_destruct_anim); s_destruct_anim = NULL;
}

static void start_destruct_animation() {
  if (s_is_destructing) return; 
  s_is_destructing = true;
  s_current_destruct_radius = s_destruct_max;
  
  s_destruct_anim = animation_create();
  animation_set_duration(s_destruct_anim, 250); 
  animation_set_curve(s_destruct_anim, AnimationCurveEaseIn); 
  animation_set_implementation(s_destruct_anim, &s_destruct_anim_impl);
  animation_set_handlers(s_destruct_anim, (AnimationHandlers) { .stopped = anim_destruct_stopped_callback }, NULL);
  
  animation_schedule(s_destruct_anim);
}

// --- MATCH DETECTION ---
static bool detect_matches() {
  bool matches_found = false;
  memset(s_marked_for_deletion, 0, sizeof(s_marked_for_deletion));
  memset(s_spawn_pearl, 0, sizeof(s_spawn_pearl));

  for (int i = 0; i < s_cursor_count; i++) {
    CursorPos c = s_cursors[i];
    uint8_t a = s_board[c.hex_a.q][c.hex_a.r];
    uint8_t b = s_board[c.hex_b.q][c.hex_b.r];
    uint8_t d = s_board[c.hex_c.q][c.hex_c.r];
    
    if (a != 0 && a == b && b == d) {
      matches_found = true;
      s_marked_for_deletion[c.hex_a.q][c.hex_a.r] = true;
      s_marked_for_deletion[c.hex_b.q][c.hex_b.r] = true;
      s_marked_for_deletion[c.hex_c.q][c.hex_c.r] = true;
    }
  }
  return matches_found; 
}

static bool detect_flowers() {
  bool flower_found = false;
  memset(s_marked_for_deletion, 0, sizeof(s_marked_for_deletion));
  memset(s_spawn_pearl, 0, sizeof(s_spawn_pearl));

  for (int r = 0; r < GRID_ROWS; r++) {
    for (int q = 0; q < GRID_COLS; q++) {
      const int (*offsets)[2] = (r % 2 == 0) ? EVEN_R_OFFSETS : ODD_R_OFFSETS;
      uint8_t target_color = 0;
      bool is_flower = true;
      
      for (int i = 0; i < 6; i++) {
        int n_q = q + offsets[i][0], n_r = r + offsets[i][1];
        if (!is_valid_coord(n_q, n_r) || s_board[n_q][n_r] == 0) { is_flower = false; break; }
        if (i == 0) {
           target_color = s_board[n_q][n_r];
           if (target_color >= PIECE_SILVER_PEARL) { is_flower = false; break; }
        } else if (s_board[n_q][n_r] != target_color) {
           is_flower = false; break;
        }
      }
      
      if (is_flower) { 
         flower_found = true; 
         s_spawn_pearl[q][r] = true; 
         for (int i = 0; i < 6; i++) { 
           s_marked_for_deletion[q+offsets[i][0]][r+offsets[i][1]] = true; 
         }
      }
    }
  }
  return flower_found;
}

// --- DRY-RUN CHECKS ---
static bool board_has_any_match(uint8_t sim_board[GRID_COLS][GRID_ROWS]) {
  for (int i = 0; i < s_cursor_count; i++) {
    CursorPos c = s_cursors[i];
    uint8_t a = sim_board[c.hex_a.q][c.hex_a.r];
    uint8_t b = sim_board[c.hex_b.q][c.hex_b.r];
    uint8_t d = sim_board[c.hex_c.q][c.hex_c.r];
    if (a != 0 && a == b && b == d) return true;
  }
  
  for (int r = 0; r < GRID_ROWS; r++) {
    for (int q = 0; q < GRID_COLS; q++) {
      const int (*offsets)[2] = (r % 2 == 0) ? EVEN_R_OFFSETS : ODD_R_OFFSETS;
      uint8_t target_color = 0;
      bool is_flower = true;
      for (int i = 0; i < 6; i++) {
        int n_q = q + offsets[i][0], n_r = r + offsets[i][1];
        if (!is_valid_coord(n_q, n_r) || sim_board[n_q][n_r] == 0) { is_flower = false; break; }
        if (i == 0) {
          target_color = sim_board[n_q][n_r];
          if (target_color >= PIECE_SILVER_PEARL) { is_flower = false; break; }
        } else if (sim_board[n_q][n_r] != target_color) { is_flower = false; break; }
      }
      if (is_flower) return true;
    }
  }
  return false;
}

static bool has_valid_moves() {
  uint8_t sim_board[GRID_COLS][GRID_ROWS];

  for (int i = 0; i < s_cursor_count; i++) {
    CursorPos c = s_cursors[i];
    
    memcpy(sim_board, s_board, sizeof(s_board)); 
    uint8_t a = sim_board[c.hex_a.q][c.hex_a.r], b = sim_board[c.hex_b.q][c.hex_b.r], d = sim_board[c.hex_c.q][c.hex_c.r];
    sim_board[c.hex_a.q][c.hex_a.r] = d; sim_board[c.hex_b.q][c.hex_b.r] = a; sim_board[c.hex_c.q][c.hex_c.r] = b;
    if (board_has_any_match(sim_board)) return true;

    memcpy(sim_board, s_board, sizeof(s_board)); 
    sim_board[c.hex_a.q][c.hex_a.r] = b; sim_board[c.hex_b.q][c.hex_b.r] = d; sim_board[c.hex_c.q][c.hex_c.r] = a;
    if (board_has_any_match(sim_board)) return true;
  }
  return false;
}

// --- GRAVITY & CASCADES ---
static void apply_gravity() {
  for (int q = 0; q < GRID_COLS; q++) {
    for (int r = GRID_ROWS - 1; r >= 0; r--) {
      if (s_board[q][r] == 0) {
        for (int k = r - 1; k >= 0; k--) {
          if (s_board[q][k] != 0) {
            s_board[q][r] = s_board[q][k]; s_bomb_timers[q][r] = s_bomb_timers[q][k];
            s_board[q][k] = 0; s_bomb_timers[q][k] = 0; break; 
          }
        }
      }
    }
  }

  int current_bombs = 0;
  for (int r = 0; r < GRID_ROWS; r++) {
    for (int q = 0; q < GRID_COLS; q++) {
      if (s_bomb_timers[q][r] > 0 || s_bomb_timers[q][r] == -1) current_bombs++;
    }
  }
  
  int max_bombs = 1 + (s_score / 1000); 

  for (int q = 0; q < GRID_COLS; q++) {
    for (int r = 0; r < GRID_ROWS; r++) {
      if (s_board[q][r] == 0) {
        s_board[q][r] = (rand() % 5) + 1; 
        
        bool safe_spawn_zone = (q > 0 && q < GRID_COLS - 1 && r > 0 && r < GRID_ROWS - 1);
        
        if (safe_spawn_zone && current_bombs < max_bombs && (rand() % 100 < 5)) {
            s_bomb_timers[q][r] = 15;
            current_bombs++; 
        } else {
            s_bomb_timers[q][r] = 0;
        }
      }
    }
  }
  layer_mark_dirty(s_grid_layer);
}

static void detect_matches_and_cascade() {
  bool made_flower = detect_flowers();
  bool made_match = (!made_flower) ? detect_matches() : false;
  
  if (made_flower || made_match) {
    s_is_cascading = true; 
    start_destruct_animation(); 
  } else {
    s_is_cascading = false; 
    if (!has_valid_moves()) {
      s_game_over = true;
      layer_mark_dirty(s_grid_layer);
    }
  }
}

static void trigger_cascade_check_callback(void *data) {
  s_cascade_timer = NULL; 
  if ((intptr_t)data == 1) { 
    apply_gravity();
    s_cascade_timer = app_timer_register(300, trigger_cascade_check_callback, (void *)0); 
  } else { 
    detect_matches_and_cascade();
  }
}

// --- MECHANICS (ROTATION & BOMBS) ---
static void rotate_cluster(int cursor_idx, bool clockwise) {
  CursorPos c = s_cursors[cursor_idx];
  uint8_t a = s_board[c.hex_a.q][c.hex_a.r], b = s_board[c.hex_b.q][c.hex_b.r], d = s_board[c.hex_c.q][c.hex_c.r];
  int8_t ta = s_bomb_timers[c.hex_a.q][c.hex_a.r], tb = s_bomb_timers[c.hex_b.q][c.hex_b.r], tc = s_bomb_timers[c.hex_c.q][c.hex_c.r];

  if (clockwise) {
    s_board[c.hex_a.q][c.hex_a.r] = d; s_board[c.hex_b.q][c.hex_b.r] = a; s_board[c.hex_c.q][c.hex_c.r] = b;
    s_bomb_timers[c.hex_a.q][c.hex_a.r] = tc; s_bomb_timers[c.hex_b.q][c.hex_b.r] = ta; s_bomb_timers[c.hex_c.q][c.hex_c.r] = tb;
  } else {
    s_board[c.hex_a.q][c.hex_a.r] = b; s_board[c.hex_b.q][c.hex_b.r] = d; s_board[c.hex_c.q][c.hex_c.r] = a;
    s_bomb_timers[c.hex_a.q][c.hex_a.r] = tb; s_bomb_timers[c.hex_b.q][c.hex_b.r] = tc; s_bomb_timers[c.hex_c.q][c.hex_c.r] = ta;
  }
}

static void tick_bombs() {
  for(int r = 0; r < GRID_ROWS; r++) {
    for(int q = 0; q < GRID_COLS; q++) {
      if (s_bomb_timers[q][r] > 0) {
        if (--s_bomb_timers[q][r] == 0) {
          s_game_over = true;
          s_bomb_timers[q][r] = -1; 
        }
      }
    }
  }
}

// --- ROTATION ANIMATION ---
static void anim_update_callback(Animation *anim, const AnimationProgress progress) {
  s_current_anim_angle = (progress * (TRIG_MAX_ANGLE / 3)) / ANIMATION_NORMALIZED_MAX;
  int32_t half_pi_progress = (progress * (TRIG_MAX_ANGLE / 2)) / ANIMATION_NORMALIZED_MAX;
  s_current_anim_pop = (sin_lookup(half_pi_progress) * 4) / TRIG_MAX_RATIO; 
  layer_mark_dirty(s_grid_layer);
}

static void anim_teardown_callback(Animation *anim) { }

static const AnimationImplementation s_anim_impl = { 
  .update = anim_update_callback, 
  .teardown = anim_teardown_callback 
};

static void anim_stopped_callback(Animation *anim, bool finished, void *context) {
  s_is_animating = false;
  s_current_anim_pop = 0;
  
  if (finished) {
    rotate_cluster(s_active_cursor_idx, s_anim_clockwise);
    tick_bombs();
    if (!s_game_over) detect_matches_and_cascade();
    layer_mark_dirty(s_grid_layer);
  }
  
  animation_destroy(s_rotation_anim); s_rotation_anim = NULL;
}

static void start_rotation_animation(bool clockwise) {
  if (s_is_animating || s_is_cascading || s_game_over || s_is_destructing) return; 
  s_is_animating = true; s_anim_clockwise = clockwise; s_current_anim_angle = 0; s_current_anim_pop = 0;
  
  s_rotation_anim = animation_create();
  animation_set_duration(s_rotation_anim, 350); 
  animation_set_curve(s_rotation_anim, AnimationCurveEaseOut); 
  animation_set_implementation(s_rotation_anim, &s_anim_impl);
  animation_set_handlers(s_rotation_anim, (AnimationHandlers) { .stopped = anim_stopped_callback }, NULL);
  
  animation_schedule(s_rotation_anim);
}

// --- INPUT HANDLING ---
static void handle_touch_event(int touch_x, int touch_y) {
  if (s_is_animating || s_is_cascading || s_game_over || s_is_destructing) return;
  int closest_idx = -1, min_dist = 999999;
  
  for (int i = 0; i < s_cursor_count; i++) {
    int dist = distance_squared(touch_x, touch_y, s_cursors[i].pixel_x, s_cursors[i].pixel_y);
    if (dist < min_dist) { min_dist = dist; closest_idx = i; }
  }
  
  if (closest_idx != -1) {
    s_active_cursor_idx = closest_idx;
    start_rotation_animation(true);
  }
}

// --- SPLASH SCREEN RENDER ---
static void splash_update_proc(Layer *layer, GContext *ctx) {
  GRect bounds = layer_get_bounds(layer);

  int cx = bounds.size.w / 2;
  int cy = bounds.size.h / 4;
  int title_y = cy + (s_hex_h / 2) + 5;
  int menu_y = title_y + 45;

  // Draw 3 connected logo hexes
  draw_hex(ctx, cx, cy - s_hex_h*3/8, 2); 
  draw_hex(ctx, cx - s_hex_w/2, cy + s_hex_h*3/8, 1); 
  draw_hex(ctx, cx + s_hex_w/2, cy + s_hex_h*3/8, 3); 

  // Title
  graphics_context_set_text_color(ctx, GColorWhite);
  graphics_draw_text(ctx, "PeXic", fonts_get_system_font(FONT_KEY_BITHAM_30_BLACK), GRect(0, title_y, bounds.size.w, 40), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);

  // Menu: PLAY
  if (s_splash_selection == 0) {
    graphics_context_set_fill_color(ctx, GColorWhite);
    graphics_fill_rect(ctx, GRect(bounds.size.w/2 - 50, menu_y, 100, 30), 4, GCornersAll);
    graphics_context_set_text_color(ctx, GColorBlack);
  } else {
    graphics_context_set_text_color(ctx, GColorWhite);
  }
  graphics_draw_text(ctx, "PLAY", fonts_get_system_font(FONT_KEY_GOTHIC_24_BOLD), GRect(0, menu_y-2, bounds.size.w, 30), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);

  // Menu: EXIT
  menu_y += 35;
  if (s_splash_selection == 1) {
    graphics_context_set_fill_color(ctx, GColorWhite);
    graphics_fill_rect(ctx, GRect(bounds.size.w/2 - 50, menu_y, 100, 30), 4, GCornersAll);
    graphics_context_set_text_color(ctx, GColorBlack);
  } else {
    graphics_context_set_text_color(ctx, GColorWhite);
  }
  graphics_draw_text(ctx, "EXIT", fonts_get_system_font(FONT_KEY_GOTHIC_24_BOLD), GRect(0, menu_y-2, bounds.size.w, 30), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);
}

// --- GLOBAL TOUCH HANDLER ---
#if defined(PBL_TOUCH)
static void touch_handler(const TouchEvent *event, void *context) {
  if (window_stack_get_top_window() == s_game_window) {
    if (event->type == TouchEvent_Touchdown) {
      if (s_game_over) {
        int mid_y = layer_get_bounds(s_grid_layer).size.h / 2;
        if (event->y < mid_y + 20) {
          game_select_click_handler(NULL, NULL);
        } else {
          game_back_click_handler(NULL, NULL);
        }
        return;
      }
      handle_touch_event(event->x, event->y);
    }
  } else if (window_stack_get_top_window() == s_splash_window) {
    if (event->type == TouchEvent_Touchdown) {
      int threshold = layer_get_bounds(s_splash_layer).size.h / 2 + 30;
      s_splash_selection = (event->y < threshold) ? 0 : 1;
      layer_mark_dirty(s_splash_layer);
    } else if (event->type == TouchEvent_Liftoff) {
      if (s_splash_selection == 0) window_stack_push(s_game_window, true);
      else window_stack_pop_all(true);
    }
  }
}
#endif

// --- SPLASH MENU CONTROLS ---
static void splash_up_click_handler(ClickRecognizerRef recognizer, void *context) {
  s_splash_selection = 0; layer_mark_dirty(s_splash_layer);
}
static void splash_down_click_handler(ClickRecognizerRef recognizer, void *context) {
  s_splash_selection = 1; layer_mark_dirty(s_splash_layer);
}
static void splash_select_click_handler(ClickRecognizerRef recognizer, void *context) {
  if (s_splash_selection == 0) window_stack_push(s_game_window, true);
  else window_stack_pop_all(true);
}
static void splash_click_config_provider(void *context) {
  window_single_click_subscribe(BUTTON_ID_UP, splash_up_click_handler);
  window_single_click_subscribe(BUTTON_ID_DOWN, splash_down_click_handler);
  window_single_click_subscribe(BUTTON_ID_SELECT, splash_select_click_handler);
}

// --- GAME MENU CONTROLS ---
static void game_up_click_handler(ClickRecognizerRef recognizer, void *context) {
  if(s_is_animating || s_is_cascading || s_game_over || s_is_destructing) return;
  if(s_active_cursor_idx > 0) { 
    s_active_cursor_idx--; 
    layer_mark_dirty(s_grid_layer); 
  }
}
static void game_down_click_handler(ClickRecognizerRef recognizer, void *context) {
  if(s_is_animating || s_is_cascading || s_game_over || s_is_destructing) return;
  if(s_active_cursor_idx < s_cursor_count - 1) { 
    s_active_cursor_idx++; 
    layer_mark_dirty(s_grid_layer); 
  }
}
static void game_select_click_handler(ClickRecognizerRef recognizer, void *context) {
  if (s_game_over) {
    if (!s_used_retry) {
      s_used_retry = true;
      s_game_over = false;
      for(int r = 0; r < GRID_ROWS; r++) {
        for(int q = 0; q < GRID_COLS; q++) {
          if (s_bomb_timers[q][r] == -1 || (s_bomb_timers[q][r] > 0 && s_bomb_timers[q][r] <= 5)) {
            s_bomb_timers[q][r] = 10;
          }
        }
      }
    } else {
      init_board(true); 
    }
    layer_mark_dirty(s_grid_layer);
    return;
  }
  start_rotation_animation(true);
}
static void game_select_long_click_handler(ClickRecognizerRef recognizer, void *context) {
  start_rotation_animation(false);
}
static void game_back_click_handler(ClickRecognizerRef recognizer, void *context) {
  window_stack_pop(true); 
}
static void game_click_config_provider(void *context) {
  window_single_click_subscribe(BUTTON_ID_UP, game_up_click_handler);
  window_single_click_subscribe(BUTTON_ID_DOWN, game_down_click_handler);
  window_single_click_subscribe(BUTTON_ID_SELECT, game_select_click_handler);
  window_long_click_subscribe(BUTTON_ID_SELECT, 0, NULL, game_select_long_click_handler);
  window_single_click_subscribe(BUTTON_ID_BACK, game_back_click_handler);
}

// --- GAME RENDER LOOP ---
static void grid_update_proc(Layer *layer, GContext *ctx) {
  CursorPos c = s_cursors[s_active_cursor_idx];
  GRect bounds = layer_get_bounds(layer);

  // 1. Draw Dummy Bezel Hexes
  for (int r = -2; r < GRID_ROWS + 2; r++) {
    for (int q = -2; q < GRID_COLS + 2; q++) {
      if (q >= 0 && q < GRID_COLS && r >= 0 && r < GRID_ROWS) continue; 
      int x = s_x_off + q * s_hex_w + (r % 2) * (s_hex_w / 2);
      int y = s_y_off + r * (s_hex_h * 3 / 4);
      gpath_move_to(s_hex_path, GPoint(x, y));
      graphics_context_set_fill_color(ctx, get_dummy_color(q, r));
      gpath_draw_filled(ctx, s_hex_path);
      graphics_context_set_stroke_color(ctx, GColorBlack);
      gpath_draw_outline(ctx, s_hex_path);
    }
  }

  // 2. Draw Static Play Board & Destruction Effects
  for (int r = 0; r < GRID_ROWS; r++) {
    for (int q = 0; q < GRID_COLS; q++) {
      if (s_board[q][r] == 0) continue;
      bool is_anim_hex = s_is_animating && ((q==c.hex_a.q && r==c.hex_a.r) || (q==c.hex_b.q && r==c.hex_b.r) || (q==c.hex_c.q && r==c.hex_c.r));
      if (is_anim_hex) continue; 

      int x = s_x_off + q * s_hex_w + (r % 2) * (s_hex_w / 2);
      int y = s_y_off + r * (s_hex_h * 3 / 4);

      if (s_is_destructing && s_marked_for_deletion[q][r]) {
        graphics_context_set_fill_color(ctx, get_piece_color(s_board[q][r]));
        graphics_fill_circle(ctx, GPoint(x, y), s_current_destruct_radius);
        graphics_context_set_stroke_width(ctx, 2);
        graphics_context_set_stroke_color(ctx, GColorWhite);
        graphics_draw_circle(ctx, GPoint(x, y), s_destruct_max - s_current_destruct_radius + 2);
        graphics_context_set_stroke_width(ctx, 1);
      } else {
        draw_hex(ctx, x, y, s_board[q][r]);
        
        if (s_bomb_timers[q][r] > 0 || s_bomb_timers[q][r] == -1) {
          int val = s_bomb_timers[q][r] == -1 ? 0 : s_bomb_timers[q][r];
          graphics_context_set_fill_color(ctx, GColorRed);
          graphics_fill_circle(ctx, GPoint(x, y), 9);
          char txt[4]; snprintf(txt, sizeof(txt), "%d", val);
          graphics_context_set_text_color(ctx, GColorWhite);
          graphics_draw_text(ctx, txt, fonts_get_system_font(FONT_KEY_GOTHIC_14_BOLD), GRect(x-10, y-10, 20, 20), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);
        }
      }
    }
  }

  // 3. Draw Animating Rotation Pieces
  if (s_is_animating) {
    int32_t angle = s_anim_clockwise ? s_current_anim_angle : -s_current_anim_angle;
    int32_t cos_a = cos_lookup(angle);
    int32_t sin_a = sin_lookup(angle);

    int start_x[3] = {
      s_x_off + c.hex_a.q * s_hex_w + (c.hex_a.r % 2) * (s_hex_w / 2),
      s_x_off + c.hex_b.q * s_hex_w + (c.hex_b.r % 2) * (s_hex_w / 2),
      s_x_off + c.hex_c.q * s_hex_w + (c.hex_c.r % 2) * (s_hex_w / 2)
    };
    int start_y[3] = {
      s_y_off + c.hex_a.r * (s_hex_h * 3 / 4),
      s_y_off + c.hex_b.r * (s_hex_h * 3 / 4),
      s_y_off + c.hex_c.r * (s_hex_h * 3 / 4)
    };

    for(int i = 0; i < 3; i++) {
      int dx = start_x[i] - c.pixel_x;
      int dy = start_y[i] - c.pixel_y;
      int length_approx = s_destruct_max + 1; 
      dx += (dx * s_current_anim_pop) / length_approx;
      dy += (dy * s_current_anim_pop) / length_approx;
      int rot_x = (dx * cos_a - dy * sin_a) / TRIG_MAX_RATIO;
      int rot_y = (dx * sin_a + dy * cos_a) / TRIG_MAX_RATIO;
      gpath_move_to(s_hex_path, GPoint(c.pixel_x + rot_x + 3, c.pixel_y + rot_y + 4));
      graphics_context_set_fill_color(ctx, GColorBlack);
      gpath_draw_filled(ctx, s_hex_path);
    }
    
    uint8_t vals[3] = { s_board[c.hex_a.q][c.hex_a.r], s_board[c.hex_b.q][c.hex_b.r], s_board[c.hex_c.q][c.hex_c.r] };
    for(int i = 0; i < 3; i++) {
      int dx = start_x[i] - c.pixel_x;
      int dy = start_y[i] - c.pixel_y;
      int length_approx = s_destruct_max + 1; 
      dx += (dx * s_current_anim_pop) / length_approx;
      dy += (dy * s_current_anim_pop) / length_approx;
      int rot_x = (dx * cos_a - dy * sin_a) / TRIG_MAX_RATIO;
      int rot_y = (dx * sin_a + dy * cos_a) / TRIG_MAX_RATIO;
      draw_hex(ctx, c.pixel_x + rot_x, c.pixel_y + rot_y, vals[i]);
    }
  }

  // 4. Draw UI Cursor Highlight
  if (!s_is_animating && !s_is_cascading && !s_game_over && !s_is_destructing) {
    graphics_context_set_stroke_width(ctx, 3);
    graphics_context_set_stroke_color(ctx, GColorYellow);
    
    int cx[3] = {
      s_x_off + c.hex_a.q * s_hex_w + (c.hex_a.r % 2) * (s_hex_w / 2),
      s_x_off + c.hex_b.q * s_hex_w + (c.hex_b.r % 2) * (s_hex_w / 2),
      s_x_off + c.hex_c.q * s_hex_w + (c.hex_c.r % 2) * (s_hex_w / 2)
    };
    int cy[3] = {
      s_y_off + c.hex_a.r * (s_hex_h * 3 / 4),
      s_y_off + c.hex_b.r * (s_hex_h * 3 / 4),
      s_y_off + c.hex_c.r * (s_hex_h * 3 / 4)
    };
    for(int i=0; i<3; i++) {
      gpath_move_to(s_hex_path, GPoint(cx[i], cy[i]));
      gpath_draw_outline(ctx, s_hex_path);
    }
    
    graphics_context_set_stroke_width(ctx, 1);
    graphics_context_set_fill_color(ctx, GColorWhite);
    graphics_fill_circle(ctx, GPoint(c.pixel_x, c.pixel_y), 4);
    graphics_context_set_stroke_color(ctx, GColorBlack);
    graphics_draw_circle(ctx, GPoint(c.pixel_x, c.pixel_y), 4);
  }

  // 5. Draw the Black Score Header
  graphics_context_set_fill_color(ctx, GColorBlack);
#if defined(PBL_ROUND)
  graphics_fill_circle(ctx, GPoint(bounds.size.w / 2, -(bounds.size.w / 2) + 26), bounds.size.w / 2);
  int score_y = 6;
#else
  graphics_fill_rect(ctx, GRect(0, 0, bounds.size.w, 24), 0, GCornerNone);
  int score_y = -2;
#endif

  char score_str[32];
  snprintf(score_str, sizeof(score_str), "SCORE: %d", s_score);
  graphics_context_set_text_color(ctx, GColorWhite);
  graphics_draw_text(ctx, score_str, fonts_get_system_font(FONT_KEY_GOTHIC_18_BOLD), GRect(0, score_y, bounds.size.w, 20), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);

  // 6. Draw Game Over Menu
  if (s_game_over) {
    graphics_context_set_fill_color(ctx, GColorOxfordBlue);
    graphics_fill_rect(ctx, GRect(bounds.size.w/2 - 80, bounds.size.h/2 - 60, 160, 120), 8, GCornersAll);
    graphics_context_set_stroke_color(ctx, GColorWhite);
    graphics_context_set_stroke_width(ctx, 2);
    graphics_draw_round_rect(ctx, GRect(bounds.size.w/2 - 80, bounds.size.h/2 - 60, 160, 120), 8);
    graphics_context_set_stroke_width(ctx, 1);
    graphics_context_set_text_color(ctx, GColorWhite);
    graphics_draw_text(ctx, "GAME OVER", fonts_get_system_font(FONT_KEY_GOTHIC_24_BOLD), GRect(0, bounds.size.h/2 - 50, bounds.size.w, 30), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);
    char go_score[32];
    snprintf(go_score, sizeof(go_score), "Final Score: %d", s_score);
    graphics_draw_text(ctx, go_score, fonts_get_system_font(FONT_KEY_GOTHIC_18), GRect(0, bounds.size.h/2 - 20, bounds.size.w, 20), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);
    
    if (!s_used_retry) {
      graphics_draw_text(ctx, "[SELECT] Use 1 Retry", fonts_get_system_font(FONT_KEY_GOTHIC_14_BOLD), GRect(0, bounds.size.h/2 + 5, bounds.size.w, 20), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);
    } else {
      graphics_draw_text(ctx, "[SELECT] Restart", fonts_get_system_font(FONT_KEY_GOTHIC_14_BOLD), GRect(0, bounds.size.h/2 + 5, bounds.size.w, 20), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);
    }
    graphics_draw_text(ctx, "[BACK] Exit", fonts_get_system_font(FONT_KEY_GOTHIC_14), GRect(0, bounds.size.h/2 + 25, bounds.size.w, 20), GTextOverflowModeWordWrap, GTextAlignmentCenter, NULL);
  }
}

// --- LIFECYCLES ---
static void splash_window_load(Window *window) {
  Layer *window_layer = window_get_root_layer(window);
  s_splash_layer = layer_create(layer_get_bounds(window_layer));
  layer_set_update_proc(s_splash_layer, splash_update_proc);
  layer_add_child(window_layer, s_splash_layer);
}

static void splash_window_appear(Window *window) {
  layer_mark_dirty(s_splash_layer);
}

static void splash_window_unload(Window *window) {
  layer_destroy(s_splash_layer);
}

static void game_window_load(Window *window) {
  Layer *window_layer = window_get_root_layer(window);
  s_grid_layer = layer_create(layer_get_bounds(window_layer));
  layer_set_update_proc(s_grid_layer, grid_update_proc);
  layer_add_child(window_layer, s_grid_layer);
}

static void game_window_appear(Window *window) {
  layer_mark_dirty(s_grid_layer); 
}

static void game_window_unload(Window *window) {
  if (s_cascade_timer) {
    app_timer_cancel(s_cascade_timer);
    s_cascade_timer = NULL;
  }
  if (s_rotation_anim) {
    animation_unschedule(s_rotation_anim);
  }
  if (s_destruct_anim) {
    animation_unschedule(s_destruct_anim);
  }
  layer_destroy(s_grid_layer);
}

static void init() {
  srand(time(NULL)); 
  s_hex_path = gpath_create(&HEX_PATH_INFO);
  
  init_cursors(); 
  init_board(false); 
  s_active_cursor_idx = s_cursor_count / 2;

  s_splash_window = window_create();
  window_set_background_color(s_splash_window, GColorOxfordBlue);
  window_set_window_handlers(s_splash_window, (WindowHandlers) {
    .load = splash_window_load,
    .appear = splash_window_appear,
    .unload = splash_window_unload
  });
  window_set_click_config_provider(s_splash_window, splash_click_config_provider);
  
  s_game_window = window_create();
  window_set_background_color(s_game_window, GColorOxfordBlue);
  window_set_window_handlers(s_game_window, (WindowHandlers) {
    .load = game_window_load,
    .appear = game_window_appear,
    .unload = game_window_unload
  });
  window_set_click_config_provider(s_game_window, game_click_config_provider);

  window_stack_push(s_splash_window, true);
  
#if defined(PBL_TOUCH)
  touch_service_subscribe(touch_handler, NULL);
#endif
}

static void deinit() { 
  SaveState state = {
    .version = SAVE_VERSION,
    .score = s_score,
    .game_over = s_game_over,
    .used_retry = s_used_retry
  };
  memcpy(state.board, s_board, sizeof(s_board));
  memcpy(state.bomb_timers, s_bomb_timers, sizeof(s_bomb_timers));
  persist_write_data(SAVE_KEY, &state, sizeof(SaveState));

  gpath_destroy(s_hex_path);

#if defined(PBL_TOUCH)
  touch_service_unsubscribe();
#endif
  window_destroy(s_game_window); 
  window_destroy(s_splash_window); 
}

int main(void) { init(); app_event_loop(); deinit(); }
