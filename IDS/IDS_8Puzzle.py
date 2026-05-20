import tkinter as tk
from tkinter import ttk

# ══════════════════════════════════════════════════
#  CONFIG
# ══════════════════════════════════════════════════
INITIAL = ((2, 8, 3), (1, 6, 4), (7, 0, 5))
GOAL    = ((1, 2, 3), (8, 0, 4), (7, 6, 5))
MAX_IDS_DEPTH = 31

MOVE_DIRS = [('L', 0, -1), ('R', 0, 1), ('U', -1, 0), ('D', 1, 0)]
ARROW = {'U': '↑ U', 'D': '↓ D', 'L': '← L', 'R': '→ R'}
def _make_label(idx):
    if idx < 26:
        return chr(65 + idx)
    idx -= 26
    return chr(65 + idx % 26) + str(idx // 26)

# Colors
BG      = '#0d1117'
PANEL   = '#161b22'
BORDER  = '#30363d'
ACCENT  = '#a371f7'
GREEN   = '#3fb950'
ORANGE  = '#d29922'
RED     = '#f85149'
GRAY    = '#8b949e'
WHITE   = '#e6edf3'
PURPLE  = '#bc8cff'

TILE_BG     = '#8957e5'
TILE_BLANK  = '#0d1117'
TILE_NEW    = '#f0883e'
TILE_GOAL_C = '#238636'
TILE_EXP    = '#21262d'


# ══════════════════════════════════════════════════
#  DATA STRUCTURES
# ══════════════════════════════════════════════════
class NodeInfo:
    def __init__(self, state, action=None, depth=0, parent_label=None, label='?', parent=None):
        self.state        = state
        self.action       = action
        self.depth        = depth
        self.parent_label = parent_label
        self.label        = label
        self.parent       = parent


class IDSStep:
    def __init__(self, phase, current_node, frontier, explored_count, new_labels, desc, limit):
        self.phase          = phase           # 'init' | 'expand' | 'found' | 'failure' | 'cutoff' | 'new_limit'
        self.current_node   = current_node    # NodeInfo | None
        self.frontier       = frontier        # list[NodeInfo]  (snapshot)
        self.explored_count = explored_count  # int
        self.new_labels     = new_labels      # set
        self.desc           = desc
        self.limit          = limit


# ══════════════════════════════════════════════════
#  PUZZLE HELPERS
# ══════════════════════════════════════════════════
def find_zero(state):
    for r in range(3):
        for c in range(3):
            if state[r][c] == 0:
                return r, c

def apply_move(state, direction):
    dr, dc = next((a, b) for n, a, b in MOVE_DIRS if n == direction)
    r, c = find_zero(state)
    nr, nc = r + dr, c + dc
    if 0 <= nr < 3 and 0 <= nc < 3:
        lst = [list(row) for row in state]
        lst[r][c], lst[nr][nc] = lst[nr][nc], lst[r][c]
        return tuple(tuple(x) for x in lst)
    return None


# ══════════════════════════════════════════════════
#  IDS – FULL TRACE
# ══════════════════════════════════════════════════
def ids_full_trace(initial, goal):
    goal_t  = tuple(tuple(r) for r in goal)
    
    steps = []
    explored_master = []
    
    # ── IDS loop (Vòng lặp tăng dần độ sâu limit) ──
    for limit in range(MAX_IDS_DEPTH):
        label_i = [0]
        def make_node(state, action=None, depth=0, parent_node=None):
            parent_label = parent_node.label if parent_node else None
            n = NodeInfo(state, action, depth, parent_label, _make_label(label_i[0]), parent=parent_node)
            label_i[0] += 1
            return n
            
        # ── Step 0 : init cho mỗi lần gọi DLS ──────────
        # DLS (Depth-Limited Search) uses Stack (LIFO)
        start = make_node(initial)
        frontier_stack = [start]
        
        steps.append(IDSStep('new_limit', None, list(frontier_stack), len(explored_master), {start.label}, f'--- BẮT ĐẦU DLS VỚI LIMIT = {limit} ---', limit))
        
        dls_result = 'failure'
        
        # ── DLS loop ──────────────────────────────────
        while frontier_stack:
            node = frontier_stack.pop()  # LIFO - pop from top of stack
            
            # Check goal on pop
            if node.state == goal_t:
                steps.append(IDSStep('found', node, list(frontier_stack), len(explored_master), set(), f'Pop [{node.label}] — đây là GOAL! Tìm thấy tại Limit={limit}', limit))
                return steps, explored_master
                
            # Check depth limit (Cutoff)
            if node.depth > limit:
                dls_result = 'cutoff'
                steps.append(IDSStep('cutoff', node, list(frontier_stack), len(explored_master), set(), f'[{node.label}] vượt quá limit ({limit}) — Cutoff!', limit))
                continue
                
            # Cycle checking (Tránh lặp lại trạng thái trên cùng một nhánh)
            curr = node.parent
            is_cycle = False
            while curr:
                if curr.state == node.state:
                    is_cycle = True
                    break
                curr = curr.parent
                
            if is_cycle:
                continue
                
            explored_master.append(node)
            
            new_labels = set()
            
            # Reverse order so first action ends up on top of stack
            for dir_name, dr, dc in reversed(MOVE_DIRS):
                child_state = apply_move(node.state, dir_name)
                if child_state is None:
                    continue
                    
                child = make_node(child_state, dir_name, node.depth + 1, node)
                frontier_stack.append(child)
                new_labels.add(child.label)
                
            steps.append(IDSStep('expand', node, list(frontier_stack), len(explored_master), new_labels, f'Mở rộng [{node.label}] (depth={node.depth}): thêm {len(new_labels)} children vào Stack', limit))
            
        if dls_result != 'cutoff':
            steps.append(IDSStep('failure', None, [], len(explored_master), set(), f'Limit={limit} trả về Failure hoàn toàn! Không có giải pháp.', limit))
            return steps, explored_master
        else:
            steps.append(IDSStep('cutoff', None, [], len(explored_master), set(), f'DLS Limit={limit} bị Cutoff, tăng Limit lên {limit+1}', limit))

    steps.append(IDSStep('failure', None, [], len(explored_master), set(), 'Vượt quá MAX_IDS_DEPTH. Dừng lại.', MAX_IDS_DEPTH))
    return steps, explored_master


# ══════════════════════════════════════════════════
#  DRAWING HELPER
# ══════════════════════════════════════════════════
CELL = 20

def draw_board(canvas, x, y, state, cell=CELL, highlight=None, is_goal_state=False):
    is_ghost = (highlight == 'ghost')
    for r in range(3):
        for c in range(3):
            val = state[r][c]
            cx  = x + c * cell
            cy  = y + r * cell
            if is_ghost:
                bg = TILE_BLANK if val == 0 else '#1a1a2e'
            elif val == 0:
                bg = TILE_BLANK
            elif is_goal_state:
                bg = TILE_GOAL_C
            elif highlight == 'explored':
                bg = TILE_EXP
            else:
                bg = TILE_BG
            canvas.create_rectangle(cx, cy, cx + cell - 1, cy + cell - 1,
                                    fill=bg, outline=BORDER, width=1)
            if val != 0:
                canvas.create_text(cx + cell // 2, cy + cell // 2,
                                   text=str(val),
                                   fill='#484f58' if is_ghost else WHITE,
                                   font=('Segoe UI', 7, 'bold'))

# ══════════════════════════════════════════════════
#  MAIN APP
# ══════════════════════════════════════════════════
class App:
    def __init__(self, root):
        self.root   = root
        self.root.title('8-Puzzle — IDS Algorithm')
        self.root.configure(bg=BG)
        self.root.geometry('1250x720')
        self.root.resizable(True, True)

        self.steps, self.explored_master = ids_full_trace(INITIAL, GOAL)
        self.idx     = 0
        self._auto   = False
        self.speed   = tk.IntVar(value=400)

        self._build_ui()
        self._render(0)

    # ─── UI Layout ────────────────────────────────
    def _build_ui(self):
        hdr = tk.Frame(self.root, bg=BG)
        hdr.pack(fill='x', padx=16, pady=(10, 4))
        tk.Label(hdr, text='8-Puzzle — IDS Algorithm',
                 font=('Segoe UI', 16, 'bold'), bg=BG, fg=ACCENT).pack(side='left')
        self.limit_lbl = tk.Label(hdr, text=f'  ({len(self.steps)} bước IDS  |  Current Limit=0)',
                 font=('Segoe UI', 10), bg=BG, fg=GRAY)
        self.limit_lbl.pack(side='left')

        body = tk.Frame(self.root, bg=BG)
        body.pack(fill='both', expand=True, padx=10, pady=4)

        self._build_left(body)
        self._build_center(body)
        self._build_right(body)
        self._build_bottom()

    def _panel(self, parent, title, width=None):
        f = tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        if width:
            f.pack(side='left', fill='y', padx=(0, 8), ipadx=4, ipady=4)
            f.pack_propagate(False)
            f.config(width=width)
        else:
            f.pack(side='left', fill='both', expand=True, padx=(0, 8))
        tk.Label(f, text=title, bg=PANEL, fg=GRAY,
                 font=('Segoe UI', 9, 'bold')).pack(anchor='w', padx=10, pady=(8, 2))
        tk.Frame(f, bg=BORDER, height=1).pack(fill='x', padx=6)
        return f

    def _build_left(self, parent):
        pnl = self._panel(parent, 'Node đang mở rộng', width=230)

        self.cur_canvas = tk.Canvas(pnl, width=120, height=120, bg=PANEL, highlightthickness=0)
        self.cur_canvas.pack(pady=(14, 4))

        self.cur_label  = tk.Label(pnl, text='—', bg=PANEL, fg=WHITE, font=('Segoe UI', 11, 'bold'))
        self.cur_label.pack()
        self.cur_action = tk.Label(pnl, text='', bg=PANEL, fg=ORANGE, font=('Segoe UI', 10))
        self.cur_action.pack()
        self.cur_depth  = tk.Label(pnl, text='', bg=PANEL, fg=GRAY, font=('Segoe UI', 9))
        self.cur_depth.pack()
        self.cur_parent = tk.Label(pnl, text='', bg=PANEL, fg=PURPLE, font=('Segoe UI', 9))
        self.cur_parent.pack(pady=(0, 8))

        tk.Frame(pnl, bg=BORDER, height=1).pack(fill='x', padx=6, pady=6)
        tk.Label(pnl, text='Goal State', bg=PANEL, fg=GRAY, font=('Segoe UI', 9, 'bold')).pack()
        gc = tk.Canvas(pnl, width=72, height=72, bg=PANEL, highlightthickness=0)
        gc.pack(pady=4)
        draw_board(gc, 3, 3, GOAL, cell=22, is_goal_state=True)

    def _build_center(self, parent):
        pnl = self._panel(parent, 'Frontier — Stack (LIFO)  ← TOP ở cuối danh sách')

        wrapper = tk.Frame(pnl, bg=PANEL)
        wrapper.pack(fill='both', expand=True, padx=4, pady=4)

        vsb = tk.Scrollbar(wrapper, orient='vertical', bg=PANEL, troughcolor=BG, width=8)
        vsb.pack(side='right', fill='y')

        self.fr_canvas = tk.Canvas(wrapper, bg=BG, yscrollcommand=vsb.set, highlightthickness=0)
        self.fr_canvas.pack(side='left', fill='both', expand=True)
        vsb.config(command=self.fr_canvas.yview)
        self.fr_canvas.bind('<Configure>', lambda e: self.fr_canvas.configure(scrollregion=self.fr_canvas.bbox('all')))
        self.fr_canvas.bind('<MouseWheel>', lambda e: self.fr_canvas.yview_scroll(-1 * (e.delta // 120), 'units'))

    def _build_right(self, parent):
        pnl = self._panel(parent, 'Explored', width=260)

        wrapper = tk.Frame(pnl, bg=PANEL)
        wrapper.pack(fill='both', expand=True, padx=4, pady=4)

        vsb = tk.Scrollbar(wrapper, orient='vertical', bg=PANEL, troughcolor=BG, width=8)
        vsb.pack(side='right', fill='y')

        self.ex_canvas = tk.Canvas(wrapper, bg=BG, yscrollcommand=vsb.set, highlightthickness=0)
        self.ex_canvas.pack(side='left', fill='both', expand=True)
        vsb.config(command=self.ex_canvas.yview)
        self.ex_canvas.bind('<Configure>', lambda e: self.ex_canvas.configure(scrollregion=self.ex_canvas.bbox('all')))
        self.ex_canvas.bind('<MouseWheel>', lambda e: self.ex_canvas.yview_scroll(-1 * (e.delta // 120), 'units'))

    def _build_bottom(self):
        self.banner = tk.Frame(self.root, bg='#1c2128', highlightthickness=2, highlightbackground=ACCENT)
        self.banner.pack(fill='x', padx=10, pady=(0, 4))

        banner_inner = tk.Frame(self.banner, bg='#1c2128')
        banner_inner.pack(fill='x', padx=14, pady=8)

        self.phase_icon = tk.Label(banner_inner, text='⬤', bg='#1c2128', font=('Segoe UI', 14), fg=ACCENT)
        self.phase_icon.pack(side='left', padx=(0, 8))

        self.phase_badge = tk.Label(banner_inner, text='INIT', bg=ACCENT, fg='black', font=('Segoe UI', 9, 'bold'), padx=8, pady=2)
        self.phase_badge.pack(side='left', padx=(0, 12))

        self.desc_lbl = tk.Label(banner_inner, text='', bg='#1c2128', fg=WHITE, font=('Segoe UI', 11, 'bold'), anchor='w')
        self.desc_lbl.pack(side='left', fill='x', expand=True)

        self.step_lbl = tk.Label(banner_inner, text='Bước 0 / 0', bg='#1c2128', fg=GRAY, font=('Segoe UI', 10, 'bold'))
        self.step_lbl.pack(side='right', padx=(12, 0))

        ctrl_bar = tk.Frame(self.root, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        ctrl_bar.pack(fill='x', padx=10, pady=(0, 8))

        ctrl = tk.Frame(ctrl_bar, bg=PANEL)
        ctrl.pack(pady=6)

        bs = dict(font=('Segoe UI', 10, 'bold'), relief='flat', cursor='hand2', padx=12, pady=5, bd=0)

        tk.Button(ctrl, text='⏮', command=self._go_first, bg='#21262d', fg=WHITE, **bs).grid(row=0, column=0, padx=3)
        tk.Button(ctrl, text='◀ Trước', command=self._go_prev, bg='#21262d', fg=WHITE, **bs).grid(row=0, column=1, padx=3)
        self.btn_auto = tk.Button(ctrl, text='▶ Auto', command=self._toggle_auto, bg=ACCENT, fg='black', **bs)
        self.btn_auto.grid(row=0, column=2, padx=3)
        tk.Button(ctrl, text='Tiếp ▶', command=self._go_next, bg='#21262d', fg=WHITE, **bs).grid(row=0, column=3, padx=3)
        tk.Button(ctrl, text='⏭', command=self._go_last, bg='#21262d', fg=WHITE, **bs).grid(row=0, column=4, padx=3)

        tk.Button(ctrl, text='🛣 Show Path', command=self._show_path, bg=PURPLE, fg='black', **bs).grid(row=0, column=5, padx=3)

        tk.Frame(ctrl, bg=BORDER, width=1, height=28).grid(row=0, column=6, padx=10)

        tk.Label(ctrl, text='Tốc độ:', bg=PANEL, fg=GRAY, font=('Segoe UI', 9)).grid(row=0, column=7, padx=(0, 4))
        tk.Scale(ctrl, from_=50, to=1500, orient='horizontal', variable=self.speed, bg=PANEL, fg=WHITE, troughcolor='#21262d', highlightthickness=0, length=150, showvalue=False).grid(row=0, column=8, padx=3)

    def _show_path(self):
        import tkinter.messagebox
        found_step = next((s for s in self.steps if s.phase == 'found'), None)
        if not found_step or not found_step.current_node:
            tkinter.messagebox.showinfo('Đường đi', 'Chưa tìm thấy Goal để hiển thị đường đi.')
            return
            
        path = []
        curr = found_step.current_node
        while curr:
            path.append(curr)
            curr = getattr(curr, 'parent', None)
        path.reverse()
        
        top = tk.Toplevel(self.root)
        top.title(f"Đường đi tới Goal ({len(path)-1} bước)")
        top.geometry("800x250")
        top.configure(bg=BG)
        
        canvas = tk.Canvas(top, bg=BG, highlightthickness=0)
        scrollbar = tk.Scrollbar(top, orient="horizontal", command=canvas.xview)
        scrollable_frame = tk.Frame(canvas, bg=BG)
        
        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(xscrollcommand=scrollbar.set)
        
        canvas.pack(side="top", fill="both", expand=True, padx=10, pady=10)
        scrollbar.pack(side="bottom", fill="x")
        
        for i, node in enumerate(path):
            frame = tk.Frame(scrollable_frame, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
            frame.pack(side="left", padx=10, pady=10, fill="y")
            
            lbl_text = "Start" if i == 0 else f"Step {i}: {ARROW.get(node.action, '')}"
            tk.Label(frame, text=lbl_text, bg=PANEL, fg=WHITE, font=('Segoe UI', 10, 'bold')).pack(pady=5)
            
            c = tk.Canvas(frame, width=80, height=80, bg=PANEL, highlightthickness=0)
            c.pack(padx=10, pady=10)
            draw_board(c, 10, 10, node.state, cell=20, is_goal_state=(i == len(path)-1))
            tk.Label(frame, text=f"[{node.label}]", bg=PANEL, fg=ACCENT, font=('Segoe UI', 9)).pack(pady=(0, 5))


    # ─── Render ───────────────────────────────────
    def _render(self, idx):
        idx = max(0, min(idx, len(self.steps) - 1))
        self.idx  = idx
        step      = self.steps[idx]
        goal_t    = tuple(tuple(r) for r in GOAL)

        self.limit_lbl.config(text=f'  ({len(self.steps)} bước IDS  |  Current Limit={step.limit})')

        # ── Phase banner ──
        phase_cfg = {
            'init':      (ACCENT,  'black', '#2a1215', '🔴', 'INIT'),
            'new_limit': (PURPLE,  'black', '#2d1a3f', '🟣', 'NEW LIMIT'),
            'expand':    (ORANGE,  'black', '#2d1a00', '🟠', 'EXPAND'),
            'found':     (GREEN,   'black', '#0d2818', '🟢', 'FOUND'),
            'cutoff':    ('#e3b341', 'black', '#332b00', '🟡', 'CUTOFF'),
            'failure':   (RED,     'white', '#2a0a0a', '🔴', 'FAIL'),
        }
        pc, fc, banner_bg, icon, badge_txt = phase_cfg.get(step.phase, (GRAY, 'black', PANEL, '⬤', '?'))
        self.banner.config(bg=banner_bg, highlightbackground=pc)
        self.banner.winfo_children()[0].config(bg=banner_bg)
        for w in self.banner.winfo_children()[0].winfo_children():
            w.config(bg=banner_bg)
        self.phase_icon.config(text=icon, fg=pc)
        self.phase_badge.config(text=badge_txt, bg=pc, fg=fc)
        self.desc_lbl.config(text=step.desc, fg=WHITE)
        self.step_lbl.config(text=f'Bước {idx} / {len(self.steps) - 1}', fg=GRAY)

        # ── Current node ──
        self.cur_canvas.delete('all')
        if step.current_node:
            n = step.current_node
            is_g = (n.state == goal_t)
            draw_board(self.cur_canvas, 10, 10, n.state, cell=32, is_goal_state=is_g)
            self.cur_label.config(text=f'Node [{n.label}]')
            self.cur_action.config(text=f'Action: {ARROW.get(n.action, "Start")}' if n.action else 'Action: Start')
            self.cur_depth.config(text=f'Depth: {n.depth}')
            self.cur_parent.config(text=f'Parent: [{n.parent_label}]' if n.parent_label else 'Parent: —')
        else:
            self.cur_label.config(text='—')
            self.cur_action.config(text='')
            self.cur_depth.config(text='')
            self.cur_parent.config(text='')

        # ── Frontier canvas ──
        self._draw_frontier(step)

        # ── Explored canvas ──
        self._draw_explored(step)

    def _draw_frontier(self, step):
        c = self.fr_canvas
        c.delete('all')
        goal_t  = tuple(tuple(r) for r in GOAL)
        col_w   = 160
        item_h  = 90
        pad_x   = 10
        pad_y   = 8

        cw = max(c.winfo_width(), 300)
        cols = max(1, cw // col_w)

        display = []
        has_ghost = False
        for node in step.frontier:
            display.append(('normal', node))
        if step.current_node and step.phase in ('expand', 'found', 'cutoff'):
            display.append(('ghost', step.current_node))
            has_ghost = True

        n_frontier = len(step.frontier)
        show_next  = step.phase in ('init', 'new_limit', 'expand', 'cutoff') and n_frontier > 0

        for i, (kind, node) in enumerate(display):
            col = i % cols
            row = i // cols
            x0  = pad_x + col * col_w
            y0  = pad_y + row * item_h

            is_g     = (node.state == goal_t)
            is_new   = node.label in step.new_labels
            is_ghost = (kind == 'ghost')
            is_next  = show_next and not is_ghost and i == n_frontier - 1

            if is_ghost:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + col_w - 10, y0 + item_h - 4, fill='#111822', outline=GRAY, width=1, dash=(4, 4))
            elif is_next:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + col_w - 10, y0 + item_h - 4, fill='#2a122e', outline=ACCENT, width=2)
            elif is_new:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + col_w - 10, y0 + item_h - 4, fill='#2d2000', outline=ORANGE, width=1)
            elif is_g:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + col_w - 10, y0 + item_h - 4, fill='#0d2818', outline=GREEN, width=1)

            draw_board(c, x0 + 2, y0 + 4, node.state, cell=CELL, highlight='ghost' if is_ghost else None, is_goal_state=is_g if not is_ghost else False)

            tx = x0 + 3 * CELL + 8
            ty = y0 + 4
            ghost_clr = '#484f58'

            if is_ghost:
                c.create_text(tx, ty, text=f'[{node.label}]  ← đang xét', anchor='nw', fill=GRAY, font=('Segoe UI', 8, 'bold'))
                act = ARROW.get(node.action, 'Start') if node.action else 'Start'
                c.create_text(tx, ty + 14, text=f'Act: {act}', anchor='nw', fill=ghost_clr, font=('Consolas', 8))
                c.create_text(tx, ty + 28, text=f'Depth: {node.depth}', anchor='nw', fill=ghost_clr, font=('Consolas', 8))
                par = f'Par: [{node.parent_label}]' if node.parent_label else 'Par: —'
                c.create_text(tx, ty + 42, text=par, anchor='nw', fill=ghost_clr, font=('Consolas', 8))
            else:
                if is_next:
                    tag = '  ⏩NEXT'
                    lbl_col = ACCENT
                elif is_new:
                    tag = '  ★NEW'
                    lbl_col = ORANGE
                elif is_g:
                    tag = ''
                    lbl_col = GREEN
                else:
                    tag = ''
                    lbl_col = ACCENT
                c.create_text(tx, ty, text=f'[{node.label}]{tag}', anchor='nw', fill=lbl_col, font=('Segoe UI', 8, 'bold'))
                act = ARROW.get(node.action, 'Start') if node.action else 'Start'
                c.create_text(tx, ty + 14, text=f'Act: {act}', anchor='nw', fill=WHITE, font=('Consolas', 8))
                c.create_text(tx, ty + 28, text=f'Depth: {node.depth}', anchor='nw', fill=GRAY, font=('Consolas', 8))
                par = f'Par: [{node.parent_label}]' if node.parent_label else 'Par: —'
                c.create_text(tx, ty + 42, text=par, anchor='nw', fill=PURPLE, font=('Consolas', 8))

        total_items = len(display)
        total_rows  = (total_items + cols - 1) // cols if total_items else 1
        total_h     = pad_y * 2 + total_rows * item_h
        c.configure(scrollregion=(0, 0, cw, max(total_h, c.winfo_height())))

        if not display:
            c.create_text(cw // 2, 60, text='∅  (Stack rỗng)', fill=GRAY, font=('Segoe UI', 11))

    def _draw_explored(self, step):
        c = self.ex_canvas
        c.delete('all')
        goal_t = tuple(tuple(r) for r in GOAL)
        item_h = 96
        pad_x  = 10
        pad_y  = 8

        explored = self.explored_master[:step.explored_count]

        for i, node in enumerate(explored):
            y0   = pad_y + i * item_h
            is_g = (node.state == goal_t)

            if i > 0:
                c.create_line(pad_x, y0 - 4, 240, y0 - 4, fill=BORDER, width=1)

            draw_board(c, pad_x, y0 + 4, node.state, cell=CELL, highlight='explored', is_goal_state=is_g)

            tx  = pad_x + 3 * CELL + 8
            ty  = y0 + 4

            c.create_text(tx, ty, text=f'[{node.label}]', anchor='nw', fill=ACCENT, font=('Segoe UI', 8, 'bold'))
            act = ARROW.get(node.action, 'Start') if node.action else 'Start'
            c.create_text(tx, ty + 16, text=f'Act : {act}', anchor='nw', fill=WHITE, font=('Consolas', 8))
            c.create_text(tx, ty + 30, text=f'Dep : {node.depth}', anchor='nw', fill=GRAY, font=('Consolas', 8))
            par = f'Par : [{node.parent_label}]' if node.parent_label else 'Par : —'
            c.create_text(tx, ty + 44, text=par, anchor='nw', fill=PURPLE, font=('Consolas', 8))

        total_h = pad_y * 2 + len(explored) * item_h
        cw = max(c.winfo_width(), 200)
        c.configure(scrollregion=(0, 0, cw, max(total_h, c.winfo_height())))

        if not explored:
            c.create_text(cw // 2, 50, text='∅  (Explored rỗng)', fill=GRAY, font=('Segoe UI', 10))

    def _go_first(self): self._stop(); self._render(0)
    def _go_last(self):  self._stop(); self._render(len(self.steps) - 1)
    def _go_prev(self):  self._stop(); self._render(self.idx - 1)
    def _go_next(self):  self._stop(); self._render(self.idx + 1)

    def _toggle_auto(self):
        if self._auto:
            self._stop()
        else:
            self._auto = True
            self.btn_auto.config(text='⏸ Dừng', bg=RED, fg='white')
            self._tick()

    def _tick(self):
        if not self._auto: return
        if self.idx >= len(self.steps) - 1:
            self._stop(); return
        self._render(self.idx + 1)
        self.root.after(self.speed.get(), self._tick)

    def _stop(self):
        self._auto = False
        self.btn_auto.config(text='▶ Auto', bg=ACCENT, fg='black')

if __name__ == '__main__':
    root = tk.Tk()
    ttk.Style(root).theme_use('clam')
    app = App(root)
    root.mainloop()
