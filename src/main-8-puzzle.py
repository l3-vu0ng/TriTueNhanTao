# ══════════════════════════════════════════════════
# 1. CẤU HÌNH & HẰNG SỐ (CONFIG & CONSTANTS)
# ══════════════════════════════════════════════════

import tkinter as tk
from tkinter import ttk, messagebox
from collections import deque
import heapq
import itertools
import random
import functools

INITIAL_STATE = ((2, 8, 3), (1, 6, 4), (7, 0, 5))
GOAL_STATE = ((1, 2, 3), (8, 0, 4), (7, 6, 5))
MAX_IDS_DEPTH = 31
DFS_DEPTH_LIMIT = 31

MOVE_DIRS = [('U', -1, 0), ('D', 1, 0), ('L', 0, -1), ('R', 0, 1)]
ARROW_MAP = {'U': '↑ U', 'D': '↓ D', 'L': '← L', 'R': '→ R'}
LABELS_LIST = list('ABCDEFGHIJKLMNOPQRSTUVWXYZ') + [f'{c}{i}' for i in range(10) for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ']

# Light Theme Colors
BG = '#ffffff'
PANEL = '#f6f8fa'
BORDER = '#d0d7de'
ACCENT = '#0969da'
GREEN = '#1a7f37'
ORANGE = '#9a6700'
RED = '#cf222e'
GRAY = '#57606a'
PURPLE = '#8250df'
BLACK = '#24292f'
WHITE = '#ffffff'

TILE_BG = '#0969da'
TILE_BLANK = '#f6f8fa'
TILE_NEW = '#bf8700'
TILE_GOAL_C = '#1a7f37'
TILE_EXP = '#eaeef2'

CELL_SIZE = 20

# ══════════════════════════════════════════════════
# 2. HÀM PHỤ TRỢ & TIỆN ÍCH (HELPER FUNCTIONS & UTILS)
# ══════════════════════════════════════════════════

def generateLabel(idx: int) -> str:
    """Generates a sequential label (A-Z, A0-Z0, etc.) for a node."""
    if idx < 26:
        return chr(65 + idx)
    idx -= 26
    return chr(65 + idx % 26) + str(idx // 26)

def drawCSPGraph(canvas, x, y, assignment, cell=CELL_SIZE):
    scale = (cell * 3) / 200.0
    nodes = {
        'WA': (40, 70), 'NT': (100, 40), 'SA': (100, 100),
        'Q': (160, 50), 'NSW': (160, 100), 'V': (140, 140), 'T': (160, 170)
    }
    edges = [
        ('WA', 'NT'), ('WA', 'SA'), ('NT', 'SA'), ('NT', 'Q'),
        ('SA', 'Q'), ('SA', 'NSW'), ('SA', 'V'), ('Q', 'NSW'), ('NSW', 'V')
    ]
    color_map = {'đỏ': '#cf222e', 'xanh lá': '#1a7f37', 'xanh dương': '#0969da', 'none': '#eaeef2'}
    
    assign_dict = dict(assignment) if isinstance(assignment, tuple) else {}
    
    for u, v in edges:
        ux, uy = nodes[u]
        vx, vy = nodes[v]
        canvas.create_line(x + ux * scale, y + uy * scale, x + vx * scale, y + vy * scale, fill='#d0d7de', width=2)
        
    r = 15 * scale
    for node_name, (nx, ny) in nodes.items():
        cx, cy = x + nx * scale, y + ny * scale
        color_name = assign_dict.get(node_name, 'none')
        fill_color = color_map.get(color_name, '#eaeef2')
        canvas.create_oval(cx - r, cy - r, cx + r, cy + r, fill=fill_color, outline='#57606a')
        
        if scale > 0.5:
            text_color = '#ffffff' if fill_color != '#eaeef2' else '#24292f'
            canvas.create_text(cx, cy, text=node_name, fill=text_color, font=('Segoe UI', max(6, int(8*scale)), 'bold'))

def drawCSPArc(canvas, x, y, domains, cell=CELL_SIZE):
    width = 3 * cell
    row_h = width / 3.0
    domains_dict = dict(domains) if isinstance(domains, tuple) else {}
    for i, var in enumerate(['X', 'Y', 'Z']):
        dom = domains_dict.get(var, tuple())
        cy = y + i * row_h
        canvas.create_text(x + 10, cy + row_h/2, text=f"{var}:", font=('Segoe UI', max(10, int(cell*0.2)), 'bold'), anchor='w')
        
        val_x = x + max(50, cell * 0.5)
        box_s = cell * 0.3
        
        for val in [1, 2, 3]:
            if val in dom:
                fill_c = '#0969da'
                txt_c = '#ffffff'
            else:
                fill_c = '#eaeef2'
                txt_c = '#d0d7de'
            
            canvas.create_rectangle(val_x, cy + (row_h - box_s)/2, val_x + box_s, cy + (row_h + box_s)/2, fill=fill_c, outline='#57606a')
            canvas.create_text(val_x + box_s/2, cy + row_h/2, text=str(val), fill=txt_c, font=('Segoe UI', max(8, int(box_s*0.5)), 'bold'))
            val_x += box_s + 10

def drawBoard(canvas, x, y, state, cell=CELL_SIZE, highlight=None, newCells=None, isGoalState=False, knownCells=None):
    """Draws a 3x3 puzzle board on the canvas."""
    # Handle Belief State (tuple of states): just draw the first state for the UI
    if state and isinstance(state[0], tuple) and isinstance(state[0][0], tuple):
        state = state[0]
        
    if state and isinstance(state, tuple) and isinstance(state[0], str):
        if state[0] in ['CSP_Graph', 'CSP_Graph_FC']:
            drawCSPGraph(canvas, x, y, state[1], cell)
            return
        elif state[0] == 'CSP_Arc':
            drawCSPArc(canvas, x, y, state[1], cell)
            return
            
    isGhost = (highlight == 'ghost')
    for r in range(3):
        for c in range(3):
            val = state[r][c]
            cx = x + c * cell
            cy = y + r * cell
            
            if isGhost:
                bg = TILE_BLANK if val == 0 else '#eaeef2'
            elif val == 0:
                bg = TILE_BLANK
            elif knownCells is not None:
                if (r, c) in knownCells:
                    bg = TILE_GOAL_C if isGoalState else '#007bff'
                else:
                    bg = '#ffc107'
            elif isGoalState:
                bg = TILE_GOAL_C
            elif highlight == 'explored':
                bg = TILE_EXP
            elif newCells and (r, c) in newCells:
                bg = TILE_NEW
            else:
                bg = TILE_BG

            canvas.create_rectangle(cx, cy, cx + cell - 1, cy + cell - 1, fill=bg, outline=BORDER, width=1)
            
            if val != 0:
                if bg in ['#007bff', TILE_GOAL_C]:
                    fg = WHITE
                elif bg == '#ffc107':
                    fg = BLACK
                else:
                    fg = GRAY if isGhost else BLACK
                fontSize = max(7, cell // 2 - 2)
                canvas.create_text(cx + cell // 2, cy + cell // 2, text=str(val), fill=fg, font=('Segoe UI', fontSize, 'bold'))

@functools.lru_cache(maxsize=8192)
def calculateManhattanDistance(state, goalState) -> int:
    """Calculates the Manhattan distance between two states."""
    dist = 0
    goalPos = {}
    for r in range(3):
        for c in range(3):
            val = goalState[r][c]
            if val != 0:
                goalPos[val] = (r, c)
                
    for r in range(3):
        for c in range(3):
            val = state[r][c]
            if val != 0:
                gr, gc = goalPos[val]
                dist += abs(r - gr) + abs(c - gc)
    return dist

@functools.lru_cache(maxsize=8192)
def calculateMisplacedTiles(state, goalState) -> int:
    """Calculates the number of misplaced tiles (excluding the blank tile)."""
    count = 0
    for r in range(3):
        for c in range(3):
            if state[r][c] != 0 and state[r][c] != goalState[r][c]:
                count += 1
    return count

@functools.lru_cache(maxsize=8192)
def calculateInversions(state) -> int:
    """Calculates the number of inversions in the state."""
    lst = []
    for r in range(3):
        for c in range(3):
            if state[r][c] != 0:
                lst.append(state[r][c])
    inversions = 0
    for i in range(len(lst)):
        for j in range(i + 1, len(lst)):
            if lst[i] > lst[j]:
                inversions += 1
    return inversions

# ══════════════════════════════════════════════════
# 3. CẤU TRÚC DỮ LIỆU (DATA STRUCTURES)
# ══════════════════════════════════════════════════

class NodeInfo:
    """Represents a node in the search tree."""
    def __init__(self, state, action=None, depth=0, cost=0, parentLabel=None, label='?', parent=None, g=0, h=0):
        self.state = state
        self.action = action
        self.depth = depth
        self.cost = cost
        self.parentLabel = parentLabel
        self.label = label
        self.parent = parent
        self.g = g
        self.h = h

class StepInfo:
    """Represents a snapshot of the algorithm at a single step."""
    def __init__(self, phase, currentNode, frontier, explored, newLabels, desc, limit=None, exploredCount=None, known_positions=None):
        self.phase = phase           # 'init' | 'expand' | 'found' | 'failure' | 'cutoff' | 'new_limit'
        self.currentNode = currentNode    
        self.frontier = frontier        
        self.explored = explored        
        self.newLabels = newLabels      
        self.desc = desc
        self.limit = limit              # Used by IDS
        self.exploredCount = exploredCount # Used by DFS/IDS to refer to master explored list
        self.known_positions = known_positions

def hasCycle(node: NodeInfo) -> bool:
    """Returns True if the node's state exists in its parent ancestry."""
    curr = node.parent
    while curr:
        if curr.state == node.state:
            return True
        curr = curr.parent
    return False

def findZero(state) -> tuple:
    """Finds the coordinates of the blank tile (0)."""
    for r in range(3):
        for c in range(3):
            if state[r][c] == 0:
                return r, c
    return -1, -1

def applyMove(state, direction) -> tuple:
    """Returns a new state after applying the given move direction, or None if invalid."""
    dr, dc = next((dr, dc) for n, dr, dc in MOVE_DIRS if n == direction)
    r, c = findZero(state)
    nr, nc = r + dr, c + dc
    if 0 <= nr < 3 and 0 <= nc < 3:
        lst = [list(row) for row in state]
        lst[r][c], lst[nr][nc] = lst[nr][nc], lst[r][c]
        return tuple(tuple(x) for x in lst)
    return None

def countCorrectPositions(state, goalState) -> int:
    """Counts the number of tiles in the correct position for UCS heuristic variation."""
    count = 0
    for r in range(3):
        for c in range(3):
            if state[r][c] == goalState[r][c]:
                count += 1
    return count

def generateRandomSolvableState(goalState, moves=10) -> tuple:
    """Generates a solvable state by applying a sequence of random moves from the goal state."""
    currentState = goalState
    # Keep track of visited states during the walk to prevent simple backtracking
    visited = {currentState}
    
    for _ in range(moves):
        possibleStates = []
        for dirName, dr, dc in MOVE_DIRS:
            nextState = applyMove(currentState, dirName)
            if nextState is not None:
                possibleStates.append(nextState)
        
        # We prefer unvisited states to maximize state space exploration and prevent dead loops
        unvisited = [s for s in possibleStates if s not in visited]
        if unvisited:
            currentState = random.choice(unvisited)
        else:
            currentState = random.choice(possibleStates)
        visited.add(currentState)
        
    return currentState

# ══════════════════════════════════════════════════
# 4. THUẬT TOÁN TÌM KIẾM CỐT LÕI (CORE SEARCH ALGORITHMS)
# ══════════════════════════════════════════════════

class SearchEngine:
    """Encapsulates the 4 search algorithms."""
    
    @staticmethod
    def runBfs(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]

        def createNode(state, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            labelIndex[0] += 1
            return n

        steps = []
        start = createNode(initial)

        frontierQueue = deque([start])
        frontierMap = {start.state: start}
        exploredList = []
        exploredSet = set()

        descInit = f"Khởi tạo Thuật toán BFS:\n👉 Tạo trạng thái xuất phát Node [{start.label}].\n👉 Đưa Node này vào Queue (Frontier) để bắt đầu duyệt."
        steps.append(StepInfo('init', None, list(frontierQueue), [], {start.label}, descInit))

        while frontierQueue:
            node = frontierQueue.popleft()
            frontierMap.pop(node.state, None)

            if node.state == goalTuple:
                descFound = f"Lấy Node [{node.label}] ra khỏi Queue để xét:\n👉 Trạng thái này CHÍNH LÀ ĐÍCH (GOAL)!\n👉 Thuật toán tìm kiếm thành công và dừng lại."
                steps.append(StepInfo('found', node, list(frontierQueue), list(exploredList), set(), descFound))
                return steps, exploredList

            exploredList.append(node)
            exploredSet.add(node.state)

            newLabels = set()
            foundGoal = False
            foundChild = None

            for dirName, dr, dc in MOVE_DIRS:
                childState = applyMove(node.state, dirName)
                if childState is None:
                    continue
                if childState in exploredSet or childState in frontierMap:
                    continue

                child = createNode(childState, dirName, node.depth + 1, node)

                if childState == goalTuple:
                    foundGoal = True
                    foundChild = child
                    newLabels.add(child.label)
                    break

                frontierQueue.append(child)
                frontierMap[childState] = child
                newLabels.add(child.label)

            if foundGoal:
                descExp = f"Mở rộng Node [{node.label}]:\n👉 Sinh ra {len(newLabels)} Node con hợp lệ.\n👉 Phát hiện Node con [{foundChild.label}] là ĐÍCH (GOAL)!"
                steps.append(StepInfo('expand', node, list(frontierQueue), list(exploredList), newLabels, descExp))
                descFound = f"Hoàn tất duyệt sớm:\n👉 Node [{foundChild.label}] đạt trạng thái Goal nên thuật toán dừng lại thành công."
                steps.append(StepInfo('found', foundChild, list(frontierQueue), list(exploredList), {foundChild.label}, descFound))
                return steps, exploredList

            descExp = f"Mở rộng Node [{node.label}]:\n👉 Sinh ra {len(newLabels)} Node con mới.\n👉 Thêm các Node con này vào cuối Queue (Frontier)."
            steps.append(StepInfo('expand', node, list(frontierQueue), list(exploredList), newLabels, descExp))

        descFail = "Thất bại:\n👉 Frontier (Queue) đã rỗng mà không tìm thấy Goal.\n👉 Không có đường đi nào tới đích."
        steps.append(StepInfo('failure', None, [], list(exploredList), set(), descFail))
        return steps, exploredList

    @staticmethod
    def runDfs(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]

        def createNode(state, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            labelIndex[0] += 1
            return n

        steps = []
        start = createNode(initial)

        frontierStack = [start]
        frontierSet = {start.state}
        exploredList = []
        exploredSet = set()

        descInit = f"Khởi tạo Thuật toán DFS:\n👉 Tạo trạng thái xuất phát Node [{start.label}].\n👉 Đưa Node này vào Stack (Frontier) để duyệt sâu."
        steps.append(StepInfo('init', None, list(frontierStack), [], {start.label}, descInit, exploredCount=0))

        while frontierStack:
            node = frontierStack.pop()
            frontierSet.discard(node.state)

            if node.state == goalTuple:
                descFound = f"Lấy Node [{node.label}] ở đỉnh Stack ra để xét:\n👉 Trạng thái này CHÍNH LÀ ĐÍCH (GOAL)!\n👉 Thuật toán tìm kiếm thành công và dừng lại."
                steps.append(StepInfo('found', node, list(frontierStack), [], set(), descFound, exploredCount=len(exploredList)))
                return steps, exploredList

            if node.depth >= DFS_DEPTH_LIMIT:
                descLimit = f"Node [{node.label}] bị huỷ:\n👉 Đã đạt tới độ sâu tối đa ({DFS_DEPTH_LIMIT}).\n👉 Bỏ qua việc mở rộng Node này để chống vòng lặp vô hạn."
                steps.append(StepInfo('expand', node, list(frontierStack), [], set(), descLimit, exploredCount=len(exploredList)))
                continue

            exploredList.append(node)
            exploredSet.add(node.state)

            newLabels = set()

            for dirName, dr, dc in reversed(MOVE_DIRS):
                childState = applyMove(node.state, dirName)
                if childState is None:
                    continue
                if childState in exploredSet or childState in frontierSet:
                    continue

                child = createNode(childState, dirName, node.depth + 1, node)
                frontierStack.append(child)
                frontierSet.add(childState)
                newLabels.add(child.label)

            descExp = f"Mở rộng Node [{node.label}]:\n👉 Sinh ra {len(newLabels)} Node con mới.\n👉 Thêm các Node con này vào ĐỈNH Stack (để ưu tiên duyệt sâu)."
            steps.append(StepInfo('expand', node, list(frontierStack), [], newLabels, descExp, exploredCount=len(exploredList)))

        descFail = "Thất bại:\n👉 Stack đã rỗng mà không tìm thấy Goal.\n👉 Không có đường đi nào tới đích."
        steps.append(StepInfo('failure', None, [], [], set(), descFail, exploredCount=len(exploredList)))
        return steps, exploredList

    @staticmethod
    def runIds(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs Iterative Deepening Search (IDS)."""
        goalTuple = tuple(tuple(r) for r in goal)
        steps: list[StepInfo] = []
        exploredMaster: list[NodeInfo] = []

        for limit in range(MAX_IDS_DEPTH):
            labelIndex = [0]
            def createNode(state: tuple, action: str = None, depth: int = 0, parentNode: NodeInfo = None) -> NodeInfo:
                parentLabel = parentNode.label if parentNode else None
                n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
                labelIndex[0] += 1
                return n

            start = createNode(initial)
            frontierStack = [start]

            descInit = f"--- BẮT ĐẦU DLS VỚI LIMIT = {limit} ---\n👉 Khởi tạo lại thuật toán duyệt sâu (DFS) nhưng giới hạn độ sâu.\n👉 Đưa Node [{start.label}] vào Stack (Frontier)."
            steps.append(StepInfo('new_limit', None, list(frontierStack), [], {start.label}, descInit, limit=limit, exploredCount=len(exploredMaster)))

            dlsResult = 'failure'

            while frontierStack:
                node = frontierStack.pop()

                if node.state == goalTuple:
                    descFound = f"Lấy Node [{node.label}] ở đỉnh Stack ra để xét:\n👉 Trạng thái này CHÍNH LÀ ĐÍCH (GOAL)!\n👉 Tìm thấy giải pháp tại Limit={limit}."
                    steps.append(StepInfo('found', node, list(frontierStack), [], set(), descFound, limit=limit, exploredCount=len(exploredMaster)))
                    return steps, exploredMaster

                if node.depth >= limit:
                    dlsResult = 'cutoff'
                    descCutoff = f"Node [{node.label}] bị Cutoff:\n👉 Đã chạm tới Limit hiện tại ({limit}).\n👉 Tạm ngưng mở rộng nhánh này để duyệt nhánh khác."
                    steps.append(StepInfo('cutoff', node, list(frontierStack), [], set(), descCutoff, limit=limit, exploredCount=len(exploredMaster)))
                    continue

                if hasCycle(node):
                    continue

                exploredMaster.append(node)
                newLabels = set()

                for dirName, dr, dc in reversed(MOVE_DIRS):
                    childState = applyMove(node.state, dirName)
                    if childState is None:
                        continue

                    child = createNode(childState, dirName, node.depth + 1, node)
                    frontierStack.append(child)
                    newLabels.add(child.label)

                descExp = f"Mở rộng Node [{node.label}]:\n👉 Sinh ra {len(newLabels)} Node con hợp lệ.\n👉 Thêm các Node con này vào ĐỈNH Stack (để ưu tiên duyệt sâu)."
                steps.append(StepInfo('expand', node, list(frontierStack), [], newLabels, descExp, limit=limit, exploredCount=len(exploredMaster)))

            if dlsResult != 'cutoff':
                descFail = f"Limit={limit} trả về Failure hoàn toàn:\n👉 Đã duyệt sạch không còn nhánh nào bị Cutoff.\n👉 Đồng nghĩa bài toán Vô nghiệm."
                steps.append(StepInfo('failure', None, [], [], set(), descFail, limit=limit, exploredCount=len(exploredMaster)))
                return steps, exploredMaster
            else:
                descNext = f"Quá trình DLS tại Limit={limit} bị Cutoff (còn nhánh chưa xét):\n👉 Cần mở rộng độ sâu.\n👉 Tăng Limit lên {limit+1} và thử lại từ đầu."
                steps.append(StepInfo('cutoff', None, [], [], set(), descNext, limit=limit, exploredCount=len(exploredMaster)))

        descMax = f"Thất bại:\n👉 Vượt quá MAX_IDS_DEPTH ({MAX_IDS_DEPTH}).\n👉 Thuật toán chủ động dừng lại."
        steps.append(StepInfo('failure', None, [], [], set(), descMax, limit=MAX_IDS_DEPTH, exploredCount=len(exploredMaster)))
        return steps, exploredMaster

    @staticmethod
    def runUcs(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]

        def createNode(state, action=None, depth=0, cost=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, cost, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            labelIndex[0] += 1
            return n

        steps = []
        start = createNode(initial, cost=0)

        frontierQueue = []
        counter = itertools.count()
        heapq.heappush(frontierQueue, (start.cost, next(counter), start))

        frontierMap = {start.state: start.cost}
        exploredList = []
        exploredSet = set()

        descInit = f"Khởi tạo Thuật toán UCS:\n👉 Tạo trạng thái xuất phát Node [{start.label}].\n👉 Đưa Node này vào Priority Queue với Cost ban đầu = 0."
        steps.append(StepInfo('init', None, [n for _, _, n in sorted(frontierQueue)], [], {start.label}, descInit))

        while frontierQueue:
            currentCost, _, node = heapq.heappop(frontierQueue)

            if node.state in exploredSet:
                continue

            frontierMap.pop(node.state, None)

            if node.state == goalTuple:
                exploredList.append(node)
                descFound = f"Lấy Node [{node.label}] ra xét:\n👉 Trạng thái này CHÍNH LÀ ĐÍCH (GOAL)!\n👉 Chi phí (Cost) tối ưu tìm được là {node.cost}."
                steps.append(StepInfo('found', node, [n for _, _, n in sorted(frontierQueue)], list(exploredList), set(), descFound))
                return steps, exploredList

            exploredList.append(node)
            exploredSet.add(node.state)

            newLabels = set()
            childrenCandidates = []

            for dirName, dr, dc in MOVE_DIRS:
                childState = applyMove(node.state, dirName)
                if childState is None:
                    continue
                correctTiles = countCorrectPositions(childState, goalTuple)
                childrenCandidates.append({
                    'state': childState,
                    'action': dirName,
                    'correct': correctTiles
                })

            childrenCandidates.sort(key=lambda x: x['correct'], reverse=True)

            currentRank = 0
            lastCorrect = None
            for cand in childrenCandidates:
                if cand['correct'] != lastCorrect:
                    currentRank += 1
                    lastCorrect = cand['correct']

                stepCost = currentRank
                childState = cand['state']
                dirName = cand['action']
                childCost = node.cost + stepCost

                if childState in exploredSet:
                    continue

                if childState not in frontierMap or childCost < frontierMap[childState]:
                    child = createNode(childState, dirName, node.depth + 1, childCost, node)
                    frontierMap[childState] = childCost
                    heapq.heappush(frontierQueue, (childCost, next(counter), child))
                    newLabels.add(child.label)

            descExp = f"Mở rộng Node [{node.label}] (Cost hiện tại = {node.cost}):\n👉 Sinh ra {len(newLabels)} Node con hợp lệ.\n👉 Đưa các Node con này vào Priority Queue theo Cost tăng dần."
            steps.append(StepInfo('expand', node, [n for _, _, n in sorted(frontierQueue)], list(exploredList), newLabels, descExp))

        descFail = "Thất bại:\n👉 Priority Queue đã rỗng mà không tìm thấy Goal.\n👉 Không có đường đi nào tới đích."
        steps.append(StepInfo('failure', None, [], list(exploredList), set(), descFail))
        return steps, exploredList

    @staticmethod
    def runGreedySearch(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]
        
        def createNode(state, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateManhattanDistance(state, goalTuple)
            labelIndex[0] += 1
            return n

        steps = []
        start = createNode(initial)
        
        frontier = [start]
        reached = {}
        
        descInit = f"Khởi tạo Greedy-Search:\n👉 FRONTIER = {{ [{start.label}] }}\n👉 Tính h(Start) = {start.h} (Manhattan)"
        steps.append(StepInfo('init', None, list(frontier), list(reached.values()), {start.label}, descInit))
        
        while frontier:
            frontier.sort(key=lambda x: x.h)
            node = frontier.pop(0)
            
            if node.state == goalTuple:
                reached[node.state] = node
                descFound = f"Lấy Node [{node.label}] ra xét:\n👉 Trạng thái CHÍNH LÀ ĐÍCH (h={node.h})!\n👉 Thuật toán thành công."
                steps.append(StepInfo('found', node, sorted(frontier, key=lambda x: x.h), list(reached.values()), set(), descFound))
                return steps, list(reached.values())
                
            reached[node.state] = node
            
            newLabels = set()
            for dirName, dr, dc in MOVE_DIRS:
                childState = applyMove(node.state, dirName)
                if childState is None:
                    continue
                    
                inFrontier = next((n for n in frontier if n.state == childState), None)
                inReached = childState in reached
                
                if not inFrontier and not inReached:
                    child = createNode(childState, dirName, node.depth + 1, node)
                    frontier.append(child)
                    newLabels.add(child.label)
                elif inFrontier or inReached:
                    pass # Bỏ qua m
                    
            descExp = f"Mở rộng Node [{node.label}] (h={node.h}):\n👉 Thêm {len(newLabels)} node con hợp lệ vào FRONTIER."
            steps.append(StepInfo('expand', node, sorted(frontier, key=lambda x: x.h), list(reached.values()), newLabels, descExp))
            
        descFail = "Thất bại:\n👉 FRONTIER rỗng mà không tìm thấy Goal."
        steps.append(StepInfo('failure', None, [], list(reached.values()), set(), descFail))
        return steps, list(reached.values())

    @staticmethod
    def runAStar(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]
        
        def createNode(state, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateMisplacedTiles(state, goalTuple)
            labelIndex[0] += 1
            return n

        steps = []
        start = createNode(initial)
        start.g = 0
        start.cost = start.g + start.h
        
        frontier = [start]
        reached = {}
        
        descInit = f"Khởi tạo A*:\n👉 FRONTIER = {{ [{start.label}] }}\n👉 f(Start) = g(0) + h({start.h}) = {start.cost}"
        steps.append(StepInfo('init', None, list(frontier), list(reached.values()), {start.label}, descInit))
        
        while frontier:
            frontier.sort(key=lambda x: x.cost)
            node = frontier.pop(0)
            
            if node.state == goalTuple:
                reached[node.state] = node
                descFound = f"Lấy Node [{node.label}] ra xét:\n👉 Trạng thái CHÍNH LÀ ĐÍCH!\n👉 Thuật toán thành công."
                steps.append(StepInfo('found', node, sorted(frontier, key=lambda x: x.cost), list(reached.values()), set(), descFound))
                return steps, list(reached.values())
                
            reached[node.state] = node
            
            newLabels = set()
            for dirName, dr, dc in MOVE_DIRS:
                childState = applyMove(node.state, dirName)
                if childState is None:
                    continue
                
                costM = calculateInversions(childState)
                gNew = node.g + costM
                
                inReached = reached.get(childState)
                inFrontierIdx = next((i for i, n in enumerate(frontier) if n.state == childState), -1)
                
                if inReached:
                    if gNew >= inReached.g:
                        continue
                    else:
                        del reached[childState]
                        inReached.g = gNew
                        inReached.cost = inReached.g + inReached.h
                        inReached.parent = node
                        inReached.parentLabel = node.label
                        inReached.action = dirName
                        inReached.depth = node.depth + 1
                        frontier.append(inReached)
                        newLabels.add(inReached.label)
                elif inFrontierIdx != -1:
                    m = frontier[inFrontierIdx]
                    if gNew < m.g:
                        m.g = gNew
                        m.cost = m.g + m.h
                        m.parent = node
                        m.parentLabel = node.label
                        m.action = dirName
                        m.depth = node.depth + 1
                        newLabels.add(m.label)
                else:
                    child = createNode(childState, dirName, node.depth + 1, node)
                    child.g = gNew
                    child.cost = child.g + child.h
                    frontier.append(child)
                    newLabels.add(child.label)
                    
            descExp = f"Mở rộng Node [{node.label}] (f={node.cost}):\n👉 Xử lý {len(newLabels)} node con hợp lệ."
            steps.append(StepInfo('expand', node, sorted(frontier, key=lambda x: x.cost), list(reached.values()), newLabels, descExp))
            
        descFail = "Thất bại:\n👉 FRONTIER rỗng mà không tìm thấy Goal."
        steps.append(StepInfo('failure', None, [], list(reached.values()), set(), descFail))
        return steps, list(reached.values())

    @staticmethod
    def runMultiStartAStar(initials: list[tuple], goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        goalTuple = tuple(tuple(r) for r in goal)
        joint_actions = []
        
        # Greedy helper for a single board
        def solve_single(start_state, goal_state):
            if start_state == goal_state:
                return []
            
            # queue element: (h, state, path)
            queue = [(calculateManhattanDistance(start_state, goal_state), start_state, [])]
            visited = {start_state}
            
            while queue:
                queue.sort(key=lambda x: x[0])
                h, curr, path = queue.pop(0)
                
                if curr == goal_state:
                    return path
                    
                for dirName, dr, dc in MOVE_DIRS:
                    next_s = applyMove(curr, dirName)
                    if next_s is not None and next_s not in visited:
                        visited.add(next_s)
                        new_path = path + [dirName]
                        next_h = calculateManhattanDistance(next_s, goal_state)
                        queue.append((next_h, next_s, new_path))
            return []

        # Try to find the joint path of actions using a joint Greedy Search (optimizing the sum of h(n) of all boards)
        # We limit the search to 10000 expanded nodes to prevent UI freeze.
        # If it fails or hits the limit, we fall back to the sequential greedy solver.
        
        k = len(initials)
        # queue element: (h_total, g, joint_state, path, reached_steps)
        # reached_steps[j] stores the step index where board j first reached Goal (None if not yet)
        start_reached = tuple(0 if s == goalTuple else None for s in initials)
        start_h = sum(0 if s == goalTuple else calculateManhattanDistance(s, goalTuple) for s in initials)
        
        queue = [(start_h, 0, tuple(initials), [], start_reached)]
        visited = {tuple(initials)}
        
        joint_actions = None
        nodes_expanded = 0
        max_nodes = 10000
        
        while queue and nodes_expanded < max_nodes:
            h_total, g, curr_states, path, reached = heapq.heappop(queue)
            nodes_expanded += 1
            
            if all(s == goalTuple for s in curr_states):
                joint_actions = path
                break
                
            for move, _, _ in MOVE_DIRS:
                next_states = []
                next_reached = list(reached)
                for j in range(k):
                    s = curr_states[j]
                    if s == goalTuple:
                        next_states.append(s)
                    else:
                        nxt = applyMove(s, move)
                        if nxt is not None:
                            next_states.append(nxt)
                            if nxt == goalTuple:
                                next_reached[j] = g + 1
                        else:
                            next_states.append(s)
                
                next_states_tuple = tuple(next_states)
                if next_states_tuple not in visited:
                    visited.add(next_states_tuple)
                    
                    next_h = 0
                    for j in range(k):
                        s = next_states_tuple[j]
                        if next_reached[j] is None:
                            next_h += calculateManhattanDistance(s, goalTuple)
                            
                    heapq.heappush(queue, (next_h, g + 1, next_states_tuple, path + [move], tuple(next_reached)))
                    
        if joint_actions is None:
            # Fallback to sequential greedy solver
            joint_actions = []
            for j in range(len(initials)):
                board_state = initials[j]
                for act in joint_actions:
                    if board_state == goalTuple:
                        break
                    next_s = applyMove(board_state, act)
                    if next_s is not None:
                        board_state = next_s
                
                if board_state != goalTuple:
                    path = solve_single(board_state, goalTuple)
                    joint_actions.extend(path)
                
        # Let's generate the StepInfo list by simulating the sequence step-by-step
        steps = []
        explored = []
        
        labelIndex = [0]
        def createNode(states: tuple, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(states, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            sum_h = 0
            for s in states:
                if s != goalTuple:
                    sum_h += calculateManhattanDistance(s, goalTuple)
            n.h = sum_h
            n.cost = sum_h # For Greedy Search, cost is just h(n)
            labelIndex[0] += 1
            return n

        curr_states_tuple = tuple(initials)
        curr_node = createNode(curr_states_tuple)
        curr_node.g = 0
        curr_node.cost = curr_node.h
        
        descInit = f"Khởi tạo Multi-Start Greedy:\n👉 Tìm thấy chuỗi hành động tối ưu giải tất cả các bảng.\n👉 Chuỗi nước đi chung gồm {len(joint_actions)} bước."
        steps.append(StepInfo('init', curr_node, [curr_node], [], {curr_node.label}, descInit))
        
        for idx, act in enumerate(joint_actions):
            explored.append(curr_node)
            next_states = []
            for s in curr_node.state:
                if s == goalTuple:
                    next_states.append(s)
                else:
                    child_s = applyMove(s, act)
                    if child_s is not None:
                        next_states.append(child_s)
                    else:
                        next_states.append(s)
            
            next_states_tuple = tuple(next_states)
            next_node = createNode(next_states_tuple, act, curr_node.depth + 1, curr_node)
            next_node.g = curr_node.g + 1
            next_node.cost = next_node.h
            
            is_last = (idx == len(joint_actions) - 1)
            phase = 'found' if is_last else 'expand'
            
            active_count = sum(1 for s in next_states_tuple if s != goalTuple)
            if phase == 'found':
                desc = f"Bước {idx+1} - Di chuyển {ARROW_MAP.get(act, act)}:\n👉 Tất cả các bảng đã đạt GOAL thành công!"
            else:
                desc = f"Bước {idx+1} - Di chuyển {ARROW_MAP.get(act, act)}:\n👉 Còn {active_count} bảng chưa đạt Goal. Tiếp tục di chuyển..."
                
            steps.append(StepInfo(phase, next_node, [next_node], list(explored), {next_node.label}, desc))
            curr_node = next_node
            
        return steps, explored

    @staticmethod
    def runSimpleHillClimbing(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs Simple Hill Climbing search to minimize Manhattan distance."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]

        def createNode(state: tuple, action: str = None, depth: int = 0, parentNode: NodeInfo = None) -> NodeInfo:
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateManhattanDistance(state, goalTuple)
            labelIndex[0] += 1
            return n

        steps: list[StepInfo] = []
        exploredList: list[NodeInfo] = []

        currentNode = createNode(initial)

        if currentNode.state == goalTuple:
            descFound = f"Khởi tạo Simple Hill Climbing:\n👉 Trạng thái bắt đầu [{currentNode.label}] (h={currentNode.h}) chính là ĐÍCH (GOAL)!"
            steps.append(StepInfo('found', currentNode, [], [currentNode], set(), descFound))
            exploredList.append(currentNode)
            return steps, exploredList

        descInit = f"Khởi tạo Simple Hill Climbing:\n👉 Trạng thái hiện tại: [{currentNode.label}] (h={currentNode.h})\n👉 Đặt làm Current_State để bắt đầu tìm kiếm."
        steps.append(StepInfo('init', currentNode, [currentNode], list(exploredList), {currentNode.label}, descInit))

        while True:
            neighbors: list[NodeInfo] = []
            for dirName, dr, dc in MOVE_DIRS:
                childState = applyMove(currentNode.state, dirName)
                if childState is not None:
                    childNode = createNode(childState, dirName, currentNode.depth + 1, currentNode)
                    neighbors.append(childNode)

            if not neighbors:
                exploredList.append(currentNode)
                descFail = f"Thất bại:\n👉 Node [{currentNode.label}] (h={currentNode.h}) không có lân cận nào hợp lệ."
                steps.append(StepInfo('failure', currentNode, [], list(exploredList), set(), descFail))
                return steps, exploredList

            foundBetter = False
            betterNode = None
            checkedNeighbors: list[NodeInfo] = []

            for childNode in neighbors:
                checkedNeighbors.append(childNode)
                if childNode.h < currentNode.h:
                    betterNode = childNode
                    foundBetter = True
                    break

            if foundBetter:
                descExp = (
                    f"Mở rộng Node [{currentNode.label}] (h={currentNode.h}):\n"
                    f"👉 Xét lần lượt lân cận. Phát hiện lân cận [{betterNode.label}] (h={betterNode.h}) tốt hơn (nhỏ hơn).\n"
                    f"👉 Di chuyển ngay sang Node [{betterNode.label}]."
                )
                steps.append(StepInfo('expand', currentNode, checkedNeighbors, list(exploredList) + [currentNode], {n.label for n in checkedNeighbors}, descExp))
                exploredList.append(currentNode)
                currentNode = betterNode

                if currentNode.state == goalTuple:
                    descFound = (
                        f"Lấy Node [{currentNode.label}] ra xét:\n"
                        f"👉 Trạng thái CHÍNH LÀ ĐÍCH (GOAL) (h=0)!\n"
                        f"👉 Thuật toán tìm kiếm thành công."
                    )
                    steps.append(StepInfo('found', currentNode, [], list(exploredList) + [currentNode], set(), descFound))
                    exploredList.append(currentNode)
                    return steps, exploredList
            else:
                # Local maximum reached: explain details of all checked neighbors
                exploredList.append(currentNode)
                neighborDetails = ", ".join([f"[{n.label}] h={n.h} ({ARROW_MAP.get(n.action, '')})" for n in neighbors])
                descFail = (
                    f"Thất bại (Cực đại cục bộ / Local Maximum):\n"
                    f"👉 Trạng thái hiện tại [{currentNode.label}] (h={currentNode.h}) không phải là Goal.\n"
                    f"👉 Đã xét toàn bộ {len(neighbors)} lân cận: {neighborDetails}.\n"
                    f"👉 Không có lân cận nào có giá trị h tốt hơn (nhỏ hơn {currentNode.h}). Thuật toán dừng lại."
                )
                steps.append(StepInfo('failure', currentNode, neighbors, list(exploredList), set(), descFail))
                return steps, exploredList

    @staticmethod
    def runSteepestAscentHillClimbing(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs Steepest-Ascent Hill Climbing search to minimize Manhattan distance."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]

        def createNode(state: tuple, action: str = None, depth: int = 0, parentNode: NodeInfo = None) -> NodeInfo:
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateManhattanDistance(state, goalTuple)
            labelIndex[0] += 1
            return n

        steps: list[StepInfo] = []
        exploredList: list[NodeInfo] = []

        currentNode = createNode(initial)

        if currentNode.state == goalTuple:
            descFound = f"Khởi tạo Steepest-Ascent Hill Climbing:\n👉 Trạng thái bắt đầu [{currentNode.label}] (h={currentNode.h}) chính là ĐÍCH (GOAL)!"
            steps.append(StepInfo('found', currentNode, [], [currentNode], set(), descFound))
            exploredList.append(currentNode)
            return steps, exploredList

        descInit = f"Khởi tạo Steepest-Ascent Hill Climbing:\n👉 Trạng thái hiện tại: [{currentNode.label}] (h={currentNode.h})\n👉 Đặt làm Current_State để bắt đầu tìm kiếm."
        steps.append(StepInfo('init', currentNode, [currentNode], list(exploredList), {currentNode.label}, descInit))

        while True:
            neighbors: list[NodeInfo] = []
            for dirName, dr, dc in MOVE_DIRS:
                childState = applyMove(currentNode.state, dirName)
                if childState is not None:
                    childNode = createNode(childState, dirName, currentNode.depth + 1, currentNode)
                    neighbors.append(childNode)

            if not neighbors:
                exploredList.append(currentNode)
                descFail = f"Thất bại:\n👉 Node [{currentNode.label}] (h={currentNode.h}) không có lân cận nào hợp lệ."
                steps.append(StepInfo('failure', currentNode, [], list(exploredList), set(), descFail))
                return steps, exploredList

            # Determine steepest step
            bestNode = min(neighbors, key=lambda x: x.h)

            if bestNode.h < currentNode.h:
                descExp = (
                    f"Mở rộng Node [{currentNode.label}] (h={currentNode.h}):\n"
                    f"👉 Xét tất cả {len(neighbors)} lân cận. Lân cận tốt nhất là [{bestNode.label}] (h={bestNode.h}).\n"
                    f"👉 Vì {bestNode.h} < {currentNode.h}, di chuyển sang Node [{bestNode.label}]."
                )
                steps.append(StepInfo('expand', currentNode, neighbors, list(exploredList) + [currentNode], {n.label for n in neighbors}, descExp))
                exploredList.append(currentNode)
                currentNode = bestNode

                if currentNode.state == goalTuple:
                    descFound = (
                        f"Lấy Node [{currentNode.label}] ra xét:\n"
                        f"👉 Trạng thái CHÍNH LÀ ĐÍCH (GOAL) (h=0)!\n"
                        f"👉 Thuật toán tìm kiếm thành công."
                    )
                    steps.append(StepInfo('found', currentNode, [], list(exploredList) + [currentNode], set(), descFound))
                    exploredList.append(currentNode)
                    return steps, exploredList
            else:
                # Local maximum reached: explain details of all checked neighbors
                exploredList.append(currentNode)
                neighborDetails = ", ".join([f"[{n.label}] h={n.h} ({ARROW_MAP.get(n.action, '')})" for n in neighbors])
                descFail = (
                    f"Thất bại (Cực đại cục bộ / Local Maximum):\n"
                    f"👉 Trạng thái hiện tại [{currentNode.label}] (h={currentNode.h}) không phải là Goal.\n"
                    f"👉 Đã xét toàn bộ {len(neighbors)} lân cận: {neighborDetails}.\n"
                    f"👉 Lân cận tốt nhất là [{bestNode.label}] (h={bestNode.h}) không tốt hơn (nhỏ hơn) giá trị hiện tại {currentNode.h}.\n"
                    f"👉 Thuật toán dừng lại."
                )
                steps.append(StepInfo('failure', currentNode, neighbors, list(exploredList), set(), descFail))
                return steps, exploredList

    @staticmethod
    def runStochasticHillClimbing(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs Stochastic Hill Climbing search to minimize Manhattan distance."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]

        def createNode(state: tuple, action: str = None, depth: int = 0, parentNode: NodeInfo = None) -> NodeInfo:
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateManhattanDistance(state, goalTuple)
            labelIndex[0] += 1
            return n

        steps: list[StepInfo] = []
        exploredList: list[NodeInfo] = []

        currentNode = createNode(initial)

        if currentNode.state == goalTuple:
            descFound = f"Khởi tạo Stochastic Hill Climbing:\n👉 Trạng thái bắt đầu [{currentNode.label}] (h={currentNode.h}) chính là ĐÍCH (GOAL)!"
            steps.append(StepInfo('found', currentNode, [], [currentNode], set(), descFound))
            exploredList.append(currentNode)
            return steps, exploredList

        descInit = f"Khởi tạo Stochastic Hill Climbing:\n👉 Trạng thái hiện tại: [{currentNode.label}] (h={currentNode.h})\n👉 Đặt làm Current_State để bắt đầu tìm kiếm."
        steps.append(StepInfo('init', currentNode, [currentNode], list(exploredList), {currentNode.label}, descInit))

        while True:
            neighbors: list[NodeInfo] = []
            for dirName, dr, dc in MOVE_DIRS:
                childState = applyMove(currentNode.state, dirName)
                if childState is not None:
                    childNode = createNode(childState, dirName, currentNode.depth + 1, currentNode)
                    neighbors.append(childNode)

            if not neighbors:
                exploredList.append(currentNode)
                descFail = f"Thất bại:\n👉 Node [{currentNode.label}] (h={currentNode.h}) không có lân cận nào hợp lệ."
                steps.append(StepInfo('failure', currentNode, [], list(exploredList), set(), descFail))
                return steps, exploredList

            # We filter only neighbors with lower h value since the 8-puzzle problem seeks to minimize Manhattan distance
            betterNeighbors = [n for n in neighbors if n.h < currentNode.h]

            if betterNeighbors:
                # Stochastic Hill Climbing selects a node randomly from the set of all better neighbors
                nextNode = random.choice(betterNeighbors)
                
                descExp = (
                    f"Mở rộng Node [{currentNode.label}] (h={currentNode.h}):\n"
                    f"👉 Xét tất cả {len(neighbors)} lân cận. Lọc ra {len(betterNeighbors)} lân cận tốt hơn (h < {currentNode.h}).\n"
                    f"👉 Chọn ngẫu nhiên một lân cận tốt hơn: [{nextNode.label}] (h={nextNode.h}).\n"
                    f"👉 Di chuyển sang Node [{nextNode.label}]."
                )
                steps.append(StepInfo('expand', currentNode, neighbors, list(exploredList) + [currentNode], {n.label for n in neighbors}, descExp))
                exploredList.append(currentNode)
                currentNode = nextNode

                if currentNode.state == goalTuple:
                    descFound = (
                        f"Lấy Node [{currentNode.label}] ra xét:\n"
                        f"👉 Trạng thái CHÍNH LÀ ĐÍCH (GOAL) (h=0)!\n"
                        f"👉 Thuật toán tìm kiếm thành công."
                    )
                    steps.append(StepInfo('found', currentNode, [], list(exploredList) + [currentNode], set(), descFound))
                    exploredList.append(currentNode)
                    return steps, exploredList
            else:
                # If there are no better neighbors, we have hit a local maximum/minimum
                exploredList.append(currentNode)
                neighborDetails = ", ".join([f"[{n.label}] h={n.h} ({ARROW_MAP.get(n.action, '')})" for n in neighbors])
                descFail = (
                    f"Thất bại (Cực đại cục bộ / Local Maximum):\n"
                    f"👉 Trạng thái hiện tại [{currentNode.label}] (h={currentNode.h}) không phải là Goal.\n"
                    f"👉 Đã xét toàn bộ {len(neighbors)} lân cận: {neighborDetails}.\n"
                    f"👉 Không có lân cận nào tốt hơn (nhỏ hơn {currentNode.h}). Thuật toán dừng lại."
                )
                steps.append(StepInfo('failure', currentNode, neighbors, list(exploredList), set(), descFail))
                return steps, exploredList

    @staticmethod
    def runRandomRestartHillClimbing(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs Random Restart Hill Climbing search."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]
        MAX_RESTART = 5

        def createNode(state: tuple, action: str = None, depth: int = 0, parentNode: NodeInfo = None) -> NodeInfo:
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateManhattanDistance(state, goalTuple)
            labelIndex[0] += 1
            return n

        steps: list[StepInfo] = []
        exploredList: list[NodeInfo] = []

        for restart_idx in range(1, MAX_RESTART + 1):
            currentNode = createNode(initial)

            descInit = (
                f"--- BẮT ĐẦU RESTART LẦN {restart_idx} / {MAX_RESTART} ---\n"
                f"👉 Đặt Current_State = Start (h={currentNode.h}).\n"
                f"👉 Bắt đầu chạy Stochastic Hill Climbing cho lượt này."
            )
            steps.append(StepInfo('restart', currentNode, [currentNode], list(exploredList), {currentNode.label}, descInit))

            if currentNode.state == goalTuple:
                descFound = f"Lượt {restart_idx}: Trạng thái bắt đầu [{currentNode.label}] (h={currentNode.h}) chính là ĐÍCH (GOAL)!"
                steps.append(StepInfo('found', currentNode, [], list(exploredList) + [currentNode], set(), descFound))
                exploredList.append(currentNode)
                return steps, exploredList

            stuck = False
            while not stuck:
                neighbors: list[NodeInfo] = []
                for dirName, dr, dc in MOVE_DIRS:
                    childState = applyMove(currentNode.state, dirName)
                    if childState is not None:
                        childNode = createNode(childState, dirName, currentNode.depth + 1, currentNode)
                        neighbors.append(childNode)

                if not neighbors:
                    exploredList.append(currentNode)
                    stuck = True
                    descFail = f"Lượt {restart_idx}: Node [{currentNode.label}] không có lân cận hợp lệ. Nhảy sang lượt restart tiếp theo."
                    steps.append(StepInfo('cutoff', currentNode, [], list(exploredList), set(), descFail))
                    break

                betterNeighbors = [n for n in neighbors if n.h < currentNode.h]

                if betterNeighbors:
                    nextNode = random.choice(betterNeighbors)
                    descExp = (
                        f"Lượt {restart_idx} - Mở rộng [{currentNode.label}] (h={currentNode.h}):\n"
                        f"👉 Sinh {len(neighbors)} lân cận, lọc ra {len(betterNeighbors)} lân cận tốt hơn.\n"
                        f"👉 Chọn ngẫu nhiên lân cận tốt hơn: [{nextNode.label}] (h={nextNode.h})."
                    )
                    steps.append(StepInfo('expand', currentNode, neighbors, list(exploredList) + [currentNode], {n.label for n in neighbors}, descExp))
                    exploredList.append(currentNode)
                    currentNode = nextNode

                    if currentNode.state == goalTuple:
                        descFound = (
                            f"Lượt {restart_idx}: Tìm thấy ĐÍCH (GOAL)!\n"
                            f"👉 Node [{currentNode.label}] (h=0) đạt Goal.\n"
                            f"👉 Thuật toán dừng lại thành công."
                        )
                        steps.append(StepInfo('found', currentNode, [], list(exploredList) + [currentNode], set(), descFound))
                        exploredList.append(currentNode)
                        return steps, exploredList
                else:
                    exploredList.append(currentNode)
                    stuck = True
                    neighborDetails = ", ".join([f"[{n.label}] h={n.h} ({ARROW_MAP.get(n.action, '')})" for n in neighbors])
                    descFail = (
                        f"Lượt {restart_idx} bị kẹt (Cực đại cục bộ / Local Maximum):\n"
                        f"👉 Node [{currentNode.label}] (h={currentNode.h}) không tốt hơn lân cận nào.\n"
                        f"👉 Đã xét {len(neighbors)} lân cận: {neighborDetails}.\n"
                        f"👉 Nhảy sang lượt restart tiếp theo."
                    )
                    steps.append(StepInfo('cutoff', currentNode, neighbors, list(exploredList), set(), descFail))
                    break

        descFailAll = f"Thất bại:\n👉 Đã chạy hết {MAX_RESTART} lượt restart mà không tìm thấy Goal."
        steps.append(StepInfo('failure', None, [], list(exploredList), set(), descFailAll))
        return steps, exploredList

    @staticmethod
    def runLocalBeamSearch(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs Local Beam Search with beam width k."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]
        k = 3

        def createNode(state: tuple, action: str = None, depth: int = 0, parentNode: NodeInfo = None) -> NodeInfo:
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateManhattanDistance(state, goalTuple)
            labelIndex[0] += 1
            return n

        steps: list[StepInfo] = []
        exploredList: list[NodeInfo] = []
        global_seen_states = set()

        # 1. Khởi tạo: Current_State_set = {Các Node lân cận hợp lệ từ Start}
        startNode = createNode(initial)
        exploredList.append(startNode)
        global_seen_states.add(startNode.state)

        initial_neighbors: list[NodeInfo] = []
        for dirName, dr, dc in MOVE_DIRS:
            childState = applyMove(startNode.state, dirName)
            if childState is not None and childState not in global_seen_states:
                global_seen_states.add(childState)
                initial_neighbors.append(createNode(childState, dirName, startNode.depth + 1, startNode))
                
        # Chọn tối đa k node có h nhỏ nhất từ các lân cận của Start
        initial_neighbors.sort(key=lambda n: n.h)
        beam = initial_neighbors[:k]

        descInit = (
            f"Bước 0: Khởi tạo Local Beam Search (k={k}):\n"
            f"👉 Từ Start [{startNode.label}], sinh ra {len(initial_neighbors)} lân cận.\n"
            f"👉 Chọn {len(beam)} trạng thái tốt nhất: " + ", ".join([f"[{n.label}] (h={n.h})" for n in beam]) + ".\n"
            f"👉 Bỏ qua trạng thái Start và chuyển các lân cận này thành chùm trạng thái hiện tại (bước 1)."
        )
        steps.append(StepInfo('init', startNode, list(beam), list(exploredList), {n.label for n in beam}, descInit))

        for n in beam:
            if n.state == goalTuple:
                descFound = f"Lần lọc đầu tiên: Phát hiện Node [{n.label}] (h={n.h}) chính là ĐÍCH (GOAL)!"
                steps.append(StepInfo('found', n, [], list(exploredList) + beam, set(), descFound))
                return steps, exploredList

        iteration = 0
        max_iterations = 200

        while iteration < max_iterations:
            iteration += 1
            neighbor_nodes: list[NodeInfo] = []
            
            for parentNode in beam:
                exploredList.append(parentNode)
                for dirName, dr, dc in MOVE_DIRS:
                    childState = applyMove(parentNode.state, dirName)
                    if childState is not None and childState not in global_seen_states:
                        global_seen_states.add(childState)
                        childNode = createNode(childState, dirName, parentNode.depth + 1, parentNode)
                        neighbor_nodes.append(childNode)

            goalNode = next((n for n in neighbor_nodes if n.state == goalTuple), None)
            if goalNode:
                descExp = (
                    f"Vòng {iteration} - Mở rộng chùm:\n"
                    f"👉 Sinh ra {len(neighbor_nodes)} lân cận từ chùm hiện tại.\n"
                    f"👉 Phát hiện lân cận [{goalNode.label}] (h=0) là ĐÍCH (GOAL)!"
                )
                steps.append(StepInfo('expand', list(beam), neighbor_nodes, list(exploredList), {n.label for n in neighbor_nodes}, descExp))

                descFound = (
                    f"Tìm thấy ĐÍCH (GOAL)!\n"
                    f"👉 Node [{goalNode.label}] (h=0) đạt Goal.\n"
                    f"👉 Thuật toán dừng lại thành công."
                )
                steps.append(StepInfo('found', goalNode, [], list(exploredList) + [goalNode], set(), descFound))
                exploredList.append(goalNode)
                return steps, exploredList

            descExp = (
                f"Vòng {iteration} - Mở rộng chùm:\n"
                f"👉 Sinh ra {len(neighbor_nodes)} lân cận từ chùm hiện tại.\n"
                f"👉 Không có lân cận nào là Goal. Chuẩn bị lựa chọn chùm mới."
            )
            steps.append(StepInfo('expand', list(beam), neighbor_nodes, list(exploredList), {n.label for n in neighbor_nodes}, descExp))

            neighbor_nodes.sort(key=lambda x: x.h)
            beam = neighbor_nodes[:k]

            beamLabels = ", ".join([f"[{n.label}] (h={n.h})" for n in beam])
            descSelect = (
                f"Vòng {iteration} - Lựa chọn chùm:\n"
                f"👉 Sắp xếp {len(neighbor_nodes)} lân cận theo h tăng dần.\n"
                f"👉 Chọn k={k} lân cận tốt nhất làm chùm mới: {beamLabels}."
            )
            steps.append(StepInfo('cutoff', list(beam), list(beam), list(exploredList), {n.label for n in beam}, descSelect))

        descFail = f"Thất bại:\n👉 Đạt giới hạn số vòng lặp tối đa ({max_iterations}) mà không tìm thấy Goal."
        steps.append(StepInfo('failure', None, [], list(exploredList), set(), descFail))
        return steps, exploredList

    @staticmethod
    def runIdaStar(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs Iterative Deepening A* (IDA*) search."""
        goalTuple = tuple(tuple(r) for r in goal)
        exploredMaster: list[NodeInfo] = []
        steps: list[StepInfo] = []

        # Determine start node configuration to get the initial f-cost limit
        labelIndexTemp = [0]
        def createTempNode(state: tuple) -> NodeInfo:
            n = NodeInfo(state, action=None, depth=0, parent=None)
            n.h = calculateMisplacedTiles(state, goalTuple)
            n.g = 0
            n.cost = n.g + n.h
            return n

        startNodeTemp = createTempNode(initial)
        limit = startNodeTemp.cost

        # Safeguard limit iteration count to avoid infinite loops
        for _ in range(100):
            labelIndex = [0]

            def createNode(state: tuple, action: str = None, depth: int = 0, parentNode: NodeInfo = None) -> NodeInfo:
                parentLabel = parentNode.label if parentNode else None
                n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
                n.h = calculateMisplacedTiles(state, goalTuple)
                labelIndex[0] += 1
                return n

            start = createNode(initial)
            start.g = 0
            start.cost = start.g + start.h

            frontierStack = [start]
            anyPruned = False
            lastExaminedNode = start

            descInit = (
                f"--- BẮT ĐẦU IDA* VỚI LIMIT = {limit} ---\n"
                f"👉 Khởi tạo lại DLS giới hạn f-cost.\n"
                f"👉 Đưa Node [{start.label}] (f={start.cost}) vào Stack."
            )
            steps.append(StepInfo('new_limit', None, list(frontierStack), [], {start.label}, descInit, limit=limit, exploredCount=len(exploredMaster)))

            while frontierStack:
                node = frontierStack.pop()
                lastExaminedNode = node

                if node.state == goalTuple:
                    descFound = (
                        f"Lấy Node [{node.label}] ở đỉnh Stack ra để xét:\n"
                        f"👉 Trạng thái này CHÍNH LÀ ĐÍCH (GOAL)!\n"
                        f"👉 Tìm thấy giải pháp tại Limit={limit}."
                    )
                    steps.append(StepInfo('found', node, list(frontierStack), [], set(), descFound, limit=limit, exploredCount=len(exploredMaster)))
                    return steps, exploredMaster

                if node.cost >= limit:
                    anyPruned = True
                    descCutoff = (
                        f"Node [{node.label}] bị Cutoff:\n"
                        f"👉 f(n) = g({node.g}) + h({node.h}) = {node.cost} > Limit ({limit}).\n"
                        f"👉 Bỏ qua việc mở rộng Node này."
                    )
                    steps.append(StepInfo('cutoff', node, list(frontierStack), [], set(), descCutoff, limit=limit, exploredCount=len(exploredMaster)))
                    continue

                if hasCycle(node):
                    continue

                exploredMaster.append(node)
                newLabels = set()

                for dirName, dr, dc in reversed(MOVE_DIRS):
                    childState = applyMove(node.state, dirName)
                    if childState is None:
                        continue

                    costM = calculateInversions(childState)
                    gNew = node.g + costM

                    child = createNode(childState, dirName, node.depth + 1, node)
                    child.g = gNew
                    child.cost = child.g + child.h

                    frontierStack.append(child)
                    newLabels.add(child.label)

                descExp = (
                    f"Mở rộng Node [{node.label}] (f={node.cost}):\n"
                    f"👉 Sinh ra {len(newLabels)} Node con.\n"
                    f"👉 Đẩy các Node con vào đỉnh Stack."
                )
                steps.append(StepInfo('expand', node, list(frontierStack), [], newLabels, descExp, limit=limit, exploredCount=len(exploredMaster)))

            if not anyPruned:
                descFail = f"Thất bại hoàn toàn:\n👉 Đã duyệt hết không gian tìm kiếm tại Limit={limit} mà không bị Cutoff bất cứ Node nào.\n👉 Bài toán vô nghiệm."
                steps.append(StepInfo('failure', None, [], [], set(), descFail, limit=limit, exploredCount=len(exploredMaster)))
                return steps, exploredMaster
            else:
                nextLimit = limit + lastExaminedNode.h
                descNext = (
                    f"Kết thúc chu kỳ duyệt tại Limit={limit} (không tìm thấy Goal):\n"
                    f"👉 Cập nhật giới hạn mới: limit += h(n) của node cuối cùng được xét [{lastExaminedNode.label}] (h={lastExaminedNode.h}).\n"
                    f"👉 Tăng Limit lên {nextLimit} và bắt đầu chu kỳ duyệt mới."
                )
                steps.append(StepInfo('cutoff', None, [], [], set(), descNext, limit=limit, exploredCount=len(exploredMaster)))
                limit = nextLimit

        descMax = "Thất bại:\n👉 Vượt quá số lần lặp tối đa của IDA* (100).\n👉 Thuật toán dừng lại."
        steps.append(StepInfo('failure', None, [], [], set(), descMax, limit=limit, exploredCount=len(exploredMaster)))
        return steps, exploredMaster

    @staticmethod
    def runAndOrSearch(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Performs a simplified AND-OR search with non-deterministic actions (intended move + 1 slip)."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]
        steps = []
        exploredList = []
        
        def createNode(state, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = calculateManhattanDistance(state, goalTuple)
            labelIndex[0] += 1
            return n

        startNode = createNode(initial)
        frontier = [startNode]
        reached = {initial: startNode}
        
        descInit = "Khởi tạo AND-OR Search:\n👉 Môi trường không tất định: 1 hành động có thể sinh ra nhiều kết quả (có rủi ro bị trượt)."
        steps.append(StepInfo('init', startNode, list(frontier), list(exploredList), {startNode.label}, descInit))
        
        while frontier:
            node = frontier.pop(0)
            exploredList.append(node)
            
            if node.state == goalTuple:
                descFound = f"Tìm thấy Goal tại Node [{node.label}].\n👉 Trong mô hình AND-OR, nhánh này đã được giải quyết thành công."
                steps.append(StepInfo('found', node, list(frontier), list(exploredList), set(), descFound))
                return steps, exploredList
                
            newLabels = set()
            for i, (dirName, dr, dc) in enumerate(MOVE_DIRS):
                outcomes = []
                intended = applyMove(node.state, dirName)
                if intended: outcomes.append(intended)
                
                # Introduce non-determinism: possible slip to the next orthogonal direction
                slipDir = MOVE_DIRS[(i + 1) % 4][0]
                slip = applyMove(node.state, slipDir)
                if slip and slip != intended:
                    outcomes.append(slip)
                
                if outcomes:
                    for out_state in outcomes:
                        if out_state not in reached:
                            child = createNode(out_state, dirName, node.depth + 1, node)
                            reached[out_state] = child
                            frontier.append(child)
                            newLabels.add(child.label)
            
            descExp = f"Mở rộng Node [{node.label}] với môi trường không tất định:\n👉 Một số hành động bị trượt sinh ra thêm trạng thái ngoài ý muốn.\n👉 Tổng {len(newLabels)} trạng thái kết quả (OR-nodes)."
            steps.append(StepInfo('expand', node, list(frontier), list(exploredList), newLabels, descExp))
            
            if len(exploredList) > 500: # Limit to avoid infinite loops
                break
                
        descFail = "Thất bại: Không tìm được giải pháp khả thi an toàn trong không gian hữu hạn."
        steps.append(StepInfo('failure', None, [], list(exploredList), set(), descFail))
        return steps, exploredList

    @staticmethod
    def runSensorlessSearch(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Searching with no observation (Sensorless), working purely in Belief Space."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]
        steps = []
        exploredList = []
        
        def createNode(states: tuple, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(states, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = min(calculateManhattanDistance(s, goalTuple) for s in states)
            labelIndex[0] += 1
            return n

        # Initial BS has 3 random states
        initial_states = [initial]
        while len(initial_states) < 3:
            rand_s = generateRandomSolvableState(goalTuple)
            if rand_s not in initial_states:
                initial_states.append(rand_s)
                
        # GS has 3 random states
        goal_states = [goalTuple]
        while len(goal_states) < 3:
            rand_g = generateRandomSolvableState(initial_states[0])
            if rand_g not in goal_states:
                goal_states.append(rand_g)
                
        startBS = tuple(initial_states)
        startNode = createNode(startBS)
        
        frontier = [startNode]
        reached = {frozenset(startBS)}
        
        descInit = f"Khởi tạo Sensorless Search:\n👉 Belief State (BS) ban đầu: 3 trạng thái ngẫu nhiên.\n👉 Goal State (GS): 3 trạng thái ngẫu nhiên."
        steps.append(StepInfo('init', startNode, list(frontier), list(exploredList), {startNode.label}, descInit))
        
        # We attach metadata to the steps for the UI to consume
        for s in steps:
            setattr(s, 'goal_states', goal_states)
        
        while frontier:
            node = frontier.pop(0)
            exploredList.append(node)
            
            # Goal check: if ANY state in current BS matches ANY state in GS
            if any(s in goal_states for s in node.state):
                descFound = f"Tìm thấy Goal tại Belief State [{node.label}]!\n👉 Ít nhất 1 trạng thái thực tế trong BS đã khớp với tập Goal State."
                steps.append(StepInfo('found', node, list(frontier), list(exploredList), set(), descFound))
                return steps, exploredList
                
            newLabels = set()
            for dirName, dr, dc in MOVE_DIRS:
                next_states = []
                for s in node.state:
                    nxt = applyMove(s, dirName)
                    if nxt is not None:
                        next_states.append(nxt)
                    else:
                        next_states.append(s)
                next_bs = tuple(next_states) # Keep exact order for UI
                fs_bs = frozenset(next_bs)
                
                if fs_bs not in reached:
                    child = createNode(next_bs, dirName, node.depth + 1, node)
                    reached.add(fs_bs)
                    frontier.append(child)
                    newLabels.add(child.label)
                    
            descExp = f"Mở rộng Belief State [{node.label}]:\n👉 Áp dụng 4 hành động mù (Sensorless) lên toàn bộ các trạng thái trong BS."
            steps.append(StepInfo('expand', node, list(frontier), list(exploredList), newLabels, descExp))
            
            if len(exploredList) > 500:
                break
                
        descFail = "Thất bại: Đã duyệt quá giới hạn không gian Belief State."
        steps.append(StepInfo('failure', None, [], list(exploredList), set(), descFail))
        return steps, exploredList

    @staticmethod
    def runPartiallyObservableSearch(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        """Searching for partially observable problems."""
        goalTuple = tuple(tuple(r) for r in goal)
        labelIndex = [0]
        steps = []
        exploredList = []
        
        def createNode(states: tuple, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            n = NodeInfo(states, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            n.h = min(calculateManhattanDistance(s, goalTuple) for s in states)
            labelIndex[0] += 1
            return n

        num_known = random.randint(1, 5)
        positions = [(r, c) for r in range(3) for c in range(3)]
        known_positions = random.sample(positions, num_known)
        
        def get_all_matching_solvable_states(base_state, known_pos):
            import itertools
            flat_base = [val for row in base_state for val in row]
            known_indices = [r * 3 + c for r, c in known_pos]
            unknown_indices = [i for i in range(9) if i not in known_indices]
            unknown_vals = [flat_base[i] for i in unknown_indices]
            
            base_inv = sum(1 for i in range(9) for j in range(i+1, 9) if flat_base[i] and flat_base[j] and flat_base[i] > flat_base[j])
            
            matching = []
            for p in itertools.permutations(unknown_vals):
                new_flat = list(flat_base)
                for idx, val in zip(unknown_indices, p):
                    new_flat[idx] = val
                    
                inv = sum(1 for i in range(9) for j in range(i+1, 9) if new_flat[i] and new_flat[j] and new_flat[i] > new_flat[j])
                if inv % 2 == base_inv % 2:
                    new_state = tuple(tuple(new_flat[r*3:(r+1)*3]) for r in range(3))
                    matching.append(new_state)
            return matching

        all_initial = get_all_matching_solvable_states(initial, known_positions)
        initial_states = random.sample(all_initial, min(3, len(all_initial)))
        if initial not in initial_states:
            initial_states[0] = initial
            
        all_goal = get_all_matching_solvable_states(goalTuple, known_positions)
        goal_states = random.sample(all_goal, min(3, len(all_goal)))
        if goalTuple not in goal_states:
            goal_states[0] = goalTuple
                
        startBS = tuple(initial_states)
        startNode = createNode(startBS)
        
        frontier = [startNode]
        reached = {frozenset(startBS)}
        
        descInit = f"Khởi tạo Partially Observable Search:\n👉 Quan sát được {num_known} ô.\n👉 Lấy ngẫu nhiên các BS và GS (3 trạng thái) tương ứng với ô đúng."
        steps.append(StepInfo('init', startNode, list(frontier), list(exploredList), {startNode.label}, descInit, known_positions=known_positions))
        
        for s in steps:
            setattr(s, 'goal_states', goal_states)
            s.known_positions = known_positions
        
        while frontier:
            node = frontier.pop(0)
            exploredList.append(node)
            
            if any(s in goal_states for s in node.state):
                descFound = f"Tìm thấy Goal tại Belief State [{node.label}]!\n👉 Đã đạt trạng thái mong đợi nhờ thông tin quan sát từng phần."
                steps.append(StepInfo('found', node, list(frontier), list(exploredList), set(), descFound, known_positions=known_positions))
                return steps, exploredList
                
            newLabels = set()
            for dirName, dr, dc in MOVE_DIRS:
                next_states = []
                for s in node.state:
                    nxt = applyMove(s, dirName)
                    if nxt is not None:
                        next_states.append(nxt)
                    else:
                        next_states.append(s)
                
                next_bs = tuple(next_states) # Keep exact order for UI
                fs_bs = frozenset(next_bs)
                
                if fs_bs not in reached:
                    child = createNode(next_bs, dirName, node.depth + 1, node)
                    reached.add(fs_bs)
                    frontier.append(child)
                    newLabels.add(child.label)
                    
            descExp = f"Mở rộng Belief State [{node.label}] có quan sát:\n👉 Tính toán trạng thái kết quả dựa trên các thông tin đã lọc."
            steps.append(StepInfo('expand', node, list(frontier), list(exploredList), newLabels, descExp, known_positions=known_positions))
            
            if len(exploredList) > 500:
                break
                
        descFail = "Thất bại: Không tìm được giải pháp với các ràng buộc quan sát hiện tại."
        steps.append(StepInfo('failure', None, [], list(exploredList), set(), descFail, known_positions=known_positions))
        return steps, exploredList

    @staticmethod
    def runBacktracking(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        variables = ['WA', 'NT', 'SA', 'Q', 'NSW', 'V', 'T']
        domains = {v: ['đỏ', 'xanh lá', 'xanh dương'] for v in variables}
        neighbors = {
            'WA': ['NT', 'SA'], 'NT': ['WA', 'SA', 'Q'], 'SA': ['WA', 'NT', 'Q', 'NSW', 'V'],
            'Q': ['NT', 'SA', 'NSW'], 'NSW': ['Q', 'SA', 'V'], 'V': ['SA', 'NSW'], 'T': []
        }
        
        steps, exploredList, labelIndex = [], [], [0]
        
        def createNode(assignment, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            state = ('CSP_Graph', tuple((k, assignment[k]) for k in variables if k in assignment))
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            labelIndex[0] += 1
            return n

        def is_consistent(var, value, assignment):
            for neighbor in neighbors[var]:
                if neighbor in assignment and assignment[neighbor] == value:
                    return False
            return True

        startNode = createNode({})
        steps.append(StepInfo('init', startNode, [], [], {startNode.label}, "Khởi tạo Backtracking: Assignment = {}"))
        
        def backtrack(assignment, parentNode):
            if len(assignment) == len(variables): return parentNode
            
            unassigned = [v for v in variables if v not in assignment]
            var = unassigned[0]
            
            for value in domains[var]:
                descExp = f"Chọn biến {var}, thử gán {var} = {value}"
                
                if is_consistent(var, value, assignment):
                    new_assignment = assignment.copy()
                    new_assignment[var] = value
                    child = createNode(new_assignment, f"{var}={value}", parentNode.depth + 1, parentNode)
                    exploredList.append(child)
                    steps.append(StepInfo('expand', child, [], list(exploredList), {child.label}, descExp + " -> Hợp lệ"))
                    
                    result = backtrack(new_assignment, child)
                    if result: return result
                else:
                    temp_assignment = assignment.copy()
                    temp_assignment[var] = value
                    child = createNode(temp_assignment, f"{var}={value}", parentNode.depth + 1, parentNode)
                    steps.append(StepInfo('expand', child, [], list(exploredList), {child.label}, descExp + " -> Vi phạm ràng buộc (Lùi lại)"))
            return None
            
        finalNode = backtrack({}, startNode)
        if finalNode: steps.append(StepInfo('found', finalNode, [], list(exploredList), set(), "Tìm thấy cấu hình hợp lệ thỏa mãn tất cả ràng buộc!"))
        else: steps.append(StepInfo('failure', None, [], list(exploredList), set(), "Thất bại: Không có giải pháp."))
        return steps, exploredList

    @staticmethod
    def runForwardChecking(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        variables = ['WA', 'NT', 'SA', 'Q', 'NSW', 'V', 'T']
        colors = ['đỏ', 'xanh lá', 'xanh dương']
        neighbors = {
            'WA': ['NT', 'SA'], 'NT': ['WA', 'SA', 'Q'], 'SA': ['WA', 'NT', 'Q', 'NSW', 'V'],
            'Q': ['NT', 'SA', 'NSW'], 'NSW': ['Q', 'SA', 'V'], 'V': ['SA', 'NSW'], 'T': []
        }
        
        steps, exploredList, labelIndex = [], [], [0]
        
        def createNode(assignment, domains, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            state = ('CSP_Graph_FC', tuple((k, assignment[k]) for k in variables if k in assignment), tuple((k, tuple(domains[k])) for k in variables))
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            labelIndex[0] += 1
            return n

        startNode = createNode({}, {v: list(colors) for v in variables})
        steps.append(StepInfo('init', startNode, [], [], {startNode.label}, "Khởi tạo Forward Checking: Assignment = {}"))
        
        def backtrack_fc(assignment, domains, parentNode):
            if len(assignment) == len(variables): return parentNode
            
            unassigned = [v for v in variables if v not in assignment]
            var = unassigned[0]
            
            for value in domains[var]:
                descExp = f"Chọn {var}, gán = {value}."
                new_domains = {k: list(v) for k, v in domains.items()}
                new_assignment = assignment.copy()
                new_assignment[var] = value
                
                valid = True
                pruned = []
                for neighbor in neighbors[var]:
                    if neighbor not in new_assignment:
                        if value in new_domains[neighbor]:
                            new_domains[neighbor].remove(value)
                            pruned.append(f"{neighbor} loại {value}")
                            if not new_domains[neighbor]: valid = False
                
                if pruned: descExp += "\n👉 FC: " + ", ".join(pruned)
                child = createNode(new_assignment, new_domains, f"{var}={value}", parentNode.depth + 1, parentNode)
                exploredList.append(child)
                
                if valid:
                    steps.append(StepInfo('expand', child, [], list(exploredList), {child.label}, descExp + " -> Miền giá trị hợp lệ."))
                    result = backtrack_fc(new_assignment, new_domains, child)
                    if result: return result
                else:
                    steps.append(StepInfo('expand', child, [], list(exploredList), {child.label}, descExp + " -> FC phát hiện miền rỗng (Lùi lại)."))
            return None
            
        finalNode = backtrack_fc({}, {v: list(colors) for v in variables}, startNode)
        if finalNode: steps.append(StepInfo('found', finalNode, [], list(exploredList), set(), "Tìm thấy cấu hình hợp lệ thỏa mãn tất cả ràng buộc!"))
        else: steps.append(StepInfo('failure', None, [], list(exploredList), set(), "Thất bại: Không có giải pháp."))
        return steps, exploredList

    @staticmethod
    def runMinConflicts(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        variables = ['WA', 'NT', 'SA', 'Q', 'NSW', 'V', 'T']
        colors = ['đỏ', 'xanh lá', 'xanh dương']
        neighbors = {
            'WA': ['NT', 'SA'], 'NT': ['WA', 'SA', 'Q'], 'SA': ['WA', 'NT', 'Q', 'NSW', 'V'],
            'Q': ['NT', 'SA', 'NSW'], 'NSW': ['Q', 'SA', 'V'], 'V': ['SA', 'NSW'], 'T': []
        }
        
        steps, exploredList, labelIndex = [], [], [0]
        
        def createNode(assignment, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            state = ('CSP_Graph', tuple((k, assignment[k]) for k in variables))
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            labelIndex[0] += 1
            return n

        def conflicts(var, val, assignment):
            return sum(1 for neighbor in neighbors[var] if assignment[neighbor] == val)
            
        assignment = {v: random.choice(colors) for v in variables}
        currentNode = createNode(assignment)
        steps.append(StepInfo('init', currentNode, [], [], {currentNode.label}, "Khởi tạo Min Conflicts:\n👉 Gán ngẫu nhiên trạng thái ban đầu."))
        
        max_steps = 100
        for i in range(max_steps):
            exploredList.append(currentNode)
            conflicted_vars = [v for v in variables if conflicts(v, assignment[v], assignment) > 0]
            
            if not conflicted_vars:
                steps.append(StepInfo('found', currentNode, [], list(exploredList), set(), "Tìm thấy trạng thái đích: Số lượng xung đột = 0!"))
                return steps, exploredList
                
            var = random.choice(conflicted_vars)
            
            min_conflicts = float('inf')
            best_values = []
            for val in colors:
                c = conflicts(var, val, assignment)
                if c < min_conflicts:
                    min_conflicts, best_values = c, [val]
                elif c == min_conflicts:
                    best_values.append(val)
                    
            new_val = random.choice(best_values)
            assignment[var] = new_val
            
            nextNode = createNode(assignment, f"{var}={new_val}", currentNode.depth + 1, currentNode)
            steps.append(StepInfo('expand', nextNode, [], list(exploredList), {nextNode.label}, f"Bước {i+1}:\n👉 Chọn ngẫu nhiên biến xung đột: {var}\n👉 Đổi thành màu ít xung đột nhất ({new_val}) với {min_conflicts} xung đột."))
            currentNode = nextNode
            
        steps.append(StepInfo('failure', currentNode, [], list(exploredList), set(), f"Thất bại: Đã đạt số bước tối đa ({max_steps})."))
        return steps, exploredList

    @staticmethod
    def runAC3(initial: tuple, goal: tuple) -> tuple[list[StepInfo], list[NodeInfo]]:
        variables = ['X', 'Y', 'Z']
        domains = {'X': [1,2,3], 'Y': [1,2,3], 'Z': [2,3]}
        arcs = [('X', 'Y'), ('Y', 'X'), ('Y', 'Z'), ('Z', 'Y')]
        
        def satisfies(x, val_x, y, val_y):
            if x == 'X' and y == 'Y': return val_x < val_y
            if x == 'Y' and y == 'X': return val_y < val_x
            if x == 'Y' and y == 'Z': return val_x < val_y
            if x == 'Z' and y == 'Y': return val_y < val_x
            return True
            
        steps, exploredList, labelIndex = [], [], [0]
        
        def createNode(doms, action=None, depth=0, parentNode=None):
            parentLabel = parentNode.label if parentNode else None
            state = ('CSP_Arc', tuple((k, tuple(doms[k])) for k in variables))
            n = NodeInfo(state, action, depth, 0, parentLabel, generateLabel(labelIndex[0]), parent=parentNode)
            labelIndex[0] += 1
            return n

        currentNode = createNode(domains)
        queue = deque(arcs)
        
        descInit = f"Khởi tạo AC-3:\n👉 Q = {', '.join([f'{a}{b}' for a, b in queue])}\n👉 D(X)={{1,2,3}}, D(Y)={{1,2,3}}, D(Z)={{2,3}}"
        steps.append(StepInfo('init', currentNode, [], [], {currentNode.label}, descInit))
        
        while queue:
            exploredList.append(currentNode)
            (xi, xj) = queue.popleft()
            
            revised = False
            new_doms = {k: list(v) for k, v in domains.items()}
            pruned_vals = []
            
            for x_val in list(new_doms[xi]):
                if not any(satisfies(xi, x_val, xj, y_val) for y_val in new_doms[xj]):
                    new_doms[xi].remove(x_val)
                    pruned_vals.append(x_val)
                    revised = True
                    
            domains = new_doms
            nextNode = createNode(domains, f"Xét {xi}{xj}", currentNode.depth + 1, currentNode)
            
            descExp = f"Xét cung {xi}{xj}:\n"
            if revised:
                descExp += f"👉 Loại bỏ {pruned_vals} khỏi D({xi}) do không có giá trị D({xj}) tương ứng thỏa mãn.\n"
                
                # Bám sát tài liệu: Thuật toán Naive AC-3 (thêm TẤT CẢ các cung còn thiếu vào hàng đợi)
                for arc in arcs:
                    if arc not in queue:
                        queue.append(arc)
                        descExp += f"👉 Thêm cung {arc[0]}{arc[1]} vào Q.\n"
            else:
                descExp += f"👉 Thỏa mãn, không có giá trị nào bị loại khỏi D({xi}).\n"
                
            descExp += f"👉 Q hiện tại: {{{', '.join([f'{a}{b}' for a, b in queue])}}}"
            steps.append(StepInfo('expand', nextNode, [], list(exploredList), {nextNode.label}, descExp))
            currentNode = nextNode
            
            if not domains[xi]:
                steps.append(StepInfo('failure', currentNode, [], list(exploredList), set(), f"Thất bại: D({xi}) rỗng."))
                return steps, exploredList
                
        steps.append(StepInfo('found', currentNode, [], list(exploredList), set(), "Thành công: Thuật toán AC-3 hoàn tất, tất cả các cung đã nhất quán!"))
        return steps, exploredList

# ══════════════════════════════════════════════════
# 5. GIAO DIỆN & ỨNG DỤNG (UI/UX & APPLICATION)
# ══════════════════════════════════════════════════

class Main8PuzzleApp:
    def __init__(self, root):
        self.root = root
        self.root.title('8-Puzzle — AI Algorithms')
        self.root.configure(bg=BG)
        self.root.geometry('1300x750')
        self.root.resizable(True, True)

        self.algorithms = {
            'BFS (Breadth-First Search)': SearchEngine.runBfs,
            'DFS (Depth-First Search)': SearchEngine.runDfs,
            'IDS (Iterative Deepening Search)': SearchEngine.runIds,
            'UCS (Uniform-Cost Search)': SearchEngine.runUcs,
            'Greedy-Search (Heuristic)': SearchEngine.runGreedySearch,
            'A* (A-Star Search)': SearchEngine.runAStar,
            'IDA* (Iterative Deepening A*)': SearchEngine.runIdaStar,
            'Simple Hill Climbing (SHC)': SearchEngine.runSimpleHillClimbing,
            'Steepest-Ascent Hill Climbing (SAHC)': SearchEngine.runSteepestAscentHillClimbing,
            'Stochastic Hill Climbing (StHC)': SearchEngine.runStochasticHillClimbing,
            'Random Restart Hill Climbing (RRHC)': SearchEngine.runRandomRestartHillClimbing,
            'Local Beam Search (LBS)': SearchEngine.runLocalBeamSearch,
            'AND-OR search': SearchEngine.runAndOrSearch,
            'Searching with no observation': SearchEngine.runSensorlessSearch,
            'Searching for partially observable problems': SearchEngine.runPartiallyObservableSearch,
            'Multi-Start Greedy Search': None,
            'Backtracking': SearchEngine.runBacktracking,
            'Forward Checking': SearchEngine.runForwardChecking,
            'Min Conflicts': SearchEngine.runMinConflicts,
            'AC-3': SearchEngine.runAC3
        }
        self.algoGroups = {
            'Uninformed Search': [
                'BFS (Breadth-First Search)',
                'DFS (Depth-First Search)',
                'IDS (Iterative Deepening Search)',
                'UCS (Uniform-Cost Search)'
            ],
            'Informed Search': [
                'Greedy-Search (Heuristic)',
                'A* (A-Star Search)',
                'IDA* (Iterative Deepening A*)'
            ],
            'Hill Climbing (Local Search)': [
                'Simple Hill Climbing (SHC)',
                'Steepest-Ascent Hill Climbing (SAHC)',
                'Stochastic Hill Climbing (StHC)',
                'Random Restart Hill Climbing (RRHC)'
            ],
            'Local Beam Search': [
                'Local Beam Search (LBS)'
            ],
            'Searching in complex environments': [
                'AND-OR search',
                'Searching with no observation',
                'Searching for partially observable problems'
            ],
            'Multi Start State': [
                'Multi-Start Greedy Search'
            ],
            'Constraint satisfaction problems': [
                'Backtracking',
                'Forward Checking',
                'Min Conflicts',
                'AC-3'
            ]
        }
        self.currentGroupName = 'Uninformed Search'
        self.currentAlgoName = 'BFS (Breadth-First Search)'
        self.steps = []
        self.exploredMaster = []
        self.idx = 0
        self.autoMode = False
        self.speed = tk.IntVar(value=400)
        self.startState = INITIAL_STATE
        self.goalState = GOAL_STATE

        self._buildUi()
        self._loadAlgorithm(self.currentAlgoName)

    def _loadAlgorithm(self, algoName: str) -> None:
        if algoName == 'Multi-Start Greedy Search':
            self._loadMultiStartSearch()
            return
            
        if algoName in ['Backtracking', 'Forward Checking', 'Min Conflicts']:
            self.startState = ('CSP_Graph', ())
            self.goalState = ('CSP_Graph', ())
        elif algoName == 'AC-3':
            self.startState = ('CSP_Arc', ())
            self.goalState = ('CSP_Arc', ())
        else:
            # We revert back to initial default if switching from CSP back to normal
            if isinstance(self.startState, tuple) and isinstance(self.startState[0], str):
                self.startState = INITIAL_STATE
                self.goalState = GOAL_STATE
            
        algoFunc = self.algorithms[algoName]
        self.steps, self.exploredMaster = algoFunc(self.startState, self.goalState)
        self.idx = 0
        self._stopAuto()
        self.algoTitleVar.set(f'8-Puzzle — {algoName}')
        
        if len(self.steps) > 0 and hasattr(self.steps[0], 'goal_states'):
            self.currentGoalStates = self.steps[0].goal_states
        else:
            self.currentGoalStates = [self.goalState]
        self._drawGoalBoard()
        
        self._render(0)

    def _drawGoalBoard(self) -> None:
        """Draws the goal board canvas with the current goalState configuration."""
        if not hasattr(self, 'goalCanvas'): return
        self.goalCanvas.delete('all')
        known = getattr(self.steps[0], 'known_positions', None) if self.steps else None
        
        if hasattr(self, 'currentGoalStates') and len(self.currentGoalStates) > 1:
            goals = tuple(self.currentGoalStates)
            self.goalCanvas.config(width=20 + len(goals) * 110, height=130)
            for i, s in enumerate(goals):
                drawBoard(self.goalCanvas, 10 + i * 110, 10, s, cell=33, isGoalState=True, knownCells=known)
        else:
            self.goalCanvas.config(width=150, height=150)
            drawBoard(self.goalCanvas, 10, 10, self.goalState, cell=43, isGoalState=True, knownCells=known)

    def _openCustomStatesDialog(self) -> None:
        """Opens a popup dialog to enter custom Start and Goal states."""
        self._stopAuto()
        
        if self.currentAlgoName in ['Backtracking', 'Forward Checking', 'Min Conflicts', 'AC-3']:
            messagebox.showinfo("Thông báo", "Không hỗ trợ tuỳ chỉnh trạng thái cho nhóm CSP.")
            return
        
        dialog = tk.Toplevel(self.root)
        dialog.title("Nhập Start & Goal")
        dialog.geometry("500x420")
        dialog.configure(bg=BG)
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()

        # Center dialog relative to root window
        dialog.update_idletasks()
        rx = self.root.winfo_x()
        ry = self.root.winfo_y()
        rw = self.root.winfo_width()
        rh = self.root.winfo_height()
        dx = rx + (rw - 500) // 2
        dy = ry + (rh - 420) // 2
        dialog.geometry(f"+{dx}+{dy}")

        # Title Label
        tk.Label(dialog, text="Nhập Cấu Hình Start & Goal", font=('Segoe UI', 12, 'bold'), bg=BG, fg=BLACK).pack(pady=10)

        # Grids Container
        gridsFrame = tk.Frame(dialog, bg=BG)
        gridsFrame.pack(padx=20, pady=5, fill='both', expand=True)

        # Left: Start State Grid
        startFrame = tk.Frame(gridsFrame, bg=BG)
        startFrame.pack(side='left', padx=15, fill='both', expand=True)
        tk.Label(startFrame, text="Start State", font=('Segoe UI', 10, 'bold'), bg=BG, fg=GRAY).pack(pady=(0, 5))
        
        startGridFrame = tk.Frame(startFrame, bg=BG, highlightthickness=1, highlightbackground=BORDER)
        startGridFrame.pack()

        startEntries = []
        for r in range(3):
            rowEntries = []
            for c in range(3):
                val = self.startState[r][c]
                ent = tk.Entry(startGridFrame, width=3, font=('Segoe UI', 14, 'bold'), justify='center', bd=1, relief='solid')
                ent.insert(0, str(val))
                ent.grid(row=r, column=c, padx=3, pady=3, ipady=4)
                rowEntries.append(ent)
            startEntries.append(rowEntries)

        # Right: Goal State Grid
        goalFrame = tk.Frame(gridsFrame, bg=BG)
        goalFrame.pack(side='right', padx=15, fill='both', expand=True)
        tk.Label(goalFrame, text="Goal State", font=('Segoe UI', 10, 'bold'), bg=BG, fg=GRAY).pack(pady=(0, 5))
        
        goalGridFrame = tk.Frame(goalFrame, bg=BG, highlightthickness=1, highlightbackground=BORDER)
        goalGridFrame.pack()

        goalEntries = []
        for r in range(3):
            rowEntries = []
            for c in range(3):
                val = self.goalState[r][c]
                ent = tk.Entry(goalGridFrame, width=3, font=('Segoe UI', 14, 'bold'), justify='center', bd=1, relief='solid')
                ent.insert(0, str(val))
                ent.grid(row=r, column=c, padx=3, pady=3, ipady=4)
                rowEntries.append(ent)
            goalEntries.append(rowEntries)

        # Inner helpers for random generation inside dialog
        def randomizeStart():
            # Read goal from entry fields if valid, otherwise fallback to app's goalState
            goalList = []
            goalValid = True
            for r in range(3):
                for c in range(3):
                    valStr = goalEntries[r][c].get().strip()
                    if not valStr.isdigit() or int(valStr) < 0 or int(valStr) > 8:
                        goalValid = False
                        break
                    goalList.append(int(valStr))
                if not goalValid:
                    break
            
            if goalValid and len(set(goalList)) == 9:
                tempGoal = tuple(tuple(goalList[i*3 : (i+1)*3]) for i in range(3))
            else:
                tempGoal = self.goalState

            # We use 10-step random walk to ensure solvability and fast pathfinding
            randStart = generateRandomSolvableState(tempGoal)
            for r in range(3):
                for c in range(3):
                    startEntries[r][c].delete(0, 'end')
                    startEntries[r][c].insert(0, str(randStart[r][c]))

        def randomizeGoal():
            # Generate random Goal permutation
            numbers = list(range(9))
            random.shuffle(numbers)
            randGoal = tuple(tuple(numbers[i*3 : (i+1)*3]) for i in range(3))
            for r in range(3):
                for c in range(3):
                    goalEntries[r][c].delete(0, 'end')
                    goalEntries[r][c].insert(0, str(randGoal[r][c]))
            
            # Automatically align Start state to be solvable relative to this new Goal
            randStart = generateRandomSolvableState(randGoal)
            for r in range(3):
                for c in range(3):
                    startEntries[r][c].delete(0, 'end')
                    startEntries[r][c].insert(0, str(randStart[r][c]))

        # Buttons under each grid
        tk.Button(startFrame, text="🎲 Random Start", command=randomizeStart, bg='#eaeef2', fg=BLACK, font=('Segoe UI', 9, 'bold'), relief='flat', cursor='hand2', bd=0, padx=10, pady=3).pack(pady=10)
        tk.Button(goalFrame, text="🎲 Random Goal", command=randomizeGoal, bg='#eaeef2', fg=BLACK, font=('Segoe UI', 9, 'bold'), relief='flat', cursor='hand2', bd=0, padx=10, pady=3).pack(pady=10)

        # Helper note
        tk.Label(dialog, text="* Nhập các số từ 0 đến 8 (0 biểu thị ô trống).", font=('Segoe UI', 8, 'italic'), bg=BG, fg=GRAY).pack(pady=(5, 0))

        # Error Label
        errVar = tk.StringVar()
        errLbl = tk.Label(dialog, textvariable=errVar, font=('Segoe UI', 9), bg=BG, fg=RED, wraplength=450)
        errLbl.pack(pady=5)

        def validateAndSave():
            # Parse start state
            startList = []
            for r in range(3):
                for c in range(3):
                    valStr = startEntries[r][c].get().strip()
                    if not valStr.isdigit():
                        errVar.set("Lỗi: Start State chỉ được chứa các chữ số từ 0 đến 8!")
                        return
                    val = int(valStr)
                    if val < 0 or val > 8:
                        errVar.set("Lỗi: Các số của Start State phải từ 0 đến 8!")
                        return
                    startList.append(val)

            # Check duplicates in start state
            if len(set(startList)) != 9:
                errVar.set("Lỗi: Start State phải chứa đủ 9 số khác nhau từ 0 đến 8!")
                return

            # Parse goal state
            goalList = []
            for r in range(3):
                for c in range(3):
                    valStr = goalEntries[r][c].get().strip()
                    if not valStr.isdigit():
                        errVar.set("Lỗi: Goal State chỉ được chứa các chữ số từ 0 đến 8!")
                        return
                    val = int(valStr)
                    if val < 0 or val > 8:
                        errVar.set("Lỗi: Các số của Goal State phải từ 0 đến 8!")
                        return
                    goalList.append(val)

            # Check duplicates in goal state
            if len(set(goalList)) != 9:
                errVar.set("Lỗi: Goal State phải chứa đủ 9 số khác nhau từ 0 đến 8!")
                return

            # Convert to tuple representation
            newStart = tuple(tuple(startList[i*3 : (i+1)*3]) for i in range(3))
            newGoal = tuple(tuple(goalList[i*3 : (i+1)*3]) for i in range(3))

            # Verify solvability
            startInversions = calculateInversions(newStart)
            goalInversions = calculateInversions(newGoal)
            if startInversions % 2 != goalInversions % 2:
                errVar.set("Lỗi: Trạng thái bắt đầu không thể giải được để đến trạng thái đích (không cùng tính chẵn lẻ của nghịch vị)!")
                return

            # If all valid, update state
            self.startState = newStart
            self.goalState = newGoal
            
            # Redraw goal panel board
            self._drawGoalBoard()
            
            # Reload algorithms with new configurations
            self._loadAlgorithm(self.currentAlgoName)
            dialog.destroy()

        # Action Buttons
        btnFrame = tk.Frame(dialog, bg=BG)
        btnFrame.pack(pady=10)
        
        bs = dict(font=('Segoe UI', 9, 'bold'), relief='flat', cursor='hand2', padx=15, pady=4, bd=0)
        tk.Button(btnFrame, text="Lưu cấu hình", command=validateAndSave, bg=GREEN, fg=WHITE, **bs).pack(side='left', padx=10)
        tk.Button(btnFrame, text="Hủy bỏ", command=dialog.destroy, bg='#eaeef2', fg=BLACK, **bs).pack(side='left', padx=10)

    def _onKChange(self, event: tk.Event) -> None:
        self._stopAuto()
        self._randomizeMultiStates()

    def _randomizeMultiStates(self) -> None:
        self._stopAuto()
        k = int(self.comboK.get())
        
        states = []
        attempts = 0
        while len(states) < k and attempts < 100:
            s = generateRandomSolvableState(self.goalState, moves=10)
            if s not in states:
                states.append(s)
            attempts += 1
        while len(states) < k:
            states.append(generateRandomSolvableState(self.goalState, moves=10))
            
        self.multiStartStates = states
        self._rebuildMultiStartPanels()
        
        for j in range(k):
            canvas = self.multiStartInitialCanvases[j]
            canvas.delete('all')
            drawBoard(canvas, 2, 2, self.multiStartStates[j], cell=12, isGoalState=False)
            
        self._loadMultiStartSearch()

    def _rebuildMultiStartPanels(self):
        for child in self.multiStartCol.winfo_children():
            child.destroy()
            
        self.multiStartCanvases = []
        self.multiStartStatusLabels = []
        self.multiStartInitialCanvases = []
        self.multiStartPathLabels = []
        
        k = int(self.comboK.get())
        
        # If k <= 5: 1 row, cell size 50
        # If k > 5: 2 rows of max 5 columns, cell size 32
        if k <= 5:
            cell = 50
        else:
            cell = 32
            
        canvas_w = cell * 3 + 20
        canvas_h = cell * 3 + 20
        
        # Configure row configurations
        self.multiStartCol.grid_rowconfigure(0, weight=1)
        if k > 5:
            self.multiStartCol.grid_rowconfigure(1, weight=1)
        else:
            self.multiStartCol.grid_rowconfigure(1, weight=0)
            
        max_cols = 5 if k > 5 else k
        for col_idx in range(max_cols):
            self.multiStartCol.grid_columnconfigure(col_idx, weight=1)
        for col_idx in range(max_cols, 10):
            self.multiStartCol.grid_columnconfigure(col_idx, weight=0)
        
        for j in range(k):
            row = j // 5 if k > 5 else 0
            col = j % 5 if k > 5 else j
            
            colFrame = tk.Frame(self.multiStartCol, bg=BG, highlightthickness=1, highlightbackground=BORDER)
            colFrame.grid(row=row, column=col, padx=4, pady=4, sticky='nsew')
            
            titleLbl = tk.Label(colFrame, text=f"STATE {j+1}", font=('Segoe UI', 9, 'bold'), bg=PANEL, fg=BLACK)
            titleLbl.pack(fill='x', ipady=4)
            tk.Frame(colFrame, bg=BORDER, height=1).pack(fill='x')
            
            statusLbl = tk.Label(colFrame, text="Đang giải", font=('Segoe UI', 8, 'bold'), bg=BG, fg=ORANGE)
            statusLbl.pack(pady=(6, 2))
            self.multiStartStatusLabels.append(statusLbl)
            
            canvas = tk.Canvas(colFrame, width=canvas_w, height=canvas_h, bg=BG, highlightthickness=0)
            canvas.pack(pady=2)
            self.multiStartCanvases.append(canvas)
            
            tk.Frame(colFrame, bg=BORDER, height=1).pack(fill='x', pady=6)
            
            pathLbl = tk.Label(colFrame, text="Đường đi: —", font=('Segoe UI', 8), bg=BG, fg=GRAY, wraplength=170)
            pathLbl.pack(pady=2)
            self.multiStartPathLabels.append(pathLbl)
            
            initFrame = tk.Frame(colFrame, bg=BG)
            initFrame.pack(pady=(4, 6))
            
            tk.Label(initFrame, text="Bắt đầu:", font=('Segoe UI', 8, 'italic'), bg=BG, fg=GRAY).pack(side='left', padx=(0, 4))
            
            initCanvas = tk.Canvas(initFrame, width=40, height=40, bg=BG, highlightthickness=0)
            initCanvas.pack(side='left')
            self.multiStartInitialCanvases.append(initCanvas)

    def _loadMultiStartSearch(self) -> None:
        self.steps, self.exploredMaster = SearchEngine.runMultiStartAStar(self.multiStartStates, self.goalState)
        self.idx = 0
        self.algoTitleVar.set(f'8-Puzzle — Multi-Start Greedy (k={len(self.multiStartStates)})')
        self._render(0)

    def _updateLayoutForGroup(self, groupName: str) -> None:
        if groupName == 'Constraint satisfaction problems':
            self.leftCol.pack_forget()
            self.frontierCol.pack_forget()
            self.exploredCol.pack_forget()
            if hasattr(self, 'multiStartCol'):
                self.multiStartCol.pack_forget()
            if hasattr(self, 'multiStartCtrlFrame'):
                self.multiStartCtrlFrame.pack_forget()
            if hasattr(self, 'btnCustomStates'):
                self.btnCustomStates.grid_forget()
            if hasattr(self, 'banner'):
                self.banner.pack_forget()
                
            self.cspCol.pack(side='left', fill='both', expand=True, pady=(0, 8))
            self._loadAlgorithm(self.currentAlgoName)
        elif groupName == 'Multi Start State':
            self.leftCol.pack_forget()
            self.frontierCol.pack_forget()
            self.exploredCol.pack_forget()
            if hasattr(self, 'cspCol'):
                self.cspCol.pack_forget()
            if hasattr(self, 'banner'):
                self.banner.pack_forget()
                
            if hasattr(self, 'btnCustomStates'):
                self.btnCustomStates.grid_forget()
            if hasattr(self, 'multiStartCtrlFrame'):
                self.multiStartCtrlFrame.pack(side='left', padx=10)
                
            self.multiStartCol.pack(side='left', fill='both', expand=True, pady=(0, 8))
            
            k = int(self.comboK.get())
            if not hasattr(self, 'multiStartStates') or len(self.multiStartStates) != k:
                self._randomizeMultiStates()
            else:
                self._rebuildMultiStartPanels()
                for j in range(k):
                    canvas = self.multiStartInitialCanvases[j]
                    canvas.delete('all')
                    drawBoard(canvas, 2, 2, self.multiStartStates[j], cell=12, isGoalState=False)
                self._loadMultiStartSearch()
        else:
            if hasattr(self, 'multiStartCol'):
                self.multiStartCol.pack_forget()
            if hasattr(self, 'multiStartCtrlFrame'):
                self.multiStartCtrlFrame.pack_forget()
            if hasattr(self, 'cspCol'):
                self.cspCol.pack_forget()
                
            if hasattr(self, 'leftCol'):
                self.leftCol.pack(side='left', fill='y', padx=(0, 8))
            if hasattr(self, 'frontierCol'):
                self.frontierCol.pack(side='left', fill='both', expand=True, padx=(0, 8), pady=(0, 8))
            if hasattr(self, 'exploredCol'):
                self.exploredCol.pack(side='left', fill='y', pady=(0, 8))
                
            if hasattr(self, 'btnCustomStates'):
                self.btnCustomStates.grid(row=0, column=6, padx=8)
                
            if hasattr(self, 'banner'):
                self.banner.pack(side='bottom', fill='x', padx=10, pady=(0, 10))
                
            self._loadAlgorithm(self.currentAlgoName)

    def _renderMultiStart(self, step):
        phaseCfg = {
            'init':      (ACCENT, WHITE, '🔵', 'INIT'),
            'new_limit': (PURPLE, WHITE, '🟣', 'NEW LIMIT'),
            'restart':   (PURPLE, WHITE, '🟣', 'RESTART'),
            'expand':    (ORANGE, WHITE, '🟠', 'EXPAND'),
            'found':     (GREEN,  WHITE, '🟢', 'FOUND'),
            'cutoff':    ('#e3b341', BLACK, '🟡', 'CUTOFF'),
            'failure':   (RED,    WHITE, '🔴', 'FAIL'),
        }
        pc, fc, icon, badgeTxt = phaseCfg.get(step.phase, (GRAY, WHITE, '⬤', '?'))
        self.phaseIcon.config(text=icon, fg=pc)
        self.phaseBadge.config(text=badgeTxt, bg=pc, fg=fc)
        self.descLbl.config(text=step.desc)
        self.stepLbl.config(text=f'Bước {self.idx} / {len(self.steps) - 1}')
        
        self.detailCanvas.delete('all')
        if step.phase == 'expand' and step.newLabels:
            self.detailCanvas.create_text(10, 40, text=f"Sinh {len(step.newLabels)} Node con mới trong Frontier", font=('Segoe UI', 10, 'bold'), fill=BLACK, anchor='w')
            
        k = len(self.multiStartStates)
        node = step.currentNode
        
        cell = 50 if k <= 5 else 32
            
        for j in range(k):
            canvas = self.multiStartCanvases[j]
            statusLbl = self.multiStartStatusLabels[j]
            pathLbl = self.multiStartPathLabels[j]
            
            if node and node.state and j < len(node.state):
                board_state = node.state[j]
                # Calculate g_val
                if board_state == self.goalState:
                    curr = node
                    while curr.parent and j < len(curr.parent.state) and curr.parent.state[j] == self.goalState:
                        curr = curr.parent
                    g_val = curr.depth
                else:
                    g_val = node.depth
            else:
                board_state = self.multiStartStates[j]
                g_val = 0
                
            isGoal = (board_state == self.goalState)
            
            canvas.delete('all')
            drawBoard(canvas, 10, 10, board_state, cell=cell, isGoalState=isGoal)
            
            manh = calculateManhattanDistance(board_state, self.goalState)
            
            if isGoal:
                statusLbl.config(text=f"✓ ĐẠT GOAL (bước {g_val})\nh(n) = 0", fg=GREEN)
            else:
                statusLbl.config(text=f"⚡ ĐANG GIẢI\nh(n) = {manh}", fg=ORANGE)
                
            actions = []
            curr = node
            while curr and curr.parent:
                if curr.state and curr.parent.state:
                    board_state_curr = curr.state[j]
                    board_state_parent = curr.parent.state[j]
                    if board_state_curr != board_state_parent:
                        actions.append(curr.action)
                curr = curr.parent
            actions.reverse()
            
            if actions:
                path_str = " ➔ ".join(actions)
                if len(path_str) > 30:
                    path_str = "..." + path_str[-28:]
                pathLbl.config(text=f"Đường đi: {path_str}", fg=GRAY)
            else:
                pathLbl.config(text="Đường đi: —", fg=GRAY)

    def _onAlgoChange(self, event: tk.Event) -> None:
        newAlgo = self.comboAlgo.get()
        if newAlgo == self.currentAlgoName:
            return
        
        # If currently running or not at start, ask user
        if self.idx > 0 or self.autoMode:
            self._stopAuto()
            ans = messagebox.askyesno("Đổi thuật toán", "Thuật toán đang chạy. Bạn có muốn Reset để chuyển sang thuật toán mới không?\n(Đồng ý = Reset, Hủy = Tiếp tục hiện tại)")
            if not ans:
                self.comboAlgo.set(self.currentAlgoName)
                return
                
        self.currentAlgoName = newAlgo
        self._loadAlgorithm(newAlgo)

    def _onGroupChange(self, event: tk.Event) -> None:
        """Handles switching between algorithm groups (e.g. Uninformed, Heuristic, Hill Climbing)."""
        newGroup = self.comboGroup.get()
        if newGroup == self.currentGroupName:
            return
        
        if self.idx > 0 or self.autoMode:
            self._stopAuto()
            ans = messagebox.askyesno("Đổi nhóm thuật toán", "Thuật toán đang chạy. Bạn có muốn Reset để chuyển sang nhóm mới không?\n(Đòng ý = Reset, Hủy = Tiếp tục nhóm hiện tại)")
            if not ans:
                self.comboGroup.set(self.currentGroupName)
                return

        self.currentGroupName = newGroup
        algosInGroup = self.algoGroups[newGroup]
        self.comboAlgo.config(values=algosInGroup)
        
        firstAlgo = algosInGroup[0]
        self.comboAlgo.set(firstAlgo)
        self.currentAlgoName = firstAlgo
        self._updateLayoutForGroup(newGroup)

    def _buildUi(self):
        # ── Top Section (Header + Controls) ──
        topFrame = tk.Frame(self.root, bg=BG)
        topFrame.pack(fill='x', padx=16, pady=(10, 4))

        # 1. Header Row (Title & Step Counter)
        headerFrame = tk.Frame(topFrame, bg=BG)
        headerFrame.pack(fill='x', pady=(0, 8))

        self.algoTitleVar = tk.StringVar()
        tk.Label(headerFrame, textvariable=self.algoTitleVar, font=('Segoe UI', 15, 'bold'), bg=BG, fg=BLACK).pack(side='left')

        self.stepLbl = tk.Label(headerFrame, text='Bước 0 / 0', bg=BG, fg=GRAY, font=('Segoe UI', 11, 'bold'))
        self.stepLbl.pack(side='right')

        # 2. Toolbar Row (Filters, Navigation, Speed)
        toolbarFrame = tk.Frame(topFrame, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        toolbarFrame.pack(fill='x', ipady=6, pady=2)

        # Left subframe: Filters
        filterFrame = tk.Frame(toolbarFrame, bg=PANEL)
        filterFrame.pack(side='left', padx=10)

        tk.Label(filterFrame, text='Nhóm:', font=('Segoe UI', 9, 'bold'), bg=PANEL, fg=GRAY).pack(side='left', padx=(0, 4))
        self.comboGroup = ttk.Combobox(filterFrame, values=list(self.algoGroups.keys()), state='readonly', width=34, font=('Segoe UI', 9))
        self.comboGroup.set(self.currentGroupName)
        self.comboGroup.bind('<<ComboboxSelected>>', self._onGroupChange)
        self.comboGroup.pack(side='left', padx=(0, 10))

        tk.Label(filterFrame, text='Thuật toán:', font=('Segoe UI', 9, 'bold'), bg=PANEL, fg=GRAY).pack(side='left', padx=(0, 4))
        self.comboAlgo = ttk.Combobox(filterFrame, values=self.algoGroups[self.currentGroupName], state='readonly', width=26, font=('Segoe UI', 9))
        self.comboAlgo.set(self.currentAlgoName)
        self.comboAlgo.bind('<<ComboboxSelected>>', self._onAlgoChange)
        self.comboAlgo.pack(side='left')

        # Buttons style config
        bs = dict(font=('Segoe UI', 9, 'bold'), relief='flat', cursor='hand2', padx=8, pady=3, bd=0)

        # Multi-Start controls (hidden by default)
        self.multiStartCtrlFrame = tk.Frame(toolbarFrame, bg=PANEL)
        
        tk.Label(self.multiStartCtrlFrame, text='k Start States:', font=('Segoe UI', 9, 'bold'), bg=PANEL, fg=GRAY).pack(side='left', padx=(10, 4))
        self.comboK = ttk.Combobox(self.multiStartCtrlFrame, values=[str(i) for i in range(2, 11)], state='readonly', width=5, font=('Segoe UI', 9))
        self.comboK.set('3')
        self.comboK.bind('<<ComboboxSelected>>', self._onKChange)
        self.comboK.pack(side='left', padx=(0, 10))
        
        self.btnRandomMulti = tk.Button(self.multiStartCtrlFrame, text='🎲 Randomize', command=self._randomizeMultiStates, bg=ACCENT, fg=WHITE, **bs)
        self.btnRandomMulti.pack(side='left', padx=(0, 10))

        # Right subframe: Buttons + Speed
        rightCtrlFrame = tk.Frame(toolbarFrame, bg=PANEL)
        rightCtrlFrame.pack(side='right', padx=10)

        # Buttons
        btnFrame = tk.Frame(rightCtrlFrame, bg=PANEL)
        btnFrame.pack(side='left', padx=(0, 10))

        tk.Button(btnFrame, text='⏮', command=self._goFirst, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=0, padx=2)
        tk.Button(btnFrame, text='◀ Trước', command=self._goPrev, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=1, padx=2)
        self.btnAuto = tk.Button(btnFrame, text='▶ Auto', command=self._toggleAuto, bg=ACCENT, fg=WHITE, **bs)
        self.btnAuto.grid(row=0, column=2, padx=2)
        tk.Button(btnFrame, text='Tiếp ▶', command=self._goNext, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=3, padx=2)
        tk.Button(btnFrame, text='⏭', command=self._goLast, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=4, padx=2)
        tk.Button(btnFrame, text='🛣 Show Path', command=self._showPath, bg=PURPLE, fg=WHITE, **bs).grid(row=0, column=5, padx=8)
        self.btnCustomStates = tk.Button(btnFrame, text='✏️ Custom States', command=self._openCustomStatesDialog, bg=GRAY, fg=WHITE, **bs)
        self.btnCustomStates.grid(row=0, column=6, padx=8)

        # Speed scale
        speedFrame = tk.Frame(rightCtrlFrame, bg=PANEL)
        speedFrame.pack(side='left')
        tk.Label(speedFrame, text='Tốc độ (ms):', bg=PANEL, fg=GRAY, font=('Segoe UI', 9)).pack(side='left', padx=(0, 4))
        tk.Scale(speedFrame, from_=50, to=1500, orient='horizontal', variable=self.speed, bg=PANEL, fg=BLACK, troughcolor=BORDER, highlightthickness=0, length=90, showvalue=False).pack(side='left')

        # ── Bottom Section (Step Info) ──
        self._buildBottomBar()

        # ── Middle Section (Main Layout) ──
        body = tk.Frame(self.root, bg=BG)
        body.pack(fill='both', expand=True, padx=10, pady=4)
        self.body = body

        # Left Column (Current Node + Goal)
        self.leftCol = tk.Frame(body, bg=BG, width=340)
        self.leftCol.pack(side='left', fill='y', padx=(0, 8))
        self.leftCol.pack_propagate(False)

        self._buildCurrentNodePanel(self.leftCol)
        self._buildGoalPanel(self.leftCol)

        # Center Column (Frontier)
        self._buildFrontierPanel(body)

        # Right Column (Explored)
        self._buildExploredPanel(body)

        # Multi Start MAIN Column (Hidden initially)
        self.multiStartCol = tk.Frame(body, bg=BG)
        
        # CSP Column
        self.cspCol = tk.Frame(body, bg=BG)
        self._buildCspPanel(self.cspCol)

    def _buildCspPanel(self, parent):
        self.cspLeftFrame = tk.Frame(parent, bg=BG, highlightthickness=1, highlightbackground=BORDER)
        self.cspLeftFrame.pack(side='left', fill='both', expand=True, padx=(0, 8))
        tk.Label(self.cspLeftFrame, text="Đồ thị / Bài toán Cung", font=('Segoe UI', 10, 'bold'), bg=PANEL, fg=BLACK).pack(fill='x', ipady=4)
        tk.Frame(self.cspLeftFrame, bg=BORDER, height=1).pack(fill='x')
        self.cspCanvas = tk.Canvas(self.cspLeftFrame, bg=BG, highlightthickness=0)
        self.cspCanvas.pack(fill='both', expand=True, padx=10, pady=10)

        self.cspRightFrame = tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=BORDER, width=320)
        self.cspRightFrame.pack(side='right', fill='y')
        self.cspRightFrame.pack_propagate(False)
        tk.Label(self.cspRightFrame, text="Thông tin chi tiết", font=('Segoe UI', 10, 'bold'), bg=PANEL, fg=BLACK).pack(fill='x', ipady=4)
        tk.Frame(self.cspRightFrame, bg=BORDER, height=1).pack(fill='x')
        
        self.cspDescLbl = tk.Label(self.cspRightFrame, text="", font=('Segoe UI', 10), bg=PANEL, fg=BLACK, justify='left', anchor='nw', wraplength=290)
        self.cspDescLbl.pack(fill='x', padx=10, pady=10)
        
        tk.Frame(self.cspRightFrame, bg=BORDER, height=1).pack(fill='x', padx=10, pady=5)
        
        tk.Label(self.cspRightFrame, text="Assignments / Arc:", font=('Segoe UI', 9, 'bold'), bg=PANEL, fg=GRAY, anchor='w').pack(fill='x', padx=10)
        self.cspAssignmentLbl = tk.Label(self.cspRightFrame, text="", font=('Consolas', 9), bg=PANEL, fg=PURPLE, justify='left', anchor='nw', wraplength=290)
        self.cspAssignmentLbl.pack(fill='x', padx=10, pady=5)
        
        self.cspDomainTitleLbl = tk.Label(self.cspRightFrame, text="Domains:", font=('Segoe UI', 9, 'bold'), bg=PANEL, fg=GRAY, anchor='w')
        self.cspDomainTitleLbl.pack(fill='x', padx=10)
        self.cspDomainLbl = tk.Label(self.cspRightFrame, text="", font=('Consolas', 9), bg=PANEL, fg=ACCENT, justify='left', anchor='nw', wraplength=290)
        self.cspDomainLbl.pack(fill='x', padx=10, pady=5)

    def _panel(self, parent, title):
        f = tk.Frame(parent, bg=BG, highlightthickness=1, highlightbackground=BORDER)
        f.pack(fill='both', expand=True, pady=(0, 8))
        tk.Label(f, text=title, bg=PANEL, fg=BLACK, font=('Segoe UI', 10, 'bold')).pack(fill='x', ipady=4)
        tk.Frame(f, bg=BORDER, height=1).pack(fill='x')
        return f

    def _buildCurrentNodePanel(self, parent):
        pnl = self._panel(parent, 'Trạng thái & Thuộc tính Node')
        
        self.curCanvas = tk.Canvas(pnl, width=150, height=150, bg=BG, highlightthickness=0)
        self.curCanvas.pack(pady=(14, 4))

        self.curLabel = tk.Label(pnl, text='—', bg=BG, fg=BLACK, font=('Segoe UI', 13, 'bold'))
        self.curLabel.pack(pady=(0, 4))
        self.curAction = tk.Label(pnl, text='', bg=BG, fg=ORANGE, font=('Segoe UI', 11))
        self.curAction.pack()
        self.curCost = tk.Label(pnl, text='', bg=BG, fg=GREEN, font=('Segoe UI', 11))
        self.curCost.pack()
        self.curDepth = tk.Label(pnl, text='', bg=BG, fg=GRAY, font=('Segoe UI', 11))
        self.curDepth.pack()
        self.curParent = tk.Label(pnl, text='', bg=BG, fg=PURPLE, font=('Segoe UI', 11))
        self.curParent.pack(pady=(0, 8))

    def _buildGoalPanel(self, parent):
        pnl = self._panel(parent, 'Goal Node')
        self.goalCanvas = tk.Canvas(pnl, width=150, height=150, bg=BG, highlightthickness=0)
        self.goalCanvas.pack(pady=(14, 4))
        self._drawGoalBoard()

    def _buildFrontierPanel(self, parent):
        self.frontierTitleVar = tk.StringVar(value='Frontier')
        self.frontierCol = tk.Frame(parent, bg=BG, highlightthickness=1, highlightbackground=BORDER)
        self.frontierCol.pack(side='left', fill='both', expand=True, padx=(0, 8), pady=(0, 8))
        
        tk.Label(self.frontierCol, textvariable=self.frontierTitleVar, bg=PANEL, fg=BLACK, font=('Segoe UI', 10, 'bold')).pack(fill='x', ipady=4)
        tk.Frame(self.frontierCol, bg=BORDER, height=1).pack(fill='x')

        wrapper = tk.Frame(self.frontierCol, bg=BG)
        wrapper.pack(fill='both', expand=True, padx=4, pady=4)
        vsb = tk.Scrollbar(wrapper, orient='vertical', bg=BG, troughcolor=PANEL, width=10)
        vsb.pack(side='right', fill='y')
        self.frCanvas = tk.Canvas(wrapper, bg=BG, yscrollcommand=vsb.set, highlightthickness=0)
        self.frCanvas.pack(side='left', fill='both', expand=True)
        vsb.config(command=self.frCanvas.yview)
        self.frCanvas.bind('<Configure>', lambda e: self.frCanvas.configure(scrollregion=self.frCanvas.bbox('all')))
        self.frCanvas.bind('<MouseWheel>', lambda e: self.frCanvas.yview_scroll(-1 * (e.delta // 120), 'units'))

    def _buildExploredPanel(self, parent):
        self.exploredCol = tk.Frame(parent, bg=BG, highlightthickness=1, highlightbackground=BORDER, width=280)
        self.exploredCol.pack(side='left', fill='y', pady=(0, 8))
        self.exploredCol.pack_propagate(False)
        
        tk.Label(self.exploredCol, text='Explored', bg=PANEL, fg=BLACK, font=('Segoe UI', 10, 'bold')).pack(fill='x', ipady=4)
        tk.Frame(self.exploredCol, bg=BORDER, height=1).pack(fill='x')

        wrapper = tk.Frame(self.exploredCol, bg=BG)
        wrapper.pack(fill='both', expand=True, padx=4, pady=4)
        vsb = tk.Scrollbar(wrapper, orient='vertical', bg=BG, troughcolor=PANEL, width=10)
        vsb.pack(side='right', fill='y')
        self.exCanvas = tk.Canvas(wrapper, bg=BG, yscrollcommand=vsb.set, highlightthickness=0)
        self.exCanvas.pack(side='left', fill='both', expand=True)
        vsb.config(command=self.exCanvas.yview)
        self.exCanvas.bind('<Configure>', lambda e: self.exCanvas.configure(scrollregion=self.exCanvas.bbox('all')))
        self.exCanvas.bind('<MouseWheel>', lambda e: self.exCanvas.yview_scroll(-1 * (e.delta // 120), 'units'))

    def _buildBottomBar(self):
        self.banner = tk.Frame(self.root, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        self.banner.pack(side='bottom', fill='x', padx=10, pady=(0, 10))

        bannerInner = tk.Frame(self.banner, bg=PANEL)
        bannerInner.pack(fill='x', padx=14, pady=8)

        # Left section: Icon, Badge, Text
        leftInfo = tk.Frame(bannerInner, bg=PANEL)
        leftInfo.pack(side='left', fill='y', padx=(0, 20))

        iconFrame = tk.Frame(leftInfo, bg=PANEL)
        iconFrame.pack(anchor='w', pady=(0, 4))

        self.phaseIcon = tk.Label(iconFrame, text='⬤', bg=PANEL, font=('Segoe UI', 14), fg=ACCENT)
        self.phaseIcon.pack(side='left', padx=(0, 8))

        self.phaseBadge = tk.Label(iconFrame, text='INIT', bg=ACCENT, fg=WHITE, font=('Segoe UI', 9, 'bold'), padx=8, pady=2)
        self.phaseBadge.pack(side='left')

        self.descLbl = tk.Label(leftInfo, text='', bg=PANEL, fg=BLACK, font=('Segoe UI', 11, 'bold'), anchor='nw', justify='left', width=65)
        self.descLbl.pack(anchor='w', fill='y', expand=True)

        # Right section: Canvas for newly generated nodes
        self.detailCanvas = tk.Canvas(bannerInner, bg=PANEL, highlightthickness=0, height=85)
        self.detailCanvas.pack(side='left', fill='both', expand=True)

    def _drawDetailNodes(self, canvas, nodes):
        """Draws a list of newly generated nodes horizontally."""
        canvas.delete('all')
        if not nodes:
            return

        startX = 10
        startY = 10
        nodeWidth = 140
        
        for i, n in enumerate(nodes):
            x = startX + i * nodeWidth
            y = startY
            
            # Draw board
            drawBoard(canvas, x, y, n.state, cell=15, newCells=[])
            
            # Label
            lblText = f"[{n.label}]  ★NEW"
            canvas.create_text(x + 55, y + 6, text=lblText, font=('Segoe UI', 9, 'bold'), fill=ORANGE, anchor='w')
            
            # Action
            actStr = f"Act: {ARROW_MAP.get(n.action, '')}"
            c_y = y + 20
            canvas.create_text(x + 55, c_y, text=actStr, font=('Consolas', 8), fill=BLACK, anchor='w')
            c_y += 14
            
            # Depth/Cost
            infoStr = f"Dep: {n.depth}"
            if 'UCS' in self.currentAlgoName and n.cost > 0:
                infoStr += f" | C:{n.cost}"
            elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName or 'Beam Search' in self.currentAlgoName:
                infoStr += f" | h:{n.h}"
            elif 'A*' in self.currentAlgoName or 'IDA*' in self.currentAlgoName:
                infoStr += f" | f:{n.cost}"
            canvas.create_text(x + 55, c_y, text=infoStr, font=('Consolas', 8), fill=GRAY, anchor='w')
            c_y += 14
            
            if 'A*' in self.currentAlgoName or 'IDA*' in self.currentAlgoName:
                canvas.create_text(x + 55, c_y, text=f"g:{n.g}, h:{n.h}", font=('Consolas', 8), fill=GRAY, anchor='w')
                c_y += 14
            
            # Parent
            parStr = f"Par: [{n.parentLabel}]" if n.parentLabel else ""
            if parStr:
                canvas.create_text(x + 55, c_y, text=parStr, font=('Consolas', 8), fill=PURPLE, anchor='w')


    def _showPath(self):
        """Displays the path to the goal using the new two-pane layout."""
        foundStep = next((s for s in self.steps if s.phase == 'found'), None)
        if not foundStep or not foundStep.currentNode:
            messagebox.showinfo('Đường đi', 'Chưa tìm thấy Goal để hiển thị đường đi.')
            return
            
        pathNodes = []
        curr = foundStep.currentNode
        while curr:
            pathNodes.append(curr)
            curr = getattr(curr, 'parent', None)
        pathNodes.reverse()
        
        top = tk.Toplevel(self.root)
        top.title(f"Đường đi tới Goal ({len(pathNodes)-1} bước)")
        
        isMultiStart = (self.currentGroupName == 'Multi Start State')
        
        if isMultiStart:
            k = len(self.multiStartStates)
            top.geometry(f"{min(1200, 220 * k + 300)}x500")
        else:
            top.geometry("700x450")
            
        top.configure(bg=BG)

        leftPane = tk.Frame(top, bg=BG, width=420 if isMultiStart else 300)
        leftPane.pack(side='left', fill='both', expand=True, padx=10, pady=10)
        
        tk.Label(leftPane, text="Trạng thái Node", font=('Segoe UI', 11, 'bold'), bg=BG, fg=BLACK).pack(pady=(0, 10))
        
        if isMultiStart:
            canvasFrame = tk.Frame(leftPane, bg=BG)
            canvasFrame.pack(fill='both', expand=True)
            
            canvases = []
            k = len(self.multiStartStates)
            for j in range(k):
                f = tk.Frame(canvasFrame, bg=BG, highlightthickness=1, highlightbackground=BORDER)
                f.pack(side='left', fill='both', expand=True, padx=4)
                tk.Label(f, text=f"Bản đồ {j+1}", font=('Segoe UI', 8, 'bold'), bg=BG, fg=BLACK).pack(pady=2)
                c = tk.Canvas(f, width=120, height=120, bg=BG, highlightthickness=0)
                c.pack(padx=4, pady=4, expand=True)
                canvases.append(c)
        else:
            leftPane.pack_propagate(False)
            canvasLeft = tk.Canvas(leftPane, width=280, height=350, bg=BG, highlightthickness=1, highlightbackground=BORDER)
            canvasLeft.pack()

        rightPane = tk.Frame(top, bg=BG, width=280)
        rightPane.pack(side='right', fill='y', padx=10, pady=10)
        rightPane.pack_propagate(False)

        tk.Label(rightPane, text="Thông tin chi tiết", font=('Segoe UI', 11, 'bold'), bg=BG, fg=BLACK).pack(pady=(0, 10))
        
        detailsFrame = tk.Frame(rightPane, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        detailsFrame.pack(fill='both', expand=True)

        infoLbl = tk.Label(detailsFrame, text="", font=('Segoe UI', 10), bg=PANEL, fg=BLACK, justify='left', anchor='nw', wraplength=250)
        infoLbl.pack(padx=15, pady=15, fill='both', expand=True)

        currentIdx = [0]

        def drawStep(idx):
            node = pathNodes[idx]
            isGoal = (idx == len(pathNodes) - 1)
            
            if isMultiStart:
                for j in range(len(self.multiStartStates)):
                    c = canvases[j]
                    c.delete('all')
                    b_state = node.state[j]
                    b_is_goal = (b_state == self.goalState)
                    drawBoard(c, 15, 15, b_state, cell=30, isGoalState=b_is_goal)
                    
                act = ARROW_MAP.get(node.action, 'Start') if node.action else 'Start'
                details = (
                    f"Bước số: {idx}\n\n"
                    f"Hành động chung: {act}\n"
                    f"Độ sâu tổng: {node.depth}\n"
                    f"Tổng h(n): {node.cost}\n"
                )
                if isGoal:
                    details += "\n🎉 Tất cả bản đồ đã đạt Goal!"
                infoLbl.config(text=details)
            else:
                canvasLeft.delete('all')
                drawBoard(canvasLeft, 110, 145, node.state, cell=30, isGoalState=isGoal)
                
                act = ARROW_MAP.get(node.action, 'Start') if node.action else 'Start'
                par = f"Parent: [{node.parentLabel}]" if node.parentLabel else "Parent: None"
                details = (
                    f"Bước số: {idx}\n\n"
                    f"Tên Node: [{node.label}]\n"
                    f"Hành động để đạt tới: {act}\n"
                    f"Độ sâu (Depth): {node.depth}\n"
                    f"Cost/f: {node.cost}\n"
                    f"h: {node.h}, g: {node.g}\n"
                    f"{par}\n\n"
                )
                if isGoal:
                    details += "🎉 Đã tới đích!"
                infoLbl.config(text=details)

        def goPrevPath():
            if currentIdx[0] > 0:
                currentIdx[0] -= 1
                drawStep(currentIdx[0])

        def goNextPath():
            if currentIdx[0] < len(pathNodes) - 1:
                currentIdx[0] += 1
                drawStep(currentIdx[0])

        btnFrame = tk.Frame(rightPane, bg=BG)
        btnFrame.pack(pady=10)
        tk.Button(btnFrame, text="◀ Trước", command=goPrevPath, width=10, bg=PANEL).pack(side='left', padx=5)
        tk.Button(btnFrame, text="Tiếp ▶", command=goNextPath, width=10, bg=PANEL).pack(side='left', padx=5)

        drawStep(0)

    def _render(self, idx):
        idx = max(0, min(idx, len(self.steps) - 1))
        self.idx = idx
        step = self.steps[idx]
        
        if self.currentGroupName == 'Multi Start State':
            self._renderMultiStart(step)
            return
            
        if self.currentGroupName == 'Constraint satisfaction problems':
            self._renderCSP(step)
            return
        
    def _renderCSP(self, step):
        self.stepLbl.config(text=f'Bước {self.idx} / {len(self.steps) - 1}')
        self.cspDescLbl.config(text=step.desc)
        
        node = step.currentNode
        self.cspCanvas.delete('all')
        
        if node and node.state:
            state_type = node.state[0]
            if state_type in ['CSP_Graph', 'CSP_Graph_FC']:
                # The scale factor is (cell * 3) / 200, so cell=150 scales by 450/200 = 2.25
                drawCSPGraph(self.cspCanvas, 30, 30, node.state[1], cell=150)
                
                assign_text = ""
                for k, v in node.state[1]:
                    assign_text += f"• {k}: {v}\n"
                self.cspAssignmentLbl.config(text=assign_text if assign_text else "Chưa gán.")
                
                if state_type == 'CSP_Graph_FC':
                    self.cspDomainTitleLbl.pack(fill='x', padx=10)
                    self.cspDomainLbl.pack(fill='x', padx=10, pady=5)
                    dom_text = ""
                    for k, v in node.state[2]:
                        dom_text += f"• {k}: {', '.join(v)}\n"
                    self.cspDomainLbl.config(text=dom_text)
                else:
                    self.cspDomainTitleLbl.pack_forget()
                    self.cspDomainLbl.pack_forget()
                    
            elif state_type == 'CSP_Arc':
                drawCSPArc(self.cspCanvas, 30, 30, node.state[1], cell=150)
                
                self.cspAssignmentLbl.config(text="Kiểm tra tính nhất quán cung.")
                self.cspDomainTitleLbl.pack(fill='x', padx=10)
                self.cspDomainLbl.pack(fill='x', padx=10, pady=5)
                
                dom_text = ""
                for k, v in node.state[1]:
                    dom_text += f"• D({k}): {{{', '.join(map(str, v))}}}\n"
                self.cspDomainLbl.config(text=dom_text)

        # Determine specific frontier details
        if 'BFS' in self.currentAlgoName:
            self.frontierTitleVar.set('Frontier — Queue (FIFO)')
        elif 'DFS' in self.currentAlgoName or 'IDS' in self.currentAlgoName:
            self.frontierTitleVar.set('Frontier — Stack (LIFO)')
        elif 'UCS' in self.currentAlgoName:
            self.frontierTitleVar.set('Frontier — Priority Queue (Min-Cost)')
        elif 'Greedy' in self.currentAlgoName or 'A*' in self.currentAlgoName:
            self.frontierTitleVar.set('Frontier — Priority List (Min-Eval)')
        elif 'IDA*' in self.currentAlgoName:
            self.frontierTitleVar.set('Frontier — Active Nodes (f-Limit)')
        elif 'Hill Climbing' in self.currentAlgoName:
            self.frontierTitleVar.set('Frontier — Neighbors (Candidates)')
        elif 'Beam Search' in self.currentAlgoName:
            self.frontierTitleVar.set('Frontier — Active Beam / Neighbors')

        # Phase banner styling
        phaseCfg = {
            'init':      (ACCENT, WHITE, '🔵', 'INIT'),
            'new_limit': (PURPLE, WHITE, '🟣', 'NEW LIMIT'),
            'restart':   (PURPLE, WHITE, '🟣', 'RESTART'),
            'expand':    (ORANGE, WHITE, '🟠', 'EXPAND'),
            'found':     (GREEN,  WHITE, '🟢', 'FOUND'),
            'cutoff':    ('#e3b341', BLACK, '🟡', 'CUTOFF'),
            'failure':   (RED,    WHITE, '🔴', 'FAIL'),
        }
        pc, fc, icon, badgeTxt = phaseCfg.get(step.phase, (GRAY, WHITE, '⬤', '?'))
        self.phaseIcon.config(text=icon, fg=pc)
        self.phaseBadge.config(text=badgeTxt, bg=pc, fg=fc)
        self.descLbl.config(text=step.desc)
        self.stepLbl.config(text=f'Bước {self.idx} / {len(self.steps) - 1}')

        # Draw newly generated children in detail canvas
        self.detailCanvas.delete('all')
        if step.phase == 'expand' and step.newLabels:
            newNodes = []
            for n in step.frontier:
                if n.label in step.newLabels:
                    newNodes.append(n)
            newNodes.sort(key=lambda x: x.label)
            self._drawDetailNodes(self.detailCanvas, newNodes)

        # Current Node
        self.curCanvas.delete('all')
        known = getattr(step, 'known_positions', None)
        if step.currentNode:
            if isinstance(step.currentNode, list):
                if len(step.currentNode) > 0:
                    n = step.currentNode[0]
                    isGoal = any(x.state == self.goalState for x in step.currentNode)
                    drawBoard(self.curCanvas, 10, 10, n.state, cell=43, isGoalState=isGoal, knownCells=known)
                    self.curLabel.config(text=f'Beam: {len(step.currentNode)} Nodes')
                    self.curAction.config(text=f'Trạng thái: Đang xét chùm')
                    self.curCost.config(text='')
                    self.curDepth.config(text='')
                    self.curParent.config(text='')
                else:
                    self.curLabel.config(text='—')
                    self.curAction.config(text='')
                    self.curCost.config(text='')
                    self.curDepth.config(text='')
                    self.curParent.config(text='')
            else:
                n = step.currentNode
                # Belief State rendering
                if n.state and isinstance(n.state[0], tuple) and isinstance(n.state[0][0], tuple):
                    bs = n.state
                    self.curCanvas.config(width=20 + len(bs) * 110, height=130)
                    for i, s in enumerate(bs):
                        isGoal = False
                        if hasattr(self, 'currentGoalStates'):
                            isGoal = s in self.currentGoalStates
                        drawBoard(self.curCanvas, 10 + i * 110, 10, s, cell=33, isGoalState=isGoal, knownCells=known)
                else:
                    self.curCanvas.config(width=150, height=150)
                    isGoal = False
                    if hasattr(self, 'currentGoalStates'):
                        isGoal = n.state in self.currentGoalStates
                    else:
                        isGoal = (n.state == self.goalState)
                    drawBoard(self.curCanvas, 10, 10, n.state, cell=43, isGoalState=isGoal, knownCells=known)
                    
                self.curLabel.config(text=f'Node [{n.label}]')
                self.curAction.config(text=f'Action: {ARROW_MAP.get(n.action, "Start")}' if n.action else 'Action: Start')
                if 'UCS' in self.currentAlgoName:
                    self.curCost.config(text=f'Cost: {n.cost}')
                elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName or 'Beam Search' in self.currentAlgoName:
                    self.curCost.config(text=f'h(n): {n.h}')
                elif 'A*' in self.currentAlgoName or 'IDA*' in self.currentAlgoName:
                    self.curCost.config(text=f'f={n.cost} (g={n.g}, h={n.h})')
                else:
                    self.curCost.config(text='')
                self.curDepth.config(text=f'Depth: {n.depth}')
                self.curParent.config(text=f'Parent: [{n.parentLabel}]' if n.parentLabel else 'Parent: —')
        else:
            self.curLabel.config(text='—')
            self.curAction.config(text='')
            self.curCost.config(text='')
            self.curDepth.config(text='')
            self.curParent.config(text='')

        self._drawFrontier(step)
        self._drawExplored(step)

    def _drawFrontier(self, step):
        c = self.frCanvas
        c.delete('all')
        isBeliefStateEnv = self.currentAlgoName in ['Searching with no observation', 'Searching for partially observable problems']
        colW = 280 if isBeliefStateEnv else 160
        itemH = 104
        padX = 10
        padY = 8

        cw = max(c.winfo_width(), 300)
        cols = max(1, cw // colW)

        display = []
        hasGhost = False
        
        isQueueLike = 'BFS' in self.currentAlgoName or 'UCS' in self.currentAlgoName or 'Greedy' in self.currentAlgoName or 'A*' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName or 'Beam Search' in self.currentAlgoName
        # Order of ghost depends on algorithm
        if isQueueLike:
            if step.currentNode and step.phase in ('expand', 'found', 'failure', 'cutoff'):
                if isinstance(step.currentNode, list):
                    for cn in step.currentNode:
                        display.append(('ghost', cn))
                    hasGhost = True
                else:
                    display.append(('ghost', step.currentNode))
                    hasGhost = True
            for node in step.frontier:
                display.append(('normal', node))
        else: # DFS, IDS, IDA*
            for node in step.frontier:
                display.append(('normal', node))
            if step.currentNode and step.phase in ('expand', 'found', 'cutoff', 'failure'):
                if isinstance(step.currentNode, list):
                    for cn in step.currentNode:
                        display.append(('ghost', cn))
                    hasGhost = True
                else:
                    display.append(('ghost', step.currentNode))
                    hasGhost = True

        nFrontier = len(step.frontier)
        showNext = step.phase in ('init', 'new_limit', 'expand', 'cutoff') and nFrontier > 0
        known = getattr(step, 'known_positions', None)

        nextCurrentNodeLabels = set()
        if self.idx < len(self.steps) - 1:
            nextStep = self.steps[self.idx + 1]
            if 'Beam Search' in self.currentAlgoName:
                if nextStep.phase == 'cutoff':
                    nextCurrentNodeLabels = {n.label for n in nextStep.frontier}
                elif nextStep.phase == 'expand':
                    nextCurrentNodeLabels = {n.label for n in step.frontier}
                elif nextStep.phase == 'found' and nextStep.currentNode:
                    nextCurrentNodeLabels.add(nextStep.currentNode.label)
            else:
                if nextStep.currentNode:
                    nextCurrentNodeLabels.add(nextStep.currentNode.label)

        for i, (kind, node) in enumerate(display):
            col = i % cols
            row = i // cols
            x0 = padX + col * colW
            y0 = padY + row * itemH

            isGoal = (node.state == self.goalState)
            isNew = node.label in step.newLabels
            isGhost = (kind == 'ghost')
            
            isNext = False
            if showNext and not isGhost and (node.label in nextCurrentNodeLabels):
                isNext = True

            isBeliefState = node.state and isinstance(node.state[0], tuple) and isinstance(node.state[0][0], tuple)
            draw_cell = 14 if isBeliefState else CELL_SIZE

            if isGhost:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill=TILE_BLANK, outline=GRAY, width=1, dash=(4, 4))
            elif isNext:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill='#e1f0ff', outline=ACCENT, width=2)
            elif isNew:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill='#fff8e6', outline=ORANGE, width=1)
            elif isGoal:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill='#e6ffec', outline=GREEN, width=1)

            if isBeliefState:
                bs = node.state
                spacing = 3 * draw_cell + 6
                for j, s in enumerate(bs):
                    is_goal = False
                    if hasattr(self, 'currentGoalStates'):
                        is_goal = s in self.currentGoalStates
                    drawBoard(c, x0 + 2 + j * spacing, y0 + 4, s, cell=draw_cell, highlight='ghost' if isGhost else None, isGoalState=is_goal if not isGhost else False, knownCells=known)
                tx = x0 + len(bs) * spacing + 6
            else:
                drawBoard(c, x0 + 2, y0 + 4, node.state, cell=draw_cell, highlight='ghost' if isGhost else None, isGoalState=isGoal if not isGhost else False, knownCells=known)
                tx = x0 + 3 * draw_cell + 8
                
            ty = y0 + 4
            ghostClr = GRAY

            if isGhost:
                c.create_text(tx, ty, text=f'[{node.label}]', anchor='nw', fill=GRAY, font=('Segoe UI', 8, 'bold'))
                y_offset = ty + 14
                act = ARROW_MAP.get(node.action, 'Start') if node.action else 'Start'
                c.create_text(tx, y_offset, text=f'Act: {act}', anchor='nw', fill=ghostClr, font=('Consolas', 8))
                y_offset += 14
                
                if 'UCS' in self.currentAlgoName:
                    c.create_text(tx, y_offset, text=f'Cost: {node.cost}', anchor='nw', fill=ghostClr, font=('Consolas', 8))
                    y_offset += 14
                elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName or 'Beam Search' in self.currentAlgoName:
                    c.create_text(tx, y_offset, text=f'h(n): {node.h}', anchor='nw', fill=ghostClr, font=('Consolas', 8))
                    y_offset += 14
                elif 'A*' in self.currentAlgoName or 'IDA*' in self.currentAlgoName:
                    c.create_text(tx, y_offset, text=f'f={node.cost}', anchor='nw', fill=ghostClr, font=('Consolas', 8))
                    y_offset += 14
                    c.create_text(tx, y_offset, text=f'g={node.g}, h={node.h}', anchor='nw', fill=ghostClr, font=('Consolas', 8))
                    y_offset += 14
                
                c.create_text(tx, y_offset, text=f'Depth: {node.depth}', anchor='nw', fill=ghostClr, font=('Consolas', 8))
            else:
                tag = '  ⏩NEXT' if isNext else ('  ★NEW' if isNew else '')
                lblCol = ACCENT if isNext else (ORANGE if isNew else (GREEN if isGoal else BLACK))
                c.create_text(tx, ty, text=f'[{node.label}]{tag}', anchor='nw', fill=lblCol, font=('Segoe UI', 8, 'bold'))
                
                y_offset = ty + 14
                act = ARROW_MAP.get(node.action, 'Start') if node.action else 'Start'
                c.create_text(tx, y_offset, text=f'Act: {act}', anchor='nw', fill=BLACK, font=('Consolas', 8))
                y_offset += 14
                
                if 'UCS' in self.currentAlgoName:
                    c.create_text(tx, y_offset, text=f'Cost: {node.cost}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                    y_offset += 14
                elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName or 'Beam Search' in self.currentAlgoName:
                    c.create_text(tx, y_offset, text=f'h(n): {node.h}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                    y_offset += 14
                elif 'A*' in self.currentAlgoName or 'IDA*' in self.currentAlgoName:
                    c.create_text(tx, y_offset, text=f'f={node.cost}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                    y_offset += 14
                    c.create_text(tx, y_offset, text=f'g={node.g}, h={node.h}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                    y_offset += 14
                
                c.create_text(tx, y_offset, text=f'Depth: {node.depth}', anchor='nw', fill=GRAY, font=('Consolas', 8))

        totalItems = len(display)
        totalRows = (totalItems + cols - 1) // cols if totalItems else 1
        totalH = padY * 2 + totalRows * itemH
        c.configure(scrollregion=(0, 0, cw, max(totalH, c.winfo_height())))

        if not display:
            c.create_text(cw // 2, 60, text='∅  (Frontier rỗng)', fill=GRAY, font=('Segoe UI', 11))

    def _drawExplored(self, step):
        c = self.exCanvas
        c.delete('all')
        itemH = 104
        padX = 10
        padY = 8

        # Get explored list based on algorithm
        if step.exploredCount is not None:
            exploredList = self.exploredMaster[:step.exploredCount]
        else:
            exploredList = step.explored
            
        known = getattr(step, 'known_positions', None)

        for i, node in enumerate(reversed(exploredList)):
            y0 = padY + i * itemH
            isGoal = (node.state == self.goalState)

            if i > 0:
                c.create_line(padX, y0 - 4, 260, y0 - 4, fill=BORDER, width=1)

            isBeliefState = node.state and isinstance(node.state[0], tuple) and isinstance(node.state[0][0], tuple)
            draw_cell = 14 if isBeliefState else CELL_SIZE

            if isBeliefState:
                bs = node.state
                spacing = 3 * draw_cell + 6
                for j, s in enumerate(bs):
                    is_goal = False
                    if hasattr(self, 'currentGoalStates'):
                        is_goal = s in self.currentGoalStates
                    drawBoard(c, padX + j * spacing, y0 + 4, s, cell=draw_cell, highlight='explored', isGoalState=is_goal, knownCells=known)
                tx = padX + len(bs) * spacing + 6
            else:
                drawBoard(c, padX, y0 + 4, node.state, cell=draw_cell, highlight='explored', isGoalState=isGoal, knownCells=known)
                tx = padX + 3 * draw_cell + 8

            ty = y0 + 4

            c.create_text(tx, ty, text=f'[{node.label}]', anchor='nw', fill=BLACK, font=('Segoe UI', 8, 'bold'))
            
            y_offset = ty + 16
            act = ARROW_MAP.get(node.action, 'Start') if node.action else 'Start'
            c.create_text(tx, y_offset, text=f'Act: {act}', anchor='nw', fill=BLACK, font=('Consolas', 8))
            y_offset += 14
            
            if 'UCS' in self.currentAlgoName:
                c.create_text(tx, y_offset, text=f'Cost: {node.cost}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                y_offset += 14
            elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName or 'Beam Search' in self.currentAlgoName:
                c.create_text(tx, y_offset, text=f'h(n): {node.h}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                y_offset += 14
            elif 'A*' in self.currentAlgoName or 'IDA*' in self.currentAlgoName:
                c.create_text(tx, y_offset, text=f'f={node.cost}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                y_offset += 14
                c.create_text(tx, y_offset, text=f'g={node.g}, h={node.h}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                y_offset += 14
            
            c.create_text(tx, y_offset, text=f'Dep: {node.depth}', anchor='nw', fill=GRAY, font=('Consolas', 8))
            y_offset += 14
            
            par = f'Par: [{node.parentLabel}]' if node.parentLabel else 'Par: —'
            c.create_text(tx, y_offset, text=par, anchor='nw', fill=PURPLE, font=('Consolas', 8))

        totalH = padY * 2 + len(exploredList) * itemH
        cw = max(c.winfo_width(), 200)
        c.configure(scrollregion=(0, 0, cw, max(totalH, c.winfo_height())))

        if not exploredList:
            c.create_text(cw // 2, 50, text='∅  (Explored rỗng)', fill=GRAY, font=('Segoe UI', 10))

    # ─── Navigation Logic ───────────────────────────────
    def _goFirst(self): self._stopAuto(); self._render(0)
    def _goLast(self):  self._stopAuto(); self._render(len(self.steps) - 1)
    def _goPrev(self):  self._stopAuto(); self._render(self.idx - 1)
    def _goNext(self):  self._stopAuto(); self._render(self.idx + 1)

    def _toggleAuto(self):
        if self.autoMode:
            self._stopAuto()
        else:
            self.autoMode = True
            self.btnAuto.config(text='⏸ Dừng', bg=RED, fg=WHITE)
            self._tick()

    def _tick(self):
        if not self.autoMode: return
        if self.idx >= len(self.steps) - 1:
            self._stopAuto(); return
        self._render(self.idx + 1)
        self.root.after(self.speed.get(), self._tick)

    def _stopAuto(self):
        self.autoMode = False
        self.btnAuto.config(text='▶ Auto', bg=ACCENT, fg=WHITE)


# ══════════════════════════════════════════════════
# 6. KHỞI CHẠY (MAIN EXECUTION)
# ══════════════════════════════════════════════════


if __name__ == '__main__':
    root = tk.Tk()
    ttk.Style(root).theme_use('clam')
    app = Main8PuzzleApp(root)
    root.mainloop()
