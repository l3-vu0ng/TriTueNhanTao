# ══════════════════════════════════════════════════
# 1. CẤU HÌNH & HẰNG SỐ (CONFIG & CONSTANTS)
# ══════════════════════════════════════════════════

import tkinter as tk
from tkinter import ttk, messagebox
from collections import deque
import heapq
import itertools

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

def drawBoard(canvas, x, y, state, cell=CELL_SIZE, highlight=None, newCells=None, isGoalState=False):
    """Draws a 3x3 puzzle board on the canvas."""
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
                fgColor = '#8c959f' if isGhost or highlight == 'explored' else WHITE
                if isGhost or highlight == 'explored':
                    fgColor = BLACK
                canvas.create_text(cx + cell // 2, cy + cell // 2, text=str(val), fill=fgColor, font=('Segoe UI', 7, 'bold'))

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
    def __init__(self, phase, currentNode, frontier, explored, newLabels, desc, limit=None, exploredCount=None):
        self.phase = phase           # 'init' | 'expand' | 'found' | 'failure' | 'cutoff' | 'new_limit'
        self.currentNode = currentNode    
        self.frontier = frontier        
        self.explored = explored        
        self.newLabels = newLabels      
        self.desc = desc
        self.limit = limit              # Used by IDS
        self.exploredCount = exploredCount # Used by DFS/IDS to refer to master explored list

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
            'Steepest-Ascent Hill Climbing (SAHC)': SearchEngine.runSteepestAscentHillClimbing
        }
        self.algoGroups = {
            'Tìm kiếm mù (Uninformed Search)': [
                'BFS (Breadth-First Search)',
                'DFS (Depth-First Search)',
                'IDS (Iterative Deepening Search)',
                'UCS (Uniform-Cost Search)'
            ],
            'Tìm kiếm Heuristic (Heuristic Search)': [
                'Greedy-Search (Heuristic)',
                'A* (A-Star Search)',
                'IDA* (Iterative Deepening A*)'
            ],
            'Tìm kiếm Local Search (Local Search)': [
                'Simple Hill Climbing (SHC)',
                'Steepest-Ascent Hill Climbing (SAHC)'
            ]
        }
        self.currentGroupName = 'Tìm kiếm mù (Uninformed Search)'
        self.currentAlgoName = 'BFS (Breadth-First Search)'
        self.steps = []
        self.exploredMaster = []
        self.idx = 0
        self.autoMode = False
        self.speed = tk.IntVar(value=400)

        self._buildUi()
        self._loadAlgorithm(self.currentAlgoName)

    def _loadAlgorithm(self, algoName: str) -> None:
        algoFunc = self.algorithms[algoName]
        self.steps, self.exploredMaster = algoFunc(INITIAL_STATE, GOAL_STATE)
        self.idx = 0
        self._stopAuto()
        self.algoTitleVar.set(f'8-Puzzle — {algoName}')
        self._render(0)

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
            ans = messagebox.askyesno("Đổi nhóm thuật toán", "Thuật toán đang chạy. Bạn có muốn Reset để chuyển sang nhóm mới không?\n(Đồng ý = Reset, Hủy = Tiếp tục nhóm hiện tại)")
            if not ans:
                self.comboGroup.set(self.currentGroupName)
                return

        self.currentGroupName = newGroup
        algosInGroup = self.algoGroups[newGroup]
        self.comboAlgo.config(values=algosInGroup)
        
        firstAlgo = algosInGroup[0]
        self.comboAlgo.set(firstAlgo)
        self.currentAlgoName = firstAlgo
        self._loadAlgorithm(firstAlgo)

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

        # Right subframe: Buttons + Speed
        rightCtrlFrame = tk.Frame(toolbarFrame, bg=PANEL)
        rightCtrlFrame.pack(side='right', padx=10)

        # Buttons
        bs = dict(font=('Segoe UI', 9, 'bold'), relief='flat', cursor='hand2', padx=8, pady=3, bd=0)
        
        btnFrame = tk.Frame(rightCtrlFrame, bg=PANEL)
        btnFrame.pack(side='left', padx=(0, 10))

        tk.Button(btnFrame, text='⏮', command=self._goFirst, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=0, padx=2)
        tk.Button(btnFrame, text='◀ Trước', command=self._goPrev, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=1, padx=2)
        self.btnAuto = tk.Button(btnFrame, text='▶ Auto', command=self._toggleAuto, bg=ACCENT, fg=WHITE, **bs)
        self.btnAuto.grid(row=0, column=2, padx=2)
        tk.Button(btnFrame, text='Tiếp ▶', command=self._goNext, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=3, padx=2)
        tk.Button(btnFrame, text='⏭', command=self._goLast, bg='#eaeef2', fg=BLACK, **bs).grid(row=0, column=4, padx=2)
        tk.Button(btnFrame, text='🛣 Show Path', command=self._showPath, bg=PURPLE, fg=WHITE, **bs).grid(row=0, column=5, padx=8)

        # Speed scale
        speedFrame = tk.Frame(rightCtrlFrame, bg=PANEL)
        speedFrame.pack(side='left')
        tk.Label(speedFrame, text='Tốc độ (ms):', bg=PANEL, fg=GRAY, font=('Segoe UI', 9)).pack(side='left', padx=(0, 4))
        tk.Scale(speedFrame, from_=50, to=1500, orient='horizontal', variable=self.speed, bg=PANEL, fg=BLACK, troughcolor=BORDER, highlightthickness=0, length=90, showvalue=False).pack(side='left')

        # ── Middle Section (Main Layout) ──
        body = tk.Frame(self.root, bg=BG)
        body.pack(fill='both', expand=True, padx=10, pady=4)

        # Left Column (Current Node + Goal)
        leftCol = tk.Frame(body, bg=BG, width=340)
        leftCol.pack(side='left', fill='y', padx=(0, 8))
        leftCol.pack_propagate(False)

        self._buildCurrentNodePanel(leftCol)
        self._buildGoalPanel(leftCol)

        # Center Column (Frontier)
        self._buildFrontierPanel(body)

        # Right Column (Explored)
        self._buildExploredPanel(body)

        # ── Bottom Section (Step Info) ──
        self._buildBottomBar()

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
        gc = tk.Canvas(pnl, width=150, height=150, bg=BG, highlightthickness=0)
        gc.pack(pady=(14, 4))
        drawBoard(gc, 10, 10, GOAL_STATE, cell=43, isGoalState=True)

    def _buildFrontierPanel(self, parent):
        self.frontierTitleVar = tk.StringVar(value='Frontier')
        pnl = tk.Frame(parent, bg=BG, highlightthickness=1, highlightbackground=BORDER)
        pnl.pack(side='left', fill='both', expand=True, padx=(0, 8), pady=(0, 8))
        
        tk.Label(pnl, textvariable=self.frontierTitleVar, bg=PANEL, fg=BLACK, font=('Segoe UI', 10, 'bold')).pack(fill='x', ipady=4)
        tk.Frame(pnl, bg=BORDER, height=1).pack(fill='x')

        wrapper = tk.Frame(pnl, bg=BG)
        wrapper.pack(fill='both', expand=True, padx=4, pady=4)
        vsb = tk.Scrollbar(wrapper, orient='vertical', bg=BG, troughcolor=PANEL, width=10)
        vsb.pack(side='right', fill='y')
        self.frCanvas = tk.Canvas(wrapper, bg=BG, yscrollcommand=vsb.set, highlightthickness=0)
        self.frCanvas.pack(side='left', fill='both', expand=True)
        vsb.config(command=self.frCanvas.yview)
        self.frCanvas.bind('<Configure>', lambda e: self.frCanvas.configure(scrollregion=self.frCanvas.bbox('all')))
        self.frCanvas.bind('<MouseWheel>', lambda e: self.frCanvas.yview_scroll(-1 * (e.delta // 120), 'units'))

    def _buildExploredPanel(self, parent):
        pnl = tk.Frame(parent, bg=BG, highlightthickness=1, highlightbackground=BORDER, width=280)
        pnl.pack(side='left', fill='y', pady=(0, 8))
        pnl.pack_propagate(False)
        
        tk.Label(pnl, text='Explored', bg=PANEL, fg=BLACK, font=('Segoe UI', 10, 'bold')).pack(fill='x', ipady=4)
        tk.Frame(pnl, bg=BORDER, height=1).pack(fill='x')

        wrapper = tk.Frame(pnl, bg=BG)
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
        self.banner.pack(fill='x', padx=10, pady=(0, 10))

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

        self.descLbl = tk.Label(leftInfo, text='', bg=PANEL, fg=BLACK, font=('Segoe UI', 11, 'bold'), anchor='nw', justify='left', width=45)
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
            elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName:
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
        top.geometry("700x450")
        top.configure(bg=BG)

        leftPane = tk.Frame(top, bg=BG, width=300)
        leftPane.pack(side='left', fill='y', padx=10, pady=10)
        leftPane.pack_propagate(False)
        
        tk.Label(leftPane, text="Trạng thái Node", font=('Segoe UI', 11, 'bold'), bg=BG, fg=BLACK).pack(pady=(0, 10))
        
        canvasLeft = tk.Canvas(leftPane, width=280, height=350, bg=BG, highlightthickness=1, highlightbackground=BORDER)
        canvasLeft.pack()

        rightPane = tk.Frame(top, bg=BG)
        rightPane.pack(side='left', fill='both', expand=True, padx=10, pady=10)

        tk.Label(rightPane, text="Thông tin chi tiết", font=('Segoe UI', 11, 'bold'), bg=BG, fg=BLACK).pack(pady=(0, 10))
        
        detailsFrame = tk.Frame(rightPane, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        detailsFrame.pack(fill='both', expand=True)

        infoLbl = tk.Label(detailsFrame, text="", font=('Segoe UI', 10), bg=PANEL, fg=BLACK, justify='left', anchor='nw')
        infoLbl.pack(padx=15, pady=15, fill='both', expand=True)

        currentIdx = [0]

        def drawStep(idx):
            canvasLeft.delete('all')
            node = pathNodes[idx]
            isGoal = (idx == len(pathNodes) - 1)
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
        tk.Button(btnFrame, text="◀ Trước", command=goPrevPath, width=10, bg=PANEL).pack(side='left', padx=10)
        tk.Button(btnFrame, text="Tiếp ▶", command=goNextPath, width=10, bg=PANEL).pack(side='left', padx=10)

        drawStep(0)

    # ─── Render Logic ───────────────────────────────────
    def _render(self, idx):
        idx = max(0, min(idx, len(self.steps) - 1))
        self.idx = idx
        step = self.steps[idx]
        
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

        # Phase banner styling
        phaseCfg = {
            'init':      (ACCENT, WHITE, '🔵', 'INIT'),
            'new_limit': (PURPLE, WHITE, '🟣', 'NEW LIMIT'),
            'expand':    (ORANGE, WHITE, '🟠', 'EXPAND'),
            'found':     (GREEN,  WHITE, '🟢', 'FOUND'),
            'cutoff':    ('#e3b341', BLACK, '🟡', 'CUTOFF'),
            'failure':   (RED,    WHITE, '🔴', 'FAIL'),
        }
        pc, fc, icon, badgeTxt = phaseCfg.get(step.phase, (GRAY, WHITE, '⬤', '?'))
        self.phaseIcon.config(text=icon, fg=pc)
        self.phaseBadge.config(text=badgeTxt, bg=pc, fg=fc)
        self.descLbl.config(text=step.desc)
        self.stepLbl.config(text=f'Bước {idx} / {len(self.steps) - 1}')

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
        if step.currentNode:
            n = step.currentNode
            isGoal = (n.state == GOAL_STATE)
            drawBoard(self.curCanvas, 10, 10, n.state, cell=43, isGoalState=isGoal)
            self.curLabel.config(text=f'Node [{n.label}]')
            self.curAction.config(text=f'Action: {ARROW_MAP.get(n.action, "Start")}' if n.action else 'Action: Start')
            if 'UCS' in self.currentAlgoName:
                self.curCost.config(text=f'Cost: {n.cost}')
            elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName:
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
        colW = 160
        itemH = 104
        padX = 10
        padY = 8

        cw = max(c.winfo_width(), 300)
        cols = max(1, cw // colW)

        display = []
        hasGhost = False
        
        isQueueLike = 'BFS' in self.currentAlgoName or 'UCS' in self.currentAlgoName or 'Greedy' in self.currentAlgoName or 'A*' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName
        # Order of ghost depends on algorithm
        if isQueueLike:
            if step.currentNode and step.phase in ('expand', 'found', 'failure'):
                display.append(('ghost', step.currentNode))
                hasGhost = True
            for node in step.frontier:
                display.append(('normal', node))
        else: # DFS, IDS, IDA*
            for node in step.frontier:
                display.append(('normal', node))
            if step.currentNode and step.phase in ('expand', 'found', 'cutoff', 'failure'):
                display.append(('ghost', step.currentNode))
                hasGhost = True

        nFrontier = len(step.frontier)
        showNext = step.phase in ('init', 'new_limit', 'expand', 'cutoff') and nFrontier > 0

        nextCurrentNode = None
        if self.idx < len(self.steps) - 1:
            nextStep = self.steps[self.idx + 1]
            if nextStep.currentNode:
                nextCurrentNode = nextStep.currentNode

        for i, (kind, node) in enumerate(display):
            col = i % cols
            row = i // cols
            x0 = padX + col * colW
            y0 = padY + row * itemH

            isGoal = (node.state == GOAL_STATE)
            isNew = node.label in step.newLabels
            isGhost = (kind == 'ghost')
            
            isNext = False
            if showNext and not isGhost and nextCurrentNode:
                if node.state == nextCurrentNode.state:
                    isNext = True

            if isGhost:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill=TILE_BLANK, outline=GRAY, width=1, dash=(4, 4))
            elif isNext:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill='#e1f0ff', outline=ACCENT, width=2)
            elif isNew:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill='#fff8e6', outline=ORANGE, width=1)
            elif isGoal:
                c.create_rectangle(x0 - 3, y0 - 3, x0 + colW - 10, y0 + itemH - 4, fill='#e6ffec', outline=GREEN, width=1)

            drawBoard(c, x0 + 2, y0 + 4, node.state, cell=CELL_SIZE, highlight='ghost' if isGhost else None, isGoalState=isGoal if not isGhost else False)

            tx = x0 + 3 * CELL_SIZE + 8
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
                elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName:
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
                elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName:
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

        for i, node in enumerate(reversed(exploredList)):
            y0 = padY + i * itemH
            isGoal = (node.state == GOAL_STATE)

            if i > 0:
                c.create_line(padX, y0 - 4, 260, y0 - 4, fill=BORDER, width=1)

            drawBoard(c, padX, y0 + 4, node.state, cell=CELL_SIZE, highlight='explored', isGoalState=isGoal)

            tx = padX + 3 * CELL_SIZE + 8
            ty = y0 + 4

            c.create_text(tx, ty, text=f'[{node.label}]', anchor='nw', fill=BLACK, font=('Segoe UI', 8, 'bold'))
            
            y_offset = ty + 16
            act = ARROW_MAP.get(node.action, 'Start') if node.action else 'Start'
            c.create_text(tx, y_offset, text=f'Act: {act}', anchor='nw', fill=BLACK, font=('Consolas', 8))
            y_offset += 14
            
            if 'UCS' in self.currentAlgoName:
                c.create_text(tx, y_offset, text=f'Cost: {node.cost}', anchor='nw', fill=GREEN, font=('Consolas', 8))
                y_offset += 14
            elif 'Greedy' in self.currentAlgoName or 'Hill Climbing' in self.currentAlgoName:
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
