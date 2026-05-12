import random
import copy

# Hàm tính số ô bị sai vị trí (Luật phản xạ / Heuristic)
def calculate_misplaced(E):
    goal = [[1, 2, 3], [4, 5, 6], [7, 8, 0]]
    count = 0
    for i in range(3):
        for j in range(3):
            if E[i][j] != 0 and E[i][j] != goal[i][j]:
                count += 1
    return count

# Hàm sinh các hướng di chuyển hợp lệ của số 0
def Zero_move(x, y):
    moves = []
    if x < 2: moves.append("D") 
    if x > 0: moves.append("U") 
    if y < 2: moves.append("R") 
    if y > 0: moves.append("L") 
    return moves

# Hàm mô phỏng hành động hoán đổi vị trí
def simulate_move(E, x, y, action):
    new_E = copy.deepcopy(E)
    nx, ny = x, y
    if action == "D": nx += 1
    elif action == "U": nx -= 1
    elif action == "R": ny += 1
    elif action == "L": ny -= 1
    
    # Hoán đổi số 0 với ô kề cạnh
    new_E[x][y], new_E[nx][ny] = new_E[nx][ny], new_E[x][y]
    return new_E, nx, ny

# HÀM XỬ LÝ CỦA MODEL-BASED REFLEX AGENT
def ModelBasedRulesMatch(E, internal_model, x, y):
    # 1. CẬP NHẬT MÔ HÌNH: Lưu trạng thái hiện tại vào bộ nhớ
    # Phải chuyển ma trận list(list) thành tuple(tuple) để có thể lưu vào Set
    current_state = tuple(tuple(row) for row in E)
    internal_model.add(current_state)

    # 2. SUY LUẬN DỰA TRÊN MÔ HÌNH VÀ LUẬT PHẢN XẠ
    valid_moves = Zero_move(x, y)
    best_action = None
    min_misplaced = float('inf')
    smart_moves = [] # Danh sách các bước đi chưa từng đi qua

    for action in valid_moves:
        next_E, nx, ny = simulate_move(E, x, y, action)
        next_state = tuple(tuple(row) for row in next_E)
        
        # Nếu trạng thái này chưa từng xuất hiện trong trí nhớ
        if next_state not in internal_model:
            smart_moves.append(action)
            
            # Tính toán xem trạng thái này tốt đến đâu (càng ít ô sai càng tốt)
            misplaced = calculate_misplaced(next_E)
            if misplaced < min_misplaced:
                min_misplaced = misplaced
                best_action = action

    # 3. RA QUYẾT ĐỊNH
    if best_action:
        # Chọn hướng đi tốt nhất trong số các hướng mới
        action = best_action 
    elif smart_moves:
        action = random.choice(smart_moves)
    else:
        # Tình huống xấu: Bị kẹt (xung quanh đều là đường cũ) -> Chấp nhận đi lùi để tìm lối thoát
        action = random.choice(valid_moves)

    # 4. THỰC THI (Act)
    final_E, new_x, new_y = simulate_move(E, x, y, action)
    return final_E, action, new_x, new_y

# Trạng thái mục tiêu cần đạt được
GOAL_STATE = [[1, 2, 3], 
              [4, 5, 6], 
              [7, 8, 0]]

# Khởi tạo môi trường ban đầu cố định
E = [[0, 6, 8],
     [7, 3, 1],
     [4, 5, 2]]

# Khởi tạo mô hình nội bộ (Lưu trữ các trạng thái đã đi qua)
internal_model = set()

# Tìm vị trí ban đầu của ô số 0
curr_x, curr_y = -1, -1
for i in range(3):
    for j in range(3):
        if E[i][j] == 0:
            curr_x, curr_y = i, j

print("--- TRẠNG THÁI BAN ĐẦU ---")
for row in E: print(row)

for i in range(10000):
    print(f"\n--- Bước thứ {i+1} ---")
    
    # Cập nhật môi trường, vị trí mới của 0 và lấy hành động
    E, action, curr_x, curr_y = ModelBasedRulesMatch(E, internal_model, curr_x, curr_y)
    
    print(f"Hành động di chuyển ô 0: {action}")
    for row in E:
        print(row)
        
    # Kiểm tra xem đã đạt trạng thái đích chưa
    if E == GOAL_STATE:
        print("\nBàn cờ đã được sắp xếp thành công về đích.")
        break
else:
    print("\nĐã đạt giới hạn số bước nhưng chưa tìm được đích.")