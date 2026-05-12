import random

def P_moves(x, y):
    moves = []
    if x < 3: moves.append("D")
    if x > 0: moves.append("U")
    if y < 3: moves.append("R")
    if y > 0: moves.append("L")
    return moves

def ModelBasedRulesMatch(E, internal_model, x, y):
    state = E[x][y]
    
    if state == 1:
        print("Vị trí hiện tại bị bẩn, thực hiện hành động dọn dẹp")
        E[x][y] = 0              
        internal_model[x][y] = 0 
    elif state == 0:
        internal_model[x][y] = 0 

    valid_moves = P_moves(x, y)
    smart_moves = []
    
    for m in valid_moves:
        if m == "D" and internal_model[x+1][y] == -1: smart_moves.append(m)
        elif m == "U" and internal_model[x-1][y] == -1: smart_moves.append(m)
        elif m == "R" and internal_model[x][y+1] == -1: smart_moves.append(m)
        elif m == "L" and internal_model[x][y-1] == -1: smart_moves.append(m)

    if smart_moves:
        action = random.choice(smart_moves)
    else:
        action = random.choice(valid_moves)

    # 4. THỰC THI (Act)
    if action == "D": x += 1
    elif action == "U": x -= 1
    elif action == "R": y += 1
    elif action == "L": y -= 1

    return action, x, y

## Ma trận môi trường thực 4x4, 1 là bẩn, 0 là sạch
E = [[0,0,1,0],
     [1,1,0,1],
     [0,1,0,0],
     [1,0,0,1]]

## KHỞI TẠO MÔ HÌNH NỘI BỘ (Internal Model / Memory)
## Sử dụng giá trị -1 để đại diện cho những ô Agent "chưa từng đi tới"
internal_model = [[-1,-1,-1,-1],
                  [-1,-1,-1,-1],
                  [-1,-1,-1,-1],
                  [-1,-1,-1,-1]]

## Khởi tạo vị trí ban đầu của agent
curr_x, curr_y = 1, 1

## Chạy vòng lặp cho 100 bước
for i in range(100):
    print(f"\n--- Lần thứ {i+1} ---")
    
    # Truyền thêm internal_model vào hàm
    action, curr_x, curr_y = ModelBasedRulesMatch(E, internal_model, curr_x, curr_y)
    
    print("Môi trường thực tế:")
    for row in E:
        print(row)
        
    print("Hành động tiếp theo:", action)
    
    count = sum(row.count(1) for row in E)
    if count == 0:
        print("Môi trường đã sạch, dừng chương trình.")
        break