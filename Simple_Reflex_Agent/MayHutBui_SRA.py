import random

def P_moves(x, y):
    moves = []
    if x < 3: moves.append("D")
    if x > 0: moves.append("U")
    if y < 3: moves.append("R")
    if y > 0: moves.append("L")
    return moves

def RulesMatch(E, x, y):
    state = E[x][y]
    if state == 1:
        print("Vị trí hiện tại bị bẩn, thực hiện hành động dọn dẹp")
        E[x][y] = 0
        moves = P_moves(x, y)
        action = random.choice(moves)
    if state == 0:
        moves = P_moves(x, y)
        action = random.choice(moves)

    if action == "D": x += 1
    elif action == "U": x -= 1
    elif action == "R": y += 1
    elif action == "L": y -= 1

    return action, x, y

## Ma trận môi trường 4x4, 1 là bẩn, 0 là sạch
E = [[0,0,1,0],
     [1,1,0,1],
     [0,1,0,0],
     [1,0,0,1]]

## Khởi tạo vị trí ban đầu của agent
curr_x, curr_y = 1, 1

## Chạy vòng lặp cho 100 bước
for i in range(100):
    print(f"\n--- Lần thứ {i+1} ---")
    action, curr_x, curr_y = RulesMatch(E, curr_x, curr_y)
    print(E)
    print("Hành động tiếp theo:", action)
    count = sum(row.count(1) for row in E)
    if count == 0:
        print("Môi trường đã sạch, dừng chương trình.")
        break