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

E = [[0,0,1,0],
     [1,1,0,1],
     [0,1,0,0],
     [1,0,0,1]]

curr_x, curr_y = 1, 1

for i in range(100):
    print(f"Bước {i+1}: Vị trí hiện tại ({curr_x}, {curr_y}), trạng thái: {E[curr_x][curr_y]}")
    action, curr_x, curr_y = RulesMatch(E, curr_x, curr_y)
    print(E)
    dirty_count = sum(row.count(1) for row in E)
    if dirty_count == 0:
        print(f"Hoàn thành dọn dẹp tại bước thứ {i+1}")
        break
