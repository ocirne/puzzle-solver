
# coding: utf-8

import copy
from sage.all import cube

"""
   0·------>
   /|      x (Wert)
  / |
 /z (Ebene)
    |
    |y (Zeile)

index with p[z][y][x]
"""

original_state = [
        [
            [[0,0,0], [1,0,0], [1,1,0], ],
            [[0,0,0], [0,0,0], [1,1,1], ],
            [[0,0,0], [0,0,0], [0,0,0], ],
            ],
        [
            [[0,0,0], [0,0,0], [1,1,1], ],
            [[1,0,0], [1,0,1], [1,0,0], ],
            [[0,0,0], [0,0,0], [0,0,0], ],
            ],
        [
            [[0,0,0], [0,0,0], [1,1,1], ],
            [[0,0,0], [1,1,0], [1,0,0], ],
            [[0,0,0], [0,0,0], [0,0,0], ],
            ],
        ]

def rotate(axis, part, rotation):
    n = 3
    ret = copy.deepcopy(part)
    for _ in range(rotation):
        for x in range(n):
            for y in range(n):
                for z in range(n):
                    if axis == 'x':
                        ret[z][y][x] = part[y][n - z - 1][x]
                    elif axis == 'y':
                        ret[z][y][x] = part[x][y][n - z - 1]
                    elif axis == 'z':
                        ret[z][y][x] = part[z][x][n - y - 1]
                    else:
                        raise Exception('Wrong axis')
        part = copy.deepcopy(ret)
    return ret

def is_collision(p1, p2, p3):
    n = len(p1)
    for x in range(n):
        for y in range(n):
            for z in range(n):
                s = 0
                if p1[z][y][x] > 0: s += 1
                if p2[z][y][x] > 0: s += 1
                if p3[z][y][x] > 0: s += 1
                if s > 1:
                    return True
    return False

def is_valid_state(state):
    return not is_collision(state[0], state[1], state[2])

def get_rotated_pieces(state):
    # part1 is fixed
    ret1 = state[0]
    # part2 and part3 are rotated to "standing"
    p2 = rotate('z', state[1], 1)
    p3 = rotate('z', state[2], 1)
    ret = []
    for r1 in range(4):
        for r2 in range(4):
            for r3 in range(4):
                for r4 in range(4):
                    ret2 = rotate('y', rotate('x', p2, r1), r2) 
                    ret3 = rotate('y', rotate('x', p3, r3), r4)
                    if not is_collision(ret1, ret2, ret3):
                        ret.append((ret1, ret2, ret3))
    # We know it's only one valid rotation, so we only check this
    assert len(ret) == 1
    return ret[0]

def transform(state, part, move):
    n = 7
    ret = get_empty_state()
    for p in range(3):
        for z in range(1, n-1):
            for y in range(1, n-1):
                for x in range(1, n-1):
                    if part == p:
                        ret[p][z+move[0]][y+move[1]][x+move[2]] = state[p][z][y][x]
                    else:
                        ret[p][z][y][x] = state[p][z][y][x]
    return ret

def plot_solution(path):
    for i, p in enumerate(path):
        G = sum([cube(center=(z, y, x), size=1, color=color, opacity=0.5, frame_thickness=1, frame_color='black')
            for (j, color) in enumerate(['red', 'green', 'blue'])
            for x in range(7)
            for y in range(7)
            for z in range(7)
            if p[j][z][y][x] == 1])
        G.save('sol%s.png' % i, aspect_ratio=1, frame=False)

def step(D, old_state, path):
    moves = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
    if D == 4:
        print 'Plot Solution ...'
        plot_solution(path)
        return
    # print old_state
    for part in range(3):
        for new_state in [transform(old_state, part, move) for move in moves]:
            if is_valid_state(new_state) and not new_state in path:
                step(D+1, new_state, path + [new_state])

def get_empty_state():
    return [[[[0 for _ in range(7)] for _ in range(7)] for _ in range(7)] for _ in range(3)]

def main():
    print 'Get rotations ...'
    rotated_state = get_rotated_pieces(original_state)

    state = get_empty_state()

    # set middle voxels
    for p in range(3):
        for z in range(3):
            for y in range(3):
                for x in range(3):
                    state[p][z+2][y+2][x+2] = rotated_state[p][z][y][x]

    # set sides (for collision detection important)
    for i in range(3):
        for j in range(3):
            state[0][i+2][j+2][1] = 2
            state[0][i+2][j+2][5] = 2
            state[1][1][i+2][j+2] = 2
            state[1][5][i+2][j+2] = 2
            state[2][i+2][1][j+2] = 2
            state[2][i+2][5][j+2] = 2

    print 'Search for solution ...'
    step(0, state, [state])
    print 'Done.'

if __name__ == '__main__':
    main()

