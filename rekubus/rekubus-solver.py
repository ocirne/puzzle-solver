
cube = [
        ((3,2), (4,6), (0,0),),
        ((0,4),),
        ((1,4),),
        ((4,4),),
        ((5,4),),
        ((3,4),),
        ((2,4),),
        ((0,2), (4,8), (1,0),),
        ((3,8), (0,6), (5,0),),
        ((0,8), (1,6), (5,2),),
        ((3,5), (0,3),),
        ((0,1), (4,7),),
        ((0,5), (1,3),),
        ((0,7), (5,1),),
        ((1,2), (4,2), (2,0),),
        ((1,8), (2,6), (5,8),),
        ((1,1), (4,5),),
        ((1,7), (5,5),),
        ((1,5), (2,3),),
        ((2,8), (3,6), (5,6),),
        ((2,2), (4,0), (3,0),),
        ((2,1), (4,1),),
        ((2,7), (5,7),),
        ((2,5), (3,3),),
        ((3,1), (4,3),),
        ((3,7), (5,3),),
        ]

def load_data(filename):
    middle = []
    edge = []
    corner = []
    for line in open(filename, 'r').readlines():
        if line.strip():
            tmp = [int(e) for e in line.split()]
            if len(tmp) == 1:
                middle.append(tmp)
            elif len(tmp) == 2:
                edge.append(tmp)
            else:
                corner.append(tmp)
    return middle, edge, corner

def is_valid(state):
    for s in range(6):
        if state[s][4] > 0:
            m = 3*state[s][4]
            for f in [(0,1,2), (3,4,5), (6,7,8), (0,3,6), (1,4,7), (2,5,8), (0,4,8), (2,4,6)]:
                n = sum(state[s][i] for i in f)
                if n > 0 and n != m:
                    return False
    return True

def set_state(state, depth, values, rot, mod):
    for i, (side, field) in enumerate(cube[depth]):
        state[side][field] = values[(i+rot)%mod]

def unset_state(state, depth):
    for side, field in cube[depth]:
        state[side][field] = -100

def without(array, value):
    return [v for v in array if v != value]

def print_solution(state):
    text = ['front', 'right', 'back', 'left', 'top', 'bottom']
    for s, side in enumerate(state):
        print text[s]
        for i in range(3):
            print side[i*3:(i+1)*3]
        print

def step(depth, state, middle, edge, corner):
    if not is_valid(state):
        return
    elif depth == 26:
        print_solution(state)
    elif len(cube[depth]) == 1:
        for m in middle:
            set_state(state, depth, m, 0, 1)
            step(depth+1, state, without(middle, m), edge, corner)
            unset_state(state, depth)
    elif len(cube[depth]) == 2:
        for e in edge:
            if e[0] == e[1]:
                set_state(state, depth, e, 0, 2)
                step(depth+1, state, middle, without(edge, e), corner)
            else:
                for rot in range(2):
                    set_state(state, depth, e, rot, 2)
                    step(depth+1, state, middle, without(edge, e), corner)
            unset_state(state, depth)
    elif len(cube[depth]) == 3:
        for c in corner:
            for rot in range(3):
                set_state(state, depth, c, rot, 3)
                step(depth+1, state, middle, edge, without(corner, c))
            unset_state(state, depth)

def main():
    middle, edge, corner = load_data('data.in')
    state = [[-100 for _ in range(9)] for _ in range(6)]
    depth = 0
    c = corner[0]
    set_state(state, depth, c, 0, 3)
    step(depth+1, state, middle, edge, without(corner, c))

if __name__ == '__main__':
    main()

