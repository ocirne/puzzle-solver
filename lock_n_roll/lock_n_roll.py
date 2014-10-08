
import random

def empty_field():
    return [[0 for _ in range(4)] for _ in range(4)]

def full_field():
    return [[random_dice() for _ in range(4)] for _ in range(4)]

def init_field():
    return full_field()

def random_dice():
    """
      g: green
      r: red
      b: blue
      y: yellow
    """
    colors = ['b', 'g', 'r', 'y']
    return random.randint(1, 4), random.choice(colors)

def random_dices():
    return [random_dice() for _ in range(4)]

def print_field(field):
    print
    print '----'
    for y in range(4):
        for x in range(4):
            if field[x][y] == 0:
                print '        ',
            else:
                print field[x][y],
        print
    print '----'

def is_all_same_number(combo):
    d = [f[0] for f in combo]
    return d[0] == d[1] == d[2] == d[3]

def is_all_same_color(combo):
    d = [f[1] for f in combo]
    return d[0] == d[1] == d[2] == d[3]

def is_all_different_numbers(combo):
    return sorted(f[0] for f in combo) == [1 ,2 ,3 ,4]

def is_all_different_colors(combo):
    return sorted(f[1] for f in combo) == ['b', 'g', 'r', 'y']

def get_combos():
    return [# vertical
            ((0,0), (0,1), (0,2), (0,3)),
            ((1,0), (1,1), (1,2), (1,3)),
            ((2,0), (2,1), (2,2), (2,3)),
            ((3,0), (3,1), (3,2), (3,3)),
            # horizontal
            ((0,0), (1,0), (2,0), (3,0)),
            ((0,1), (1,1), (2,1), (3,1)),
            ((0,2), (1,2), (2,2), (3,2)),
            ((0,3), (1,3), (2,3), (3,3)),
            # box
            ((0,0), (1,0), (0,1), (1,1)),
            ((1,0), (2,0), (1,1), (2,1)),
            ((2,0), (3,0), (2,1), (3,1)),
            ((0,1), (1,1), (0,2), (1,2)),
            ((1,1), (2,1), (1,2), (2,2)),
            ((2,1), (3,1), (2,2), (3,2)),
            ((0,2), (1,2), (0,3), (1,3)),
            ((1,2), (2,2), (1,3), (2,3)),
            ((2,2), (3,2), (2,3), (3,3)),
            # diagonal
            ((0,0), (1,1), (2,2), (3,3)),
            ((3,0), (2,1), (1,2), (0,3)),
            # corners
            ((0,0), (3,0), (0,3), (3,3)),
            ]

def next_state(field):
    """
          All 4 dice the same color and number
          All 4 dice the same color and all different numbers
          All 4 dice different colors, but the same number
          All 4 dice different colors and all 4 different numbers
    """
    for c in get_combos():
        print "%s:" % str(c)
        s = ''
        for y in range(4):
            for x in range(4):
                for f in c:
                    if f[0] == x and f[1] == y:
                        s += '#'
                        break
                else:
                    s += ' '
            s += '\n'
        print s
        print  '----'

def get_value_of_field(field):
    """
      Returns the point value for the current field
    """
    ret = 0
    for y in range(4):
        for x in range(4):
            if field[x][y] == 0:
                ret += 1
    return ret

def get_dices(field, combo):
    for c in combo:
        if field[c[0]][c[1]] == 0:
            return None
    return [field[c[0]][c[1]] for c in combo]

def analyze_field(field):
    erase_combos = []
    for combo in get_combos():
        dices = get_dices(field, combo)
        # "%s:" % str(combo),
        if dices:
            if is_all_same_number(dices):
                # "same number",
                erase_combos.append(combo)
            if is_all_same_color(dices):
                # "same color",
                erase_combos.append(combo)
            if is_all_different_numbers(dices):
                # "different numbers",
                erase_combos.append(combo)
            if is_all_different_colors(dices):
                # "different colors",
                erase_combos.append(combo)
    if erase_combos:
        for erase_combo in erase_combos:
            for c in erase_combo:
                field[c[0]][c[1]] = 0
    return field

def get_free_fields(field):
    ret = []
    for y in range(4):
        for x in range(4):
            if field[x][y] == 0:
                ret.append((x,y))
    random.shuffle(ret)
    return ret

def add_four_dices(field):
    free = get_free_fields(field)
    if len(free) < 4:
        return True, field
    for i, dice in enumerate(random_dices()):
        field[free[i][0]][free[i][1]] = dice
    return False, field

def test_color_detecting():
    for _ in range(40):
        dices = random_dices()
        print dices,
        if is_all_same_number(dices):
            print "same number",
        if is_all_same_color(dices):
            print "same color",
        if is_all_different_numbers(dices):
            print "different numbers",
        if is_all_different_colors(dices):
            print "different colors",
        print

def main():
    field = init_field()
    rounds = 0
    while True:
        print_field(field)
        field = analyze_field(field)
        game_over, field = add_four_dices(field)
        if game_over:
            print 'game over'
            break
        else:
            rounds += 1
    print rounds, 'Rounds'

if __name__ == '__main__':
    main()

