
class Brick(object):

    def __init__(self, is_row, z, length, begin, end):
        self.is_row = is_row
        self.z = z
        self.length = length
        self.begin = begin
        self.end = end

    def __repr__(self):
        return '<%s> %s (%s, %s)' % (self.z, self.length, self.begin, self.end)

    def complete(self):
        return self.end-self.begin == self.length

class Field(object):

    def __init__(self, M, value):
        self.field = [[value for _ in range(M)] for _ in range(M)]

    def set(self, brick, i, value):
        if brick.is_row:
            self.field[brick.z][i] = value
        else:
            self.field[i][brick.z] = value

    def get(self, brick, i):
        if brick.is_row:
            return self.field[brick.z][i]
        else:
            return self.field[i][brick.z]

    def __repr__(self):
        return "\n        " + "\n        ".join(''.join(r) for r in self.field)

class Algorithm(object):

    BLACK = '#'
    WHITE = '_'
    EMPTY = '.'

    def __init__(self, M, rows, cols):
        self.M = M
        assert len(rows) == M
        assert len(cols) == M
        self.lines = ([[Brick(True, z, v, 0, 0) for v in row] for z, row in enumerate(rows)] +
                      [[Brick(False, z, v, 0, 0) for v in col] for z, col in enumerate(cols)])
        self.field = Field(M, self.EMPTY)

    def row_n_col_to_field(self):
        for line in self.lines:
            reachable = [False for _ in range(self.M)]
            for brick in line:
                for i in range(brick.begin, brick.end):
                    self.field.set(brick, i, self.BLACK)
                for i in range(max(0, brick.end-brick.length), min(brick.begin+brick.length, self.M)):
                    reachable[i] = True
            for i in range(self.M):
                if not reachable[i]:
                    self.field.set(brick, i, self.WHITE)

    def solution(self):
        self.row_n_col_to_field()
        return str(self.field)

    def debug_data(self):
        return "\n".join(str(v) for v in self.lines)

    def initial_solve(self):
        for line in self.lines:
            begin = self.M
            for brick in reversed(line):
                begin -= brick.length
                brick.begin = begin
                begin -= 1
            end = 0
            for brick in line:
                end += brick.length
                brick.end = end
                end += 1
            for brick in line:
                brick.visible = brick.end - brick.begin

    def second_step(self):
        self.row_n_col_to_field()
        for line in self.lines:
            brick = line[0]
            for i in range(self.M):
                if self.field.get(brick, i) == self.BLACK:
                    brick.begin = min(brick.begin, i)
                    break
            brick = line[-1]
            for i in range(self.M-1, -1, -1):
                if self.field.get(brick, i) == self.BLACK:
                    brick.end = max(brick.end, i+1)
                    break

    def correct_borders(self):
        self.row_n_col_to_field()
        for line in self.lines:
            for brick in line:
                if brick.begin < brick.end:
                    min_begin = brick.begin
                    max_end = brick.end
                    black_begin = True
                    black_end = True
                    assert self.field.get(brick, min_begin) == self.BLACK
                    assert self.field.get(brick, max_end-1) == self.BLACK
                    while True:
                        if self.field.get(brick, min_begin) != self.BLACK:
                            black_begin = False
                        if min_begin == 0 or self.field.get(brick, min_begin-1) == self.WHITE:
                            break
                        min_begin -= 1
                    brick.end = max(brick.end, min_begin + brick.length)
                    while True:
                        if self.field.get(brick, max_end-1) != self.BLACK:
                            black_end = False
                        if max_end == self.M or self.field.get(brick, max_end) == self.WHITE:
                            break
                        max_end += 1
                    brick.begin = min(brick.begin, max_end - brick.length)
                    if black_begin:
                        brick.begin = min_begin
                        brick.end = brick.begin + brick.length
                    if black_end:
                        brick.end = max_end
                        brick.begin = brick.end - brick.length

    def aligning(self):
        self.row_n_col_to_field()
        for line in self.lines:
            bn = 0
            brick = line[bn]
            i = 0
            while i < self.M and self.field.get(brick, i) != self.EMPTY:
                while i < self.M and self.field.get(brick, i) == self.WHITE:
                    i += 1
                if i < self.M and self.field.get(brick, i) == self.BLACK:
                    brick.begin, brick.end = i, i + brick.length
                    i += brick.length + 1
                    bn += 1
                    if bn < len(line):
                        brick = line[bn]
                    else:
                        break

            bn = len(line) - 1
            brick = line[bn]
            i = self.M - 1
            while i >= 0 and self.field.get(brick, i) != self.EMPTY:
                while i >= 0 and self.field.get(brick, i) == self.WHITE:
                    i -= 1
                if i >= 0 and self.field.get(brick, i) == self.BLACK:
                    brick.begin, brick.end = i+1 - brick.length, i+1
                    i -= brick.length + 1
                    bn -= 1
                    if bn >= 0:
                        brick = line[bn]
                    else:
                        break

    def fill_holes(self):
        self.row_n_col_to_field()
        for line in self.lines:
            i = 0
            brick = line[0]
            count_holes = 0
            while i < self.M:
                while i < self.M and self.field.get(brick, i) != self.EMPTY:
                    i += 1
                if i < self.M:
                    count_holes += 1
                    hole_begin = i
                while i < self.M and self.field.get(brick, i) == self.EMPTY:
                    i += 1
                if i < self.M or self.field.get(brick, i-1) == self.EMPTY:
                    hole_end = i
            count_candidate = 0
            for brick in line:
                if brick.end <= brick.begin:
                    count_candidate += 1
                    candidate = brick
            if count_holes == count_candidate == 1 and hole_end - hole_begin >= candidate.length:
                candidate.begin, candidate.end = hole_end-candidate.length, hole_begin+candidate.length

    def solve(self):
        self.initial_solve()
        for s in range(10):
            self.second_step()
            self.correct_borders()
            self.aligning()
            if s > 5:
                self.fill_holes()

