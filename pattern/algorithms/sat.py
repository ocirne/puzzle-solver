
import subprocess

class Algorithm(object):

    def __init__(self, M, rows, cols):
        self.in_file = 'blub.in'
        self.out_file = 'blub.out'
        self.M = M
        self.rows = rows
        self.cols = cols

    def write_problem(self):
        with open(self.in_file, 'w') as f:
            f.write('p cnf 2 4')
            f.write('-1 -2 0')
            f.write('-1 2 0')
            f.write('-1 -2 0')
            f.write('1 2 0')

    def sat_solver_wrapper(self):
        subprocess.Popen(['/usr/local/bin/minisat', self.in_file, self.out_file])

    def solution(self):
        with open(self.out_file, 'r') as f:
            print '***', f.read(), '***'
        return 'BLUB'

    def solve(self):
        self.write_problem()
        self.sat_solver_wrapper()

    def debug_data(self):
        return None

    def self_check(self, x):
        return None
