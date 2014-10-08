
from tests import tc5
from tests import check

from algorithms import naive
from algorithms import sat

if __name__ == '__main__':
    tc = tc5.TestCase()
    f = naive.Algorithm(tc.M, tc.rows, tc.cols)
    f.solve()
    print tc.solution
    print 10*'='
    print f.solution()
    print f.debug_data()
    c = check.Checker()
    c.check(tc.M, tc.solution, f.solution())

