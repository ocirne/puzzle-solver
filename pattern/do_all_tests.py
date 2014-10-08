
from tests import tc0, tc1, tc2, tc3, tc4, tc5, tc6, tc7
from tests import check
from algorithms import naive
from algorithms import sat

if __name__ == '__main__':

    check = check.Checker()
    total = correct = 0
    for t in [tc0, tc1, tc2, tc3, tc4, tc5, tc6, tc7]:
        tc = t.TestCase()
        print '%s:' % tc.__module__
        f = naive.Algorithm(tc.M, tc.rows, tc.cols)
        f.solve()
        c, t = check.check(tc.M, tc.solution, f.solution())
        correct += c
        total += t
        print 8*'='
    print "overall: %2.1f%%" % (100*correct/total)

