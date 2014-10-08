
import string

class Checker(object):

    def check(self, M, soll_raw, ist_raw):
        soll = soll_raw.translate(None, string.whitespace)
        ist = ist_raw.translate(None, string.whitespace)
        assert len(soll) == len(ist)
        total = M*M
        correct = 0
        problem = {}
        for i in range(total):
            if ist[i] == soll[i]:
                correct += 1
            elif not ist[i] == '.':
                problem[i] = True
        p = ''
        for i in range(total):
            if i in problem:
                p += '^'
            else:
                p += ' '
        print 'Self check:'
        if problem:
            print soll
            print ist
            print p
            print 'Oops: %s' % sorted(problem.keys())
        print '%d/%d (%2.1f%%)' % (correct, total, 100.*correct/total)
        return correct, total

