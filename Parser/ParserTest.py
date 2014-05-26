import unittest
from Parser import Automata, Parser, ThompsonVisitor, NfaToDfaVisitor, ReducingVisitor, MatchingVisitor

class AutomataTest(unittest.TestCase):

    def testState ( self ):
        states = [Automata.State() for i in range(10)]
        self.assertEqual(\
            range(states[0].id, states[-1].id+1), map(lambda s: s.id, states),
            "Created %d states with ids %s" % (len(states), str(map(lambda s: s.id, states))))
 
        s1, s2, s3 = states[0:3]
        s1.addTransition(Automata.EPSILON, s2)
        s1.addTransition('b', s3)
        s2.addTransition('a', s1)
        self.assertEqual(\
            s1.next(), {Automata.EPSILON: (s2,), 'b': (s3,)},\
            "s1 transitions: " + str(s1.next()))
        self.assertIn(s2, s1.next(Automata.EPSILON), "s2 not in s1.next(EPSILON)")
        self.assertIn(s1, s2.next('a'), "s1 not in s2.next('a')")
        s2.removeTransition(s1)
        s2.removeTransition(s3)
        self.assertNotIn(s1, s2.next('a'), "s1 still in s2.next('a')")

        s4, s5 = states[3:5]
        s4.addTransition(('a', 'b', 'c',), s5)
        self.assertEqual(\
            s4.next(), {'a': (s5,), 'b': (s5,), 'c': (s5,)},\
            "s4 transitions: " + str(s4.next()))
        
    def testAutomata ( self ):
        s1, s2, s3 = Automata.State(), Automata.State(), Automata.State()
        s1.addTransition('a', s2)
        s1.addTransition(Automata.EPSILON, s3)
        s2.addTransition('b', s1)
        nfa = Automata(s1)
        self.assertIn(s1, nfa, "s1 not in NFA")
        self.assertIn(s2, nfa, "s2 not in NFA")
        self.assertIn(s3, nfa, "s3 not in NFA")
        
        s4, s5, s6 = Automata.State(), Automata.State(), Automata.State()
        s4.addTransition(Automata.EPSILON, s5)
        s4.addTransition('c', s6)
        nfa.add(s4)
        self.assertIn(s4, nfa, "s4 not in NFA")
        self.assertIn(s5, nfa, "s5 not in NFA")
        self.assertIn(s6, nfa, "s6 not in NFA")
        
        other_nfa = Automata()
        other_nfa.add(Automata.State())
        nfa.update(other_nfa)
        self.assertTrue(other_nfa.issubset(nfa), "New NFA not added to existing NFA")
        
        c = nfa.closure(set((s1, s4)), Automata.EPSILON)
        self.assertIn(s1, c, "s1 not in Epsilon closure of (s1, s4)")
        self.assertIn(s4, c, "s4 not in Epsilon closure of (s1, s4)")
        self.assertIn(s3, c, "s3 not in Epsilon closure of (s1, s4)")
        self.assertIn(s5, c, "s5 not in Epsilon closure of (s1, s4)")
        s3.addTransition(Automata.EPSILON, s4)
        c = nfa.closure(set((s1,)), Automata.EPSILON)
        self.assertIn(s1, c, "s1 not in Epsilon closure of (s1,)")
        self.assertIn(s4, c, "s4 not in Epsilon closure of (s1,)")
        self.assertIn(s3, c, "s3 not in Epsilon closure of (s1,)")
        self.assertIn(s5, c, "s5 not in Epsilon closure of (s1,)")
        c = nfa.closure(set((s1, s4)), 'a')
        self.assertIn(s2, c, "s2 not in 'a' closure of (s1, s4)")
        self.assertNotIn(s1, c, "s1 in 'a' closure of (s1, s4)")
        self.assertNotIn(s4, c, "s4 in 'a' closure of (s1, s4)")
        
    def testNfaToDfaVisitor ( self ):
        s1, s2, s3, s4, s5 = [Automata.State() for i in range(5)]
        s1.addTransition(Automata.EPSILON, s2)
        s1.addTransition(Automata.EPSILON, s4)
        s2.addTransition('a', s3)
        s3.addTransition('b', s3)
        s4.addTransition('a', s4)
        s4.addTransition('b', s5)
        s3.accepting, s5.accepting = 2*(True,)
        nfa = Automata(s1)
        visitor = NfaToDfaVisitor()
        dfa = nfa.accept(visitor)
        self.assertIn(s1, dfa.initial.id, "s1 not in initial state id")
        self.assertIn(s2, dfa.initial.id, "s2 not in initial state id")
        self.assertIn(s4, dfa.initial.id, "s4 not in initial state id")
        sa = dfa.initial.next('a')[0]
        self.assertIn(s3, sa.id, "s3 not in initial-(a)->()")
        self.assertIn(s4, sa.id, "s4 not in initial-(a)->()")
        self.assertTrue(sa.accepting, "initial-(a)->() is not accepting")
        sb = dfa.initial.next('b')[0]
        self.assertIn(s5, sb.id, "s5 not in initial-(b)->()")
        self.assertTrue(sb.accepting, "initial-(b)->() is not accepting")
        saa = sa.next('a')[0]
        self.assertIn(s4, sa.id, "s4 not in initial-(a)->()-(a)->()")
        sab = sa.next('b')[0]
        self.assertIn(s3, sab.id, "s3 not in initial-(a)->()-(b)->()")
        self.assertIn(s5, sab.id, "s5 not in initial-(a)->()-(b)->()")
        self.assertTrue(sab.accepting, "initial-(a)->()-(b)->() is not accepting")
        self.assertEqual(saa.next('a')[0], saa, "initial-(a)->()-(a)->() doesn't point to itself")
        self.assertEqual(saa.next('b')[0], dfa.initial.next('b')[0], "initial-(a)->()-(a)->()->(b)->() is not initial-(b)->()")
        sabb = sab.next('b')[0]
        self.assertIn(s3, sabb.id, "s3 not in initial-(a)->()-(b)->()-(b)->()")
        self.assertEqual(sabb.next('b')[0], sabb, "initial-(a)->()-(b)->()-(b)->() doesn't point to itself")
        self.assertTrue(sabb.accepting, "initial-(a)->()-(b)->()-(b)->() is not accepting")
        
    def testReducingVisitor ( self ):
        s1, s2, s3, s4, s5, s6, s7 = [Automata.State() for i in range(7)]
        s1.addTransition('a', s2)
        s1.addTransition(('b', 'c', 'e', 'f'), s3)
        s2.addTransition('b', s4)
        s2.addTransition(('a', 'c', 'e', 'f'), s3)
        s4.addTransition('c', s5)
        s4.addTransition('e', s6)
        s4.addTransition('f', s7)
        s4.addTransition(('a', 'b'), s3)
        s3.addTransition(('a', 'b', 'c', 'e', 'f'), s3)
        s5.addTransition(('a', 'b', 'c', 'e', 'f'), s3)
        s5.accepting = True
        s6.addTransition(('a', 'b', 'c', 'e', 'f'), s3)
        s6.accepting = True
        s7.addTransition(('a', 'b', 'c', 'e', 'f'), s3)
        s7.accepting = True
        dfa = Automata(s1)
        dfa.accept(ReducingVisitor())
        self.assertNotIn(s3, s1.fringe(), "s3 still in s1 fringe: " + str(s1.fringe()))
        self.assertNotIn(s3, s2.fringe(), "s3 still in s2 fringe")
        self.assertNotIn(s3, s4.fringe(), "s3 still in s4 fringe")
        self.assertNotIn(s3, s5.fringe(), "s3 still in s5 fringe")
        self.assertNotIn(s3, s6.fringe(), "s3 still in s6 fringe")
        self.assertNotIn(s3, s7.fringe(), "s3 still in s7 fringe")


class ParserTest(unittest.TestCase):

    def testPreprocess ( self ):
        parser = Parser()
        syntaxes = ("ab", "abc", \
                    "a(b)c", "a(bc)", \
                    "a*b", "a*(b)c", "a(b)*c", "abc*", \
                    "a|b", "a(b|c)", "(a|b)c", "(ab|cd)*e", )
        results  = ("a\0b", "a\0b\0c", \
                    "a\0(b)\0c", "a\0(b\0c)", \
                    "a*\0b", "a*\0(b)\0c", "a\0(b)*\0c", "a\0b\0c*", \
                    "a|b", "a\0(b|c)", "(a|b)\0c", "(a\0b|c\0d)*\0e", )
        betterSyntaxes = \
            tuple(map(lambda s: ''.join(Parser.tokenGenerator(parser, s)), syntaxes))
        self.assertEqual(\
            betterSyntaxes, results, \
            "Pre-processed syntaxes: " + str(betterSyntaxes))            
    
    def testConcat ( self ):
        parser = Parser()
        parser.push('a')
        parser.push('b')
        parser.push(chr(0))
        nfa = parser.accept(ThompsonVisitor())
        self.assertRaises(IndexError, parser.pop)
        self.assertRaises(IndexError, parser.popOp)
        self.assertTrue(nfa[1] in nfa[0].next('a'))
        self.assertTrue(nfa[2] in nfa[1].next(Automata.EPSILON))
        self.assertTrue(nfa[3] in nfa[2].next('b'))
        
    def testUnion ( self ):
        parser = Parser()
        parser.push('a')
        parser.push('b')
        parser.push('|')
        nfa = parser.accept(ThompsonVisitor())
        self.assertRaises(IndexError, parser.pop)
        self.assertRaises(IndexError, parser.popOp)
        self.assertTrue(nfa[1] in nfa[0].next(Automata.EPSILON))        
        self.assertTrue(nfa[3] in nfa[0].next(Automata.EPSILON))
        self.assertTrue(nfa[2] in nfa[1].next('a'))
        self.assertTrue(nfa[4] in nfa[3].next('b'))
        self.assertTrue(nfa[5] in nfa[2].next(Automata.EPSILON))
        self.assertTrue(nfa[5] in nfa[4].next(Automata.EPSILON))
    
    def testStar ( self ):
        parser = Parser()
        parser.push('a')
        parser.push('*')
        nfa = parser.accept(ThompsonVisitor())
        self.assertRaises(IndexError, parser.pop)
        self.assertRaises(IndexError, parser.popOp)
        self.assertTrue(nfa[1] in nfa[0].next(Automata.EPSILON))
        self.assertTrue(nfa[3] in nfa[0].next(Automata.EPSILON))
        self.assertTrue(nfa[2] in nfa[1].next('a'))
        self.assertTrue(nfa[1] in nfa[2].next(Automata.EPSILON))
        self.assertTrue(nfa[3] in nfa[2].next(Automata.EPSILON))
    
    def testPlus ( self ):
        parser = Parser()
        parser.push('a')
        parser.push('+')
        nfa = parser.accept(ThompsonVisitor())
        self.assertRaises(IndexError, parser.pop)
        self.assertRaises(IndexError, parser.popOp)
        self.assertTrue(nfa[1] in nfa[0].next('a'))
        self.assertTrue(nfa[0] in nfa[1].next(Automata.EPSILON))
        self.assertTrue(nfa[2] in nfa[1].next(Automata.EPSILON))
    
    def testMakeNfa ( self ):
        parser = Parser()
        syntax = "ab(c|d)+e*(fg)"
        nfa = parser.accept(ThompsonVisitor(), syntax)
        self.assertRaises(IndexError, parser.pop)
        self.assertRaises(IndexError, parser.popOp)
        
    def testMatch ( self ):
        parser = Parser()
        syntax = "Emily*"
        thompsonsm = parser.accept(ThompsonVisitor(), syntax)
        nfa = Automata(thompsonsm[0])
        dfa = nfa.accept(NfaToDfaVisitor())
        dfa.accept(ReducingVisitor())
        matcher = MatchingVisitor("Emily went visiting his uncle Emil")
        matches = dfa.accept(matcher)
        self.assertEqual(\
            matches, ["Emil", "Emily", "Emil"],\
            "Matcher couldn't find all matches: " + str(matcher.matches))
        
        
if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()

