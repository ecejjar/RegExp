from collections import deque

class NfaGenerationException(Exception):
    pass

class UnknownOperatorException(Exception):
    pass

class NotAnOperatorException(Exception):
    pass

class NotAStateException(Exception):
    pass
    
class Automata(set):

    EPSILON = 0
    
    class State(object):
        id_generator = 0
    
        @classmethod
        def nextId ( c ):
            try:
                c.id_generator = c.id_generator+1
            except:
                c.id_generator = 0
            return c.id_generator
            
        def __init__ ( self, stid = None ):
            self.__id = stid or self.nextId()
            self.__accepting = False
            self.__transitions = {}

        def __eq__ ( self, obj ):
            return self.__id == obj.__id
            
        def __lt__ ( self, obj ):
            return self.__id < obj.__id

        def __repr__ ( self ):
            set_repr = lambda ss: ','.join(map(lambda s: str(s.id), ss))
            tr_repr = lambda it: "%s->(%s)" % (it[0], set_repr(it[1]))
            return "(%s):{%s}" % (str(self.id), ','.join(map(tr_repr, self.__transitions.items())))
            
        def getId ( self ) : return self.__id
        id = property(getId)
        
        def getAccepting ( self ) : return self.__accepting
        def setAccepting ( self, acc ): self.__accepting = acc
        accepting = property(getAccepting, setAccepting)
            
        def addTransition ( self, event, target ):
            try:
                if not any(event): return
            except TypeError:
                event = (event,) 
            finally:
                for e in event:
                    self.__transitions[e] = self.__transitions.get(e, ()) + (target,)

        def removeTransition ( self, target ):
            for event in self.__transitions:
                self.__transitions[event] = \
                    tuple(filter(lambda s: s != target, self.__transitions[event]))
                    
        def next ( self, event=None ):
            if event is None: return self.__transitions
            return self.__transitions.get(event, tuple())
        
        def fringe ( self ):
            return reduce(lambda s1, s2: set(s1).union(s2), self.__transitions.itervalues())
            
        def isDeadEnd ( self ):
            return self.fringe() == {self,}

    def __init__ ( self, initial=None ):
        self.__initial = initial
        self.add(initial)
        
    def getInitial ( self ): return self.__initial
    initial = property(getInitial)
    
    def add ( self, state ):
        if state:
            if not self.__initial: self.__initial = state
            super(Automata, self).add(state)
            for event in state.next():
                for s in filter(lambda s: not s in self, state.next(event)):
                    self.add(s)

    def update ( self, automata ):
        try:
            return self.add(automata.initial)
        except AttributeError:
            return super(Automata, self).update(automata)

    def closure ( self, states, event ):
        result = set()
        if event == Automata.EPSILON: result.update(states)
        for s in states:
            if event == Automata.EPSILON:
                result.update(self.closure(s.next(event), event))
            else:
                result.update(s.next(event))
        return result
            
    def accept ( self, visitor ):
        return visitor.visit(self)        
        
class NfaToDfaVisitor(object):
    def visit ( self, nfa ):
        visited = {}
        Dstates = deque()
        ic = nfa.closure((nfa.initial,), Automata.EPSILON)
        initial = Automata.State(ic)
        Dstates.appendleft(initial)
        while len(Dstates):
            state = Dstates.pop()
            events = {e for s in state.id for e in s.next() if e != Automata.EPSILON}
            for e in events:
                u = nfa.closure(nfa.closure(state.id, e), Automata.EPSILON)
                try:
                    new_state = visited[repr(u)]
                except KeyError:
                    new_state = Automata.State(u)
                    new_state.accepting = any(s.accepting for s in u)
                    Dstates.appendleft(new_state)
                state.addTransition(e, new_state)
            visited[repr(state.id)] = state
        return Automata(initial)

class ReducingVisitor(object):
    def visit ( self, dfa ):
        try:
            visited = set()
            self.__recurse(dfa.initial, visited)
        except AttributeError:
            pass    # not an automata
        finally:
            return dfa
            
    def __recurse ( self, state, visited ):
        if state not in visited:
            visited.add(state)
            for s in state.fringe():
                if s.isDeadEnd():
                    state.removeTransition(s)   # the base case
                else:
                    self.__recurse(s, visited)  # the recursive case

class MatchingVisitor(object):
    def __init__ ( self, string ):
        self.__string = string
        self.__matches = []
        
    def visit ( self, dfa ):
        activestates = deque()
        for i, c in enumerate(self.__string):
            for matcherstate in activestates:
                state, beg = matcherstate
                nextstates = state.next(c)
                if any(nextstates):
                    print("Matched char %s at position %i" % (c, i))
                    if nextstates[0].accepting:
                        self.__matches.append(self.__string[beg:i+1])
                        print("Legal match %s at positions (%i,%i)" % (self.__string[beg:i+1], beg, i+1))
                    matcherstate[0] = nextstates[0]
                    
            nextstates = dfa.initial.next(c)
            if any(nextstates):
                print("Matched char %s at position %i" % (c, i))
                if nextstates[0].accepting:
                    self.__matches.append(self.__string[i:i+1])
                    print("Legal match %s at positions (%i,%i)" % (self.__string[i:i+1], i, i+1))
                activestates.append([nextstates[0], i])
                
        return self.__matches

    def getString ( self ):
        return self.__string
    string = property(getString)
    
    def getMatches ( self ):
        return self.__matches
    matches = property(getMatches)
    
    
class Parser(object):

    def __init__ ( self, oper = ('(', ')', '|', '\0', '*', '+',) ):
        self.__operators = oper
        self.__operandStack = deque()
        self.__operatorStack = deque()
        self.__inputSet = set()

    def isOperator ( self, token ):
        return token in self.__operators

    def isEvent ( self, token ):
        try:
            return token.isalnum() and not self.isOperator(token)
        except:
            return False
            
    def isUnaryOperator ( self, token ):
        return self.isOperator(token) and token in ('*', '+')
    
    def isBinaryOperator ( self, token ):
        return self.isOperator(token) and not self.isUnaryOperator(token)

    def precedence ( self, opl, opr ):
        return self.__operators.index(opl) <= self.__operators.index(opr)
        
    def entersNest ( self, token ):
        return token == self.__operators[0]
                
    def leavesNest ( self, token ):
        return token == self.__operators[1]
                
    def push ( self, token ):
        if self.isEvent(token):
            s0, s1 = Automata.State(), Automata.State()
            s0.addTransition(token, s1);
            nfa = [s0, s1]
            self.__inputSet.add(token)
            self.__operandStack.append(nfa)
        elif self.isOperator(token):
            self.__operatorStack.append(token)
        else:
            try:
                any(token) and token[0].addTransition and token[-1].addTransition
            except:
                raise Exception("Unknown object pushed: " + str(token))
            self.__operandStack.append(token)

    def pop ( self ):
        return self.__operandStack.pop()

    def popOp ( self ):
        return self.__operatorStack.pop()
        
    def tokenGenerator ( self, syntax ):
        def isConcat ( a, b ):
            if not a or not b: return False
            return self.isUnaryOperator(a) and self.entersNest(b) \
                or self.isUnaryOperator(a) and not self.isOperator(b) \
                or self.leavesNest(a) and self.entersNest(b) \
                or self.leavesNest(a) and not self.isOperator(b) \
                or not self.isOperator(a) and self.entersNest(b) \
                or not self.isOperator(a) and not self.isOperator(b)

        if syntax:
            last = None
            for token in syntax:
                if isConcat(last, token): yield chr(0)
                last = token
                yield token
                
    def accept ( self, visitor, syntax = None ):
        for token in self.tokenGenerator(syntax):
            if self.isEvent(token):
                self.push(token)
            #elif len(self.__operatorStack) == 0:   I think this is not needed
            #    self.pushOp(token)
            elif self.entersNest(token):
                self.push(token)
            elif self.leavesNest(token):
                while not self.entersNest(self.__operatorStack[-1]):
                    visitor.visit(self)
                self.popOp()    # pop the '('
            else:
                while any(self.__operatorStack) and \
                      self.precedence(token, self.__operatorStack[-1]):
                    visitor.visit(self)
                self.push(token)
                    
        while any(self.__operatorStack):
            visitor.visit(self)
                  
        nfa = self.pop()
        nfa[-1].accepting = True
        return nfa
        

class ThompsonVisitor(object):
    
    def visit ( self, parser ):
        self.eval(parser)
        
    def eval ( self, parser ):
        operator = parser.popOp()
        if not parser.isOperator(operator):
            raise NotAnOperatorException(operator)
            
        if operator == '*': self.star(parser)
        elif operator == '+': self.plus(parser)
        elif operator == '|': self.union(parser)
        elif operator == '\0': self.concat(parser)
        else:
            raise UnknownOperatorException(operator)
    
    def concat ( self, parser ):
        nfaB, nfaA = parser.pop(), parser.pop()   # Pop order matters: AB != BA
        nfaA[-1].addTransition(Automata.EPSILON, nfaB[0])
        nfaA.extend(nfaB)
        parser.push(nfaA)

    def plus ( self, parser ):
        nfa = parser.pop()
        afterState = Automata.State()
        nfa[-1].addTransition(Automata.EPSILON, nfa[0])
        nfa[-1].addTransition(Automata.EPSILON, afterState)
        nfa.append(afterState)
        parser.push(nfa)

    def star ( self, parser ):
        nfa = parser.pop()
        beforeState, afterState = Automata.State(), Automata.State()
        beforeState.addTransition(Automata.EPSILON, afterState)
        beforeState.addTransition(Automata.EPSILON, nfa[0])
        nfa[-1].addTransition(Automata.EPSILON, afterState)
        nfa[-1].addTransition(Automata.EPSILON, nfa[0])
        nfa.insert(0, beforeState)
        nfa.append(afterState)
        parser.push(nfa)

    def union ( self, parser ):
        nfaB, nfaA = parser.pop(), parser.pop()   # Pop order matters: AB != BA
        beforeState, afterState = Automata.State(), Automata.State()
        beforeState.addTransition(Automata.EPSILON, nfaA[0])

        beforeState.addTransition(Automata.EPSILON, nfaB[0])
        nfaA[-1].addTransition(Automata.EPSILON, afterState)
        nfaB[-1].addTransition(Automata.EPSILON, afterState)
        nfaA.insert(0, beforeState)
        nfaA.extend(nfaB)
        nfaA.append(afterState)
        parser.push(nfaA)


