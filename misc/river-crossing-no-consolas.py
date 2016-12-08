'''
A man has a wolf, a goat and a cabbage.
On the way home he must cross a river.
His boat is small and won't fit more than one of his object.
He cannot leave the goat alone with the cabbage (because the goat would eat it),
nor he can leave the goat alone with the wolf (because the goat would be eaten).
How can the man get everything on the other side in this river crossing puzzle?

http://stackoverflow.com/questions/26562177/river-crossing-puzzle-in-z3
'''


from z3 import *
import timeit

s = Then('qe', 'smt').solver() # This strategy improves efficiency

Obj, (Man, Wolf, Goat, Cabbage) = EnumSort('Obj', ['Man', 'Wolf', 'Goat', 'Cabbage'])
Pos, (Left, Right) = EnumSort('Pos', ['Left', 'Right'])
f = Function('f', Obj, IntSort(), Pos) # f(obj, t) returns the position of the object obj at time t (from 0)

# variables for quantifier
i, j, k, x = Ints('i j k x')
a, b = Consts('a b', Obj)

# At time 0, all the objects are at left side
s.add(ForAll([a],
             f(a, 0) == Left))

# At time x (x >= 0), all objects are at right side
# And before that, the duplicated cases are not allowed
s.add(And(x >= 0,
          ForAll([a], f(a, x) == Right),
          ForAll([j, k],
                 Implies(And(j >= 0, j <= x, k >= 0, k <= x, j != k),
                         Exists([b],
                                f(b, j) != f(b, k))))))

# Man will come over and again between two sides until all objects are at right
s.add(ForAll([i],
             Implies(And(i >= 0, i < x),
                     f(Man, i) != f(Man, i + 1))))

# Man is at the same side with the goat, or goat is at a different side with wolf and cabbage
s.add(ForAll([i],
             Implies(And(i >= 0, i <= x),
                     Or(f(Man, i) == f(Goat, i),
                        And(f(Wolf, i) != f(Goat, i),
                            f(Cabbage, i) != f(Goat, i))))))

# All objects except man remain at the same side,
# or only one object moves the same with man while others remain the same side
s.add(ForAll([i],
             Implies(And(i >= 0, i < x),
                     Or(ForAll([a],  # all objects except man remain the same
                               Implies(a != Man,
                                       f(a, i) == f(a, i + 1))),
                        Exists([b],  # or there must one moves the same with man
                               And(b != Man,
                                   f(b, i) == f(Man, i),
                                   f(b, i + 1) == f(Man, i + 1),
                                   ForAll([a],  # and except that one must remain the same
                                          Implies(And(a != b, a != Man),
                                                  f(a, i) == f(a, i + 1)))))))))

print "Time eclipsed:", timeit.timeit(s.check, number=1)
print

if s.check() != sat:
    print "No result!"
    exit()

m = s.model()
total = m[x].as_long() + 1

for t in range(total):
    print "Step:", t
    print "Man", m.eval(f(Man, t)), "\t",
    print "Wolf", m.eval(f(Wolf, t)), "\t",
    print "Goat", m.eval(f(Goat, t)), "\t",
    print "Cabbage", m.eval(f(Cabbage, t))

print

for t in range(total):
    print "Step:", t
    if m.eval(f(Man, t)).eq(Left):
        print "Man",
    if m.eval(f(Wolf, t)).eq(Left):
        print "Wolf",
    if m.eval(f(Goat, t)).eq(Left):
        print "Goat",
    if m.eval(f(Cabbage, t)).eq(Left):
        print "Cabbage",
    print "~~~>",
    if m.eval(f(Man, t)).eq(Right):
        print "Man",
    if m.eval(f(Wolf, t)).eq(Right):
        print "Wolf",
    if m.eval(f(Goat, t)).eq(Right):
        print "Goat",
    if m.eval(f(Cabbage, t)).eq(Right):
        print "Cabbage",
    print

print "finished"