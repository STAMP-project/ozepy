from src.model import *
from z3 import *
import yaml
import timeit

NUM_STATES = 8

class_in_yaml = """
-
  name: State
  reference:
  - {name: next, type: State}
  - {name: near, type: Object, multiple: true}
  - {name: far, type: Object, multiple: true}
-
  name: Object
  reference: [{name: eat, type: Object}]
"""

State, Object = load_all_classes(yaml.load(class_in_yaml))

s = ObjectVar(State, 's')
o, o2 = ObjectVars(Object, 'o', 'o2')
Start, Final = ObjectConsts(State, 'Start', 'Final')

generate_meta_constraints()
meta_facts(
    State.join(Object).forall([s, o], s['near'].contains(o) != s['far'].contains(o)),
    Object.forall(o, Start['near'].contains(o)),
    State.forall(s, Object.forall(o, s['far'].contains(o)) == (s == Final)),
    State.forall(s, And(s.alive(), s['next'].undefined()) == (s == Final)),
    And(Start.alive(), Final.alive())
)

farmer, fox, chicken, grain = [DefineObject(name, Object).get_constant()
                               for name in ['farmer', 'fox', 'chicken', 'grain']]
states = [DefineObject('state%d' % i, State, suspended=True).get_constant() for i in range(0, NUM_STATES)]

generate_config_constraints()
config_facts(
    fox['eat'] == chicken, chicken['eat'] == grain, grain['eat'].undefined(), farmer['eat'].undefined(),
    Implies(states[-1].alive(), states[-1]['next'].undefined()), Start == states[0]
)
config_fact(And([Or(Not(states[i].alive()), states[i] == Final, states[i]['next'] == states[i+1])
                 for i in range(0, len(states)-1)]))

def move(s, thisside, otherside):
    return And(s['next'][otherside].contains(farmer), s[thisside].exists(
        o, And(s['next'][otherside].contains(o), Object.forall(
            o2, Or(o2 == farmer, o2 == o, s['next'][thisside].contains(o2) == s[thisside].contains(o2))))))

config_fact(State.forall(
    s, Or(s == Final, If(s['near'].contains(farmer), move(s, 'near', 'far'), move(s, 'far', 'near')))))
config_fact(State.forall(s, If(
    s['near'].contains(farmer),
    s['far'].forall(o, Not(s['far'].contains(o['eat']))),
    s['near'].forall(o, Not(s['near'].contains(o['eat']))))))

solver = Solver()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())

print "Time for checking:", timeit.timeit(solver.check, number=1)
result = cast_all_objects(solver.model())
# pprint(result)

print 'Here is how they move:'
for s in states:
    sname = str(s)
    if sname in result:
        print '%40s, %40s' % (result[sname]['near'], result[sname]['far'])

