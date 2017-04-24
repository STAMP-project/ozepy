from src.model import *
import yaml
import timeit

NUM_STATES = 8

class_in_yaml = """
-
  name: State
  reference:
  - {name: next, type: State}
  - {name: near, type: Object, multiple: true}
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
    Object.forall(o, Start['near'].contains(o)),
    State.forall(s, Object.forall(o, Not(s['near'].contains(o))) == (s == Final)),
    State.forall(s, And(s.alive(), s['next'].undefined()) == (s == Final)),
    Start.alive()
)
farmer, fox, chicken, grain = [DefineObject(name, Object).get_constant() for name in ['farmer', 'fox', 'chicken', 'grain']]
states = [DefineObject('state%d' % i, State, suspended=True).get_constant() for i in range(0, NUM_STATES)]
generate_config_constraints()
config_facts(
    fox['eat'] == chicken, chicken['eat'] == grain, grain['eat'].undefined(), farmer['eat'].undefined(),
    Implies(states[-1].alive(), states[-1]['next'].undefined()), Start == states[0]
)
config_fact(And([Or(Not(s1.alive()), s1 == Final, s1['next'] == s2)
                 for s1, s2 in zip(states, states[1:])]))

# def move(s, thisside, otherside):
#     return And(s['next'][otherside].contains(farmer), s[thisside].exists(
#         o, And(s['next'][otherside].contains(o), Object.forall(
#             o2, Or(o2 == farmer, o2 == o, s['next'][thisside].contains(o2) == s[thisside].contains(o2))))))

def move(s):
    return And(s['next']['near'].contains(farmer)!=s['near'].contains(farmer), Object.all_instances().existsOne(
        o, And(s['near'].contains(o) != s['next']['near'].contains(o), o != farmer)))

config_fact(State.forall(
    s, Or(s == Final, move(s))))
config_fact(State.forall(s, Object.forall(o,
    Or(s['near'].contains(farmer)==s['near'].contains(o),
       o['eat'].undefined(),
       s['near'].contains(o)!=s['near'].contains(o['eat'])))))


# config_fact((State * Object).forall(
#     [s, o], Or(o['eat'].undefined(), Implies(
#         s['far'].contains(o) == s['far'].contains(o['eat']), s['far'].contains(o) == s['far'].contains(farmer)))))

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
        print '%40s' % (result[sname]['near'])

