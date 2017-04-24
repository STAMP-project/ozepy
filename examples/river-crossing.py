from src.model import *
import yaml, timeit

NUM_STATES = 8
State, Object = load_all_classes(yaml.load("""
-
  name: State
  reference:
  - {name: next, type: State}
  - {name: near, type: Object, multiple: true}
  - {name: far, type: Object, multiple: true}
-
  name: Object
  reference: [{name: eat, type: Object}]
"""))

s = ObjectVar(State, 's')
o, o2 = ObjectVars(Object, 'o', 'o2')
Start, Final = ObjectConsts(State, 'Start', 'Final')
generate_meta_constraints()
meta_facts(
    State.join(Object).forall([s, o], s.near.contains(o) != s.far.contains(o)),
    Object.forall(o, Start.near.contains(o)),
    State.forall(s, Object.forall(o, s.far.contains(o)) == (s == Final)),
    Start.alive()
)
farmer, fox, chicken, grain = [DefineObject(name, Object) for name in ['farmer', 'fox', 'chicken', 'grain']]
states = [DefineObject('state%d' % i, State).get_constant() for i in range(0, NUM_STATES)]
generate_config_constraints()
config_facts(
    fox.eat == chicken, chicken.eat == grain, grain.eat.undefined(), farmer.eat.undefined(),
    Start == states[0], Final == states[-1]
)
config_facts(*[s1['next'] == s2 for s1, s2 in zip(states, states[1:])])

sameside = lambda side: s.next[side].contains(o2) == s[side].contains(o2)
move = lambda s, thisside, otherside: And(s.next[otherside].contains(farmer), Object.exists(
        o, And(s.next[otherside].contains(o), Object.forall(
            o2, Or(o2 == farmer, o2 == o, sameside(thisside))))))

config_fact(State.forall(
    s, Or(s == Final, If(s.near.contains(farmer), move(s, 'near', 'far'), move(s, 'far', 'near')))))

noeat = lambda side: s[side].forall(o, Not(s[side].contains(o.eat)))
config_fact(State.forall(s, If(s.near.contains(farmer), noeat('far'), noeat('near'))))
# solver = Solver()
# solver.add(*once_for_all())
#
# print "Time for checking:", timeit.timeit(solver.check, number=1)
# result = cast_all_objects(solver.model())
#
# for s in states:
#     print result[str(s)]['near']