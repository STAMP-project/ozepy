from src.model import *
from z3 import *

import yaml
import pprint
import inspect
import linecache
import timeit



classes_yaml = """
-
  name: Element
  reference: [{name: label, type: Label, multiple: true}]
-
  name: Container
  supertype: Element
  abstract: True
  attribute:
    - {name: ports, type: Integer, multiple: true}
  reference:
    - {name: deploy, type: Node, mandatory: true}
    - {name: affinityLabel, type: Label}
    - {name: naffinity, type: Label}
    - {name: nodeLabel, type: Label, multiple: true}
    - {name: link, type: Container, multiple: true}
-
  name: Node
  supertype: Element
  abstract: True
  attribute:
    - {name: isMaster, type: Boolean}
    - {name: slots, type: Integer}
    - {name: price, type: Integer}
  reference:
    - {name: host, type: Container, multiple: true, opposite: deploy}
-
  name: Label
-
  name: UniqueLabel
  supertype: Label
# Below are the service definitions from Docker-Compose file
-
  name: TypeLabel
  supertype: Label
-
  name: StorageLabel
  supertype: UniqueLabel
-
  name: Resource
  supertype: Label
-
  name: Throughput
  supertype: UniqueLabel
-
  name: Web
  supertype: Container
-
  name: Admin
  supertype: Container
-
  name: SingleContainer
  supertype: Container
-
  name: Fast
  supertype: Node
-
  name: Solid
  supertype: Node
"""


classes = yaml.load(classes_yaml)

Element, Container, Node, Label, UniqueLabel, \
TypeLabel, StorageLabel, Resource, Throughput, Web, Admin, SingleContainer, Fast, Solid \
    = load_all_classes(classes)

generate_meta_constraints()

NWEB, NSN, NADM = (10, 9, 1)

e1 = ObjectVar(Element, 'e1')
s1, s2 = ObjectVars(Container, 's1', 's2')
n1, n2 = ObjectVars(Node, 'n1', 'n2')
l1, l2 = ObjectVars(Label, 'l1', 'l2')
i1 = DeclareVar(IntSort(), 'i1')

backupdb = DefineObject('backupdb', SingleContainer)
db = DefineObject('db', SingleContainer)
secondweb = DefineObject('secondweb', SingleContainer)
gallery = DefineObject('gallery', SingleContainer)
imageindex = DefineObject('imageindex', SingleContainer)

webs = [DefineObject('web%d'%i, Web) for i in range(0, NWEB)]
admins = [DefineObject('admin%d'%i, Admin) for i in range(0, NADM)]
sns = [DefineObject('sn%d' % i, Node, suspended=True) for i in range(0, NSN)]

master = DefineObject('master', Fast)
slave = DefineObject('slave', Solid)


ssd, disk = DefineObjects(['ssd', 'disk'], StorageLabel)
high = DefineObject('high', Throughput)
ram = DefineObject('ram', Resource)
lbdb, lbui = DefineObjects(['lbdb', 'lbui'], TypeLabel)

generate_config_constraints()

# General constraints simulating the behaviour of docker-swarm scheduler
meta_facts(
    Element.forall(e1, e1.label.forall(
        l1, Implies(l1.isinstance(UniqueLabel), Not(e1.label.exists(
            l2, And(l1.sametype(l2), l1 != l2))
        ))
    )),
    Container.forall(s1, Or(
        s1.affinityLabel == Undefined,
        s1['deploy']['host'].exists(s2, And(s2 != s1, s2['label'].contains(s1['affinityLabel'])))
    )),
    Container.forall(s1, Or(
        s1.naffinity == Undefined,
        s1['deploy']['host'].forall(s2, Not(s2['label'].contains(s1['naffinity'])))
    )),
    Container.forall(s1, s1['link'].forall(s2, s2['deploy'] == s1['deploy'])),
    Container.forall(s1, s1['nodeLabel'].forall(l1, s1['deploy']['label'].contains(l1))),
#    Container.forall(s1, s1['nNodeLabel'].forall(l1, Not(s1['deploy']['label'].contains(l1)))),
#    Container.forall(s1, Or(s1['nodeDirect'].undefined(), s1['nodeDirect'] == s1['deploy'])),
    Container.forall(s1, s1['ports'].forall(
        i1, s1['deploy']['host'].forall(s2, Or(s1 == s2, Not(s2['ports'].contains(i1))))
    )),
    Node.exists(n1, n1['isMaster']),
    Node.forall(n1, Or(n1['slots'] <= 0, n1['host'].count() <= n1['slots']))
)


lineno_label_assings = inspect.currentframe().f_lineno
label_assigns = [
    db['label'] == [lbdb],
    db['nodeLabel'].contains(ssd),
    db['link'] == [],
    db['ports'] == [],
    db['affinityLabel'] == Undefined,
    db['naffinity'] == Undefined,
    Web['affinityLabel'] == Undefined,
    Web['label'] == [lbui, ram],
    Web['ports'] == [8080],
    Web['naffinity'] == Undefined,
    Web['nodeLabel'] == [],
    Web['link'] == [],
    secondweb['naffinity'] == lbui,
    secondweb['label'] == [],
    secondweb['nodeLabel']==[],
    secondweb['link'] == [],
    secondweb['ports'] == [],
    secondweb['affinityLabel'] == Undefined,
    backupdb['label'] == [],
    backupdb['naffinity'] == lbdb,
    backupdb['nodeLabel'] == [],
    backupdb['link'] == [],
    backupdb['ports'] == [],
    gallery['nodeLabel'] == [high],
    gallery['label'] == [],
    gallery['naffinity'] == Undefined,
    gallery['affinityLabel'] == Undefined,
    gallery['link'] == [],
    gallery['ports'] == [],
    imageindex['label'] == [ram],
    imageindex['link'] == [gallery],
    imageindex['naffinity'] == Undefined,
    imageindex['affinityLabel'] == Undefined,
    imageindex['nodeLabel'] == [],
    imageindex['ports'] == [],
    Admin['label'] == [ram],
    # Admin['naffinity'] == Undefined,
    Admin['affinityLabel'] == Undefined,
    Admin['nodeLabel'] == [],
    Admin['ports'] == [],
    Admin['link'] == [],
    Fast['label'] == [high],
    Fast['slots'] == 3,
    Fast['isMaster'] == True,
    Solid['label'] == [ssd],
    Solid['slots'] == 50,
    Fast['price'] == 5,
    Solid['price'] == 3
]

solver = Solver()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())


def print_model_deploy(model):
    result = cast_all_objects(model)
    for v in result.values():
        if 'deploy' in v:
            print '%s(%s) -> %s(%s) ' % (v['name'], v['type'], v['deploy'], result[v['deploy']]['type'])
    # pprint.pprint(result)


def record_original_text(constraintlist, lineno):
    lineno += 2
    record = dict()
    for c in constraintlist:
        constraint_text = linecache.getline(__file__, lineno).strip(" ,\n")
        while constraint_text.strip().startswith("#"):
            lineno += 1
            constraint_text = linecache.getline(__file__, lineno).strip(" ,\n")
        lineno += 1
        record[c] = constraint_text
    return record

####################################
# Now starts different usages
####################################


def check_conflicting_labels():
    """
    If check returns sat, the model provides a sample scheduling
    If unsat, The unsat_core indicates which labels may make the scheduling impossible
    :return:
    """
    ps = []
    assumptions = []

    original_text = record_original_text(label_assigns, lineno_label_assings)
    for c in label_assigns:
        p = Bool(original_text[c])
        assumptions.append(Implies(p, c))
        ps.append(p)

    solver.add(*assumptions)

    if solver.check(*ps) == sat:
        print_model_deploy(solver.model())
        return True
    else:
        print solver.unsat_core()
        return False


def check_constant_propositions():
    '''
    The function can lead to two conclusions:
      - All the propositions are constant, which means that no matter how the swarm scheduler behave, these
        proposition will hold
      - A set of propositions are not constant. If this is the case, this function
        also prints a sample scheduling that break these propositions
    :return:
    '''
    count_ram = lambda x: x['host'].filter(s1, s1['label'].contains(ram)).count()
    ps = set()
    assumptions = []
    proposition_lineno = inspect.currentframe().f_lineno
    assertions = [
        Not(imageindex['deploy'] == db['deploy']),
        Web.exists(s1, Or(s1['deploy']==imageindex['deploy'], s1['deploy']==db['deploy'])),
        Node.join(Node).forall([n1, n2], count_ram(n1)-count_ram(n2) <= 1)
    ]

    original_text = record_original_text(assertions, proposition_lineno)
    ps = set([Bool(original_text[c]) for c in assertions])
    solver.add(*[Implies(p, Not(c)) for p, c in zip(ps, assertions)])


    # for c in assertions:
    #     p = Bool(original_text[c])
    #     assumptions.append(Implies(p, Not(c)))
    #     ps.add(p)

    # label_assigns.append(Admin['naffinity'] == lbui)
    # solver.add(*assumptions)
    solver.add(*label_assigns)

    if solver.check() == unsat:
        print "There is no valid scheduling at all, please check you labeling first!"
        return

    const_props = set()
    while solver.check(*(ps - const_props)) == unsat:
        const_props = const_props.union(solver.unsat_core())
    if const_props == ps:
        print "All propositions are constant!"
    else:
        print "These propositions can be broken:"
        print list(ps - const_props)
        print "by the following scheduling:"
        print_model_deploy(solver.model())


def optimize_scheduling():
    optimize = Optimize()
    optimize.add(*get_all_meta_facts())
    optimize.add(*get_all_config_facts())
    optimize.add(*label_assigns)

    optimize.minimize(Node.all_instances().map(n1, n1['price']).sum())
    optimize.minimize(master['host'].filter(s1, s1['label'].contains(ram)).count())
    if optimize.check() == sat:
        print_model_deploy(optimize.model())
    else:
        print "no scheduling under current labeling"

# solver.push()
# t = timeit.timeit(check_conflicting_labels, number=1)
# print "Time for checking labels:", t, "\n"
# solver.pop()

# solver.push()
# t = timeit.timeit(check_constant_propositions, number=1)
# print "Time for checking propositions:", t, "\n"
# solver.pop()

solver.push()
t = timeit.timeit(optimize_scheduling, number=1)
print "Time for optimize:", t
solver.pop()

