from src.model import *
from z3 import *

import yaml
import pprint
import inspect
import linecache
import timeit

classes_yaml = """
-
  StorageDriver: ['overlay', 'aufs', 'btrfs', 'devicemapper', 'vfs', 'zfs']
  OperatingSystem: ['boot2docker', 'ubuntu', 'rancherOS', 'debian', 'redhat', 'centos', 'fedora']
-
  name: Element
  reference: [{name: label, type: Label, multiple: true}]
-
  name: Service
  supertype: Element
  attribute:
    - {name: ports, type: Integer, multiple: true}
    - {name: rsdr, type: StorageDriver}
    - {name: ros, type: OperatingSystem}
  reference:
    - {name: deploy, type: Node, mandatory: true}
    - {name: affinityLabel, type: Label}
    - {name: nodeLabel, type: Label, multiple: true}
    - {name: nodeDirect, type: Node}
    - {name: link, type: Service, multiple: true}
-
  name: Node
  supertype: Element
  attribute:
    - {name: isMaster, type: Boolean}
    - {name: slots, type: Integer}
    - {name: sdr, type: StorageDriver}
    - {name: os, type: OperatingSystem}
  reference:
    - {name: host, type: Service, multiple: true, opposite: deploy}
-
  name: Label
-
  name: UniqueLabel
  supertype: Label
# Below are the service definitions from Docker-Compose file
-
  name: FunctionLabel
  supertype: Label
-
  name: StorageLabel
  supertype: UniqueLabel
-
  name: Db
  supertype: Service
-
  name: Wordpress
  supertype: Service
-
  name: SmallVm
  supertype: Node
-
  name: LargeVm
  supertype: Node
"""


classes = yaml.load(classes_yaml)
StorageDriver, OperatingSystem, \
    Element, Service, Node, Label, UniqueLabel, \
    FunctionLabel, StorageLabel, Db, Wordpress, SmallVm, LargeVm \
    = load_all_classes(classes)

generate_meta_constraints()

e1 = ObjectVar(Element, 'e1')
s1, s2 = ObjectVars(Service, 's1', 's2')
n1, n2 = ObjectVars(Node, 'n1', 'n2')
l1, l2 = ObjectVars(FunctionLabel, 'l1', 'l2')
i1 = DeclareVar(IntSort(), 'i1')

db = DefineObject('db', Db)
# wordpress = DefineObject('wordpress', Wordpress)
wordpresses = DefineObjects(['wordpress%d'%n for n in range(0, 3)], Wordpress)
lb_wordpressdb, lb_cachedb = DefineObjects(['lb_wordpressdb', 'lb_cachedb'], FunctionLabel)
lb_ssd, lb_disk = DefineObjects(['lb_ssd', 'lb_disk'], StorageLabel)
vm1 = DefineObject('vm1', LargeVm, suspended=True)
vm3, vm4 = DefineObjects(['vm3', 'vm4'], SmallVm, suspended=True)


generate_config_constraints()

# General constraints simulating the behaviour of docker-swarm scheduler
meta_facts(
    Element.forall(e1, e1['label'].forall(
        l1, Implies(l1.isinstance(UniqueLabel), Not(e1['label'].exists(
            l2, And(l1.sametype(l2), l1 != l2))
        ))
    )),
    Service.forall(s1, Or(
        s1.affinityLabel.undefined(),
        s1['deploy']['host'].exists(s2, And(s2 != s1, s2['label'].contains(s1['affinityLabel'])))
    )),
    Service.forall(s1, s1['link'].forall(s2, s2['deploy'] == s1['deploy'])),
    Service.forall(s1, s1['nodeLabel'].forall(l1, s1['deploy']['label'].contains(l1))),
    Service.forall(s1, Or(s1['nodeDirect'].undefined(), s1['nodeDirect'] == s1['deploy'])),
    Service.forall(s1, s1['ports'].forall(
        i1, s1['deploy']['host'].forall(s2, Not(s2['ports'].contains(i1)))
    )),
    # Service.forall(s1, s1['deploy']['sdr'] == s1['rsdr']),
    # Service.forall(s1, s1['deploy']['os'] == s1['ros']),
    Node.exists(n1, n1['isMaster']),
    Node.forall(n1, Or(n1['slots'] <= 0, n1['host'].count() <= n1['slots'])),
    Node.forall(n1, n1['host'].forall(s1, n1['os'] == s1['ros']))
)

# Labels set up by users
# lineno_label_assings = inspect.currentframe().f_lineno
# label_assigns = [
#     db['label'] == [lb_wordpressdb],
#     wordpress['label'] == [],
#     wordpress['affinityLabel'] == lb_wordpressdb,
#     vm1['slots'] == 2,
#     vm1['label'].contains(lb_ssd),
#     vm2['label'].contains(lb_disk),
#     db['nodeLabel'].contains(lb_ssd),
#     db['nodeDirect'] == vm2
# ]
lineno_label_assings = inspect.currentframe().f_lineno
label_assigns = [
    db['label'] == [lb_wordpressdb],
    db['nodeLabel'].contains(lb_ssd),
    Wordpress['affinityLabel'] == lb_wordpressdb,
    Wordpress['label'] == [],
    # Wordpress.forcevalue('ports', [8080]),
    SmallVm['slots'] == 4,
    LargeVm['slots'] == 16,
    vm1['label'].contains(lb_ssd),
    LargeVm.forall(n1, n1['label'].contains(lb_disk))
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
    ps = set()
    assumptions = []
    proposition_lineno = inspect.currentframe().f_lineno
    propositions = [
        And([wp['deploy'].alive() for wp in wordpresses]),
        And([wp['deploy'] == db['deploy'] for wp in wordpresses]),
        And([wp['deploy'] == vm3 for wp in wordpresses]),
        And([wp['label'].count() == 0 for wp in wordpresses])
    ]

    original_text = record_original_text(propositions, proposition_lineno)
    for c in propositions:
        p = Bool(original_text[c])
        assumptions.append(Implies(p, Not(c)))
        ps.add(p)

    solver.add(*assumptions)
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

    optimize.maximize(Node.all_instances().count())
    if optimize.check() == sat:
        print_model_deploy(optimize.model())
    else:
        print "no scheduling under current labeling"

solver.push()
t = timeit.timeit(check_conflicting_labels, number=1)
print "Time for checking labels:", t, "\n"
solver.pop()

solver.push()
t = timeit.timeit(check_constant_propositions, number=1)
print "Time for checking propositions:", t, "\n"
solver.pop()

solver.push()
t = timeit.timeit(optimize_scheduling, number=1)
print "Time for optimize:", t
solver.pop()

