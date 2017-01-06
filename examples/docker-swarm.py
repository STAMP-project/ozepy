from src.model import *
from z3 import *

import yaml
import inspect
import pprint
import inspect
import linecache

classes_yaml = """
-
  name: Service
  attribute:
    - {name: ports, type: Integer, multiple: true}
  reference:
    - {name: deploy, type: Node, mandatory: true}
    - {name: affinityLabel, type: Label}
    - {name: nodeLabel, type: Label, multiple: true}
    - {name: nodeDirect, type: Node}
    - {name: link, type: Service, multiple: true}
    - {name: label, type: Label, multiple: true}
-
  name: Node
  attribute:
    - {name: isMaster, type: Boolean}
    - {name: slots, type: Integer}
  reference:
    - {name: label, type: Label, multiple: true}
    - {name: host, type: Service, multiple: true, opposite: deploy}
-
  name : Label
-
  name: FunctionLabel
  supertype: Label
-
  name: StorageLabel
  supertype: Label
"""


classes = yaml.load(classes_yaml)
Service, Node, Label, FunctionLabel, StorageLabel = load_all_classes(classes)

generate_meta_constraints()

s1, s2 = ObjectVars(Service, 's1', 's2')
n1, n2 = ObjectVars(Node, 'n1', 'n2')
l1, l2 = ObjectVars(FunctionLabel, 'l1', 'l2')

db = DefineObject('db', Service)
wordpress = DefineObject('wordpress', Service)
lb_wordpressdb, lb_cachedb = DefineObjects(['lb_wordpressdb', 'lb_cachedb'], FunctionLabel)
lb_ssd, lb_disk = DefineObjects(['lb_ssd', 'lb_disk'], StorageLabel)
vm1, vm2 = DefineObjects(['vm1', 'vm2'], Node, suspended=True)


generate_config_constraints()

meta_facts(
    Service.forall(s1, Or(
        s1['affinityLabel'].undefined(),
        s1['deploy']['host'].exists(s2, And(s2 != s1, s2['label'].contains(s1['affinityLabel'])))
    )),
    Service.forall(s1, s1['nodeLabel'].forall(l1, s1['deploy']['label'].contains(l1))),
    Service.forall(s1, Or(s1['nodeDirect'].undefined(), s1['nodeDirect']==s1['deploy'])),
    Node.exists(n1, n1['isMaster']),
    Node.forall(n1, Or(n1['slots'] <= 0, n1['host'].count() <= n1['slots'])),
    (StorageLabel * StorageLabel).forall([l1, l2], Node.forall(
        n1, Implies(And(n1['label'].contains(l1), n1['label'].contains(l2)), l1 == l2)))
)

lineno_label_assings = inspect.currentframe().f_lineno
label_assigns = [
    db['label'] == [lb_wordpressdb],
    wordpress['label'] == [],
    wordpress['affinityLabel'] == lb_wordpressdb,
    vm1['slots'] == 1,
    vm1['label'].contains(lb_ssd),
    vm2['label'].contains(lb_disk),
    db['nodeLabel'].contains(lb_ssd)
]

solver = Solver()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())


def print_model_deploy(model):
    result = cast_all_objects(model)
    for v in result.values():
        if v['type'] == 'Service':
            print '%s -> %s ' % (v['name'], v['deploy'])

####################################
# Now starts different usages
####################################

def check_conflicting_labels():
    '''
    If check returns sat, the model provides a sample scheduling
    If unsat, The unsat_core indicates which labels may make the scheduling impossible
    :return:
    '''
    ps = []
    assumptions = []
    lineno = lineno_label_assings + 2
    for c in label_assigns:
        constraint_text = linecache.getline(__file__, lineno).strip(" ,\n")
        while constraint_text.strip().startswith("#"):
            lineno += 1
            constraint_text = linecache.getline(__file__, lineno).strip(" ,\n")
        lineno += 1
        p = Bool(constraint_text)
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
    If unsat, then unsat_core indicate which proposition is always true under the current labeling
      remove the unsat_core, and check again, the new unsat_core indicate more constant propositions
      until sat, then the model gives a sample "wrong scheduling" that breaks the remained propositions
    :return:
    '''
    ps = set()
    assumptions = []
    propositions = [
        wordpress['deploy'].alive(),
        wordpress['deploy'] == db['deploy'],
        # wordpress['deploy'] == vm2
        wordpress['label'].count() == 0
    ]
    for c in propositions:
        p = Bool(str(c))
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

solver.push()
check_conflicting_labels()
solver.pop()

solver.push()
check_constant_propositions()
solver.pop()




    # pprint.pprint(result)