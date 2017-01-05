from src.model import *
from z3 import *

import yaml
import pprint

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
l1 = ObjectVar(FunctionLabel, 'l1')

db = DefineObject('db', Service)
wordpress = DefineObject('wordpress', Service)
lb_wordpressdb = DefineObject('lb_wordpressdb', FunctionLabel).get_constant()
lb_ssd, lb_disk = DefineObjects(['lb_ssd', 'lb_disk'], StorageLabel)
vm1, vm2 = DefineObjects(['vm1', 'vm2'], Node, suspended=True)


generate_config_constraints()

meta_facts(
    Service.forall(s1, Or(
        s1['affinityLabel'].undefined(),
        s1['deploy']['host'].exists(s2, s2['label'].contains(s1['affinityLabel']))
    )),
    Service.forall(s1, s1['nodeLabel'].forall(l1, s1['deploy'].contains(l1))),
    Node.exists(n1, n1['isMaster']),
    Node.forall(n1, Or(n1['slots'] <= 0, n1['host'].count() <= n1['slots']))
)

config_facts(
    db['label'].contains(lb_wordpressdb),
    wordpress['affinityLabel'] == lb_wordpressdb,
    vm1['slots'] == 2,
    vm1['label'].contains(lb_ssd)
)

solver = Solver()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())

print solver.check()

pprint.pprint(cast_all_objects(solver.model()))