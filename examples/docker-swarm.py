from src.model import *
from z3 import *

import yaml
import pprint

classes_yaml = """
-
  name: Service
  attribute: [{name: ports, type: Integer, multiple: true}]
  reference:
    - {name: deploy, type: Node, mandatory: true}
    - {name: affinityLabel, type: Label}
    - {name: nodeLabel, type: Label}
    - {name: nodeDirect, type: Node}
    - {name: link, type: Service, multiple: true}
    - {name: label, type: Label, multiple: true}
-
  name: Node
  attribute: [{name: isMaster, type: Boolean}, {name: slots, type: Integer}]
  reference:
    - {name: master, type: Node}
    - {name: label, type: Label, multiple: true}
    - {name: host, type: Service, multiple: true, opposite: deploy}
-
  name : Label
-
  name: FunctionLabel
  supertype: Label
"""


classes = yaml.load(classes_yaml)
Service, Node, Label, FunctionLabel = load_all_classes(classes)

generate_meta_constraints()

s1, s2 = ObjectVars(Service, 's1', 's2')
l1 = ObjectVar(FunctionLabel, 'l1')

meta_fact(Service.forall(s1, Or(
    s1['affinityLabel'].undefined(),
    s1['deploy']['host'].exists(s2, s2['label'].contains(s1['affinityLabel']))
)))

db = DefineObject('db', Service)
wordpress = DefineObject('wordpress', Service)
lb_wordpressdb = DefineObject('lb_wordpressdb', FunctionLabel).get_constant()
vm1 = DefineObject('vm1', Node)
vm2 = DefineObject('vm2', Node)

generate_config_constraints()

config_fact(db['label'].contains(lb_wordpressdb))
config_fact(wordpress['affinityLabel'] == lb_wordpressdb)

solver = Solver()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())

print solver.check()

pprint.pprint(cast_all_objects(solver.model()))