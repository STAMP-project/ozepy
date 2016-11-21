from src.model import *
from z3 import *
import pprint

import yaml

classes_yaml = """
-
  name: DockerImage
  attribute: [{name: mem, type: Integer}]
  reference: [{name: deploy, type: Vm, mandatory: true}]
-
  name: Ubuntu
  supertype: DockerImage
-
  name: Nimbus
  supertype: Ubuntu
-
  name: Vm
  abstract: True
  attribute: [{name: vmem, type: Integer}]
  reference: [{name: host, type: DockerImage, multiple: true, opposite: deploy}]
-
  name: LargeVm
  supertype: Vm
-
  name: SmallVm
  supertype: Vm
"""

classes = yaml.load(classes_yaml)
DockerImage, Ubuntu, Nimbus, Vm, LargeVm, SmallVm = load_all_classes(classes)

x = declare_obj_var(DockerImage, 'x')
y = declare_obj_var(Vm, 'y')

solver = Optimize()
solver.add(generate_meta_constraints())

solver.add(LargeVm.forall(y, y['vmem'] == 16))
solver.add(SmallVm.forall(y, y['vmem'] == 4))
solver.add(Nimbus.forall(x, x['mem'] == 3))


vm1, vm2 = DefineObjects(['vm1', 'vm2'], Vm, suspended=True)
nimbuses = DefineObjects(['nb%d' % i for i in range(1,3)], Nimbus, suspended=True)

nimbuses[0].suspended = False
nimbuses[1].suspended = False

solver.add(generate_config_constraints())
solver.add(Vm.forall(y, y['vmem'] >= y['host'].map(x, x['mem']).sum()))

solver.minimize(Vm.all_instances().map(y, y['vmem']).sum())

print solver.sexpr()

print solver.check()
model = solver.model()


result = cast_all_objects(model)
pprint.pprint([obj for obj in result.values() if obj['alive']])

