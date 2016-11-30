from src.model import *
from z3 import *
import pprint

import yaml

# Define and load the meta-model

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
  name: Supervisor
  supertype: Ubuntu
-
  name: Vm
  abstract: True
  attribute: [{name: vmem, type: Integer}, {name: price, type: Integer}]
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

# Some temporary variables to be used later in quantifiers
x = ObjectVar(DockerImage, 'x')
y = ObjectVar(Vm, 'y')

# Summon the Z3Opt solver, with optimization and weak constraint support
optimizer = Optimize()

# Put in the generated meta-level constraints
optimizer.add(generate_meta_constraints())

# Additional constraints, force values based on its real type
optimizer.add(LargeVm.forall(y, y['vmem'] == 16))
optimizer.add(LargeVm.forall(y, y['price'] == 20))
optimizer.add(SmallVm.forall(y, y['vmem'] == 4))
optimizer.add(SmallVm.forall(y, y['price'] == 4))
optimizer.add(Nimbus.forall(x, x['mem'] == 3))

# Define Objects. The five VMs are "suspended", which means that they may not be instantiated in
# the solving results. In contrary, all the 5 nimbuses are forced to be instantiated.
# Consolas will not create "new objects" that are not defined (suspended or not) in advance.
vm1, vm2, vm3, vm4, vm5 = DefineObjects(['vm1', 'vm2', 'vm3', 'vm4', 'vm5'], Vm, suspended=True)
nimbuses = DefineObjects(['nb%d' % i for i in range(1,6)], Nimbus)

# Put the generated object-level constraints.
optimizer.add(generate_config_constraints())

# Additional object-level constraints. It is worth noting that the following example (a vm must not
# host more container than its memory capacity allows) is a meta-model level constraints, but in
# Consolas, the "sum" and "count" operation have to declared after all the objects are defined.
optimizer.add(Vm.forall(y, y['vmem'] >= y['host'].map(x, x['mem']).sum()))

print '== minimize the total amount of VM memory:'
optimizer.push()
# Minimize the total amount of memory in all the instanstiated Vms
optimizer.minimize(Vm.map(y, y['vmem']).sum())

print optimizer.check()
result = cast_all_objects(optimizer.model())
print 'Objects: %s' % [(obj['name'], obj['type']) for obj in result.values()]
print 'Deployment: ' + str(['%s -> %s' % (obj['name'], obj['deploy']) for obj in result.values() if obj['type'] == 'Nimbus'])
optimizer.pop()

print '== minimize the total price on VMs:'
optimizer.push()
optimizer.minimize(Vm.map(y, y['price']).sum())

print optimizer.check()
result = cast_all_objects(optimizer.model())
print 'Objects: %s' % [(obj['name'], obj['type']) for obj in result.values()]
print 'Deployment: ' + str(['%s -> %s' % (obj['name'], obj['deploy']) for obj in result.values() if obj['type'] == 'Nimbus'])