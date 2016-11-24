# consolas
Z3 front-end on object-oriented systems - an Alloy-like modeller, but on an SMT solver! Woring with Z3-4.5.0 and above

# Meta-model definition

A meta-model is defined as a set of classes. We allow the definition of classes using the core concepts from MOF standard, 
i.e., class, attribute, reference and single inheritance.

Classes can be defined inline:

```python
from z3 import *

DockerImage = Class('DockerImage') # class
Vm = Class('Vm')
DockerImage.define_attribute('mem', IntSort()) # attribute, using primitive Z3 sorts
DockerImage.define_reference('deploy', Vm, mandatory=True) # reference, default as single valued
Vm.define_reference('host', DockerImage, multiple=True) #multi-valued, not mandatory
Vm.define_attribute('vmem', IntSort())
Vm.define_attribute('price', IntSort())
```

Or loaded from a dictionary.

```python

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
```

# Constraint definition

Z3 provides an elegant python-based domain-specific language, the Z3Py, to write SMT constraints. 
The idea of Consolas is to enjoy all the expression power of Z3Py, but extending it with OO conventions.

```Python

d1 = ObjectConst('d1', DockerImage)
x = declare_obj_var(DockerImage, 'x')
y = declare_obj_var(Vm, 'y')

print d1['deploy']['host'].contains(d1)
#> host(deploy(d1), d1)

print DockerImage.all_instances().forall(x, x['mem'] > 0)
#> ForAll(x,Implies(And(alive(x),is_instance(x,DockerImage)),mem(x)>0))

print DockerImage.all_instances().otherwise(x, x['deploy'].undefined())
#> ForAll(x,Or(And(alive(x),is_instance(x,DockerImage)),deploy(x)==nil))

print DockerImage.all_instances().map(x, x['deploy']).forall(y, y.alive())
#> ForAll(x,Implies(And(alive(x),is_instance(x,DockerImage)),alive(deploy(x))))

print DockerImage.all_instances().map(x, x['deploy']).forall(y, y.isinstance(self.Vm))
#> ForAll(x,Implies(And(alive(x),is_instance(x,DockerImage)),is_instance(deploy(x),Vm)))

all_di = self.DockerImage.all_instances()
x1 = DeclareTempObjVar(self.DockerImage, 'x1')
x2 = DeclareTempObjVar(self.DockerImage, 'x2')

print all_di.join(all_di).forall([x1, x2], Implies(x1['port']==x2['port'], x1 == x2))
#> ForAll([x1,x2],Implies(And(And(alive(x1),is_instance(x1, DockerImage)),And(alive(x2),is_instance(x2, DockerImage))),Implies(port(x1) == port(x2), x1 == x2)))
```

# Constraint solving in Z3

```python
# Meta-model definition is the same as above

solver = Solver() #Summon the Z3 Solver

# general meta-level constraints
solver.add(generate_meta_constraints())

# additional meta-level constraints
x = declare_obj_var(self.DockerImage, 'x')
solver.add(self.DockerImage.all_instances().forall(x, x['mem'] <= x['deploy']['vmem']))

# seed objects. ubuntu1 is a must-have object, whereas vm1 is just a stub
ubuntu1 = DefineObject('ubuntu1', Ubuntu)
vm1 = DefineObject('vm1', Vm, suspended=True)
ubuntu1.force_value('mem', 10)

# general object-level constraints
solver.add(generate_config_constraints())

print solver.check()
#> sat

model = solver.model()

print ubuntu1.cast('mem', model)
#> 10

print ubuntu1.cast('deploy', model)
#> vm1

result = cast_all_objects(model)
print result
#> {'ubuntu1': {'name': 'ubuntu1', 'deploy': 'vm1', 'mem': 10, 'alive': True, 'type': Nimbus, 'port': None},
#>  'vm1': {'vmem': 10, 'host': ['ubuntu1'], 'type': LargeVm, 'name': 'vm1', 'alive': True}}

```

# Examples

A simple example for optimizing the deployment of docker images on a set of Vms in
different sizes: [examples/docker-vm.py](https://github.com/SINTEF-9012/consolas/blob/72a198261a8dc3b794302d34c7315b56bebd1ba9/examples/docker-vm.py)

Another example of the farmer river crossing problem [examples/river-crossing],
which is also used by [alloy's tutorial](http://alloy.mit.edu/alloy/tutorials/online/frame-RC-1.html).