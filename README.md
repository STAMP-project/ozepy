# consolas
Z3 front-end on object-oriented systems - an Alloy-like modeller, but on an SMT solver!

# Modeling and constraint definition

```Python
from z3 import *

DockerImage = Class('DockerImage')
Vm = Class('Vm')
DockerImage.define_attribute('mem', IntSort())
DockerImage.define_reference('deploy', Vm)
Vm.define_reference('host', DockerImage, True)
Vm.define_attribute('vmem', IntSort())

d1 = ObjectConst('d1', DockerImage)
x = DeclareTempObjVar(DockerImage, 'x')
y = DeclareTempObjVar(Vm, 'y')

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

solver = Solver()

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

# TODO:
- Intersect, Union
