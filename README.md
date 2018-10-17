![GitHub tag](https://img.shields.io/github/tag/fchauvel/storage.svg)

# OZEPy

Z3 front-end on object-oriented systems - an Alloy-like modeller, but on an SMT solver! 
Working with Z3-4.5.0 and above

# install

```bash docker run -it songhui/ozepy```

Inside the container, you can use ```bash python dockerbuild-single.py``` to try one of the files in the examples folder.

# Meta-model definition

A meta-model is defined as a set of classes. We allow the definition of classes using the core concepts from MOF standard, 
i.e., class, attribute, reference and single inheritance.

Classes can be defined inline:

```python
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

## Object constant

```python
animage = ObjectConst('animage', DockerImage)
```
Like the integer and boolean constant in Z3, an object constant is actually a function that has no argument and
returns an Object in the specified type.
Here ```animage``` is not a specific ```DockerImage``` object in the system.
Instead, it is a place holder, and it will be the Z3 solver to decide which object it points to.

## Attribute and reference access

```python
expr1 = animage['mem']
expr2 = animage['mem'] > 0
expr3 = animage['deploy']
expr4 = expr3['host']
```

We used the '[]' operator (or the ```__getitem__``` method) on an object constant to access an attribute or a reference
of the object. The operator makes an expression, whose type is the same as the attribute or reference.
```expr1``` is an integer expression, which can be used just as any z3 integer experssions, such as comparing
to another integer to construct a boolean expression (```expr2```).
```expr3``` is an object expression in type of ```Vm```, and therefore, we can access any ```Vm``` reference on ```expr3```.
So, the '[]' operator is not defined on object constant, but on object expression.
Object constant is just a special object expression.
Since ```Vm.host``` is a multi-value reference, ```expr4``` is not an object expression, but a Set experssion,
which we will explain later.

## Other operations on object expression
```python
expr5 = (animage['deploy'] == avm) # equals, expr5 is a boolean expression
animage['deploy'].undefined() # animage does not have a 'deploy' reference
expr6 = animage['deploy'].isinstance(DockerImage) # check the type of an object
```

Those are some other operations we defined on an object expression.
Note that expr6 is not False, even though it makes a wrong claim. 

## Set expression and operations

There are several ways to consruct a set expression, and the most common
one is to access a multi-value reference, such as ```expr4```. 
Another common way is to get all the instances of a type: 
```expr7 = Image.all_instances()```

Check if an object is in a set:
```python
avim['host'].contains(animage)
```

We support *quantifiers* on set expressions.

```python
x = ObjectVar(DockerImage, 'x')
expr7 = DockerImage.all_instances().forall(x, x['mem'] > 0)
expr8 = avm['host'].exists(x, x['deploy'] != avm)
```

In a quantifier, we first declare a free variable, and then give a boolean
expression based on the variable.

We can also join two sets, in order to write quantifiers with two variables.

```python
expr9 = DockerImage.all_instance().join(DockerImage.all_instance()).forall(
  [x,y], Implies(x1['port']==x2['port'], x1 == x2)
)
```

We also support map and filter operators on sets. 
Below ```expr10``` is a constant proposition.

```python
expr10 = DockerImage.all_instances().map(x, x['deploy']).forall(y, y.isinstance(self.Vm))
```

We made some shortcuts for sets.

```python
DockerImage.forall(x, x['mem']==0) # same as: DockerImage.all_instances().forall(...)
(DockerImage * Vm).forall([x, y]) # same as DockerImage.join(DockerImage).forall(...)
```

Finally, we can count the number of items in a set, and for a set in type of Integer or Real, we can get the summary.
 
```python
expr11 = avim['host'].count() # an integer expression
expr12 = avim['host'].map(y, y['mem']).sum() < avim['vmem'] # a boolean expression
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
