from src.model import *
from z3 import *

import yaml
import pprint
import inspect
import linecache
import timeit


classes_yaml = """
-
  name: Image
  abstract: True
  reference: [{name: features, type: Feature, multiple: true}]
- 
  name: BuildImage
  supertype: Image
  reference: [
    {name: from, type: Image, mandatory: true},
    {name: using, type: BuildRule, mandatory: true}
  ]
-
  name: DownloadImage
  supertype: Image
-
  name: BuildRule
  reference: [
    {name: requires, type: Feature, multiple: true},
    {name: adds, type: Feature, multiple: true}
  ]
-
  name: Feature
  reference: [
    {name: sub, type: Feature, multiple: true, opposite: sup},
    {name: sup, type: Feature}
  ]
"""


classes = yaml.load(classes_yaml)

Image, BuildImage, DownloadImage, BuildRule, Feature \
    = load_all_classes(classes)

generate_meta_constraints()

e1, e2 = ObjectVars(Image, 'e1', 'e2')
f1, f2 = ObjectVars(Feature, 's1', 's2')

linux = DefineObject('linux', Feature)
alpine = DefineObject('alpine', Feature).force_value('sup', linux)
ubuntu = DefineObject('ubuntu', Feature).force_value('sup', linux)

java = DefineObject('java', Feature)
java7 = DefineObject('java7', Feature).force_value('sup', java)
java8 = DefineObject('java8', Feature).force_value('sup', java)

python = DefineObject('python', Feature)

java7_lib = DefineObject('java7_lib', DownloadImage).force_value('features', [java7, alpine])
ubuntu_lib = DefineObject('ubuntu_lib', DownloadImage).force_value('features', [ubuntu])

br_python_alpine = DefineObject('br_python_alpine', BuildRule)\
    .force_value('requires', [alpine])\
    .force_value('adds', [python])
br_python_ubuntu = DefineObject('br_python_ubuntu', BuildRule)\
    .force_value('requires', [ubuntu])\
    .force_value('adds', [python])

images = [DefineObject('image%d'%i, BuildImage, suspended=True) for i in range(0, 3)]

wanted = ObjectConst(Image, 'wanted')

generate_config_constraints()

def supersetf(set1, set2):
    return set2.forall(f1, set1.contains(f1))
def subsetf(set1, set2):
    return set1.forall(f1, set2.contains(f1))
def isunionf(res, set1, set2):
    return And(
        res.forall(f1, Or(set1.contains(f1), set2.contains(f1))),
        set1.forall(f1, res.contains(f1)),
        set2.forall(f1, res.contains(f1))
    )
# General constraints simulating the behaviour of docker-swarm scheduler
bi1 = ObjectVar(BuildImage, 'bi1')
bi2 = ObjectVar(BuildImage, 'bi2')
meta_facts(
    BuildImage.forall(bi1, And(
        supersetf(bi1['from'].features, bi1.using.requires),
        isunionf(bi1.features, bi1['from'].features, bi1.using.adds)
    )),
    BuildImage.forall(bi1, Not(bi1['from'] == bi1)),
    BuildImage.forall(bi1, bi1.features.exists(f1, Not(bi1['from'].features.contains(f1))))
)

solver = Solver()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())

solver.add(wanted.features.contains(python), wanted.features.contains(java8))
solver.add(wanted.alive())
solver.add(wanted == images[0])


def print_model_deploy(model):
    result = cast_all_objects(model)
    v = ''
    print result
    print model.eval(wanted == images[2])
    for i in images:
        if str(model.eval(wanted == i)) == 'True':
            v = result[str(i)]
            print 'Found %s' % v
    # while True:
    #     try:
    #         print '%s[%s] -> '%(v['name'], v['using'])
    #         v = result[v['from']]
    #     except:
    #         print v['name']
    #         break

print solver.check()
print_model_deploy(solver.model())

