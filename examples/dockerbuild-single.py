from src.model import *
from z3 import *

import yaml
import pprint
import inspect
import linecache
import timeit
import itertools

NSPAR = 3

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
    {name: sup, type: Feature},
    {name: allsup, type: Feature, multiple: true},
    {name: root, type: Feature}
  ]
"""

def prepare_all_sup():
    features = [fea for fea in get_all_objects() if fea.type.name == 'Feature']
    for fea in features:
        sup = fea.forced_values.get('sup', None)
        if sup is None:
            fea.forced_values['allsup'] = []
        else:
            fea.forced_values['allsup'] = [sup]
    # print features
    for f1 in features:
        for f2 in features:
            for f3 in features:
                if (f2 in f1.forced_values['allsup']) and (f3 in f2.forced_values['allsup']):
                    f1.forced_values['allsup'].append(f3)
    #======== See later if we need a root reference or not=========#
    for fea in features:
        roots = [f for f in fea.forced_values['allsup'] if not ('sup' in f.forced_values) ]
        if roots:
            fea.forced_values['root'] = roots[0]
        else:
            fea.forced_values['root'] = fea

    # for fea in features:
    #     print '%s: (%s)' % (fea.name, fea.forced_values['root'])



classes = yaml.load(classes_yaml)

Image, BuildImage, DownloadImage, BuildRule, Feature \
    = load_all_classes(classes)

generate_meta_constraints()

e1, e2 = ObjectVars(Image, 'e1', 'e2')
f1, f2, f3 = ObjectVars(Feature, 'f1', 'f2', 'f3')


def afeature(name, sup=None):
    fea = DefineObject(name, Feature)
    if not sup is None:
        fea.force_value('sup', sup)
    return fea

linux = afeature('linux')
alpine = afeature('alpine', linux)
alpine36 = afeature('alpine36', alpine)
ubuntu = afeature('ubuntu', linux)

java = afeature('java')
java7 = afeature('java7', java)
java8 = afeature('java8', java)
java9 = afeature('java9', java)

python = afeature('python')

appserver = afeature('appserver')
tomcat = afeature('tomcat', appserver)
tomcat7 = afeature('tomcat7', tomcat)
tomcat8 =  afeature('tomcat8', tomcat)
jetty = afeature('jetty', appserver)

prepare_all_sup()

java7_lib = DefineObject('java7_lib', DownloadImage).force_value('features', [java7, alpine36])
ubuntu_lib = DefineObject('ubuntu_lib', DownloadImage).force_value('features', [ubuntu])

br_python_alpine = DefineObject('br_python_alpine', BuildRule)\
    .force_value('requires', [alpine])\
    .force_value('adds', [python])
br_python_ubuntu = DefineObject('br_python_ubuntu', BuildRule)\
    .force_value('requires', [ubuntu])\
    .force_value('adds', [python])
br_java8_ubuntu = DefineObject('br_java8_ubuntu', BuildRule)\
    .force_value('requires', [ubuntu])\
    .force_value('adds', [java8])
br_tomcat7_java = DefineObject('br_tomcat7_java', BuildRule)\
    .force_value('requires', [java]).force_value('adds', [tomcat7])
br_tomcat8_java = DefineObject('br_tomcat8_java', BuildRule)\
    .force_value('requires', [java]).force_value('adds', [tomcat8])
br_jetty_java8 = DefineObject('br_jetty_java', BuildRule).force_value('requires', [java8])\
    .force_value('adds', [jetty])

images = [DefineObject('image%d'%i, BuildImage, suspended=True) for i in range(0, NSPAR)]

# wanted = ObjectConst(Image, 'wanted')

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


bi1 = ObjectVar(BuildImage, 'bi1')
bi2 = ObjectVar(BuildImage, 'bi2')
meta_facts(
    BuildImage.forall(bi1, And(
        bi1.using.requires.forall(
            f1, bi1['from'].features.exists(
                f2, Or(f2==f1, f2.allsup.contains(f1))
            )
        ),
        isunionf(bi1.features, bi1['from'].features, bi1.using.adds)
    )),
    BuildImage.forall(bi1, Not(bi1['from'] == bi1)),
    BuildImage.forall(bi1, bi1.features.exists(f1, Not(bi1['from'].features.contains(f1)))),
    # Image.forall(e1, (e1.features * e1.features).forall(
    #     [f1, f2], Or(f1==f2, Not(Feature.exists(f3, And(f1.allsup.contains(f3), f2.allsup.contains(f3)))))
    # )),
    Image.forall(e1, (e1.features * e1.features).forall(
        [f1, f2], Or(f1 == f2, Not(f1.root == f2.root))
    ))
)

solver = Optimize()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())

#solver.add(wanted.features.contains(python), wanted.features.contains(java8))
# solver.add(wanted.alive())
# solver.add(wanted == images[0])

def require_feature(w, f):
    return w.features.exists(f1, Or(f1 == f, f1.allsup.contains(f)))

def require_feature_all(wanted, featurelist):
    return And([require_feature(wanted,f) for f in featurelist])

# solver.add(
#     require_feature(wanted, java),
#     require_feature(wanted, python),
#     require_feature(wanted, ubuntu)
# )

wanted = ObjectConst(Image, 'wanted')
solver.add(wanted.isinstance(Image))
solver.add(wanted.alive())
solver.add(require_feature_all(wanted, [appserver, python]))

def get_wanted(model):
    result = cast_all_objects(model)
    for i in get_all_objects():
        if str(model.eval(wanted == i)) == 'True':
            return result[str(i)]


def print_model_deploy(model):
    result = cast_all_objects(model)
    v = get_wanted(model)
    toprint = '\# %s: ' % v['features']

    while True:
        try:
            toprint = toprint + '%s(%s) -> '%(v['name'], v['using'])
            v = result[v['from']]
        except:
            toprint = toprint + v['name']
            break
    print toprint

covered = []

def find_covered_features(model):
    v = get_wanted(model)
    for f in v['features']:
        for i in get_all_objects():
            if i.name == f and not (i in covered):
                covered.append(i)
    print 'features covered: %s' % covered

for i in range(0, 3):
    print 'Image number %d in %.2f seconds.>>' % (i, timeit.timeit(solver.check, number=1))
    print_model_deploy(solver.model())
    find_covered_features(solver.model())
    solver.maximize(wanted.features.filter(f1, And([Not(f1 == fea) for fea in covered])).count())
    print ''


