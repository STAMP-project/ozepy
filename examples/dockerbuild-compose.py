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
  reference: [
    {name: features, type: Feature, multiple: true},
    {name: dep, type: Feature, multiple: true}
  ]
-
  name: DownloadImage
  supertype: Image
-
  name: Feature
  reference: [
    {name: sup, type: Feature},
    {name: allsup, type: Feature, multiple: true},
    {name: root, type: Feature}
  ]
-
  name: Service
  reference: [
    {name: image, type: Image, mandatory: true},
    {name: dependson, type: Service, multiple: true},
    {name: imgfeature, type: Feature, multiple: true}
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
    #     print '%s: (%s)' % (fea.name, fea.forced_values['allsup'])



classes = yaml.load(classes_yaml)

Image, DownloadImage, Feature, Service\
    = load_all_classes(classes)

generate_meta_constraints()

e1, e2 = ObjectVars(Image, 'e1', 'e2')
f1, f2, f3 = ObjectVars(Feature, 'f1', 'f2', 'f3')
s1, s2 = ObjectVars(Service, 's1', 's2')


def afeature(name, sup=None):
    fea = DefineObject(name, Feature)
    if not sup is None:
        fea.force_value('sup', sup)
    return fea

db = afeature('db')
mysql = afeature('mysql', db)
mysql8 = afeature('mysql8', mysql)
mysql5 = afeature('mysql5', mysql)

postgres = afeature('postgres', db)

be = afeature('be')
bemysql = afeature('bemysql', be)
bepostgres = afeature('bepostgres', be)

prepare_all_sup()

img_mysql5 = DefineObject('img_mysql5', DownloadImage)\
    .force_value('features', [mysql5])
img_mysql8 = DefineObject('img_mysql8', DownloadImage)\
    .force_value('features', [mysql8])

img_postgres = DefineObject('img_postgres', DownloadImage)\
    .force_value('features', [postgres])

img_be_mysql =  DefineObject('img_be_mysql', DownloadImage)\
    .force_value('features', [bemysql])\
    .force_value('dep', [mysql])\

img_be_postgres =  DefineObject('img_be_postgres', DownloadImage)\
    .force_value('features', [bepostgres])\
    .force_value('dep', [postgres])\

srv_be = DefineObject('srv_be', Service).force_value('imgfeature', [be])
srv_db = DefineObject('srv_db', Service, suspended=True).force_value('imgfeature', [db])



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


def eq_or_child(sub, sup):
    return Or(sub == sup, sub.allsup.contains(sup))

meta_facts(
    Service.forall(s1, s1.image.dep.forall(
        f1, s1.dependson.exists(s2, s2.image.features.exists(f2, eq_or_child(f2, f1))))),
    Service.forall(s1, s1.imgfeature.forall(
        f1, s1.image.features.exists(f2, eq_or_child(f2, f1))
    ))
)

solver = Optimize()
solver.add(*get_all_meta_facts())
solver.add(*get_all_config_facts())


def print_result(model):
    result = cast_all_objects(solver.model())
    for obj in result:
        if result[obj]['type'] == 'Service':
            print result[obj]

covered = []

def find_covered_features(model):
    result = cast_all_objects(model)
    for x in result:
        if result[x]['type'] == 'Service' and result[x]['alive']:
            img = result[result[x]['image']]
            for fea in img['features']:
                feaobj = get_object_by_name(fea)
                if feaobj not in covered:
                    covered.append(feaobj)
solver.push()
for i in range(0, 3):
    print 'In %.2f seconds.>>' % timeit.timeit(solver.check, number=1)
    print_result(solver.model())
    find_covered_features(solver.model())
    print covered
    solver.pop()
    solver.push()
    solver.maximize(Feature.filter(
        f1, And(
            And([f1 != fea for fea in covered]),
            Service.exists(s1, s1.image.features.contains(f1))
        )).count()
    )



