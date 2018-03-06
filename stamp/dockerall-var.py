from src.model import *
from z3 import *

import yaml
import pprint
import inspect
import linecache
import timeit
import itertools
import sys, getopt, os

NSPAR = 2

classes_yaml = """
-
  name: Variable
-
  name: VarValue
  reference: [{name: variable, type: Variable, mandatory: true}]
-
  name: IntValue
  supertype: VarValue
  attribute: [{name: value, type: Integer}]
-
  name: Image
  abstract: True
  reference: [
    {name: features, type: Feature, multiple: true},
    {name: dep, type: Feature, multiple: true}
  ]
- 
  name: BuildImage
  supertype: Image
  reference: [
    {name: from, type: Image, mandatory: true},
    {name: using, type: BuildRule, mandatory: true},
    {name: ival, type: VarValue, multiple: true}
  ]
-
  name: DownloadImage
  supertype: Image
-
  name: BuildRule
  reference: [
    {name: depends, type: Feature, multiple: true},
    {name: requires, type: Feature, multiple: true},
    {name: adds, type: Feature, multiple: true},
    {name: rvar, type: Variable, multiple: true}
  ]
-
  name: Service
  reference: [
    {name: image, type: Image, mandatory: true},
    {name: dependson, type: Service, multiple: true},
    {name: imgfeature, type: Feature, multiple: true},
    {name: sval, type: VarValue, multiple: true}
  ]
-
  name: Feature
  reference: [
    {name: sup, type: Feature},
    {name: allsup, type: Feature, multiple: true},
    {name: root, type: Feature}
  ]
"""

comp_spec = None
variable_spec = None
features = dict()
dimages = dict()
rules = dict()
services = dict()
variables = dict()
varvalues = dict()

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

def afeature(name, sup=None):
    fea = DefineObject(name, Feature)
    if not sup is None:
        fea.force_value('sup', sup)
    features[name] = fea
    return fea

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

def require_feature(w, f):
    return w.features.exists(f1, Or(f1 == f, f1.allsup.contains(f)))

def require_feature_all(wanted, featurelist):
    return And([require_feature(wanted,f) for f in featurelist])

classes = yaml.load(classes_yaml)

Variable, VarValue, IntValue, Image, BuildImage, DownloadImage, BuildRule, Service, Feature \
    = load_all_classes(classes)

generate_meta_constraints()

e1, e2 = ObjectVars(Image, 'e1', 'e2')
f1, f2, f3 = ObjectVars(Feature, 'f1', 'f2', 'f3')
s1, s2 = ObjectVars(Service, 's1', 's2')
wanted = ObjectConst(Image, 'wanted')

buildchains = []
image_spec = None
resultbuildimages = []

def get_wanted(model):
    result = cast_all_objects(model)
    for i in get_all_objects():
        if i.type.package == wanted.type.package:
            if str(model.eval(wanted == i)) == 'True':
                return result[str(i)]

ampimages = dict()
composes = dict()
current_features = []
index = 0

def print_model_deploy(result, wanted):
    v = result[wanted]
    toprint = '\# %s: ' % v['features']

    for elem in result.itervalues():
        if elem['type'] == 'VarValue':
            elem['show'] = elem['name']
        if elem['type'] == 'IntValue':
            elem['show'] = '%s=%s' % (elem['name'], elem['value'])

    chain = []
    bc_item = {
        'chain': chain,
        'features': v['features']
    }
    buildchains.append(bc_item)
    newkey = ''
    newname = None
    newtag = None
    newfeatures = v['features']
    dep = []
    while True:
        if 'using' in v:
            if newname is None:
                newname = v['using']
            else:
                if newtag is None:
                    newtag = v['using']
                else:
                    newtag = newtag + '-' + v['using']
            newkey = newkey + v['using']
            for x in image_spec['buildingrules'][v['using']].get('depends', []):
                dep.append(x)
            toprint = toprint + '%s(%s, %s) -> '%(v['name'], v['using'], [result[s]['show'] for s in v['ival']])
            chain.append({'rule': v['using']})
            v = result[v['from']]
        else:
            toprint = toprint + v['name']
            dimage = image_spec['downloadimages'][v['name']]
            chain.append({'name': dimage['name'], 'tag': dimage['tag']})
            newtag = '%s-%s-%s' % (newtag, dimage['name'], dimage['tag'])
            newkey = newkey + v['name']
            break
    ampimages[newkey] = {
        'name': newname.lower(),
        'tag': newtag.lower(),
        'features': newfeatures,
        'dep': dep
    }
    print toprint
    return ampimages[newkey]

def print_result(model):
    result = cast_all_objects(model)
    print result['image1']
    global index
    resultsrvs = dict()
    composite = {'features': current_features, 'services': resultsrvs}
    for obj in result:
        if result[obj]['type'] == 'Service':
            srv = result[obj]
            srvname = srv['name'][4:]
            wanted = srv['image']
            img = result[srv['image']]
            nametag = None
            if img['type']=='DownloadImage':
                nametag = image_spec['downloadimages'][wanted]
            else:
                nametag = print_model_deploy(result, wanted)
            resultsrvs[srvname] = {
                'image': "%s:%s"%(nametag['name'], nametag['tag'])
            }
            dependson = [x[4:] for x in srv['dependson']]
            if dependson:
                resultsrvs[srvname]['depends_on'] = dependson
            print result[obj]
    index += 1
    composes['compose%d' % index] = composite



covered = []

def find_covered_features(model):
    result = cast_all_objects(model)
    global current_features
    for x in result:
        if result[x]['type'] == 'Service' and result[x]['alive']:
            img = result[result[x]['image']]
            for fea in img['features']:
                feaobj = get_object_by_name(fea)
                current_features.append(str(feaobj))
                if feaobj not in covered:
                    covered.append(feaobj)


def declare_feature(spec, parent):
    if type(spec) is list:
        for str in spec:
            afeature(str, parent)
    if type(spec) is dict:
        for str, val in spec.iteritems():
            newparent = afeature(str, parent)
            declare_feature(val, newparent)

def resolve_features(featurenames):
    return [features[n] for n in featurenames]

def eq_or_child(sub, sup):
    return Or(sub == sup, sub.allsup.contains(sup))

def generate(workingdir):
    global image_spec
    global comp_spec
    global variable_spec
    global NSPAR

    with open(workingdir+'/features.yml', 'r') as stream:
        feature_spec = yaml.load(stream)
    declare_feature(feature_spec, None)
    # print features
    prepare_all_sup()

    with open(workingdir + '/variables.yml') as stream:
        variable_spec = yaml.load(stream)
    for name, value in variable_spec.iteritems():
        if name == 'constraints':
            continue
        variables[name] = DefineObject(name, Variable)
        for valname, valbody in value.iteritems():
            if(valbody['type'] == 'Int'):
                varvalues[valname] = DefineObject(valname, IntValue)
                if 'value' in valbody:
                    varvalues[valname].force_value('value', int(valbody['value']))
            else:
                varvalues[valname] = DefineObject(valname, VarValue)
            varvalues[valname].force_value('variable', variables[name])


    print "Start searching for images"

    with open(workingdir + '/images.yml', 'r') as stream:
        image_spec = yaml.load(stream)
    for name, value in image_spec['downloadimages'].iteritems():
        img = DefineObject(name, DownloadImage)
        dimages[name] = img
        img.force_value('features', resolve_features(value['features']))
    if 'maxfreebuild' in image_spec:
        NSPAR = image_spec['maxfreebuild']
    for name, value in image_spec['buildingrules'].iteritems():
        img = DefineObject(name, BuildRule)
        rules[name] = img
        img.force_value('requires', resolve_features(value['requires']))
        img.force_value('adds', resolve_features(value['adds']))
        img.force_value('depends', resolve_features(value.get('depends', [])))

    with open(workingdir + '/composite.yml', 'r') as stream:
        comp_spec = yaml.load(stream)
    for name, value in comp_spec['services'].iteritems():
        srv = DefineObject('srv_' + name, Service, suspended=True) #not value.get('mandatory', False))
        services[name] = srv
        srv.force_value('imgfeature', resolve_features(value.get('imgfeature', [])))
    for name, value in comp_spec['services'].iteritems():
        srv = services[name]
        if 'dependson' in value:
            srv.force_value('dependson', [services[s] for s in value['dependson']])

    images = [DefineObject('image%d'%i, BuildImage, suspended=True) for i in range(0, NSPAR)]

    generate_config_constraints()

    bi1 = ObjectVar(BuildImage, 'bi1')
    bi2 = ObjectVar(BuildImage, 'bi2')
    v1 = ObjectVar(Variable, 'v1')
    vv1 = ObjectVar(VarValue, 'vv1')
    vv2 = ObjectVar(VarValue, 'vv2')
    meta_facts(
        BuildImage.forall(bi1, And(
            bi1.using.requires.forall(
                f1, bi1['from'].features.exists(
                    f2, Or(f2==f1, f2.allsup.contains(f1))
                )
            ),
            isunionf(bi1.features, bi1['from'].features, bi1.using.adds),
            isunionf(bi1.dep, bi1['from'].dep, bi1.using.depends)
        )),
        BuildImage.forall(bi1, Not(bi1['from'] == bi1)),
        BuildImage.forall(bi1, bi1.features.exists(f1, Not(bi1['from'].features.contains(f1)))),
        BuildImage.forall(bi1, And(
            bi1.using.rvar.forall(v1, Or(
                bi1.ival.exists(vv1, vv1.variable == v1),
                Service.exists(s1, And(s1.image == bi1, s1.sval.exists(vv1, vv1.variable == v1)))
            )),
            bi1.ival.forall(vv1, bi1.using.rvar.contains(vv1.variable)),
            bi1.ival.forall(vv1, bi1.ival.forall(vv2, Or(vv1 == vv2, vv1.variable != vv2.variable)))
        )),
        Image.forall(e1, (e1.features * e1.features).forall(
            [f1, f2], Or(f1 == f2, Not(f1.root == f2.root))
        )),
        Service.forall(s1, s1.image.dep.forall(
            f1, s1.dependson.exists(s2, s2.image.features.exists(f2, eq_or_child(f2, f1))))),
        Service.forall(s1, Or(Feature.exists(f1, s1.image.dep.contains(f1)),
                              Service.forall(s2, Not(s1.dependson.contains(s2))))),
        Service.forall(s1, Not(s1.dependson.contains(s1))),
        Service.forall(s1, s1.imgfeature.forall(
            f1, s1.image.features.exists(f2, eq_or_child(f2, f1))
        ))
    )

    solver = Optimize()
    solver.add(*get_all_meta_facts())
    solver.add(*get_all_config_facts())

    for cst in image_spec.get('constraints', []):
        solver.add(eval(cst))
    for cst in comp_spec.get('constraints', []):
        solver.add(eval(cst))
    for cst in variable_spec.get('constraints', []):
        solver.add(eval(cst))

    maxi = image_spec.get('maximal', 4)
    solver.push()
    for i in range(0, maxi):
        oldlen = len(covered)
        print solver.check()
        print 'Image number %d in %.2f seconds.>>' % (i, timeit.timeit(solver.check, number=1))

        find_covered_features(solver.model())
        print current_features
        if len(covered) == oldlen:
            break
        print_result(solver.model())
        solver.pop()
        solver.push()
        solver.maximize(Feature.filter(
            f1, And(
                And([f1 != fea for fea in covered]),
                Service.exists(s1, s1.image.features.contains(f1))
            )).count()
        )
        print ''
    with open(workingdir + '/out/genimages.yml', 'w') as stream:
        yaml.dump({'buildchains': buildchains}, stream)
        stream.close()
    with open(workingdir + '/out/ampimages.yml', 'w') as stream:
        yaml.dump({'images': ampimages}, stream)
        stream.close()
    finalresult = {
        'watching': comp_spec['services'].keys(),
        'composes': composes
    }
    with open(workingdir+'/out/ampcompose.yml', 'w') as stream:
        yaml.dump(finalresult, stream)
        stream.close()

HELPTEXT = 'dockerbuild.py -d <working dir>'
def main(argv):
    workingdir = ''
    try:
        opts, args = getopt.getopt(argv,"hd:",["dir="])
    except getopt.GetoptError:
        print HELPTEXT
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print HELPTEXT
            sys.exit()
        elif opt in ("-d", "--dir"):
            workingdir = arg

    print 'Working directory is ', workingdir

    if workingdir == '':
        print 'working directory required: ' + HELPTEXT
        exit()

    generate(workingdir)


if __name__ == "__main__":
    main(sys.argv[1:])