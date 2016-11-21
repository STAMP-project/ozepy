import unittest
from model import *
import re
import pprint


class TestModelCreation(unittest.TestCase):

    def _extractTempleVar(self, exprstr):
        return re.search('var\w+\d+', exprstr).group(0)

    def setUp(self):
        start_over()
        self.DockerImage = DefineClass('DockerImage')
        self.Vm = DefineClass('Vm', abstract=True)
        self.SmallVm = DefineClass('SmallVm', self.Vm)
        self.LargeVm = DefineClass('LargeVm', self.Vm)
        self.Ubuntu = DefineClass('Ubuntu', self.DockerImage)
        self.Nimbus = DefineClass('Nimbus', self.Ubuntu)
        self.DockerImage.define_attribute('mem', IntSort())
        self.DockerImage.define_reference('deploy', self.Vm, mandatory=True)
        self.Vm.define_reference('host', self.DockerImage, multiple=True, opposite='deploy')
        self.Vm.define_attribute('vmem', IntSort())
        self.DockerImage.define_attribute('port', IntSort())

    def test_newclass(self):
        d1 = Object('d1', self.DockerImage)

        self.assertEqual(self.DockerImage.attributes['mem'].z3()(d1.z3()).sort(), IntSort())
        # Not very logical, but yes they are all _Inst
        self.assertEqual(self.DockerImage.references['deploy'].z3()(d1.z3()).sort(), d1.z3().sort())

    def test_reference_refers(self):
        d1 = ObjectConst('d1', self.DockerImage)
        self.assertEqual(d1['deploy'].z3(), self.DockerImage.references['deploy'].z3()(d1.z3()))

        # self.assertEqual( str(d1['deploy']['host'].guard), '([varDockerImage1] | host(deploy(d1), varDockerImage1))')

        x = declare_obj_var(self.DockerImage, 'x')
        y = declare_obj_var(self.Vm, 'y')

        # deploy = self.DockerImage.references['deploy'].z3()
        # host = self.Vm.references['host'].z3()
        # h = host(deploy(d1.z3()), d1.z3())
        # print substitute(h, (d1.z3(), x.z3()))

        self._assert_expr_in_string(d1['deploy']['host'].contains(d1), 'host(deploy(d1), d1)')

        self._assert_expr_in_string(
            d1['deploy']['host'].forall(x, x['mem'] < 10),
            'ForAll(x,Implies(host(deploy(d1),x),mem(x)<10))'
        )

        self._assert_expr_in_string(
            self.DockerImage.forall(x, x['mem'] > 0),
            'ForAll(x,Implies(And(alive(x),is_instance(x,DockerImage)),mem(x)>0))'
        )

        self._assert_expr_in_string(
            self.DockerImage.all_instances().otherwise(x, x['deploy'].undefined()),
            'ForAll(x,Or(And(alive(x),is_instance(x,DockerImage)),deploy(x)==nil))'
        )

        # expr = self.DockerImage.all_instances().map(x, x['deploy']).forall(y, y.alive())
        # print expr
        self._assert_expr_in_string(
            self.DockerImage.map(x, x['deploy']).forall(y, y.alive()),
            'ForAll(x,Implies(And(alive(x),is_instance(x,DockerImage)),alive(deploy(x))))'
        )

        # print self.DockerImage.all_instances().map(x, x['deploy']).forall(y, y.has_type(self.Vm))
        self._assert_expr_in_string(
            self.DockerImage.map(x, x['deploy']).forall(y, y.isinstance(self.Vm)),
            'ForAll(x,Implies(And(alive(x),is_instance(x,DockerImage)),is_instance(deploy(x),Vm)))'
        )

        print self.DockerImage.all_instances().filter(x, x['mem']>10).map(x, x['deploy']).contains(y)

    def test_join_set(self):
        all_di = self.DockerImage.all_instances()
        all_vm = self.Vm.all_instances()
        x1 = declare_obj_var(self.DockerImage, 'x1')
        x2 = declare_obj_var(self.DockerImage, 'x2')
        y1 = declare_obj_var(self.Vm, 'y1')
        y2 = declare_obj_var(self.Vm, 'y2')
        self._assert_expr_in_string(
            all_di.join(all_di).forall([x1, x2], Implies(x1['port']==x2['port'], x1 == x2)),
            'ForAll([x1,x2],Implies(And(And(alive(x1),is_instance(x1, DockerImage)),And(alive(x2),is_instance(x2, DockerImage))),Implies(port(x1) == port(x2), x1 == x2)))'
        )

        # self._assert_expr_in_string(
        #     (all_di * all_vm).contains((x1, y1)),
        #     'And(And(alive(x1), is_instance(x1,DockerImage)), And(alive(y1), is_instance(y1,Vm)))'
        # )

        print (all_di.map(x1, x1['deploy']) * all_vm).exists([y1, y2], y1 == y2)


    def test_config_constraints(self):
        ubuntu1 = DefineObject('ubuntu1', self.Ubuntu)
        vm1 = DefineObject('vm1', self.Vm, suspended=True)
        ubuntu1.force_value('mem', 10)

        # for i in generate_meta_constraints():
        #     print i
        # for i in generate_config_constraints():
        #     print i

        solver = Solver()
        solver.add(generate_meta_constraints())

        x = declare_obj_var(self.DockerImage, 'x')
        solver.add(self.DockerImage.all_instances().forall(x, x['mem'] <= x['deploy']['vmem']))

        solver.add(generate_config_constraints())

        self.assertEqual(sat, solver.check())
        model = solver.model()
        # print model

        self.assertEqual(10, ubuntu1.cast('mem', model))
        self.assertEqual(str(vm1), ubuntu1.cast('deploy', model))
        result = cast_all_objects(model)
        print result
        pprint.pprint(result)
        self.assertEqual(10, result['vm1']['vmem'])

    def test_sum(self):
        ubuntu1 = DefineObject('ubuntu1', self.Ubuntu)
        vm1 = DefineObject('vm1', self.Vm, suspended=True)

        di1 = DefineObject('di1', self.DockerImage, suspended=True)

        generate_config_constraints()

        x = declare_obj_var(self.DockerImage, 'x')
        y = declare_obj_var(self.Vm, 'y')

        self._assert_expr_in_string(
            self.Vm.forall(y, y['host'].map(x, x['mem']).sum() <= y['vmem']),
            'ForAll(y,\
                   Implies(And(alive(y), is_instance(y, Vm)),\
                           If(host(y, di1), mem(di1), 0) +\
                           If(host(y, ubuntu1), mem(ubuntu1), 0) <=\
                           vmem(y)))'
        )

        print self.Vm.exists(y, y['host'].count() < 2)

    def test_load_class(self):
        start_over()
        DockerImageDesc = {
            'name': 'DockerImage',
            'attribute': [{'name': 'mem', 'type':'Integer'}],
            'reference': [{'name': 'deploy', 'type': 'Vm', 'mandatory': True}]
        }

        UbuntuDesc = {
            'name': 'Ubuntu',
            'supertype': 'DockerImage'
        }

        VmDesc ={
            'name': 'Vm',
            'abstract' : True,
            'attribute': [{'name': 'vmem', 'type': 'Integer'}],
            'reference': [{'name': 'host', 'multiple': True, 'type': 'DockerImage'}]
        }

        DockerImage, Ubuntu, Vm = load_all_classes([DockerImageDesc, UbuntuDesc, VmDesc])

        self.assertEqual(IntSort(), Vm.get_feature('vmem').type)
        print Ubuntu.get_feature('mem').mandatory
        self.assertTrue(DockerImage.get_feature('deploy').mandatory)
        self._assert_onevar_expr_in_pattern(
            declare_obj_var(Ubuntu, 'ubuntu')['deploy']['host'],
            '[([{0}] | host(deploy(ubuntu), {0}))]'
        )


    def test_supertypes(self):
        # self.assertEqual(True, get_ancestors(self.Nimbus))
        self.assertEqual([self.Ubuntu, self.DockerImage], get_ancestors(self.Nimbus))

    def _assert_expr_in_string(self, expr, text):
        self.assertEqual(''.join(str(expr).split()), ''.join(text.split()))

    def _assert_onevar_expr_in_pattern(self, expr, pattern):
        varstr = self._extractTempleVar(str(expr))
        self.assertEqual(
            ''.join(pattern.format(varstr).split()),
            ''.join(str(expr).split())
        )


if __name__ == '__main__':
    unittest.main()