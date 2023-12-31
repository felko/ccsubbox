#!/usr/bin/env python

"""
Find unused definitions in the Coq project.
The roots are the progress and preservation lemmas in CCsub_Soundness.v
as well as capture prediction in CCsub_Substitutition.v.
"""

import os
import sys
import re
import ast
import subprocess
from collections import namedtuple, defaultdict, deque
import tempfile

COQ_DPDGRAPH_LIB = os.getenv("COQ_DPDGRAPH_LIB")

ROOTS = {
    # Local lemmas testing if automation works correctly
    'CCsub_Wellformedness.__test_wf_cset_singleton2',
    'CCsub_Wellformedness.__test_wf_cset_singleton1',
    'CCsub_Lemmas.test_subcapt_regular',

    # Lemmas defined mutually but that are only used by
    # the other lemmas within the same `with` group
    'CCsub_Infrastructure.typeN_weakening',
    'CCsub_Infrastructure.subst_tt_type',
    'CCsub_Infrastructure.subst_ct_type',
    'CCsub_Infrastructure.open_tt_rec_pure_typeN_aux',
    'CCsub_Infrastructure.open_ct_rec_pure_typeN_aux',

    # Main results
    'CCsub_Substitution.capture_prediction',
    'CCsub_Soundness.preservation',
    'CCsub_Soundness.progress',
}

def get_coq_module_names():
    with open("_CoqProject") as coq_project_file:
        coq_project_contents = coq_project_file.read()
        coq_module_names = re.findall(r"\w+(?=\.v)", coq_project_contents)
        return coq_module_names

def generate_dpd_file(coq_module_names, dpd_file_path):
    process = subprocess.Popen(
        args=["coqtop", "-R", ".", "Top", "-I", COQ_DPDGRAPH_LIB, "-I", "."],
        stdin=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
    )

    coq_input = "Require dpdgraph.dpdgraph.\n"
    for module in coq_module_names:
        coq_input += f"Require {module}.\n"
    coq_input += f'Set DependGraph File "{dpd_file_path}".\n'
    coq_input += f"Print FileDependGraph {' '.join(coq_module_names)}.\n"

    process.communicate(coq_input.encode('utf-8'))
    process.wait()

class CoqDPDParseError(ValueError):
    pass

class CoqDependencyGraph:
    Node = namedtuple('Node', ['id', 'name', 'kind', 'prop', 'module'])

    def __init__(self, nodes=None, reverse_dependencies=None, ids_by_name=None):
        self.nodes = nodes or {}
        self.reverse_dependencies = reverse_dependencies or defaultdict(set)
        if ids_by_name is None:
            self.ids_by_name = {f"{node.module}.{node.name}": node.id for id, node in self.nodes.items()}
        else:
            self.ids_by_name = ids_by_name

    @classmethod
    def parse_dpd_file(cls, dpd_file):
        graph = cls()
        for line in dpd_file.readlines():
            if line.startswith('N'):
                node = cls.parse_node(line)
                graph.add_node(node)
            elif line.startswith('E'):
                used, using = cls.parse_dependency(line)
                graph.add_dependency(used, using)
            else:
                raise CoqDPDParseError(f"unable to parse line {line!r}")
        return graph

    @classmethod
    def parse_node(cls, line):
        if m := re.match(r'N: (?P<id>\d+) (?P<name>"[^\"]+") \[(?P<attrs>[^\]]*)\];\n', line):
            id, name, attrs = m.groups()
            name = ast.literal_eval(name)
            attr_dict = {}
            for attr in attrs.split(', '):
                try:
                    key, value = attr.split('=')
                    attr_dict[key] = value
                except ValueError:
                    pass
            kind = attr_dict['kind']
            prop = attr_dict['prop'] == 'yes'
            module = ast.literal_eval(attr_dict['path'])
            return cls.Node(int(id), name, kind, prop, module)
        else:
            raise CoqDPDParseError(f"unable to parse name from line {line!r}")

    @classmethod
    def parse_dependency(cls, line):
        if m := re.match(r'E: (?P<used>\d+) (?P<using>\d+) \[[^\]]*\];\n', line):
            used, using = map(int, m.groups())
            return used, using
        else:
            raise CoqDPDParseError(f"unable to parse dependency from line {line!r}")

    def add_node(self, node):
        self.nodes[node.id] = node
        self.ids_by_name[f"{node.module}.{node.name}"] = node.id

    def add_dependency(self, used, using):
        self.reverse_dependencies[used].add(using)

    def restrict(self, node_ids):
        subgraph = CoqDependencyGraph()

        for node in self.nodes.values():
            if node.id in node_ids:
                subgraph.add_node(node)
            
        for used, using in self.reverse_dependencies.items():
            if used in node_ids and using in node_ids:
                subgraph.add_dependency(used, using)

        return subgraph

    def bfs(self, roots):
        visited = set(roots)
        queue = deque(roots)
        reachable = set()
        
        while queue:
            node_id = queue.popleft()
            reachable.add(node_id)
            
            for using_id in self.reverse_dependencies[node_id]:
                if using_id not in visited:
                    visited.add(using_id)
                    queue.append(using_id)

        return reachable

    def unused(self, roots):
        roots_ids = set(map(self.ids_by_name.get, roots))
        reachable_set = self.bfs(roots_ids)
        return set(self.nodes.keys()).difference(reachable_set)

 
    def topsort(self, coq_module_names):
        visited = set()
        sorted_components = []
        
        def go(node_id):
            visited.add(node_id)
            for using in self.reverse_dependencies[node_id]:
                if using not in visited:
                    self.topsort_aux(using)
            sorted_components[-1].appendleft(self.nodes[node_id])
 
        def module_key(node_id):
            node = self.nodes[node_id]
            try:
                return -coq_module_names.index(node.module)
            except ValueError:
                return 1

        for node_id in sorted(self.nodes, key=module_key):
            if node_id not in visited:
                if not sorted_components or not sorted_components[-1]:
                    sorted_components.append(deque())
                go(node_id)

        return sorted_components

if __name__ == '__main__':
    coq_module_names = get_coq_module_names()
    ccsub_modules = [
        module_name for module_name in coq_module_names
        if module_name.startswith('CCsub_')
    ]

    with tempfile.NamedTemporaryFile(mode="w+") as dpd_file:
        generate_dpd_file(coq_module_names, dpd_file.name)
        dependency_graph = CoqDependencyGraph.parse_dpd_file(dpd_file)
    
    unused_set = dependency_graph.unused(ROOTS)
    unused_graph = dependency_graph.restrict(unused_set)
    sorted_components = unused_graph.topsort(coq_module_names)

    for component in sorted_components:
        print()
        for unused in component:
            if unused.kind == 'cnst' and \
                    unused.prop and \
                    not unused.name.endswith('_ind') and \
                    unused.module in ccsub_modules:
                print(f"{unused.module}.{unused.name}")
