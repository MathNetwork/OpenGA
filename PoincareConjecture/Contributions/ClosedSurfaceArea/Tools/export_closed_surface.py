#!/usr/bin/env python3
"""Plan and transplant the exact closed-surface proof using Lean oracle facts."""
import hashlib
import json
from collections import defaultdict
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parents[1]
REPOSITORY = DIRECTORY.parents[2]
META = DIRECTORY / 'Metadata'
TARGET = 'OpenGA.RicciFlow.hasDerivAt_area'
ENVIRONMENT = '0df444a360eaa60ab8c11dca51a86af692955474'
SOURCE_REVISION = '58a1945f5e5ed41d2b0bf0ff83544cd7a290ee12'
UPSTREAM_REVISION = '1b535dd102b94cc42b107cca27059687888f08b3'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def path_for(module):
    root = REPOSITORY / '.lake/packages/DifferentialGeometry' if module.startswith('DifferentialGeometry.') else REPOSITORY
    return root / (module.replace('.', '/') + '.lean')


def user_name(name):
    if not name.startswith('_private.'):
        return name
    segments = name.split('.')
    return '.'.join(segments[next(i for i, s in enumerate(segments) if s.isdecimal()) + 1:])


def slug(name):
    return name.replace('.', '_')


def edited(data, edits):
    right = len(data)
    for start, end, value in sorted(set(edits), reverse=True):
        if not 0 <= start <= end <= right:
            raise RuntimeError(f'Overlapping or invalid source spans: {start}, {end}, {right}')
        data = data[:start] + value + data[end:]
        right = start
    return data


class Export:
    def __init__(self):
        self.graph = {r['name']: r for r in map(json.loads, (META / 'declaration_graph.jsonl').read_text().splitlines())}
        self.initial = json.loads((META / 'plan.json').read_text())
        self.provided = set(self.initial['provided'])
        self.modules = self.initial['modules']
        self.sources = {m: path_for(m).read_bytes() for m in self.modules}
        self.facts = {}
        self.groups = {}
        self.owner = {}
        self.rows_by_module = defaultdict(list)
        for row in self.graph.values():
            self.rows_by_module[row['module']].append(row)
        for m in self.modules:
            text = (META / 'Facts' / (m + '.jsonl')).read_text()
            facts = [json.loads(l) for l in text.splitlines() if l.startswith('{')]
            if not any(f['kind'] == 'header' for f in facts):
                raise RuntimeError('No successful oracle extraction: ' + m)
            self.facts[m] = facts
            for f in facts:
                if f['kind'] != 'decl':
                    continue
                key = m + ':' + str(f['declStart']['line'])
                rows = [r for r in self.rows_by_module[m]
                        if f['declStart']['line'] <= r['startLine'] <= f['declEnd']['line']]
                # Local instances disappear from the environment's global
                # instance extension; the parsed binding is the authority.
                if f['nameText'] is None:
                    for r in rows:
                        r['isInstance'] = True
                self.groups[key] = {'module': m, 'fact': f, 'rows': rows}
                for r in rows:
                    if r['name'] in self.owner:
                        raise RuntimeError('Ambiguous declaration owner: ' + r['name'])
                    self.owner[r['name']] = key
        self.constructor_children = defaultdict(list)
        self.elaboration_deps = defaultdict(set)
        for key, group in self.groups.items():
            m, f = group['module'], group['fact']
            for ref in self.facts[m]:
                if ref['kind'] != 'ref' or not (f['declStart']['offset'] <= ref['start']['offset'] < f['declEnd']['offset']):
                    continue
                name = ref['const']
                if name not in self.graph and name.startswith('_private.'):
                    matches = [r['name'] for r in self.rows_by_module[m] if r['userName'] == user_name(name)]
                    if len(matches) == 1:
                        name = matches[0]
                if name in self.graph:
                    self.elaboration_deps[key].add(name)
        for n, r in self.graph.items():
            if r['kind'] == 'ctor':
                for dep in r['typeDeps']:
                    if self.graph[dep]['kind'] == 'inductive':
                        self.constructor_children[dep].append(n)
        # The notation macro's quotation precheck is not a kernel dependency.
        self.selected, self.reached = self.closure([TARGET, 'Bundle.continuousMultilinearMap.productFun'])
        while True:
            roots = set(self.reached)
            for key in self.selected:
                roots.update(r['name'] for r in self.groups[key]['rows'])
            roots.update(n for n, r in self.graph.items() if r['module'] in self.modules and r['isInstance'])
            groups, reached = self.closure(roots)
            if groups == self.selected:
                self.reached = reached
                break
            self.selected, self.reached = groups, reached
        # A structure and all its constructor/field declarations form one unit.
        self.def_groups = {k for k in self.selected if any(r['isInstance'] or r['kind'] not in ('theorem', 'ctor', 'rec')
                            for r in self.groups[k]['rows'])}
        seeds = [r['name'] for k in self.def_groups for r in self.groups[k]['rows']]
        self.embedded, _ = self.closure(seeds)
        self.embedded |= self.def_groups
        while True:
            more, _ = self.closure(r['name'] for k in self.embedded for r in self.groups[k]['rows'])
            if more <= self.embedded:
                break
            self.embedded |= more
        self.nodes = {}
        for k in sorted(self.selected - self.embedded):
            group = self.groups[k]
            f = group['fact']
            candidates = [r for r in group['rows'] if r['kind'] == 'theorem' and not r['isPrivate'] and not r['isInstance']]
            if not candidates or not f['valStart']:
                continue
            row = min(candidates, key=lambda r: len(r['name']))
            if f['declEnd']['line'] - f['valStart']['line'] > 10 or row['name'] == TARGET:
                if not row['name'].isascii() or not all(c.isalnum() or c in '._' for c in row['name']):
                    raise RuntimeError('A node needs an explicit reviewed ASCII rename: ' + row['name'])
                self.nodes[k] = row['name']
        self.inline = self.selected - self.embedded - set(self.nodes)
        self.renames = {}
        self.binding_edits = defaultdict(list)
        self.ref_names = defaultdict(dict)
        for k in self.selected:
            group = self.groups[k]
            m, f = group['module'], group['fact']
            rows = group['rows']
            binding_refs = [r for r in self.facts[m] if r['kind'] == 'ref' and f['declStart']['offset'] <= r['start']['offset']
                            and r['end']['offset'] <= (f['valStart'] or f['declEnd'])['offset']]
            if f['nameText'] is None:
                instances = [r for r in rows if r['isInstance']]
                if len(instances) != 1:
                    raise RuntimeError('Cannot identify anonymous declaration: ' + k)
                row = instances[0]
                refs = [r for r in binding_refs if self.slice(m, r['start'], r['end']) == b'instance']
                if len(refs) != 1:
                    raise RuntimeError('Missing anonymous-instance binding oracle: ' + k)
                new = ('OpenGAExport.' + m + '.instance_' + str(f['declStart']['line'])) if row['isPrivate'] else row['name']
                self.renames[row['name']] = new
                self.binding_edits[m].append((refs[0]['start']['offset'], refs[0]['end']['offset'], ('instance _root_.' + new).encode()))
                self.ref_names[m][refs[0]['const']] = new
            elif any(r['isPrivate'] for r in rows):
                row = next(r for r in rows if r['isPrivate'] and r['userName'].endswith(f['nameText']))
                new = row['userName'] + '_closedSurface_' + slug(m)
                if row['userName'] == 'DifferentialGeometry.TensorMultilinear.contMDiffAt_section_apply_aux':
                    # Recursive self-references are elaborated as local
                    # variables and have no constant-ref oracle span. Keep
                    # the collision-checked source name when deprivatizing.
                    new = row['userName']
                    conflicts = [r for k2 in self.selected for r in self.groups[k2]['rows']
                                 if r['userName'] == new and r['name'] != row['name']]
                    if conflicts:
                        raise RuntimeError('Recursive helper name collision')
                self.renames[row['name']] = new
                for ref in binding_refs:
                    if user_name(ref['const']) == row['userName']:
                        self.ref_names[m][ref['const']] = new
            if f['privateTok']:
                d = f['privateTok']
                self.binding_edits[m].append((d['start']['offset'], d['end']['offset'], b''))
        for m in self.modules:
            for ref in self.facts[m]:
                if ref['kind'] != 'ref':
                    continue
                n = ref['const']
                if n in self.renames:
                    self.ref_names[m][n] = self.renames[n]
                elif n.startswith('_private.'):
                    matches = [r for r in self.rows_by_module[m] if r['isPrivate'] and r['userName'] == user_name(n) and r['name'] in self.renames]
                    if len(matches) == 1:
                        self.ref_names[m][n] = self.renames[matches[0]['name']]
        self.edits = {}
        for m in self.modules:
            edits = self.binding_edits[m][:]
            occupied = {(a, b) for a, b, _ in edits}
            for ref in self.facts[m]:
                if ref['kind'] == 'ref' and ref['const'] in self.ref_names[m]:
                    a, b = ref['start']['offset'], ref['end']['offset']
                    if (a, b) not in occupied:
                        edits.append((a, b, ('_root_.' + self.ref_names[m][ref['const']]).encode()))
                        occupied.add((a, b))
            self.edits[m] = edits
        self.module_order = self.topological_modules()

    def slice(self, module, start, end):
        return self.sources[module][start['offset']:end['offset']]

    def closure(self, roots, stop_groups=()):
        reached, groups, work = set(), set(), list(roots)
        stop = set(stop_groups)
        while work:
            name = work.pop()
            if name in reached or name in self.provided:
                continue
            reached.add(name)
            row = self.graph[name]
            key = self.owner.get(name)
            if key:
                groups.add(key)
                if key in stop:
                    continue
                work.extend(self.elaboration_deps[key])
            elif row['startLine'] and row['module'] not in self.modules:
                raise RuntimeError('Additional source module required: ' + row['module'])
            work.extend(row['typeDeps'] + row['valueDeps'])
            work.extend(self.constructor_children.get(name, []))
        return groups, reached

    def imports(self, module, seen=None):
        seen = set() if seen is None else seen
        if module in seen:
            return set()
        seen.add(module)
        result = set()
        for line in path_for(module).read_text().splitlines():
            if line.startswith('import '):
                child = line.split()[1]
                if child.startswith(('DifferentialGeometry.', 'OpenGALib.')):
                    result |= self.imports(child, seen)
                else:
                    result.add(child)
        return result

    def topological_modules(self):
        # The staged headers preserve source-import ancestry, including
        # elaboration-only imports absent from kernel proof terms.
        def ancestors(module, seen):
            for line in path_for(module).read_text().splitlines():
                if line.startswith('import '):
                    child = line.split()[1]
                    if child.startswith(('DifferentialGeometry.', 'OpenGALib.')) and child not in seen:
                        seen.add(child)
                        ancestors(child, seen)
            return seen
        deps = {m: ancestors(m, set()) for m in self.modules}
        for k in self.selected:
            m = self.groups[k]['module']
            for row in self.groups[k]['rows']:
                for dep in row['typeDeps'] + row['valueDeps']:
                    if dep not in self.provided and self.graph[dep]['module'] != m:
                        deps[m].add(self.graph[dep]['module'])
        order = []
        while deps:
            ready = sorted(m for m, ds in deps.items() if not ds.intersection(deps))
            if not ready:
                raise RuntimeError('Cyclic module dependencies: ' + str(deps))
            for m in ready:
                order.append(m)
                deps.pop(m)
        return order

    def code(self, module, start, end, extra=()):
        a, b = start['offset'], end['offset']
        edits = [(x-a, y-a, s) for x, y, s in self.edits[module] if a <= x <= y <= b]
        edits += [(x-a, y-a, s) for x, y, s in extra]
        return edited(self.sources[module][a:b], edits).decode()

    def group_code(self, key):
        g = self.groups[key]
        return self.code(g['module'], g['fact']['declStart'], g['fact']['declEnd'])

    def command_code(self, module, fact):
        code = self.code(module, fact['start'], fact['end'])
        if code.startswith('open ') and not code.startswith('open scoped '):
            names = code.removeprefix('open ').split()
            if all(n.isascii() and all(c.isalnum() or c in '._' for c in n) for n in names):
                # An imported namespace can become empty after subtraction.
                # Register fully qualified project namespaces before opening
                # them; this introduces no constants or proof assumptions.
                declared = self.provided | {r['userName'] for k in self.selected for r in self.groups[k]['rows']}
                empty = [n for n in names if n.startswith(('DifferentialGeometry.', 'OpenGA.'))
                         and not any(d.startswith(n + '.') for d in declared)]
                return ''.join('namespace ' + n + '\nend ' + n + '\n' for n in empty) + code
        return code

    def skeleton(self, module, selected, instance_attributes=False):
        by_start = {g['fact']['declStart']['offset']: k for k, g in self.groups.items() if g['module'] == module}
        root = {'children': []}
        stack = [root]
        for f in self.facts[module]:
            if f['kind'] != 'command':
                continue
            kind = f['syntaxKind'].removeprefix('Lean.Parser.Command.')
            code = self.command_code(module, f)
            if kind in ('namespace', 'section'):
                child = {'open': code, 'children': []}
                stack[-1]['children'].append(child)
                stack.append(child)
            elif kind == 'end':
                stack[-1]['close'] = code
                stack.pop()
            elif f['start']['offset'] in by_start:
                key = by_start[f['start']['offset']]
                g = self.groups[key]
                if key in selected:
                    stack[-1]['children'].append({'code': code, 'selected': True})
                elif instance_attributes and key in self.embedded and any(r['isInstance'] for r in g['rows']):
                    names = [self.renames.get(r['name'], r['name']) for r in g['rows'] if r['isInstance']]
                    stack[-1]['children'].append({'code': 'attribute [local instance] ' + ' '.join('_root_.' + n for n in names)})
            elif kind not in ('eoi', 'moduleDoc'):
                stack[-1]['children'].append({'code': code})

        def render(node):
            if 'code' in node:
                return node['code'], node.get('selected', False)
            children = [render(c) for c in node['children']]
            keep = any(k for _, k in children)
            if not keep:
                return '', False
            body = '\n\n'.join(s for s, _ in children if s)
            return (node['open'] + '\n\n' + body + '\n\n' + node.get('close', 'end')
                    if 'open' in node else body), True
        return render(root)[0]

    def bundle_name(self, module):
        return 'ClosedSurface_' + slug(module)

    def context(self, key):
        group = self.groups[key]
        module, target = group['module'], group['fact']['declStart']['offset']
        by_start = {g['fact']['declStart']['offset']: k for k, g in self.groups.items() if g['module'] == module}
        scopes = [[]]
        namespaces = ['']
        for f in self.facts[module]:
            if f['kind'] != 'command':
                continue
            if f['start']['offset'] >= target:
                break
            kind = f['syntaxKind'].removeprefix('Lean.Parser.Command.')
            code = self.command_code(module, f)
            if kind == 'namespace':
                name = code.split(None, 1)[1].strip()
                full = (namespaces[-1] + '.' + name).strip('.')
                namespaces.append(full)
                prefixes = ['.'.join(full.split('.')[:i]) for i in range(1, len(full.split('.')) + 1)]
                scopes.append(['namespace ' + full + '\nend ' + full + '\n' +
                               '\n'.join('open _root_.' + p for p in prefixes)])
            elif kind == 'section':
                namespaces.append(namespaces[-1])
                scopes.append([])
            elif kind == 'end':
                namespaces.pop()
                scopes.pop()
            elif f['start']['offset'] in by_start:
                k = by_start[f['start']['offset']]
                if k in self.embedded:
                    names = [self.renames.get(r['name'], r['name']) for r in self.groups[k]['rows'] if r['isInstance']]
                    if names:
                        scopes[-1].append('attribute [local instance] ' + ' '.join('_root_.' + n for n in names))
            elif kind not in ('eoi', 'moduleDoc'):
                scopes[-1].append(code)
        result = 'noncomputable section\n\n' + '\n\n'.join(code for scope in scopes for code in scope)
        body_namespace = self.nodes[key].rsplit('.', 1)[0]
        result += '\n\nnamespace ' + body_namespace + '\nend ' + body_namespace + '\nopen _root_.' + body_namespace
        f = group['fact']
        if f['coreDecl'] and f['coreDecl']['start']['offset'] > f['declStart']['offset']:
            wrapper = self.slice(module, f['declStart'], f['coreDecl']['start']).decode().strip()
            if not wrapper.endswith(' in') or not wrapper.startswith(('omit ', 'include ', 'set_option ', 'open ')):
                raise RuntimeError('Review declaration wrapper: ' + wrapper)
            result += '\n\n' + wrapper[:-3]
        return result

    def node_declaration(self, key, solution=False, stub=False):
        group = self.groups[key]
        module, f = group['module'], group['fact']
        name = self.nodes[key]
        refs = [r for r in self.facts[module] if r['kind'] == 'ref' and r['const'] == name
                and f['declStart']['offset'] <= r['start']['offset'] < r['end']['offset'] <= f['valStart']['offset']]
        if len(refs) != 1:
            raise RuntimeError('Missing unique node binding oracle: ' + name)
        binding = refs[0]
        extra = [(binding['start']['offset'], binding['end']['offset'], ('solution' if solution else name).encode())]
        if stub and f['docstring']:
            d = f['docstring']
            extra.append((d['start']['offset'], d['end']['offset'], b''))
        end = f['valStart'] if stub else f['declEnd']
        start = f['coreDecl']['start'] if f['coreDecl'] else f['declStart']
        return self.code(module, start, end, extra).strip() + (' := by sorry' if stub else '')

    def node_files(self):
        records = []
        for key, name in self.nodes.items():
            group = self.groups[key]
            module = group['module']
            roots = [dep for r in group['rows'] for dep in r['typeDeps'] + r['valueDeps']]
            roots += [n for n in self.elaboration_deps[key] if self.owner.get(n) != key]
            reached, _ = self.closure(roots, stop_groups=set(self.nodes) | self.embedded)
            children = reached.intersection(self.nodes) - {key}
            helpers = reached - self.embedded - set(self.nodes)
            imports = self.header(module, self.embedded).splitlines()
            if any(self.groups[k]['module'] == module for k in self.embedded):
                imports.append('import Definitions.Def_' + self.bundle_name(module))
            for k in helpers:
                m = self.groups[k]['module']
                imports += self.header(m, self.embedded).splitlines()
                if any(self.groups[x]['module'] == m for x in self.embedded):
                    imports.append('import Definitions.Def_' + self.bundle_name(m))
            # Only proof files import child theorems. Statements use the actual
            # definition bundles and preserve the exact original binder context.
            header = '\n'.join(sorted(set(line for line in imports if line))) + '\n\n'
            preamble = header + self.context(key)
            statement = self.node_declaration(key, stub=True)
            path = 'Theorems/Thm_' + slug(name) + '.lean'
            (DIRECTORY / path).write_text(preamble + '\n\n' + statement + '\n')
            proof = '\n'.join('import Theorems.Thm_' + slug(self.nodes[k]) for k in sorted(children)) + '\n' + header
            for m in self.module_order:
                local = {k for k in helpers if self.groups[k]['module'] == m}
                if local:
                    proof += '\nsection\n\n' + self.skeleton(m, local, instance_attributes=True) + '\n\nend\n'
            proof += '\n' + self.context(key) + '\n\n' + self.node_declaration(key, solution=True) + '\n'
            proof_path = 'Solutions/Sol_' + slug(name) + '.lean'
            (DIRECTORY / proof_path).write_text(proof)
            records.append({'key': key, 'name': name, 'path': path, 'proof_path': proof_path,
                            'preamble': preamble, 'formal_statement': statement,
                            'children': sorted(self.nodes[k] for k in children), 'helpers': sorted(helpers)})
        return records

    def header(self, module, available, verified=False):
        imports = self.imports(module)
        imports.add('Definitions.Def_OpenGA_ImmersedMetric')
        ancestors = set()

        def visit(name):
            for line in path_for(name).read_text().splitlines():
                if line.startswith('import '):
                    child = line.split()[1]
                    if child.startswith(('DifferentialGeometry.', 'OpenGALib.')) and child not in ancestors:
                        ancestors.add(child)
                        visit(child)
        visit(module)
        for other in self.module_order:
            if other in ancestors and any(self.groups[k]['module'] == other for k in available):
                imports.add(('Verified.' if verified else 'Definitions.Def_') + self.bundle_name(other))
        return '\n'.join('import ' + m for m in sorted(imports)) + '\n\n'

    def write(self):
        for d in ('Definitions', 'Theorems', 'Solutions', 'Verified'):
            (DIRECTORY / d).mkdir(exist_ok=True)
        for name in ('Def_DifferentialGeometry_SmoothRiemannianMetric.lean', 'Def_OpenGA_ImmersedMetric.lean'):
            (DIRECTORY / 'Definitions' / name).write_bytes((REPOSITORY / 'PoincareConjecture/Contributions/ImmersedSurfaceMetric/Definitions' / name).read_bytes())
        for name in ('lake-manifest.json', 'lean-toolchain', 'lakefile.lean'):
            text = (REPOSITORY / 'PoincareConjecture/Contributions/ImmersedSurfaceMetric' / name).read_text()
            (DIRECTORY / name).write_text(text.replace('ImmersedSurfaceMetricSubmission', 'ClosedSurfaceAreaSubmission'))
        records = []
        for m in self.module_order:
            embedded = {k for k in self.embedded if self.groups[k]['module'] == m}
            if embedded:
                code = self.header(m, self.embedded) + self.skeleton(m, embedded) + '\n'
                path = 'Definitions/Def_' + self.bundle_name(m) + '.lean'
                (DIRECTORY / path).write_text(code)
                records.append({'module': m, 'path': path, 'lines': len(code.splitlines()), 'groups': sorted(embedded)})
            selected = {k for k in self.selected if self.groups[k]['module'] == m}
            code = self.header(m, self.selected, verified=True) + self.skeleton(m, selected) + '\n'
            (DIRECTORY / 'Verified' / (self.bundle_name(m) + '.lean')).write_text(code)
        node_records = self.node_files()
        plan = {'target': TARGET, 'source_revision': SOURCE_REVISION, 'upstream_revision': UPSTREAM_REVISION,
                'selected_groups': sorted(self.selected), 'embedded_groups': sorted(self.embedded),
                'nodes': self.nodes, 'inline_groups': sorted(self.inline), 'renames': self.renames,
                'module_order': self.module_order, 'definition_bundles': records,
                'provided': sorted(self.provided), 'theorem_files': node_records}
        (META / 'export_plan.json').write_text(json.dumps(plan, indent=2) + '\n')
        print(f'Planned {len(records)} definition bundles, {len(self.nodes)} theorem nodes, {len(self.inline)} inline helpers.')


if __name__ == '__main__':
    Export().write()
