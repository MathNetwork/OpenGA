#!/usr/bin/env python3
"""Export the immersion metric and area compatibility from Lean oracle spans."""
import hashlib
import json
import subprocess
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parents[1]
REPOSITORY = DIRECTORY.parents[2]
GRAPH_PATH = REPOSITORY / 'PoincareConjecture/Contributions/ClosedSurfaceArea/Metadata/declaration_graph.jsonl'
ENVIRONMENT = '0df444a360eaa60ab8c11dca51a86af692955474'
UPSTREAM_REVISION = '1b535dd102b94cc42b107cca27059687888f08b3'
PREFIX = 'OpenGA.Surface.'
MODULES = ['DifferentialGeometry.Bundle.Equiv', 'DifferentialGeometry.Bundle.Frame',
           'DifferentialGeometry.Bundle.ClmSectionSmooth',
           'DifferentialGeometry.Geometry.Metric.MetricExistence',
           'OpenGALib.Riemannian.Surface.InducedMetric']
COORDINATES = 'OpenGALib.Riemannian.Surface.Coordinates'
TARGETS = ['surfaceDensity_inducedMetric', 'patchArea_inducedMetric']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_path(module):
    root = REPOSITORY / '.lake/packages/DifferentialGeometry' if module.startswith('DifferentialGeometry.') else REPOSITORY
    return root / (module.replace('.', '/') + '.lean')


def edit(source, edits):
    right = len(source)
    for start, end, text in sorted(edits, reverse=True):
        if not 0 <= start <= end <= right:
            raise RuntimeError('Overlapping oracle spans')
        source = source[:start] + text + source[end:]
        right = start
    return source


def main():
    record_path = DIRECTORY / 'publication.json'
    if record_path.exists():
        old = json.loads(record_path.read_text())
        if any(e.get('publication') or e.get('submission') for e in old['definitions'] + old['theorems']):
            raise RuntimeError('Refusing to replace publication receipts')
    graph = {r['name']: r for r in map(json.loads, GRAPH_PATH.read_text().splitlines())}
    sources = {m: source_path(m).read_bytes() for m in MODULES + [COORDINATES]}
    facts = {m: [json.loads(l) for l in (DIRECTORY / 'Metadata' / (m + '.jsonl')).read_text().splitlines()
                 if l.startswith('{')] for m in sources}
    roots = [PREFIX + n for n in ['inducedInner', 'inducedInner_apply', 'inducedInner_pos',
        'inducedInner_contMDiff', 'inducedMetric', 'inducedMetric_inner',
        'surfaceMetricMatrix_inducedMetric'] + TARGETS]
    roots += [n for n, r in graph.items() if r['isInstance'] and r['module'] in sources]
    selected, pending = set(), roots[:]
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        selected.add(name)
        row = graph[name]
        pending.extend(row['typeDeps'] + row['valueDeps'])
        if row['kind'] == 'inductive':
            pending.extend(n for n, r in graph.items() if r['kind'] == 'ctor' and name in r['typeDeps'])
    survivors = [graph[n] for n in sorted(selected) if graph[n]['startLine']]
    external = {r['module'] for r in survivors} - set(sources)
    if external != {'DifferentialGeometry.Geometry.Metric.Basic', 'OpenGALib.Interoperability.RicciFlow.SurfaceArea'}:
        raise RuntimeError('Unexpected external modules: ' + str(external))
    (DIRECTORY / 'Metadata/selected_declaration_graph.json').write_text(json.dumps(survivors, indent=2) + '\n')

    def owned_declarations(module):
        rows = [r for r in survivors if r['module'] == module]
        for r in rows:
            matches = [f for f in facts[module] if f['kind'] == 'decl' and
                       f['declStart']['line'] <= r['startLine'] <= f['declEnd']['line']]
            if len(matches) != 1:
                raise RuntimeError('Missing or ambiguous oracle fact: ' + r['name'])
        return [f for f in facts[module] if f['kind'] == 'decl' and any(
            f['declStart']['line'] <= r['startLine'] <= f['declEnd']['line'] for r in rows)]

    def skeleton(module):
        # Scope pruning only removes blocks containing no retained declarations.
        # Every declaration, variable, notation and option in a retained scope
        # is copied using the oracle's command spans, without retyping binders.
        selected_spans = {f['declStart']['offset'] for f in owned_declarations(module)}
        all_decls = {f['declStart']['offset'] for f in facts[module] if f['kind'] == 'decl'}
        root = {'children': []}
        stack = [root]
        for f in facts[module]:
            if f['kind'] != 'command':
                continue
            kind = f['syntaxKind'].removeprefix('Lean.Parser.Command.')
            code = sources[module][f['start']['offset']:f['end']['offset']].decode()
            if kind in ('namespace', 'section'):
                child = {'open': code, 'children': []}
                stack[-1]['children'].append(child)
                stack.append(child)
            elif kind == 'end':
                if len(stack) == 1:
                    raise RuntimeError('Unbalanced source scope')
                stack[-1]['close'] = code
                stack.pop()
            elif f['start']['offset'] in all_decls:
                if f['start']['offset'] in selected_spans:
                    stack[-1]['children'].append({'code': code, 'selected': True})
            elif kind != 'eoi':
                stack[-1]['children'].append({'code': code})

        def render(node):
            if 'code' in node:
                return node['code'], node.get('selected', False)
            rendered = [render(c) for c in node['children']]
            keep = any(k for _, k in rendered)
            if not keep:
                return '', False
            body = '\n\n'.join(s for s, _ in rendered if s)
            return ((node['open'] + '\n\n' + body + '\n\n' + node.get('close', 'end'))
                    if 'open' in node else body), True
        return render(root)[0]

    imports, visited = set(), set()

    def import_closure(module):
        if module in visited:
            return
        visited.add(module)
        for line in source_path(module).read_text().splitlines():
            if line.startswith('import '):
                child = line.split()[1]
                if child.startswith(('OpenGALib.', 'DifferentialGeometry.')):
                    import_closure(child)
                else:
                    imports.add(child)
    for module in sources:
        import_closure(module)
    common_imports = '\n'.join('import ' + m for m in sorted(imports)) + '\n'
    definitions = 'import Definitions.Def_DifferentialGeometry_SmoothRiemannianMetric\n' + common_imports
    definitions += '\n/-! Induced metrics of smooth immersions. Supporting proofs are embedded\n'
    definitions += 'because they construct the proof fields of the metric definition.\n'
    definitions += 'Reused DifferentialGeometry code: Apache-2.0, commit ' + UPSTREAM_REVISION + '. -/\n'
    for m in MODULES:
        definitions += '\nsection\n\n/- Source: ' + m + ' -/\n\n' + skeleton(m) + '\n\nend\n'

    def declaration(name, rename=None, stub=False):
        row = graph[PREFIX + name]
        fact, = [f for f in facts[COORDINATES] if f['kind'] == 'decl' and
                 f['declStart']['line'] <= row['startLine'] <= f['declEnd']['line']]
        start = fact['declStart']['offset']
        end = fact['valStart']['offset'] if stub else fact['declEnd']['offset']
        edits = []
        if rename:
            ref, = [f for f in facts[COORDINATES] if f['kind'] == 'ref' and f['const'] == PREFIX + name
                    and start <= f['start']['offset'] < f['end']['offset'] <= fact['valStart']['offset']]
            edits.append((ref['start']['offset'] - start, ref['end']['offset'] - start, rename.encode()))
        if stub and fact.get('docstring'):
            d = fact['docstring']
            edits.append((d['start']['offset'] - start, d['end']['offset'] - start, b''))
        return edit(sources[COORDINATES][start:end], edits).decode().strip() + (' := by sorry' if stub else '')

    context = '\n\n'.join(sources[COORDINATES][f['start']['offset']:f['end']['offset']].decode()
        for f in facts[COORDINATES] if f['kind'] == 'command' and f['syntaxKind'] in
        {'Lean.Parser.Command.open', 'Lean.Parser.Command.variable', 'Lean.Parser.Command.section'})
    base = ('import Definitions.Def_OpenGA_ImmersedMetric\nimport Definitions.Def_OpenGA_SurfaceArea\n'
            + common_imports + '\n' + context + '\n\nopen OpenGA.Surface')
    helper = 'namespace OpenGA.Surface\n\n' + declaration('surfaceMetricMatrix_inducedMetric') + '\n\nend OpenGA.Surface\n\n'

    def save(path, code):
        (DIRECTORY / path).write_text(code)
        return {'path': path, 'sha256': digest(code.encode())}

    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPOSITORY, text=True).strip()

    def source(name):
        row = graph[name]
        repo, rev = ('qinz1yang/differential-geometry', UPSTREAM_REVISION) if row['module'].startswith('DifferentialGeometry.') else ('MathNetwork/OpenGA', revision)
        return f'https://github.com/{repo}/blob/{rev}/{row["module"].replace(".", "/")}.lean#L{row["startLine"]}-L{row["endLine"]}'

    shared = {'env': ENVIRONMENT, 'tags': ['surface-area', 'immersed-surfaces', 'riemannian-geometry', 'colding-minicozzi']}
    definition = {'id': 'OpenGA_ImmersedMetric', 'definitions': [],
        **save('Definitions/Def_OpenGA_ImmersedMetric.lean', definitions),
        'payload': dict(shared, definition_name='OpenGA_ImmersedMetric',
            definition_title='The smooth metric induced by an immersion', definition=definitions,
            natural_language_statement=r'''Let $f:N\to M$ be a smooth map between smooth real manifolds, where $N$ is Hausdorff and finite dimensional, and let $g$ be a smooth Riemannian metric on $M$. Suppose $df_x$ is injective for every $x\in N$. The induced metric on $N$ is

$$h_x(v,w)=g_{f(x)}(df_xv,df_xw).$$

The construction proves symmetry, positive definiteness, finite-dimensional boundedness and smoothness, and returns an actual smooth Riemannian metric. The map $f$ itself need not be injective; self-intersections are allowed. Branch points are excluded by differential injectivity. Supporting smooth-section and positivity proofs are retained from DifferentialGeometry with attribution; the immersion construction is the OpenGA adaptation.''',
            source='; '.join(source(r['name']) for r in survivors if r['module'] in MODULES))}
    descriptions = {
        TARGETS[0]: ('Induced-metric area density agrees with ambient parametrized area', r'''Let $f:N\to(M,g)$ be a smooth immersion of a finite-dimensional Hausdorff manifold, and write $h=f^*g$. Let $p:\mathbb R^2\to N$ be differentiable at $u$. With $J$ denoting the square root of the determinant of the pullback Gram matrix,

$$J_h p(u)=J_g(f\circ p)(u).$$

No injectivity of $p$ or of $f$ as a map is required. This identifies the existing parametrized area density with that computed from the actual induced metric. It supplies local compatibility for global surface area; it is not yet the area variation theorem.''',
        'Apply the manifold chain rule to f composed with p. The induced metric evaluates as the ambient metric on df of each tangent vector, so the two Gram matrices agree entrywise. Their determinants and square roots therefore agree.'),
        TARGETS[1]: ('Induced-metric patch area agrees with ambient parametrized area', r'''Let $f:N\to(M,g)$ be a smooth immersion of a finite-dimensional Hausdorff manifold, and put $h=f^*g$. Let $A\subseteq\mathbb R^2$ be measurable and suppose $p:\mathbb R^2\to N$ is differentiable at every point of $A$. Then

$$\int_A J_h p(u)\,du=\int_A J_g(f\circ p)(u)\,du.$$

The integrals are Bochner integrals, so the equality also applies with Lean's total-integral convention; it identifies the ordinary finite areas whenever the density is integrable. Multiplicity is retained because neither map is required to be injective. This is compatibility of local patch integrals, not a claim about branch points or finite-time extinction.''',
        'Use the proved pointwise equality of area densities at every point of the measurable parameter domain. The set-integral congruence theorem then identifies the two Bochner integrals. The density result is the actual imported proof dependency.')}
    theorems = []
    for index, name in enumerate(TARGETS):
        preamble = base if not index else 'import Theorems.Thm_OpenGA_Surface_' + TARGETS[0] + '\n' + base
        statement = declaration(name, PREFIX + name, True)
        code = preamble + '\n\n' + (helper if not index else '') + declaration(name, 'solution') + '\n'
        entry = {'id': name, 'definitions': ['OpenGA_ImmersedMetric'], 'imports': [] if not index else [TARGETS[0]],
            **save('Theorems/Thm_OpenGA_Surface_' + name + '.lean', preamble + '\n\n' + statement + '\n'),
            'payload': dict(shared, theorem_name=PREFIX + name, theorem_title=descriptions[name][0],
                natural_language_statement=descriptions[name][1], preamble=preamble,
                formal_statement=statement, source=source(PREFIX + name)), 'explanation': descriptions[name][2]}
        proof = save('Solutions/Sol_OpenGA_Surface_' + name + '.lean', code)
        entry.update(proof_path=proof['path'], proof_sha256=proof['sha256'])
        theorems.append(entry)
        verified = base if not index else 'import Verified.' + TARGETS[0] + '\n' + base
        save('Verified/' + name + '.lean', verified + '\n\n' + (helper if not index else '') + declaration(name, PREFIX + name) + '\n')
    record = {'schema_version': 1, 'batch': 'immersed_surface_metric', 'source_revision': revision,
        'mission_id': '29133a9f-c412-4f19-968e-3deae9a335b5', 'milestone_id': '33045187-e820-4325-a253-c8ba2c778897',
        'mathlib_rev': ENVIRONMENT, 'toolchain': 'leanprover/lean4:v4.33.1',
        'definitions': [definition], 'theorems': theorems, 'source_reviewed': True,
        'status': 'STAGED', 'validation': {'status': 'required'},
        'sources': [{'path': str(source_path(m).relative_to(REPOSITORY)), 'sha256': digest(sources[m])} for m in sources],
        'scope': 'Actual induced metric and compatibility with existing local area. Global closed-surface area variation is committed in OpenGA but is not part of this platform batch.',
        'prerequisites': [
            {'theorem_id': '9f78021b-c594-4538-b61f-06a8831433af', 'path': 'Definitions/Def_DifferentialGeometry_SmoothRiemannianMetric.lean'},
            {'theorem_id': '0e220955-5806-447e-b322-843240f3f915', 'path': 'Definitions/Def_OpenGA_SurfaceArea.lean'}],
        'transformations': ['Select declarations and preserve their scope using Lean oracle command spans.',
            'Embed the upstream helper proofs needed to construct the actual smooth metric.',
            'Rename only target bindings using elaborator-resolved reference positions.',
            'Import the proved density compatibility in the patch integral proof.']}
    record_path.write_text(json.dumps(record, indent=2, ensure_ascii=False) + '\n')
    print('Staged the immersion metric and two area compatibility theorems.')


if __name__ == '__main__':
    main()
