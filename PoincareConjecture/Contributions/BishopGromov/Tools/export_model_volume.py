#!/usr/bin/env python3
"""Export a bounded model-volume batch using Lean declaration and reference spans."""
import json
from export_ratio_integral import DIRECTORY, REPOSITORY, PREFIX, REVISION, ENVIRONMENT, NOTICE, edited, digest

TARGET = 'antitoneOn_lintegral_div_hypRadVol'
MODEL = 'DifferentialGeometry_HyperbolicModel'
VOLUME = 'DifferentialGeometry_ModelRadialVolume'
UPSTREAM = REPOSITORY / '.lake/packages/DifferentialGeometry/DifferentialGeometry/Geometry/Comparison/Volume'
PROOF_NOTICE = ('/-\nIncludes unchanged helper proofs from qinz1yang/differential-geometry,\n'
                'Copyright 2026 The DifferentialGeometry contributors, Apache-2.0.\n'
                'Source commit: ' + REVISION + '.\n'
                'The model-integral identity and final specialization are OpenGA results.\n-/\n\n')


def main():
    record_path = DIRECTORY / 'model_publication.json'
    if record_path.exists() and any(e.get('publication') or e.get('submission')
            for es in ('definitions', 'theorems') for e in json.loads(record_path.read_text())[es]):
        raise RuntimeError('Refusing to overwrite publication receipts')
    source_paths = {'model': UPSTREAM / 'HyperbolicModel.lean', 'volume': UPSTREAM / 'BishopBall.lean',
                    'local': REPOSITORY / 'OpenGALib/Analysis/ModelVolume.lean',
                    'ratio': UPSTREAM / 'RatioIntegral.lean',
                    'normalized': REPOSITORY / 'OpenGALib/Analysis/IntegralComparison.lean'}
    fact_paths = {'model': '/tmp/bishop-hyperbolic-facts.jsonl', 'volume': '/tmp/bishop-ball-facts.jsonl',
                  'local': '/tmp/bishop-model-volume-facts.jsonl',
                  'ratio': DIRECTORY / 'Metadata/ratio_integral_facts.jsonl',
                  'normalized': DIRECTORY / 'Metadata/normalized_integral_facts.jsonl'}
    from pathlib import Path
    facts = {key: [json.loads(s) for s in Path(path).read_text().splitlines()] for key, path in fact_paths.items()}
    sources = {key: path.read_bytes() for key, path in source_paths.items()}
    selected = {key: [] for key in facts}

    def declaration(key, name, rename=None, stub=False):
        fact, = [f for f in facts[key] if f['kind'] == 'decl' and f['nameText'] == name]
        if fact not in selected[key]: selected[key].append(fact)
        start, end = fact['declStart']['offset'], fact['declEnd']['offset']
        changes = []
        if rename:
            full = ('OpenGA' if key in ('local', 'normalized') else PREFIX) + '.' + name
            binding, = [f for f in facts[key] if f['kind'] == 'ref' and f['const'] == full
                        and start <= f['start']['offset'] < f['end']['offset'] <= fact['valStart']['offset']]
            changes.append((binding['start']['offset'] - start, binding['end']['offset'] - start, rename.encode()))
        if stub:
            end = fact['valStart']['offset']
            if fact['docstring']:
                doc = fact['docstring']
                changes.append((doc['start']['offset'] - start, doc['end']['offset'] - start, b''))
        value = edited(sources[key][start:end], changes).decode().strip()
        return value + (' := by sorry' if stub else '')

    def group(key, names):
        return '\n\n'.join(declaration(key, name) for name in names)

    def save(path, code):
        (DIRECTORY / path).write_text(code)
        return {'path': path, 'sha256': digest(code.encode())}

    defs = ['hypSn', 'hypSnDeriv', 'hypDensity', 'hypDensityDeriv']
    helpers = ['hasDerivAt_hypSn', 'hypSn_continuous', 'hypSn_pos', 'hasDerivAt_hypDen',
               'hypDen_continuous', 'hypDensity_pos']
    model_code = (NOTICE + 'import Mathlib.Analysis.Calculus.Deriv.Pow\n'
                  'import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\n\n'
                  'noncomputable section\n\nnamespace ' + PREFIX + '\n\n' + group('model', defs) +
                  '\n\nend ' + PREFIX + '\n')
    volume_code = (NOTICE + 'import Definitions.Def_' + MODEL + '\n'
                   'import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic\n\n'
                   'noncomputable section\n\nnamespace ' + PREFIX + '\n\n' +
                   declaration('volume', 'hypRadVol') + '\n\nend ' + PREFIX + '\n')
    common = {'env': ENVIRONMENT, 'tags': ['bishop-gromov', 'differential-geometry', 'measure-theory']}
    upstream_url = 'https://github.com/qinz1yang/differential-geometry/blob/' + REVISION + '/DifferentialGeometry/Geometry/Comparison/Volume/'
    definitions = []
    for id_, name, title, code, dependencies, description, source in [
        ('hyperbolic_model', MODEL, 'Model radial function and density for nonpositive curvature', model_code, [],
         r'Let $q\in\mathbb R$ and $d\in\mathbb N$. Define the model radial function and density by' + '\n\n' +
         r'$$s_q(r)=\begin{cases}r,&q=0,\\\sinh(qr)/q,&q\ne0,\end{cases}\qquad J_{q,d}(r)=s_q(r)^d.$$' + '\n\n' +
         r'For $q\ge0$ and $d=n-1$, these give the radial factors of the $n$-dimensional constant-curvature model with curvature $-q^2$. The bundle also defines their derivative expressions. The zero-curvature case is included; positive model curvature requires a separate trigonometric model.',
         upstream_url + 'HyperbolicModel.lean#L17-L98'),
        ('model_radial_volume', VOLUME, 'Radial model volume for nonpositive curvature', volume_code, ['hyperbolic_model'],
         r'For $q\in\mathbb R$, $d\in\mathbb N$ and $r\in\mathbb R$, let $s_q$ be the model radial function and define' + '\n\n' +
         r'$$V_{q,d}(r)=\int_0^r s_q(t)^d\,dt.$$' + '\n\n' +
         r'For $q\ge0$, $r>0$ and $d=n-1$, this is the radial volume factor in the $n$-dimensional model of curvature $-q^2$. The constant angular factor is omitted because it cancels in volume ratios. The Lean definition uses the oriented interval integral, so it is defined for every real radius.',
         upstream_url + 'BishopBall.lean#L272-L273')]:
        definitions.append({'id': id_, 'definitions': dependencies, **save('Definitions/Def_' + name + '.lean', code),
            'payload': dict(common, definition_name=name, definition_title=title, definition=code,
                            natural_language_statement=description, source=source)})
    preamble = ('import Definitions.Def_' + VOLUME + '\n'
                'import Definitions.Def_DifferentialGeometry_RadialCrossComparison\n\n'
                'set_option autoImplicit false\n\nopen MeasureTheory Set\nopen scoped ENNReal\nopen ' + PREFIX)
    statement = declaration('local', TARGET, 'OpenGA.' + TARGET, stub=True)
    helper_code = ('namespace ' + PREFIX + '\n\n' + group('model', helpers) + '\n\n' +
                   declaration('volume', 'hypRadVol_pos') + '\n\nend ' + PREFIX + '\n\n' +
                   'namespace OpenGA\n\n' + declaration('local', 'lintegral_hypDensity') + '\n\nend OpenGA\n')
    solution = declaration('local', TARGET, 'solution')
    # Restore the original namespace's name resolution, but keep solution at top level.
    proof = (PROOF_NOTICE + 'import Theorems.Thm_OpenGA_antitoneOn_lintegral_Ioc_div\n' + preamble + '\n\n' +
             helper_code + '\nopen OpenGA in\n' + solution + '\n')
    proof_path = 'Solutions/Sol_OpenGA_' + TARGET + '.lean'
    proof_record = save(proof_path, proof)
    theorem = {'id': TARGET, **save('Theorems/Thm_OpenGA_' + TARGET + '.lean', preamble + '\n\n' + statement + '\n'),
        'proof_path': proof_path, 'proof_sha256': proof_record['sha256'],
        'definitions': ['hyperbolic_model', 'model_radial_volume'], 'imports': ['antitoneOn_lintegral_Ioc_div'],
        'payload': dict(common, theorem_name='OpenGA.' + TARGET,
            theorem_title='Radial integral monotonicity with the model-volume denominator',
            preamble=preamble, formal_statement=statement,
            natural_language_statement=(r'Let $q\ge0$, $d\in\mathbb N$, $R\in\mathbb R$, and let $f:\mathbb R\to[0,\infty]$ be almost-everywhere measurable on $(0,R]$ with respect to Lebesgue measure. Set $J(t)=s_q(t)^d$ and $V(r)=\int_0^r J(t)\,dt$. Assume $f(b)J(a)\le f(a)J(b)$ for every $0<a\le b\le R$, interpreting the products in the extended nonnegative reals. Then' + '\n\n' +
                r'$$\frac{\int_{(0,s]}f(t)\,dt}{V(s)}\le\frac{\int_{(0,r]}f(t)\,dt}{V(r)}\qquad(0<r\le s\le R).$$' + '\n\n' +
                r'The numerator may be infinite. For $d=n-1$, the denominator is the radial model volume at curvature $-q^2$. This supplies the analytic normalization step for volume comparison; identifying the numerator with Riemannian ball volume and deriving the density comparison from a Ricci bound are separate geometric steps.'),
            source='OpenGA, OpenGALib/Analysis/ModelVolume.lean#L33-L55; derived from the published normalized integral comparison and the DifferentialGeometry model definitions. https://github.com/MathNetwork/OpenGA/blob/feat/prove2me-differential-geometry/OpenGALib/Analysis/ModelVolume.lean#L33'),
        'explanation': ('Continuity and positivity of the model density give a positive finite model integral at every positive radius. The real interval integral agrees with its extended nonnegative Lebesgue integral. Apply the already proved normalized radial integral comparison and substitute this identity at both radii. The imported comparison theorem and both model definition bundles are genuine dependencies of this proof.')}
    # Complete proof audit: replace the imported analytic stub with the same audited source proofs.
    old = json.loads((DIRECTORY / 'publication.json').read_text())
    child = next(e for e in old['theorems'] if e['id'] == 'lintegral_cross_le')
    original_child = declaration('ratio', 'lintegral_cross_le', PREFIX + '.lintegral_cross_le')
    normalized = declaration('normalized', 'antitoneOn_lintegral_Ioc_div', 'OpenGA.antitoneOn_lintegral_Ioc_div')
    audit = ('import Lean\nimport Theorems.Thm_OpenGA_' + TARGET + '\n' + child['payload']['preamble'] +
             '\n\n' + original_child + '\n\n' + normalized + '\n\n' + helper_code +
             '\nopen OpenGA in\n' + solution + '\n\nopen Lean in\nrun_meta do\n'
             '  let target ← Lean.getConstInfo `OpenGA.' + TARGET + '\n'
             '  let solved ← Lean.getConstInfo `solution\n'
             '  unless ← Lean.Meta.isDefEq target.type solved.type do\n'
             '    throwError "Solution type mismatch"\n'
             '  let axioms ← Lean.collectAxioms `solution\n'
             '  for name in axioms do\n'
             '    unless #[`propext, `Classical.choice, `Quot.sound].contains name do\n'
             '      throwError "Unexpected axiom: {name}"\n'
             '  Lean.logInfo m!"Exact target type and complete proof checked; axioms: {axioms}"\n')
    save('Tools/Audit_' + TARGET + '.lean', audit)
    # Source-selected declaration graph, including compiler-generated closure rows.
    graph_path = DIRECTORY / 'Metadata/declaration_graph.jsonl'
    graph = {r['name']: r for r in map(json.loads, graph_path.read_text().splitlines())}
    roots = [PREFIX + '.' + n for n in defs + helpers + ['hypRadVol', 'hypRadVol_pos']]
    roots += ['OpenGA.lintegral_hypDensity', 'OpenGA.' + TARGET]
    closure, pending = set(), roots[:]
    while pending:
        name = pending.pop()
        if name in closure: continue
        row = graph[name]
        closure.add(name)
        pending.extend(n for n in row['typeDeps'] + row['valueDeps'] if n not in closure)
    graph_out = DIRECTORY / 'Metadata/model_declaration_closure.json'
    graph_out.write_text(json.dumps([graph[n] for n in sorted(closure)], indent=2) + '\n')
    fact_records = []
    for key, decls in selected.items():
        ranges = [(f['declStart']['offset'], f['declEnd']['offset']) for f in decls]
        kept = [f for f in facts[key] if f in decls or f['kind'] == 'header' or
                (f['kind'] in ('ref', 'command') and any(a <= f['start']['offset'] < f['end']['offset'] <= b for a,b in ranges))]
        fp = DIRECTORY / ('Metadata/model_' + key + '_facts.jsonl')
        fp.write_text('\n'.join(json.dumps(f) for f in kept) + '\n')
        fact_records.append(fp)
    record = {'batch': 'model_volume', 'mission_id': old['mission_id'], 'milestone_id': old['milestone_id'],
        'mathlib_rev': ENVIRONMENT, 'toolchain': old['toolchain'], 'upstream_revision': REVISION,
        'definitions': definitions, 'theorems': [theorem],
        'external_theorems': ['antitoneOn_lintegral_Ioc_div'],
        'source_reviewed': True, 'validation': {'status': 'required'}, 'status': 'EXPORTED_NOT_VALIDATED',
        'source_review': 'Five original definitions retain their names, elaborated types and bodies. Seven upstream helper proofs are copied unchanged into the solution using Lean source spans. The two OpenGA lemmas connect the model denominator to the existing normalized-integral comparison; no Ricci or ball-volume hypothesis is inferred.',
        'declaration_graph_sha256': digest(graph_path.read_bytes()),
        'sources': [{'path': str(p.relative_to(REPOSITORY)), 'sha256': digest(p.read_bytes())}
                    for p in list(source_paths.values()) + fact_records + [graph_out]],
        'scout': json.loads(Path('/tmp/bishop-model-scout.json').read_text())}
    record_path.write_text(json.dumps(record, ensure_ascii=False, indent=2, sort_keys=True) + '\n')
    print('Exported two definition bundles and one model-volume comparison theorem.')


if __name__ == '__main__':
    main()
