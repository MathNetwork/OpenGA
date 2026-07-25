# Modifications Log

Tracks modifications to the vendored DeGiorgi code (https://github.com/scottnarmstrong/DeGiorgi,
commit `4c1b307`) per Apache License 2.0 §4(b).

## Format

```
### <YYYY-MM-DD> — <short tag>

**Files**: <list of modified files, relative to this directory>
**Change**: <short description>
```

## Entries

### 2026-04-23 — initial vendoring

**Files**: (none modified)
**Change**: Repository vendored verbatim at commit 4c1b307.

### 2026-04-28 — import-path rewire

**Files**: all `.lean` files under this directory
**Change**: rewrote internal `import DeGiorgi.…` statements as `import DifferentialGeometry.External.DeGiorgi.…` to fit the project's module path layout.

### 2026-05-16 — style-warning cleanup

**Files**:
- `BallExtension.lean`
- `BallExtension/ApproximationControl.lean`
- `BallExtension/SmoothApproximation.lean`
- `BallExtension/SmoothCore.lean`
- `BallExtensionEstimates.lean`
- `BallScaling.lean`
- `DeGiorgiIteration/Linfty.lean`
- `DeGiorgiIteration/PreIteration.lean`
- `Harnack.lean`
- `Holder/Representative.lean`
- `Localization.lean`
- `LpFunctionToolkit.lean`
- `MoserIteration/CutoffPrep/Profiles.lean`
- `MoserIteration/CutoffPrep/RegularizedEnergy.lean`
- `MoserIteration/CutoffPrep/RegularizedWitnesses.lean`
- `MoserIteration/CutoffPrep/WitnessConstruction.lean`
- `MoserIteration/Iteration.lean`
- `Oscillation/BMO.lean`
- `Oscillation/Campanato.lean`
- `Oscillation/LocalJohnNirenberg.lean`
- `Poincare.lean`
- `PositivePart.lean`
- `SobolevChainRule.lean`
- `SobolevPoincare.lean`
- `SobolevSpace/Approximation.lean`
- `SobolevSpace/WeakDerivatives.lean`
- `SobolevSpace/Witnesses.lean`
- `StampacchiaTruncation.lean`
- `Supersolutions/Caccioppoli.lean`
- `Supersolutions/ForwardIteration/Basics.lean`
- `Supersolutions/ForwardIteration/Energy.lean`
- `Supersolutions/InverseEnergy.lean`
- `Supersolutions/RegularizationSupport.lean`
- `Supersolutions/TestFunctions.lean`
- `Support/MeasureBounds.lean`
- `UnitBallApproximationCore/Profiles.lean`
- `UnitBallApproximationCore/Rescaling.lean`
- `WeakFormulation/ExistenceTheory.lean`
- `WeakHarnack.lean`

**Change**: addressed all Lean linter style warnings flagged by `lake build` under this directory. Changes are semantic-preserving and consist of:
- `show <goal>` rewritten to `change <goal>` at sites the linter flagged as goal-modifying;
- `simp [...]` rewritten to `simp only [...]` at sites flagged as flexible (lemma lists adjusted as needed to keep the next tactic step closing);
- `push_neg` replaced with `push Not`;
- isolated `·` bullets merged with the following line;
- `set_option maxHeartbeats N` and `set_option synthInstance.maxHeartbeats N` scoped via `... in` and given an inline comment describing the elaboration that needs the extended budget; a small number of declarations additionally use a narrow `set_option linter.style.setOption false in` so that the `... in`-scoped form is not itself flagged;
- one tactic call in `StampacchiaTruncation.lean` made unification-explicit (`(s := Ioo a b)`) to satisfy the "tactic operates on only one of multiple goals" linter.

<!-- Add entries below as modifications occur. -->
