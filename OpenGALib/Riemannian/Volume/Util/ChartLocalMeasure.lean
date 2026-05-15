import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import OpenGALib.Riemannian.Volume.Util.ChartSqrtGramDet

/-!
# Chart-local Riemannian volume measure

For a Riemannian metric `g` and a model-space basepoint `α : M`, the
**chart-local volume measure**

  `chartLocalMeasure g α : MeasureTheory.Measure M`

is constructed in three steps from `chartSqrtGramDet`:

1. Take the canonical additive Haar measure on `E` (induced by
   `Module.finBasis ℝ E`).
2. Restrict to the chart target `(extChartAt I α).target ⊆ E` and weight
   by the chart-pulled-back density
   `chartSqrtGramDet g α ((extChartAt I α).symm y)`.
3. Push the result forward along `(extChartAt I α).symm : E → M`.

The measure is mathematically meaningful only when restricted to
`(extChartAt I α).source ⊆ M` (off-source it takes junk values). Its
chart-invariance on overlaps — the input to the eventual
partition-of-unity glue — is the content of the upcoming B3 block.

Ground truth: do Carmo Ch.1 Eq.(5); Lee Ch.16; Federer §2.10. The
construction is the standard "pull back Lebesgue along chart, weight by
`√det g_ij`" recipe found in every textbook.
-/

noncomputable section


open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

/-! ## File-local Borel structures on `E` and `H`

`MeasurableSpace M` / `BorelSpace M` come from the consumer's variable
block so that the result type `Measure M` matches downstream. The
auxiliary `E` and `H` Borel structures are file-local since they appear
only inside the construction, not in the public result type. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace H := borel H
private local instance : BorelSpace H := ⟨rfl⟩

/-! ## The canonical Haar reference measure on `E` -/

/-- **Math.** Canonical additive Haar measure on the model space `E`,
induced by `Module.finBasis ℝ E`. Serves as the reference Lebesgue-style
measure on the chart target.

When `E = EuclideanSpace ℝ (Fin n)`, `modelHaar` agrees with the
standard `volume` on `E` (Mathlib's `MeasureSpace` instance is
`(stdOrthonormalBasis ℝ E).toBasis.addHaar`, of which our `modelHaar` is
a specialization to `Module.finBasis`). -/
noncomputable def modelHaar : MeasureTheory.Measure E :=
  (Module.finBasis ℝ E).addHaar

/-- **Eng.** Instance: `modelHaar` is an additive Haar measure
(inherits from `Basis.addHaar` via `isAddHaarMeasure_basis_addHaar`). -/
instance modelHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance

/-- **Eng.** Instance: `modelHaar` is sigma-finite (inherits from
`Basis.addHaar`). -/
instance modelHaar_sigmaFinite :
    MeasureTheory.SigmaFinite (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance

/-! ## The chart-local volume measure -/

/-- **Math.** The **chart-local Riemannian volume measure** at the
model-space basepoint `α : M`. Three-step construction:

  `chartLocalMeasure g α := (extChartAt I α).symm.map
      ((modelHaar.restrict (extChartAt I α).target).withDensity
        (ENNReal.ofReal ∘ chartSqrtGramDet g α ∘ (extChartAt I α).symm))`

i.e. pushforward through `(extChartAt I α).symm` of the `chartSqrtGramDet`-
weighted Lebesgue measure on the chart target. Mathematically meaningful
on `(extChartAt I α).source`; the partition-of-unity glue (Glue.lean
equivalent) sums these chart-local measures into the global `volumeMeasure`.

Ground truth: do Carmo Ch.1 Eq.(5); Lee Ch.16. -/
noncomputable def chartLocalMeasure
    (g : RiemannianMetric I M) (α : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I α).symm
    (((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y))))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BorelSpace M] in
/-- **Eng.** Unfolding lemma: definitional expansion of `chartLocalMeasure`. -/
lemma chartLocalMeasure_def
    (g : RiemannianMetric I M) (α : M) :
    chartLocalMeasure (I := I) g α =
      MeasureTheory.Measure.map (extChartAt I α).symm
        (((modelHaar (E := E)).restrict (extChartAt I α).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartSqrtGramDet (I := I) g α ((extChartAt I α).symm y)))) := rfl

end Riemannian.Tensor
