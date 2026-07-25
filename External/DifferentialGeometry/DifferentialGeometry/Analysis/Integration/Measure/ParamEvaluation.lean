import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.Geometry.Manifold.LocalDiffeomorph










noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩









def paramGramMatrix (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun w => Matrix.of fun i j =>
    g.inner (Ψ w)
      (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
      (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))






@[simp] lemma paramGramMatrix_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (w : E) (i j : Fin (Module.finrank ℝ E)) :
    paramGramMatrix (I := I) g Ψ w i j =
      g.inner (Ψ w)
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := rfl








def paramDensity (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) : E → ℝ :=
  fun w => Real.sqrt (paramGramMatrix (I := I) g Ψ w).det





@[simp] lemma paramDensity_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    (w : E) :
    paramDensity (I := I) g Ψ w =
      Real.sqrt (paramGramMatrix (I := I) g Ψ w).det := rfl








noncomputable def paramDerivEquiv
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    E ≃L[ℝ] TangentSpace I (Ψ w) :=
  (PartialDiffeomorph.isLocalDiffeomorphAt
    (I := 𝓘(ℝ, E)) (J := I) (n := 1) Ψ hw).mfderivToContinuousLinearEquiv
      (by norm_num)






omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma paramDeriv_ker
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    (mfderiv 𝓘(ℝ, E) I Ψ w).ker = ⊥ := by
  have hlocal :=
    PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(ℝ, E)) (J := I) (n := 1) Ψ hw
  apply LinearMap.ker_eq_bot.mpr
  intro v hv
  apply (hlocal.mfderivToContinuousLinearEquiv (by norm_num)).injective







def paramChartMap (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) : E → E :=
  fun w => extChartAt I x₀ (Ψ w)






def paramJacobianMatrix (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
    (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).toLinearMap






omit [IsManifold I ∞ M] in
@[simp] lemma paramJacobianMatrix_apply
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E)
    (k i : Fin (Module.finrank ℝ E)) :
    paramJacobianMatrix (I := I) x₀ Ψ w k i =
      (chartModelBasis E).repr
        ((fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w)
          ((chartModelBasis E) i)) k := by
  simp [paramJacobianMatrix, LinearMap.toMatrix_apply]








lemma paramDeriv_chartBasis_eq_sum
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i) =
      ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
        chartBasisVecFiber (I := I) x₀ k (Ψ w) := by
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using hx
  have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxchart
  have hΨdiff : MDifferentiableAt 𝓘(ℝ, E) I Ψ w :=
    (Ψ.contMDiffOn_toFun.mdifferentiableOn one_ne_zero w hw).mdifferentiableAt
      (Ψ.open_source.mem_nhds hw)
  have hchartdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w) :=
    mdifferentiableAt_extChartAt (I := I) (x := x₀) (y := Ψ w) hxchart
  have hchain :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (paramChartMap (I := I) x₀ Ψ) w =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w)).comp
          (mfderiv 𝓘(ℝ, E) I Ψ w) := by
    simpa [paramChartMap, Function.comp_def] using
      (mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
        (g := extChartAt I x₀) (f := Ψ) (x := w) hchartdiff hΨdiff)
  have hchain_f :
      fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w)).comp
          (mfderiv 𝓘(ℝ, E) I Ψ w) := by
    simpa [mfderiv_eq_fderiv] using hchain
  set T₀ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₀
  apply (T₀.continuousLinearEquivAt ℝ (Ψ w) hx).injective
  have hrepr :
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) ((chartModelBasis E) i) =
        ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
          (chartModelBasis E) k := by
    simpa [paramJacobianMatrix_apply] using
      (((chartModelBasis E).sum_repr
        ((fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w)
          ((chartModelBasis E) i))).symm)
  calc
    T₀.continuousLinearEquivAt ℝ (Ψ w) hx
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
        = (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) ((chartModelBasis E) i) := by
          rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) T₀ hx]
          rw [TangentBundle.continuousLinearMapAt_trivializationAt
            (I := I) (x₀ := x₀) (x := Ψ w) hxchart]
          rw [hchain_f]
          rfl
    _ = ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
          (chartModelBasis E) k := hrepr
    _ = T₀.continuousLinearEquivAt ℝ (Ψ w) hx
          (∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
            chartBasisVecFiber (I := I) x₀ k (Ψ w)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [map_smul]
          have hbasis :
              chartBasisVecFiber (I := I) x₀ k (Ψ w) =
                (T₀.continuousLinearEquivAt ℝ (Ψ w) hx).symm
                  ((chartModelBasis E) k) := by
            change T₀.symm (Ψ w) ((chartModelBasis E) k) =
              (T₀.continuousLinearEquivAt ℝ (Ψ w) hx).symm ((chartModelBasis E) k)
            rfl
          rw [hbasis]
          rw [ContinuousLinearEquiv.apply_symm_apply]








lemma paramGramMatrix_pullback_eq_sum
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    paramGramMatrix (I := I) g Ψ w i j =
      ∑ k, ∑ l,
        paramJacobianMatrix (I := I) x₀ Ψ w k i *
        paramJacobianMatrix (I := I) x₀ Ψ w l j *
        chartGramMatrix g x₀ (Ψ w) k l := by
  rw [paramGramMatrix_apply]
  rw [paramDeriv_chartBasis_eq_sum (I := I) x₀ Ψ hw hx i]
  rw [paramDeriv_chartBasis_eq_sum (I := I) x₀ Ψ hw hx j]
  have hL :
      g.inner (Ψ w)
          (∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
            chartBasisVecFiber (I := I) x₀ k (Ψ w))
        = ∑ k, paramJacobianMatrix (I := I) x₀ Ψ w k i •
            g.inner (Ψ w) (chartBasisVecFiber (I := I) x₀ k (Ψ w)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply]
  have hR :
      g.inner (Ψ w) (chartBasisVecFiber (I := I) x₀ k (Ψ w))
          (∑ l, paramJacobianMatrix (I := I) x₀ Ψ w l j •
            chartBasisVecFiber (I := I) x₀ l (Ψ w))
        = ∑ l, paramJacobianMatrix (I := I) x₀ Ψ w l j *
            g.inner (Ψ w) (chartBasisVecFiber (I := I) x₀ k (Ψ w))
              (chartBasisVecFiber (I := I) x₀ l (Ψ w)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
    rw [smul_eq_mul]
  rw [hR, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartGramMatrix_apply]
  ring







theorem paramGramMatrix_pullback_eq_mul
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    paramGramMatrix (I := I) g Ψ w =
      (paramJacobianMatrix (I := I) x₀ Ψ w)ᵀ *
        chartGramMatrix g x₀ (Ψ w) *
        paramJacobianMatrix (I := I) x₀ Ψ w := by
  ext i j
  rw [paramGramMatrix_pullback_eq_sum (I := I) g x₀ Ψ hw hx i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring







omit [IsManifold I ∞ M] in
lemma paramJacobianMatrix_det
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E) :
    (paramJacobianMatrix (I := I) x₀ Ψ w).det =
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det := by
  unfold paramJacobianMatrix
  rw [LinearMap.det_toMatrix]







lemma paramGramMatrix_det_pullback
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (paramGramMatrix (I := I) g Ψ w).det =
      ((fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det) ^ 2 *
        (chartGramMatrix g x₀ (Ψ w)).det := by
  rw [paramGramMatrix_pullback_eq_mul (I := I) g x₀ Ψ hw hx]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [paramJacobianMatrix_det (I := I) x₀ Ψ w]
  ring







theorem paramDensity_eq_abs_det_mul_chartDensity
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    paramDensity (I := I) g Ψ w =
      |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
        chartDensity g x₀ (Ψ w) := by
  unfold paramDensity chartDensity
  rw [paramGramMatrix_det_pullback (I := I) g x₀ Ψ hw hx]
  rw [Real.sqrt_mul (sq_nonneg _)]
  rw [Real.sqrt_sq_eq_abs]






omit [FiniteDimensional ℝ E] in
lemma paramChartMap_contDiffOn
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContDiffOn ℝ 1 (paramChartMap (I := I) x₀ Ψ) s := by
  have hΨ : ContMDiffOn 𝓘(ℝ, E) I 1 Ψ s :=
    Ψ.contMDiffOn_toFun.mono hs_source
  have hchart : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I x₀) (chartAt H x₀).source :=
    contMDiffOn_extChartAt (I := I) (x := x₀) (n := 1)
  have hmaps : s ⊆ Ψ ⁻¹' (chartAt H x₀).source := by
    intro w hw
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
      hs_chart w hw
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (extChartAt I x₀ ∘ Ψ) s :=
    hchart.comp hΨ hmaps
  exact contMDiffOn_iff_contDiffOn.mp
    (by simpa [paramChartMap, Function.comp_def] using hcomp)







lemma paramDensity_continuousOn_chart
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_open : IsOpen s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContinuousOn (paramDensity (I := I) g Ψ) s := by
  have hT : ContDiffOn ℝ 1 (paramChartMap (I := I) x₀ Ψ) s :=
    paramChartMap_contDiffOn (I := I) x₀ Ψ hs_source hs_chart
  have hfderiv : ContinuousOn (fun w => fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s :=
    hT.continuousOn_fderiv_of_isOpen hs_open le_rfl
  have hdet : ContinuousOn
      (fun w => |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det|) s :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn hfderiv).abs
  have hΨcont : ContinuousOn Ψ s :=
    (Ψ.contMDiffOn_toFun.mono hs_source).continuousOn
  have hchartDensity : ContinuousOn (fun w => chartDensity g x₀ (Ψ w)) s :=
    (chartDensity_continuousOn (I := I) g x₀).comp hΨcont hs_chart
  have hR : ContinuousOn
      (fun w => |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
        chartDensity g x₀ (Ψ w)) s :=
    hdet.mul hchartDensity
  exact hR.congr (fun w hw =>
    paramDensity_eq_abs_det_mul_chartDensity (I := I) g x₀ Ψ
      (hs_source hw) (hs_chart w hw))


lemma aemeasurable_ofReal_paramDensity_on_chart
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s) (hs_open : IsOpen s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    AEMeasurable (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w))
      ((modelHaar (E := E)).restrict s) := by
  have hcont : ContinuousOn (paramDensity (I := I) g Ψ) s :=
    paramDensity_continuousOn_chart (I := I) g x₀ Ψ hs_open hs_source hs_chart
  exact ENNReal.measurable_ofReal.comp_aemeasurable (hcont.aemeasurable hs_meas)







omit [FiniteDimensional ℝ E] in
lemma paramChartMap_hasFDerivWithinAt
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} {w : E} (hw : w ∈ Ψ.source)
    (hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using hx
  have hΨdiff : MDifferentiableAt 𝓘(ℝ, E) I Ψ w :=
    (Ψ.contMDiffOn_toFun.mdifferentiableOn one_ne_zero w hw).mdifferentiableAt
      (Ψ.open_source.mem_nhds hw)
  have hchartdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) (Ψ w) :=
    mdifferentiableAt_extChartAt (I := I) (x := x₀) (y := Ψ w) hxchart
  have hTdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (paramChartMap (I := I) x₀ Ψ) w := by
    simpa [paramChartMap, Function.comp_def] using hchartdiff.comp w hΨdiff
  exact hTdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt







omit [FiniteDimensional ℝ E] in
lemma paramChartMap_injOn
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Set.InjOn (paramChartMap (I := I) x₀ Ψ) s := by
  intro u hu v hv huv
  have hu_chart : Ψ u ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using
      hs_chart u hu
  have hv_chart : Ψ v ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using
      hs_chart v hv
  have hu_ext : Ψ u ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hu_chart
  have hv_ext : Ψ v ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hv_chart
  have hΨuv : Ψ u = Ψ v :=
    (extChartAt I x₀).injOn hu_ext hv_ext huv
  exact Ψ.toPartialEquiv.injOn (hs_source hu) (hs_source hv) hΨuv







lemma measurableSet_image_paramChartMap
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MeasurableSet ((paramChartMap (I := I) x₀ Ψ) '' s) := by
  have hf' : ∀ w ∈ s, HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
    intro w hw
    exact paramChartMap_hasFDerivWithinAt (I := I) x₀ Ψ
      (hs_source hw) (hs_chart w hw)
  exact MeasureTheory.measurable_image_of_fderivWithin hs_meas hf'
    (paramChartMap_injOn (I := I) x₀ Ψ hs_source hs_chart)







lemma measurableSet_image_param
    [T2Space M]
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MeasurableSet (Ψ '' s) := by
  set V : Set E := (paramChartMap (I := I) x₀ Ψ) '' s with hV_def
  have hV_meas : MeasurableSet V := by
    rw [hV_def]
    exact measurableSet_image_paramChartMap (I := I) x₀ Ψ hs_meas hs_source hs_chart
  have hV_target : V ⊆ (extChartAt I x₀).target := by
    rw [hV_def]
    rintro y ⟨w, hw, rfl⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    exact (extChartAt I x₀).map_source hxsrc
  have hsymm_cont : ContinuousOn (extChartAt I x₀).symm V :=
    (continuousOn_extChartAt_symm (I := I) x₀).mono hV_target
  have hsymm_inj : Set.InjOn (extChartAt I x₀).symm V := by
    intro y hy z hz hyz
    rw [← (extChartAt I x₀).right_inv (hV_target hy), hyz,
      (extChartAt I x₀).right_inv (hV_target hz)]
  have hsymm_image :
      MeasurableSet ((extChartAt I x₀).symm '' V) :=
    hV_meas.image_of_continuousOn_injOn hsymm_cont hsymm_inj
  convert hsymm_image using 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨paramChartMap (I := I) x₀ Ψ w, ?_, ?_⟩
    · rw [hV_def]
      exact ⟨w, hw, rfl⟩
    · have hxchart : Ψ w ∈ (chartAt H x₀).source := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
          hs_chart w hw
      have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact hxchart
      simpa [paramChartMap] using (extChartAt I x₀).left_inv hxsrc
  · rintro ⟨y, hyV, rfl⟩
    rw [hV_def] at hyV
    rcases hyV with ⟨w, hw, rfl⟩
    refine ⟨w, hw, ?_⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    simpa [paramChartMap] using ((extChartAt I x₀).left_inv hxsrc).symm







omit [IsManifold I ∞ M] in
lemma measurableSet_image_param_global
    [T2Space M]
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    MeasurableSet (Ψ '' s) := by
  have hcont : ContinuousOn Ψ s :=
    (Ψ.contMDiffOn_toFun.mono hs_source).continuousOn
  have hinj : Set.InjOn Ψ s := by
    intro u hu v hv huv
    exact Ψ.toPartialEquiv.injOn (hs_source hu) (hs_source hv) huv
  exact hs_meas.image_of_continuousOn_injOn hcont hinj







omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma measurableSet_symm_image_param
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_target : A ⊆ Ψ.target) :
    MeasurableSet (Ψ.symm '' A) := by
  have hsrc_meas : MeasurableSet Ψ.source := Ψ.open_source.measurableSet
  have hcont : Continuous (fun w : Ψ.source => Ψ (w : E)) :=
    continuousOn_iff_continuous_restrict.mp Ψ.contMDiffOn_toFun.continuousOn
  have hpre_sub :
      MeasurableSet {w : Ψ.source | Ψ (w : E) ∈ A} :=
    hcont.measurable hA_meas
  have hpre :
      MeasurableSet (Ψ.source ∩ Ψ ⁻¹' A) := by
    convert hsrc_meas.subtype_image hpre_sub using 1
    ext w
    constructor
    · rintro ⟨hwsrc, hwA⟩
      exact ⟨⟨w, hwsrc⟩, hwA, rfl⟩
    · rintro ⟨w', hwA, hw_eq⟩
      rw [← hw_eq]
      exact ⟨w'.2, hwA⟩
  convert hpre using 1
  ext w
  constructor
  · rintro ⟨x, hxA, rfl⟩
    exact ⟨Ψ.toPartialEquiv.map_target (hA_target hxA), by
      change Ψ.toPartialEquiv (Ψ.toPartialEquiv.symm x) ∈ A
      rw [Ψ.toPartialEquiv.right_inv (hA_target hxA)]
      exact hxA⟩
  · rintro ⟨hwsrc, hwA⟩
    exact ⟨Ψ w, hwA, by
      change Ψ.toPartialEquiv.symm (Ψ.toPartialEquiv w) = w
      exact Ψ.toPartialEquiv.left_inv hwsrc⟩






omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma measurableSet_param_chartPiece
    (x₀ : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    MeasurableSet (s ∩ Ψ ⁻¹' (chartAt H x₀).source) := by
  have hΨcont : ContinuousOn Ψ Ψ.source :=
    Ψ.contMDiffOn_toFun.continuousOn
  have hopen : IsOpen (Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source) :=
    hΨcont.isOpen_inter_preimage Ψ.open_source (chartAt H x₀).open_source
  have heq :
      s ∩ Ψ ⁻¹' (chartAt H x₀).source =
        s ∩ (Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source) := by
    ext w
    constructor
    · rintro ⟨hw, hchart⟩
      exact ⟨hw, hs_source hw, hchart⟩
    · rintro ⟨hw, _, hchart⟩
      exact ⟨hw, hchart⟩
  rw [heq]
  exact hs_meas.inter hopen.measurableSet








lemma aemeasurable_ofReal_paramDensity_on_chartPiece
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w))
      ((modelHaar (E := E)).restrict (s ∩ Ψ ⁻¹' (chartAt H x₀).source)) := by
  set U : Set E := Ψ.source ∩ Ψ ⁻¹' (chartAt H x₀).source with hU_def
  have hΨcont : ContinuousOn Ψ Ψ.source :=
    Ψ.contMDiffOn_toFun.continuousOn
  have hUopen : IsOpen U := by
    rw [hU_def]
    exact hΨcont.isOpen_inter_preimage Ψ.open_source (chartAt H x₀).open_source
  have hU_source : U ⊆ Ψ.source := by
    rw [hU_def]
    exact Set.inter_subset_left
  have hU_chart :
      ∀ w ∈ U, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro w hw
    rw [hU_def] at hw
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hw.2
  have hcontU : ContinuousOn (paramDensity (I := I) g Ψ) U :=
    paramDensity_continuousOn_chart (I := I) g x₀ Ψ hUopen hU_source hU_chart
  have hpiece_meas : MeasurableSet (s ∩ Ψ ⁻¹' (chartAt H x₀).source) :=
    measurableSet_param_chartPiece (I := I) x₀ Ψ hs_meas hs_source
  have hpiece_sub : s ∩ Ψ ⁻¹' (chartAt H x₀).source ⊆ U := by
    intro w hw
    rw [hU_def]
    exact ⟨hs_source hw.1, hw.2⟩
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    ((hcontU.mono hpiece_sub).aemeasurable hpiece_meas)



omit [IsManifold I ∞ M] in
lemma aemeasurable_ofReal_pou_param_on_chartPiece
    (ρ : SmoothPartitionOfUnity M I M univ) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable (fun w => ENNReal.ofReal (ρ x₀ (Ψ w)))
      ((modelHaar (E := E)).restrict (s ∩ Ψ ⁻¹' (chartAt H x₀).source)) := by
  set S : Set E := s ∩ Ψ ⁻¹' (chartAt H x₀).source with hS_def
  have hS_meas : MeasurableSet S := by
    rw [hS_def]
    exact measurableSet_param_chartPiece (I := I) x₀ Ψ hs_meas hs_source
  have hΨcont_source : ContinuousOn Ψ Ψ.source :=
    Ψ.contMDiffOn_toFun.continuousOn
  have hS_sub_source : S ⊆ Ψ.source := by
    rw [hS_def]
    exact fun w hw => hs_source hw.1
  have hΨ_aem : AEMeasurable Ψ ((modelHaar (E := E)).restrict S) :=
    (hΨcont_source.mono hS_sub_source).aemeasurable hS_meas
  exact (measurable_ofReal_pou_weight (I := I) ρ x₀).comp_aemeasurable hΨ_aem



lemma aemeasurable_paramDensity_mul_pou_on_chartPiece
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable
      (fun w =>
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ x₀ (Ψ w)))
      ((modelHaar (E := E)).restrict (s ∩ Ψ ⁻¹' (chartAt H x₀).source)) := by
  exact (aemeasurable_ofReal_paramDensity_on_chartPiece (I := I) g x₀ Ψ
    hs_meas hs_source).mul
    (aemeasurable_ofReal_pou_param_on_chartPiece (I := I) ρ x₀ Ψ
      hs_meas hs_source)



lemma aemeasurable_paramDensity_mul_pou_indicator_chartPiece
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source) :
    AEMeasurable
      ((s ∩ Ψ ⁻¹' (chartAt H x₀).source).indicator
        (fun w =>
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ x₀ (Ψ w))))
      (modelHaar (E := E)) := by
  have hS_meas : MeasurableSet (s ∩ Ψ ⁻¹' (chartAt H x₀).source) :=
    measurableSet_param_chartPiece (I := I) x₀ Ψ hs_meas hs_source
  exact (aemeasurable_indicator_iff hS_meas).mpr
    (aemeasurable_paramDensity_mul_pou_on_chartPiece (I := I) g ρ x₀ Ψ
      hs_meas hs_source)



omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma pou_weight_eq_zero_of_notMem_chart
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    {α x : M} (hx : x ∉ (chartAt H α).source) :
    ρ α x = 0 := by
  by_contra hne
  exact hx (hρ α (subset_tsupport _ hne))









theorem lintegral_image_paramChartMap_chartDensity_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∫⁻ y in (paramChartMap (I := I) x₀ Ψ) '' s,
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))
        ∂(modelHaar (E := E)) =
      ∫⁻ w in s, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  have hf' : ∀ w ∈ s, HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
    intro w hw
    exact paramChartMap_hasFDerivWithinAt (I := I) x₀ Ψ
      (hs_source hw) (hs_chart w hw)
  have hinj : Set.InjOn (paramChartMap (I := I) x₀ Ψ) s :=
    paramChartMap_injOn (I := I) x₀ Ψ hs_source hs_chart
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := modelHaar (E := E)) hs_meas hf' hinj
    (g := fun y : E =>
      ENNReal.ofReal
        (chartDensity g x₀ ((extChartAt I x₀).symm y)))]
  refine MeasureTheory.setLIntegral_congr_fun hs_meas ?_
  intro w hw
  have hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    hs_chart w hw
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I) x₀] using hx
  have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxchart
  have hsymm :
      (extChartAt I x₀).symm (paramChartMap (I := I) x₀ Ψ w) = Ψ w := by
    simpa [paramChartMap] using (extChartAt I x₀).left_inv hxsrc
  change ENNReal.ofReal |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
      ENNReal.ofReal
        (chartDensity g x₀ ((extChartAt I x₀).symm
          (paramChartMap (I := I) x₀ Ψ w))) =
    ENNReal.ofReal (paramDensity (I := I) g Ψ w)
  rw [hsymm]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [← paramDensity_eq_abs_det_mul_chartDensity (I := I) g x₀ Ψ (hs_source hw) hx]






theorem lintegral_image_paramChartMap_mul_chartDensity_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (F : M → ℝ≥0∞) :
    ∫⁻ y in (paramChartMap (I := I) x₀ Ψ) '' s,
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          F ((extChartAt I x₀).symm y)
        ∂(modelHaar (E := E)) =
      ∫⁻ w in s,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) * F (Ψ w)
        ∂(modelHaar (E := E)) := by
  have hf' : ∀ w ∈ s, HasFDerivWithinAt (paramChartMap (I := I) x₀ Ψ)
      (fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w) s w := by
    intro w hw
    exact paramChartMap_hasFDerivWithinAt (I := I) x₀ Ψ
      (hs_source hw) (hs_chart w hw)
  have hinj : Set.InjOn (paramChartMap (I := I) x₀ Ψ) s :=
    paramChartMap_injOn (I := I) x₀ Ψ hs_source hs_chart
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := modelHaar (E := E)) hs_meas hf' hinj
    (g := fun y : E =>
      ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
        F ((extChartAt I x₀).symm y))]
  refine MeasureTheory.setLIntegral_congr_fun hs_meas ?_
  intro w hw
  have hx : Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    hs_chart w hw
  have hxchart : Ψ w ∈ (chartAt H x₀).source := by
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hx
  have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxchart
  have hsymm :
      (extChartAt I x₀).symm (paramChartMap (I := I) x₀ Ψ w) = Ψ w := by
    simpa [paramChartMap] using (extChartAt I x₀).left_inv hxsrc
  change ENNReal.ofReal |(fderiv ℝ (paramChartMap (I := I) x₀ Ψ) w).det| *
      (ENNReal.ofReal
        (chartDensity g x₀ ((extChartAt I x₀).symm
          (paramChartMap (I := I) x₀ Ψ w))) *
        F ((extChartAt I x₀).symm (paramChartMap (I := I) x₀ Ψ w))) =
    ENNReal.ofReal (paramDensity (I := I) g Ψ w) * F (Ψ w)
  rw [hsymm]
  rw [← mul_assoc]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [← paramDensity_eq_abs_det_mul_chartDensity (I := I) g x₀ Ψ (hs_source hw) hx]










theorem chartLocalMeasure_image_param_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (himage_meas : MeasurableSet (Ψ '' s)) :
    chartLocalMeasure (I := I) g x₀ (Ψ '' s) =
      ∫⁻ w in s, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  rw [← MeasureTheory.setLIntegral_one
    (μ := chartLocalMeasure (I := I) g x₀) (s := Ψ '' s)]
  rw [chartLocalMeasure_setLintegral_indicator (I := I) g x₀ himage_meas
    (measurable_const : Measurable (fun _ : M => (1 : ℝ≥0∞)))]
  set V : Set E := (paramChartMap (I := I) x₀ Ψ) '' s with hV_def
  have hV_meas : MeasurableSet V := by
    rw [hV_def]
    exact measurableSet_image_paramChartMap (I := I) x₀ Ψ hs_meas hs_source hs_chart
  have hV_target : V ⊆ (extChartAt I x₀).target := by
    rw [hV_def]
    rintro y ⟨w, hw, rfl⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    exact (extChartAt I x₀).map_source hxsrc
  have hmem : ∀ y ∈ (extChartAt I x₀).target,
      (extChartAt I x₀).symm y ∈ Ψ '' s ↔ y ∈ V := by
    intro y hy
    constructor
    · rintro ⟨w, hw, hw_eq⟩
      refine ⟨w, hw, ?_⟩
      rw [paramChartMap, hw_eq, (extChartAt I x₀).right_inv hy]
    · rw [hV_def]
      rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      have hxchart : Ψ w ∈ (chartAt H x₀).source := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
          hs_chart w hw
      have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact hxchart
      simpa [paramChartMap] using ((extChartAt I x₀).left_inv hxsrc).symm
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hpt : ∀ y ∈ (extChartAt I x₀).target,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          (Ψ '' s).indicator (fun _ : M => (1 : ℝ≥0∞))
            ((extChartAt I x₀).symm y) =
        V.indicator
          (fun y : E =>
            ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))) y := by
    intro y hy
    by_cases hyV : y ∈ V
    · have hyU : (extChartAt I x₀).symm y ∈ Ψ '' s := (hmem y hy).2 hyV
      rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hyV, mul_one]
    · have hyU : (extChartAt I x₀).symm y ∉ Ψ '' s := by
        intro hU
        exact hyV ((hmem y hy).1 hU)
      rw [Set.indicator_of_notMem hyU, Set.indicator_of_notMem hyV, mul_zero]
  rw [MeasureTheory.setLIntegral_congr_fun htarget_meas hpt]
  rw [MeasureTheory.setLIntegral_indicator hV_meas]
  rw [show V ∩ (extChartAt I x₀).target = V from by
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      exact ⟨hy, hV_target hy⟩]
  rw [hV_def]
  exact lintegral_image_paramChartMap_chartDensity_eq (I := I) g x₀ Ψ
    hs_meas hs_source hs_chart




theorem chartLocalMeasure_image_param_eq_t2
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    chartLocalMeasure (I := I) g x₀ (Ψ '' s) =
      ∫⁻ w in s, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) :=
  chartLocalMeasure_image_param_eq (I := I) g x₀ Ψ hs_meas hs_source hs_chart
    (measurableSet_image_param (I := I) x₀ Ψ hs_meas hs_source hs_chart)





theorem chartLocalMeasure_lintegral_image_param_eq_t2
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {s : Set E} (hs_meas : MeasurableSet s)
    (hs_source : s ⊆ Ψ.source)
    (hs_chart : ∀ w ∈ s, Ψ w ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Ψ '' s, F x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫⁻ w in s,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) * F (Ψ w)
        ∂(modelHaar (E := E)) := by
  have himage_meas : MeasurableSet (Ψ '' s) :=
    measurableSet_image_param (I := I) x₀ Ψ hs_meas hs_source hs_chart
  rw [chartLocalMeasure_setLintegral_indicator (I := I) g x₀ himage_meas hF]
  set V : Set E := (paramChartMap (I := I) x₀ Ψ) '' s with hV_def
  have hV_meas : MeasurableSet V := by
    rw [hV_def]
    exact measurableSet_image_paramChartMap (I := I) x₀ Ψ hs_meas hs_source hs_chart
  have hV_target : V ⊆ (extChartAt I x₀).target := by
    rw [hV_def]
    rintro y ⟨w, hw, rfl⟩
    have hxchart : Ψ w ∈ (chartAt H x₀).source := by
      simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
        hs_chart w hw
    have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hxchart
    exact (extChartAt I x₀).map_source hxsrc
  have hmem : ∀ y ∈ (extChartAt I x₀).target,
      (extChartAt I x₀).symm y ∈ Ψ '' s ↔ y ∈ V := by
    intro y hy
    constructor
    · rintro ⟨w, hw, hw_eq⟩
      refine ⟨w, hw, ?_⟩
      rw [paramChartMap, hw_eq, (extChartAt I x₀).right_inv hy]
    · rw [hV_def]
      rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      have hxchart : Ψ w ∈ (chartAt H x₀).source := by
        simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using
          hs_chart w hw
      have hxsrc : Ψ w ∈ (extChartAt I x₀).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact hxchart
      simpa [paramChartMap] using ((extChartAt I x₀).left_inv hxsrc).symm
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  have hpt : ∀ y ∈ (extChartAt I x₀).target,
      ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
          (Ψ '' s).indicator F ((extChartAt I x₀).symm y) =
        V.indicator
          (fun y : E =>
            ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) *
              F ((extChartAt I x₀).symm y)) y := by
    intro y hy
    by_cases hyV : y ∈ V
    · have hyU : (extChartAt I x₀).symm y ∈ Ψ '' s := (hmem y hy).2 hyV
      rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hyV]
    · have hyU : (extChartAt I x₀).symm y ∉ Ψ '' s := by
        intro hU
        exact hyV ((hmem y hy).1 hU)
      rw [Set.indicator_of_notMem hyU, Set.indicator_of_notMem hyV, mul_zero]
  rw [MeasureTheory.setLIntegral_congr_fun htarget_meas hpt]
  rw [MeasureTheory.setLIntegral_indicator hV_meas]
  rw [show V ∩ (extChartAt I x₀).target = V from by
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      exact ⟨hy, hV_target hy⟩]
  rw [hV_def]
  exact lintegral_image_paramChartMap_mul_chartDensity_eq (I := I) g x₀ Ψ
    hs_meas hs_source hs_chart F








theorem riemannianMeasure_param_summand_eq
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source) :
    ∫⁻ x, ENNReal.ofReal (ρ α x) *
        (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
        ∂(chartLocalMeasure (I := I) g α) =
      ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
  set S : Set E := B ∩ Ψ ⁻¹' (chartAt H α).source with hS_def
  have hS_meas : MeasurableSet S := by
    rw [hS_def]
    exact measurableSet_param_chartPiece (I := I) α Ψ hB_meas hB_source
  have hS_source : S ⊆ Ψ.source := by
    rw [hS_def]
    exact fun w hw => hB_source hw.1
  have hS_chart :
      ∀ w ∈ S, Ψ w ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro w hw
    rw [hS_def] at hw
    simpa [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hw.2
  have hS_image_meas : MeasurableSet (Ψ '' S) :=
    measurableSet_image_param (I := I) α Ψ hS_meas hS_source hS_chart
  have hF_meas : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) :=
    measurable_ofReal_pou_weight (I := I) ρ α
  have hpoint : ∀ x : M,
      ENNReal.ofReal (ρ α x) *
          (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x =
        (Ψ '' S).indicator (fun x : M => ENNReal.ofReal (ρ α x)) x := by
    intro x
    by_cases hxS : x ∈ Ψ '' S
    · have hxB : x ∈ Ψ '' B := by
        rcases hxS with ⟨w, hwS, rfl⟩
        rw [hS_def] at hwS
        exact ⟨w, hwS.1, rfl⟩
      rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxS, mul_one]
    · by_cases hxB : x ∈ Ψ '' B
      · have hx_not_chart : x ∉ (chartAt H α).source := by
          intro hxchart
          rcases hxB with ⟨w, hwB, rfl⟩
          exact hxS ⟨w, by
            rw [hS_def]
            exact ⟨hwB, hxchart⟩, rfl⟩
        have hρx : ρ α x = 0 :=
          pou_weight_eq_zero_of_notMem_chart (I := I) ρ hρ hx_not_chart
        rw [Set.indicator_of_mem hxB, Set.indicator_of_notMem hxS, hρx,
          ENNReal.ofReal_zero, zero_mul]
      · rw [Set.indicator_of_notMem hxB, Set.indicator_of_notMem hxS, mul_zero]
  calc
    ∫⁻ x, ENNReal.ofReal (ρ α x) *
        (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
        ∂(chartLocalMeasure (I := I) g α)
        = ∫⁻ x, (Ψ '' S).indicator
            (fun x : M => ENNReal.ofReal (ρ α x)) x
            ∂(chartLocalMeasure (I := I) g α) := by
          exact MeasureTheory.lintegral_congr hpoint
    _ = ∫⁻ x in Ψ '' S, ENNReal.ofReal (ρ α x)
        ∂(chartLocalMeasure (I := I) g α) := by
          rw [MeasureTheory.lintegral_indicator hS_image_meas]
    _ = ∫⁻ w in S,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
          exact chartLocalMeasure_lintegral_image_param_eq_t2
            (I := I) g α Ψ hS_meas hS_source hS_chart hF_meas
    _ = ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
          rw [hS_def]



lemma param_pou_piece_zero
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M)
    (hα : Function.support (ρ α) = ∅)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} :
    ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) = 0 := by
  have hzero : ∀ w : E, ρ α (Ψ w) = 0 := by
    intro w
    by_contra hne
    have hx : Ψ w ∈ Function.support (ρ α) := hne
    rw [hα] at hx
    exact (Set.notMem_empty _) hx
  simp [hzero]



lemma tsum_param_pou_piece_eq_subtype
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} :
    (∑' α : M, ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
        ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
          ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E))) =
      ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α.val).source,
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α.val (Ψ w)) ∂(modelHaar (E := E)) := by
  classical
  refine tsum_subtype_eq_of_support_subset
    (s := {α : M | (Function.support (ρ α)).Nonempty}) ?_
  intro α hα
  simp only [Set.mem_setOf_eq]
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  exact hα (param_pou_piece_zero (I := I) g ρ α hne Ψ)


lemma tsum_param_pou_piece_indicator_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (w : E) :
    (∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
          (fun w =>
            ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
              ENNReal.ofReal (ρ α.val (Ψ w))) w) =
      B.indicator
        (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w)) w := by
  classical
  by_cases hwB : w ∈ B
  · rw [Set.indicator_of_mem hwB]
    have hterm :
        (fun α : {α : M | (Function.support (ρ α)).Nonempty} =>
          (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
            (fun w =>
              ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
                ENNReal.ofReal (ρ α.val (Ψ w))) w)
          =
        fun α : {α : M | (Function.support (ρ α)).Nonempty} =>
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α.val (Ψ w)) := by
      funext α
      by_cases hxchart : Ψ w ∈ (chartAt H α.val).source
      · have hmem : w ∈ B ∩ Ψ ⁻¹' (chartAt H α.val).source := ⟨hwB, hxchart⟩
        rw [Set.indicator_of_mem hmem]
      · have hmem : w ∉ B ∩ Ψ ⁻¹' (chartAt H α.val).source := by
          intro hw
          exact hxchart hw.2
        have hρw : ρ α.val (Ψ w) = 0 :=
          pou_weight_eq_zero_of_notMem_chart (I := I) ρ hρ hxchart
        rw [Set.indicator_of_notMem hmem, hρw, ENNReal.ofReal_zero, mul_zero]
    rw [hterm, ENNReal.tsum_mul_left]
    have hfull :
        (∑' α : {α : M | (Function.support (ρ α)).Nonempty},
            ENNReal.ofReal (ρ α.val (Ψ w))) =
          ∑' α : M, ENNReal.ofReal (ρ α (Ψ w)) := by
      symm
      refine tsum_subtype_eq_of_support_subset
        (s := {α : M | (Function.support (ρ α)).Nonempty})
        (f := fun α => ENNReal.ofReal (ρ α (Ψ w))) ?_
      intro α hα
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hα
      refine Set.nonempty_iff_ne_empty.mpr ?_
      intro h_empty
      have : ρ α (Ψ w) = 0 := by
        by_contra hne
        have hx : Ψ w ∈ Function.support (ρ α) := hne
        rw [h_empty] at hx
        exact (Set.notMem_empty _) hx
      linarith
    rw [hfull, tsum_ofReal_pou_eq_one (I := I) ρ (Ψ w), mul_one]
  · rw [Set.indicator_of_notMem hwB]
    refine (ENNReal.tsum_eq_zero).mpr ?_
    intro α
    have hmem : w ∉ B ∩ Ψ ⁻¹' (chartAt H α.val).source := by
      intro hw
      exact hwB hw.1
    rw [Set.indicator_of_notMem hmem]




theorem riemannianMeasure_image_param_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source) :
    riemannianMeasure (I := I) g ρ (Ψ '' B) =
      ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  classical
  have hB_image_meas : MeasurableSet (Ψ '' B) :=
    measurableSet_image_param_global (I := I) Ψ hB_meas hB_source
  have hInd_meas :
      Measurable ((Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞))) :=
    (measurable_const).indicator hB_image_meas
  calc
    riemannianMeasure (I := I) g ρ (Ψ '' B)
        = ∫⁻ x, (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
            ∂(riemannianMeasure (I := I) g ρ) := by
          simpa using
            (MeasureTheory.lintegral_indicator_one
              (μ := riemannianMeasure (I := I) g ρ) hB_image_meas).symm
    _ = ∑' α : M, ∫⁻ x,
          ENNReal.ofReal (ρ α x) *
            (Ψ '' B).indicator (fun _ : M => (1 : ℝ≥0∞)) x
          ∂(chartLocalMeasure (I := I) g α) := by
          rw [riemannianMeasure_lintegral_eq (I := I) g ρ hInd_meas]
    _ = ∑' α : M, ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α).source,
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α (Ψ w)) ∂(modelHaar (E := E)) := by
          refine tsum_congr (fun α => ?_)
          exact riemannianMeasure_param_summand_eq (I := I) g ρ hρ α Ψ
            hB_meas hB_source
    _ = ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ w in B ∩ Ψ ⁻¹' (chartAt H α.val).source,
          ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
            ENNReal.ofReal (ρ α.val (Ψ w)) ∂(modelHaar (E := E)) := by
          exact tsum_param_pou_piece_eq_subtype (I := I) g ρ Ψ
    _ = ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
        ∫⁻ w, (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
          (fun w =>
            ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
              ENNReal.ofReal (ρ α.val (Ψ w))) w
          ∂(modelHaar (E := E)) := by
          refine tsum_congr (fun α => ?_)
          have hS_meas :
              MeasurableSet (B ∩ Ψ ⁻¹' (chartAt H α.val).source) :=
            measurableSet_param_chartPiece (I := I) α.val Ψ hB_meas hB_source
          symm
          rw [MeasureTheory.lintegral_indicator hS_meas]
    _ = ∫⁻ w,
        ∑' α : {α : M | (Function.support (ρ α)).Nonempty},
          (B ∩ Ψ ⁻¹' (chartAt H α.val).source).indicator
            (fun w =>
              ENNReal.ofReal (paramDensity (I := I) g Ψ w) *
                ENNReal.ofReal (ρ α.val (Ψ w))) w
        ∂(modelHaar (E := E)) := by
          haveI hCρ : Countable {α : M | (Function.support (ρ α)).Nonempty} :=
            (countable_nonempty_support_of_pou (I := I) ρ).to_subtype
          symm
          exact MeasureTheory.lintegral_tsum (μ := modelHaar (E := E)) (fun α =>
            aemeasurable_paramDensity_mul_pou_indicator_chartPiece
              (I := I) g ρ α.val Ψ hB_meas hB_source)
    _ = ∫⁻ w, B.indicator
        (fun w => ENNReal.ofReal (paramDensity (I := I) g Ψ w)) w
        ∂(modelHaar (E := E)) := by
          exact MeasureTheory.lintegral_congr
            (fun w => tsum_param_pou_piece_indicator_eq (I := I) g ρ hρ Ψ w)
    _ = ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
          rw [MeasureTheory.lintegral_indicator hB_meas]


theorem riemannianVolumeMeasure_image_param_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {B : Set E} (hB_meas : MeasurableSet B)
    (hB_source : B ⊆ Ψ.source) :
    riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) =
      ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  rw [← riemannianMeasure_eq_riemannianVolumeMeasure (I := I) g
    (chartAtlasPOU I M) (chartAtlasPOU_isSubordinate I M)]
  exact riemannianMeasure_image_param_eq (I := I) g (chartAtlasPOU I M)
    (chartAtlasPOU_isSubordinate I M) Ψ hB_meas hB_source








theorem riemannianVolumeMeasure_param_target_eq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {A : Set M} (hA_meas : MeasurableSet A)
    (hA_target : A ⊆ Ψ.target) :
    riemannianVolumeMeasure (I := I) (M := M) g A =
      ∫⁻ w in Ψ.symm '' A, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
  set B : Set E := Ψ.symm '' A with hB_def
  have hB_meas : MeasurableSet B := by
    rw [hB_def]
    exact measurableSet_symm_image_param (I := I) Ψ hA_meas hA_target
  have hB_source : B ⊆ Ψ.source := by
    rw [hB_def]
    rintro w ⟨x, hxA, rfl⟩
    exact Ψ.toPartialEquiv.map_target (hA_target hxA)
  have himage : Ψ '' B = A := by
    rw [hB_def]
    exact PartialEquiv.image_symm_image_of_subset_target Ψ.toPartialEquiv hA_target
  calc
    riemannianVolumeMeasure (I := I) (M := M) g A =
        riemannianVolumeMeasure (I := I) (M := M) g (Ψ '' B) := by
          rw [himage]
    _ = ∫⁻ w in B, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
          exact riemannianVolumeMeasure_image_param_eq (I := I) g Ψ hB_meas hB_source
    _ = ∫⁻ w in Ψ.symm '' A, ENNReal.ofReal (paramDensity (I := I) g Ψ w)
        ∂(modelHaar (E := E)) := by
          rw [hB_def]






lemma paramGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E) :
    (paramGramMatrix (I := I) g Ψ w).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (paramGramMatrix (I := I) g Ψ w j i) =
    paramGramMatrix (I := I) g Ψ w i j
  simp only [paramGramMatrix_apply, star_trivial]
  exact g.symm (Ψ w)
    (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))
    (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))







lemma paramGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) (w : E)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (paramGramMatrix (I := I) g Ψ w) *ᵥ c =
      g.inner (Ψ w)
        (∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
        (∑ j, c j • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := by
  have hexpand' :
      g.inner (Ψ w)
          (∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
          (∑ j, c j • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))
        = ∑ i, ∑ j, (c i * c j) *
            g.inner (Ψ w)
              (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
              (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := by
    have hL :
        g.inner (Ψ w)
            (∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
          = ∑ i, c i •
              g.inner (Ψ w)
                (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.smul_apply]
    have hR :
        g.inner (Ψ w)
            (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
            (∑ j, c j • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))
          = ∑ j, c j *
              g.inner (Ψ w)
                (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
                (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand']
  simp only [dotProduct, Matrix.mulVec, paramGramMatrix_apply, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring







lemma paramGramMatrix_posDef
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    (paramGramMatrix (I := I) g Ψ w).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (paramGramMatrix_isHermitian (I := I) g Ψ w) ?_
  intro c hc
  set v : TangentSpace I (Ψ w) :=
    ∑ i, c i • mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i) with hv_def
  have heq := paramGramMatrix_dotProduct_mulVec (I := I) g Ψ w c
  rw [heq]
  have hker := paramDeriv_ker (I := I) Ψ hw
  have hli : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i)) := by
    simpa [Function.comp_def] using
      (chartModelBasis E).linearIndependent.map'
        (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap hker
  have hvnz : v ≠ 0 := by
    intro hv0
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hv0)
    exact hc this
  exact g.pos (Ψ w) v hvnz





lemma paramGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    0 < (paramGramMatrix (I := I) g Ψ w).det :=
  (paramGramMatrix_posDef (I := I) g Ψ hw).det_pos







lemma paramDensity_pos
    (g : SmoothRiemannianMetric I M)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    0 < paramDensity (I := I) g Ψ w :=
  Real.sqrt_pos.mpr (paramGramMatrix_det_pos (I := I) g Ψ hw)

end Measure
end Integral
end DifferentialGeometry
