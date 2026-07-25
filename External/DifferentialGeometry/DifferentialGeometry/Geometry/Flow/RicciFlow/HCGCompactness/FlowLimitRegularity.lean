import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Metric.ChartGram



























noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open Tensor0SBundle
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M]

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in



theorem chartGramBound_contOn
    (gRef : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank Real E)) :
    ContinuousOn (fun x : M =>
      Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
          (chartBasisVecFiber (I := I) x₀ i x))
        * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
            (chartBasisVecFiber (I := I) x₀ j x)))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hii : ContinuousOn (fun x : M => chartGramMatrix (I := I) gRef x₀ x i i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (chartGramMatrix_entry_contMDiffOn (I := I) gRef x₀ i i).continuousOn
  have hjj : ContinuousOn (fun x : M => chartGramMatrix (I := I) gRef x₀ x j j)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (chartGramMatrix_entry_contMDiffOn (I := I) gRef x₀ j j).continuousOn
  exact (Real.continuous_sqrt.comp_continuousOn hii).mul
    (Real.continuous_sqrt.comp_continuousOn hjj)







omit [SigmaCompactSpace M] in
theorem chartGram_sub_le
    (gRef u u' : SmoothRiemannianMetric I M) (x₀ x : M)
    (i j : Fin (Module.finrank Real E)) :
    |chartGramMatrix (I := I) u x₀ x i j - chartGramMatrix (I := I) u' x₀ x i j|
      ≤ metricDerivNorm (I := I) 0 u u' gRef x
        * (Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
              (chartBasisVecFiber (I := I) x₀ i x))
          * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
              (chartBasisVecFiber (I := I) x₀ j x))) := by
  classical
  have hentry : chartGramMatrix (I := I) u x₀ x i j - chartGramMatrix (I := I) u' x₀ x i j
      = (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
          ![chartBasisVecFiber (I := I) x₀ i x, chartBasisVecFiber (I := I) x₀ j x] := by
    rw [chartGramMatrix_apply, chartGramMatrix_apply]
    have hu := Tensor0SBundle.metricTensorField_apply (I := I) u x
      (fun a => (![chartBasisVecFiber (I := I) x₀ i x,
        chartBasisVecFiber (I := I) x₀ j x] : Fin 2 → TangentSpace I x) a)
    have hu' := Tensor0SBundle.metricTensorField_apply (I := I) u' x
      (fun a => (![chartBasisVecFiber (I := I) x₀ i x,
        chartBasisVecFiber (I := I) x₀ j x] : Fin 2 → TangentSpace I x) a)
    simp only [metricDiffCovDerivAt, ContinuousMultilinearMap.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hu'
    change u.inner x _ _ - u'.inner x _ _
      = (metricCovDeriv (I := I) u gRef 0 x) _ - (metricCovDeriv (I := I) u' gRef 0 x) _
    rw [show (metricCovDeriv (I := I) u gRef 0 x)
          = Tensor0SBundle.metricTensorField (I := I) u x from rfl,
      show (metricCovDeriv (I := I) u' gRef 0 x)
          = Tensor0SBundle.metricTensorField (I := I) u' x from rfl,
      hu, hu']
  rw [hentry]
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have h := abs_apply_le_sqrt_normSq0S (I := I) (g := gRef) (x := x) (s := 2)
    basis hON (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
    ![chartBasisVecFiber (I := I) x₀ i x, chartBasisVecFiber (I := I) x₀ j x]
  refine h.trans (le_of_eq ?_)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl








omit [SigmaCompactSpace M] in
theorem chartGramLim_contOn
    [LocallyCompactSpace M]
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gInf : ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (β ψ : ℝ)
    (hconv : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ x ∈ K,
        metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x < ε)
    (x₀ : M) (i j : Fin (Module.finrank Real E))
    (hkcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  classical
  intro p₀ hp₀
  obtain ⟨hp₀t, hp₀x⟩ := hp₀

  obtain ⟨K, hKc, hKint, hKsub⟩ := exists_compact_subset
    (trivializationAt E (TangentSpace I) x₀).open_baseSet hp₀x
  have hKne : K.Nonempty := ⟨p₀.2, interior_subset hKint⟩

  set c : M → ℝ := fun x =>
    Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ i x))
      * Real.sqrt (gRef.inner x (chartBasisVecFiber (I := I) x₀ j x)
          (chartBasisVecFiber (I := I) x₀ j x)) with hc
  have hcnonneg : ∀ x : M, 0 ≤ c x := fun x =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨z, hzK, hz⟩ := hKc.exists_isMaxOn hKne
    ((chartGramBound_contOn (I := I) gRef x₀ i j).mono hKsub)
  set Cb : ℝ := c z with hCb
  have hCb0 : 0 ≤ Cb := hcnonneg z
  have hzle : ∀ x ∈ K, c x ≤ Cb := fun x hx => isMaxOn_iff.mp hz x hx

  have htu : TendstoUniformlyOn
      (fun (k : ℕ) (p : ℝ × M) => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      atTop (Set.Icc β ψ ×ˢ K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconv K hKc (ε / (Cb + 1)) (by positivity)
    filter_upwards [Filter.eventually_ge_atTop k0] with k hk
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hd : metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x ≤ ε / (Cb + 1) :=
      (hk0 k hk t ht x hx).le
    have hcs := chartGram_sub_le (I := I) gRef (gSeq k t) (gInf t) x₀ x i j
    calc dist (chartGramMatrix (I := I) (gInf t) x₀ x i j)
          (chartGramMatrix (I := I) (gSeq k t) x₀ x i j)
        = |chartGramMatrix (I := I) (gSeq k t) x₀ x i j
            - chartGramMatrix (I := I) (gInf t) x₀ x i j| := by
          rw [Real.dist_eq, abs_sub_comm]
      _ ≤ metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x * c x := hcs
      _ ≤ (ε / (Cb + 1)) * Cb := by
          exact mul_le_mul hd (hzle x hx) (hcnonneg x) (by positivity)
      _ < (ε / (Cb + 1)) * (Cb + 1) := by
          have hpos : 0 < ε / (Cb + 1) := by positivity
          exact mul_lt_mul_of_pos_left (by linarith) hpos
      _ = ε := div_mul_cancel₀ ε (by positivity)

  have hcOn : ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gInf p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ K) :=
    htu.continuousOn (Filter.Eventually.of_forall (fun k =>
      (hkcont k).mono (Set.prod_mono le_rfl hKsub))).frequently
  have hmem : Set.Icc β ψ ×ˢ K
      ∈ 𝓝[Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet] p₀ := by
    have hnhds : (Set.univ ×ˢ interior K : Set (ℝ × M)) ∈ 𝓝 p₀ :=
      prod_mem_nhds Filter.univ_mem (isOpen_interior.mem_nhds hKint)
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin _ hnhds) ?_
    rintro ⟨t, x⟩ ⟨⟨ht, _⟩, _, hxK⟩
    exact ⟨ht, interior_subset hxK⟩
  exact (hcOn.continuousWithinAt
    ⟨hp₀t, interior_subset hKint⟩).mono_of_mem_nhdsWithin hmem

set_option maxHeartbeats 1000000 in





omit [SigmaCompactSpace M] in
theorem metricTensorContLim
    [LocallyCompactSpace M]
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gInf : ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (β ψ : ℝ)
    (hconv : ∀ K : Set M, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ x ∈ K,
        metricDerivNorm (I := I) 0 (gSeq k t) (gInf t) gRef x < ε)
    (hkcont : ∀ (k : ℕ) (x₀ : M) (i j : Fin (Module.finrank Real E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (gSeq k p.1) x₀ p.2 i j)
      (Set.Icc β ψ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet
      (I := I) (M := M) 2 (Set.Icc β ψ)
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (gInf t) x) := by
  apply metricTensorCont_of_chartGram (I := I) (K := Set.Icc β ψ) gInf
  intro x₀ i j
  have hlim := chartGramLim_contOn (I := I) gSeq gInf gRef β ψ hconv x₀ i j
    (fun k => hkcont k x₀ i j)
  have hincl : ContinuousOn
      (fun q : {t : ℝ // t ∈ Set.Icc β ψ} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ Set.Icc β ψ} × M |
        q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  exact hlim.comp hincl (fun q hq => ⟨q.1.2, hq⟩)

end HCGCompactness
end DifferentialGeometry
