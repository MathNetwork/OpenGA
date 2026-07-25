import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.MetricJet3Difference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields









noncomputable section

set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))



omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem metricComp_sub
    (gBase g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (a b : Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) gBase 0 2
        (metricCcTensor (I := I) (M := M) gBase g₁ -
          metricCcTensor (I := I) (M := M) gBase g₂)
        α (![] : Fin 0 → Fin (Module.finrank ℝ E)) ![a, b] x =
      chartGramMatrix (I := I) g₁ α x a b -
        chartGramMatrix (I := I) g₂ α x a b := by
  have hIdx : (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)) :=
    Subsingleton.elim _ _
  have hcomp := ccTensorBilin_chartBasisVecFiber_eq_tensorChartComponentRaw
    (I := I) gBase
    (metricCcTensor (I := I) (M := M) gBase g₁ -
      metricCcTensor (I := I) (M := M) gBase g₂) α hx a b
  rw [← hIdx] at hcomp
  rw [← hcomp]
  rw [ccTensorBilin_sub,
    metricCcTensor_apply, metricCcTensor_apply,
    g_inner_eq_chartGramMatrix_basis, g_inner_eq_chartGramMatrix_basis]



omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem gramDiff_eqOn
    (gBase g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (a b : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (fun y : E => chartGramOnE (I := I) g₁ α a b y -
        chartGramOnE (I := I) g₂ α a b y)
      (tensorChartComponentOnModel (I := I) (M := M) gBase
        (metricCcTensor (I := I) (M := M) gBase g₁ -
          metricCcTensor (I := I) (M := M) gBase g₂) α ![a, b])
      (interior (extChartAt I α).target) := by
  intro y hy
  have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have hsrc := (extChartAt I α).map_target (interior_subset hy)
    rwa [extChartAt_source] at hsrc
  rw [tensorChartComponentOnModel,
    metricComp_sub (I := I) (M := M) gBase g₁ g₂ α hx a b]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma basisJet_apply_le {m : ℕ}
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ)
    (v : Fin m → Fin (Module.finrank ℝ E)) :
    |F (fun i => (chartModelBasis E) (v i))| ≤
      ‖F‖ * (∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖) ^ m := by
  classical
  set B : ℝ := ∑ a : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) a‖ with hB_def
  have hB : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsingle : ∀ i : Fin m, ‖(chartModelBasis E) (v i)‖ ≤ B := by
    intro i
    rw [hB_def]
    exact Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ (v i))
  have hprod : (∏ i : Fin m, ‖(chartModelBasis E) (v i)‖) ≤ B ^ m := by
    calc
      (∏ i : Fin m, ‖(chartModelBasis E) (v i)‖) ≤ ∏ _i : Fin m, B :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hsingle i)
      _ = B ^ m := by simp
  have hop := F.le_opNorm (fun i => (chartModelBasis E) (v i))
  rw [Real.norm_eq_abs] at hop
  exact hop.trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg F))

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gramIter_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (a b : Fin (Module.finrank ℝ E)) {N m : ℕ} (hm : m ≤ N) :
    ‖iteratedFDeriv ℝ m
        (fun z => chartGramOnE (I := I) g₁ α a b z -
          chartGramOnE (I := I) g₂ α a b z) y‖ ≤
      chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
        (interior (extChartAt I α).target) y := by
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m isOpen_interior hy]
  exact (norm_iteratedFDerivWithin_le_seminorm hm _ _ _).trans
    (iteratedFDerivSeminorm_gramDiff_le_sum
      (I := I) (M := M) N g₁ g₂ α
      (interior (extChartAt I α).target) y a b)

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gram0_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (N : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (a b : Fin (Module.finrank ℝ E)) :
    |chartGramMatrix (I := I) g₁ α ((extChartAt I α).symm y) a b -
      chartGramMatrix (I := I) g₂ α ((extChartAt I α).symm y) a b| ≤
      chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
        (interior (extChartAt I α).target) y := by
  have h := gramIter_le (I := I) (M := M) g₁ g₂ α hy a b
    (N := N) (m := 0) (Nat.zero_le N)
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gram1_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (N : ℕ)
    (hN : 1 ≤ N) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d a b : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) d (chartGramOnE (I := I) g₁ α a b) y -
      partialDeriv (E := E) d (chartGramOnE (I := I) g₂ α a b) y| ≤
      (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) *
        chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  let f₁ : E → ℝ := chartGramOnE (I := I) g₁ α a b
  let f₂ : E → ℝ := chartGramOnE (I := I) g₂ α a b
  have h₁ : ContDiffAt ℝ ∞ f₁ y :=
    (chartGramOnE_contDiffOn_int (I := I) g₁ α a b).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have h₂ : ContDiffAt ℝ ∞ f₂ y :=
    (chartGramOnE_contDiffOn_int (I := I) g₂ α a b).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have hsub : iteratedFDeriv ℝ 1 f₁ y - iteratedFDeriv ℝ 1 f₂ y =
      iteratedFDeriv ℝ 1 (fun z => f₁ z - f₂ z) y := by
    simpa only [Pi.sub_apply] using
      (iteratedFDeriv_sub_apply
        (h₁.of_le (WithTop.coe_le_coe.2
          (show ((1 : ℕ) : ℕ∞) ≤ ⊤ from le_top)))
        (h₂.of_le (WithTop.coe_le_coe.2
          (show ((1 : ℕ) : ℕ∞) ≤ ⊤ from le_top)))).symm
  have heq : partialDeriv (E := E) d f₁ y - partialDeriv (E := E) d f₂ y =
      iteratedFDeriv ℝ 1 (fun z => f₁ z - f₂ z) y
        ![(chartModelBasis E) d] := by
    rw [partial_eq_iter1, partial_eq_iter1]
    exact congrArg (fun F => F ![(chartModelBasis E) d]) hsub
  rw [show chartGramOnE (I := I) g₁ α a b = f₁ from rfl,
    show chartGramOnE (I := I) g₂ α a b = f₂ from rfl, heq]
  have happ := basisJet_apply_le
    (E := E) (iteratedFDeriv ℝ 1 (fun z => f₁ z - f₂ z) y) ![d]
  have hnorm := gramIter_le (I := I) (M := M) g₁ g₂ α hy a b
    (N := N) (m := 1) hN
  calc
    |iteratedFDeriv ℝ 1 (fun z => f₁ z - f₂ z) y ![(chartModelBasis E) d]|
        ≤ ‖iteratedFDeriv ℝ 1 (fun z => f₁ z - f₂ z) y‖ *
            (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 1 := by
          simpa using happ
    _ ≤ chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
          (interior (extChartAt I α).target) y *
            (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 1 :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg (Finset.sum_nonneg
        fun _ _ => norm_nonneg _) _)
    _ = (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) *
          chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
            (interior (extChartAt I α).target) y := by ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gram2_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (N : ℕ)
    (hN : 2 ≤ N) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d c a b : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) d
        (partialDeriv (E := E) c (chartGramOnE (I := I) g₁ α a b)) y -
      partialDeriv (E := E) d
        (partialDeriv (E := E) c (chartGramOnE (I := I) g₂ α a b)) y| ≤
      (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 2 *
        chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  let f₁ : E → ℝ := chartGramOnE (I := I) g₁ α a b
  let f₂ : E → ℝ := chartGramOnE (I := I) g₂ α a b
  have h₁ : ContDiffAt ℝ ∞ f₁ y :=
    (chartGramOnE_contDiffOn_int (I := I) g₁ α a b).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have h₂ : ContDiffAt ℝ ∞ f₂ y :=
    (chartGramOnE_contDiffOn_int (I := I) g₂ α a b).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have hsub : iteratedFDeriv ℝ 2 f₁ y - iteratedFDeriv ℝ 2 f₂ y =
      iteratedFDeriv ℝ 2 (fun z => f₁ z - f₂ z) y := by
    simpa only [Pi.sub_apply] using
      (iteratedFDeriv_sub_apply
        (h₁.of_le (WithTop.coe_le_coe.2
          (show ((2 : ℕ) : ℕ∞) ≤ ⊤ from le_top)))
        (h₂.of_le (WithTop.coe_le_coe.2
          (show ((2 : ℕ) : ℕ∞) ≤ ⊤ from le_top)))).symm
  have heq : partialDeriv (E := E) d (partialDeriv (E := E) c f₁) y -
      partialDeriv (E := E) d (partialDeriv (E := E) c f₂) y =
        iteratedFDeriv ℝ 2 (fun z => f₁ z - f₂ z) y
          ![(chartModelBasis E) d, (chartModelBasis E) c] := by
    rw [partial2_eq_iter2 f₁ h₁ d c, partial2_eq_iter2 f₂ h₂ d c]
    exact congrArg
      (fun F => F ![(chartModelBasis E) d, (chartModelBasis E) c]) hsub
  rw [show chartGramOnE (I := I) g₁ α a b = f₁ from rfl,
    show chartGramOnE (I := I) g₂ α a b = f₂ from rfl, heq]
  have happ := basisJet_apply_le
    (E := E) (iteratedFDeriv ℝ 2 (fun z => f₁ z - f₂ z) y) ![d, c]
  have hv : (fun i => (chartModelBasis E) (![d, c] i)) =
      ![(chartModelBasis E) d, (chartModelBasis E) c] := by
    funext i
    fin_cases i <;> rfl
  have hnorm := gramIter_le (I := I) (M := M) g₁ g₂ α hy a b
    (N := N) (m := 2) hN
  calc
    |iteratedFDeriv ℝ 2 (fun z => f₁ z - f₂ z) y
        ![(chartModelBasis E) d, (chartModelBasis E) c]|
        ≤ ‖iteratedFDeriv ℝ 2 (fun z => f₁ z - f₂ z) y‖ *
            (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 2 := by
          rw [← hv]
          exact happ
    _ ≤ chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
          (interior (extChartAt I α).target) y *
            (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg (Finset.sum_nonneg
        fun _ _ => norm_nonneg _) _)
    _ = (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 2 *
          chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
            (interior (extChartAt I α).target) y := by ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma gram3_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (N : ℕ)
    (hN : 3 ≤ N) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (d c m a b : Fin (Module.finrank ℝ E)) :
    |partialDeriv (E := E) d
        (partialDeriv (E := E) c
          (partialDeriv (E := E) m (chartGramOnE (I := I) g₁ α a b))) y -
      partialDeriv (E := E) d
        (partialDeriv (E := E) c
          (partialDeriv (E := E) m (chartGramOnE (I := I) g₂ α a b))) y| ≤
      (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 3 *
        chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  let f₁ : E → ℝ := chartGramOnE (I := I) g₁ α a b
  let f₂ : E → ℝ := chartGramOnE (I := I) g₂ α a b
  have h₁ : ContDiffAt ℝ ∞ f₁ y :=
    (chartGramOnE_contDiffOn_int (I := I) g₁ α a b).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have h₂ : ContDiffAt ℝ ∞ f₂ y :=
    (chartGramOnE_contDiffOn_int (I := I) g₂ α a b).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have hsub : iteratedFDeriv ℝ 3 f₁ y - iteratedFDeriv ℝ 3 f₂ y =
      iteratedFDeriv ℝ 3 (fun z => f₁ z - f₂ z) y := by
    simpa only [Pi.sub_apply] using
      (iteratedFDeriv_sub_apply
        (h₁.of_le (WithTop.coe_le_coe.2
          (show ((3 : ℕ) : ℕ∞) ≤ ⊤ from le_top)))
        (h₂.of_le (WithTop.coe_le_coe.2
          (show ((3 : ℕ) : ℕ∞) ≤ ⊤ from le_top)))).symm
  have heq :
      partialDeriv (E := E) d (partialDeriv (E := E) c
          (partialDeriv (E := E) m f₁)) y -
        partialDeriv (E := E) d (partialDeriv (E := E) c
          (partialDeriv (E := E) m f₂)) y =
        iteratedFDeriv ℝ 3 (fun z => f₁ z - f₂ z) y
          ![(chartModelBasis E) d, (chartModelBasis E) c,
            (chartModelBasis E) m] := by
    rw [partial3_eq_iter3 f₁ h₁ d c m, partial3_eq_iter3 f₂ h₂ d c m]
    exact congrArg
      (fun F => F ![(chartModelBasis E) d, (chartModelBasis E) c,
        (chartModelBasis E) m]) hsub
  rw [show chartGramOnE (I := I) g₁ α a b = f₁ from rfl,
    show chartGramOnE (I := I) g₂ α a b = f₂ from rfl, heq]
  have happ := basisJet_apply_le
    (E := E) (iteratedFDeriv ℝ 3 (fun z => f₁ z - f₂ z) y) ![d, c, m]
  have hv : (fun i => (chartModelBasis E) (![d, c, m] i)) =
      ![(chartModelBasis E) d, (chartModelBasis E) c,
        (chartModelBasis E) m] := by
    funext i
    fin_cases i <;> rfl
  have hnorm := gramIter_le (I := I) (M := M) g₁ g₂ α hy a b
    (N := N) (m := 3) hN
  calc
    |iteratedFDeriv ℝ 3 (fun z => f₁ z - f₂ z) y
        ![(chartModelBasis E) d, (chartModelBasis E) c,
          (chartModelBasis E) m]|
        ≤ ‖iteratedFDeriv ℝ 3 (fun z => f₁ z - f₂ z) y‖ *
            (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 3 := by
          rw [← hv]
          exact happ
    _ ≤ chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
          (interior (extChartAt I α).target) y *
            (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 3 :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg (Finset.sum_nonneg
        fun _ _ => norm_nonneg _) _)
    _ = (∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖) ^ 3 *
          chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
            (interior (extChartAt I α).target) y := by ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in



theorem metricJet2_le_gram (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g₂ : SmoothRiemannianMetric I M) {y : E},
        y ∈ interior (extChartAt I α).target →
        chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y ≤
          C * chartGramJetDiffSeminormSum (I := I) (M := M) 2 g₁ g₂ α
            (interior (extChartAt I α).target) y := by
  classical
  let B : ℝ := ∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let C : ℝ :=
    (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)) +
    (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E), B) +
    (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro g₁ g₂ y hy
  set J : ℝ := chartGramJetDiffSeminormSum (I := I) (M := M) 2 g₁ g₂ α
    (interior (extChartAt I α).target) y with hJ_def
  have hJ : 0 ≤ J := by
    rw [hJ_def]
    exact chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) 2 g₁ g₂ α _ y
  have h0 : chartGramDiffSup (I := I) (M := M) g₁ g₂ α
      ((extChartAt I α).symm y) ≤
      (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)) * J := by
    unfold chartGramDiffSup matrixEntryL1
    calc
      (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |(chartGramMatrix g₁ α ((extChartAt I α).symm y) -
            chartGramMatrix g₂ α ((extChartAt I α).symm y)) p.1 p.2|)
          ≤ ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), J :=
        Finset.sum_le_sum fun p _ => by
          simpa [Matrix.sub_apply, hJ_def] using
            gram0_le (I := I) (M := M) g₁ g₂ α 2 hy p.1 p.2
      _ = (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (1 : ℝ)) * J := by simp
  have h1 : chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y ≤
      (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E), B) * J := by
    unfold chartGramPartialDiffSup gramPartialDiffEntry
    calc
      (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₁ α p.1 p.2.2) y -
            partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₂ α p.1 p.2.2) y|)
          ≤ ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E), B * J :=
        Finset.sum_le_sum fun p _ => by
          simpa [B, hJ_def] using
            gram1_le (I := I) (M := M) g₁ g₂ α 2 (by omega)
              hy p.2.1 p.1 p.2.2
      _ = (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), B) * J := by
        simp only [B, Finset.sum_mul]
  have h2 : chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2) * J := by
    unfold chartGramPartial2DiffSup gramPartial2DiffEntry
    calc
      (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) g₁ α p.2.2.1 p.2.2.2)) y -
            partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) g₂ α p.2.2.1 p.2.2.2)) y|)
          ≤ ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2 * J :=
        Finset.sum_le_sum fun p _ => by
          simpa [B, hJ_def] using gram2_le (I := I) (M := M) g₁ g₂ α 2
            (by omega) hy p.1 p.2.1 p.2.2.1 p.2.2.2
      _ = (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2) * J := by
        rw [Finset.sum_mul]
  unfold chartMetricJet2DiffSup chartMetricJet1DiffSup
  calc
    chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) +
          chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y +
        chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y
        ≤ ((∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)) * J +
            (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E), B) * J) +
          (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2) * J :=
      add_le_add (add_le_add h0 h1) h2
    _ = C * J := by
      dsimp [C]
      ring
    _ = C * chartGramJetDiffSeminormSum (I := I) (M := M) 2 g₁ g₂ α
          (interior (extChartAt I α).target) y := by rw [hJ_def]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in



theorem metricJet3_le_gram (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g₂ : SmoothRiemannianMetric I M) {y : E},
        y ∈ interior (extChartAt I α).target →
        metricJet3DiffSup (I := I) (M := M) g₁ g₂ α y ≤
          C * chartGramJetDiffSeminormSum (I := I) (M := M) 3 g₁ g₂ α
            (interior (extChartAt I α).target) y := by
  classical
  let B : ℝ := ∑ q : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) q‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let C : ℝ :=
    (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)) +
    (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E), B) +
    (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2) +
    (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E), B ^ 3)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro g₁ g₂ y hy
  set J : ℝ := chartGramJetDiffSeminormSum (I := I) (M := M) 3 g₁ g₂ α
    (interior (extChartAt I α).target) y with hJ_def
  have hJ : 0 ≤ J := by
    rw [hJ_def]
    exact chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) 3 g₁ g₂ α _ y
  have h0 : chartGramDiffSup (I := I) (M := M) g₁ g₂ α
      ((extChartAt I α).symm y) ≤
      (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)) * J := by
    unfold chartGramDiffSup matrixEntryL1
    calc
      (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |(chartGramMatrix g₁ α ((extChartAt I α).symm y) -
            chartGramMatrix g₂ α ((extChartAt I α).symm y)) p.1 p.2|)
          ≤ ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), J :=
        Finset.sum_le_sum fun p _ => by
          simpa [Matrix.sub_apply, hJ_def] using
            gram0_le (I := I) (M := M) g₁ g₂ α 3 hy p.1 p.2
      _ = (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (1 : ℝ)) * J := by simp
  have h1 : chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y ≤
      (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E), B) * J := by
    unfold chartGramPartialDiffSup gramPartialDiffEntry
    calc
      (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₁ α p.1 p.2.2) y -
            partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) g₂ α p.1 p.2.2) y|)
          ≤ ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E), B * J :=
        Finset.sum_le_sum fun p _ => by
          simpa [B, hJ_def] using
            gram1_le (I := I) (M := M) g₁ g₂ α 3 (by omega)
              hy p.2.1 p.1 p.2.2
      _ = (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), B) * J := by
        simp only [B, Finset.sum_mul]
  have h2 : chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2) * J := by
    unfold chartGramPartial2DiffSup gramPartial2DiffEntry
    calc
      (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) g₁ α p.2.2.1 p.2.2.2)) y -
            partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (chartGramOnE (I := I) g₂ α p.2.2.1 p.2.2.2)) y|)
          ≤ ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2 * J :=
        Finset.sum_le_sum fun p _ => by
          simpa [B, hJ_def] using gram2_le (I := I) (M := M) g₁ g₂ α 3
            (by omega) hy p.1 p.2.1 p.2.2.1 p.2.2.2
      _ = (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2) * J := by
        rw [Finset.sum_mul]
  have h3 : gramD3DiffSup (I := I) (M := M) g₁ g₂ α y ≤
      (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E), B ^ 3) * J := by
    unfold gramD3DiffSup
    calc
      (∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (partialDeriv (E := E) p.2.2.1
                  (chartGramOnE (I := I) g₁ α p.2.2.2.1 p.2.2.2.2))) y -
            partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (partialDeriv (E := E) p.2.2.1
                  (chartGramOnE (I := I) g₂ α p.2.2.2.1 p.2.2.2.2))) y|)
          ≤ ∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E), B ^ 3 * J :=
        Finset.sum_le_sum fun p _ => by
          simpa [B, hJ_def] using gram3_le (I := I) (M := M) g₁ g₂ α 3
            (by omega) hy p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
      _ = (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), B ^ 3) * J := by
        rw [Finset.sum_mul]
  unfold metricJet3DiffSup chartMetricJet2DiffSup chartMetricJet1DiffSup
  calc
    chartGramDiffSup (I := I) (M := M) g₁ g₂ α ((extChartAt I α).symm y) +
          chartGramPartialDiffSup (I := I) (M := M) g₁ g₂ α y +
        chartGramPartial2DiffSup (I := I) (M := M) g₁ g₂ α y +
      gramD3DiffSup (I := I) (M := M) g₁ g₂ α y
        ≤ ((∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (1 : ℝ)) * J +
            (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E), B) * J) +
          (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), B ^ 2) * J +
          (∑ _p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E), B ^ 3) * J :=
      add_le_add (add_le_add (add_le_add h0 h1) h2) h3
    _ = C * J := by
      dsimp [C]
      ring
    _ = C * chartGramJetDiffSeminormSum (I := I) (M := M) 3 g₁ g₂ α
          (interior (extChartAt I α).target) y := by rw [hJ_def]



omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem gramJet_le_bare
    (gBase g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (N : ℕ)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    chartGramJetDiffSeminormSum (I := I) (M := M) N g₁ g₂ α
        (interior (extChartAt I α).target) y ≤
      (∑ _a : Fin (Module.finrank ℝ E),
        ∑ _b : Fin (Module.finrank ℝ E), (1 : ℝ)) *
        chartComponentJetSeminormSum (I := I) (M := M) gBase
          (metricCcTensor (I := I) (M := M) gBase g₁ -
            metricCcTensor (I := I) (M := M) gBase g₂) α N y := by
  classical
  let D : SmoothCcTensor gBase 0 2 :=
    metricCcTensor (I := I) (M := M) gBase g₁ -
      metricCcTensor (I := I) (M := M) gBase g₂
  set B : ℝ := chartComponentJetSeminormSum (I := I) (M := M) gBase D α N y
    with hB_def
  have hB : 0 ≤ B := by
    rw [hB_def]
    exact bareChartJetContentOnE_nonneg (I := I) (M := M) gBase D α N y
  have hpair : ∀ a b : Fin (Module.finrank ℝ E),
      iteratedFDerivSeminorm N
        (fun z => chartGramOnE (I := I) g₁ α a b z -
          chartGramOnE (I := I) g₂ α a b z)
        (interior (extChartAt I α).target) y ≤ B := by
    intro a b
    have heq := gramDiff_eqOn (I := I) (M := M) gBase g₁ g₂ α a b
    change Set.EqOn _ (tensorChartComponentOnModel (I := I) (M := M) gBase D α ![a, b]) _ at heq
    unfold iteratedFDerivSeminorm
    calc
      (∑ m ∈ Finset.range (N + 1),
          ‖iteratedFDerivWithin ℝ m
            (fun z => chartGramOnE (I := I) g₁ α a b z -
              chartGramOnE (I := I) g₂ α a b z)
            (interior (extChartAt I α).target) y‖)
          = ∑ m ∈ Finset.range (N + 1),
              ‖iteratedFDerivWithin ℝ m
                (tensorChartComponentOnModel (I := I) (M := M) gBase D α ![a, b])
                (interior (extChartAt I α).target) y‖ := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [iteratedFDerivWithin_congr (𝕜 := ℝ) heq hy m]
      _ ≤ B := by
        rw [hB_def]
        unfold chartComponentJetSeminormSum
        exact Finset.single_le_sum
          (fun (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) _ =>
            Finset.sum_nonneg fun m _ =>
              norm_nonneg (iteratedFDerivWithin ℝ m
                (tensorChartComponentOnModel (I := I) (M := M) gBase D α Jdx)
                (interior (extChartAt I α).target) y))
          (Finset.mem_univ ![a, b])
  unfold chartGramJetDiffSeminormSum
  calc
    (∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          iteratedFDerivSeminorm N
            (fun z => chartGramOnE (I := I) g₁ α a b z -
              chartGramOnE (I := I) g₂ α a b z)
            (interior (extChartAt I α).target) y)
        ≤ ∑ _a : Fin (Module.finrank ℝ E),
            ∑ _b : Fin (Module.finrank ℝ E), B :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpair a b
    _ = (∑ _a : Fin (Module.finrank ℝ E),
          ∑ _b : Fin (Module.finrank ℝ E), (1 : ℝ)) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = (∑ _a : Fin (Module.finrank ℝ E),
          ∑ _b : Fin (Module.finrank ℝ E), (1 : ℝ)) *
        chartComponentJetSeminormSum (I := I) (M := M) gBase
          (metricCcTensor (I := I) (M := M) gBase g₁ -
            metricCcTensor (I := I) (M := M) gBase g₂) α N y := by
      rw [hB_def]




omit [BoundarylessManifold I M] in
theorem metricJet2_intrinsic
    (gBase : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g₂ : SmoothRiemannianMetric I M) {b : M},
        b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α (extChartAt I α b) ≤
          C * ∑ i ∈ Finset.range 3,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + i) b
              ((iteratedCovGrad (I := I) gBase 0 2 i
                (metricCcTensor (I := I) (M := M) gBase g₁ -
                  metricCcTensor (I := I) (M := M) gBase g₂)).toSection b)) := by
  classical
  obtain ⟨Cmetric, hCmetric, hmetric⟩ :=
    metricJet2_le_gram (I := I) (M := M) α
  obtain ⟨Ceucl, hCeucl, heucl⟩ :=
    bareOnE_le_bare (I := I) (M := M) gBase α 2
  obtain ⟨Cfib, hCfib, hfib⟩ :=
    bareJet_le_fiber (I := I) (M := M) gBase 0 2 α 2
  let Npair : ℝ := ∑ _a : Fin (Module.finrank ℝ E),
    ∑ _b : Fin (Module.finrank ℝ E), (1 : ℝ)
  have hNpair : 0 ≤ Npair := by
    dsimp [Npair]
    positivity
  refine ⟨Cmetric * Npair * Ceucl * Cfib, by positivity, ?_⟩
  intro g₁ g₂ b hb
  let D : SmoothCcTensor gBase 0 2 :=
    metricCcTensor (I := I) (M := M) gBase g₁ -
      metricCcTensor (I := I) (M := M) gBase g₂
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact (chartAtlasPOU_isSubordinate I M) α hb
  have hy_int : extChartAt I α b ∈ interior (extChartAt I α).target :=
    chartImage_pouTsupport_subset_interior_target (I := I) (M := M) α
      ⟨b, hb, rfl⟩
  have hyK : toEuclidean (E := E) (extChartAt I α b) ∈
      chartPouKernel (I := I) (M := M) α := by
    exact ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
  have hb_pre :
      (extChartAt I α).symm
          ((toEuclidean (E := E)).symm
            (toEuclidean (E := E) (extChartAt I α b))) = b := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I α).left_inv hb_src
  have hmetric' := hmetric g₁ g₂ hy_int
  have hgram := gramJet_le_bare (I := I) (M := M) gBase g₁ g₂ α 2 hy_int
  change chartGramJetDiffSeminormSum (I := I) (M := M) 2 g₁ g₂ α
      (interior (extChartAt I α).target) (extChartAt I α b) ≤
        Npair * chartComponentJetSeminormSum (I := I) (M := M) gBase D α 2
          (extChartAt I α b) at hgram
  have heucl' := heucl D hy_int
  have hfib' := hfib D hyK
  rw [hb_pre] at hfib'
  calc
    chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α (extChartAt I α b)
        ≤ Cmetric * chartGramJetDiffSeminormSum (I := I) (M := M) 2 g₁ g₂ α
            (interior (extChartAt I α).target) (extChartAt I α b) := hmetric'
    _ ≤ Cmetric * (Npair *
          chartComponentJetSeminormSum (I := I) (M := M) gBase D α 2
            (extChartAt I α b)) :=
      mul_le_mul_of_nonneg_left hgram hCmetric
    _ ≤ Cmetric * (Npair * (Ceucl *
          bareChartJetContent (I := I) (M := M) gBase 0 2 D α 2
            (toEuclidean (E := E) (extChartAt I α b)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left heucl' hNpair) hCmetric
    _ ≤ Cmetric * (Npair * (Ceucl * (Cfib *
          ∑ i ∈ Finset.range 3,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + i) b
              ((iteratedCovGrad (I := I) gBase 0 2 i D).toSection b))))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfib' hCeucl) hNpair) hCmetric
    _ = (Cmetric * Npair * Ceucl * Cfib) *
          ∑ i ∈ Finset.range 3,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + i) b
              ((iteratedCovGrad (I := I) gBase 0 2 i
                (metricCcTensor (I := I) (M := M) gBase g₁ -
                  metricCcTensor (I := I) (M := M) gBase g₂)).toSection b)) := by
      dsimp [D]
      ring




omit [BoundarylessManifold I M] in
theorem metricJet3_intrinsic
    (gBase : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g₂ : SmoothRiemannianMetric I M) {b : M},
        b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        metricJet3DiffSup (I := I) (M := M) g₁ g₂ α (extChartAt I α b) ≤
          C * ∑ i ∈ Finset.range 4,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + i) b
              ((iteratedCovGrad (I := I) gBase 0 2 i
                (metricCcTensor (I := I) (M := M) gBase g₁ -
                  metricCcTensor (I := I) (M := M) gBase g₂)).toSection b)) := by
  classical
  obtain ⟨Cmetric, hCmetric, hmetric⟩ :=
    metricJet3_le_gram (I := I) (M := M) α
  obtain ⟨Ceucl, hCeucl, heucl⟩ :=
    bareOnE_le_bare (I := I) (M := M) gBase α 3
  obtain ⟨Cfib, hCfib, hfib⟩ :=
    bareJet_le_fiber (I := I) (M := M) gBase 0 2 α 3
  let Npair : ℝ := ∑ _a : Fin (Module.finrank ℝ E),
    ∑ _b : Fin (Module.finrank ℝ E), (1 : ℝ)
  have hNpair : 0 ≤ Npair := by
    dsimp [Npair]
    positivity
  refine ⟨Cmetric * Npair * Ceucl * Cfib, by positivity, ?_⟩
  intro g₁ g₂ b hb
  let D : SmoothCcTensor gBase 0 2 :=
    metricCcTensor (I := I) (M := M) gBase g₁ -
      metricCcTensor (I := I) (M := M) gBase g₂
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact (chartAtlasPOU_isSubordinate I M) α hb
  have hy_int : extChartAt I α b ∈ interior (extChartAt I α).target :=
    chartImage_pouTsupport_subset_interior_target (I := I) (M := M) α
      ⟨b, hb, rfl⟩
  have hyK : toEuclidean (E := E) (extChartAt I α b) ∈
      chartPouKernel (I := I) (M := M) α := by
    exact ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
  have hb_pre :
      (extChartAt I α).symm
          ((toEuclidean (E := E)).symm
            (toEuclidean (E := E) (extChartAt I α b))) = b := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I α).left_inv hb_src
  have hmetric' := hmetric g₁ g₂ hy_int
  have hgram := gramJet_le_bare (I := I) (M := M) gBase g₁ g₂ α 3 hy_int
  change chartGramJetDiffSeminormSum (I := I) (M := M) 3 g₁ g₂ α
      (interior (extChartAt I α).target) (extChartAt I α b) ≤
        Npair * chartComponentJetSeminormSum (I := I) (M := M) gBase D α 3
          (extChartAt I α b) at hgram
  have heucl' := heucl D hy_int
  have hfib' := hfib D hyK
  rw [hb_pre] at hfib'
  calc
    metricJet3DiffSup (I := I) (M := M) g₁ g₂ α (extChartAt I α b)
        ≤ Cmetric * chartGramJetDiffSeminormSum (I := I) (M := M) 3 g₁ g₂ α
            (interior (extChartAt I α).target) (extChartAt I α b) := hmetric'
    _ ≤ Cmetric * (Npair *
          chartComponentJetSeminormSum (I := I) (M := M) gBase D α 3
            (extChartAt I α b)) :=
      mul_le_mul_of_nonneg_left hgram hCmetric
    _ ≤ Cmetric * (Npair * (Ceucl *
          bareChartJetContent (I := I) (M := M) gBase 0 2 D α 3
            (toEuclidean (E := E) (extChartAt I α b)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left heucl' hNpair) hCmetric
    _ ≤ Cmetric * (Npair * (Ceucl * (Cfib *
          ∑ i ∈ Finset.range 4,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + i) b
              ((iteratedCovGrad (I := I) gBase 0 2 i D).toSection b))))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfib' hCeucl) hNpair) hCmetric
    _ = (Cmetric * Npair * Ceucl * Cfib) *
          ∑ i ∈ Finset.range 4,
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) gBase 0 (2 + i) b
              ((iteratedCovGrad (I := I) gBase 0 2 i
                (metricCcTensor (I := I) (M := M) gBase g₁ -
                  metricCcTensor (I := I) (M := M) gBase g₂)).toSection b)) := by
      dsimp [D]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
