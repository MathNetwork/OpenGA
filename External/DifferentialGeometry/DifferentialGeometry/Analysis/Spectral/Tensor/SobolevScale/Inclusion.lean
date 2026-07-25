import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSobolevWeight_mono {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    tensorSobolevWeight (I := I) (M := M) i τ ≤
      tensorSobolevWeight (I := I) (M := M) i σ := by
  unfold tensorSobolevWeight
  exact Real.rpow_le_rpow_of_exponent_le
    (one_le_one_add_lambda (I := I) (M := M) i) hτσ

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma weighted_summable_of_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le ?_ ?_ T.weighted_summable
  · intro i
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i τ
    positivity
  · intro i
    have hmono : tensorSobolevWeight (I := I) (M := M) i τ ≤
        tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_mono (I := I) (M := M) i hτσ
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

def inclusionFun {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHs (I := I) (M := M) g r s τ where
  coeff := T.coeff
  weighted_summable := weighted_summable_of_le (I := I) (M := M) hτσ T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma inclusionFun_coeff {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    (inclusionFun (I := I) (M := M) hτσ T).coeff = T.coeff := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inclusionFun_add {τ σ : ℝ} (hτσ : τ ≤ σ)
    (S T : tensorHs (I := I) (M := M) g r s σ) :
    inclusionFun (I := I) (M := M) hτσ (S + T) =
      inclusionFun (I := I) (M := M) hτσ S +
        inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, add_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inclusionFun_smul {τ σ : ℝ} (hτσ : τ ≤ σ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    inclusionFun (I := I) (M := M) hτσ (c • T) =
      c • inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, smul_coeff]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_inclusionFun_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖inclusionFun (I := I) (M := M) hτσ T‖ ≤ ‖T‖ := by
  have h_t_sq : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (inclusionFun (I := I) (M := M) hτσ T)
    rwa [inclusionFun_coeff] at h
  have h_s_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_le_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    exact mul_le_mul_of_nonneg_right
      (tensorSobolevWeight_mono (I := I) (M := M) i hτσ) (sq_nonneg _)
  have h_tsum_le :
      ∑' i, tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms
      (weighted_summable_of_le (I := I) (M := M) hτσ T) T.weighted_summable
  have h_sq_le : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_t_sq, h_s_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖inclusionFun (I := I) (M := M) hτσ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end tensorHs

def tensorHsInclusion {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {τ σ : ℝ} (hτσ : τ ≤ σ) :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s τ :=
  LinearMap.mkContinuous
    { toFun := tensorHs.inclusionFun (I := I) (M := M) hτσ
      map_add' := tensorHs.inclusionFun_add (I := I) (M := M) hτσ
      map_smul' := fun c T =>
        tensorHs.inclusionFun_smul (I := I) (M := M) hτσ c T }
    1
    (fun T => by
      change ‖tensorHs.inclusionFun (I := I) (M := M) hτσ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact tensorHs.norm_inclusionFun_le (I := I) (M := M) hτσ T)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorHsInclusion_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T =
      tensorHs.inclusionFun (I := I) (M := M) hτσ T := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsInclusion_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T).coeff =
      T.coeff := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsInclusion_coeff_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T).coeff i =
      T.coeff i := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_norm_le {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T‖ ≤ ‖T‖ :=
  tensorHs.norm_inclusionFun_le (I := I) (M := M) hτσ T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_injective {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {τ σ : ℝ} (hτσ : τ ≤ σ) :
    Function.Injective
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ) := by
  intro S T hST
  ext i
  have h := congrArg (fun U => tensorHs.coeff U i) hST
  simpa only [tensorHsInclusion_coeff] using h

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsInclusion_refl {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ} :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (le_refl σ) =
      ContinuousLinearMap.id ℝ
        (tensorHs (I := I) (M := M) g r s σ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ContinuousLinearMap.id_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsInclusion_refl_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (le_refl σ) T = T := by
  ext i
  simp only [tensorHsInclusion_coeff_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_trans {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {ρ τ σ : ℝ} (hρτ : ρ ≤ τ) (hτσ : τ ≤ σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (hρτ.trans hτσ) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hρτ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ) := by
  ext T i
  simp only [tensorHsInclusion_coeff_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_trans_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {ρ τ σ : ℝ} (hρτ : ρ ≤ τ) (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) (hρτ.trans hτσ) T =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hρτ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ T) := by
  ext i
  simp only [tensorHsInclusion_coeff_apply]

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

def finiteSupportSubmodule (σ : ℝ) :
    Submodule ℝ (tensorHs (I := I) (M := M) g r s σ) where
  carrier := {T | (Function.support T.coeff).Finite}
  add_mem' := by
    intro S T hS hT
    refine Set.Finite.subset (hS.union hT) ?_
    intro i hi
    simp only [Function.mem_support, add_coeff, ne_eq] at hi
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, ne_eq, not_or,
      not_not] at hcon
    exact hi (by rw [hcon.1, hcon.2, add_zero])
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zero_coeff]
    refine Set.finite_empty.subset ?_
    intro i hi
    simp only [Function.mem_support, ne_eq, not_true_eq_false] at hi
  smul_mem' := by
    intro c T hT
    refine Set.Finite.subset hT ?_
    intro i hi
    simp only [Function.mem_support, smul_coeff, ne_eq] at hi
    simp only [Function.mem_support, ne_eq]
    intro hcon
    exact hi (by rw [hcon, mul_zero])

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma mem_finiteSupportSubmodule {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ) :
    T ∈ finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s) σ ↔
      (Function.support T.coeff).Finite := Iff.rfl

end tensorHs

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ}

open scoped Classical in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rescaleEquivL2_smul_basisVec
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    rescaleEquivL2 (I := I) (M := M) (σ := σ)
        (T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i) =
      lp.single 2 i
        (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i) := by
  classical
  apply lp.ext
  funext j
  rw [rescaleEquivL2_apply, lp.single_apply]
  simp only [smul_coeff, tensorHsBasisVec_coeff]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasSum_smul_basisVec
    (T : tensorHs (I := I) (M := M) g r s σ) :
    HasSum (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i) T := by
  classical
  rw [← ContinuousLinearEquiv.hasSum'
    (e := (rescaleEquivL2 (I := I) (M := M)
      (σ := σ)).toContinuousLinearEquiv)]
  have h_l2 : HasSum
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        lp.single 2 i
          (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i))
      (rescaleEquivL2 (I := I) (M := M)
        (σ := σ) T) := by
    have h := lp.hasSum_single (α := TensorEigenIdx (I := I) (M := M) g r s)
      (E := fun _ => ℝ) (p := 2) (by norm_num)
      (rescaleEquivL2 (I := I) (M := M)
        (σ := σ) T)
    refine h.congr_fun (fun i => ?_)
    rw [rescaleEquivL2_apply]
  refine h_l2.congr_fun (fun i => ?_)
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    rescaleEquivL2_smul_basisVec]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem mem_closure_finiteSupportSubmodule
    (T : tensorHs (I := I) (M := M) g r s σ) :
    T ∈ closure
      (finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s) σ :
        Set (tensorHs (I := I) (M := M) g r s σ)) := by
  classical
  refine mem_closure_of_tendsto
    (hasSum_smul_basisVec (I := I) (M := M) T) ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  refine Submodule.sum_mem _ (fun i _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  rw [mem_finiteSupportSubmodule]
  refine Set.Finite.subset (Set.finite_singleton i) ?_
  intro j hj
  simp only [Function.mem_support, tensorHsBasisVec_coeff, ne_eq,
    ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hj
  simpa using hj

end tensorHs

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsFiniteSupportSubmodule_topologicalClosure
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ} :
    (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s)
        σ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro T _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact tensorHs.mem_closure_finiteSupportSubmodule (I := I) (M := M) T

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsFiniteSupportSubmodule_dense
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ} :
    Dense (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s)
      σ :
      Set (tensorHs (I := I) (M := M) g r s σ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact tensorHsFiniteSupportSubmodule_topologicalClosure
    (I := I) (M := M) (g := g) (r := r) (s := s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHs_dense_finiteSupport {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ} :
    Dense {T : tensorHs (I := I) (M := M) g r s σ |
      (Function.support T.coeff).Finite} :=
  tensorHsFiniteSupportSubmodule_dense (I := I) (M := M) (g := g) (r := r) (s := s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsBasisVec_span_dense {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {σ : ℝ} :
    Dense (Submodule.span ℝ
      (Set.range (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ)) :
      Set (tensorHs (I := I) (M := M) g r s σ)) := by
  classical
  refine tensorHsFiniteSupportSubmodule_dense (I := I) (M := M) (g := g) (r := r) (s := s)
    |>.mono ?_
  intro T hT
  rw [SetLike.mem_coe, tensorHs.mem_finiteSupportSubmodule] at hT
  classical
  have h_eq : T = ∑ i ∈ hT.toFinset,
      T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) σ i := by
    refine tensorHs.ext ?_
    funext j
    have h_sum : (∑ i ∈ hT.toFinset,
          T.coeff i • tensorHsBasisVec (I := I) (M := M) σ i).coeff j =
        ∑ i ∈ hT.toFinset,
          (if j = i then T.coeff i else 0) := by
      induction hT.toFinset using Finset.induction with
      | empty => simp
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
            tensorHs.add_coeff]
          simp only [tensorHs.smul_coeff, tensorHsBasisVec_coeff,
            mul_ite, mul_one, mul_zero]
    rw [h_sum]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj
      have hzero : T.coeff j = 0 := by
        by_contra hne
        exact hj (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [hzero]
  rw [h_eq]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

example {g : SmoothRiemannianMetric I M} {r s : ℕ} {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s τ :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hτσ

example {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ : ℝ} :
    Dense {T : tensorHs (I := I) (M := M) g r s σ |
      (Function.support T.coeff).Finite} :=
  tensorHs_dense_finiteSupport (I := I) (M := M)

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
