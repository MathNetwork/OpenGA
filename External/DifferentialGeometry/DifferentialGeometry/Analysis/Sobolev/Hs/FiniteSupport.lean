import DifferentialGeometry.Analysis.Sobolev.Hs.SpectralDefs
import DifferentialGeometry.Analysis.Sobolev.Hs.Inclusion


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace scalarHs

variable {g : SmoothRiemannianMetric I M} {σ : ℝ}

def ofFiniteSupport (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (f : EigenIdx (I := I) (M := M) g → ℝ)
    (hf : (Function.support f).Finite) :
    scalarHs (I := I) (M := M) g σ where
  coeff := f
  weighted_summable := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset hf
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    intro hfi
    apply hi
    rw [hfi]
    ring

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ofFiniteSupport_coeff (g : SmoothRiemannianMetric I M)
    (σ : ℝ) (f : EigenIdx (I := I) (M := M) g → ℝ)
    (hf : (Function.support f).Finite) :
    (ofFiniteSupport (I := I) (M := M) g σ f hf).coeff = f := rfl

open scoped Classical in

def basisVec (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (i : EigenIdx (I := I) (M := M) g) :
    scalarHs (I := I) (M := M) g σ :=
  ofFiniteSupport (I := I) (M := M) g σ
    (fun j => if j = i then (1 : ℝ) else 0)
    (by
      apply Set.Finite.subset (Set.finite_singleton i)
      intro j hj
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at hj
      simpa using hj)

open scoped Classical in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma basisVec_coeff (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (i j : EigenIdx (I := I) (M := M) g) :
    (basisVec (I := I) (M := M) g σ i).coeff j =
      (if j = i then (1 : ℝ) else 0) := rfl

def finiteSupportSubmodule (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    Submodule ℝ (scalarHs (I := I) (M := M) g σ) where
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

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma mem_finiteSupportSubmodule
    (T : scalarHs (I := I) (M := M) g σ) :
    T ∈ finiteSupportSubmodule (I := I) (M := M) g σ ↔
      (Function.support T.coeff).Finite := Iff.rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem hasSum_smul_basisVec_of_finite
    (T : scalarHs (I := I) (M := M) g σ)
    (hT : T ∈ finiteSupportSubmodule (I := I) (M := M) g σ) :
    T = ∑ i ∈ ((mem_finiteSupportSubmodule (I := I) (M := M) T).mp hT).toFinset,
      T.coeff i • basisVec (I := I) (M := M) g σ i := by
  classical
  set hT' := (mem_finiteSupportSubmodule (I := I) (M := M) T).mp hT
  refine scalarHs.ext ?_
  funext j
  have h_sum : (∑ i ∈ hT'.toFinset,
        T.coeff i • basisVec (I := I) (M := M) g σ i).coeff j =
      ∑ i ∈ hT'.toFinset,
        (if j = i then T.coeff i else 0) := by
    induction hT'.toFinset using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
          scalarHs.add_coeff]
        simp only [scalarHs.smul_coeff, basisVec_coeff,
          mul_ite, mul_one, mul_zero]
  rw [h_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · intro hj
    have hzero : T.coeff j = 0 := by
      by_contra hne
      exact hj (hT'.mem_toFinset.mpr (Function.mem_support.mpr hne))
    simp [hzero]

open scoped Classical in

omit [NeZero (Module.finrank ℝ E)] in
lemma rescaleEquivL2_smul_basisVec
    (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    rescaleEquivL2 (I := I) (M := M) (g := g) (σ := σ)
        (T.coeff i • basisVec (I := I) (M := M) g σ i) =
      lp.single 2 i
        (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i) := by
  classical
  apply lp.ext
  funext j
  rw [rescaleEquivL2_apply, lp.single_apply]
  simp only [smul_coeff, basisVec_coeff]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [NeZero (Module.finrank ℝ E)] in
theorem hasSum_smul_basisVec
    (T : scalarHs (I := I) (M := M) g σ) :
    HasSum (fun i : EigenIdx (I := I) (M := M) g =>
      T.coeff i • basisVec (I := I) (M := M) g σ i) T := by
  classical
  rw [← ContinuousLinearEquiv.hasSum'
    (e := (rescaleEquivL2 (I := I) (M := M)
      (g := g) (σ := σ)).toContinuousLinearEquiv)]
  have h_l2 : HasSum
      (fun i : EigenIdx (I := I) (M := M) g =>
        lp.single 2 i
          (Real.sqrt (scalarSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i))
      (rescaleEquivL2 (I := I) (M := M)
        (g := g) (σ := σ) T) := by
    have h := lp.hasSum_single (α := EigenIdx (I := I) (M := M) g)
      (E := fun _ => ℝ) (p := 2) (by norm_num)
      (rescaleEquivL2 (I := I) (M := M)
        (g := g) (σ := σ) T)
    refine h.congr_fun (fun i => ?_)
    rw [rescaleEquivL2_apply]
  refine h_l2.congr_fun (fun i => ?_)
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    rescaleEquivL2_smul_basisVec]

omit [NeZero (Module.finrank ℝ E)] in
theorem mem_closure_finiteSupportSubmodule
    (T : scalarHs (I := I) (M := M) g σ) :
    T ∈ closure
      (finiteSupportSubmodule (I := I) (M := M) g σ :
        Set (scalarHs (I := I) (M := M) g σ)) := by
  classical
  refine mem_closure_of_tendsto
    (hasSum_smul_basisVec (I := I) (M := M) T) ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  refine Submodule.sum_mem _ (fun i _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  rw [mem_finiteSupportSubmodule]
  refine Set.Finite.subset (Set.finite_singleton i) ?_
  intro j hj
  simp only [Function.mem_support, basisVec_coeff, ne_eq,
    ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hj
  simpa using hj

end scalarHs

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarHs.finiteSupportSubmodule_topologicalClosure_eq_top
    {g : SmoothRiemannianMetric I M} {σ : ℝ} :
    (scalarHs.finiteSupportSubmodule (I := I) (M := M)
        g σ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro T _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact scalarHs.mem_closure_finiteSupportSubmodule (I := I) (M := M) T

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarHs.finiteSupportSubmodule_dense
    {g : SmoothRiemannianMetric I M} {σ : ℝ} :
    Dense (scalarHs.finiteSupportSubmodule (I := I) (M := M) g σ :
      Set (scalarHs (I := I) (M := M) g σ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact scalarHs.finiteSupportSubmodule_topologicalClosure_eq_top
    (I := I) (M := M)

example {g : SmoothRiemannianMetric I M} {σ : ℝ}
    (i : EigenIdx (I := I) (M := M) g) :
    scalarHs (I := I) (M := M) g σ :=
  scalarHs.basisVec (I := I) (M := M) g σ i

example {g : SmoothRiemannianMetric I M} {σ : ℝ} :
    Dense (scalarHs.finiteSupportSubmodule (I := I) (M := M) g σ :
      Set (scalarHs (I := I) (M := M) g σ)) :=
  scalarHs.finiteSupportSubmodule_dense (I := I) (M := M)

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
