import DifferentialGeometry.Analysis.Spectral.Tensor.Rellich.Tensor
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.RellichManifold
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Analysis.Normed.Operator.Bilinear


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

section NormedComponents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def dualCoordinateProductMultilinearMap (r : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
    (fun k : Fin r =>
      LinearMap.toContinuousLinearMap ((chartModelBasis E).coord (Idx k)))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma dualCovariantCMM_apply (r : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E)) (v : Fin r → E) :
    dualCoordinateProductMultilinearMap (E := E) r Idx v =
      ∏ k : Fin r, ((chartModelBasis E).coord (Idx k)) (v k) := by
  classical
  unfold dualCoordinateProductMultilinearMap
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma dualCovariantCMM_apply_basis_tuple (r : ℕ)
    (Idx Jdx : Fin r → Fin (Module.finrank ℝ E)) :
    dualCoordinateProductMultilinearMap (E := E) r Idx
        (fun k : Fin r => chartModelBasis E (Jdx k)) =
      if Idx = Jdx then (1 : ℝ) else 0 := by
  classical
  rw [dualCovariantCMM_apply]
  by_cases hEq : Idx = Jdx
  · subst hEq
    rw [if_pos rfl]
    have hone : ∀ k : Fin r,
        ((chartModelBasis E).coord (Idx k)) (chartModelBasis E (Idx k)) = 1 := by
      intro k
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_pos rfl]
    rw [Finset.prod_congr rfl (fun k _ => hone k)]
    simp
  · rw [if_neg hEq]
    have h_exists : ∃ k : Fin r, Idx k ≠ Jdx k := by
      by_contra h_all
      apply hEq
      funext k
      by_contra hne
      exact h_all ⟨k, hne⟩
    obtain ⟨k₀, hk₀⟩ := h_exists
    have hzero : ((chartModelBasis E).coord (Idx k₀)) (chartModelBasis E (Jdx k₀)) = 0 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply]
      exact if_neg hk₀.symm
    refine Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
    exact hzero

noncomputable def tensorChartComponentProjection (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ
      (fun k : Fin s => chartModelBasis E (Jdx k))).comp
    (ContinuousLinearMap.apply ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
      (dualCoordinateProductMultilinearMap (E := E) r Idx))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorChartComponentProjection_apply (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (T : TensorRSModel r s ℝ E) :
    tensorChartComponentProjection (E := E) r s Idx Jdx T =
      T (dualCoordinateProductMultilinearMap (E := E) r Idx)
        (fun k : Fin s => chartModelBasis E (Jdx k)) := rfl

noncomputable def tensorChartBasisElement (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    TensorRSModel r s ℝ E :=
  ContinuousLinearMap.smulRight
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => E) ℝ
      (fun k : Fin r => chartModelBasis E (Idx k)))
    (dualCoordinateProductMultilinearMap (E := E) s Jdx)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorChartBasisElement_apply (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (w : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) :
    tensorChartBasisElement (E := E) r s Idx Jdx w =
      w (fun k : Fin r => chartModelBasis E (Idx k)) •
        dualCoordinateProductMultilinearMap (E := E) s Jdx := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorChartComponentProjection_basisElement (r s : ℕ)
    (Idx₁ Idx₂ : Fin r → Fin (Module.finrank ℝ E))
    (Jdx₁ Jdx₂ : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx₁ Jdx₁
        (tensorChartBasisElement (E := E) r s Idx₂ Jdx₂) =
      (if Idx₁ = Idx₂ then (1 : ℝ) else 0) *
        (if Jdx₂ = Jdx₁ then (1 : ℝ) else 0) := by
  classical
  rw [tensorChartComponentProjection_apply, tensorChartBasisElement_apply]
  rw [ContinuousMultilinearMap.smul_apply,
    dualCovariantCMM_apply_basis_tuple (E := E) s Jdx₂ Jdx₁,
    dualCovariantCMM_apply_basis_tuple (E := E) r Idx₁ Idx₂,
    smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
private lemma cmm_eq_sum_basis_coeffs (s : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    f = ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          f (fun k : Fin s => chartModelBasis E (Jdx k)) •
            dualCoordinateProductMultilinearMap (E := E) s Jdx := by
  classical
  ext v
  have hexpand : ∀ k : Fin s,
      v k = ∑ i : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).coord i) (v k) • chartModelBasis E i := by
    intro k
    have hrep := (chartModelBasis E).sum_repr (v k)
    conv_lhs => rw [← hrep]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Module.Basis.coord_apply]
  have h_v_eq : v =
      fun k : Fin s => ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).coord i) (v k) • chartModelBasis E i := by
    funext k; exact hexpand k
  rw [show f v = f (fun k : Fin s =>
        ∑ i : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).coord i) (v k) • chartModelBasis E i) from
    congrArg f h_v_eq]
  rw [ContinuousMultilinearMap.map_sum
    (f := f)
    (g := fun (k : Fin s) (i : Fin (Module.finrank ℝ E)) =>
      ((chartModelBasis E).coord i) (v k) • chartModelBasis E i)]
  have h_pull : ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
      f (fun k : Fin s =>
          ((chartModelBasis E).coord (Jdx k)) (v k) • chartModelBasis E (Jdx k)) =
        (∏ k : Fin s, ((chartModelBasis E).coord (Jdx k)) (v k)) *
          f (fun k : Fin s => chartModelBasis E (Jdx k)) := by
    intro Jdx
    have hpull := f.toMultilinearMap.map_smul_univ
      (c := fun k : Fin s => ((chartModelBasis E).coord (Jdx k)) (v k))
      (m := fun k : Fin s => chartModelBasis E (Jdx k))
    have hpull' :
        f (fun k : Fin s => ((chartModelBasis E).coord (Jdx k)) (v k) •
            chartModelBasis E (Jdx k)) =
        (∏ k : Fin s, ((chartModelBasis E).coord (Jdx k)) (v k)) •
          f (fun k : Fin s => chartModelBasis E (Jdx k)) := hpull
    rw [hpull']
    rfl
  rw [show ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        f (fun k : Fin s =>
            ((chartModelBasis E).coord (Jdx k)) (v k) • chartModelBasis E (Jdx k)) =
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        (∏ k : Fin s, ((chartModelBasis E).coord (Jdx k)) (v k)) *
          f (fun k : Fin s => chartModelBasis E (Jdx k)) from
    Finset.sum_congr rfl (fun Jdx _ => h_pull Jdx)]
  have h_rhs_eq :
      (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          f (fun k : Fin s => chartModelBasis E (Jdx k)) •
            dualCoordinateProductMultilinearMap (E := E) s Jdx) v =
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          f (fun k : Fin s => chartModelBasis E (Jdx k)) *
            (∏ k : Fin s, ((chartModelBasis E).coord (Jdx k)) (v k)) := by
    classical
    rw [show (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            f (fun k : Fin s => chartModelBasis E (Jdx k)) •
              dualCoordinateProductMultilinearMap (E := E) s Jdx) v =
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (f (fun k : Fin s => chartModelBasis E (Jdx k)) •
              dualCoordinateProductMultilinearMap (E := E) s Jdx) v from
      ContinuousMultilinearMap.sum_apply
        (fun Jdx : Fin s → Fin (Module.finrank ℝ E) =>
          f (fun k : Fin s => chartModelBasis E (Jdx k)) •
            dualCoordinateProductMultilinearMap (E := E) s Jdx) v]
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [ContinuousMultilinearMap.smul_apply,
      dualCovariantCMM_apply (E := E) s Jdx v]
    rfl
  rw [h_rhs_eq]
  refine Finset.sum_congr rfl ?_
  intro Jdx _
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorRSModel_eq_sum_basis (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    T = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx T •
              tensorChartBasisElement (E := E) r s Idx Jdx := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro w
  have hw := cmm_eq_sum_basis_coeffs (E := E) r w
  set c : (Fin r → Fin (Module.finrank ℝ E)) → ℝ := fun Idx =>
    w (fun k : Fin r => chartModelBasis E (Idx k)) with hc_def
  have hw' : w = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      c Idx • dualCoordinateProductMultilinearMap (E := E) r Idx := hw
  have hT : T w = ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      c Idx • T (dualCoordinateProductMultilinearMap (E := E) r Idx) := by
    conv_lhs => rw [hw']
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    rw [map_smul]
  rw [hT]
  have hT_inner : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      T (dualCoordinateProductMultilinearMap (E := E) r Idx) =
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          T (dualCoordinateProductMultilinearMap (E := E) r Idx)
              (fun k : Fin s => chartModelBasis E (Jdx k)) •
            dualCoordinateProductMultilinearMap (E := E) s Jdx := fun Idx =>
    cmm_eq_sum_basis_coeffs (E := E) s (T (dualCoordinateProductMultilinearMap (E := E) r Idx))
  have hrhs :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx T •
              tensorChartBasisElement (E := E) r s Idx Jdx) w =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx T •
              (tensorChartBasisElement (E := E) r s Idx Jdx w) := by
    classical
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rfl
  rw [hrhs]
  have hrhs_simplified : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx T •
          (tensorChartBasisElement (E := E) r s Idx Jdx w)) =
      c Idx •
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          T (dualCoordinateProductMultilinearMap (E := E) r Idx)
              (fun k : Fin s => chartModelBasis E (Jdx k)) •
            dualCoordinateProductMultilinearMap (E := E) s Jdx := by
    intro Idx
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [tensorChartBasisElement_apply, tensorChartComponentProjection_apply,
      smul_smul, smul_smul]
    congr 1
    exact mul_comm _ _
  refine Finset.sum_congr rfl ?_
  intro Idx _
  rw [hrhs_simplified Idx, ← hT_inner Idx]

noncomputable def tensorChartBasisNormConstant (r s : ℕ) : ℝ :=
  ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
    ‖tensorChartBasisElement (E := E) r s p.1 p.2‖

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorChartBasisNormConstant_nonneg (r s : ℕ) :
    0 ≤ tensorChartBasisNormConstant (E := E) r s :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorChartBasisElement_norm_le (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ ≤
      tensorChartBasisNormConstant (E := E) r s := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)))))
    (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) =>
      ‖tensorChartBasisElement (E := E) r s p.1 p.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (Idx, Jdx))
  exact h

noncomputable def tensorTrivProj
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (x : M) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x
      (S.toSection x)

noncomputable def tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (x : M) : ℝ :=
  tensorChartComponentProjection (E := E) r s Idx Jdx
    (tensorTrivProj (I := I) (M := M) g r s S α x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma tensorChartComponentRaw_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (x : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x =
      tensorChartComponentProjection (E := E) r s Idx Jdx
        (tensorTrivProj (I := I) (M := M) g r s S α x) := rfl

noncomputable def tensorChartComponentPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (x : M) : ℝ :=
  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x

end NormedComponents

section EuclideanComponents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  chartPushedRaw (I := I) (M := M) α
    (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartComponent_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx =
      chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) := rfl

section RawComponentSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rs_baseSet_eq_chart_source' (α : M) (r s : ℕ) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet =
      (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_contMDiffOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (tensorTrivProj (I := I) (M := M) g r s S α)
      ((chartAt H α).source) := by
  classical
  have hbase := rs_baseSet_eq_chart_source' (I := I) (M := M) α r s
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  refine ContMDiffOn.congr hrewrite ?_
  intro x hx
  have hx_base : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [hbase]; exact hx
  unfold tensorTrivProj
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x (S.toSection x) = _
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorChartComponentRaw_contMDiffOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((chartAt H α).source) := by
  classical
  have hsmooth := tensorTrivProj_contMDiffOn_chart_source
    (I := I) (M := M) g r s S α
  have hCLM :
      ContMDiff (𝓘(ℝ, TensorRSModel r s ℝ E)) (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentProjection (E := E) r s Idx Jdx) :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).contMDiff
  exact hCLM.comp_contMDiffOn hsmooth

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComponentPou_support_subset_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentPou (I := I) (M := M)
        g r s S α Idx Jdx) ⊆
      (chartAt H α).source := by
  classical
  unfold tensorChartComponentPou
  have hsub :
      tsupport (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    have h_eq : (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x) =
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x •
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x) := by
      funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      (g := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
  exact hsub.trans (chartAtlasPOU_isSubordinate (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponentPou_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  intro x
  by_cases hx_chart : x ∈ (chartAt H α).source
  · have hPOU : ContMDiff I (𝓘(ℝ, ℝ)) ∞
        (fun y : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have hRaw_on := tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx
    have hRaw_at : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) x :=
      hRaw_on.contMDiffAt
        (IsOpen.mem_nhds (chartAt H α).open_source hx_chart)
    exact (hPOU.contMDiffAt).mul hRaw_at
  · have hsupp_sub := tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S α Idx Jdx
    have hx_notin : x ∉ tsupport (tensorChartComponentPou (I := I) (M := M)
        g r s S α Idx Jdx) := fun h => hx_chart (hsupp_sub h)
    apply ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : M => (0 : ℝ)) contMDiffAt_const
    have hopen : IsOpen
        (tsupport (tensorChartComponentPou (I := I) (M := M)
          g r s S α Idx Jdx))ᶜ :=
      isClosed_tsupport _ |>.isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have : y ∉ Function.support (tensorChartComponentPou (I := I) (M := M)
        g r s S α Idx Jdx) := by
      intro h_in
      exact hy (subset_tsupport _ h_in)
    have hzero : tensorChartComponentPou (I := I) (M := M)
        g r s S α Idx Jdx y = 0 := by
      by_contra hne
      exact this hne
    exact hzero

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentPou_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport (tensorChartComponentPou (I := I) (M := M)
      g r s S α Idx Jdx) := by
  classical
  have hsub :
      tsupport (tensorChartComponentPou (I := I) (M := M)
        g r s S α Idx Jdx) ⊆
        (Set.univ : Set M) := fun _ _ => trivial
  have hcompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have htsupp_closed : IsClosed (tsupport (tensorChartComponentPou (I := I) (M := M)
      g r s S α Idx Jdx)) := isClosed_tsupport _
  exact (hcompact.of_isClosed_subset htsupp_closed hsub)

end RawComponentSmoothness

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponent_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set f : M → ℝ := tensorChartComponentPou (I := I) (M := M)
    g r s S α Idx Jdx with hf_def
  have hf_smooth : ContMDiff I (𝓘(ℝ, ℝ)) ∞ f :=
    tensorChartComponentPou_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S α Idx Jdx
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_target : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_target
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  rw [contMDiff_iff_contDiff]
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target :
      y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α
    have hformula_smooth :
        ContDiffOn ℝ ∞
          (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
      have hscalar : ContDiffOn ℝ ∞
          (fun z : E => f ((extChartAt I α).symm z))
          (extChartAt I α).target :=
        DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hf_smooth
      have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
        ContinuousLinearEquiv.contDiff _
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)
          (extChartAt I α).target := by
        intro z hz
        rcases hz with ⟨w, hw_target, hwz⟩
        have h_eq : (toEuclidean (E := E)).symm z = w := by
          rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) y := hformula_smooth y hy_target
    have hformula_at : ContDiffAt ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y :=
      hwithin.contDiffAt (hOpen.mem_nhds hy_target)
    refine hformula_at.congr_of_eventuallyEq ?_
    filter_upwards [hOpen.mem_nhds hy_target] with z hz
    have h_apply :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) α f hz
    rw [tensorChartComponent_def, h_apply]
  · have hcarrier_subset_target :
        K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      intro z hz_carrier
      rcases hz_carrier with ⟨w, ⟨x, hx_supp, hxw⟩, hwz⟩
      have hx_src : x ∈ (extChartAt I α).source := hsub_target hx_supp
      have hw_target : w ∈ (extChartAt I α).target := by
        rw [← hxw]; exact (extChartAt I α).map_source hx_src
      exact ⟨w, hw_target, hwz⟩
    have hy_off : y ∉ K := fun hy_in =>
      hy_target (hcarrier_subset_target hy_in)
    have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ))
      contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off] with z hz
    by_cases hz_target :
        z ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
    · obtain ⟨w, hw_target, hwz⟩ := hz_target
      have hz_target' :
          z ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α := ⟨w, hw_target, hwz⟩
      have h_eq : (toEuclidean (E := E)).symm z = w := by
        rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
      have h_apply :=
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) α f hz_target'
      rw [tensorChartComponent_def, h_apply]
      by_contra hne_f
      apply hz
      have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈
          tsupport f := subset_tsupport _ hne_f
      rw [h_eq] at hin_supp
      have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
        (extChartAt I α).right_inv hw_target
      refine ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwz⟩
    · rw [tensorChartComponent_def]
      exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) α f hz_target

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponent_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set f : M → ℝ := tensorChartComponentPou (I := I) (M := M)
    g r s S α Idx Jdx with hf_def
  have hf_supp : tsupport f ⊆ (chartAt H α).source :=
    tensorChartComponentPou_support_subset_chart_source
      (I := I) (M := M) g r s S α Idx Jdx
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f)) with hK_def
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub_src : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_supp hx
  have hcont_chart : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub_src
  have hK_compact_M : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont_chart
  have hK_compact : IsCompact K :=
    hK_compact_M.image (toEuclidean (E := E)).continuous
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  by_cases hy_target :
      y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · rcases hy_target with ⟨w, hw_target, hwy⟩
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    rw [tensorChartComponent_def]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f ⟨w, hw_target, hwy⟩]
    by_contra hne_f
    apply hyK
    have hin_supp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        tsupport f := by
      apply subset_tsupport
      exact hne_f
    rw [h_eq] at hin_supp
    have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
      (extChartAt I α).right_inv hw_target
    exact ⟨w, ⟨(extChartAt I α).symm w, hin_supp, hext_right⟩, hwy⟩
  · rw [tensorChartComponent_def]
    exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α f hy_target

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M) (x : M) :
    tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α x =
      tensorTrivProj (I := I) (M := M) g r s S₁ α x +
        tensorTrivProj (I := I) (M := M) g r s S₂ α x := by
  unfold tensorTrivProj
  rw [show (S₁ + S₂).toSection x = S₁.toSection x + S₂.toSection x from
    by rw [SmoothCcTensor.toSection_add]; rfl]
  exact map_add _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M) (x : M) :
    tensorTrivProj (I := I) (M := M) g r s (c • S) α x =
      c • tensorTrivProj (I := I) (M := M) g r s S α x := by
  unfold tensorTrivProj
  rw [show (c • S).toSection x = c • S.toSection x from
    by rw [SmoothCcTensor.toSection_smul]; rfl]
  exact map_smul _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx x =
      tensorChartComponentRaw (I := I) (M := M) g r s S₁ α Idx Jdx x +
        tensorChartComponentRaw (I := I) (M := M) g r s S₂ α Idx Jdx x := by
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_add (I := I) (M := M) g r s S₁ S₂ α x]
  exact map_add _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    tensorChartComponentRaw (I := I) (M := M) g r s (c • S) α Idx Jdx x =
      c • tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x := by
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_smul (I := I) (M := M) g r s c S α x]
  exact map_smul _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentPou_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentPou (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      tensorChartComponentPou (I := I) (M := M) g r s S₁ α Idx Jdx +
        tensorChartComponentPou (I := I) (M := M) g r s S₂ α Idx Jdx := by
  funext x
  unfold tensorChartComponentPou
  rw [tensorChartComponentRaw_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx x,
    Pi.add_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentPou_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentPou (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx := by
  funext x
  unfold tensorChartComponentPou
  rw [tensorChartComponentRaw_smul (I := I) (M := M) g r s c S α Idx Jdx x,
    Pi.smul_apply]
  change _ * (c * _) = c * (_ * _)
  ring

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_add_fn (α : M) (u₁ u₂ : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I)
        (M := M) α (u₁ + u₂) =
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I)
          (M := M) α u₁ +
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I)
          (M := M) α u₂ := by
  funext y
  rw [Pi.add_apply]
  by_cases hy :
      y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy]
    rfl
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy]
    ring

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_smul_fn (α : M) (c : ℝ) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I)
        (M := M) α (c • u) =
      c • DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw (I := I)
        (M := M) α u := by
  funext y
  rw [Pi.smul_apply]
  by_cases hy :
      y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy]
    rfl
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy]
    change (0 : ℝ) = c * 0
    ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponent_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponent (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      tensorChartComponent (I := I) (M := M) g r s S₁ α Idx Jdx +
        tensorChartComponent (I := I) (M := M) g r s S₂ α Idx Jdx := by
  unfold tensorChartComponent
  rw [tensorChartComponentPou_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx,
    chartPushedRaw_add_fn (I := I) (M := M) α]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponent_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponent (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := by
  unfold tensorChartComponent
  rw [tensorChartComponentPou_smul (I := I) (M := M) g r s c S α Idx Jdx,
    chartPushedRaw_smul_fn (I := I) (M := M) α]

noncomputable def tensorChartPushedRawModel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    TensorRSModel r s ℝ E := by
  classical
  exact
    if y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α then
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) •
        tensorTrivProj (I := I) (M := M) g r s S α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartPushedRawModel_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    tensorChartPushedRawModel (I := I) (M := M) g r s S α y =
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) •
        tensorTrivProj (I := I) (M := M) g r s S α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold tensorChartPushedRawModel
  exact if_pos hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartPushedRawModel_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    tensorChartPushedRawModel (I := I) (M := M) g r s S α y = 0 := by
  classical
  unfold tensorChartPushedRawModel
  exact if_neg hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartPushedRaw_eq_sum_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushedRawModel (I := I) (M := M) g r s S α y =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx y •
            tensorChartBasisElement (E := E) r s Idx Jdx := by
  classical
  by_cases hy :
      y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · rw [tensorChartPushedRawModel_apply_of_mem
      (I := I) (M := M) g r s S α hy]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have hexpand := tensorRSModel_eq_sum_basis (E := E) r s
      (tensorTrivProj (I := I) (M := M) g r s S α x)
    have hscaled :
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x •
            tensorTrivProj (I := I) (M := M) g r s S α x =
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
                tensorChartComponentProjection (E := E) r s Idx Jdx
                  (tensorTrivProj (I := I) (M := M) g r s S α x)) •
                tensorChartBasisElement (E := E) r s Idx Jdx := by
      rw [show (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x •
            tensorTrivProj (I := I) (M := M) g r s S α x =
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x •
            (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                tensorChartComponentProjection (E := E) r s Idx Jdx
                    (tensorTrivProj (I := I) (M := M) g r s S α x) •
                  tensorChartBasisElement (E := E) r s Idx Jdx) from
        by rw [← hexpand]]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro Idx _
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro Jdx _
      rw [smul_smul]
    rw [hscaled]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [tensorChartComponent_def]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy]
    rfl
  · rw [tensorChartPushedRawModel_apply_of_notMem
      (I := I) (M := M) g r s S α hy]
    symm
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    rw [tensorChartComponent_def]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy]
    rw [zero_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartPushedRaw_norm_sq_le_sum_tensorChartComponent_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g r s,
        ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
          ‖tensorChartPushedRawModel (I := I) (M := M) g r s S α y‖^2 ≤
            C * ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                  ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                    (tensorChartComponent (I := I) (M := M)
                        g r s S α Idx Jdx y)^2 := by
  classical
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  set Ncard : ℕ := V.card with hN_def
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nonneg : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  refine ⟨(Ncard : ℝ) * Bnorm ^ 2, ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  intro S y
  set u : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ := fun p =>
    tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y with hu_def
  have hrec :
      tensorChartPushedRawModel (I := I) (M := M) g r s S α y =
        ∑ p ∈ V, u p •
          tensorChartBasisElement (E := E) r s p.1 p.2 := by
    rw [chartPushedRaw_eq_sum_tensorChartComponent
      (I := I) (M := M) g r s S α y]
    rw [show V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
        (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) from
      Finset.univ_product_univ.symm]
    rw [Finset.sum_product (s := (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))))
            (t := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
            (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E)) =>
              u p • tensorChartBasisElement (E := E) r s p.1 p.2)]
  have h_norm_le : ‖tensorChartPushedRawModel (I := I) (M := M) g r s S α y‖ ≤
      ∑ p ∈ V, |u p| * Bnorm := by
    rw [hrec]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro p _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (tensorChartBasisElement_norm_le (E := E) r s p.1 p.2) (abs_nonneg _)
  have h_factor : (∑ p ∈ V, |u p| * Bnorm) = (∑ p ∈ V, |u p|) * Bnorm := by
    rw [Finset.sum_mul]
  rw [h_factor] at h_norm_le
  have h_lhs_nonneg :
      0 ≤ ‖tensorChartPushedRawModel (I := I) (M := M) g r s S α y‖ := norm_nonneg _
  have h_sum_abs_nonneg : 0 ≤ ∑ p ∈ V, |u p| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_rhs_nonneg : 0 ≤ (∑ p ∈ V, |u p|) * Bnorm :=
    mul_nonneg h_sum_abs_nonneg hBnorm_nonneg
  have h_norm_sq : ‖tensorChartPushedRawModel (I := I) (M := M) g r s S α y‖^2 ≤
      ((∑ p ∈ V, |u p|) * Bnorm) ^ 2 := by
    have hmul := mul_le_mul h_norm_le h_norm_le h_lhs_nonneg h_rhs_nonneg
    simpa [sq] using hmul
  have hCS : (∑ p ∈ V, |u p|) ^ 2 ≤ (Ncard : ℝ) * ∑ p ∈ V, (u p) ^ 2 := by
    have hbase :
        (∑ p ∈ V, (1 : ℝ) * |u p|) ^ 2 ≤
          (∑ p ∈ V, (1 : ℝ) ^ 2) * ∑ p ∈ V, |u p| ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq V (fun _ => (1 : ℝ)) (fun p => |u p|)
    have h1 : (∑ p ∈ V, (1 : ℝ) * |u p|) = ∑ p ∈ V, |u p| := by
      refine Finset.sum_congr rfl ?_
      intro p _; ring
    have h2 : (∑ p ∈ V, (1 : ℝ) ^ 2) = (Ncard : ℝ) := by
      simp [Ncard, V]
    have h3 : (∑ p ∈ V, |u p| ^ 2) = (∑ p ∈ V, (u p) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro p _
      rw [sq_abs]
    rw [h1, h2, h3] at hbase
    exact hbase
  have hBnorm_sq_nonneg : 0 ≤ Bnorm ^ 2 := sq_nonneg _
  have hCS_mul :
      (∑ p ∈ V, |u p|) ^ 2 * Bnorm ^ 2 ≤
        (Ncard : ℝ) * (∑ p ∈ V, (u p) ^ 2) * Bnorm ^ 2 :=
    mul_le_mul_of_nonneg_right hCS hBnorm_sq_nonneg
  have h_sq_eq : ((∑ p ∈ V, |u p|) * Bnorm) ^ 2 =
      (∑ p ∈ V, |u p|) ^ 2 * Bnorm ^ 2 := by ring
  rw [h_sq_eq] at h_norm_sq
  have h_double_sum_eq :
      (∑ p ∈ V, (u p) ^ 2) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponent (I := I) (M := M)
              g r s S α Idx Jdx y) ^ 2 := by
    rw [show V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
        (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) from
      Finset.univ_product_univ.symm]
    rw [Finset.sum_product (s := (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))))
      (t := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
      (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)) => (u p) ^ 2)]
  have h_const_eq : (Ncard : ℝ) * (∑ p ∈ V, (u p) ^ 2) * Bnorm ^ 2 =
      ((Ncard : ℝ) * Bnorm ^ 2) *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponent (I := I) (M := M)
              g r s S α Idx Jdx y) ^ 2 := by
    rw [h_double_sum_eq]; ring
  rw [h_const_eq] at hCS_mul
  exact le_trans h_norm_sq hCS_mul

end EuclideanComponents

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
