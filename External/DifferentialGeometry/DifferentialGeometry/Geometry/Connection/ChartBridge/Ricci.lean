import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Connection.ChartBridge.Riemann
import DifferentialGeometry.Geometry.Curvature.Riemann.Ricci

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

def chartRiemannBasisIdentity (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  ∀ i j k l : Fin (Module.finrank ℝ E),
    ((chartModelBasis E).repr
        (riemannOp (cov := LeviCivita (I := I) g) x
          ((chartModelBasis E) j) ((chartModelBasis E) k)
          ((chartModelBasis E) i))) l =
      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartRiemannBasisIdentity_iff (g : SmoothRiemannianMetric I M) (x : M) :
    chartRiemannBasisIdentity (I := I) g x ↔
      ∀ i j k : Fin (Module.finrank ℝ E),
        riemannOp (cov := LeviCivita (I := I) g) x
            ((chartModelBasis E) j) ((chartModelBasis E) k)
            ((chartModelBasis E) i) =
          chartRiemannCLM (I := I) g x
            ((chartModelBasis E) j) ((chartModelBasis E) k)
            ((chartModelBasis E) i) := by
  classical
  constructor
  · intro h i j k
    apply (chartModelBasis E).repr.injective
    ext l
    rw [h i j k]
    rw [chartRiemannCLM_repr_basis (I := I) g x i j k l]
  · intro h i j k l
    rw [h i j k]
    rw [chartRiemannCLM_repr_basis (I := I) g x i j k l]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannOp_eq_chartRiemannCLM_apply_of_basis_identity
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) g) x v w u =
      chartRiemannCLM (I := I) g x v w u := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  have hbasis := (chartRiemannBasisIdentity_iff (I := I) g x).mp h
  have hv : v = ∑ j : Fin (Module.finrank ℝ E), b.repr v j • b j :=
    (Module.Basis.sum_repr b v).symm
  have hw : w = ∑ k : Fin (Module.finrank ℝ E), b.repr w k • b k :=
    (Module.Basis.sum_repr b w).symm
  have hu : u = ∑ i : Fin (Module.finrank ℝ E), b.repr u i • b i :=
    (Module.Basis.sum_repr b u).symm
  have hLHS : riemannOp (cov := LeviCivita (I := I) g) x v w u =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k * b.repr u i) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) (b i) := by
    have h1 : riemannOp (cov := LeviCivita (I := I) g) x v =
        ∑ j : Fin (Module.finrank ℝ E),
          b.repr v j • riemannOp (cov := LeviCivita (I := I) g) x (b j) := by
      conv_lhs => rw [hv]
      set f : TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          riemannOp (cov := LeviCivita (I := I) g) x with hf_def
      change f (∑ j : Fin (Module.finrank ℝ E), b.repr v j • b j) =
          ∑ j : Fin (Module.finrank ℝ E), b.repr v j • f (b j)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact f.map_smul (b.repr v j) (b j)
    have h2 : riemannOp (cov := LeviCivita (I := I) g) x v w =
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) := by
      rw [h1, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h_smul : (b.repr v j • riemannOp (cov := LeviCivita (I := I) g) x (b j)) w =
          b.repr v j • riemannOp (cov := LeviCivita (I := I) g) x (b j) w := rfl
      rw [h_smul]
      have h_inner : riemannOp (cov := LeviCivita (I := I) g) x (b j) w =
          ∑ k : Fin (Module.finrank ℝ E),
            b.repr w k • riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) := by
        conv_lhs => rw [hw]
        set f : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          riemannOp (cov := LeviCivita (I := I) g) x (b j) with hf_def
        change f (∑ k : Fin (Module.finrank ℝ E), b.repr w k • b k) =
            ∑ k : Fin (Module.finrank ℝ E), b.repr w k • f (b k)
        rw [map_sum f]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact f.map_smul (b.repr w k) (b k)
      rw [h_inner, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
    rw [h2]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h_smul :
        ((b.repr v j * b.repr w k) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k)) u =
        (b.repr v j * b.repr w k) •
            riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) u := rfl
    rw [h_smul]
    have h_inner : riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) u =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr u i • riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) (b i) := by
      conv_lhs => rw [hu]
      set f : TangentSpace I x →L[ℝ] TangentSpace I x :=
        riemannOp (cov := LeviCivita (I := I) g) x (b j) (b k) with hf_def
      change f (∑ i : Fin (Module.finrank ℝ E), b.repr u i • b i) =
          ∑ i : Fin (Module.finrank ℝ E), b.repr u i • f (b i)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact f.map_smul (b.repr u i) (b i)
    rw [h_inner, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
  have hRHS : chartRiemannCLM (I := I) g x v w u =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k * b.repr u i) •
            chartRiemannCLM (I := I) g x (b j) (b k) (b i) := by
    have h1 : chartRiemannCLM (I := I) g x v =
        ∑ j : Fin (Module.finrank ℝ E),
          b.repr v j • chartRiemannCLM (I := I) g x (b j) := by
      conv_lhs => rw [hv]
      set f : TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          chartRiemannCLM (I := I) g x with hf_def
      change f (∑ j : Fin (Module.finrank ℝ E), b.repr v j • b j) =
          ∑ j : Fin (Module.finrank ℝ E), b.repr v j • f (b j)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact f.map_smul (b.repr v j) (b j)
    have h2 : chartRiemannCLM (I := I) g x v w =
        ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          (b.repr v j * b.repr w k) • chartRiemannCLM (I := I) g x (b j) (b k) := by
      rw [h1, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h_smul : (b.repr v j • chartRiemannCLM (I := I) g x (b j)) w =
          b.repr v j • chartRiemannCLM (I := I) g x (b j) w := rfl
      rw [h_smul]
      have h_inner : chartRiemannCLM (I := I) g x (b j) w =
          ∑ k : Fin (Module.finrank ℝ E),
            b.repr w k • chartRiemannCLM (I := I) g x (b j) (b k) := by
        conv_lhs => rw [hw]
        set f : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          chartRiemannCLM (I := I) g x (b j) with hf_def
        change f (∑ k : Fin (Module.finrank ℝ E), b.repr w k • b k) =
            ∑ k : Fin (Module.finrank ℝ E), b.repr w k • f (b k)
        rw [map_sum f]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact f.map_smul (b.repr w k) (b k)
      rw [h_inner, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]
    rw [h2, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h_smul : ((b.repr v j * b.repr w k) • chartRiemannCLM (I := I) g x (b j) (b k)) u =
        (b.repr v j * b.repr w k) • chartRiemannCLM (I := I) g x (b j) (b k) u := rfl
    rw [h_smul]
    have h_inner : chartRiemannCLM (I := I) g x (b j) (b k) u =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr u i • chartRiemannCLM (I := I) g x (b j) (b k) (b i) := by
      conv_lhs => rw [hu]
      set f : TangentSpace I x →L[ℝ] TangentSpace I x :=
        chartRiemannCLM (I := I) g x (b j) (b k) with hf_def
      change f (∑ i : Fin (Module.finrank ℝ E), b.repr u i • b i) =
          ∑ i : Fin (Module.finrank ℝ E), b.repr u i • f (b i)
      rw [map_sum f]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact f.map_smul (b.repr u i) (b i)
    rw [h_inner, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbasis i j k]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_eq_chartRicciSwap_of_basis_identity
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) k *
            ((chartModelBasis E).repr w) i *
            chartRicciTensor (I := I) g x i k (extChartAt I x x) := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  rw [ricciTensor_apply_basisSum]
  have hrewrite_term : ∀ t : Fin (Module.finrank ℝ E),
      (b.repr (riemannOp (cov := LeviCivita (I := I) g) x (b t) v w)) t =
        (b.repr (chartRiemannCLM (I := I) g x (b t) v w)) t := by
    intro t
    rw [riemannOp_eq_chartRiemannCLM_apply_of_basis_identity (I := I) g x h (b t) v w]
  have h_chart_term : ∀ t : Fin (Module.finrank ℝ E),
      (b.repr (chartRiemannCLM (I := I) g x (b t) v w)) t =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (b.repr w) i * (b.repr v) k *
              chartRiemannTensor (I := I) g x i t k t (extChartAt I x x) := by
    intro t
    rw [chartRiemannCLM_apply]
    rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
    have h_smul_repr : ∀ (c : ℝ) (l : Fin (Module.finrank ℝ E)),
        ((b.repr (c • (b l : E))) t : ℝ) = c * (if l = t then (1 : ℝ) else 0) := by
      intro c l
      rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [Module.Basis.repr_self_apply]
    rw [Finset.sum_eq_single t]
    · rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      rw [Finset.sum_eq_single t]
      · rw [h_smul_repr]
        rw [if_pos rfl, mul_one]
        rw [show ((b.repr (b t)) t : ℝ) = 1 by
          rw [Module.Basis.repr_self_apply]; rw [if_pos rfl]]
        ring
      · intro l _ hl_ne
        rw [h_smul_repr]
        rw [if_neg hl_ne, mul_zero]
      · intro hl
        exact absurd (Finset.mem_univ t) hl
    · intro j _ hj_ne
      rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [map_sum]; rw [Finsupp.coe_finset_sum]; rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [h_smul_repr]
      have htj : ¬ (t = j) := fun h => hj_ne h.symm
      rw [show ((b.repr (b t)) j : ℝ) = 0 by
        rw [Module.Basis.repr_self_apply]; rw [if_neg htj]]
      ring
    · intro hj
      exact absurd (Finset.mem_univ t) hj
  have h_combined : ∀ t : Fin (Module.finrank ℝ E),
      (b.repr (riemannOp (cov := LeviCivita (I := I) g) x (b t) v w)) t =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (b.repr w) i * (b.repr v) k *
              chartRiemannTensor (I := I) g x i t k t (extChartAt I x x) := by
    intro t
    rw [hrewrite_term t, h_chart_term t]
  rw [Finset.sum_congr rfl (fun t _ => h_combined t)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chartRicciTensor_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciFun_eq_ricciTensor_swap_of_basis_identity
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w : TangentSpace I x) :
    ricciFun (I := I) g x v w = ricciTensor (I := I) g x w v := by
  classical
  rw [ricciFun_apply, ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I) g x h]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciFun_eq_ricciTensor_of_basis_identity [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (h : chartRiemannBasisIdentity (I := I) g x)
    (v w : TangentSpace I x) :
    ricciFun (I := I) g x v w = ricciTensor (I := I) g x v w := by
  classical
  rw [ricciFun_eq_ricciTensor_swap_of_basis_identity (I := I) g x h v w]
  exact ricciTensor_symm (I := I) g x w v

end Connection
end Integral
end DifferentialGeometry
