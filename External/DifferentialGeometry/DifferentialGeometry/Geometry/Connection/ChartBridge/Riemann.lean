import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs


noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace
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

def chartRiemannLin (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := {
    toFun := fun w => {
      toFun := fun u =>
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ((chartModelBasis E).repr u i *
                    (chartModelBasis E).repr v j *
                    (chartModelBasis E).repr w k *
                    chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                  ((chartModelBasis E) l : TangentSpace I x)
      map_add' := fun u₁ u₂ => by
        classical
        have hrepr : (chartModelBasis E).repr (u₁ + u₂) =
            (chartModelBasis E).repr u₁ + (chartModelBasis E).repr u₂ := map_add _ _ _
        simp only [hrepr]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        simp only [Finsupp.coe_add, Pi.add_apply]
        rw [show ((((chartModelBasis E).repr u₁) i + ((chartModelBasis E).repr u₂) i) *
              ((chartModelBasis E).repr v) j * ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
            (((chartModelBasis E).repr u₁) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) +
            (((chartModelBasis E).repr u₂) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
        exact add_smul _ _ _
      map_smul' := fun c u => by
        classical
        have hrepr : (chartModelBasis E).repr (c • u) =
            c • (chartModelBasis E).repr u := map_smul _ _ _
        simp only [hrepr]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        rw [show (c * ((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
              c * (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
        exact mul_smul _ _ _
    }
    map_add' := fun w₁ w₂ => by
      classical
      ext u
      have hrepr : (chartModelBasis E).repr (w₁ + w₂) =
          (chartModelBasis E).repr w₁ + (chartModelBasis E).repr w₂ := map_add _ _ _
      change (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr (w₁ + w₂)) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) =
          (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr w₁) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) +
          (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr w₂) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x))
      simp only [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [show (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
              (((chartModelBasis E).repr w₁) k + ((chartModelBasis E).repr w₂) k) *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
            (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w₁) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) +
            (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w₂) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
      exact add_smul _ _ _
    map_smul' := fun c w => by
      classical
      ext u
      have hrepr : (chartModelBasis E).repr (c • w) =
          c • (chartModelBasis E).repr w := map_smul _ _ _
      change (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr (c • w)) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) =
          c • (∑ i, ∑ j, ∑ k, ∑ l,
              (((chartModelBasis E).repr u) i *
                  ((chartModelBasis E).repr v) j *
                  ((chartModelBasis E).repr w) k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x))
      simp only [hrepr]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [show (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
              (c * ((chartModelBasis E).repr w) k) *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
            c * (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
      exact mul_smul _ _ _
  }
  map_add' := fun v₁ v₂ => by
    classical
    ext w u
    have hrepr : (chartModelBasis E).repr (v₁ + v₂) =
        (chartModelBasis E).repr v₁ + (chartModelBasis E).repr v₂ := map_add _ _ _
    change (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr (v₁ + v₂)) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x)) =
        (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr v₁) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x)) +
        (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr v₂) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x))
    simp only [hrepr]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [show (((chartModelBasis E).repr u) i *
            (((chartModelBasis E).repr v₁) j + ((chartModelBasis E).repr v₂) j) *
            ((chartModelBasis E).repr w) k *
            chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
          (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v₁) j *
              ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) +
          (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v₂) j *
              ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
    exact add_smul _ _ _
  map_smul' := fun c v => by
    classical
    ext w u
    have hrepr : (chartModelBasis E).repr (c • v) =
        c • (chartModelBasis E).repr v := map_smul _ _ _
    change (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr (c • v)) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x)) =
        c • (∑ i, ∑ j, ∑ k, ∑ l,
            (((chartModelBasis E).repr u) i *
                ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x))
    simp only [hrepr]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [show (((chartModelBasis E).repr u) i * (c * ((chartModelBasis E).repr v) j) *
            ((chartModelBasis E).repr w) k *
            chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
          c * (((chartModelBasis E).repr u) i * ((chartModelBasis E).repr v) j *
              ((chartModelBasis E).repr w) k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
    exact mul_smul _ _ _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartRiemannLin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannLin (I := I) g x v w u =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) := rfl

def chartRiemannCLM (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  let outer : TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
    { toFun := fun v =>
        let mid : TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
          { toFun := fun w =>
              LinearMap.toContinuousLinearMap (chartRiemannLin (I := I) g x v w)
            map_add' := fun w₁ w₂ => by
              ext u; change chartRiemannLin (I := I) g x v (w₁ + w₂) u = _
              rw [map_add]; rfl
            map_smul' := fun c w => by
              ext u; change chartRiemannLin (I := I) g x v (c • w) u = _
              rw [map_smul]; rfl }
        LinearMap.toContinuousLinearMap mid
      map_add' := fun v₁ v₂ => by
        ext w u
        change chartRiemannLin (I := I) g x (v₁ + v₂) w u = _
        rw [map_add]; rfl
      map_smul' := fun c v => by
        ext w u
        change chartRiemannLin (I := I) g x (c • v) w u = _
        rw [map_smul]; rfl }
  LinearMap.toContinuousLinearMap outer

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem chartRiemannCLM_apply_eq_chartRiemannLin
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v w u = chartRiemannLin (I := I) g x v w u := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRiemannCLM_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v w u =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) :=
  chartRiemannLin_apply (I := I) g x v w u

omit [NeZero (Module.finrank ℝ E)] in
private lemma repr_basis_eq_kron (a b' : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr ((chartModelBasis E) a)) b' =
      (if a = b' then (1 : ℝ) else 0) :=
  Module.Basis.repr_self_apply _ _ _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRiemannCLM_basis_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartRiemannCLM (I := I) g x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) •
          ((chartModelBasis E) l : TangentSpace I x) := by
  classical
  rw [chartRiemannCLM_apply]
  have hkron :
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k' : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
                  ((chartModelBasis E).repr ((chartModelBasis E) j)) j' *
                  ((chartModelBasis E).repr ((chartModelBasis E) k)) k' *
                  chartRiemannTensor (I := I) g x i' j' k' l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k' : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((if i = i' then (1 : ℝ) else 0) *
                  (if j = j' then (1 : ℝ) else 0) *
                  (if k = k' then (1 : ℝ) else 0) *
                  chartRiemannTensor (I := I) g x i' j' k' l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) := by
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [repr_basis_eq_kron, repr_basis_eq_kron, repr_basis_eq_kron]
  rw [hkron]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · refine Finset.sum_congr rfl (fun l _ => ?_)
        simp
      · intro k' _ hk_ne
        refine Finset.sum_eq_zero (fun l _ => ?_)
        have hkk' : ¬ k = k' := fun h => hk_ne h.symm
        simp [hkk']
      · intro hk; exact absurd (Finset.mem_univ _) hk
    · intro j' _ hj_ne
      refine Finset.sum_eq_zero (fun k' _ => Finset.sum_eq_zero (fun l _ => ?_))
      have hjj' : ¬ j = j' := fun h => hj_ne h.symm
      simp [hjj']
    · intro hj; exact absurd (Finset.mem_univ _) hj
  · intro i' _ hi_ne
    refine Finset.sum_eq_zero (fun j' _ =>
      Finset.sum_eq_zero (fun k' _ => Finset.sum_eq_zero (fun l _ => ?_)))
    have hii' : ¬ i = i' := fun h => hi_ne h.symm
    simp [hii']
  · intro hi; exact absurd (Finset.mem_univ _) hi

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRiemannCLM_repr_basis (g : SmoothRiemannianMetric I M) (x : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        (chartRiemannCLM (I := I) g x
          ((chartModelBasis E) j) ((chartModelBasis E) k)
          ((chartModelBasis E) i))) l =
      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) := by
  classical
  rw [chartRiemannCLM_basis_apply]
  rw [map_sum]
  rw [Finsupp.coe_finset_sum]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single l]
  · rw [LinearEquiv.map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self_apply, smul_eq_mul, if_pos rfl, mul_one]
  · intro l' _ hl_ne
    rw [LinearEquiv.map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self_apply, smul_eq_mul]
    have h_neg : ¬ l' = l := hl_ne
    rw [if_neg h_neg, mul_zero]
  · intro hl; exact absurd (Finset.mem_univ _) hl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannCLM_antisymm_jk (g : SmoothRiemannianMetric I M) (x : M)
    (v w u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v w u = - chartRiemannCLM (I := I) g x w v u := by
  classical
  rw [chartRiemannCLM_apply, chartRiemannCLM_apply]
  have key : ∀ i j k l : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr u i *
          (chartModelBasis E).repr w k *
          (chartModelBasis E).repr v j *
          chartRiemannTensor (I := I) g x i k j l (extChartAt I x x)) •
        ((chartModelBasis E) l : TangentSpace I x) =
      -(((chartModelBasis E).repr u i *
          (chartModelBasis E).repr v j *
          (chartModelBasis E).repr w k *
          chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
        ((chartModelBasis E) l : TangentSpace I x)) := by
    intro i j k l
    rw [show chartRiemannTensor (I := I) g x i k j l (extChartAt I x x) =
          - chartRiemannTensor (I := I) g x i j k l (extChartAt I x x) from
        chartRiemannTensor_antisymm_jk (I := I) g x i k j l _]
    rw [show ((chartModelBasis E).repr u i *
            (chartModelBasis E).repr w k *
            (chartModelBasis E).repr v j *
            -chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) =
          -((chartModelBasis E).repr u i *
              (chartModelBasis E).repr v j *
              (chartModelBasis E).repr w k *
              chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) from by ring]
    rw [neg_smul]
  have hRHS_to_neg_LHS :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr w j *
                  (chartModelBasis E).repr v k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x) =
      -(∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) := by
    have step1 : ∀ i : Fin (Module.finrank ℝ E),
        (∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr w j *
                  (chartModelBasis E).repr v k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) =
        -(∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr u i *
                  (chartModelBasis E).repr v j *
                  (chartModelBasis E).repr w k *
                  chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                ((chartModelBasis E) l : TangentSpace I x)) := by
      intro i
      rw [Finset.sum_comm
        (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (f := fun j k =>
          ∑ l : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr u i *
                (chartModelBasis E).repr w j *
                (chartModelBasis E).repr v k *
                chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
              ((chartModelBasis E) l : TangentSpace I x))]
      rw [show ∑ k : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w j *
                      (chartModelBasis E).repr v k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x) =
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w k *
                      (chartModelBasis E).repr v j *
                      chartRiemannTensor (I := I) g x i k j l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x) from by
        rw [Finset.sum_comm]]
      rw [show ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w k *
                      (chartModelBasis E).repr v j *
                      chartRiemannTensor (I := I) g x i k j l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x) =
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  -(((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr v j *
                      (chartModelBasis E).repr w k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x)) from by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun l _ => ?_)
        exact key i j k l]
      simp only [Finset.sum_neg_distrib]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr w j *
                      (chartModelBasis E).repr v k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x)) =
          ∑ i : Fin (Module.finrank ℝ E),
            -(∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr u i *
                      (chartModelBasis E).repr v j *
                      (chartModelBasis E).repr w k *
                      chartRiemannTensor (I := I) g x i j k l (extChartAt I x x)) •
                    ((chartModelBasis E) l : TangentSpace I x)) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact step1 i]
    simp only [Finset.sum_neg_distrib]
  rw [hRHS_to_neg_LHS]
  abel

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannCLM_basis_antisymm_jk (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartRiemannCLM (I := I) g x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      - chartRiemannCLM (I := I) g x
          ((chartModelBasis E) k) ((chartModelBasis E) j)
          ((chartModelBasis E) i) :=
  chartRiemannCLM_antisymm_jk (I := I) g x
    ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannCLM_diag (g : SmoothRiemannianMetric I M) (x : M)
    (v u : TangentSpace I x) :
    chartRiemannCLM (I := I) g x v v u = 0 := by
  have h : chartRiemannCLM (I := I) g x v v u = -chartRiemannCLM (I := I) g x v v u :=
    chartRiemannCLM_antisymm_jk (I := I) g x v v u
  set a := chartRiemannCLM (I := I) g x v v u with ha_def
  have h_add : a + a = 0 := by
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  have h_two_smul : (2 : ℝ) • a = a + a := by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, add_smul, one_smul]
  have h_smul_zero : (2 : ℝ) • a = 0 := h_two_smul.trans h_add
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h_smul_zero).resolve_left htwo

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannOp_chartBasis_via_riemannSec (g : SmoothRiemannianMetric I M) (x : M)
    {X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hX : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (X i)))
    (hXx : ∀ i, X i x = (chartModelBasis E) i)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      riemannSec (LeviCivita (I := I) g) (X j) (X k) (X i) x := by
  rw [show ((chartModelBasis E) j : TangentSpace I x) = X j x from (hXx j).symm,
      show ((chartModelBasis E) k : TangentSpace I x) = X k x from (hXx k).symm,
      show ((chartModelBasis E) i : TangentSpace I x) = X i x from (hXx i).symm]
  exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hX j) (hX k) (hX i)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem riemannSec_chartBasis_swap (g : SmoothRiemannianMetric I M) (x : M)
    (X : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannSec (LeviCivita (I := I) g) (X j) (X k) (X i) x =
      - riemannSec (LeviCivita (I := I) g) (X k) (X j) (X i) x :=
  riemannSec_swap (cov := LeviCivita (I := I) g) (X j) (X k) (X i) x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem riemannSec_chartBasis_diag (g : SmoothRiemannianMetric I M) (x : M)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, TangentSpace I b) :
    riemannSec (LeviCivita (I := I) g) X X Z x = 0 :=
  riemannSec_self_eq_zero (cov := LeviCivita (I := I) g) X Z x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannOp_basis_antisymm_jk (g : SmoothRiemannianMetric I M) (x : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    riemannOp (cov := LeviCivita (I := I) g) x
        ((chartModelBasis E) j) ((chartModelBasis E) k)
        ((chartModelBasis E) i) =
      - riemannOp (cov := LeviCivita (I := I) g) x
          ((chartModelBasis E) k) ((chartModelBasis E) j)
          ((chartModelBasis E) i) :=
  riemannOp_swap (cov := LeviCivita (I := I) g) x
    ((chartModelBasis E) j) ((chartModelBasis E) k) ((chartModelBasis E) i)

end Connection
end Integral
end DifferentialGeometry
