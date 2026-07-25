import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism


noncomputable section

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def nablaChartRiemannCoeff (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s l : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l) y
      + (∑ m : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) g α s q r m y *
            chartChristoffel (I := I) g α p m l y)
      - (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p q m y *
            chartRiemannTensor (I := I) g α s m r l y)
      - (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p r m y *
            chartRiemannTensor (I := I) g α s q m l y)
      - (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p s m y *
            chartRiemannTensor (I := I) g α m q r l y)


omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma partialDeriv_contDiffOn_interior_of_contDiffOn
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior ((extChartAt I α).target : Set E)))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a f)
      (interior ((extChartAt I α).target : Set E)) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hrw : (partialDeriv (E := E) a f) =
      fun y => fderiv ℝ f y ((chartModelBasis E) a) := rfl
  rw [hrw]
  exact hfderiv.clm_apply contDiffOn_const


omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRiemannTensor_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α i j k l)
      (interior ((extChartAt I α).target : Set E)) := by
  classical
  set U : Set E := interior ((extChartAt I α).target : Set E) with hU_def
  have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b c) U :=
    fun a b c => chartChristoffel_contDiffOn_interior (I := I) g α a b c
  have hdΓ1 : ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hΓ i k l) j
  have hdΓ2 : ContDiffOn ℝ ∞
      (partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hΓ i j l) k
  have hΓΓ : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l y *
            chartChristoffel (I := I) g α i k m y -
          chartChristoffel (I := I) g α k m l y *
            chartChristoffel (I := I) g α i j m y)) U := by
    refine ContDiffOn.sum (fun m _ => ?_)
    exact ((hΓ j m l).mul (hΓ i k m)).sub ((hΓ k m l).mul (hΓ i j m))
  have hrw : (chartRiemannTensor (I := I) g α i j k l) =
      fun y : E =>
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y) +
        (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)) := by
    funext y; rw [chartRiemannTensor_def]
  rw [hrw]
  exact (hdΓ1.sub hdΓ2).add hΓΓ


omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nablaChartRiemannCoeff_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (nablaChartRiemannCoeff (I := I) g α p q r s l)
      (interior ((extChartAt I α).target : Set E)) := by
  classical
  set U : Set E := interior ((extChartAt I α).target : Set E) with hU_def
  have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α a b c) U :=
    fun a b c => chartChristoffel_contDiffOn_interior (I := I) g α a b c
  have hR : ∀ a b c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartRiemannTensor (I := I) g α a b c d) U :=
    fun a b c d => chartRiemannTensor_contDiffOn_interior (I := I) g α a b c d
  have hdR : ContDiffOn ℝ ∞
      (partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l)) U :=
    partialDeriv_contDiffOn_interior_of_contDiffOn (I := I) α (hR s q r l) p
  have hsum1 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α s q r m y *
          chartChristoffel (I := I) g α p m l y) U :=
    ContDiffOn.sum (fun m _ => (hR s q r m).mul (hΓ p m l))
  have hsum2 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p q m y *
          chartRiemannTensor (I := I) g α s m r l y) U :=
    ContDiffOn.sum (fun m _ => (hΓ p q m).mul (hR s m r l))
  have hsum3 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p r m y *
          chartRiemannTensor (I := I) g α s q m l y) U :=
    ContDiffOn.sum (fun m _ => (hΓ p r m).mul (hR s q m l))
  have hsum4 : ContDiffOn ℝ ∞
      (fun y : E => ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p s m y *
          chartRiemannTensor (I := I) g α m q r l y) U :=
    ContDiffOn.sum (fun m _ => (hΓ p s m).mul (hR m q r l))
  have hrw : (nablaChartRiemannCoeff (I := I) g α p q r s l) =
      fun y : E =>
        partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l) y
          + (∑ m : Fin (Module.finrank ℝ E),
              chartRiemannTensor (I := I) g α s q r m y *
                chartChristoffel (I := I) g α p m l y)
          - (∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α p q m y *
                chartRiemannTensor (I := I) g α s m r l y)
          - (∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α p r m y *
                chartRiemannTensor (I := I) g α s q m l y)
          - (∑ m : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α p s m y *
                chartRiemannTensor (I := I) g α m q r l y) := rfl
  rw [hrw]
  exact ((((hdR.add hsum1).sub hsum2).sub hsum3).sub hsum4)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_chartBasisVec_alpha_leadingTerm
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (_hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    (LeviCivita (I := I) g).toFun
        (fun b => riemannSec (LeviCivita (I := I) g) Xq Xr Xs b) x (Xp x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r l) (extChartAt I α x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartRiemannTensor (I := I) g α s q r m (extChartAt I α x) *
              chartChristoffel (I := I) g α p m l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hXp_x : Xp x = chartBasisVecFiber (I := I) α p x := hXp_eq x hxU
  set S : Π y : M, TangentSpace I y := fun b => riemannSec cov Xq Xr Xs b with hS_def
  have hS_diff : MDiffAt (T% S) x :=
    (riemannSec_contMDiff (cov := cov) hXq hXr hXs x).mdifferentiableAt (by simp)

  set Rc : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun m y => chartRiemannTensor (I := I) g α s q r m (extChartAt I α y) with hRc_def
  set term : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun m y => Rc m y • chartBasisVecFiber (I := I) α m y with hterm_def
  have hS_eq_sum_on_U : ∀ y ∈ U, S y = ∑ m : Fin (Module.finrank ℝ E), term m y := by
    intro y hy
    have hy_good : y ∈ chartLeviCivitaGoodSet (I := I) α := hU_good hy
    have hSval : S y = riemannSec cov Xq Xr Xs y := rfl
    rw [hSval]

    rw [← riemannOp_apply_smooth (cov := cov) hXq hXr hXs]
    rw [hXq_eq y hy, hXr_eq y hy, hXs_eq y hy]
    rw [riemannOp_chartBasisVec_alpha_eq (I := I) g α s q r hy_good]
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hRc_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (Rc m) x := by
    intro m
    have hR_cda : ContDiffAt ℝ ∞ (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
      have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
        chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
      exact (chartRiemannTensor_contDiffOn_interior (I := I) g α s q r m).contDiffAt
        (isOpen_interior.mem_nhds hxint)
    have hR_d : DifferentiableAt ℝ (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) :=
      hR_cda.differentiableAt (by simp)
    have hR_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
      rw [mdifferentiableAt_iff_differentiableAt]; exact hR_d
    have hphi_mdiff : MDiffAt (extChartAt I α) x :=
      mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
    exact hR_mdiff.comp x hphi_mdiff
  have hframe_diff : ∀ m : Fin (Module.finrank ℝ E),
      MDiffAt (T% (fun y : M => chartBasisVecFiber (I := I) α m y)) x :=
    fun m => chartBasisVec_alpha_mdifferentiableAt (I := I) α m hx
  have hterm_diff : ∀ m : Fin (Module.finrank ℝ E), MDiffAt (T% (term m)) x :=
    fun m => MDifferentiableAt.smul_section (hRc_diff m) (hframe_diff m)
  have hsum_diff :
      MDiffAt (T% fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    MDifferentiableAt.sum_section (s := Finset.univ) (t := term) hterm_diff
  have hS_ev_sum :
      (fun y : M => S y) =ᶠ[𝓝 x]
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) := by
    filter_upwards [hU_open.mem_nhds hxU] with y hy using hS_eq_sum_on_U y hy
  have hcov_S_eq :
      cov.toFun S x =
        cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hS_diff hsum_diff
      Filter.univ_mem hS_ev_sum
  rw [hS_def] at hcov_S_eq ⊢
  rw [hcov_S_eq, hXp_x]
  have hsum_apply :
      (cov.toFun (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) x)
          (chartBasisVecFiber (I := I) α p x) =
        ∑ m : Fin (Module.finrank ℝ E),
          (cov.toFun (term m) x) (chartBasisVecFiber (I := I) α p x) := by
    have hfun :
        (fun y : M => ∑ m : Fin (Module.finrank ℝ E), term m y) =
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum term := by
      funext y; simp
    rw [hfun]
    exact leviCivita_finset_sum_apply (I := I) g
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) term
      (chartBasisVecFiber (I := I) α p x) hterm_diff
  rw [hsum_apply]
  have hleib : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (term m) x) (chartBasisVecFiber (I := I) α p x) =
        extDerivFun (I := I) (Rc m) x (chartBasisVecFiber (I := I) α p x) •
            chartBasisVecFiber (I := I) α m x +
          Rc m x •
            (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α m y) x)
              (chartBasisVecFiber (I := I) α p x) := by
    intro m
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y : M => chartBasisVecFiber (I := I) α m y) (g := Rc m) (x := x)
      (hframe_diff m) (hRc_diff m)
    have hterm_eq : term m = (Rc m) • (fun y : M => chartBasisVecFiber (I := I) α m y) := by
      funext y; rfl
    rw [hterm_eq]
    have happ := congr($(hleibniz) (chartBasisVecFiber (I := I) α p x))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] at happ
    rw [happ, add_comm]
  rw [Finset.sum_congr rfl (fun m _ => hleib m)]
  have hder : ∀ m : Fin (Module.finrank ℝ E),
      extDerivFun (I := I) (Rc m) x (chartBasisVecFiber (I := I) α p x) =
        partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
    intro m
    have hR_cda : ContDiffAt ℝ ∞ (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x) := by
      have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
        chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
      exact (chartRiemannTensor_contDiffOn_interior (I := I) g α s q r m).contDiffAt
        (isOpen_interior.mem_nhds hxint)
    exact extDerivFun_comp_extChartAt_apply_basis_alpha (I := I) α hx hR_cda p
  have hRc_x : ∀ m : Fin (Module.finrank ℝ E),
      Rc m x = chartRiemannTensor (I := I) g α s q r m (extChartAt I α x) := fun m => rfl
  have hinner : ∀ m : Fin (Module.finrank ℝ E),
      (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α m y) x)
          (chartBasisVecFiber (I := I) α p x) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p m l (extChartAt I α x) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α p m hx]
  rw [Finset.sum_congr rfl (fun m _ => by rw [hder m, hRc_x m, hinner m])]

  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun l => chartBasisVecFiber (I := I) α l x with he_def
  set D : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => partialDeriv (E := E) p (chartRiemannTensor (I := I) g α s q r m) (extChartAt I α x)
    with hD_def
  set Rr : Fin (Module.finrank ℝ E) → ℝ :=
    fun m => chartRiemannTensor (I := I) g α s q r m (extChartAt I α x) with hRr_def
  set Γq : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun m l => chartChristoffel (I := I) g α p m l (extChartAt I α x) with hΓq_def
  calc
    (∑ m : Fin (Module.finrank ℝ E),
        (D m • e m + Rr m • ∑ l : Fin (Module.finrank ℝ E), Γq m l • e l))
        = (∑ m : Fin (Module.finrank ℝ E), D m • e m) +
            (∑ m : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E), (Rr m * Γq m l) • e l) := by
          rw [Finset.sum_add_distrib]
          refine congrArg (fun t => (∑ m : Fin (Module.finrank ℝ E), D m • e m) + t) ?_
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [smul_smul]
      _ = (∑ l : Fin (Module.finrank ℝ E), D l • e l) +
            (∑ l : Fin (Module.finrank ℝ E),
              ∑ m : Fin (Module.finrank ℝ E), (Rr m * Γq m l) • e l) := by
          rw [Finset.sum_comm]
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (D l + ∑ m : Fin (Module.finrank ℝ E), Rr m * Γq m l) • e l := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← Finset.sum_smul, ← add_smul]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma riemannOp_chartFrame_triple
    (g : SmoothRiemannianMetric I M) (α : M)
    (m' r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    riemannOp (cov := LeviCivita (I := I) g) x
        (chartBasisVecFiber (I := I) α m' x) (chartBasisVecFiber (I := I) α r x)
        (chartBasisVecFiber (I := I) α s x) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α s m' r l (extChartAt I α x) •
          chartBasisVecFiber (I := I) α l x :=
  riemannOp_chartBasisVec_alpha_eq (I := I) g α s m' r hx

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma covApply_chartFrame_value
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq : Π b : M, TangentSpace I b} {U : Set M}
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y) :
    covApply (LeviCivita (I := I) g) Xp Xq x =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α p q m (extChartAt I α x) •
          chartBasisVecFiber (I := I) α m x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  rw [covApply_apply]
  have hXq_diff : MDiffAt (T% Xq) x := (hXq x).mdifferentiableAt (by simp)
  have hchart_q_diff : MDiffAt (T% (fun z : M => chartBasisVecFiber (I := I) α q z)) x :=
    chartBasisVec_alpha_mdifferentiableAt (I := I) α q hx
  have hXq_ev : (fun z : M => Xq z) =ᶠ[𝓝 x]
      (fun z : M => chartBasisVecFiber (I := I) α q z) := by
    filter_upwards [hU_open.mem_nhds hxU] with z hz using hXq_eq z hz
  have hcov_congr :
      cov.toFun Xq x = cov.toFun (fun z : M => chartBasisVecFiber (I := I) α q z) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hXq_diff hchart_q_diff
      Filter.univ_mem hXq_ev
  rw [hcov_congr, hXp_eq x hxU]
  rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α p q hx]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_chartBasisVec_alpha_corr_firstAntisym
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (_hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    riemannSec (LeviCivita (I := I) g) (covApply (LeviCivita (I := I) g) Xp Xq) Xr Xs x =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p q m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s m r l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hcXpXq := covApply_contMDiff (cov := cov) hXp hXq

  rw [← riemannOp_apply_smooth (cov := cov) hcXpXq hXr hXs]
  rw [covApply_chartFrame_value (I := I) g α p q hx hXq hU_open hxU hXp_eq hXq_eq,
    hXr_eq x hxU, hXs_eq x hxU]

  set er : TangentSpace I x := chartBasisVecFiber (I := I) α r x with her_def
  set es : TangentSpace I x := chartBasisVecFiber (I := I) α s x with hes_def
  have hexpand :
      riemannOp (cov := cov) x
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α p q m (extChartAt I α x) •
              chartBasisVecFiber (I := I) α m x) er es =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p q m (extChartAt I α x) •
            riemannOp (cov := cov) x (chartBasisVecFiber (I := I) α m x) er es := by
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply]
  rw [hexpand]
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α p q m (extChartAt I α x) •
          riemannOp (cov := cov) x (chartBasisVecFiber (I := I) α m x) er es =
        ∑ l : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α p q m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s m r l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [her_def, hes_def, riemannOp_chartFrame_triple (I := I) g α m r s hx, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
  rw [Finset.sum_congr rfl (fun m _ => hper m), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_smul]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_chartBasisVec_alpha_corr_secondAntisym
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (_hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    riemannSec (LeviCivita (I := I) g) Xq (covApply (LeviCivita (I := I) g) Xp Xr) Xs x =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p r m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s q m l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hcXpXr := covApply_contMDiff (cov := cov) hXp hXr
  rw [← riemannOp_apply_smooth (cov := cov) hXq hcXpXr hXs]
  rw [hXq_eq x hxU,
    covApply_chartFrame_value (I := I) g α p r hx hXr hU_open hxU hXp_eq hXr_eq,
    hXs_eq x hxU]
  set eq' : TangentSpace I x := chartBasisVecFiber (I := I) α q x with heq'_def
  set es : TangentSpace I x := chartBasisVecFiber (I := I) α s x with hes_def
  have hexpand :
      riemannOp (cov := cov) x eq'
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α p r m (extChartAt I α x) •
              chartBasisVecFiber (I := I) α m x) es =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p r m (extChartAt I α x) •
            riemannOp (cov := cov) x eq' (chartBasisVecFiber (I := I) α m x) es := by
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply]
  rw [hexpand]
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α p r m (extChartAt I α x) •
          riemannOp (cov := cov) x eq' (chartBasisVecFiber (I := I) α m x) es =
        ∑ l : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α p r m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α s q m l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [heq'_def, hes_def, riemannOp_chartFrame_triple (I := I) g α q m s hx, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
  rw [Finset.sum_congr rfl (fun m _ => hper m), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_smul]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaCurvSec_chartBasisVec_alpha_corr_acted
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (_hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    riemannSec (LeviCivita (I := I) g) Xq Xr (covApply (LeviCivita (I := I) g) Xp Xs) x =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p s m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α m q r l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hcXpXs := covApply_contMDiff (cov := cov) hXp hXs
  rw [← riemannOp_apply_smooth (cov := cov) hXq hXr hcXpXs]
  rw [hXq_eq x hxU, hXr_eq x hxU,
    covApply_chartFrame_value (I := I) g α p s hx hXs hU_open hxU hXp_eq hXs_eq]
  set eq' : TangentSpace I x := chartBasisVecFiber (I := I) α q x with heq'_def
  set er : TangentSpace I x := chartBasisVecFiber (I := I) α r x with her_def
  have hexpand :
      riemannOp (cov := cov) x eq' er
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α p s m (extChartAt I α x) •
              chartBasisVecFiber (I := I) α m x) =
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α p s m (extChartAt I α x) •
            riemannOp (cov := cov) x eq' er (chartBasisVecFiber (I := I) α m x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [map_smul]
  rw [hexpand]
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α p s m (extChartAt I α x) •
          riemannOp (cov := cov) x eq' er (chartBasisVecFiber (I := I) α m x) =
        ∑ l : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α p s m (extChartAt I α x) *
            chartRiemannTensor (I := I) g α m q r l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
    intro m
    rw [heq'_def, her_def, riemannOp_chartFrame_triple (I := I) g α q r m hx, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
  rw [Finset.sum_congr rfl (fun m _ => hper m), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_smul]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaCurvSec_chartBasisVec_alpha_frame_expand
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {Xp Xq Xr Xs : Π b : M, TangentSpace I b} {U : Set M}
    (hXp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xp))
    (hXq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xq))
    (hXr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xr))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xs))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α)
    (hXp_eq : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y)
    (hXq_eq : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y)
    (hXr_eq : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y)
    (hXs_eq : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y) :
    nablaCurvSec (LeviCivita (I := I) g) Xp Xq Xr Xs x =
      ∑ l : Fin (Module.finrank ℝ E),
        nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  rw [nablaCurvSec_def]
  rw [nablaCurvSec_chartBasisVec_alpha_leadingTerm (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq,
    nablaCurvSec_chartBasisVec_alpha_corr_firstAntisym (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq,
    nablaCurvSec_chartBasisVec_alpha_corr_secondAntisym (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq,
    nablaCurvSec_chartBasisVec_alpha_corr_acted (I := I) g α p q r s hx
      hXp hXq hXr hXs hU_open hxU hU_good hXp_eq hXq_eq hXr_eq hXs_eq]

  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← sub_smul, ← sub_smul, ← sub_smul]
  rfl

end Connection
end Integral
end DifferentialGeometry

end
