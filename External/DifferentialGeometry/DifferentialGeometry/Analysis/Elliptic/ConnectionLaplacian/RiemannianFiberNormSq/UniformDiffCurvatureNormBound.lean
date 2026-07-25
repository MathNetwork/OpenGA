import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Connection.ChartBridge.DiffRiemannBasisIdentityOffCentre
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformRiemannOperatorNormBound


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_eq_of_leftMidRight
    (g : SmoothRiemannianMetric I M)
    (X X' Y Y' Z Z' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hXX' : (X : Π b : M, TangentSpace I b) x = X' x)
    (hYY' : (Y : Π b : M, TangentSpace I b) x = Y' x)
    (hZZ' : (Z : Π b : M, TangentSpace I b) x = Z' x) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x u = nablaBaseSlotCurv (I := I) g X' Y' Z' x u := by
  classical
  rw [nablaBaseSlotCurv_eq_of_leftMid (I := I) g X X' Y Y' Z x hXX' hYY' u]
  have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => smoothExtensionTangent (I := I) x u b)) :=
    smoothExtensionTangent_contMDiff (I := I) x u
  have hswap : ∀ W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      nablaBaseSlotCurv (I := I) g X' Y' W x u =
        - nablaBaseSlotCurv (I := I) g X' W Y' x u := by
    intro W
    rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
    exact nablaCurvSec_swap23 (g := g) Y'.contMDiff W.contMDiff hext
  rw [hswap Z, hswap Z']
  congr 1
  exact nablaBaseSlotCurv_eq_of_leftMid (I := I) g X' X' Z Z' Y' x rfl hZZ' u

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_chartBasisVec_alpha_value
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (Sp Sq Sr : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hSp : (Sp : Π b : M, TangentSpace I b) x = chartBasisVecFiber (I := I) α p x)
    (hSq : (Sq : Π b : M, TangentSpace I b) x = chartBasisVecFiber (I := I) α q x)
    (hSr : (Sr : Π b : M, TangentSpace I b) x = chartBasisVecFiber (I := I) α r x) :
    nablaBaseSlotCurv (I := I) g Sp Sq Sr x (chartBasisVecFiber (I := I) α s x) =
      ∑ l : Fin (Module.finrank ℝ E),
        nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  obtain ⟨Xp, Up, hXp_sm, hUp_open, hxUp, hUp_good, hXp_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α p hx
  obtain ⟨Xq, Uq, hXq_sm, hUq_open, hxUq, hUq_good, hXq_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α q hx
  obtain ⟨Xr, Ur, hXr_sm, hUr_open, hxUr, hUr_good, hXr_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α r hx
  obtain ⟨Xs, Us, hXs_sm, hUs_open, hxUs, hUs_good, hXs_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α s hx
  set U : Set M := Up ∩ Uq ∩ Ur ∩ Us with hU_def
  have hU_open : IsOpen U := (((hUp_open.inter hUq_open).inter hUr_open).inter hUs_open)
  have hxU : x ∈ U := ⟨⟨⟨hxUp, hxUq⟩, hxUr⟩, hxUs⟩
  have hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α :=
    fun y hy => hUp_good hy.1.1.1
  have hXp_eqU : ∀ y ∈ U, Xp y = chartBasisVecFiber (I := I) α p y :=
    fun y hy => hXp_eq y hy.1.1.1
  have hXq_eqU : ∀ y ∈ U, Xq y = chartBasisVecFiber (I := I) α q y :=
    fun y hy => hXq_eq y hy.1.1.2
  have hXr_eqU : ∀ y ∈ U, Xr y = chartBasisVecFiber (I := I) α r y :=
    fun y hy => hXr_eq y hy.1.2
  have hXs_eqU : ∀ y ∈ U, Xs y = chartBasisVecFiber (I := I) α s y :=
    fun y hy => hXs_eq y hy.2
  set Pp : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk Xp hXp_sm with hPp_def
  set Pq : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk Xq hXq_sm with hPq_def
  set Pr : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk Xr hXr_sm with hPr_def
  have hPp_x : (Pp : Π b : M, TangentSpace I b) x = chartBasisVecFiber (I := I) α p x :=
    hXp_eqU x hxU
  have hPq_x : (Pq : Π b : M, TangentSpace I b) x = chartBasisVecFiber (I := I) α q x :=
    hXq_eqU x hxU
  have hPr_x : (Pr : Π b : M, TangentSpace I b) x = chartBasisVecFiber (I := I) α r x :=
    hXr_eqU x hxU
  rw [nablaBaseSlotCurv_eq_of_leftMidRight (I := I) g Sp Pp Sq Pq Sr Pr x
      (hSp.trans hPp_x.symm) (hSq.trans hPq_x.symm) (hSr.trans hPr_x.symm)
      (chartBasisVecFiber (I := I) α s x)]
  rw [nablaBaseSlotCurv_eq_nablaCurvSec]
  have hacted :
      nablaCurvSec (LeviCivita (I := I) g) (fun b => Pp b) (fun b => Pq b) (fun b => Pr b)
          (fun b => smoothExtensionTangent (I := I) x
            (chartBasisVecFiber (I := I) α s x) b) x =
        nablaCurvSec (LeviCivita (I := I) g) (fun b => Pp b) (fun b => Pq b) (fun b => Pr b)
          (fun b => Xs b) x := by
    set Es : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ContMDiffSection.mk (smoothExtensionTangent (I := I) x
        (chartBasisVecFiber (I := I) α s x))
        (smoothExtensionTangent_contMDiff (I := I) x (chartBasisVecFiber (I := I) α s x))
      with hEs_def
    set Ps : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk Xs hXs_sm with hPs_def
    have hval : (Es : Π b : M, TangentSpace I b) x = (Ps : Π b : M, TangentSpace I b) x := by
      rw [hEs_def, hPs_def]
      change smoothExtensionTangent (I := I) x (chartBasisVecFiber (I := I) α s x) x = Xs x
      rw [smoothExtensionTangent_eq, hXs_eqU x hxU]
    exact nablaCurvSec_eq_of_acted_eq (g := g) Pp Pq Pr Es Ps x hval
  rw [hacted]
  exact nablaCurvSec_chartBasisVec_alpha_frame_expand (I := I) g α p q r s hx
    hXp_sm hXq_sm hXr_sm hXs_sm hU_open hxU hU_good hXp_eqU hXq_eqU hXr_eqU hXs_eqU

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_zero_left
    (g : SmoothRiemannianMetric I M)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g 0 Y Z x u = 0 := by
  have h := nablaBaseSlotCurv_add_left (I := I) g 0 0 Y Z x u
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_zero_Z
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y 0 x u = 0 := by
  classical

  have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => smoothExtensionTangent (I := I) x u b)) :=
    smoothExtensionTangent_contMDiff (I := I) x u
  have hswap : ∀ W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      nablaBaseSlotCurv (I := I) g X Y W x u = - nablaBaseSlotCurv (I := I) g X W Y x u := by
    intro W
    rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
    exact nablaCurvSec_swap23 (g := g) Y.contMDiff W.contMDiff hext
  rw [hswap 0]

  have h := nablaBaseSlotCurv_add_right (I := I) g X 0 0 Y x u
  rw [add_zero] at h
  rw [add_eq_left.mp h.symm, neg_zero]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_finsetSum_left
    (g : SmoothRiemannianMetric I M) {ι : Type*} (t : Finset ι)
    (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g (∑ i ∈ t, X i) Y Z x u =
      ∑ i ∈ t, nablaBaseSlotCurv (I := I) g (X i) Y Z x u := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [nablaBaseSlotCurv_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, nablaBaseSlotCurv_add_left, ih, Finset.sum_insert ha]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_finsetSum_right
    (g : SmoothRiemannianMetric I M) {ι : Type*} (t : Finset ι)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Y : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X (∑ i ∈ t, Y i) Z x u =
      ∑ i ∈ t, nablaBaseSlotCurv (I := I) g X (Y i) Z x u := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h := nablaBaseSlotCurv_add_right (I := I) g X 0 0 Z x u
      rw [add_zero] at h
      exact add_eq_left.mp h.symm
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, nablaBaseSlotCurv_add_right, ih, Finset.sum_insert ha]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_smul_Z
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y (c • Z) x u =
      c • nablaBaseSlotCurv (I := I) g X Y Z x u := by
  classical
  have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => smoothExtensionTangent (I := I) x u b)) :=
    smoothExtensionTangent_contMDiff (I := I) x u
  have hswap : ∀ W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      nablaBaseSlotCurv (I := I) g X Y W x u = - nablaBaseSlotCurv (I := I) g X W Y x u := by
    intro W
    rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
    exact nablaCurvSec_swap23 (g := g) Y.contMDiff W.contMDiff hext
  rw [hswap (c • Z), nablaBaseSlotCurv_smul_right, hswap Z, smul_neg]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_finsetSum_Z
    (g : SmoothRiemannianMetric I M) {ι : Type*} (t : Finset ι)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Z : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y (∑ i ∈ t, Z i) x u =
      ∑ i ∈ t, nablaBaseSlotCurv (I := I) g X Y (Z i) x u := by
  classical

  have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => smoothExtensionTangent (I := I) x u b)) :=
    smoothExtensionTangent_contMDiff (I := I) x u
  have hswap : ∀ W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      nablaBaseSlotCurv (I := I) g X Y W x u = - nablaBaseSlotCurv (I := I) g X W Y x u := by
    intro W
    rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec]
    exact nablaCurvSec_swap23 (g := g) Y.contMDiff W.contMDiff hext
  rw [hswap (∑ i ∈ t, Z i)]

  have hY : nablaBaseSlotCurv (I := I) g X (∑ i ∈ t, Z i) Y x u =
      ∑ i ∈ t, nablaBaseSlotCurv (I := I) g X (Z i) Y x u := by
    classical
    induction t using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        have h := nablaBaseSlotCurv_add_right (I := I) g X 0 0 Y x u
        rw [add_zero] at h
        exact add_eq_left.mp h.symm
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, nablaBaseSlotCurv_add_right, ih, Finset.sum_insert ha]
  rw [hY, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hswap (Z i)]

omit [CompactSpace M] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_finsetSum_smul_acted
    (g : SmoothRiemannianMetric I M) {ι : Type*} (t : Finset ι)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (d : ι → ℝ) (v : ι → TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x (∑ i ∈ t, d i • v i) =
      ∑ i ∈ t, d i • nablaBaseSlotCurv (I := I) g X Y Z x (v i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h := nablaBaseSlotCurv_add_acted (I := I) g X Y Z x 0 0
      rw [add_zero] at h
      exact add_eq_left.mp h.symm
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, nablaBaseSlotCurv_add_acted,
        nablaBaseSlotCurv_smul_acted, ih, Finset.sum_insert ha]

private def chartFrameExtSection
    (α : M) (p : Fin (Module.finrank ℝ E)) (x : M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk (smoothExtensionTangent (I := I) x (chartBasisVecFiber (I := I) α p x))
    (smoothExtensionTangent_contMDiff (I := I) x (chartBasisVecFiber (I := I) α p x))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma chartFrameExtSection_value
    (α : M) (p : Fin (Module.finrank ℝ E)) (x : M) :
    (chartFrameExtSection (I := I) α p x : Π b : M, TangentSpace I b) x =
      chartBasisVecFiber (I := I) α p x := by
  change smoothExtensionTangent (I := I) x (chartBasisVecFiber (I := I) α p x) x = _
  rw [smoothExtensionTangent_eq]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_chartCoord_expand
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Sp Sq Sr : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (w : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g Sp Sq Sr x w =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
            (chartBasisFamily (I := I) α hxbase).repr (Sp x) p *
              (chartBasisFamily (I := I) α hxbase).repr (Sq x) q *
              (chartBasisFamily (I := I) α hxbase).repr (Sr x) r *
              (chartBasisFamily (I := I) α hxbase).repr w s *
              nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set a : Fin n → ℝ := fun p => (chartBasisFamily (I := I) α hxbase).repr (Sp x) p with ha_def
  set b : Fin n → ℝ := fun q => (chartBasisFamily (I := I) α hxbase).repr (Sq x) q with hb_def
  set c : Fin n → ℝ := fun r => (chartBasisFamily (I := I) α hxbase).repr (Sr x) r with hc_def
  set ev : Fin n → ℝ := fun s => (chartBasisFamily (I := I) α hxbase).repr w s with hev_def
  set P : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    fun p => chartFrameExtSection (I := I) α p x with hP_def

  have hSp_decomp : (Sp : Π z : M, TangentSpace I z) x =
      (∑ p : Fin n, a p • P p : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := by
    rw [ContMDiffSection.finset_sum_apply]
    have hrep := (chartBasisFamily (I := I) α hxbase).sum_repr (Sp x)
    rw [← hrep]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, ha_def, chartFrameExtSection_value,
      chartBasisFamily_apply]
  have hSq_decomp : (Sq : Π z : M, TangentSpace I z) x =
      (∑ q : Fin n, b q • P q : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := by
    rw [ContMDiffSection.finset_sum_apply]
    have hrep := (chartBasisFamily (I := I) α hxbase).sum_repr (Sq x)
    rw [← hrep]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, hb_def, chartFrameExtSection_value,
      chartBasisFamily_apply]
  have hSr_decomp : (Sr : Π z : M, TangentSpace I z) x =
      (∑ r : Fin n, c r • P r : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := by
    rw [ContMDiffSection.finset_sum_apply]
    have hrep := (chartBasisFamily (I := I) α hxbase).sum_repr (Sr x)
    rw [← hrep]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ContMDiffSection.coe_smul, Pi.smul_apply, hc_def, chartFrameExtSection_value,
      chartBasisFamily_apply]
  have hw_decomp : w = ∑ s : Fin n, ev s • chartBasisVecFiber (I := I) α s x := by
    have hrep := (chartBasisFamily (I := I) α hxbase).sum_repr w
    rw [← hrep]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hev_def, chartBasisFamily_apply]

  rw [nablaBaseSlotCurv_eq_of_leftMidRight (I := I) g Sp (∑ p : Fin n, a p • P p)
      Sq (∑ q : Fin n, b q • P q) Sr (∑ r : Fin n, c r • P r) x hSp_decomp hSq_decomp hSr_decomp w]
  conv_lhs => rw [hw_decomp]
  rw [nablaBaseSlotCurv_finsetSum_smul_acted]

  have hper_s : ∀ s : Fin n,
      nablaBaseSlotCurv (I := I) g (∑ p : Fin n, a p • P p) (∑ q : Fin n, b q • P q)
          (∑ r : Fin n, c r • P r) x (chartBasisVecFiber (I := I) α s x) =
        ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
          (a p * b q * c r) •
            nablaBaseSlotCurv (I := I) g (P p) (P q) (P r) x
              (chartBasisVecFiber (I := I) α s x) := by
    intro s
    rw [nablaBaseSlotCurv_finsetSum_left]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [nablaBaseSlotCurv_smul_left, nablaBaseSlotCurv_finsetSum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [nablaBaseSlotCurv_smul_right, nablaBaseSlotCurv_finsetSum_Z, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [nablaBaseSlotCurv_smul_Z, smul_smul, smul_smul]

  rw [Finset.sum_congr rfl (fun s _ => by rw [hper_s s])]

  have hPval : ∀ (p q r s : Fin n),
      nablaBaseSlotCurv (I := I) g (P p) (P q) (P r) x (chartBasisVecFiber (I := I) α s x) =
        ∑ l : Fin n,
          nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x) •
            chartBasisVecFiber (I := I) α l x := by
    intro p q r s
    exact nablaBaseSlotCurv_chartBasisVec_alpha_value (I := I) g α p q r s hx (P p) (P q) (P r)
      (chartFrameExtSection_value (I := I) α p x) (chartFrameExtSection_value (I := I) α q x)
      (chartFrameExtSection_value (I := I) α r x)

  have hLHS : (∑ s : Fin n, ev s •
        ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
          (a p * b q * c r) •
            nablaBaseSlotCurv (I := I) g (P p) (P q) (P r) x
              (chartBasisVecFiber (I := I) α s x)) =
      ∑ s : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ l : Fin n,
        (a p * b q * c r * ev s *
          nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hPval p q r s, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [smul_smul]
    congr 2
    ring
  rw [hLHS]

  rw [show (∑ s : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ l : Fin n,
        (a p * b q * c r * ev s *
          nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x) =
      ∑ l : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ s : Fin n,
        (a p * b q * c r * ev s *
          nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x from by
    set F : Fin n → Fin n → Fin n → Fin n → Fin n → TangentSpace I x :=
      fun s p q r l =>
        (a p * b q * c r * ev s *
          nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x with hF_def

    have e1 : (∑ s : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, ∑ l : Fin n, F s p q r l) =
        ∑ s : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ l : Fin n, ∑ r : Fin n, F s p q r l := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      refine Finset.sum_congr rfl (fun p _ => ?_)
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_comm]
    have e2 : (∑ s : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ l : Fin n, ∑ r : Fin n, F s p q r l) =
        ∑ s : Fin n, ∑ p : Fin n, ∑ l : Fin n, ∑ q : Fin n, ∑ r : Fin n, F s p q r l := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_comm]
    have e3 : (∑ s : Fin n, ∑ p : Fin n, ∑ l : Fin n, ∑ q : Fin n, ∑ r : Fin n, F s p q r l) =
        ∑ s : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, F s p q r l := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Finset.sum_comm]
    have e4 : (∑ s : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, F s p q r l) =
        ∑ l : Fin n, ∑ s : Fin n, ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, F s p q r l := by
      rw [Finset.sum_comm]
    rw [e1, e2, e3, e4]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl (fun l _ => ?_)

  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.sum_smul]

private def nablaChartRiemannEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s l : Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => nablaChartRiemannCoeff (I := I) g α p q r s l (toEuclidean.symm y)

omit [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma nablaChartRiemannEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (p q r s l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (nablaChartRiemannEuclid (I := I) g α p q r s l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hE : ContDiffOn ℝ ∞ (nablaChartRiemannCoeff (I := I) g α p q r s l)
      ((extChartAt I α).target) := by
    have htarget_open : IsOpen ((extChartAt I α).target : Set E) :=
      isOpen_extChartAt_target (I := I) α
    rw [show ((extChartAt I α).target : Set E) =
        interior ((extChartAt I α).target : Set E) from htarget_open.interior_eq.symm]
    exact nablaChartRiemannCoeff_contDiffOn_interior (I := I) g α p q r s l
  have hcomp : ContDiffOn ℝ ∞
      (nablaChartRiemannCoeff (I := I) g α p q r s l ∘
        (toEuclidean.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hE.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      exact DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
        (I := I) (M := M) hy
  exact hcomp

omit [BoundarylessManifold I M] in
private lemma exists_nablaChartRiemannData_uniform_bound_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (p q r s l : Fin (Module.finrank ℝ E)),
          |nablaChartRiemannCoeff (I := I) g α p q r s l ((extChartAt I α) b)| ≤ C := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set K_set : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_image_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ chartTargetEuclid (I := I) (M := M) α :=
    pouTsupport_image_subset_chartTargetEuclid (I := I) (M := M) α
  have h_each : ∀ idx : ((Fin n × Fin n) × (Fin n × Fin n)) × Fin n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ K_set,
        |nablaChartRiemannEuclid (I := I) g α idx.1.1.1 idx.1.1.2 idx.1.2.1 idx.1.2.2 idx.2 y| ≤ C := by
    intro idx
    exact exists_sup_bound_of_contDiffOn_on_compact_subset hK_compact hK_sub
      (nablaChartRiemannEuclid_contDiffOn (I := I) (M := M) g α
        idx.1.1.1 idx.1.1.2 idx.1.2.1 idx.1.2.2 idx.2)
  choose C_fn hC_fn_nn hC_fn_bd using h_each
  set C : ℝ :=
    (Finset.univ : Finset (((Fin n × Fin n) × (Fin n × Fin n)) × Fin n)).sup'
      Finset.univ_nonempty C_fn with hC_def
  have hC_nn : 0 ≤ C := by
    rcases Finset.univ_nonempty
      (α := ((Fin n × Fin n) × (Fin n × Fin n)) × Fin n) with ⟨idx₀, _⟩
    exact (hC_fn_nn idx₀).trans
      (Finset.le_sup'_of_le C_fn (Finset.mem_univ idx₀) (le_refl _))
  refine ⟨C, hC_nn, ?_⟩
  intro b hb_tsupp p q r s l
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hy_K : y ∈ K_set := ⟨b, hb_tsupp, rfl⟩
  have hval : nablaChartRiemannEuclid (I := I) g α p q r s l y =
      nablaChartRiemannCoeff (I := I) g α p q r s l ((extChartAt I α) b) := by
    rw [nablaChartRiemannEuclid, hy_def]
    congr 1
    exact toEuclidean.symm_apply_apply ((extChartAt I α) b)
  have hbd_idx := hC_fn_bd (((p, q), (r, s)), l) y hy_K
  have hidx_le : C_fn (((p, q), (r, s)), l) ≤ C :=
    Finset.le_sup'_of_le C_fn (Finset.mem_univ (((p, q), (r, s)), l)) (le_refl _)
  calc |nablaChartRiemannCoeff (I := I) g α p q r s l ((extChartAt I α) b)|
      = |nablaChartRiemannEuclid (I := I) g α p q r s l y| := by rw [hval]
    _ ≤ C_fn (((p, q), (r, s)), l) := hbd_idx
    _ ≤ C := hidx_le


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
private lemma pouTsupport_subset_goodSet (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
  intro b hb
  have heq : chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
          (I := I) α]
    exact extChartAt_source_eq_chartAt_source (I := I) α
  rw [heq]
  exact chartAtlasPOU_isSubordinate I M α hb


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma gInner_self_eq_chartGram_quadForm
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : TangentSpace I x) :
    g.inner x v v =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i j *
            (chartBasisFamily (I := I) α hx).repr v i *
            (chartBasisFamily (I := I) α hx).repr v j := by
  classical
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => (chartBasisFamily (I := I) α hx).repr v i with hc_def
  have hv : v = ∑ i, c i • chartBasisVecFiber (I := I) α i x := by
    have h := (chartBasisFamily (I := I) α hx).sum_repr v
    rw [← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc_def, chartBasisFamily_apply (I := I) α hx i]
  have hdot := chartGramMatrix_dotProduct_mulVec (I := I) g α x c
  have hgi : g.inner x (∑ i, c i • chartBasisVecFiber (I := I) α i x)
        (∑ j, c j • chartBasisVecFiber (I := I) α j x)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g α x i j * c i * c j := by
    rw [← hdot]
    simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  calc g.inner x v v
      = g.inner x (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          (∑ j, c j • chartBasisVecFiber (I := I) α j x) := by rw [← hv]
    _ = _ := hgi

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartCoord_sq_sum_le
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {cg : ℝ} (hcg : 0 < cg)
    (hcgbound : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      cg * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i j * ξ i * ξ j)
    (v : TangentSpace I x) :
    (∑ p : Fin (Module.finrank ℝ E), (chartBasisFamily (I := I) α hx).repr v p ^ 2) ≤
      cg⁻¹ * g.inner x v v := by
  set ξ : Fin (Module.finrank ℝ E) → ℝ := fun p => (chartBasisFamily (I := I) α hx).repr v p
    with hξ_def
  have hlow : cg * (∑ p, ξ p ^ 2) ≤ g.inner x v v := by
    rw [gInner_self_eq_chartGram_quadForm (I := I) g α hx v]; exact hcgbound ξ
  rw [inv_mul_eq_div, le_div_iff₀' hcg]; exact hlow


private lemma sum4_prod_factor {ι : Type*} [Fintype ι] (F G H K : ι → ℝ) :
    (∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, F p * G q * H r * K s) =
      (∑ p : ι, F p) * (∑ q : ι, G q) * (∑ r : ι, H r) * (∑ s : ι, K s) := by
  classical

  have hs : (∑ p : ι, ∑ q : ι, ∑ r : ι, ∑ s : ι, F p * G q * H r * K s) =
      ∑ p : ι, ∑ q : ι, ∑ r : ι, (F p * G q * H r) * (∑ s : ι, K s) :=
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun r _ => by rw [Finset.mul_sum])))
  rw [hs]
  have hr : (∑ p : ι, ∑ q : ι, ∑ r : ι, (F p * G q * H r) * (∑ s : ι, K s)) =
      ∑ p : ι, ∑ q : ι, (F p * G q) * (∑ r : ι, H r) * (∑ s : ι, K s) :=
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by
      rw [← Finset.sum_mul, ← Finset.mul_sum]))
  rw [hr]
  have hq : (∑ p : ι, ∑ q : ι, (F p * G q) * (∑ r : ι, H r) * (∑ s : ι, K s)) =
      ∑ p : ι, F p * (∑ q : ι, G q) * (∑ r : ι, H r) * (∑ s : ι, K s) :=
    Finset.sum_congr rfl (fun p _ => by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum])
  rw [hq, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma W_chartFrame_expand
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Ba : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (u : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u) =
      ∑ l : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
          ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
            (chartBasisFamily (I := I) α hxbase).repr (B i x) p *
              (chartBasisFamily (I := I) α hxbase).repr (B i x) q *
              (chartBasisFamily (I := I) α hxbase).repr (Ba x) r *
              (chartBasisFamily (I := I) α hxbase).repr u s *
              nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => nablaBaseSlotCurv_chartCoord_expand (I := I) g α hx hxbase
    (B i) (B i) Ba u)]

  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_smul]


private lemma diffCurv_arith_core
    {CR Sa Su T N G U : ℝ}
    (_hCR : 0 ≤ CR) (_hSa : 0 ≤ Sa) (_hSu : 0 ≤ Su) (hT : 0 ≤ T)
    (hN : 0 ≤ N) (hG : 0 ≤ G) (hU : 0 ≤ U)
    (hSa_sq : Sa ^ 2 ≤ N * G) (hSu_sq : Su ^ 2 ≤ N * G * U) (hT_le : T ≤ N ^ 2 * G) :
    (CR * Sa * Su * T) ^ 2 ≤ CR ^ 2 * (N ^ 6 * G ^ 4) * U := by
  have hT_sq : T ^ 2 ≤ (N ^ 2 * G) ^ 2 := pow_le_pow_left₀ hT hT_le 2
  have hNG_nn : 0 ≤ N ^ 2 * G := by positivity
  calc (CR * Sa * Su * T) ^ 2 = CR ^ 2 * (Sa ^ 2 * (Su ^ 2 * T ^ 2)) := by ring
    _ ≤ CR ^ 2 * ((N * G) * ((N * G * U) * (N ^ 2 * G) ^ 2)) := by
        gcongr
    _ = CR ^ 2 * (N ^ 6 * G ^ 4) * U := by ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma nablaBaseSlotCurv_frameSum_normSq_le_chartConstants_mul_normSq_u
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {CR CG cg : ℝ} (hCR : 0 ≤ CR) (hCG : 0 ≤ CG) (hcg : 0 < cg)
    (hCRbound : ∀ p q r s l : Fin (Module.finrank ℝ E),
      |nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x)| ≤ CR)
    (hCGbound : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i j * ξ i * ξ j ≤
        CG * ∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2)
    (hcgbound : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      cg * (∑ i : Fin (Module.finrank ℝ E), ξ i ^ 2) ≤
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i j * ξ i * ξ j)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Ba : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hBon : ∀ i : Fin (Module.finrank ℝ E), g.inner x (B i x) (B i x) = 1)
    (hBaon : g.inner x (Ba x) (Ba x) = 1)
    (u : TangentSpace I x) :
    g.inner x
        (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u)
        (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u) ≤
      CG * CR ^ 2 * (Module.finrank ℝ E : ℝ) ^ 7 * cg⁻¹ ^ 4 * g.inner x u u := by
  classical

  set bi : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun i p => (chartBasisFamily (I := I) α hx_base).repr (B i x) p
    with hbi_def
  set ca : Fin (Module.finrank ℝ E) → ℝ := fun r => (chartBasisFamily (I := I) α hx_base).repr (Ba x) r with hca_def
  set du : Fin (Module.finrank ℝ E) → ℝ := fun s => (chartBasisFamily (I := I) α hx_base).repr u s with hdu_def
  set R : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun p q r s l => nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α x) with hR_def

  set coeff : Fin (Module.finrank ℝ E) → ℝ := fun l =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
      bi i p * bi i q * ca r * du s * R p q r s l with hcoeff_def
  have hWexp :
      (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u) =
        ∑ l : Fin (Module.finrank ℝ E), coeff l • chartBasisVecFiber (I := I) α l x := by
    rw [W_chartFrame_expand (I := I) g α hx_good hx_base B Ba u]

  have hgnorm_le :
      g.inner x (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u)
          (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u) ≤
        CG * ∑ l : Fin (Module.finrank ℝ E), coeff l ^ 2 := by
    rw [hWexp]
    have hdot := chartGramMatrix_dotProduct_mulVec (I := I) g α x coeff
    have heq : g.inner x (∑ l : Fin (Module.finrank ℝ E), coeff l • chartBasisVecFiber (I := I) α l x)
          (∑ l' : Fin (Module.finrank ℝ E), coeff l' • chartBasisVecFiber (I := I) α l' x) =
        ∑ l : Fin (Module.finrank ℝ E), ∑ l' : Fin (Module.finrank ℝ E), chartGramMatrix (I := I) g α x l l' * coeff l * coeff l' := by
      rw [← hdot]
      simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l' _ => ?_)
      ring
    rw [heq]
    exact hCGbound coeff

  set Sbi : Fin (Module.finrank ℝ E) → ℝ := fun i => ∑ p : Fin (Module.finrank ℝ E), |bi i p| with hSbi_def
  set Sa : ℝ := ∑ r : Fin (Module.finrank ℝ E), |ca r| with hSa_def
  set Su : ℝ := ∑ s : Fin (Module.finrank ℝ E), |du s| with hSu_def
  have hSbi_nn : ∀ i, 0 ≤ Sbi i := fun i => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hSa_nn : 0 ≤ Sa := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hSu_nn : 0 ≤ Su := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

  have hcoeff_abs : ∀ l, |coeff l| ≤ ∑ i : Fin (Module.finrank ℝ E), CR * (Sbi i * Sbi i * Sa * Su) := by
    intro l
    rw [hcoeff_def]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => ?_))

    have hinner : |∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
          bi i p * bi i q * ca r * du s * R p q r s l| ≤
        ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
          |bi i p| * |bi i q| * |ca r| * |du s| * CR := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun p _ => ?_))
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun q _ => ?_))
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun r _ => ?_))
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun s _ => ?_))
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hCRbound p q r s l) (by positivity)
    refine le_trans hinner ?_

    have hfac : (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
          |bi i p| * |bi i q| * |ca r| * |du s| * CR) =
        (Sbi i) * (Sbi i) * Sa * Su * CR := by
      rw [hSbi_def, hSa_def, hSu_def]

      rw [show (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
            |bi i p| * |bi i q| * |ca r| * |du s| * CR) =
          (∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E), ∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
            |bi i p| * |bi i q| * |ca r| * |du s|) * CR from by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Finset.sum_mul]]
      rw [sum4_prod_factor (fun p => |bi i p|) (fun q => |bi i q|) (fun r => |ca r|)
        (fun s => |du s|)]
    rw [hfac]; exact le_of_eq (by ring)

  set T : ℝ := ∑ i : Fin (Module.finrank ℝ E), Sbi i * Sbi i with hT_def
  have hT_nn : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (hSbi_nn i) (hSbi_nn i))
  have hcoeff_abs' : ∀ l, |coeff l| ≤ CR * Sa * Su * T := by
    intro l
    refine le_trans (hcoeff_abs l) ?_
    rw [hT_def, Finset.mul_sum]
    refine le_of_eq (Finset.sum_congr rfl (fun i _ => by ring))

  have hcoeff_sq : ∀ l, coeff l ^ 2 ≤ (CR * Sa * Su * T) ^ 2 := by
    intro l
    calc coeff l ^ 2 = |coeff l| ^ 2 := (sq_abs _).symm
      _ ≤ (CR * Sa * Su * T) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hcoeff_abs' l) 2
  have hsum_coeff_sq : ∑ l : Fin (Module.finrank ℝ E), coeff l ^ 2 ≤ (Module.finrank ℝ E : ℝ) * (CR * Sa * Su * T) ^ 2 := by
    calc ∑ l : Fin (Module.finrank ℝ E), coeff l ^ 2 ≤ ∑ _l : Fin (Module.finrank ℝ E), (CR * Sa * Su * T) ^ 2 :=
          Finset.sum_le_sum (fun l _ => hcoeff_sq l)
      _ = (Module.finrank ℝ E : ℝ) * (CR * Sa * Su * T) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  have hCheb : ∀ (v : TangentSpace I x), (∑ p : Fin (Module.finrank ℝ E), |(chartBasisFamily (I := I) α hx_base).repr v p|) ^ 2 ≤
      (Module.finrank ℝ E : ℝ) * ∑ p : Fin (Module.finrank ℝ E), (chartBasisFamily (I := I) α hx_base).repr v p ^ 2 := by
    intro v
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (f := fun p => |(chartBasisFamily (I := I) α hx_base).repr v p|)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have heq : ∑ p : Fin (Module.finrank ℝ E), |(chartBasisFamily (I := I) α hx_base).repr v p| ^ 2 =
        ∑ p : Fin (Module.finrank ℝ E), (chartBasisFamily (I := I) α hx_base).repr v p ^ 2 :=
      Finset.sum_congr rfl (fun p _ => sq_abs _)
    rw [heq] at h
    exact h

  have hcg_inv_nn : (0 : ℝ) ≤ cg⁻¹ := le_of_lt (inv_pos.mpr hcg)
  have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hguu_nn : 0 ≤ g.inner x u u := metric_inner_self_nonneg (I := I) g x u
  have hSa_sq : Sa ^ 2 ≤ (Module.finrank ℝ E : ℝ) * cg⁻¹ := by
    have h1 : Sa ^ 2 ≤ (Module.finrank ℝ E : ℝ) * (cg⁻¹ * g.inner x (Ba x) (Ba x)) := by
      refine le_trans (hCheb (Ba x)) ?_
      gcongr
      exact chartCoord_sq_sum_le (I := I) g α hx_base hcg hcgbound (Ba x)
    rw [hBaon, mul_one] at h1; exact h1
  have hSu_sq : Su ^ 2 ≤ (Module.finrank ℝ E : ℝ) * cg⁻¹ * g.inner x u u := by
    have h1 : Su ^ 2 ≤ (Module.finrank ℝ E : ℝ) * (cg⁻¹ * g.inner x u u) := by
      refine le_trans (hCheb u) ?_
      gcongr
      exact chartCoord_sq_sum_le (I := I) g α hx_base hcg hcgbound u
    rw [← mul_assoc] at h1; exact h1
  have hSbi_sq : ∀ i, Sbi i ^ 2 ≤ (Module.finrank ℝ E : ℝ) * cg⁻¹ := by
    intro i
    have hcoord : (∑ p : Fin (Module.finrank ℝ E), (chartBasisFamily (I := I) α hx_base).repr (B i x) p ^ 2) ≤ cg⁻¹ := by
      refine le_trans (chartCoord_sq_sum_le (I := I) g α hx_base hcg hcgbound (B i x)) ?_
      rw [hBon i, mul_one]
    refine le_trans (hCheb (B i x)) ?_
    gcongr

  have hT_le : T ≤ (Module.finrank ℝ E : ℝ) ^ 2 * cg⁻¹ := by
    have hstep : T ≤ ∑ _i : Fin (Module.finrank ℝ E), (Module.finrank ℝ E : ℝ) * cg⁻¹ := by
      rw [hT_def]
      exact Finset.sum_le_sum (fun i _ => by rw [← sq]; exact hSbi_sq i)
    refine le_trans hstep ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((Module.finrank ℝ E : ℝ) ^ 2 * cg⁻¹) = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * cg⁻¹) from by ring]

  have hSaTU_sq : (CR * Sa * Su * T) ^ 2 ≤
      CR ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 6 * cg⁻¹ ^ 4) * g.inner x u u :=
    diffCurv_arith_core hCR hSa_nn hSu_nn hT_nn hn_nn hcg_inv_nn hguu_nn hSa_sq hSu_sq hT_le
  have hcoeffsum_le : ∑ l : Fin (Module.finrank ℝ E), coeff l ^ 2 ≤
      CR ^ 2 * (Module.finrank ℝ E : ℝ) ^ 7 * cg⁻¹ ^ 4 * g.inner x u u := by
    calc ∑ l : Fin (Module.finrank ℝ E), coeff l ^ 2 ≤ (Module.finrank ℝ E : ℝ) * (CR * Sa * Su * T) ^ 2 := hsum_coeff_sq
      _ ≤ (Module.finrank ℝ E : ℝ) * (CR ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 6 * cg⁻¹ ^ 4) * g.inner x u u) := by gcongr
      _ = CR ^ 2 * (Module.finrank ℝ E : ℝ) ^ 7 * cg⁻¹ ^ 4 * g.inner x u u := by ring
  calc g.inner x
        (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u)
        (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g (B i) (B i) Ba x u)
      ≤ CG * ∑ l : Fin (Module.finrank ℝ E), coeff l ^ 2 := hgnorm_le
    _ ≤ CG * (CR ^ 2 * (Module.finrank ℝ E : ℝ) ^ 7 * cg⁻¹ ^ 4 * g.inner x u u) :=
          mul_le_mul_of_nonneg_left hcoeffsum_le hCG
    _ = CG * CR ^ 2 * (Module.finrank ℝ E : ℝ) ^ 7 * cg⁻¹ ^ 4 * g.inner x u u := by ring

theorem exists_continuous_nablaCurvSec_frameSum_gNorm_envelope
    (g : SmoothRiemannianMetric I M) :
    ∃ Kw : M → ℝ, Continuous Kw ∧ (∀ x : M, 0 ≤ Kw x) ∧
      ∀ (x : M) (a : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
        g.inner x
            (nablaBaseSlotCurvFrameSumCLM (I := I) g
              (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame_smooth (I := I) g x i))
              (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                (smoothOrthoFrame_smooth (I := I) g x a)) x u)
            (nablaBaseSlotCurvFrameSumCLM (I := I) g
              (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame_smooth (I := I) g x i))
              (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                (smoothOrthoFrame_smooth (I := I) g x a)) x u) ≤
          Kw x * g.inner x u u := by
  classical

  have hCR_ex : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ∀ p q r s l : Fin (Module.finrank ℝ E),
          |nablaChartRiemannCoeff (I := I) g α p q r s l (extChartAt I α b)| ≤ C := by
    intro α
    obtain ⟨C, hC0, hCbound⟩ :=
      exists_nablaChartRiemannData_uniform_bound_pouTsupport (I := I) g α
    exact ⟨C, hC0, fun b hb p q r s l => hCbound hb p q r s l⟩
  have hCG_ex : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          ∑ i, ∑ j, chartGramMatrix (I := I) g α b i j * ξ i * ξ j ≤ C * ∑ i, ξ i ^ 2 := by
    intro α
    obtain ⟨C, hC0, hCbound⟩ :=
      exists_chartGramMatrix_quadForm_upper_bound_on_pouTsupport (I := I) g α
    refine ⟨C, hC0, fun b hb ξ => ?_⟩
    refine le_trans (le_of_eq ?_) (hCbound hb ξ)
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [chartGramMatrix_apply]
  choose CR hCR0 hCRbound using hCR_ex
  choose CG hCG0 hCGbound using hCG_ex
  choose cg hcg0 hcgbound using fun α =>
    exists_chartGramMatrix_quadForm_lower_bound_on_pouTsupport (I := I) g α
  set Kα : M → ℝ := fun α =>
    CG α * CR α ^ 2 * (Module.finrank ℝ E : ℝ) ^ 7 * (cg α)⁻¹ ^ 4 with hKα_def
  have hKα_nonneg : ∀ α, 0 ≤ Kα α := by
    intro α
    rw [hKα_def]
    have hcgα : 0 < cg α := hcg0 α
    have hinv : 0 ≤ (cg α)⁻¹ ^ 4 := by positivity
    have hCRα : 0 ≤ CR α := hCR0 α
    have hCGα : 0 ≤ CG α := hCG0 α
    positivity
  refine ⟨fun _ => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Kα α, continuous_const,
    fun _ => Finset.sum_nonneg (fun α _ => hKα_nonneg α), ?_⟩
  intro x a u

  simp only [nablaBaseSlotCurvFrameSumCLM_apply]
  have hsum := DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
    (I := I) (M := M) x
  have hex_pos : ∃ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ((chartAtlasPOU I M) α) x ≠ 0 := by
    by_contra hno
    have hzero : ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) α) x = 0 :=
      Finset.sum_eq_zero (fun α hα => by
        by_contra hne; exact hno ⟨α, hα, hne⟩)
    rw [hzero] at hsum; exact one_ne_zero hsum.symm
  obtain ⟨α, hα_mem, hα_pos⟩ := hex_pos
  have hx_tsupport : x ∈ tsupport
      (fun y : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
    subset_tsupport _ hα_pos
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet (I := I) α hx_tsupport
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good

  have hBon : ∀ i : Fin (Module.finrank ℝ E),
      g.inner x ((ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame_smooth (I := I) g x i)) x)
        ((ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame_smooth (I := I) g x i)) x) = 1 := by
    intro i
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    rw [if_pos rfl] at this
    simpa using this
  have hBaon :
      g.inner x ((ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
          (smoothOrthoFrame_smooth (I := I) g x a)) x)
        ((ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
          (smoothOrthoFrame_smooth (I := I) g x a)) x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x a a
    rw [if_pos rfl] at this
    simpa using this

  have hpt := nablaBaseSlotCurv_frameSum_normSq_le_chartConstants_mul_normSq_u (I := I) g α hx_base hx_good
    (CR := CR α) (CG := CG α) (cg := cg α) (hCR0 α) (hCG0 α) (hcg0 α)
    (fun p q r s l => hCRbound α x hx_tsupport p q r s l)
    (fun ξ => hCGbound α x hx_tsupport ξ)
    (fun ξ => hcgbound α x hx_tsupport ξ)
    (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i))
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
      (smoothOrthoFrame_smooth (I := I) g x a)) hBon hBaon u
  have hKα_le : Kα α ≤ ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M), Kα β :=
    Finset.single_le_sum (fun β _ => hKα_nonneg β) hα_mem
  have hguu_nonneg : 0 ≤ g.inner x u u := metric_inner_self_nonneg (I := I) g x u
  calc g.inner x
        (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
            (smoothOrthoFrame_smooth (I := I) g x a)) x u)
        (∑ i : Fin (Module.finrank ℝ E), nablaBaseSlotCurv (I := I) g
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
            (smoothOrthoFrame_smooth (I := I) g x a)) x u)
      ≤ Kα α * g.inner x u u := by rw [hKα_def]; exact hpt
    _ ≤ (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M), Kα β) * g.inner x u u := by
        gcongr

theorem exists_uniform_nablaCurvSec_LeviCivita_gNorm_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ Kw : ℝ, 0 ≤ Kw ∧
      ∀ (x : M) (a : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
        g.inner x
            (nablaBaseSlotCurvFrameSumCLM (I := I) g
              (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame_smooth (I := I) g x i))
              (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                (smoothOrthoFrame_smooth (I := I) g x a)) x u)
            (nablaBaseSlotCurvFrameSumCLM (I := I) g
              (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame_smooth (I := I) g x i))
              (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
                (smoothOrthoFrame_smooth (I := I) g x a)) x u) ≤
          Kw * g.inner x u u := by
  classical
  obtain ⟨Kw, hKw_cont, hKw_nonneg, hKw_bound⟩ :=
    exists_continuous_nablaCurvSec_frameSum_gNorm_envelope (I := I) (M := M) g
  have hKpt := (isCompact_univ (X := M)).image hKw_cont
  obtain ⟨C₀, hC₀⟩ := hKpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x a u
  have hKw_le : Kw x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have huu_nonneg : 0 ≤ g.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g x u
  calc
    g.inner x
        (nablaBaseSlotCurvFrameSumCLM (I := I) g
          (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
            (smoothOrthoFrame_smooth (I := I) g x a)) x u)
        (nablaBaseSlotCurvFrameSumCLM (I := I) g
          (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
            (smoothOrthoFrame_smooth (I := I) g x a)) x u)
        ≤ Kw x * g.inner x u u := hKw_bound x a u
    _ ≤ max C₀ 0 * g.inner x u u := mul_le_mul_of_nonneg_right hKw_le huu_nonneg

end Connection
end Integral
end DifferentialGeometry

end
