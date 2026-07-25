import DifferentialGeometry.Analysis.ODE.SecondOrderGronwall
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Metric.InnerExpansion
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false






















noncomputable section

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]





omit [T2Space M] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGronwall_bounds_at
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {K b : ℝ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ, Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (J : ∀ t : ℝ, TangentSpace I (γ t))
    (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b, covDerivAlong (I := I) g γ (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (γ t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t))
    (hJ0 : J 0 = 0)
    {w : TangentSpace I (γ 0)}
    (hDJ0 : covDerivAlong (I := I) g γ J 0 = w) :
    (∀ t ∈ Icc (0 : ℝ) b,
      Real.sqrt (g.inner (γ t) (J t) (J t)) ≤
        t * Real.sqrt (g.inner (γ 0) w w) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (γ 0) w w))) t) ∧
    (∀ t ∈ Icc (0 : ℝ) b,
      t * Real.sqrt (g.inner (γ 0) w w) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (γ 0) w w))) t ≤
        Real.sqrt (g.inner (γ t) (J t) (J t))) := by
  classical
  have h0Icc : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb⟩
  set L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm with hL
  set Y : ℝ → EuclideanSpace ℝ ι :=
    fun t => L fun i => g.inner (γ t) (F i t) (J t) with hYdef
  set Y' : ℝ → EuclideanSpace ℝ ι :=
    fun t => L fun i =>
      g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ J t) with hY'def
  set Y'' : ℝ → EuclideanSpace ℝ ι :=
    fun t => L fun i =>
      g.inner (γ t) (F i t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ J s) t) with hY''def
  have hYapp : ∀ t i, Y t i = g.inner (γ t) (F i t) (J t) := fun t i => rfl
  have hder1 : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt Y (Y' t) t := by
    intro t ht
    have hpi : ∀ i, HasDerivAt (fun s => g.inner (γ s) (F i s) (J s))
        (g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ J t)) t := by
      intro i
      have h := inner_deriv_at (I := I) (n := 1) le_rfl g γ
        (F i) J t (hγ t ht) (hFdiff i t ht) (hJdiff t ht)
      rw [hpar i t ht] at h
      have hz : g.inner (γ t) (0 : TangentSpace I (γ t)) (J t) = 0 := by
        rw [map_zero]; rfl
      rwa [hz, zero_add] at h
    have hpi' : HasDerivAt
        (fun s => (fun i => g.inner (γ s) (F i s) (J s) : ι → ℝ))
        (fun i => g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ J t)) t :=
      hasDerivAt_pi.mpr hpi
    exact (L.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hpi'
  have hder2 : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt Y' (Y'' t) t := by
    intro t ht
    have hpi : ∀ i, HasDerivAt
        (fun s => g.inner (γ s) (F i s) (covDerivAlong (I := I) g γ J s))
        (g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ
            (fun s => covDerivAlong (I := I) g γ J s) t)) t := by
      intro i
      have h := inner_deriv_at (I := I) (n := 1) le_rfl g γ
        (F i) (fun s => covDerivAlong (I := I) g γ J s) t (hγ t ht)
        (hFdiff i t ht) (hDJdiff t ht)
      rw [hpar i t ht] at h
      have hz : g.inner (γ t) (0 : TangentSpace I (γ t))
          (covDerivAlong (I := I) g γ J t) = 0 := by
        rw [map_zero]; rfl
      rwa [hz, zero_add] at h
    have hpi' : HasDerivAt
        (fun s => (fun i =>
          g.inner (γ s) (F i s) (covDerivAlong (I := I) g γ J s) : ι → ℝ))
        (fun i => g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ
            (fun s => covDerivAlong (I := I) g γ J s) t)) t :=
      hasDerivAt_pi.mpr hpi
    exact (L.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hpi'
  have hnorm : ∀ t ∈ Icc (0 : ℝ) b, ∀ u : TangentSpace I (γ t),
      ‖(L fun i => g.inner (γ t) (F i t) u : EuclideanSpace ℝ ι)‖ ^ 2
        = g.inner (γ t) u u := by
    intro t ht u
    rw [EuclideanSpace.norm_sq_eq]
    have happ : ∀ i,
        ‖(L fun i => g.inner (γ t) (F i t) u : EuclideanSpace ℝ ι) i‖ ^ 2
          = (g.inner (γ t) (F i t) u) ^ 2 := by
      intro i
      rw [show (L fun i => g.inner (γ t) (F i t) u : EuclideanSpace ℝ ι) i
          = g.inner (γ t) (F i t) u from rfl, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_congr rfl fun i _ => happ i]
    exact (inner_self_eq_sum_sq g (γ t) (hcard t) (fun i => F i t)
      (hON t ht) u).symm
  have hbound : ∀ t ∈ Ico (0 : ℝ) b, ‖Y'' t‖ ≤ K * ‖Y t‖ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) b := Ico_subset_Icc_self ht
    have e1 : ‖Y'' t‖ ^ 2 = g.inner (γ t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ J s) t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ J s) t) := by
      change ‖(L fun i => g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ
            (fun s => covDerivAlong (I := I) g γ J s) t) :
        EuclideanSpace ℝ ι)‖ ^ 2 = _
      exact hnorm t htI _
    have e2 : ‖Y t‖ ^ 2 = g.inner (γ t) (J t) (J t) := by
      change ‖(L fun i => g.inner (γ t) (F i t) (J t) :
        EuclideanSpace ℝ ι)‖ ^ 2 = _
      exact hnorm t htI (J t)
    have h2 : ‖Y'' t‖ ^ 2 ≤ (K * ‖Y t‖) ^ 2 := by
      rw [mul_pow, e1, e2]
      exact hODE t ht
    have hs := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hs
  have hY0 : Y 0 = 0 := by
    refine PiLp.ext fun i => ?_
    rw [hYapp 0 i, hJ0]
    change (g.inner (γ 0) (F i 0)) 0 = 0
    exact map_zero _
  have hwnorm : ‖Y' 0‖ = Real.sqrt (g.inner (γ 0) w w) := by
    have hsq : ‖Y' 0‖ ^ 2 = g.inner (γ 0) w w := by
      have h := hnorm 0 h0Icc (covDerivAlong (I := I) g γ J 0)
      rw [hDJ0] at h
      change ‖(L fun i => g.inner (γ 0) (F i 0)
          (covDerivAlong (I := I) g γ J 0) : EuclideanSpace ℝ ι)‖ ^ 2 = _
      rw [hDJ0]
      exact h
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hJnorm : ∀ t ∈ Icc (0 : ℝ) b,
      Real.sqrt (g.inner (γ t) (J t) (J t)) = ‖Y t‖ := by
    intro t ht
    have hsq : ‖Y t‖ ^ 2 = g.inner (γ t) (J t) (J t) := by
      change ‖(L fun i => g.inner (γ t) (F i t) (J t) : EuclideanSpace ℝ ι)‖ ^ 2 = _
      exact hnorm t ht (J t)
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hle := gronwall_le_linear (Y := Y) (Y' := Y') (Y'' := Y'') hK hb
    (fun t ht => (hder1 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder2 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder1 t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => (hder2 t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hbound hY0 rfl
  have hge := gronwall_ge_linear (Y := Y) (Y' := Y') (Y'' := Y'') hK hb
    (fun t ht => (hder1 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder2 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder1 t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => (hder2 t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hbound hY0 rfl
  constructor
  · intro t ht
    simpa [hJnorm t ht, hwnorm] using hle t ht
  · intro t ht
    simpa [hJnorm t ht, hwnorm] using hge t ht



omit [T2Space M] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGronwall_bounds
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ, Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (J : ∀ t : ℝ, TangentSpace I (γ t))
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b, covDerivAlong (I := I) g γ (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (γ t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t))
    (hJ0 : J 0 = 0)
    {w : TangentSpace I (γ 0)}
    (hDJ0 : covDerivAlong (I := I) g γ J 0 = w) :
    (∀ t ∈ Icc (0 : ℝ) b,
      Real.sqrt (g.inner (γ t) (J t) (J t)) ≤
        t * Real.sqrt (g.inner (γ 0) w w) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (γ 0) w w))) t) ∧
    (∀ t ∈ Icc (0 : ℝ) b,
      t * Real.sqrt (g.inner (γ 0) w w) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (γ 0) w w))) t ≤
        Real.sqrt (g.inner (γ t) (J t) (J t))) := by
  refine covGronwall_bounds_at (I := I) g γ (fun t _ => ?_) hcard F J
    hK hb hpar hON hFdiff hJdiff hDJdiff hODE hJ0 hDJ0
  exact hγ.contMDiffAt







omit [T2Space M] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGronwall_ne_zero_at
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {K b : ℝ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ, Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (J : ∀ t : ℝ, TangentSpace I (γ t))
    (hK : 0 ≤ K) (hb : 0 < b)
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b, covDerivAlong (I := I) g γ (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (γ t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t))
    (hJ0 : J 0 = 0)
    {w : TangentSpace I (γ 0)}
    (hDJ0 : covDerivAlong (I := I) g γ J 0 = w)
    (hsmall : gronwallBound 0 (max K 1)
        (K * (b * Real.sqrt (g.inner (γ 0) w w))) b
      < b * Real.sqrt (g.inner (γ 0) w w)) :
    J b ≠ 0 := by
  classical
  have h0Icc : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hbIcc : b ∈ Icc (0 : ℝ) b := ⟨hb.le, le_rfl⟩
  set L : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm with hL

  set Y : ℝ → EuclideanSpace ℝ ι :=
    fun t => L fun i => g.inner (γ t) (F i t) (J t) with hYdef
  set Y' : ℝ → EuclideanSpace ℝ ι :=
    fun t => L fun i =>
      g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ J t) with hY'def
  set Y'' : ℝ → EuclideanSpace ℝ ι :=
    fun t => L fun i =>
      g.inner (γ t) (F i t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ J s) t) with hY''def
  have hYapp : ∀ t i, Y t i = g.inner (γ t) (F i t) (J t) := fun t i => rfl
  have hY'app : ∀ t i,
      Y' t i = g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ J t) :=
    fun t i => rfl
  have hY''app : ∀ t i, Y'' t i =
      g.inner (γ t) (F i t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ J s) t) := fun t i => rfl

  have hder1 : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt Y (Y' t) t := by
    intro t ht
    have hpi : ∀ i, HasDerivAt (fun s => g.inner (γ s) (F i s) (J s))
        (g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ J t)) t := by
      intro i
      have h := inner_deriv_at (I := I) (n := 1) le_rfl g γ
        (F i) J t (hγ t ht) (hFdiff i t ht) (hJdiff t ht)
      rw [hpar i t ht] at h
      have hz : g.inner (γ t) (0 : TangentSpace I (γ t)) (J t) = 0 := by
        rw [map_zero]; rfl
      rwa [hz, zero_add] at h
    have hpi' : HasDerivAt
        (fun s => (fun i => g.inner (γ s) (F i s) (J s) : ι → ℝ))
        (fun i => g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ J t)) t :=
      hasDerivAt_pi.mpr hpi
    exact (L.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hpi'

  have hder2 : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt Y' (Y'' t) t := by
    intro t ht
    have hpi : ∀ i, HasDerivAt
        (fun s => g.inner (γ s) (F i s) (covDerivAlong (I := I) g γ J s))
        (g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ
            (fun s => covDerivAlong (I := I) g γ J s) t)) t := by
      intro i
      have h := inner_deriv_at (I := I) (n := 1) le_rfl g γ
        (F i) (fun s => covDerivAlong (I := I) g γ J s) t (hγ t ht)
        (hFdiff i t ht) (hDJdiff t ht)
      rw [hpar i t ht] at h
      have hz : g.inner (γ t) (0 : TangentSpace I (γ t))
          (covDerivAlong (I := I) g γ J t) = 0 := by
        rw [map_zero]; rfl
      rwa [hz, zero_add] at h
    have hpi' : HasDerivAt
        (fun s => (fun i =>
          g.inner (γ s) (F i s) (covDerivAlong (I := I) g γ J s) : ι → ℝ))
        (fun i => g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ
            (fun s => covDerivAlong (I := I) g γ J s) t)) t :=
      hasDerivAt_pi.mpr hpi
    exact (L.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hpi'

  have hnorm : ∀ t ∈ Icc (0 : ℝ) b, ∀ u : TangentSpace I (γ t),
      ‖(L fun i => g.inner (γ t) (F i t) u : EuclideanSpace ℝ ι)‖ ^ 2
        = g.inner (γ t) u u := by
    intro t ht u
    rw [EuclideanSpace.norm_sq_eq]
    have happ : ∀ i,
        ‖(L fun i => g.inner (γ t) (F i t) u : EuclideanSpace ℝ ι) i‖ ^ 2
          = (g.inner (γ t) (F i t) u) ^ 2 := by
      intro i
      rw [show (L fun i => g.inner (γ t) (F i t) u : EuclideanSpace ℝ ι) i
          = g.inner (γ t) (F i t) u from rfl, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_congr rfl fun i _ => happ i]
    exact (inner_self_eq_sum_sq g (γ t) (hcard t) (fun i => F i t)
      (hON t ht) u).symm

  have hbound : ∀ t ∈ Ico (0 : ℝ) b, ‖Y'' t‖ ≤ K * ‖Y t‖ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) b := Ico_subset_Icc_self ht
    have e1 : ‖Y'' t‖ ^ 2 = g.inner (γ t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ J s) t)
        (covDerivAlong (I := I) g γ
          (fun s => covDerivAlong (I := I) g γ J s) t) := by
      change ‖(L fun i => g.inner (γ t) (F i t)
          (covDerivAlong (I := I) g γ
            (fun s => covDerivAlong (I := I) g γ J s) t) :
        EuclideanSpace ℝ ι)‖ ^ 2 = _
      exact hnorm t htI _
    have e2 : ‖Y t‖ ^ 2 = g.inner (γ t) (J t) (J t) := by
      change ‖(L fun i => g.inner (γ t) (F i t) (J t) :
        EuclideanSpace ℝ ι)‖ ^ 2 = _
      exact hnorm t htI (J t)
    have h2 : ‖Y'' t‖ ^ 2 ≤ (K * ‖Y t‖) ^ 2 := by
      rw [mul_pow, e1, e2]
      exact hODE t ht
    have hs := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hs

  have hY0 : Y 0 = 0 := by
    refine PiLp.ext fun i => ?_
    rw [hYapp 0 i, hJ0]
    change (g.inner (γ 0) (F i 0)) 0 = 0
    exact map_zero _
  have hwnorm : ‖Y' 0‖ = Real.sqrt (g.inner (γ 0) w w) := by
    have hsq : ‖Y' 0‖ ^ 2 = g.inner (γ 0) w w := by
      have h := hnorm 0 h0Icc (covDerivAlong (I := I) g γ J 0)
      rw [hDJ0] at h
      change ‖(L fun i => g.inner (γ 0) (F i 0)
          (covDerivAlong (I := I) g γ J 0) : EuclideanSpace ℝ ι)‖ ^ 2 = _
      rw [hDJ0]
      exact h
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

  have hYb : Y b ≠ 0 := by
    refine gronwall_ne_zero (Y := Y) (Y' := Y') (Y'' := Y'') hK hb
      (fun t ht => (hder1 t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder2 t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder1 t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => (hder2 t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      hbound hY0 rfl ?_
    rw [hwnorm]
    exact hsmall

  intro hJb
  apply hYb
  refine PiLp.ext fun i => ?_
  rw [hYapp b i, hJb]
  change (g.inner (γ b) (F i b)) 0 = (0 : EuclideanSpace ℝ ι) i
  rw [map_zero]
  rfl



omit [T2Space M] [SigmaCompactSpace M] in
omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGronwall_ne_zero
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ, Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (γ t))
    (J : ∀ t : ℝ, TangentSpace I (γ t))
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 < b)
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b, covDerivAlong (I := I) g γ (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (γ t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
        (covDerivAlong (I := I) g γ (fun s => covDerivAlong (I := I) g γ J s) t)
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t))
    (hJ0 : J 0 = 0)
    {w : TangentSpace I (γ 0)}
    (hDJ0 : covDerivAlong (I := I) g γ J 0 = w)
    (hsmall : gronwallBound 0 (max K 1)
        (K * (b * Real.sqrt (g.inner (γ 0) w w))) b
      < b * Real.sqrt (g.inner (γ 0) w w)) :
    J b ≠ 0 := by
  refine covGronwall_ne_zero_at (I := I) g γ (fun t _ => ?_) hcard F J
    hK hb hpar hON hFdiff hJdiff hDJdiff hODE hJ0 hDJ0 hsmall
  exact hγ.contMDiffAt

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
