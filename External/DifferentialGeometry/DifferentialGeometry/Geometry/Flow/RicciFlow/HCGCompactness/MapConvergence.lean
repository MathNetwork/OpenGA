import DifferentialGeometry.Analysis.Calculus.MapConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ArzelaAscoli
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false



















namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

section MapArzelaAscoli

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem cmm_finiteDimensional (r : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) := by
  induction r with
  | zero =>
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearEquiv.finiteDimensional
  | succ r ih =>
      haveI := ih
      exact ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (r + 1) => E) F).symm.toLinearEquiv).finiteDimensional

omit [FiniteDimensional ℝ F] in




private theorem equicont_iteratedFDeriv
    (Φ : ℕ → E → F) (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k))
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) (r : ℕ) :
    Equicontinuous (fun k => iteratedFDeriv ℝ r (Φ k)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  obtain ⟨M, hM⟩ := hbdd (r + 1) (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1)
  intro ε hε
  have hM₀ : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  refine ⟨min 1 (ε / (max M 0 + 1)), lt_min one_pos (by positivity), fun x hx k => ?_⟩
  have hx1 : x ∈ Metric.closedBall x₀ 1 :=
    Metric.mem_closedBall.mpr (hx.trans_le (min_le_left _ _)).le
  have hx₀1 : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one

  have hlip : ‖iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r (Φ k) x₀‖
      ≤ max M 0 * ‖x - x₀‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f' := fun y => (iteratedFDeriv ℝ (r + 1) (Φ k) y).curryLeft)
      (fun y _ => ((contDiff_infty.mp (hΦ k) (r + 1)).ftaylorSeries.fderiv r
        (by exact_mod_cast lt_add_one r) y).hasFDerivWithinAt)
      (fun y hy => ?_) (convex_closedBall x₀ 1) hx₀1 hx1
    rw [ContinuousMultilinearMap.curryLeft_norm]
    exact (hM k y hy).trans (le_max_left M 0)
  rw [dist_comm, dist_eq_norm]
  calc ‖iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r (Φ k) x₀‖
      ≤ max M 0 * ‖x - x₀‖ := hlip
    _ ≤ max M 0 * (ε / (max M 0 + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM₀
        rw [← dist_eq_norm]
        exact (hx.trans_le (min_le_right _ _)).le
    _ < (max M 0 + 1) * (ε / (max M 0 + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := by field_simp






















theorem exists_cInf_subseq
    (Φ : ℕ → E → F) (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k))
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Φ (φ k)) Φinf := by
  classical

  let Fb : (r : ℕ) → ℕ → C(E, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r k => ⟨iteratedFDeriv ℝ r (Φ k),
      (contDiff_infty.mp (hΦ k) r).continuous_iteratedFDeriv'⟩

  have hcpt : ∀ r : ℕ, IsCompact (closure (Set.range (Fb r))) := by
    intro r
    haveI := cmm_finiteDimensional (E := E) (F := F) r
    refine arzelaAscoli_isCompact_closure (Fb r)
      (equicont_iteratedFDeriv Φ hΦ hbdd r) (fun x => ?_)
    obtain ⟨M, hM⟩ := hbdd r {x} isCompact_singleton
    exact ⟨M, fun k => hM k x rfl⟩

  haveI : ∀ r : ℕ, CompactSpace (closure (Set.range (Fb r))) :=
    fun r => isCompact_iff_compactSpace.mp (hcpt r)
  set xseq : ℕ → Π r : ℕ, closure (Set.range (Fb r)) :=
    fun k r => ⟨Fb r k, subset_closure ⟨k, rfl⟩⟩ with hxseq
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ :
        IsCompact (Set.univ : Set (Π r : ℕ, closure (Set.range (Fb r))))).tendsto_subseq
      (x := xseq) (fun k => Set.mem_univ _)
  set G : (r : ℕ) → C(E, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r => (a r : C(E, _)) with hG
  have hGconv : ∀ r : ℕ, Tendsto (fun k => Fb r (φ k)) atTop (𝓝 (G r)) := by
    intro r
    have h1 : Tendsto (fun k => xseq (φ k) r) atTop (𝓝 (a r)) :=
      (tendsto_pi_nhds.mp ha) r
    have h2 := (continuous_subtype_val.tendsto (a r)).comp h1
    simpa [hxseq, hG, Function.comp] using h2
  have hGunif : ∀ r : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => ⇑(Fb r (φ k))) (⇑(G r)) atTop K :=
    fun r => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp (hGconv r)

  have hGderiv : ∀ (r : ℕ) (x₀ : E),
      HasFDerivAt (⇑(G r)) (((G (r + 1)) x₀).curryLeft) x₀ := by
    intro r x₀
    have hball : IsCompact (Metric.closedBall x₀ 1) := isCompact_closedBall x₀ 1
    have hf' : TendstoUniformlyOn (fun k y => ((Fb (r + 1) (φ k)) y).curryLeft)
        (fun y => ((G (r + 1)) y).curryLeft) atTop (Metric.ball x₀ 1) := by
      have h2 := ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (r + 1) => E) F).isometry.uniformContinuous).comp_tendstoUniformlyOn
        ((hGunif (r + 1) _ hball).mono Metric.ball_subset_closedBall)
      simpa [Function.comp_def] using h2
    have hfd : ∀ k : ℕ, ∀ y ∈ Metric.ball x₀ 1,
        HasFDerivAt (⇑(Fb r (φ k))) (((Fb (r + 1) (φ k)) y).curryLeft) y := fun k y _ =>
      (contDiff_infty.mp (hΦ (φ k)) (r + 1)).ftaylorSeries.fderiv r
        (by exact_mod_cast lt_add_one r) y
    have hfg : ∀ y ∈ Metric.ball x₀ 1,
        Tendsto (fun k => (Fb r (φ k)) y) atTop (𝓝 ((G r) y)) := fun y hy =>
      (hGunif r _ hball).tendsto_at (Metric.ball_subset_closedBall hy)
    exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hf' hfd hfg
      (Metric.mem_ball_self one_pos)

  have htaylor : HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => ((G 0) y).curry0) (fun y r => (G r) y) :=
    ⟨fun _ => rfl, fun m _ y => hGderiv m y, fun m _ => (G m).continuous⟩
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => ((G 0) y).curry0) := htaylor.contDiff
  have hid : ∀ (r : ℕ) (y : E),
      iteratedFDeriv ℝ r (fun z => ((G 0) z).curry0) y = (G r) y := fun r y =>
    (htaylor.eq_iteratedFDeriv (by exact_mod_cast le_top) y).symm
  refine ⟨φ, fun y => ((G 0) y).curry0, hφ, hsmooth, ?_⟩
  intro K hK _ p
  refine mapCPConvOn_of_tendstoUniformly
    (fun k => (hΦ (φ k)).of_le (by exact_mod_cast le_top))
    (hsmooth.of_le (by exact_mod_cast le_top)) ?_
  intro r _hr
  have h := hGunif r K hK
  rw [show (⇑(G r)) = fun y => iteratedFDeriv ℝ r (fun z => ((G 0) z).curry0) y from
    funext fun y => (hid r y).symm] at h
  exact h








omit [FiniteDimensional ℝ F] in




private theorem equicontOn_iteratedFDerivWithin
    {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ r (Φ k) U x‖ ≤ M)
    (r : ℕ) :
    Equicontinuous
      (fun k => fun x : U => iteratedFDerivWithin ℝ r (Φ k) U (x : E)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨ρ, hρpos, hρU⟩ := Metric.isOpen_iff.mp hU (x₀ : E) x₀.2
  have hsub : Metric.closedBall (x₀ : E) (ρ / 2) ⊆ U := by
    intro y hy
    apply hρU
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith
  obtain ⟨M, hM⟩ :=
    hbdd (r + 1) (Metric.closedBall (x₀ : E) (ρ / 2))
      (isCompact_closedBall _ _) hsub
  have hM₀ : (0 : ℝ) ≤ max M 0 := le_max_right M 0
  refine ⟨min (ρ / 2) (ε / (max M 0 + 1)),
    lt_min (by positivity) (by positivity), fun x hx k => ?_⟩
  rw [Subtype.dist_eq] at hx
  have hxsub : (x : E) ∈ Metric.closedBall (x₀ : E) (ρ / 2) :=
    Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hx (min_le_left _ _)))
  have hx₀sub : (x₀ : E) ∈ Metric.closedBall (x₀ : E) (ρ / 2) :=
    Metric.mem_closedBall_self (by positivity)
  have hlip :
      ‖iteratedFDerivWithin ℝ r (Φ k) U (x : E) -
          iteratedFDerivWithin ℝ r (Φ k) U (x₀ : E)‖
        ≤ max M 0 * ‖(x : E) - (x₀ : E)‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f' := fun y => (iteratedFDerivWithin ℝ (r + 1) (Φ k) U y).curryLeft)
      (fun y hy => ?_) (fun y hy => ?_)
      (convex_closedBall _ _) hx₀sub hxsub
    · exact (((hΦ k).ftaylorSeriesWithin hU.uniqueDiffOn).fderivWithin r
        (by exact_mod_cast WithTop.coe_lt_top r) y (hsub hy)).mono hsub
    · rw [ContinuousMultilinearMap.curryLeft_norm]
      exact (hM k y hy).trans (le_max_left M 0)
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖iteratedFDerivWithin ℝ r (Φ k) U (x : E) -
          iteratedFDerivWithin ℝ r (Φ k) U (x₀ : E)‖
        ≤ max M 0 * ‖(x : E) - (x₀ : E)‖ := hlip
    _ ≤ max M 0 * (ε / (max M 0 + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM₀
        rw [← dist_eq_norm]
        exact le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
    _ < (max M 0 + 1) * (ε / (max M 0 + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := by field_simp













theorem exists_cInf_subseq_on
    {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
        ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧
        MapCInfConvOnCompacts U (fun k => Φ (φ k)) Φinf := by
  classical
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace

  have hbddW : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ r (Φ k) U x‖ ≤ M := by
    intro r K hK hKU
    obtain ⟨M, hM⟩ := hbdd r K hK hKU
    exact ⟨M, fun k x hx => by
      rw [iteratedFDerivWithin_of_isOpen r hU (hKU hx)]; exact hM k x hx⟩

  let Fb : (r : ℕ) → ℕ → C(U, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r k => ⟨fun x => iteratedFDerivWithin ℝ r (Φ k) U (x : E),
      ((hΦ k).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
        hU.uniqueDiffOn).comp_continuous continuous_subtype_val (fun x => x.2)⟩
  have hcpt : ∀ r : ℕ, IsCompact (closure (Set.range (Fb r))) := by
    intro r
    haveI := cmm_finiteDimensional (E := E) (F := F) r
    refine arzelaAscoli_isCompact_closure (Fb r)
      (equicontOn_iteratedFDerivWithin hU Φ hΦ hbddW r) (fun x => ?_)
    obtain ⟨M, hM⟩ := hbddW r {(x : E)} isCompact_singleton
      (Set.singleton_subset_iff.mpr x.2)
    exact ⟨M, fun k => hM k (x : E) rfl⟩
  haveI : ∀ r : ℕ, CompactSpace (closure (Set.range (Fb r))) :=
    fun r => isCompact_iff_compactSpace.mp (hcpt r)
  set xseq : ℕ → Π r : ℕ, closure (Set.range (Fb r)) :=
    fun k r => ⟨Fb r k, subset_closure ⟨k, rfl⟩⟩ with hxseq
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ :
        IsCompact (Set.univ : Set (Π r : ℕ, closure (Set.range (Fb r))))).tendsto_subseq
      (x := xseq) (fun k => Set.mem_univ _)
  set G : (r : ℕ) → C(U, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F) :=
    fun r => (a r : C(U, _)) with hG
  have hGconv : ∀ r : ℕ, Tendsto (fun k => Fb r (φ k)) atTop (𝓝 (G r)) := by
    intro r
    have h1 : Tendsto (fun k => xseq (φ k) r) atTop (𝓝 (a r)) := (tendsto_pi_nhds.mp ha) r
    have h2 := (continuous_subtype_val.tendsto (a r)).comp h1
    simpa [hxseq, hG, Function.comp] using h2
  have hGunif : ∀ r : ℕ, ∀ K : Set U, IsCompact K →
      TendstoUniformlyOn (fun k => ⇑(Fb r (φ k))) (⇑(G r)) atTop K :=
    fun r => ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp (hGconv r)

  let Gext : (r : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin r => E) F :=
    fun r x => if h : x ∈ U then (G r) ⟨x, h⟩ else 0
  have hGext : ∀ (r : ℕ) (x : E) (hx : x ∈ U), Gext r x = (G r) ⟨x, hx⟩ :=
    fun r x hx => dif_pos hx
  let Φinf : E → F := fun x => (Gext 0 x).curry0

  have hGunifE : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDerivWithin ℝ r (Φ (φ k)) U)
        (Gext r) atTop K := by
    intro r K hK hKU
    have hKsub : IsCompact (Subtype.val ⁻¹' K : Set U) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.mpr hKU]
      exact hK
    have hsub := hGunif r (Subtype.val ⁻¹' K) hKsub
    rw [Metric.tendstoUniformlyOn_iff] at hsub ⊢
    intro ε hε
    filter_upwards [hsub ε hε] with k hk x hx
    have hxU : x ∈ U := hKU hx
    have hkx := hk ⟨x, hxU⟩ hx
    rwa [show (G r) ⟨x, hxU⟩ = Gext r x from (hGext r x hxU).symm] at hkx

  have hGderiv : ∀ (r : ℕ) (x₀ : E), x₀ ∈ U →
      HasFDerivAt (Gext r) ((Gext (r + 1) x₀).curryLeft) x₀ := by
    intro r x₀ hx₀
    obtain ⟨ρ, hρpos, hρU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
    have hball2U : Metric.closedBall x₀ (ρ / 2) ⊆ U := fun y hy => by
      apply hρU; rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith
    have hballU : Metric.ball x₀ (ρ / 2) ⊆ U :=
      fun y hy => hball2U (Metric.ball_subset_closedBall hy)
    have hf' : TendstoUniformlyOn
        (fun k y => (iteratedFDerivWithin ℝ (r + 1) (Φ (φ k)) U y).curryLeft)
        (fun y => (Gext (r + 1) y).curryLeft) atTop (Metric.ball x₀ (ρ / 2)) := by
      have h2 := ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (r + 1) => E) F).isometry.uniformContinuous).comp_tendstoUniformlyOn
        ((hGunifE (r + 1) (Metric.closedBall x₀ (ρ / 2)) (isCompact_closedBall _ _)
            hball2U).mono Metric.ball_subset_closedBall)
      simpa [Function.comp_def] using h2
    have hfd : ∀ k : ℕ, ∀ y ∈ Metric.ball x₀ (ρ / 2),
        HasFDerivAt (iteratedFDerivWithin ℝ r (Φ (φ k)) U)
          ((iteratedFDerivWithin ℝ (r + 1) (Φ (φ k)) U y).curryLeft) y := fun k y hy =>
      (((hΦ (φ k)).ftaylorSeriesWithin hU.uniqueDiffOn).fderivWithin r
        (by exact_mod_cast WithTop.coe_lt_top r) y (hballU hy)).hasFDerivAt
          (hU.mem_nhds (hballU hy))
    have hfg : ∀ y ∈ Metric.ball x₀ (ρ / 2),
        Tendsto (fun k => iteratedFDerivWithin ℝ r (Φ (φ k)) U y) atTop (𝓝 (Gext r y)) :=
      fun y hy => (hGunifE r {y} isCompact_singleton
        (Set.singleton_subset_iff.mpr (hballU hy))).tendsto_at rfl
    exact hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hf' hfd hfg
      (Metric.mem_ball_self (by positivity))

  have hcontGext : ∀ m : ℕ, ContinuousOn (Gext m) U := by
    intro m
    rw [continuousOn_iff_continuous_restrict]
    have he : Set.restrict U (Gext m) = ⇑(G m) := by
      funext x; simp only [Set.restrict_apply]; rw [hGext m (x : E) x.2]
    rw [he]; exact (G m).continuous
  have htaylor : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) Φinf (fun y r => Gext r y) U :=
    ⟨fun _ _ => rfl, fun m _ x hx => (hGderiv m x hx).hasFDerivWithinAt,
      fun m _ => hcontGext m⟩
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Φinf U := htaylor.contDiffOn
  have hid : ∀ (r : ℕ), ∀ x ∈ U, iteratedFDerivWithin ℝ r Φinf U x = Gext r x :=
    fun r x hx =>
      (htaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast le_top)
        hU.uniqueDiffOn hx).symm
  refine ⟨φ, Φinf, hφ, hsmooth, ?_⟩
  intro K hK hKU p ε hε
  have key : ∀ r : ℕ, r ≤ p → ∀ᶠ k in atTop, ∀ x ∈ K,
      mapDerivNorm r (Φ (φ k)) Φinf x ≤ ε := by
    intro r _hr
    have hunif := hGunifE r K hK hKU
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    filter_upwards [hunif ε hε] with k hk x hx
    have hxU : x ∈ U := hKU hx
    have e1 : iteratedFDeriv ℝ r (fun y => Φ (φ k) y - Φinf y) x
        = iteratedFDerivWithin ℝ r (fun y => Φ (φ k) y - Φinf y) U x :=
      (iteratedFDerivWithin_of_isOpen r hU hxU).symm
    have e2 : iteratedFDerivWithin ℝ r (fun y => Φ (φ k) y - Φinf y) U x
        = iteratedFDerivWithin ℝ r (Φ (φ k)) U x - iteratedFDerivWithin ℝ r Φinf U x :=
      iteratedFDerivWithin_sub_apply
        (((hΦ (φ k)).contDiffWithinAt hxU).of_le (by exact_mod_cast le_top))
        ((hsmooth.contDiffWithinAt hxU).of_le (by exact_mod_cast le_top))
        hU.uniqueDiffOn hxU
    rw [mapDerivNorm, e1, e2, hid r x hxU, ← dist_eq_norm, dist_comm]
    exact le_of_lt (hk x hx)
  have hfin : ∀ᶠ k in atTop, ∀ r ∈ Set.Iic p, ∀ x ∈ K,
      mapDerivNorm r (Φ (φ k)) Φinf x ≤ ε :=
    (Set.finite_Iic p).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩

end MapArzelaAscoli

end HCGCompactness
end DifferentialGeometry
