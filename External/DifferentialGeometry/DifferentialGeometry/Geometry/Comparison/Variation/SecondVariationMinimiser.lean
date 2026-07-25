import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import DifferentialGeometry.Geometry.Exponential.ExpVariationSmooth
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicMfderivZero
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv



noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

theorem second_deriv_nonneg_of_isLocalMin {L : ℝ → ℝ} {x₀ c : ℝ}
    (hmin : IsLocalMin L x₀) (hL' : HasDerivAt L 0 x₀)
    (hL'' : HasDerivAt (deriv L) c x₀) : 0 ≤ c := by
  by_contra hc
  push Not at hc
  have hderiv0 : deriv L x₀ = 0 := hL'.deriv
  have hsecond : deriv (deriv L) x₀ = c := hL''.deriv
  have hmax : IsLocalMax L x₀ :=
    isLocalMax_of_deriv_deriv_neg (by rw [hsecond]; exact hc) hderiv0 hL'.continuousAt
  have hconst : L =ᶠ[𝓝 x₀] (fun _ => L x₀) :=
    eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  have hderiv_const : deriv L =ᶠ[𝓝 x₀] (fun _ => (0 : ℝ)) := by
    have := hconst.deriv
    refine this.trans ?_
    filter_upwards with x using deriv_const x (L x₀)
  have hL''0 : HasDerivAt (deriv L) c x₀ := hL''
  rw [hderiv_const.hasDerivAt_iff] at hL''0
  have : c = 0 := hL''0.unique (hasDerivAt_const x₀ (0 : ℝ))
  exact absurd this (ne_of_lt hc)

def reparam (r : ℝ) (s : ℝ) : ℝ :=
  (2 * r / Real.pi) * Real.arctan ((Real.pi / (2 * r)) * s)

theorem contDiff_reparam (r : ℝ) : ContDiff ℝ ∞ (reparam r) := by
  unfold reparam
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_const.mul contDiff_id))

@[simp] theorem reparam_zero (r : ℝ) : reparam r 0 = 0 := by
  simp [reparam, Real.arctan_zero]

theorem abs_reparam_lt (r : ℝ) (hr : 0 < r) (s : ℝ) : |reparam r s| < r := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : (0 : ℝ) < 2 * r / Real.pi := by positivity
  rw [reparam, abs_mul, abs_of_pos hcoef]
  have harctan : |Real.arctan ((Real.pi / (2 * r)) * s)| < Real.pi / 2 :=
    abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  calc (2 * r / Real.pi) * |Real.arctan ((Real.pi / (2 * r)) * s)|
      < (2 * r / Real.pi) * (Real.pi / 2) :=
        mul_lt_mul_of_pos_left harctan hcoef
    _ = r := by field_simp

theorem hasDerivAt_reparam_zero (r : ℝ) (hr : 0 < r) :
    HasDerivAt (reparam r) 1 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hinner : HasDerivAt (fun s : ℝ => (Real.pi / (2 * r)) * s)
      (Real.pi / (2 * r)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (Real.pi / (2 * r))
  have harctan : HasDerivAt Real.arctan (1 / (1 + ((Real.pi / (2 * r)) * (0 : ℝ)) ^ 2))
      ((Real.pi / (2 * r)) * (0 : ℝ)) :=
    Real.hasDerivAt_arctan _
  have hcomp := harctan.comp 0 hinner
  have hscaled := hcomp.const_mul (2 * r / Real.pi)
  have hval : (2 * r / Real.pi) *
      ((1 / (1 + ((Real.pi / (2 * r)) * (0 : ℝ)) ^ 2)) * (Real.pi / (2 * r))) = 1 := by
    have hr' : (2 * r) ≠ 0 := by positivity
    have hpi' : Real.pi ≠ 0 := ne_of_gt hpi
    rw [mul_zero]
    field_simp
    ring
  have : HasDerivAt (reparam r) ((2 * r / Real.pi) *
      ((1 / (1 + ((Real.pi / (2 * r)) * (0 : ℝ)) ^ 2)) * (Real.pi / (2 * r)))) 0 := by
    convert hscaled using 1
  rw [hval] at this
  exact this

theorem exists_cutoff_one_on_Icc (L : ℝ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) χ ∧ Set.EqOn χ 1 (Set.Icc 0 L) ∧
      Set.EqOn χ 0 ((Set.Ioo (-1 : ℝ) (L + 1))ᶜ) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  have hclosed_t : IsClosed (Set.Icc (0 : ℝ) L) := isClosed_Icc
  have hclosed_s : IsClosed ((Set.Ioo (-1 : ℝ) (L + 1))ᶜ) := isOpen_Ioo.isClosed_compl
  have hdisj : Disjoint ((Set.Ioo (-1 : ℝ) (L + 1))ᶜ) (Set.Icc 0 L) := by
    rw [Set.disjoint_compl_left_iff_subset]
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨f, hf0, hf1, hfIcc⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℝ) (n := (⊤ : ℕ∞)) hclosed_s hclosed_t hdisj
  refine ⟨f, ?_, hf1, hf0, hfIcc⟩
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f : ℝ → ℝ) := by
    rw [← contMDiff_iff_contDiff]; exact f.contMDiff
  exact hcd

section Construction

variable [T2Space (TangentBundle I M)] [ConnectedSpace M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [CompleteSpace E]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [CompleteSpace E] in
theorem contMDiff_smul_bundleField
    {γ : ℝ → M} {V : ℝ → E} {χ : ℝ → ℝ} {n : WithTop ℕ∞}
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) I n γ) (hχ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n χ)
    (hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent n
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)))) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent n
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (γ t) (χ t • V t))) := by
  intro t₀
  rw [contMDiffAt_totalSpace]
  refine ⟨hγ t₀, ?_⟩
  have hVfib := ((contMDiffAt_totalSpace (f := fun t : ℝ =>
    (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)))).1 (hVbundle t₀)).2
  have hsmul := (hχ t₀).smul hVfib
  refine hsmul.congr_of_eventuallyEq ?_
  have hbase : ∀ᶠ t in 𝓝 t₀, γ t ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet := by
    have hmem : (γ t₀) ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' (γ t₀)
    exact (hγ t₀).continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (γ t₀)).open_baseSet.mem_nhds hmem)
  filter_upwards [hbase] with t ht
  simp only [TotalSpace.mk']
  rw [(trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt ℝ
        (γ t) ht,
      (trivializationAt E (TangentSpace I) (γ t₀)).apply_eq_prod_continuousLinearEquivAt ℝ
        (γ t) ht]
  exact map_smul _ _ _

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem mdifferentiableAt_expMapIntrinsic_zero
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    MDifferentiableAt 𝓘(ℝ, E) I
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
      (0 : E) := by
  classical
  obtain ⟨ρ, hρ_pos, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  have hcont : Continuous (fun v : E => Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))) :=
    continuous_sqrt_gInner_self (I := I) g p
  set S : Set E :=
    {v : E | Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v)) < ρ} with hS_def
  have hS_open : IsOpen S := hcont.isOpen_preimage (Set.Iio ρ) isOpen_Iio
  have hzero_mem : (0 : E) ∈ S := by
    have h0 : Real.sqrt (g.inner p (show TangentSpace I p from (0 : E))
        (show TangentSpace I p from (0 : E))) = 0 := by
      have hgz : g.inner p (show TangentSpace I p from (0 : E))
          (show TangentSpace I p from (0 : E)) = 0 := by
        change g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0
        simp
      rw [hgz, Real.sqrt_zero]
    change Real.sqrt (g.inner p (show TangentSpace I p from (0 : E))
      (show TangentSpace I p from (0 : E))) < ρ
    rw [h0]; exact hρ_pos
  have hEvEq :
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
        =ᶠ[𝓝 (0 : E)]
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) := by
    refine Filter.eventuallyEq_of_mem (hS_open.mem_nhds hzero_mem) ?_
    intro v hv
    exact hagree hv
  refine (MDifferentiableAt.congr_of_eventuallyEq ?_ hEvEq)
  exact (expMap_contMDiffAt_zero (I := I) g p).mdifferentiableAt (by norm_num)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem exists_expVar_field
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V : ℝ → E) (L : ℝ)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ)
    (hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)))) :
    ∃ f : ℝ → ℝ → M,
      IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = γ t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s t) 0 (1 : ℝ) : E) = V t) ∧
      (V 0 = 0 → ∀ s : ℝ, f s 0 = γ 0) ∧
      (V L = 0 → ∀ s : ℝ, f s L = γ L) := by
  classical
  obtain ⟨χ, hχ_cd, hχ_one, hχ_zero, hχ_Icc⟩ := exists_cutoff_one_on_Icc L
  set Vc : ℝ → E := fun t => χ t • V t with hVc_def
  have hχ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) χ := by
    rw [contMDiff_iff_contDiff]; exact hχ_cd
  have hVcbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (Vc t))) :=
    contMDiff_smul_bundleField (I := I) hγ hχ_smooth hVbundle
  set V₀ : ℝ → TangentBundle I M :=
    fun t => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (Vc t)) with hV₀_def
  have hV₀proj : ∀ t, (V₀ t).proj = γ t := fun t => rfl
  have hV₀snd : ∀ t, (V₀ t).snd = Vc t := fun t => rfl
  set F : ℝ × ℝ → M :=
    fun p => expMapIntrinsic (I := I) g hEnorm (γ p.2)
      ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) with hF_def
  set U : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ∞) F p} with hU_def
  have hU_open : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have : ∀ᶠ q in 𝓝 p, ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ∞) F q :=
      (contMDiffAt_iff_contMDiffAt_nhds (by
        exact_mod_cast (by decide : ((8 : ℕ) : ℕ∞) ≠ (⊤ : ℕ∞)))).1 hp
    exact this
  set K : Set ℝ := Set.Icc (-1 : ℝ) (L + 1) with hK_def
  have hK_compact : IsCompact K := isCompact_Icc
  have hslice : ({(0 : ℝ)} ×ˢ K) ⊆ U := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    simp only [Set.mem_singleton_iff] at hs
    subst hs
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      expMapIntrinsic_variation_contMDiffAt_of_smallField (I := I) g hEnorm γ V₀ hγ
        hVcbundle hV₀proj 8 (by norm_num) t
    exact hδ 0 (Metric.mem_ball_self hδ_pos)
  obtain ⟨u, v, hu_open, _hv_open, h0u, hKv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) hK_compact hU_open hslice
  have h0u' : (0 : ℝ) ∈ u := h0u rfl
  obtain ⟨δ', hδ'_pos, hδ'_ball⟩ := Metric.isOpen_iff.mp hu_open 0 h0u'
  have hKsub : K ⊆ v := hKv
  set η : ℝ → ℝ := reparam δ' with hη_def
  have hη0 : η 0 = 0 := reparam_zero δ'
  have hη_cd : ContDiff ℝ (∞ : WithTop ℕ∞) η := contDiff_reparam δ'
  have hη_bound : ∀ s, η s ∈ u := by
    intro s
    refine hδ'_ball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_reparam_lt δ' hδ'_pos s
  have hΦη : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ∞)
      (fun p : ℝ × ℝ => (η p.1, p.2)) := by
    have hηM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ∞) η := by
      rw [contMDiff_iff_contDiff]; exact hη_cd.of_le (by decide)
    exact (hηM.comp contMDiff_fst).prodMk contMDiff_snd
  refine ⟨fun s t => F (η s, t), ?_, ?_, ?_, ?_, ?_⟩
  · change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (fun p : ℝ × ℝ => F (η p.1, p.2))
    intro p
    by_cases hpK : p.2 ∈ K
    · have hmem : (η p.1, p.2) ∈ U := huv ⟨hη_bound p.1, hKsub hpK⟩
      have hFat : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ∞) F (η p.1, p.2) := hmem
      have hcomp := hFat.comp p (hΦη p)
      exact hcomp
    · have hopen : IsOpen ((Set.Icc (-1 : ℝ) (L + 1))ᶜ) := isClosed_Icc.isOpen_compl
      have hp2 : p.2 ∈ (Set.Icc (-1 : ℝ) (L + 1))ᶜ := hpK
      have hsub : (Set.Icc (-1 : ℝ) (L + 1))ᶜ ⊆ (Set.Ioo (-1 : ℝ) (L + 1))ᶜ :=
        Set.compl_subset_compl.mpr Set.Ioo_subset_Icc_self
      have heq : (fun q : ℝ × ℝ => F (η q.1, q.2)) =ᶠ[𝓝 p] (fun q : ℝ × ℝ => γ q.2) := by
        have hnhds : (Set.univ ×ˢ (Set.Icc (-1 : ℝ) (L + 1))ᶜ) ∈ 𝓝 p :=
          (isOpen_univ.prod hopen).mem_nhds (Set.mem_prod.mpr ⟨Set.mem_univ _, hp2⟩)
        filter_upwards [hnhds] with q hq
        have hχq : χ q.2 = 0 := hχ_zero (hsub hq.2)
        have hVcq : Vc q.2 = 0 := by simp only [hVc_def, hχq, zero_smul]
        change F (η q.1, q.2) = γ q.2
        have harg : (η q.1 • (V₀ q.2).snd : E) = (0 : E) := by
          rw [hV₀snd, hVcq]; exact smul_zero _
        change expMapIntrinsic (I := I) g hEnorm (γ q.2)
          ((η q.1 • (V₀ q.2).snd : E) : TangentSpace I (γ q.2)) = γ q.2
        rw [harg]
        exact expMapIntrinsic_zero (I := I) g hEnorm (γ q.2)
      refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
      exact (hγ.of_le (by decide)).contMDiffAt.comp p contMDiffAt_snd
  · intro t
    change expMapIntrinsic (I := I) g hEnorm (γ t)
      ((η 0 • (V₀ t).snd : E) : TangentSpace I (γ t)) = γ t
    have harg : (η 0 • (V₀ t).snd : E) = (0 : E) := by rw [hη0]; exact zero_smul _ _
    rw [harg]
    exact expMapIntrinsic_zero (I := I) g hEnorm (γ t)
  · intro t ht
    have hVct : Vc t = V t := by
      simp only [hVc_def, hχ_one ht, Pi.one_apply, one_smul]
    set expFun : E → M :=
      fun v : E => (expMapIntrinsic (I := I) g hEnorm (γ t) (show TangentSpace I (γ t) from v) : M)
      with hexpFun_def
    have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I expFun (0 : E) :=
      mdifferentiableAt_expMapIntrinsic_zero (I := I) g hEnorm (γ t)
    have hexp_mfd : HasMFDerivAt 𝓘(ℝ, E) I expFun (0 : E)
        (ContinuousLinearMap.id ℝ E) := by
      have hh := hexp_mdiff.hasMFDerivAt
      rwa [mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm (γ t)] at hh
    have hinner_deriv : HasDerivAt (fun s : ℝ => η s • Vc t) (Vc t) 0 := by
      have hη' : HasDerivAt η 1 0 := hasDerivAt_reparam_zero δ' hδ'_pos
      have hsc := hη'.smul_const (Vc t)
      simpa using hsc
    have hinner_fd : HasFDerivAt (fun s : ℝ => η s • Vc t)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t)) 0 :=
      hinner_deriv.hasFDerivAt
    have hinner_mfd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => η s • Vc t) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t)) :=
      hinner_fd.hasMFDerivAt
    have hinner0 : (fun s : ℝ => η s • Vc t) 0 = (0 : E) := by
      simp only [hη0, zero_smul]
    have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => expFun (η s • Vc t)) 0
        ((ContinuousLinearMap.id ℝ E).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t))) := by
      have hcomp0 : HasMFDerivAt 𝓘(ℝ, E) I expFun ((fun s : ℝ => η s • Vc t) 0)
          (ContinuousLinearMap.id ℝ E) := by rw [hinner0]; exact hexp_mfd
      exact hcomp0.comp 0 hinner_mfd
    have hmfderiv := hcomp.mfderiv
    change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F (η s, t)) 0 (1 : ℝ) = V t
    have hfeq : (fun s : ℝ => F (η s, t)) = (fun s : ℝ => expFun (η s • Vc t)) := by
      funext s; rfl
    rw [hfeq, hmfderiv]
    change ((ContinuousLinearMap.id ℝ E).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t))) (1 : ℝ) = V t
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
    exact hVct
  · intro hV0 s
    have hVc0 : Vc 0 = 0 := by simp only [hVc_def, hV0, smul_zero]
    change expMapIntrinsic (I := I) g hEnorm (γ 0)
      ((η s • (V₀ (0 : ℝ)).snd : E) : TangentSpace I (γ 0)) = γ 0
    have harg : (η s • (V₀ (0 : ℝ)).snd : E) = (0 : E) := by
      rw [hV₀snd, hVc0]; exact smul_zero _
    rw [harg]
    exact expMapIntrinsic_zero (I := I) g hEnorm (γ 0)
  · intro hVL s
    have hVcL : Vc L = 0 := by simp only [hVc_def, hVL, smul_zero]
    change expMapIntrinsic (I := I) g hEnorm (γ L)
      ((η s • (V₀ L).snd : E) : TangentSpace I (γ L)) = γ L
    have harg : (η s • (V₀ L).snd : E) = (0 : E) := by
      rw [hV₀snd, hVcL]; exact smul_zero _
    rw [harg]
    exact expMapIntrinsic_zero (I := I) g hEnorm (γ L)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
theorem exists_expVar_fixEnd
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V : ℝ → E) (L : ℝ)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ)
    (hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t))))
    (hVL : V L = 0) :
    ∃ f : ℝ → ℝ → M,
      IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = γ t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s t) 0 (1 : ℝ) : E) = V t) ∧
      (∀ s : ℝ, f s L = γ L) := by
  obtain ⟨f, hf, hcentral, hderiv, _hfix0, hfixL⟩ :=
    exists_expVar_field (I := I) g hEnorm γ V L hγ hVbundle
  exact ⟨f, hf, hcentral, hderiv, hfixL hVL⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [ConnectedSpace M] in
theorem exists_sqDeriv_field
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    [PseudoMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V : ℝ → E) (L : ℝ)
    (hγsmooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ)
    (hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t))))
    (hVL : V L = 0) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1) :
    ∃ f : ℝ → ℝ → M,
      IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = γ t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s t) 0 (1 : ℝ) : E) = V t) ∧
      (∀ s : ℝ, f s L = γ L) ∧
      (((fun s : ℝ => dist (f s 0) (γ L)) =ᶠ[nhds (0 : ℝ)]
          (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)) →
        dist (f 0 0) (γ L) = L →
        HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * dist (f s 0) (γ L) ^ 2)
          (L * (- g.inner (γ 0)
              (show TangentSpace I (γ 0) from V 0)
              (mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ)))) 0) := by
  obtain ⟨f, hf, hcentral, hfield, hfixL⟩ :=
    exists_expVar_fixEnd (I := I) g hEnorm γ V L hγsmooth hVbundle hVL
  refine ⟨f, hf, hcentral, hfield, hfixL, ?_⟩
  intro hdist hdist0
  have hraw := halfSq_deriv_length (I := I) g γ f L hf hL hγ hcentral hfixL hUnit hdist hdist0
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, le_of_lt hL⟩
  have hfield0 :
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s 0) 0 (1 : ℝ) =
        (show TangentSpace I (γ 0) from V 0) := by
    change (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s 0) 0 (1 : ℝ) : E) = V 0
    exact hfield 0 h0mem
  rwa [hfield0] at hraw

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem exists_variation_realising_field_via_exp
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (V : ℝ → E) (L : ℝ)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ)
    (hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t)))) :
    ∃ f : ℝ → ℝ → M,
      IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = γ t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L,
        (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s t) 0 (1 : ℝ) : E) = V t) ∧
      (V 0 = 0 → ∀ s : ℝ, f s 0 = γ 0) ∧
      (V L = 0 → ∀ s : ℝ, f s L = γ L) := by
  classical
  obtain ⟨χ, hχ_cd, hχ_one, hχ_zero, hχ_Icc⟩ := exists_cutoff_one_on_Icc L
  set Vc : ℝ → E := fun t => χ t • V t with hVc_def
  have hχ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) χ := by
    rw [contMDiff_iff_contDiff]; exact hχ_cd
  have hVcbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (Vc t))) :=
    contMDiff_smul_bundleField (I := I) hγ hχ_smooth hVbundle
  set V₀ : ℝ → TangentBundle I M :=
    fun t => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (Vc t)) with hV₀_def
  have hV₀proj : ∀ t, (V₀ t).proj = γ t := fun t => rfl
  have hV₀snd : ∀ t, (V₀ t).snd = Vc t := fun t => rfl
  set F : ℝ × ℝ → M :=
    fun p => expMapIntrinsic (I := I) g hEnorm (γ p.2)
      ((p.1 • (V₀ p.2).snd : E) : TangentSpace I (γ p.2)) with hF_def
  set U : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ∞) F p} with hU_def
  have hU_open : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have : ∀ᶠ q in 𝓝 p, ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ∞) F q :=
      (contMDiffAt_iff_contMDiffAt_nhds (by
        exact_mod_cast (by decide : ((8 : ℕ) : ℕ∞) ≠ (⊤ : ℕ∞)))).1 hp
    exact this
  set K : Set ℝ := Set.Icc (-1 : ℝ) (L + 1) with hK_def
  have hK_compact : IsCompact K := isCompact_Icc
  have hslice : ({(0 : ℝ)} ×ˢ K) ⊆ U := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    simp only [Set.mem_singleton_iff] at hs
    subst hs
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      expMapIntrinsic_variation_contMDiffAt_of_smallField (I := I) g hEnorm γ V₀ hγ
        hVcbundle hV₀proj 8 (by norm_num) t
    exact hδ 0 (Metric.mem_ball_self hδ_pos)
  obtain ⟨u, v, hu_open, _hv_open, h0u, hKv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) hK_compact hU_open hslice
  have h0u' : (0 : ℝ) ∈ u := h0u rfl
  obtain ⟨δ', hδ'_pos, hδ'_ball⟩ := Metric.isOpen_iff.mp hu_open 0 h0u'
  have hKsub : K ⊆ v := hKv
  set η : ℝ → ℝ := reparam δ' with hη_def
  have hη0 : η 0 = 0 := reparam_zero δ'
  have hη_cd : ContDiff ℝ (∞ : WithTop ℕ∞) η := contDiff_reparam δ'
  have hη_bound : ∀ s, η s ∈ u := by
    intro s
    refine hδ'_ball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_reparam_lt δ' hδ'_pos s
  have hΦη : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ∞)
      (fun p : ℝ × ℝ => (η p.1, p.2)) := by
    have hηM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (8 : ℕ∞) η := by
      rw [contMDiff_iff_contDiff]; exact hη_cd.of_le (by decide)
    exact (hηM.comp contMDiff_fst).prodMk contMDiff_snd
  refine ⟨fun s t => F (η s, t), ?_, ?_, ?_, ?_, ?_⟩
  · change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ) (fun p : ℝ × ℝ => F (η p.1, p.2))
    intro p
    by_cases hpK : p.2 ∈ K
    · have hmem : (η p.1, p.2) ∈ U := huv ⟨hη_bound p.1, hKsub hpK⟩
      have hFat : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ∞) F (η p.1, p.2) := hmem
      have hcomp := hFat.comp p (hΦη p)
      exact hcomp
    · have hopen : IsOpen ((Set.Icc (-1 : ℝ) (L + 1))ᶜ) := isClosed_Icc.isOpen_compl
      have hp2 : p.2 ∈ (Set.Icc (-1 : ℝ) (L + 1))ᶜ := hpK
      have hsub : (Set.Icc (-1 : ℝ) (L + 1))ᶜ ⊆ (Set.Ioo (-1 : ℝ) (L + 1))ᶜ :=
        Set.compl_subset_compl.mpr Set.Ioo_subset_Icc_self
      have heq : (fun q : ℝ × ℝ => F (η q.1, q.2)) =ᶠ[𝓝 p] (fun q : ℝ × ℝ => γ q.2) := by
        have hnhds : (Set.univ ×ˢ (Set.Icc (-1 : ℝ) (L + 1))ᶜ) ∈ 𝓝 p :=
          (isOpen_univ.prod hopen).mem_nhds (Set.mem_prod.mpr ⟨Set.mem_univ _, hp2⟩)
        filter_upwards [hnhds] with q hq
        have hχq : χ q.2 = 0 := hχ_zero (hsub hq.2)
        have hVcq : Vc q.2 = 0 := by simp only [hVc_def, hχq, zero_smul]
        change F (η q.1, q.2) = γ q.2
        have harg : (η q.1 • (V₀ q.2).snd : E) = (0 : E) := by
          rw [hV₀snd, hVcq]; exact smul_zero _
        change expMapIntrinsic (I := I) g hEnorm (γ q.2)
          ((η q.1 • (V₀ q.2).snd : E) : TangentSpace I (γ q.2)) = γ q.2
        rw [harg]
        exact expMapIntrinsic_zero (I := I) g hEnorm (γ q.2)
      refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
      exact (hγ.of_le (by decide)).contMDiffAt.comp p contMDiffAt_snd
  · intro t
    change expMapIntrinsic (I := I) g hEnorm (γ t)
      ((η 0 • (V₀ t).snd : E) : TangentSpace I (γ t)) = γ t
    have harg : (η 0 • (V₀ t).snd : E) = (0 : E) := by rw [hη0]; exact zero_smul _ _
    rw [harg]
    exact expMapIntrinsic_zero (I := I) g hEnorm (γ t)
  · intro t ht
    have hVct : Vc t = V t := by
      simp only [hVc_def, hχ_one ht, Pi.one_apply, one_smul]
    set expFun : E → M :=
      fun v : E => (expMapIntrinsic (I := I) g hEnorm (γ t) (show TangentSpace I (γ t) from v) : M)
      with hexpFun_def
    have hexp_mdiff : MDifferentiableAt 𝓘(ℝ, E) I expFun (0 : E) :=
      mdifferentiableAt_expMapIntrinsic_zero (I := I) g hEnorm (γ t)
    have hexp_mfd : HasMFDerivAt 𝓘(ℝ, E) I expFun (0 : E)
        (ContinuousLinearMap.id ℝ E) := by
      have hh := hexp_mdiff.hasMFDerivAt
      rwa [mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm (γ t)] at hh
    have hinner_deriv : HasDerivAt (fun s : ℝ => η s • Vc t) (Vc t) 0 := by
      have hη' : HasDerivAt η 1 0 := hasDerivAt_reparam_zero δ' hδ'_pos
      have hsc := hη'.smul_const (Vc t)
      simpa using hsc
    have hinner_fd : HasFDerivAt (fun s : ℝ => η s • Vc t)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t)) 0 :=
      hinner_deriv.hasFDerivAt
    have hinner_mfd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => η s • Vc t) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t)) :=
      hinner_fd.hasMFDerivAt
    have hinner0 : (fun s : ℝ => η s • Vc t) 0 = (0 : E) := by
      simp only [hη0, zero_smul]
    have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => expFun (η s • Vc t)) 0
        ((ContinuousLinearMap.id ℝ E).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t))) := by
      have hcomp0 : HasMFDerivAt 𝓘(ℝ, E) I expFun ((fun s : ℝ => η s • Vc t) 0)
          (ContinuousLinearMap.id ℝ E) := by rw [hinner0]; exact hexp_mfd
      exact hcomp0.comp 0 hinner_mfd
    have hmfderiv := hcomp.mfderiv
    change mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F (η s, t)) 0 (1 : ℝ) = V t
    have hfeq : (fun s : ℝ => F (η s, t)) = (fun s : ℝ => expFun (η s • Vc t)) := by
      funext s; rfl
    rw [hfeq, hmfderiv]
    change ((ContinuousLinearMap.id ℝ E).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vc t))) (1 : ℝ) = V t
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
    exact hVct
  · intro hV0 s
    have hVc0 : Vc 0 = 0 := by simp only [hVc_def, hV0, smul_zero]
    change expMapIntrinsic (I := I) g hEnorm (γ 0)
      ((η s • (V₀ (0 : ℝ)).snd : E) : TangentSpace I (γ 0)) = γ 0
    have harg : (η s • (V₀ (0 : ℝ)).snd : E) = (0 : E) := by
      rw [hV₀snd, hVc0]; exact smul_zero _
    rw [harg]
    exact expMapIntrinsic_zero (I := I) g hEnorm (γ 0)
  · intro hVL s
    have hVcL : Vc L = 0 := by simp only [hVc_def, hVL, smul_zero]
    change expMapIntrinsic (I := I) g hEnorm (γ L)
      ((η s • (V₀ L).snd : E) : TangentSpace I (γ L)) = γ L
    have harg : (η s • (V₀ L).snd : E) = (0 : E) := by
      rw [hV₀snd, hVcL]; exact smul_zero _
    rw [harg]
    exact expMapIntrinsic_zero (I := I) g hEnorm (γ L)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem indexForm_nonneg_of_minimising_geodesic
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (γ : ℝ → M) (L : ℝ) (V : ℝ → E)
    (hL : 0 < L)
    (hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ)
    (hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t))))
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (hmin : ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) →
      η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (hVperp : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0)
    (hV0 : V 0 = 0) (hVL : V L = 0) :
    0 ≤ indexForm (I := I) g γ 0 L V V := by
  classical
  obtain ⟨f, hf_smooth, hf0, hf_vel, hf_fix0_if, hf_fixL_if⟩ :=
    exists_variation_realising_field_via_exp (I := I) g hEnorm γ V L hγ_smooth hVbundle
  have hf_fix0 : ∀ s : ℝ, f s 0 = γ 0 := hf_fix0_if hV0
  have hf_fixL : ∀ s : ℝ, f s L = γ L := hf_fixL_if hVL
  set L_arc : ℝ → ℝ := fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L with hL_arc
  set Vfield : ℝ → E :=
    fun t : ℝ => (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s t) 0 (1 : ℝ) : E) with hVfield
  have hVfield_Icc : ∀ t ∈ Set.Icc (0 : ℝ) L, Vfield t = V t := fun t ht => hf_vel t ht
  have hslice_C1 : ∀ s : ℝ, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t : ℝ => f s t) (Set.Icc 0 L) := by
    intro s
    have hincl : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun t : ℝ => (s, t)) := contMDiff_const.prodMk contMDiff_id
    have hcomp : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun t : ℝ => f s t) :=
      (hf_smooth : ContMDiff _ _ _ _).comp hincl
    exact (hcomp.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8))).contMDiffOn
  have hmin_arc : ∀ s : ℝ, L_arc 0 ≤ L_arc s := by
    intro s
    have hcentral : L_arc 0 = arcLength (I := I) g γ 0 L := by
      have hfun : (fun t : ℝ => f 0 t) = γ := by funext t; exact hf0 t
      change arcLength (I := I) g (fun t : ℝ => f 0 t) 0 L = arcLength (I := I) g γ 0 L
      rw [hfun]
    rw [hcentral]
    exact hmin (fun t : ℝ => f s t) (hslice_C1 s) (hf_fix0 s) (hf_fixL s)
  have hLocalMin : IsLocalMin L_arc 0 :=
    Filter.Eventually.of_forall hmin_arc
  have hfirst : HasDerivAt L_arc 0 0 :=
    first_variation_vanishes_for_geodesic (I := I) g γ f L hf_smooth hL hγ hf0
      hf_fix0 hf_fixL hUnit
  have hperp_field : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (Vfield t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0 := by
    intro t ht
    rw [hVfield_Icc t ht]; exact hVperp t ht
  have hsecond : HasDerivAt (fun s : ℝ => deriv L_arc s)
      (indexForm (I := I) g γ 0 L Vfield Vfield) 0 :=
    second_variation_of_arcLength_eq_indexForm (I := I) g γ f L Vfield hf_smooth hL hγ hf0
      (fun t => rfl) hUnit hf_fix0 hf_fixL hperp_field
  have hnonneg_field : 0 ≤ indexForm (I := I) g γ 0 L Vfield Vfield :=
    second_deriv_nonneg_of_isLocalMin hLocalMin hfirst hsecond
  have hVfield_Ioo_eventually : ∀ t ∈ Set.Ioo (0 : ℝ) L,
      (fun s : ℝ => (Vfield s : TangentSpace I (γ s)))
        =ᶠ[nhds t] (fun s : ℝ => (V s : TangentSpace I (γ s))) := by
    intro t ht
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) ?_
    intro s hs
    exact hVfield_Icc s (Set.Ioo_subset_Icc_self hs)
  have hintegrand_Ioo : ∀ t ∈ Set.Ioo (0 : ℝ) L,
      indexFormIntegrand (I := I) g γ Vfield Vfield t
        = indexFormIntegrand (I := I) g γ V V t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) L := Set.Ioo_subset_Icc_self ht
    have hpt : Vfield t = V t := hVfield_Icc t htIcc
    have hcov : DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g γ Vfield t
        = DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g γ V t :=
      covDerivAlong_congr_of_eventuallyEq (I := I) g γ (hVfield_Ioo_eventually t ht)
    simp only [indexFormIntegrand, hcov, hpt]
  have hindexForm_eq :
      indexForm (I := I) g γ 0 L Vfield Vfield = indexForm (I := I) g γ 0 L V V := by
    rw [indexForm_eq_intervalIntegral, indexForm_eq_intervalIntegral]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume L] with t htne hmem
    rw [Set.uIoc_of_le (le_of_lt hL)] at hmem
    exact hintegrand_Ioo t ⟨hmem.1, lt_of_le_of_ne hmem.2 htne⟩
  rw [← hindexForm_eq]
  exact hnonneg_field

end Construction

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
