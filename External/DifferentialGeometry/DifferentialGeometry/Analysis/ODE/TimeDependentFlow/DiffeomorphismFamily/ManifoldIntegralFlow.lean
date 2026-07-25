import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.MeanValue


namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Manifold Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

noncomputable def autonomizedFlowVF (X : ℝ → ∀ x : M, TangentSpace I x) :
    (p : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod I) p :=
  fun p => ((1 : ℝ), X p.1 p.2)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in

theorem autonomizedFlow_snd_hasMFDerivAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (c : ℝ → ℝ × M) (t : ℝ)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t)))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (c s).2) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t).1 (c t).2)) := by
  have h := (hasMFDerivAt_snd (c t)).comp t hc
  convert h using 2

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in

theorem autonomizedFlow_fst_hasDerivAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (c : ℝ → ℝ × M) (t : ℝ)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t)))) :
    HasDerivAt (fun s => (c s).1) (1 : ℝ) t := by
  have h := (hasMFDerivAt_fst (c t)).comp t hc
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have h2 := h.hasDerivAt
  refine h2.congr_deriv ?_
  exact congrArg Prod.fst (one_smul ℝ (autonomizedFlowVF X (c t)))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in

theorem hasDerivAt_one_eq_self_on_Ioo (φ : ℝ → ℝ) {a b : ℝ}
    (h0mem : (0 : ℝ) ∈ Ioo a b)
    (hφ : ∀ s ∈ Ioo a b, HasDerivAt φ 1 s) (hval : φ 0 = 0) :
    ∀ s ∈ Ioo a b, φ s = s := by
  have hconst : ∀ s ∈ Ioo a b, HasDerivAt (fun u => φ u - u) (0 : ℝ) s := by
    intro u hu; simpa using (hφ u hu).sub (hasDerivAt_id u)
  intro s hs
  have hkey : (fun u => φ u - u) s = (fun u => φ u - u) 0 := by
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_Ioo a b)
      (f := fun u => φ u - u) (s := Ioo a b)
    · intro u hu
      exact (hconst u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      have huniq : UniqueDiffWithinAt ℝ (Ioo a b) u :=
        isOpen_Ioo.uniqueDiffWithinAt hu
      have hfd : HasFDerivWithinAt (fun u => φ u - u)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (0 : ℝ)) (Ioo a b) u :=
        ((hconst u hu).hasDerivWithinAt).hasFDerivWithinAt
      rw [hfd.fderivWithin huniq]; ext; simp
    · exact hs
    · exact h0mem
  simp only at hkey; rw [hval] at hkey; linarith

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem time_dependent_vf_local_integral_flow_bare [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ∀ p : ℝ × M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
        (fun p : ℝ × M =>
          (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))
        p)
    (x : M) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
  obtain ⟨c, hc0, hcurve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 (hX (0, x))
  rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at hcurve
  obtain ⟨S, hS, hSon⟩ := hcurve
  rw [Metric.mem_nhds_iff] at hS
  obtain ⟨ε, hε, hball⟩ := hS
  refine ⟨ε, hε, fun s => (c s).2, by change (c 0).2 = x; rw [hc0], ?_⟩
  intro t ht
  have htS : t ∈ S := by
    apply hball
    rw [Real.ball_eq_Ioo]
    constructor
    · simpa using ht.1
    · simpa using ht.2
  have hct : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (c t))) := hSon t htS
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> simp [hε]
  have htime : ∀ s ∈ Ioo (-ε) ε, (c s).1 = s := by
    apply hasDerivAt_one_eq_self_on_Ioo (fun s => (c s).1) h0mem
    · intro u hu
      have huS : u ∈ S := by
        apply hball
        rw [Real.ball_eq_Ioo]
        constructor
        · simpa using hu.1
        · simpa using hu.2
      exact autonomizedFlow_fst_hasDerivAt X c u (hSon u huS)
    · rw [hc0]
  have hsnd := autonomizedFlow_snd_hasMFDerivAt X c t hct
  rw [htime t ht] at hsnd
  exact hsnd.hasMFDerivWithinAt

variable [CompactSpace M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M] in
theorem time_dependent_vf_manifold_integral_flow_family
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (_hT : 0 < T) (Φ : ℝ → M → M)
    (_hΦ0 : ∀ x : M, Φ 0 x = x)
    (hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x)
    (hflow : ∀ t, 0 < t → t < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) ∧
      (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) := by
  classical
  refine ⟨fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    ?_, ?_, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x
  · intro s hs hsT x
    have hagree : ∀ t : ℝ, 0 < t → t < T → ∀ y : M,
        (if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose
          else Diffeomorph.refl I M ∞) y = Φ t y := by
      intro t ht htT y
      have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
      simp only [hguard, dif_pos, and_self]
      exact (hdiffeo t ht htT).choose_spec y
    have hbase : (if h : 0 < s ∧ s < T then (hdiffeo s h.1 h.2).choose
        else Diffeomorph.refl I M ∞) x = Φ s x := hagree s hs hsT x
    have hcurve_eq : (fun u : ℝ =>
          (if h : 0 < u ∧ u < T then (hdiffeo u h.1 h.2).choose
            else Diffeomorph.refl I M ∞) x) =ᶠ[𝓝[Ici 0] s]
        (fun u : ℝ => Φ u x) := by
      have hopen : Ioo (0 : ℝ) T ∈ 𝓝[Ici 0] s :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hs hsT)
      filter_upwards [hopen] with u hu
      exact hagree u hu.1 hu.2 x
    have hbase_flow := hflow s hs hsT x
    rw [← hbase] at hbase_flow
    exact hbase_flow.congr_of_eventuallyEq hcurve_eq hbase

end DifferentialGeometry.PDE.RicciFlow.ODE
