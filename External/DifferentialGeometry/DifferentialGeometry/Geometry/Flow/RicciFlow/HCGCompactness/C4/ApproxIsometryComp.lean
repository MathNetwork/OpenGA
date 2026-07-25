


import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Bundle.ClmSectionSmooth
import DifferentialGeometry.Geometry.Metric.MetricExistence
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option linter.style.longLine false
















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]


omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricInner_nonneg
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le


omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricEquiv_mono
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C C' : Real}
    (hCC' : C ≤ C')
    (hgh : MetricUniformEquivalentOn (I := I) K g h C) :
    MetricUniformEquivalentOn (I := I) K g h C' := by
  obtain ⟨hC1, hbound⟩ := hgh
  refine ⟨hC1.trans hCC', fun x hx v => ?_⟩
  obtain ⟨hlow, hup⟩ := hbound x hx v
  have hg0 : 0 ≤ g.inner x v v := metricInner_nonneg (I := I) g x v
  have hC0 : (0 : Real) < C := lt_of_lt_of_le one_pos hC1
  have hC'0 : (0 : Real) < C' := lt_of_lt_of_le one_pos (hC1.trans hCC')
  constructor
  · have hinv : C'⁻¹ ≤ C⁻¹ := inv_anti₀ hC0 hCC'
    calc C'⁻¹ * g.inner x v v ≤ C⁻¹ * g.inner x v v :=
          mul_le_mul_of_nonneg_right hinv hg0
      _ ≤ h.inner x v v := hlow
  · calc h.inner x v v ≤ C * g.inner x v v := hup
      _ ≤ C' * g.inner x v v := mul_le_mul_of_nonneg_right hCC' hg0



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricEquiv_trans
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h k : SmoothRiemannianMetric I M} {C₁ C₂ : Real}
    (hgh : MetricUniformEquivalentOn (I := I) K g h C₁)
    (hhk : MetricUniformEquivalentOn (I := I) K h k C₂) :
    MetricUniformEquivalentOn (I := I) K g k (C₁ * C₂) := by
  obtain ⟨hC₁, hbound₁⟩ := hgh
  obtain ⟨hC₂, hbound₂⟩ := hhk
  have hC₁0 : (0 : Real) ≤ C₁ := le_trans zero_le_one hC₁
  have hC₂0 : (0 : Real) ≤ C₂ := le_trans zero_le_one hC₂
  refine ⟨by nlinarith, fun x hx v => ?_⟩
  obtain ⟨hlow₁, hup₁⟩ := hbound₁ x hx v
  obtain ⟨hlow₂, hup₂⟩ := hbound₂ x hx v
  constructor
  · have h1 : (C₁ * C₂)⁻¹ * g.inner x v v =
        C₂⁻¹ * (C₁⁻¹ * g.inner x v v) := by
      rw [mul_inv]
      ring
    rw [h1]
    calc C₂⁻¹ * (C₁⁻¹ * g.inner x v v) ≤ C₂⁻¹ * h.inner x v v :=
          mul_le_mul_of_nonneg_left hlow₁ (inv_nonneg.mpr hC₂0)
      _ ≤ k.inner x v v := hlow₂
  · calc k.inner x v v ≤ C₂ * h.inner x v v := hup₂
      _ ≤ C₂ * (C₁ * g.inner x v v) :=
          mul_le_mul_of_nonneg_left hup₁ hC₂0
      _ = C₁ * C₂ * g.inner x v v := by ring



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricEquiv_comp_eps
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {K : Set M} {g h k : SmoothRiemannianMetric I M} {eps₀ eps₁ : Real}
    (heps₀ : 0 ≤ eps₀) (heps₀1 : eps₀ ≤ 1)
    (heps₁ : 0 ≤ eps₁)
    (hgh : MetricUniformEquivalentOn (I := I) K g h (1 + eps₀))
    (hhk : MetricUniformEquivalentOn (I := I) K h k (1 + eps₁)) :
    MetricUniformEquivalentOn (I := I) K g k (1 + 3 * (eps₀ + eps₁)) := by
  have hC : (1 + eps₀) * (1 + eps₁) ≤ 1 + 3 * (eps₀ + eps₁) := by
    nlinarith [mul_le_of_le_one_left heps₁ heps₀1]
  exact metricEquiv_mono hC (metricEquiv_trans hgh hhk)




theorem compEpsAccum {C : Real} {e δ : Nat → Real}
    (h0 : e 0 ≤ C * δ 0)
    (hstep : ∀ k : Nat, e (k + 1) ≤ e k + C * δ (k + 1)) :
    ∀ n : Nat, e n ≤ C * Finset.sum (Finset.range (n + 1)) (fun i => δ i) := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      have h3 : C * Finset.sum (Finset.range (n + 1)) (fun i => δ i) + C * δ (n + 1) =
          C * Finset.sum (Finset.range (n + 1 + 1)) (fun i => δ i) := by
        conv_rhs => rw [Finset.sum_range_succ, mul_add]
      linarith [hstep n, ih]





omit [CompleteSpace E] in
theorem exists_bump_one_on {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) χ ∧ Set.EqOn χ 1 K ∧
      tsupport χ ⊆ U ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  haveI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  haveI : NormalSpace M := inferInstance
  obtain ⟨V, hVopen, hKV, hVU⟩ :=
    hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨f, hf1, hf0, hf01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (n := (⊤ : ℕ∞))
      hK.isClosed
      (hKV.trans (interior_maximal subset_closure hVopen))
  refine ⟨⇑f, f.contMDiff, ?_, ?_, hf01⟩
  · intro x hx
    exact hf1.self_of_nhdsSet x hx
  · refine (closure_minimal ?_ isClosed_closure).trans hVU
    intro x hx
    by_contra hxV
    exact hx (hf0 x hxV)

section PullbackField

open Bundle

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]







omit [CompleteSpace E] in
theorem exists_pullbackInner (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ Φ.source) (h : SmoothRiemannianMetric I N) :
    ∃ (χ : M → ℝ) (P : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ),
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (∞ : WithTop ℕ∞)
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (P x)) ∧
      ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) χ ∧
      Set.EqOn χ 1 K ∧ tsupport χ ⊆ Φ.source ∧ (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ x : M, P x = χ x •
        (ContinuousLinearMap.precomp ℝ (mfderiv I I Φ x)).comp
          ((h.inner (Φ x)).comp (mfderiv I I Φ x)) := by
  classical
  obtain ⟨χ, hχ, hχK, hχsupp, hχ01⟩ :=
    exists_bump_one_on (I := I) hK Φ.open_source hKs

  set Q : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
    (ContinuousLinearMap.precomp ℝ (mfderiv I I Φ x)).comp
      ((h.inner (Φ x)).comp (mfderiv I I Φ x)) with hQ
  refine ⟨χ, fun x => χ x • Q x, ?_, hχ, hχK, hχsupp, hχ01, fun x => rfl⟩
  ·
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x => χ x • Q x)
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : M => ℝ)
      (φ := fun x => (χ x • Q x) (Y x))
    intro W x₀
    rw [Bundle.contMDiffAt_section]
    have hval : ∀ x : M, (χ x • Q x) (Y x) (W x)
        = χ x * (h.inner (Φ x) (mfderiv I I Φ x (Y x)) (mfderiv I I Φ x (W x))) := by
      intro x
      simp only [hQ, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.precomp_apply, smul_eq_mul]
    have hstage : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        (fun x => (χ x • Q x) (Y x) (W x)) x₀ := by
      by_cases hx₀ : x₀ ∈ Φ.source
      ·
        have hφ : ContMDiffAt I I (∞ : WithTop ℕ∞) (Φ : M → N) x₀ :=
          Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx₀)
        have hg' : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (∞ : WithTop ℕ∞)
            (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun b : N => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
              ((Φ : M → N) x) (h.inner ((Φ : M → N) x))) x₀ := by
          have hcomp := ContMDiffAt.comp (I' := I) x₀ (h.contMDiff ((Φ : M → N) x₀)) hφ
          exact hcomp
        have hφOn : ContMDiffOn I I (∞ : WithTop ℕ∞) (Φ : M → N) Φ.source :=
          Φ.contMDiffOn_toFun
        have htm : ContMDiffOn I.tangent I.tangent (∞ : WithTop ℕ∞)
            (tangentMapWithin I I (Φ : M → N) Φ.source)
            (Bundle.TotalSpace.proj ⁻¹' Φ.source) :=
          hφOn.contMDiffOn_tangentMapWithin le_rfl Φ.open_source.uniqueMDiffOn
        have hpre_open : IsOpen
            (Bundle.TotalSpace.proj ⁻¹' Φ.source : Set (TangentBundle I M)) :=
          Φ.open_source.preimage (FiberBundle.continuous_proj E (TangentSpace I))
        have hsec : ∀ Y' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
            ContMDiffAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
              (fun x => TotalSpace.mk' E (E := fun b : N => TangentSpace I b)
                ((Φ : M → N) x) (mfderiv I I (Φ : M → N) x (Y' x))) x₀ := by
          intro Y'
          have hYs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
              (fun x => TotalSpace.mk' E (E := fun b : M => TangentSpace I b)
                x (Y' x)) x₀ := Y'.contMDiff x₀
          have hmem : (TotalSpace.mk' E (E := fun b : M => TangentSpace I b)
                x₀ (Y' x₀) : TangentBundle I M)
              ∈ Bundle.TotalSpace.proj ⁻¹' Φ.source := hx₀
          have hcomp := (htm.contMDiffAt (hpre_open.mem_nhds hmem)).comp x₀ hYs
          refine hcomp.congr_of_eventuallyEq ?_
          filter_upwards [Φ.open_source.mem_nhds hx₀] with x hx
          show TotalSpace.mk' E (E := fun b : N => TangentSpace I b)
              ((Φ : M → N) x) (mfderiv I I (Φ : M → N) x (Y' x))
            = TotalSpace.mk' E (E := fun b : N => TangentSpace I b)
              ((Φ : M → N) x)
              (mfderivWithin I I (Φ : M → N) Φ.source x (Y' x))
          rw [mfderivWithin_of_isOpen Φ.open_source hx]
        have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) (∞ : WithTop ℕ∞)
            (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ)
              ((Φ : M → N) x)
              (h.inner ((Φ : M → N) x)
                (mfderiv I I (Φ : M → N) x (Y x))
                (mfderiv I I (Φ : M → N) x (W x)))) x₀ :=
          ContMDiffAt.clm_bundle_apply₂
            (E₁ := fun b : N => TangentSpace I b)
            (E₂ := fun b : N => TangentSpace I b)
            (E₃ := fun _ : N => ℝ)
            hg' (hsec Y) (hsec W)
        have h_scalar : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
            (fun x => h.inner ((Φ : M → N) x)
              (mfderiv I I (Φ : M → N) x (Y x))
              (mfderiv I I (Φ : M → N) x (W x))) x₀ := by
          rw [contMDiffAt_totalSpace] at h_total
          convert h_total.2 using 1
        have hmul := (hχ.contMDiffAt (x := x₀)).mul h_scalar
        refine hmul.congr_of_eventuallyEq ?_
        filter_upwards with x
        exact hval x
      ·
        have hx₀' : x₀ ∉ tsupport χ := fun hmem => hx₀ (hχsupp hmem)
        have hev : (fun x => (χ x • Q x) (Y x) (W x)) =ᶠ[nhds x₀] (fun _ => (0 : ℝ)) := by
          filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx₀'] with x hx
          rw [hval x, image_eq_zero_of_notMem_tsupport hx, zero_mul]
        exact contMDiffAt_const.congr_of_eventuallyEq hev
    refine hstage.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl





omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem pullInner_pos (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {x : M} (hx : x ∈ Φ.source) (h : SmoothRiemannianMetric I N)
    (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < h.inner ((Φ : M → N) x) (mfderiv I I (Φ : M → N) x v)
        (mfderiv I I (Φ : M → N) x v) := by
  refine h.pos _ _ (fun h0 => hv ?_)

  have hfg : (Φ.symm : N → M) ∘ (Φ : M → N) =ᶠ[nhds x] id := by
    filter_upwards [Φ.open_source.mem_nhds hx] with y hy
    exact Φ.left_inv' hy
  have hΦd : MDifferentiableAt I I (Φ : M → N) x :=
    ((Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ : M → N) x) :=
    ((Φ.symm.contMDiffOn_toFun.contMDiffAt
      (Φ.symm.open_source.mem_nhds (Φ.map_source' hx)))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp : (mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)).comp
      (mfderiv I I (Φ : M → N) x) = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    rw [← mfderiv_comp x hΦsd hΦd, hfg.mfderiv_eq]
    exact mfderiv_id
  have happ : mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)
      (mfderiv I I (Φ : M → N) x v) = v := by
    simpa using DFunLike.congr_fun hcomp v
  rw [← happ, h0]
  exact (mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)).map_zero

end PullbackField

end HCGCompactness
end DifferentialGeometry
