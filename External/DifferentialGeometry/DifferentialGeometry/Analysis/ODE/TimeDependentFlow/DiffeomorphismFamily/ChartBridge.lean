import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.Hartman
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldFlowFamily
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic


namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_diffeomorph_slice_of_smooth_bijective
    (Φ Ψ : M → M)
    (hΦ_smooth : ContMDiff I I ∞ Φ) (hΨ_smooth : ContMDiff I I ∞ Ψ)
    (hΨΦ : ∀ x : M, Ψ (Φ x) = x) (hΦΨ : ∀ x : M, Φ (Ψ x) = x) :
    ∃ d : M ≃ₘ⟮I, I⟯ M, (∀ x : M, d x = Φ x) ∧ (∀ x : M, d.symm x = Ψ x) := by
  let e : M ≃ M :=
    { toFun := Φ
      invFun := Ψ
      left_inv := fun x => hΨΦ x
      right_inv := fun x => hΦΨ x }
  exact ⟨⟨e, hΦ_smooth, hΨ_smooth⟩, fun _ => rfl, fun _ => rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_hdiffeo_of_smooth_bijective
    (Φ Ψ : ℝ → M → M) (T : ℝ)
    (hΦ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hΨ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t))
    (hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x)
    (hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) :
    ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x := by
  intro t ht htT
  have hmem : t ∈ Set.Ico (0 : ℝ) T := ⟨ht.le, htT⟩
  obtain ⟨d, hd_fwd, _hd_rev⟩ :=
    time_dependent_vf_diffeomorph_slice_of_smooth_bijective
      (Φ t) (Ψ t) (hΦ_smooth t ht htT) (hΨ_smooth t ht htT)
      (fun x => hΨΦ t hmem x) (fun x => hΦΨ t hmem x)
  exact ⟨d, hd_fwd⟩

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_hflow_transported_of_chartLocal
    (X : ℝ → ∀ x : M, TangentSpace I x) (α x : M)
    (hper : ChartLocalPicardData X α)
    (hxU : x ∈ hper.U)
    (Φ : ℝ → M → M)
    (hΦ_repr : ∀ s : ℝ, Φ s x = (chartAt H α).symm
      (I.symm (hper.flow (I ((chartAt H α) x)) s)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) hper.T)
    (hconf : (hper.flow (I ((chartAt H α) x))) ⁻¹' (Set.range I) ∈
      𝓝[Set.Icc (0 : ℝ) hper.T] t)
    (htgt_t :
      hper.flow (I ((chartAt H α) x)) t ∈ (extChartAt I α).target) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Icc 0 hper.T) t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
          (hper.flow (I ((chartAt H α) x)) t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) := by
  have hcurve : (fun s : ℝ => Φ s x) =
      fun s : ℝ => (chartAt H α).symm
        (I.symm (hper.flow (I ((chartAt H α) x)) s)) := by
    funext s; exact hΦ_repr s
  have hbase : Φ t x =
      (chartAt H α).symm (I.symm (hper.flow (I ((chartAt H α) x)) t)) :=
    hΦ_repr t
  rw [hcurve, hbase]
  exact manifoldFlow_hasMFDerivWithinAt_of_chartLocal X α x hper hxU t ht hconf
    htgt_t

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_diffeomorph_family_of_smooth_bijective
    (Φ Ψ : ℝ → M → M) (T : ℝ) (_hT : 0 < T)
    (_hΦ_init : ∀ x : M, Φ 0 x = x)
    (hΦ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hΨ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t))
    (hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x)
    (hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) := by
  classical
  have hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x :=
    time_dependent_vf_hdiffeo_of_smooth_bijective Φ Ψ T hΦ_smooth hΨ_smooth hΨΦ hΦΨ
  refine ⟨fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    ?_, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem time_dependent_vf_diffeomorph_family_of_hdiffeo
    (Φ : ℝ → M → M) (T : ℝ)
    (hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) := by
  classical
  refine ⟨fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    ?_, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x

end DifferentialGeometry.PDE.RicciFlow.ODE
