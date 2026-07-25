import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Diffeomorph


namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Manifold Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

def AutonomizedFieldJointC1 (X : ℝ → ∀ x : M, TangentSpace I x) : Prop :=
  ∀ p : ℝ × M,
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))
      p

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem time_dependent_vf_bare_local_flow_of_jointC1 [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : AutonomizedFieldJointC1 (I := I) X) (x : M) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) :=
  time_dependent_vf_local_integral_flow_bare X hX x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in

theorem autonomizedLift_hasMFDerivWithinAt (X : ℝ → ∀ x : M, TangentSpace I x)
    (γ : ℝ → M) (s : Set ℝ) (t : ℝ)
    (hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun u : ℝ => (u, γ u)) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (t, γ t))) := by
  have hfst : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u : ℝ => u) s t
      (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)) :=
    hasMFDerivWithinAt_id s t
  have hprod := hfst.prodMk hγ
  have hCLM :
      ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF X (t, γ t)))
        = (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)).prod
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))) := by
    apply ContinuousLinearMap.ext
    intro r
    apply Prod.ext
    · change r • (1 : ℝ) = r
      rw [smul_eq_mul, mul_one]
    · change r • X t (γ t) = r • X t (γ t)
      rfl
  rw [hCLM]
  exact hprod

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] in

theorem autonomizedLift_isMIntegralCurveOn_of_bareFlow
    (X : ℝ → ∀ x : M, TangentSpace I x) (Φ : ℝ → M → M) (x : M) (s : Set ℝ)
    (hflow : ∀ t ∈ s,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) s t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    IsMIntegralCurveOn (fun u : ℝ => (u, Φ u x)) (autonomizedFlowVF X) s := by
  intro t ht
  exact autonomizedLift_hasMFDerivWithinAt X (fun u : ℝ => Φ u x) s t (hflow t ht)

omit [FiniteDimensional ℝ E] in
theorem bare_integral_flow_eqOn_of_jointC1 [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : AutonomizedFieldJointC1 (I := I) X)
    (Φ Φ' : ℝ → M → M) (x x' : M) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hflow : ∀ t ∈ Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hflow' : ∀ t ∈ Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ' u x') (Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x'))))
    (hstart : Φ t₀ x = Φ' t₀ x') :
    ∀ t ∈ Ioo a b, Φ t x = Φ' t x' := by
  have hc : IsMIntegralCurveOn (fun u : ℝ => (u, Φ u x)) (autonomizedFlowVF X)
      (Ioo a b) :=
    autonomizedLift_isMIntegralCurveOn_of_bareFlow X Φ x (Ioo a b) hflow
  have hc' : IsMIntegralCurveOn (fun u : ℝ => (u, Φ' u x')) (autonomizedFlowVF X)
      (Ioo a b) :=
    autonomizedLift_isMIntegralCurveOn_of_bareFlow X Φ' x' (Ioo a b) hflow'
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    fun p => hX p
  have hstartlift : (fun u : ℝ => (u, Φ u x)) t₀ = (fun u : ℝ => (u, Φ' u x')) t₀ := by
    simp only
    rw [hstart]
  have heq : EqOn (fun u : ℝ => (u, Φ u x)) (fun u : ℝ => (u, Φ' u x')) (Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hv hc hc' hstartlift
  intro t ht
  have := heq ht
  simpa using congrArg Prod.snd this

omit [FiniteDimensional ℝ E] in
theorem time_dependent_vf_bare_local_flow_exists_unique_of_jointC1 [CompleteSpace E]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : AutonomizedFieldJointC1 (I := I) X) (x : M) :
    ∃ (ε : ℝ) (_ : 0 < ε) (γ : ℝ → M), γ 0 = x ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) ∧
      (∀ (γ' : ℝ → M), γ' 0 = x →
        (∀ t ∈ Ioo (-ε) ε,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => γ' u) (Ioo (-ε) ε) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ' t)))) →
        (∀ t ∈ Ioo (-ε) ε,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => γ u) (Ioo (-ε) ε) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) →
        ∀ t ∈ Ioo (-ε) ε, γ t = γ' t) := by
  obtain ⟨ε, hε, γ, hγ0, hγflow⟩ :=
    time_dependent_vf_local_integral_flow_bare X hX x
  refine ⟨ε, hε, γ, hγ0, hγflow, ?_⟩
  intro γ' hγ'0 hγ'two hγtwo t ht
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> simp [hε]
  have hstart : γ 0 = γ' 0 := by rw [hγ0, hγ'0]
  exact bare_integral_flow_eqOn_of_jointC1 (a := -ε) (b := ε) (t₀ := 0)
    X hX (fun u : ℝ => fun _ : M => γ u) (fun u : ℝ => fun _ : M => γ' u) x x
    h0mem hγtwo hγ'two hstart t ht

variable [CompactSpace M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M] in
theorem time_dependent_vf_bare_flow_family
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (hT : 0 < T) (Φ : ℝ → M → M)
    (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x)
    (hflow : ∀ t, 0 < t → t < T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Ici 0) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) ∧
      (∀ s : ℝ, 0 < s → s < T → ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ_fam u x) (Ici 0) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ_fam s x)))) :=
  time_dependent_vf_manifold_integral_flow_family X T hT Φ hΦ0 hdiffeo hflow

end DifferentialGeometry.PDE.RicciFlow.ODE
