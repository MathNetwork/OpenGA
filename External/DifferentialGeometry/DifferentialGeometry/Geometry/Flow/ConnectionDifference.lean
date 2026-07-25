import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def connDiff (g g' : SmoothRiemannianMetric I M) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  CovariantDerivative.difference (LeviCivita (I := I) g) (LeviCivita (I := I) g')

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem connDiff_apply (g g' : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    connDiff (I := I) g g' x (σ x) v =
      (LeviCivita (I := I) g).toFun σ x v - (LeviCivita (I := I) g').toFun σ x v := by
  have h := IsCovariantDerivativeOn.difference_apply
    (LeviCivita (I := I) g).isCovariantDerivativeOnUniv
    (LeviCivita (I := I) g').isCovariantDerivativeOnUniv
    (x := x) (mem_univ x) (σ := σ) hσ
  simp only [connDiff, CovariantDerivative.difference]
  rw [h]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
@[simp]
theorem connDiff_self (g : SmoothRiemannianMetric I M) :
    connDiff (I := I) g g = 0 := by
  classical
  funext x
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have hval : connDiff (I := I) g g x (σ x) v =
      (LeviCivita (I := I) g).toFun (fun y => σ y) x v -
        (LeviCivita (I := I) g).toFun (fun y => σ y) x v :=
    connDiff_apply (I := I) g g hσ v
  rw [sub_self] at hval
  simpa [hσx] using hval

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem leviCivita_section_contMDiff (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  have h := LeviCivita_section_contMDiffOn_univ (I := I) g hσ'
  rw [← contMDiffOn_univ]
  exact h

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiff_contMDiff (g g' : SmoothRiemannianMetric I M)
    {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% τ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) := by
  have hcovg := leviCivita_section_contMDiff (I := I) g hσ
  have hcovg' := leviCivita_section_contMDiff (I := I) g' hσ
  have hg : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g).toFun σ x (τ x)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcovg hτ
  have hg' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g').toFun σ x (τ x)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcovg' hτ
  have hdiff := hg.sub_section hg'
  refine hdiff.congr (fun x => ?_)
  have hσ_at : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp)
  have hval := connDiff_apply (I := I) g g' hσ_at (τ x)
  change (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ : TotalSpace E (TangentSpace I)) =
      ⟨x, ((fun y => (LeviCivita (I := I) g).toFun σ y (τ y)) -
        (fun y => (LeviCivita (I := I) g').toFun σ y (τ y))) x⟩
  rw [Pi.sub_apply, hval]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connDiff_contMDiffOn (g g' : SmoothRiemannianMetric I M)
    {U : Set M} {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ))
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% τ) U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) U := by
  have hcovg := (leviCivita_section_contMDiff (I := I) g hσ).contMDiffOn (s := U)
  have hcovg' := (leviCivita_section_contMDiff (I := I) g' hσ).contMDiffOn (s := U)
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g).toFun σ x (τ x)))) U :=
    ContMDiffOn.clm_bundle_apply (b := id) hcovg hτ
  have hg' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g').toFun σ x (τ x)))) U :=
    ContMDiffOn.clm_bundle_apply (b := id) hcovg' hτ
  have hdiff := hg.sub_section hg'
  refine hdiff.congr (fun x _hx => ?_)
  have hσ_at : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp)
  have hval := connDiff_apply (I := I) g g' hσ_at (τ x)
  change (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ : TotalSpace E (TangentSpace I)) =
      ⟨x, ((fun y => (LeviCivita (I := I) g).toFun σ y (τ y)) -
        (fun y => (LeviCivita (I := I) g').toFun σ y (τ y))) x⟩
  rw [Pi.sub_apply, hval]

end DeTurck
end PDE
end DifferentialGeometry
