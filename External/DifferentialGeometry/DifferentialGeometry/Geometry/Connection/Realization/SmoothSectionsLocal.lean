import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Geometry.Manifold.BumpFunction























noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle

section SmoothSectionsLocal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem contMDiffOn_dual_apply
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    {V : (y : M) → TangentSpace I y} {u : Set M}
    (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V y)) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => α y (V y)) u := by
  have hα : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        y (α y)) u := α.contMDiff.contMDiffOn
  have hap : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (α y (V y))) u :=
    ContMDiffOn.clm_bundle_apply (b := id) hα hV
  intro y hy
  exact (contMDiffWithinAt_section (F := ℝ) (E := Bundle.Trivial M ℝ)).mp (hap y hy)



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem extDerivFun_congr_nhds
    {f g : M → ℝ} {x : M} (V : TangentSpace I x) (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x V = extDerivFun (I := I) g x V := by
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv I f x V,
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I g x V,
    Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) h]
  rfl







omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem contMDiffAt_extDerivFun_apply
    {u : Set M} (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f u)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V y)) u) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => extDerivFun (I := I) f y (V y)) x := by
  classical

  obtain ⟨b, -, hb_supp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hu.mem_nhds hx)

  set ftil : M → ℝ := fun y => b y * f y with hftil_def
  have hftil : ContMDiff I 𝓘(ℝ, ℝ) ∞ ftil := by
    apply contMDiff_of_locally_contMDiffOn
    intro z
    by_cases hz : z ∈ u
    · exact ⟨u, hu, hz, (b.contMDiff.contMDiffOn).mul hf⟩
    · refine ⟨(tsupport (b : M → ℝ))ᶜ, (isClosed_tsupport _).isOpen_compl,
        fun hmem => hz (hb_supp hmem), ?_⟩
      refine (contMDiffOn_const (c := (0 : ℝ))).congr ?_
      intro y hy
      have hb0 : b y = 0 := by
        by_contra hne
        exact hy (subset_tsupport _ hne)
      simp [hftil_def, hb0]

  let dα : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
    ⟨fun y => extDerivFun (I := I) ftil y,
      contMDiff_extDerivFun_section (I := I) (M := M) ⟨ftil, hftil⟩⟩
  have hpair : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => extDerivFun (I := I) ftil y (V y)) u :=
    contMDiffOn_dual_apply (I := I) dα hV
  have hAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => extDerivFun (I := I) ftil y (V y)) x :=
    hpair.contMDiffAt (hu.mem_nhds hx)

  refine hAt.congr_of_eventuallyEq ?_
  obtain ⟨w, hw_one, hw_open, hxw⟩ := eventually_nhds_iff.mp b.eventuallyEq_one
  refine eventually_nhds_iff.mpr ⟨w, ?_, hw_open, hxw⟩
  intro y hyw
  refine extDerivFun_congr_nhds (I := I) (V y) ?_
  refine eventually_nhds_iff.mpr ⟨w, ?_, hw_open, hyw⟩
  intro z hzw
  simp [hftil_def, hw_one z hzw]

end SmoothSectionsLocal
