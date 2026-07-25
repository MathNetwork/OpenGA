import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.InteriorCompactSupport
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.IntegrationByParts
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.Algebra.Support


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

omit [InnerProductSpace ℝ E] in
private lemma gradFun_eq_zero_on_compl_tsupport
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    {x : M} (hx : x ∈ (tsupport f)ᶜ) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hx] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  exact gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hev

omit [InnerProductSpace ℝ E] in
private lemma gradFun_total_eq_zeroSection_on_compl_tsupport
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    {y : M} (hy : y ∈ (tsupport f)ᶜ) :
    TotalSpace.mk' E y (gradFun (I := I) g f y) =
      (Bundle.zeroSection E (TangentSpace I : M → Type _) y) := by
  have hzero : gradFun (I := I) g f y = (0 : TangentSpace I y) :=
    gradFun_eq_zero_on_compl_tsupport (I := I) g hy
  rw [hzero]
  rfl

omit [InnerProductSpace ℝ E] in
private lemma gradFun_total_contMDiffOn_compl_tsupport
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
      (tsupport f)ᶜ := by
  have hzero : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (Bundle.zeroSection E (TangentSpace I : M → Type _)) :=
    contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)
  refine (hzero.contMDiffOn).congr ?_
  intro y hy
  exact gradFun_total_eq_zeroSection_on_compl_tsupport (I := I) g hy

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma interior_union_compl_tsupport_eq_univ
    {f : M → ℝ} (hf_int : tsupport f ⊆ I.interior M) :
    I.interior M ∪ (tsupport f)ᶜ = (Set.univ : Set M) := by
  refine Set.eq_univ_of_forall ?_
  intro x
  by_cases hx : x ∈ I.interior M
  · exact Or.inl hx
  · refine Or.inr ?_
    intro hx_supp
    exact hx (hf_int hx_supp)

def grad_g_with_boundary_section [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := I) g f x, by
    have hs_open : IsOpen (I.interior M) := isOpen_interior_M
    have ht_open : IsOpen ((tsupport f)ᶜ) := (isClosed_tsupport _).isOpen_compl
    have hs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
        (I.interior M) :=
      gradFun_contMDiffOn_interior (I := I) g hf
    have ht : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x))
        ((tsupport f)ᶜ) :=
      gradFun_total_contMDiffOn_compl_tsupport (I := I) g f
    have hcover : I.interior M ∪ (tsupport f)ᶜ = (Set.univ : Set M) :=
      interior_union_compl_tsupport_eq_univ (I := I) (M := M) hf_int
    exact contMDiff_of_contMDiffOn_union_of_isOpen hs ht hcover hs_open ht_open⟩

omit [InnerProductSpace ℝ E] in
@[simp] lemma grad_g_with_boundary_section_apply [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    (grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradFun (I := I) g f x := rfl

omit [InnerProductSpace ℝ E] in
@[simp] lemma grad_g_with_boundary_section_coe [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    (grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      grad_g_with_boundary (I := I) g f x := rfl

omit [InnerProductSpace ℝ E] in
lemma support_grad_g_with_boundary_section_subset [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Function.support
        ((grad_g_with_boundary_section (I := I) g hf hf_int :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
          ∀ x, TangentSpace I x) ⊆ tsupport f :=
  support_grad_g_with_boundary_subset (I := I) g f

omit [InnerProductSpace ℝ E] in
lemma tsupport_grad_g_with_boundary_section_subset [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      ∀ x, TangentSpace I x) ⊆ tsupport f :=
  closure_minimal
    (support_grad_g_with_boundary_section_subset (I := I) g hf hf_int)
    (isClosed_tsupport _)

omit [InnerProductSpace ℝ E] in
lemma tsupport_grad_g_with_boundary_section_subset_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      ∀ x, TangentSpace I x) ⊆ I.interior M :=
  (tsupport_grad_g_with_boundary_section_subset (I := I) g hf hf_int).trans hf_int

omit [InnerProductSpace ℝ E] in
lemma hasCompactSupport_grad_g_with_boundary_section [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (hf_cs : HasCompactSupport f) :
    HasCompactSupport
      ((grad_g_with_boundary_section (I := I) g hf hf_int :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  exact support_grad_g_with_boundary_section_subset (I := I) g hf hf_int hx

def Δ_g_with_boundary [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) : M → ℝ :=
  divergence_g_with_boundary (I := I) g
    (grad_g_with_boundary_section (I := I) g hf hf_int)

omit [InnerProductSpace ℝ E] in
@[simp] lemma Δ_g_with_boundary_def [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) (x : M) :
    Δ_g_with_boundary (I := I) g hf hf_int x =
      divergence_g_with_boundary (I := I) g
        (grad_g_with_boundary_section (I := I) g hf hf_int) x := rfl

omit [InnerProductSpace ℝ E] in
theorem Δ_g_with_boundary_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (Δ_g_with_boundary (I := I) g hf hf_int)
      (I.interior M) :=
  divergence_g_with_boundary_contMDiffOn_interior (I := I) g
    (grad_g_with_boundary_section (I := I) g hf hf_int)

omit [InnerProductSpace ℝ E] in
lemma tsupport_Δ_g_with_boundary_subset [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    tsupport (Δ_g_with_boundary (I := I) g hf hf_int) ⊆ tsupport f := by
  have hsec_supp : tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x, TangentSpace I x) ⊆
        I.interior M :=
    tsupport_grad_g_with_boundary_section_subset_interior (I := I) g hf hf_int
  have h1 : tsupport (Δ_g_with_boundary (I := I) g hf hf_int) ⊆
      tsupport ((grad_g_with_boundary_section (I := I) g hf hf_int :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x, TangentSpace I x) :=
    tsupport_divergence_g_with_boundary_subset_of_interior_support
      (I := I) g (grad_g_with_boundary_section (I := I) g hf hf_int) hsec_supp
  exact h1.trans (tsupport_grad_g_with_boundary_section_subset (I := I) g hf hf_int)

omit [InnerProductSpace ℝ E] in
theorem Δ_g_with_boundary_continuous [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M) :
    Continuous (Δ_g_with_boundary (I := I) g hf hf_int) := by
  classical
  have hΔ_supp_int : tsupport (Δ_g_with_boundary (I := I) g hf hf_int) ⊆
      I.interior M :=
    (tsupport_Δ_g_with_boundary_subset (I := I) g hf hf_int).trans hf_int
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_supp : x ∈ tsupport (Δ_g_with_boundary (I := I) g hf hf_int)
  · have hx_int : x ∈ I.interior M := hΔ_supp_int hx_supp
    have hcont_int : ContinuousOn (Δ_g_with_boundary (I := I) g hf hf_int)
        (I.interior M) :=
      (Δ_g_with_boundary_contMDiffOn_interior (I := I) g hf hf_int).continuousOn
    exact (hcont_int x hx_int).continuousAt (isOpen_interior_M.mem_nhds hx_int)
  · have h_open : IsOpen (tsupport (Δ_g_with_boundary (I := I) g hf hf_int))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev_zero : (Δ_g_with_boundary (I := I) g hf hf_int) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_supp] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    exact (continuous_const.continuousAt.congr hev_zero.symm)

omit [InnerProductSpace ℝ E] in
lemma hasCompactSupport_Δ_g_with_boundary [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_int : tsupport f ⊆ I.interior M)
    (hf_cs : HasCompactSupport f) :
    HasCompactSupport (Δ_g_with_boundary (I := I) g hf hf_int) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  have h1 : x ∈ tsupport (Δ_g_with_boundary (I := I) g hf hf_int) :=
    subset_tsupport _ hx
  exact tsupport_Δ_g_with_boundary_subset (I := I) g hf hf_int h1

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
