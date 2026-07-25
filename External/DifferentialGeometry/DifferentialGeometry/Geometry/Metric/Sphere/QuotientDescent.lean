import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import DifferentialGeometry.Geometry.Metric.SmoothMetricFromCoeff
import DifferentialGeometry.Geometry.Metric.BumpExtend
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityLocal
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature























set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]





structure SectionWitness (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) [Fact (finrank ℝ E = n + 1)] [NeZero n]
    (Q : Type*) [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    [IsManifold (𝓡 n) ∞ Q]
    (proj : sphere (0 : E) 1 → Q) (x : Q) where
  W : TopologicalSpace.Opens Q
  V : TopologicalSpace.Opens (sphere (0 : E) 1)
  [scW : SigmaCompactSpace W]
  [t2W : T2Space W]
  [bW : BoundarylessManifold (𝓡 n) W]
  [m1W : IsManifold (𝓡 n) 1 W]
  [mtW : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) W]
  [scV : SigmaCompactSpace V]
  [t2V : T2Space V]
  [bV : BoundarylessManifold (𝓡 n) V]
  [m1V : IsManifold (𝓡 n) 1 V]
  [mtV : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) V]
  s : W ≃ₘ⟮𝓡 n, 𝓡 n⟯ V
  mem : x ∈ W
  isSec : ∀ r : W, proj ((s r : V) : sphere (0 : E) 1) = (r : Q)





structure RoundQuotientData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) [Fact (finrank ℝ E = n + 1)] [NeZero n] where
  Q : Type*
  [topos : TopologicalSpace Q]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
  [mfld : IsManifold (𝓡 n) ∞ Q]
  [mfld1 : IsManifold (𝓡 n) 1 Q]
  [mfldTop : IsManifold (𝓡 n) ((∞ : WithTop ℕ∞) + 1) Q]
  [t2 : T2Space Q]
  [sigmaCompact : SigmaCompactSpace Q]
  [boundaryless : BoundarylessManifold (𝓡 n) Q]
  Γ : Type*
  [grp : Group Γ]
  [fin : Fintype Γ]
  ρ : Γ →* (E ≃ₗᵢ[ℝ] E)
  proj : sphere (0 : E) 1 → Q
  proj_smooth : ContMDiff (𝓡 n) (𝓡 n) ∞ proj
  proj_smul : ∀ (γ : Γ) (q : sphere (0 : E) 1),
    proj (sphereDiffeo (n := n) (ρ γ) q) = proj q
  proj_eq_imp : ∀ q₁ q₂ : sphere (0 : E) 1,
    proj q₁ = proj q₂ → ∃ γ : Γ, sphereDiffeo (n := n) (ρ γ) q₁ = q₂
  section_at : ∀ x : Q, SectionWitness E n Q proj x

attribute [instance] RoundQuotientData.topos RoundQuotientData.charted RoundQuotientData.mfld
  RoundQuotientData.mfld1 RoundQuotientData.mfldTop RoundQuotientData.t2
  RoundQuotientData.sigmaCompact RoundQuotientData.boundaryless RoundQuotientData.grp
  RoundQuotientData.fin
  SectionWitness.scW SectionWitness.t2W SectionWitness.bW SectionWitness.m1W
  SectionWitness.mtW SectionWitness.scV SectionWitness.t2V SectionWitness.bV
  SectionWitness.m1V SectionWitness.mtV






theorem SmoothRiemannianMetric.ext'
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {g g' : SmoothRiemannianMetric I' M'}
    (h : ∀ (x : M') (v w : TangentSpace I' x), g.inner x v w = g'.inner x v w) : g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

namespace SectionWitness

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
  [IsManifold (𝓡 n) ∞ Q] {proj : sphere (0 : E) 1 → Q} {x₀ : Q}
  (S : SectionWitness E n Q proj x₀)



def toSphere : S.W → sphere (0 : E) 1 := fun r => ((S.s r : S.V) : sphere (0 : E) 1)

theorem toSphere_proj (r : S.W) : proj (S.toSphere r) = (r : Q) := S.isSec r

theorem toSphere_contMDiff : ContMDiff (𝓡 n) (𝓡 n) ∞ S.toSphere := by
  have h : ContMDiff (𝓡 n) (𝓡 n) ∞
      ((Subtype.val : S.V → sphere (0 : E) 1) ∘ (S.s : S.W → S.V)) :=
    (contMDiff_subtype_val (I := 𝓡 n)).comp S.s.contMDiff
  exact h



theorem mfderiv_toSphere_apply (r : S.W) (v : TangentSpace (𝓡 n) r) :
    mfderiv (𝓡 n) (𝓡 n) S.toSphere r v = mfderiv (𝓡 n) (𝓡 n) S.s r v := by
  have hval : MDifferentiableAt (𝓡 n) (𝓡 n)
      (Subtype.val : S.V → sphere (0 : E) 1) (S.s r) :=
    (contMDiff_subtype_val (I := 𝓡 n)).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hs : MDifferentiableAt (𝓡 n) (𝓡 n) (S.s : S.W → S.V) r :=
    S.s.contMDiff.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp : S.toSphere = (Subtype.val : S.V → sphere (0 : E) 1) ∘ (S.s : S.W → S.V) := rfl
  rw [hcomp, mfderiv_comp_apply r hval hs v, mfderiv_subtype_val_apply]



theorem pullback_inner_eval {x : Q} (hx : x ∈ S.W) (v w : TangentSpace (𝓡 n) x) :
    (Diffeomorph.pullbackMetric
        ((roundMetric (E := E) (n := n)).restrictOpen S.V) S.s).inner ⟨x, hx⟩ v w
      = roundInner (n := n) (S.toSphere ⟨x, hx⟩)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, hx⟩ v)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, hx⟩ w) := by
  rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    mfderiv_toSphere_apply, mfderiv_toSphere_apply]
  rfl


theorem dproj_sec (hproj : ContMDiff (𝓡 n) (𝓡 n) ∞ proj) (r : S.W) :
    (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)).comp (mfderiv (𝓡 n) (𝓡 n) S.toSphere r)
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) r) := by
  have hp : MDifferentiableAt (𝓡 n) (𝓡 n) proj (S.toSphere r) :=
    hproj.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hts : MDifferentiableAt (𝓡 n) (𝓡 n) S.toSphere r :=
    S.toSphere_contMDiff.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hpts : proj ∘ S.toSphere = (Subtype.val : S.W → Q) := by
    funext r'; exact S.toSphere_proj r'
  have e1 : mfderiv (𝓡 n) (𝓡 n) (proj ∘ S.toSphere) r
      = (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)).comp
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere r) := mfderiv_comp r hp hts
  rw [hpts] at e1
  rw [← e1]
  exact mfderiv_subtype_val (I := 𝓡 n) S.W r


theorem dproj_inj (hproj : ContMDiff (𝓡 n) (𝓡 n) ∞ proj) (r : S.W) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)) := by
  have hcomp := S.dproj_sec hproj r
  have hrinv : Function.RightInverse
      (mfderiv (𝓡 n) (𝓡 n) S.toSphere r) (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)) := by
    intro u
    have := ContinuousLinearMap.ext_iff.mp hcomp u
    simpa [ContinuousLinearMap.comp_apply] using this
  have hsurj : Function.Surjective (mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)) :=
    hrinv.surjective
  have hlin : Function.Injective
      ((mfderiv (𝓡 n) (𝓡 n) proj (S.toSphere r)).toLinearMap :
        TangentSpace (𝓡 n) (S.toSphere r) →ₗ[ℝ] TangentSpace (𝓡 n) (r : Q)) :=
    LinearMap.injective_iff_surjective.mpr hsurj
  exact hlin

end SectionWitness

namespace RoundQuotientData

variable (D : RoundQuotientData E n)




def gm (x : D.Q) : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  (Diffeomorph.pullbackMetric
    ((roundMetric (E := E) (n := n)).restrictOpen (D.section_at x).V)
    (D.section_at x).s).inner ⟨x, (D.section_at x).mem⟩

theorem gm_symm (x : D.Q) (v w : TangentSpace (𝓡 n) x) : D.gm x v w = D.gm x w v :=
  (Diffeomorph.pullbackMetric
    ((roundMetric (E := E) (n := n)).restrictOpen (D.section_at x).V)
    (D.section_at x).s).symm _ _ _

theorem gm_pos (x : D.Q) (v : TangentSpace (𝓡 n) x) (hv : v ≠ 0) : 0 < D.gm x v v :=
  (Diffeomorph.pullbackMetric
    ((roundMetric (E := E) (n := n)).restrictOpen (D.section_at x).V)
    (D.section_at x).s).pos _ _ hv






theorem sections_agree {x₁ x : D.Q} (hx : x ∈ (D.section_at x₁).W) :
    ∃ γ : D.Γ,
      (D.section_at x₁).toSphere ⟨x, hx⟩
          = sphereDiffeo (n := n) (D.ρ γ)
              ((D.section_at x).toSphere ⟨x, (D.section_at x).mem⟩)
      ∧ ∀ v : TangentSpace (𝓡 n) x,
          mfderiv (𝓡 n) (𝓡 n) (D.section_at x₁).toSphere ⟨x, hx⟩ v
            = mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ))
                ((D.section_at x).toSphere ⟨x, (D.section_at x).mem⟩)
                (mfderiv (𝓡 n) (𝓡 n) (D.section_at x).toSphere
                  ⟨x, (D.section_at x).mem⟩ v) := by
  have h0 : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hpq : D.proj ((D.section_at x).toSphere ⟨x, (D.section_at x).mem⟩) = x :=
    (D.section_at x).toSphere_proj ⟨x, (D.section_at x).mem⟩
  have hpq₁ : D.proj ((D.section_at x₁).toSphere ⟨x, hx⟩) = x :=
    (D.section_at x₁).toSphere_proj ⟨x, hx⟩
  obtain ⟨γ, hγ⟩ := D.proj_eq_imp _ _ (hpq.trans hpq₁.symm)
  refine ⟨γ, hγ.symm, fun v => ?_⟩
  apply (D.section_at x₁).dproj_inj D.proj_smooth ⟨x, hx⟩
  have hA1 := ContinuousLinearMap.ext_iff.mp
    ((D.section_at x₁).dproj_sec D.proj_smooth ⟨x, hx⟩) v
  simp only [ContinuousLinearMap.comp_apply] at hA1
  have hφ : MDifferentiableAt (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ))
      ((D.section_at x).toSphere ⟨x, (D.section_at x).mem⟩) :=
    (sphereDiffeo (n := n) (D.ρ γ)).contMDiff.mdifferentiableAt h0
  have hp' : MDifferentiableAt (𝓡 n) (𝓡 n) D.proj
      (sphereDiffeo (n := n) (D.ρ γ)
        ((D.section_at x).toSphere ⟨x, (D.section_at x).mem⟩)) :=
    D.proj_smooth.mdifferentiableAt h0
  have hA2 : mfderiv (𝓡 n) (𝓡 n) D.proj ((D.section_at x₁).toSphere ⟨x, hx⟩)
      (mfderiv (𝓡 n) (𝓡 n) (sphereDiffeo (n := n) (D.ρ γ))
        ((D.section_at x).toSphere ⟨x, (D.section_at x).mem⟩)
        (mfderiv (𝓡 n) (𝓡 n) (D.section_at x).toSphere
          ⟨x, (D.section_at x).mem⟩ v)) = v := by
    rw [← hγ, ← mfderiv_comp_apply _ hp' hφ,
      show D.proj ∘ ⇑(sphereDiffeo (n := n) (D.ρ γ)) = D.proj from by
        funext y; exact D.proj_smul γ y]
    have hsx := ContinuousLinearMap.ext_iff.mp
      ((D.section_at x).dproj_sec D.proj_smooth ⟨x, (D.section_at x).mem⟩) v
    simp only [ContinuousLinearMap.comp_apply] at hsx
    exact hsx
  exact hA1.trans hA2.symm




theorem gm_locallyEq {x₁ x : D.Q} (hx : x ∈ (D.section_at x₁).W)
    (v w : TangentSpace (𝓡 n) x) :
    D.gm x v w = (Diffeomorph.pullbackMetric
        ((roundMetric (E := E) (n := n)).restrictOpen (D.section_at x₁).V)
        (D.section_at x₁).s).inner ⟨x, hx⟩ v w := by
  rw [show D.gm x v w = (Diffeomorph.pullbackMetric
        ((roundMetric (E := E) (n := n)).restrictOpen (D.section_at x).V)
        (D.section_at x).s).inner ⟨x, (D.section_at x).mem⟩ v w from rfl,
    (D.section_at x).pullback_inner_eval (D.section_at x).mem v w,
    (D.section_at x₁).pullback_inner_eval hx v w]
  obtain ⟨γ, hq₁, hd⟩ := D.sections_agree hx
  rw [hd v, hd w, hq₁, roundInner_sphereDiffeo]






theorem gm_coeff (x₀ : D.Q) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ) ∞
      (fun x => D.gm x (frameVec (I := 𝓡 n) x₀ i x) (frameVec (I := 𝓡 n) x₀ j x))
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀).baseSet := by
  intro x₁ hx₁
  apply ContMDiffAt.contMDiffWithinAt
  refine (contMDiffAt_subtype_iff (U := (D.section_at x₁).W)
    (x := ⟨x₁, (D.section_at x₁).mem⟩)).mp ?_
  have hfun : (fun r : (D.section_at x₁).W =>
        D.gm (↑r) (frameVec (I := 𝓡 n) x₀ i ↑r) (frameVec (I := 𝓡 n) x₀ j ↑r))
      = fun r : (D.section_at x₁).W =>
        (Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen (D.section_at x₁).V)
          (D.section_at x₁).s).inner r
          (frameVec (I := 𝓡 n) x₀ i ↑r) (frameVec (I := 𝓡 n) x₀ j ↑r) := by
    funext r
    exact D.gm_locallyEq r.2 _ _
  rw [hfun]
  exact CovariantDerivative.metric_inner_contMDiffAt
    (Diffeomorph.pullbackMetric
      ((roundMetric (E := E) (n := n)).restrictOpen (D.section_at x₁).V)
      (D.section_at x₁).s)
    (frameVec_sub_cmdiffAt (I := 𝓡 n) (D.section_at x₁).W x₀ i hx₁ (D.section_at x₁).mem)
    (frameVec_sub_cmdiffAt (I := 𝓡 n) (D.section_at x₁).W x₀ j hx₁ (D.section_at x₁).mem)
    (le_refl _)



def gQuot : SmoothRiemannianMetric (𝓡 n) D.Q :=
  (smoothMetric_of_localCoeff (I := 𝓡 n) D.gm D.gm_symm D.gm_pos D.gm_coeff).choose

theorem gQuot_inner (x : D.Q) (v w : TangentSpace (𝓡 n) x) :
    D.gQuot.inner x v w = D.gm x v w :=
  (smoothMetric_of_localCoeff (I := 𝓡 n) D.gm D.gm_symm D.gm_pos D.gm_coeff).choose_spec x v w





theorem gQuot_constPosSec :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : D.Q) (X Y : TangentSpace (𝓡 n) x),
      metricRm04StdAt (I := 𝓡 n) D.gQuot x X Y Y X =
        c * (D.gQuot.inner x X X * D.gQuot.inner x Y Y
          - D.gQuot.inner x X Y * D.gQuot.inner x X Y) := by
  refine ⟨1, one_pos, fun x X Y => ?_⟩
  haveI : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]; infer_instance
  set S := D.section_at x with hS

  have hB : metricRm04StdAt (I := 𝓡 n) D.gQuot x X Y Y X
      = metricRm04StdAt (I := 𝓡 n) (D.gQuot.restrictOpen S.W) ⟨x, S.mem⟩ X Y Y X :=
    (metricRm04StdAt_restrictOpen (I := 𝓡 n) D.gQuot S.W ⟨x, S.mem⟩ X Y Y X).symm

  have hmetric : D.gQuot.restrictOpen S.W
      = Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen S.V) S.s := by
    apply SmoothRiemannianMetric.ext'
    intro r v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, D.gQuot_inner]
    exact D.gm_locallyEq (x₁ := x) r.2 v w

  have hC : metricRm04StdAt (I := 𝓡 n)
        (Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen S.V) S.s) ⟨x, S.mem⟩ X Y Y X
      = metricRm04StdAt (I := 𝓡 n) (roundMetric (E := E) (n := n)) (S.toSphere ⟨x, S.mem⟩)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ X)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ Y)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ Y)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ X) := by
    rw [metricRm04StdAt_pullback_localDiffeo (I := 𝓡 n) (roundMetric (E := E) (n := n))
        S.V S.W S.s ⟨x, S.mem⟩ X Y Y X,
      S.mfderiv_toSphere_apply ⟨x, S.mem⟩ X, S.mfderiv_toSphere_apply ⟨x, S.mem⟩ Y]
    rfl

  have hbridge : ∀ v w : TangentSpace (𝓡 n) x,
      (roundMetric (E := E) (n := n)).inner (S.toSphere ⟨x, S.mem⟩)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ v)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ w)
        = D.gQuot.inner x v w := by
    intro v w
    rw [D.gQuot_inner,
      show D.gm x v w = (Diffeomorph.pullbackMetric
          ((roundMetric (E := E) (n := n)).restrictOpen S.V) S.s).inner ⟨x, S.mem⟩ v w from rfl,
      S.pullback_inner_eval S.mem v w]
    rfl
  rw [hB, hmetric, hC,
    roundMetric_sec_value (S.toSphere ⟨x, S.mem⟩)
      (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ X)
      (mfderiv (𝓡 n) (𝓡 n) S.toSphere ⟨x, S.mem⟩ Y),
    hbridge X X, hbridge Y Y, hbridge X Y, one_mul]

end RoundQuotientData

end Geometry
end DifferentialGeometry
