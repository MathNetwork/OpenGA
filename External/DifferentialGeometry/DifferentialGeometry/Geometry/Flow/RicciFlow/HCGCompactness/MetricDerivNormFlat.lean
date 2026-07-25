import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormRestrict
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Geometry.Topology.SigmaCompactOpen

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem codRestr_mdiffAt
    {A B : Type*} [TopologicalSpace A] [ChartedSpace H A]
    [TopologicalSpace B] [ChartedSpace H B]
    {W : Opens B} {f : A → B} (hmem : ∀ y, f y ∈ W) {x : A}
    (hf : ContMDiffAt I I (∞ : WithTop ℕ∞) f x) :
    ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y => (⟨f y, hmem y⟩ : W)) x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hcont, hdiff⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (by simpa [Function.comp_def] using hcont), ?_⟩
  convert hdiff using 2

private def nestedOpen {U V : Opens M} (_hVU : V ≤ U) : Opens U :=
  ⟨Subtype.val ⁻¹' (V : Set M), V.isOpen.preimage continuous_subtype_val⟩

private def flatNestedEquiv {U V : Opens M} (hVU : V ≤ U) :
    V ≃ nestedOpen hVU where
  toFun x := ⟨⟨x.1, hVU x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv _ := rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def flatNestedDiffeo {U V : Opens M} (hVU : V ≤ U) :
    V ≃ₘ⟮I, I⟯ nestedOpen hVU where
  toEquiv := flatNestedEquiv hVU
  contMDiff_toFun := by
    intro x
    exact codRestr_mdiffAt (fun y => y.2) (contMDiff_inclusion hVU).contMDiffAt
  contMDiff_invFun := by
    intro x
    apply codRestr_mdiffAt (fun y => y.2)
    exact ((contMDiff_subtype_val (I := I) (U := U)).comp
      (contMDiff_subtype_val (I := I) (U := nestedOpen hVU))).contMDiffAt

omit [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem flatNested_mfderiv {U V : Opens M} (hVU : V ≤ U) (x : V) :
    mfderiv I I (flatNestedDiffeo (I := I) hVU : V → nestedOpen hVU) x =
      ContinuousLinearMap.id Real E := by
  let F := flatNestedDiffeo (I := I) hVU
  have hF : MDifferentiableAt I I (F : V → nestedOpen hVU) x :=
    F.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I (Subtype.val : nestedOpen hVU → U) (F x) :=
    (contMDiff_subtype_val (I := I) (U := nestedOpen hVU)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hF
  change mfderiv I I (Opens.inclusion hVU : V → U) x =
    (mfderiv I I (Subtype.val : nestedOpen hVU → U) (F x)).comp
      (mfderiv I I (F : V → nestedOpen hVU) x) at hcomp
  rw [mfderiv_opens_incl (I := I) hVU x,
    mfderiv_subtype_val (I := I) (nestedOpen hVU) (F x)] at hcomp
  simpa [F] using hcomp.symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private theorem metric_ext
    {U : Opens M} {g g' : SmoothRiemannianMetric I U}
    (h : ∀ (x : U) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem flatMetric_eq
    {U V : Opens M} (hVU : V ≤ U)
    [SigmaCompactSpace U] [T2Space U]
    [SigmaCompactSpace V] [T2Space V]
    [SigmaCompactSpace (nestedOpen hVU)]
    (g : SmoothRiemannianMetric I U) :
    g.restrictOpenOfSubset (I := I) hVU =
      Diffeomorph.pullbackMetric (I := I)
        (g.restrictOpen (I := I) (nestedOpen hVU))
        (flatNestedDiffeo (I := I) hVU) := by
  apply metric_ext
  intro x v w
  rw [SmoothRiemannianMetric.restrictSubset_inner,
    Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    flatNested_mfderiv (I := I)]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_eq_of_pull
    {P Q : Type*} [TopologicalSpace P] [ChartedSpace H P]
    [TopologicalSpace Q] [ChartedSpace H Q]
    [IsManifold I ∞ P] [IsManifold I ∞ Q]
    [SigmaCompactSpace P] [T2Space P] [BoundarylessManifold I P]
    [SigmaCompactSpace Q] [T2Space Q] [BoundarylessManifold I Q]
    [IsManifold I 1 P] [IsManifold I 2 P]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    [IsManifold I 1 Q] [IsManifold I 2 Q]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) Q]
    (A B C : SmoothRiemannianMetric I P)
    (gk gInf gRef : SmoothRiemannianMetric I Q)
    (F : P ≃ₘ⟮I, I⟯ Q)
    (hA : A = Diffeomorph.pullbackMetric (I := I) gk F)
    (hB : B = Diffeomorph.pullbackMetric (I := I) gInf F)
    (hC : C = Diffeomorph.pullbackMetric (I := I) gRef F)
    (a : Nat) (x : P) :
    metricDerivNorm (I := I) a A B C x =
      metricDerivNorm (I := I) a gk gInf gRef (F x) := by
  subst A
  subst B
  subst C
  exact metricDerivNorm_pullback (E := E) (H := H) (I := I)
    (M := P) (N := Q) gk gInf gRef F a x



omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDerivNorm_flat
    [I.Boundaryless] {U V : Opens M} (hVU : V ≤ U)
    [SigmaCompactSpace U] [T2Space U]
    [SigmaCompactSpace V] [T2Space V]
    (gk gInf gRef : SmoothRiemannianMetric I U) (a : Nat) (x : V) :
    metricDerivNorm (I := I) a
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricDerivNorm (I := I) a gk gInf gRef (Opens.inclusion hVU x) := by
  let W := nestedOpen hVU
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  letI : IsManifold I 1 V :=
    IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  letI : IsManifold I 2 V :=
    IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) V := by
    change IsManifold I ∞ V
    infer_instance
  letI : IsManifold I 1 W :=
    IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  letI : IsManifold I 2 W :=
    IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) W := by
    change IsManifold I ∞ W
    infer_instance
  let F := flatNestedDiffeo (I := I) hVU
  calc
    metricDerivNorm (I := I) a
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricDerivNorm (I := I) a (gk.restrictOpen (I := I) W)
        (gInf.restrictOpen (I := I) W)
        (gRef.restrictOpen (I := I) W) (F x) :=
      norm_eq_of_pull (E := E) (H := H) (I := I)
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU)
        (gk.restrictOpen (I := I) W)
        (gInf.restrictOpen (I := I) W)
        (gRef.restrictOpen (I := I) W) F
        (flatMetric_eq (I := I) hVU gk)
        (flatMetric_eq (I := I) hVU gInf)
        (flatMetric_eq (I := I) hVU gRef) a x
    _ = metricDerivNorm (I := I) a gk gInf gRef ((F x : W) : U) :=
      metricDerivNorm_restrictOpen (I := I) gk gInf gRef W a (F x)
    _ = metricDerivNorm (I := I) a gk gInf gRef (Opens.inclusion hVU x) := by
      rfl

end HCGCompactness
end DifferentialGeometry
