import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomTensorRSRiemannian


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

def homTensorRSApplyFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    TensorRSSpace r c I x :=
  Ψ x (W.toSection x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullRSFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        (homTensorRSApplyFib (I := I) (M := M) g r a c Ψ W x)) :=
  ContMDiff.clm_bundle_apply (b := id) hΨ W.toSection.contMDiff

set_option backward.isDefEq.respectTransparency false in

def homTensorRSApply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r c where
  toSection :=
    { toFun := fun x : M => homTensorRSApplyFib (I := I) (M := M) g r a c Ψ W x
      contMDiff_toFun := appFullRSFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma appFullRS_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) :
    (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x = Ψ x (W.toSection x) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullRS_add_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W₁ W₂ : SmoothCcTensor g r a) :
    homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ (W₁ + W₂) =
      homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁ + homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁ +
        homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x) =
      (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁).toSection x +
        (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection, appFullRS_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace r a I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [map_add (Ψ x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullRS_smul_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (k : ℝ) (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ (k • W) =
      k • homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x) =
      k • (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x from rfl]
  rw [appFullRS_toSection, appFullRS_toSection]
  rw [show ((k • W).toSection x : TensorRSSpace r a I x) = k • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [map_smul (Ψ x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullRSFib_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ₁ Ψ₂ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    homTensorRSApplyFib (I := I) (M := M) g r a c (fun y => Ψ₁ y + Ψ₂ y) W x =
      homTensorRSApplyFib (I := I) (M := M) g r a c Ψ₁ W x +
        homTensorRSApplyFib (I := I) (M := M) g r a c Ψ₂ W x := by
  rw [homTensorRSApplyFib, homTensorRSApplyFib, homTensorRSApplyFib, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

noncomputable def slotInsertHomTensorRSFib (_g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) :
    TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (a + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (a + 1) I x))
  haveI : T2Space (TensorRSSpace r (a + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (a + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        covGradBundleEquiv (I := I) (M := M) r c x
          (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_add, map_add (covGradBundleEquiv (I := I) (M := M) r c x)]
      map_smul' := fun k D => by
        rw [map_smul (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_smul, map_smul (covGradBundleEquiv (I := I) (M := M) r c x)]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma slotExtendFullFib_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x) :
    slotInsertHomTensorRSFib (I := I) (M := M) g r a c x A D =
      covGradBundleEquiv (I := I) (M := M) r c x
        (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotExtendFullFib_apply_eval (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x)
    (Dlow : Tensor0SSpace r I x) (v0 : TangentSpace I x) (vs : Fin c → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          slotInsertHomTensorRSFib (I := I) (M := M) g r a c x A D) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          A ((covGradBundleEquiv (I := I) (M := M) r a x).symm D v0)) Dlow) vs := by
  rw [slotExtendFullFib_apply (I := I) (M := M) g r a c x A D]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r c x
    (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) = vs := by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) 0 = v0 := by simp [Fin.cons_zero]
  rw [htail, hhead, ContinuousLinearMap.comp_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtendFullFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (a + 1) I z →L[ℝ] TensorRSSpace r (c + 1) I z) x
        (slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (a + 1) I z)
    (V₂ := fun z : M => TensorRSSpace r (c + 1) I z)
    (φ := fun x => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
  intro D
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x
        ((Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r c I z)
      (φ := fun x => (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))
    intro Y
    have hH : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r a ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r a ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r a I z) x
          ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x))) :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r a).comp D.contMDiff
    have hstep1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
          (E := fun z : M => TensorRSSpace r a I z) x
          ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x) (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id) hH Y.contMDiff
    have hstep2 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
          (E := fun z : M => TensorRSSpace r c I z) x
          ((Ψ x) ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x) (Y x)))) :=
      ContMDiff.clm_bundle_apply (b := id) hΨ hstep1
    refine hstep2.congr ?_
    intro x
    rfl
  letI : NormedAddCommGroup (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (c + 1)
  letI : NormedSpace ℝ (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedSpace r (c + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y)) :=
    tensorRSBundle_topology r (c + 1)
  letI : FiberBundle (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_fiber r (c + 1)
  letI : VectorBundle ℝ (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_vector r (c + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) I := tensorRSBundle_smooth ∞ r (c + 1)
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (c + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph ∘
          (fun x : M => (⟨x, (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x))⟩ :
            TotalSpace (E →L[ℝ] TensorRSModel r c ℝ E)
              fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r c I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph.contMDiff.comp hG
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r c x
      ((Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))]
  congr 1

set_option backward.isDefEq.respectTransparency false in

def homTensorRSDirCovDeriv (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) (v : TangentSpace I x) :
    TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
  homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x v

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovDirHom_continuous (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) :
    Continuous (fun v : TangentSpace I x => homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v) :=
  (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x).continuous

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovDirHom_add (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) (v v' : TangentSpace I x) :
    homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x (v + v') =
      homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v +
        homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v' := by
  rw [homTensorRSDirCovDeriv, homTensorRSDirCovDeriv, homTensorRSDirCovDeriv,
    map_add (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x)]

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovDirHom_smul (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) (k : ℝ)
    (v : TangentSpace I x) :
    homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x (k • v) =
      k • homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v := by
  rw [homTensorRSDirCovDeriv, homTensorRSDirCovDeriv,
    map_smul (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x)]

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSCovGradDirCLM (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace r c I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : T2Space (TensorRSSpace r c I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun v : TangentSpace I x => homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v d
      map_add' := fun v v' => by rw [homTensorRSCovDirHom_add, ContinuousLinearMap.add_apply]
      map_smul' := fun k v => by rw [homTensorRSCovDirHom_smul, ContinuousLinearMap.smul_apply]; rfl }

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma homTensorRSCovGradDirCLM_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) (v : TangentSpace I x) :
    homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d v =
      homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v d := by
  rw [homTensorRSCovGradDirCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSCovGradFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) :
    TensorRSSpace r a I x →L[ℝ] TensorRSSpace r (c + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  haveI : T2Space (TensorRSSpace r a I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun d =>
        covGradBundleEquiv (I := I) (M := M) r c x
          (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d)
      map_add' := fun d₁ d₂ => by
        rw [← map_add (covGradBundleEquiv (I := I) (M := M) r c x)]
        refine congrArg (covGradBundleEquiv (I := I) (M := M) r c x) ?_
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.add_apply, homTensorRSCovGradDirCLM_apply,
          homTensorRSCovGradDirCLM_apply, homTensorRSCovGradDirCLM_apply, map_add]
      map_smul' := fun k d => by
        rw [RingHom.id_apply, ← map_smul (covGradBundleEquiv (I := I) (M := M) r c x)]
        refine congrArg (covGradBundleEquiv (I := I) (M := M) r c x) ?_
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.smul_apply, homTensorRSCovGradDirCLM_apply,
          homTensorRSCovGradDirCLM_apply, map_smul] }

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovGradFieldFib_apply_eval (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) (Dlow : Tensor0SSpace r I x)
    (v0 : TangentSpace I x) (vs : Fin c → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x d) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v0 d) Dlow) vs := by
  letI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  letI : T2Space (TensorRSSpace r a I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I x →L[ℝ] Tensor0SSpace a I x))
  have hval : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
        homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
        covGradBundleEquiv (I := I) (M := M) r c x
          (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d)) := by
    rw [homTensorRSCovGradFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk]
  rw [hval]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r c x
    (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) = vs := by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) 0 = v0 := by simp [Fin.cons_zero]
  rw [htail, hhead, homTensorRSCovGradDirCLM_apply]

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem homTensorRSCovGradField_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r (c + 1) I z) x
        (homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)) := by
  have hgrad : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] HomTensorRSModel r a c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] HomTensorRSModel r a c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] HomTensorRSSpace r a c I z) x
        ((homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)).toFun
          (fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x)) := by
    haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
        (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)) ∞ := inferInstance
    have hΨ' : ContMDiffOn I (I.prod 𝓘(ℝ, HomTensorRSModel r a c ℝ E)) ((∞ : WithTop ℕ∞) + 1)
        (fun x : M => TotalSpace.mk' (HomTensorRSModel r a c ℝ E)
          (E := fun z : M => HomTensorRSSpace r a c I z) x
          ((fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x)) Set.univ := by
      have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
      exact (hΨ.of_le h_le).contMDiffOn
    have hres := hcov.contMDiff.contMDiff
      (σ := fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) hΨ'
    intro x
    exact (hres x (Set.mem_univ x)).contMDiffAt Filter.univ_mem
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r a I z) (V₂ := fun z : M => TensorRSSpace r (c + 1) I z)
    (φ := fun x => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
  intro Z
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x
        (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r c I z)
      (φ := fun x => homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))
    intro Y
    have hstep1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
          (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x
          (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
            ((homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)).toFun
              (fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x) (Y x))) :=
      ContMDiff.clm_bundle_apply (b := id) hgrad Y.contMDiff
    have hstep2 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
          (E := fun z : M => TensorRSSpace r c I z) x
          ((show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
            ((homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)).toFun
              (fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x) (Y x)) (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hstep1 Z.contMDiff
    refine hstep2.congr ?_
    intro x
    congr 1
  letI : NormedAddCommGroup (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (c + 1)
  letI : NormedSpace ℝ (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModel_normedSpace r (c + 1)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y)) :=
    tensorRSBundle_topology r (c + 1)
  letI : FiberBundle (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_fiber r (c + 1)
  letI : VectorBundle ℝ (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) :=
    tensorRSBundle_vector r (c + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (c + 1) ℝ E)
      (fun y : M => TensorRSSpace r (c + 1) I y) I := tensorRSBundle_smooth ∞ r (c + 1)
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (c + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph ∘
          (fun x : M => (⟨x, homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x)⟩ :
            TotalSpace (E →L[ℝ] TensorRSModel r c ℝ E)
              fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r c I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph.contMDiff.comp hG
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r c x
      (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))]
  congr 1

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) (v : E) :
    (show TensorRSSpace r c I x from
        tensorCovDerivAt (I := I) (M := M) g r c (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W) x v) =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
          homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x v) (W.toSection x) +
        (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
          (show TensorRSSpace r a I x from tensorCovDerivAt (I := I) (M := M) g r a W x v) := by
  have hval : (fun y : M => (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection y) =
      (fun y : M => (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W.toSection y)) := by
    funext y; rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W y]
  have hΨ_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) y (Ψ y)) x :=
    hΨ.contMDiffAt.mdifferentiableAt (by simp)
  have hW_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun z : M => TensorRSSpace r a I z) y (W.toSection y)) x :=
    W.toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  obtain ⟨Vsec, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hV_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Vsec y)) x :=
    Vsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [tensorCovDerivAt_def (I := I) (M := M) g r c (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W) x v,
    hval]
  rw [show v = (Vsec : Π z : M, TangentSpace I z) x from hVx.symm]
  have hprod := homTensorRSCovariantDerivative_apply_of_mdifferentiableAt I M r a c
    (LeviCivita (I := I) g) Ψ (fun y : M => W.toSection y) (fun y : M => Vsec y)
    hΨ_diff hW_diff hV_diff
  rw [eq_sub_iff_add_eq] at hprod
  rw [tensorCovDerivAt_def (I := I) (M := M) g r a W x ((Vsec : Π z : M, TangentSpace I z) x)]
  rw [← hprod]

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGradBundleEquiv_symm_covGrad_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a : ℕ)
    (W : SmoothCcTensor g r a) (x : M) (v0 : TangentSpace I x) :
    (covGradBundleEquiv (I := I) (M := M) r a x).symm
        ((covGrad (I := I) (M := M) g r a W).toSection x) v0 =
      (show TensorRSSpace r a I x from tensorCovDerivAt (I := I) (M := M) g r a W x v0) := by
  rw [covGrad_toSection_apply (I := I) (M := M) g r a W x, ContinuousLinearEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r c (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W) =
      homTensorRSApply (I := I) (M := M) g r a (c + 1)
          (fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
          (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W +
        homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
          (fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
          (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
          (covGrad (I := I) (M := M) g r a W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSApply (I := I) (M := M) g r a (c + 1)
        (fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
        (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W +
      homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
        (fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
        (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
        (covGrad (I := I) (M := M) g r a W)).toSection x) =
      (homTensorRSApply (I := I) (M := M) g r a (c + 1)
          (fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
          (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W).toSection x +
        (homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
          (fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
          (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
          (covGrad (I := I) (M := M) g r a W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r c (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W) x
    d v]

  have hT1val : Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (homTensorRSApply (I := I) (M := M) g r a (c + 1)
            (fun y : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ y)
            (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x (v 0) (W.toSection x)) d)
        (Matrix.vecTail v) := by
    rw [appFullRS_toSection (I := I) (M := M) g r a (c + 1)
        (fun y : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ y)
        (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [homTensorRSCovGradFieldFib_apply_eval (I := I) (M := M) g r a c Ψ x (W.toSection x) d (v 0)
      (Matrix.vecTail v)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT1val]

  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
            (fun y : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c y (Ψ y))
            (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
            (covGrad (I := I) (M := M) g r a W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
            (show TensorRSSpace r a I x from
              tensorCovDerivAt (I := I) (M := M) g r a W x (v 0))) d)
        (Matrix.vecTail v) := by
    rw [appFullRS_toSection (I := I) (M := M) g r (a + 1) (c + 1)
        (fun y : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c y (Ψ y))
        (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
        (covGrad (I := I) (M := M) g r a W) x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFullFib_apply_eval (I := I) (M := M) g r a c x (Ψ x)
      ((covGrad (I := I) (M := M) g r a W).toSection x) d (v 0) (Matrix.vecTail v)]
    rw [covGradBundleEquiv_symm_covGrad_appFullRS_eq (I := I) (M := M) g r a W x (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]

  rw [tensorCovDerivAt_appFullRS_eq (I := I) (M := M) g r a c Ψ hΨ W x (v 0)]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    homTensorRSDirCovDeriv]

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_continuous_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_homSection_clm_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v :=
  exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (g := g) (r := r) (a := a) (c := c) (Ψ := Ψ) (hΨ := hΨ)

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_appFullRS_le
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g r a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r c x
          ((homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x (W.toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_uniform_riemannianFiberNormSq_homSection_clm_le (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨C, hC_nn, fun W x => ?_⟩
  rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W x]
  exact hC x (W.toSection x)

abbrev HomTensorRSField (r a c : ℕ) (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] : Type _ :=
  Cₛ^∞⟮I; HomTensorRSModel r a c ℝ E, (fun x : M => HomTensorRSSpace r a c I x)⟯

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSFieldApply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) : SmoothCcTensor g r c :=
  homTensorRSApply (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma appFullSec_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) (x : M) :
    (homTensorRSFieldApply (I := I) (M := M) g r a c Q W).toSection x =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Q x) (W.toSection x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullSec_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (Qa + Qb) W =
      homTensorRSFieldApply (I := I) (M := M) g r a c Qa W + homTensorRSFieldApply (I := I) (M := M) g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g r a c Qa W +
        homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x) =
      (homTensorRSFieldApply (I := I) (M := M) g r a c Qa W).toSection x +
        (homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x from rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((Qa + Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) +
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_add, Pi.add_apply]]
  rw [ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullSec_zero_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (0 : HomTensorRSField (E := E) (M := M) r a c I) W = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection]
  rw [show ((0 : HomTensorRSField (E := E) (M := M) r a c I) x :
      TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) = 0 from by
    rw [ContMDiffSection.coe_zero, Pi.zero_apply]]
  rw [ContinuousLinearMap.zero_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullSec_sub_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Qa Qb : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    homTensorRSFieldApply (I := I) (M := M) g r a c (Qa - Qb) W =
      homTensorRSFieldApply (I := I) (M := M) g r a c Qa W - homTensorRSFieldApply (I := I) (M := M) g r a c Qb W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSFieldApply (I := I) (M := M) g r a c Qa W -
        homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x) =
      (homTensorRSFieldApply (I := I) (M := M) g r a c Qa W).toSection x -
        (homTensorRSFieldApply (I := I) (M := M) g r a c Qb W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appFullSec_toSection, appFullSec_toSection, appFullSec_toSection]
  rw [show ((Qa - Qb) x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) =
      (Qa x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) -
        (Qb x : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) from by
    rw [ContMDiffSection.coe_sub, Pi.sub_apply]]
  rw [ContinuousLinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSCovGradSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) : HomTensorRSField (E := E) (M := M) r a (c + 1) I where
  toFun := fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c (fun y : M => Q y) x
  contMDiff_toFun :=
    homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma homTensorRSCovGradSec_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        homTensorRSCovGradSec (I := I) (M := M) g r a c Q x) =
      homTensorRSCovGradFib (I := I) (M := M) g r a c (fun y : M => Q y) x := rfl

set_option backward.isDefEq.respectTransparency false in

noncomputable def slotExtendFullSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r (a + 1) (c + 1) I where
  toFun := fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Q x)
  contMDiff_toFun :=
    slotExtendFullFib_contMDiff (I := I) (M := M) g r a c (fun y : M => Q y) Q.contMDiff

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma slotExtendFullSec_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (x : M) :
    (show TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x from
        slotExtendFullSec (I := I) (M := M) g r a c Q x) =
      slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Q x) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_appFullSec_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r c (homTensorRSFieldApply (I := I) (M := M) g r a c Q W) =
      homTensorRSFieldApply (I := I) (M := M) g r a (c + 1) (homTensorRSCovGradSec (I := I) (M := M) g r a c Q) W +
        homTensorRSFieldApply (I := I) (M := M) g r (a + 1) (c + 1) (slotExtendFullSec (I := I) (M := M) g r a c Q)
          (covGrad (I := I) (M := M) g r a W) :=
  covGrad_appFullRS_eq (I := I) (M := M) g r a c (fun x : M => Q x) Q.contMDiff W


def castHomTensorRSFieldTgt {c c' : ℕ} (r a : ℕ) (h : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a c' I :=
  h ▸ Q


def castHomTensorRSFieldSrc {a a' : ℕ} (r c : ℕ) (h : a = a')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) :
    HomTensorRSField (E := E) (M := M) r a' c I :=
  h ▸ Q

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem appFullSec_castRankCc_db {a a' c c' : ℕ} (g : SmoothRiemannianMetric I M) (r : ℕ)
    (ha : a = a') (hc : c = c')
    (Q : HomTensorRSField (E := E) (M := M) r a c I) (V : SmoothCcTensor g r a) :
    castCcTensorRank g r hc (homTensorRSFieldApply (I := I) (M := M) g r a c Q V) =
      homTensorRSFieldApply (I := I) (M := M) g r a' c' (castHomTensorRSFieldSrc (E := E) (M := M) r c' ha
        (castHomTensorRSFieldTgt (E := E) (M := M) r a hc Q)) (castCcTensorRank g r ha V) := by
  subst ha; subst hc; rfl


def NormalFormFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (p rr : ℕ) : Prop :=
  ∃ Q : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + k) (rr + d + p) I,
    ∀ W : SmoothCcTensor g r rr,
      op p rr W =
        ∑ k ∈ Finset.range (p + 1),
          homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k) (iteratedCovGrad g r rr k W)


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalForm_zeroFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (rr : ℕ) (Q₀ : HomTensorRSField (E := E) (M := M) r (rr + 0) (rr + d + 0) I)
    (hbase : ∀ W : SmoothCcTensor g r rr,
      op 0 rr W = homTensorRSFieldApply (I := I) (M := M) g r (rr + 0) (rr + d + 0) Q₀ W) :
    NormalFormFull (E := E) (I := I) (M := M) g r d op 0 rr := by
  refine ⟨fun k => match k with | 0 => Q₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_normalFormFull_sum (g : SmoothRiemannianMetric I M) (r d p rr : ℕ)
    (Q : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + k) (rr + d + p) I)
    (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + d + p)
        (∑ k ∈ Finset.range (p + 1),
          homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k) (iteratedCovGrad g r rr k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + (p + 1))
            (homTensorRSCovGradSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k))
            (iteratedCovGrad g r rr k W) +
          homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
            (slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k))
            (iteratedCovGrad g r rr (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appFullSec_eq (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
    (iteratedCovGrad g r rr k W)]
  rw [show covGrad (I := I) (M := M) g r (rr + k) (iteratedCovGrad g r rr k W) =
      iteratedCovGrad g r rr (k + 1) W from (iteratedCovGrad_succ g r rr k W).symm]
  rfl


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem castRankCc_appFullSec_iteratedCovGrad_covGrad (g : SmoothRiemannianMetric I M) (r d p rr k : ℕ)
    (Q : HomTensorRSField (E := E) (M := M) r ((rr + 1) + k) ((rr + 1) + d + p) I)
    (W : SmoothCcTensor g r rr) :
    castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
        (homTensorRSFieldApply (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + d + p) Q
          (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))) =
      homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
        (castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
          (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
            (by omega : (rr + 1) + d + p = rr + d + (p + 1)) Q))
        (iteratedCovGrad g r rr (k + 1) W) := by
  rw [appFullSec_castRankCc_db (E := E) g r (by omega : (rr + 1) + k = rr + (k + 1))
    (by omega : (rr + 1) + d + p = rr + d + (p + 1)) Q
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g r rr k W)
  exact castRankCc_db_heq g r (by omega : (rr + 1) + k = rr + (k + 1))
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))


omit [NeZero (Module.finrank ℝ E)] in
theorem normalFormFull_succ (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + d + p) (op p rr W) =
        op (p + 1) rr W +
          castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (p : ℕ) (hp : ∀ rr, NormalFormFull (E := E) (I := I) (M := M) g r d op p rr) (rr : ℕ) :
    NormalFormFull (E := E) (I := I) (M := M) g r d op (p + 1) rr := by
  classical
  obtain ⟨Qr, hQr⟩ := hp rr
  obtain ⟨Qr1, hQr1⟩ := hp (rr + 1)

  set Tk : (k : ℕ) → HomTensorRSField (E := E) (M := M) r (rr + (k + 1)) (rr + d + (p + 1)) I := fun k =>
    slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k) -
      castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
        (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
          (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k))
    with hTk_def
  refine ⟨fun j => match j with
    | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (rr + 0) (rr + d + p) (Qr 0)
    | (k + 1) =>
        (if h : k + 1 < p + 1 then
          homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
          else 0) + Tk k, ?_⟩
  intro W

  have hrec : op (p + 1) rr W =
      covGrad g r (rr + d + p) (op p rr W) -
        castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
          (op p (rr + 1) (covGrad g r rr W)) := by
    rw [covGrad_op p rr W]; abel
  rw [hrec, hQr W]

  rw [covGrad_normalFormFull_sum (I := I) (M := M) g r d p rr Qr W]

  rw [hQr1 (covGrad g r rr W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
          (homTensorRSFieldApply (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + d + p) (Qr1 k)
            (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W)))) =
      ∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
              (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k)))
          (iteratedCovGrad g r rr (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appFullSec_iteratedCovGrad_covGrad (E := E) (I := I) (M := M) g r d p rr k (Qr1 k) W)]

  rw [Finset.sum_add_distrib]

  rw [Finset.sum_range_succ' (fun j =>
    homTensorRSFieldApply (I := I) (M := M) g r (rr + j) (rr + d + (p + 1))
      ((match j with
        | 0 => homTensorRSCovGradSec (I := I) (M := M) g r (rr + 0) (rr + d + p) (Qr 0)
        | (k + 1) =>
            (if h : k + 1 < p + 1 then
              homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g r rr j W)) (p + 1)]

  rw [show (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          ((if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appFullSec_add_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (slotExtendFullSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k))
          (iteratedCovGrad g r rr (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (castHomTensorRSFieldSrc (E := E) (M := M) r (rr + d + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castHomTensorRSFieldTgt (E := E) (M := M) r ((rr + 1) + k)
              (by omega : (rr + 1) + d + p = rr + d + (p + 1)) (Qr1 k)))
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appFullSec_sub_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (if h : k + 1 < p + 1 then
            homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        homTensorRSFieldApply (I := I) (M := M) g r (rr + (k + 1)) (rr + d + (p + 1))
          (homTensorRSCovGradSec (I := I) (M := M) g r (rr + (k + 1)) (rr + d + p) (Qr (k + 1)))
          (iteratedCovGrad g r rr (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [dif_neg (by omega : ¬ (p + 1 < p + 1)), appFullSec_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [dif_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]

  rw [Finset.sum_range_succ' (fun k =>
    homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + (p + 1))
      (homTensorRSCovGradSec (I := I) (M := M) g r (rr + k) (rr + d + p) (Qr k))
      (iteratedCovGrad g r rr k W)) p]

  abel


omit [NeZero (Module.finrank ℝ E)] in
theorem normalFormFull_of_base (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + d + p) (op p rr W) =
        op (p + 1) rr W +
          castCcTensorRank g r (by omega : (rr + 1) + d + p = rr + d + (p + 1))
            (op p (rr + 1) (covGrad g r rr W)))
    (Q₀ : ∀ rr : ℕ, HomTensorRSField (E := E) (M := M) r (rr + 0) (rr + d + 0) I)
    (hbase : ∀ (rr : ℕ) (W : SmoothCcTensor g r rr),
      op 0 rr W = homTensorRSFieldApply (I := I) (M := M) g r (rr + 0) (rr + d + 0) (Q₀ rr) W)
    (p : ℕ) : ∀ rr : ℕ, NormalFormFull (E := E) (I := I) (M := M) g r d op p rr := by
  induction p with
  | zero => exact fun rr => normalForm_zeroFull (E := E) (I := I) (M := M) g r d op rr (Q₀ rr) (hbase rr)
  | succ p ih =>
      exact fun rr => normalFormFull_succ (E := E) (I := I) (M := M) g r d op covGrad_op p ih rr

set_option maxHeartbeats 1600000 in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_jet_bound_of_normalFormFull (g : SmoothRiemannianMetric I M) (r d : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + d + p))
    (p rr : ℕ) (hNF : NormalFormFull (E := E) (I := I) (M := M) g r d op p rr) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + d + p) x ((op p rr W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  obtain ⟨Q, hQ⟩ := hNF

  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appFullRS_le (I := I) (M := M) g r (rr + k) (rr + d + p)
      (fun x : M => Q k x) (Q k).contMDiff
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩
  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g r (rr + k) x
    ((iteratedCovGrad g r rr k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + k) x _

  rw [hQ W, SmoothCcTensor.toSection_sum_apply]

  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (rr + d + p) x
    (Finset.range (p + 1))
    (fun k => (homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
      (iteratedCovGrad g r rr k W)).toSection x)) ?_
  rw [Finset.card_range]

  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + d + p) x
          ((homTensorRSFieldApply (I := I) (M := M) g r (rr + k) (rr + d + p) (Q k)
            (iteratedCovGrad g r rr k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_

  have hCa_le : (∑ k ∈ Finset.range (p + 1), C k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by ring

set_option backward.isDefEq.respectTransparency false in

private noncomputable def chooseSecAtFull
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    SmoothCcTensor g r a where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
    letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
      (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma chooseSecAtFull_eq
    (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    (chooseSecAtFull (I := I) (M := M) g r a x v).toSection x = v :=
  letI : NormedAddCommGroup (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
  letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
    (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x v)

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

private noncomputable def valueLocalLinearHomFib
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (x : M) : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) := inferInstance
  haveI : T2Space (TensorRSSpace r a I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun v : TensorRSSpace r a I x =>
        (F (chooseSecAtFull (I := I) (M := M) g r a x v)).toSection x
      map_add' := fun v w => by
        have hsum : (chooseSecAtFull (I := I) (M := M) g r a x (v + w)).toSection x =
            (chooseSecAtFull (I := I) (M := M) g r a x v +
              chooseSecAtFull (I := I) (M := M) g r a x w).toSection x := by
          rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
            chooseSecAtFull_eq, chooseSecAtFull_eq, chooseSecAtFull_eq]
        rw [hloc _ _ x hsum, hadd]
      map_smul' := fun k v => by
        have hsm : (chooseSecAtFull (I := I) (M := M) g r a x (k • v)).toSection x =
            (k • chooseSecAtFull (I := I) (M := M) g r a x v).toSection x := by
          rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
            chooseSecAtFull_eq, chooseSecAtFull_eq]
        rw [hloc _ _ x hsm, hsmul]
        rfl }

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma valueLocalLinearHomFib_apply
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x)
    (W : SmoothCcTensor g r a) (x : M) :
    valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (W.toSection x) =
      (F W).toSection x := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  rw [valueLocalLinearHomFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  exact hloc _ W x (chooseSecAtFull_eq (I := I) (M := M) g r a x (W.toSection x))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem valueLocalLinearHomFib_contMDiff
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x
        (valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := TensorRSModel r a ℝ E) (V₁ := fun z : M => TensorRSSpace r a I z)
    (F₂ := TensorRSModel r c ℝ E) (V₂ := fun z : M => TensorRSSpace r c I z)
    (φ := fun x => valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x)
  intro Z
  set Wσ : SmoothCcTensor g r a := ⟨Z, HasCompactSupport.of_compactSpace _⟩ with hWσ
  have hpt : ∀ x : M, valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x (Z x) =
      (F Wσ).toSection x := fun x =>
    valueLocalLinearHomFib_apply (I := I) (M := M) g r a c F hadd hsmul hloc Wσ x
  refine (F Wσ).toSection.contMDiff.congr ?_
  intro x
  exact (congrArg (TotalSpace.mk' (TensorRSModel r c ℝ E)
    (E := fun z : M => TensorRSSpace r c I z) x) (hpt x)).symm ▸ rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem exists_value_local_appFullSec (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (F : SmoothCcTensor g r a → SmoothCcTensor g r c)
    (hadd : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      (F (W₁ + W₂)).toSection x = (F W₁).toSection x + (F W₂).toSection x)
    (hsmul : ∀ (k : ℝ) (W : SmoothCcTensor g r a) (x : M),
      (F (k • W)).toSection x = k • (F W).toSection x)
    (hloc : ∀ (W₁ W₂ : SmoothCcTensor g r a) (x : M),
      W₁.toSection x = W₂.toSection x → (F W₁).toSection x = (F W₂).toSection x) :
    ∃ Θ : HomTensorRSField (E := E) (M := M) r a c I,
      ∀ (W : SmoothCcTensor g r a), F W = homTensorRSFieldApply (I := I) (M := M) g r a c Θ W := by
  refine ⟨{ toFun := fun x : M => valueLocalLinearHomFib (I := I) (M := M) g r a c F hadd hsmul hloc x
            contMDiff_toFun :=
              valueLocalLinearHomFib_contMDiff (I := I) (M := M) g r a c F hadd hsmul hloc }, fun W => ?_⟩
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appFullSec_toSection]
  exact (valueLocalLinearHomFib_apply (I := I) (M := M) g r a c F hadd hsmul hloc W x).symm

end Connection
end Integral
end DifferentialGeometry

end
