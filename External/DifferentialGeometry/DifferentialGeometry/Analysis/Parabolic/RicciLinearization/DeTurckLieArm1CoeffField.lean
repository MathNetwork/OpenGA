import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSubstitutionFiberNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.DeTurckLieArm2TraceCoeff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricConnDiffLoweredTrilinear


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieArm1PairPermCorrection : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 1, 3, 5], ![1, 3, 2, 4, 0, 5], by decide, by decide⟩

def deTurckLieArm1PairPermOuterZero : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1], by decide, by decide⟩

def deTurckLieArm1PairPermOuterTwo : Equiv.Perm (Fin 6) :=
  ⟨![0, 5, 2, 4, 1, 3], ![0, 4, 2, 5, 3, 1], by decide, by decide⟩

def deTurckLieArm1PairPermInnerTwo : Equiv.Perm (Fin 6) :=
  ⟨![4, 0, 2, 5, 1, 3], ![1, 4, 2, 5, 0, 3], by decide, by decide⟩

def deTurckLieArm1VecSlotPerm : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

def deTurckLieArm1KoszulMidPerm : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

def deTurckLieArm1KoszulZeroPerm : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

noncomputable def deTurckLiePairTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 6)) (x : M) (κ : Tensor0SBundle.Tensor0SSpace 3 I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ((cometricDoubleTraceFib (I := I) g₁ 2 x).comp
      ((cometricDoubleTraceFib (I := I) g₁ 4 x).comp
        (domDomCongrFibRank (I := I) 6 σ x))).comp
    (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x κ)

noncomputable def deTurckLieKoszulTraceFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      connDiffFib (I := I) g₁ g₀ x).comp
    ((cometricDoubleTraceFib (I := I) g₁ 1 x).comp
      (domDomCongrFibRank (I := I) 3 σ x))

noncomputable def deTurckLieArm1CoreFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermInnerTwo x
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermCorrection x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    - (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)).comp
        (domDomCongrFibRank (I := I) 3 deTurckLieArm1VecSlotPerm x)
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterZero x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    - deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulMidPerm x
    - deTurckLiePairTraceFib (I := I) g₁ deTurckLieArm1PairPermOuterTwo x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)

noncomputable def deTurckLieArm1Fib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x)
    + deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x
    + (domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x).comp
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x)
    + deTurckLieKoszulTraceFib (I := I) g₀ g₁ deTurckLieArm1KoszulZeroPerm x

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor0SProd_section_contMDiff {p q : ℕ}
    (Y : ∀ x : M, Tensor0SBundle.Tensor0SSpace p I x)
    (K : ∀ x : M, Tensor0SBundle.Tensor0SSpace q I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x (Y x)))
    (hK : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z) x (K x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + q) I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
            (Tensor0SBundle.Tensor0SSpace.toModel (K x))))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
          (Tensor0SBundle.Tensor0SSpace.toModel (K x))) :
          Tensor0SBundle.Tensor0SSpace (p + q) I x))).mpr ?_
  have hYc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Y x)).mp hY
  have hKc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => K x)).mp hK
  intro τ x₀
  refine (((contMDiffAt_const (I := I) (x := x₀) (n := (∞ : WithTop ℕ∞))
    (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
      (hYc (τ ∘ Fin.castAdd q) x₀)).clm_apply
        (hKc (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
    continuousMultilinearMap_basis_repr]
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
      (Tensor0SBundle.Tensor0SSpace.toModel (Y x)) (Tensor0SBundle.Tensor0SSpace.toModel (K x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem deTurckLiePairTraceFib_apply_section_contMDiff
    (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 6))
    (κ : ∀ x : M, Tensor0SBundle.Tensor0SSpace 3 I x)
    (hκ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x (κ x)))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLiePairTraceFib (I := I) g₁ σ x (κ x) (Y x))) := by
  classical
  have hprod := tensor0SProd_section_contMDiff (I := I) (p := 3) (q := 3)
    (fun x => Y x) κ Y.contMDiff hκ
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 6) σ
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 3 3
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x))
        (Tensor0SBundle.Tensor0SSpace.toModel (κ x)))) hprod
  have htr4 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 4) hperm
  have htr2 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) htr4
  refine htr2.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLiePairTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, tensor0SProdKappaFib_apply, domDomCongrFibRank_apply]
  rfl


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieKoszulTraceFib_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 3))
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieKoszulTraceFib (I := I) g₀ g₁ σ x (Y x))) := by
  classical
  have hperm := domDomCongr_section_contMDiff_local (I := I) (d := 3) σ
    (fun x => Y x) Y.contMDiff
  have htr1 := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) hperm
  have hkos := ContMDiff.clm_bundle_apply (b := id)
    (connDiffFib_contMDiff (I := I) g₁ g₀) htr1
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieKoszulTraceFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply]
  rfl


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieArm1CoreFib_apply_section_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Y : ContMDiffSection I (Tensor0SBundle.Tensor0SModel 3 ℝ E) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x (Y x))) := by
  classical
  have hS2 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermInnerTwo
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hB := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermCorrection
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg) Y
  have hpermY := domDomCongr_section_contMDiff_local (I := I) (d := 3)
    deTurckLieArm1VecSlotPerm (fun x => Y x) Y.contMDiff
  have hT2 := interiorProductField_contMDiff (I := I) 2
    (fun x => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr deTurckLieArm1VecSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))) hpermY
    (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)
  have hT3 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermOuterZero
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hT4 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieArm1KoszulMidPerm Y
  have hT5 := deTurckLiePairTraceFib_apply_section_contMDiff (I := I) g₁
    deTurckLieArm1PairPermOuterTwo
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀) Y
  have hsum := ((((hS2.sub_section hB).sub_section hT2).sub_section hT3).sub_section
    hT4).sub_section hT5
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieArm1CoreFib]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckLieArm1Fib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)
  intro Y
  have hW := interiorProductField_contMDiff (I := I) 2 (fun x => Y x) Y.contMDiff
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg)
  have hcore := deTurckLieArm1CoreFib_apply_section_contMDiff (I := I) g₀ g₁ g_bg Y
  have hcoreswap := domDomCongr_section_contMDiff_local (I := I) (d := 2)
    (Equiv.swap (0 : Fin 2) 1)
    (fun x => deTurckLieArm1CoreFib (I := I) g₀ g₁ g_bg x (Y x)) hcore
  have hS3 := deTurckLieKoszulTraceFib_apply_section_contMDiff (I := I) g₀ g₁
    deTurckLieArm1KoszulZeroPerm Y
  have hsum := ((hW.add_section hcore).add_section hcoreswap).add_section hS3
  refine hsum.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieArm1Fib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [domDomCongrFibRank_apply]
  rfl

noncomputable def deTurckLieArm1Coeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x)
      contMDiff_toFun := deTurckLieArm1Fib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckLieArm1Coeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        deTurckLieArm1Fib (I := I) g₀ g₁ g_bg x) := rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
