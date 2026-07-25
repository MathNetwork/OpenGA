import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Tensor.Multilinear.ModelProductContinuousBilinear
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficientsFibreOperators


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongrSectionContMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
          Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ
      (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem slotPermCLM_field_contMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (slotPermCLM (I := I) ρ x (Z x))) := by
  refine (domDomCongrSectionContMDiff (I := I) ρ Z hZ).congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t)
    (slotPermCLM_apply (I := I) ρ x (Z x))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem tensorProdWithCLM_field_contMDiff (m k : ℕ)
    (P : ∀ x : M, Tensor0SBundle.Tensor0SSpace m I x)
    (Q : ∀ x : M, Tensor0SBundle.Tensor0SSpace k I x)
    (hP : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x (P x)))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel k ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x (Q x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z) x
        (tensorProdWithCLM (I := I) m k x (P x) (Q x))) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) m
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) k
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (m + k)
  intro x₀
  rw [Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel (m + k) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + k) I z)]
  have hP' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel m ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀).mp (hP x₀)
  have hQ' := (Bundle.contMDiffAt_section (F := Tensor0SBundle.Tensor0SModel k ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀).mp (hQ x₀)
  have h_combine : ContMDiffAt I 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + k) ℝ E) ∞
      (fun x => Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        ((trivializationAt (Tensor0SBundle.Tensor0SModel m ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace m I z) x₀ ⟨x, P x⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel k ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace k I z) x₀ ⟨x, Q x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := Bundle.continuousMultilinearMap.modelProductL
        (𝕜 := ℝ) (F := E) m k)).clm_apply hP').clm_apply hQ'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  apply ContinuousMultilinearMap.ext
  intro v
  rw [Bundle.continuousMultilinearMap.modelProductL_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x with hsymmL
  change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
      (Tensor0SBundle.Tensor0SSpace.toModel (P x))
      (Tensor0SBundle.Tensor0SSpace.toModel (Q x)))
      (fun i => symmL (v i)) = _
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connContrCLM_field_contMDiff (m k : ℕ)
    (Bf : ∀ x : M, Tensor0SBundle.TensorRSSpace 1 (k + 1) I x)
    (hBf : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (k + 1) I z) x (Bf x)))
    (Df : ∀ x : M, Tensor0SBundle.Tensor0SSpace (m + 1) I x)
    (hDf : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1) I z) x (Df x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) x
        (connContrCLM (I := I) m k x (Bf x) (Df x))) := by
  have hΨ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 (m + 1 + k + 1) ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I z) x
        (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) x (Df x)).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (F₂ := Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z)
      (φ := fun x : M =>
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) x (Df x)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x))
    intro om
    have hBom : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (k + 1) ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace (k + 1) I z) x
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x) (om x))) :=
      ContMDiff.clm_bundle_apply (b := id) hBf om.contMDiff
    have hprod := tensorProdWithCLM_field_contMDiff (I := I) (m + 1) (k + 1)
      (fun x => Df x)
      (fun x => (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
          Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x) (om x))
      hDf hBom
    refine hprod.congr (fun x => ?_)
    exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k + 1) ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k + 1) I z) x t) rfl
  have hTr := contractTraceField_contMDiff (I := I) 0 (m + 1 + k)
    (fun x : M =>
      (show Tensor0SBundle.TensorRSSpace 1 (m + 1 + k + 1) I x from
        (tensorProdWithCLM (I := I) (m + 1) (k + 1) x (Df x)).comp
          (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (k + 1) I x from Bf x)))
    hΨ
  have hEval := ContMDiff.clm_bundle_apply (b := id) hTr
    (unitZeroSec (I := I) (M := M)).contMDiff
  refine hEval.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (m + 1 + k) ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace (m + 1 + k) I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem linearizedRicciConnDiffOrder1CLM_field_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 3 I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
        (linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x))) := by
  have hAsm := (connDiffSection (I := I) g₁ g₀).toSection.contMDiff
  have hpre102 := slotPermCLM_field_contMDiff (I := I) perm3_102 Z hZ
  have hpre120 := slotPermCLM_field_contMDiff (I := I) perm3_120 Z hZ
  have h₁ := slotPermCLM_field_contMDiff (I := I) perm4_0312 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x (Z x)) hpre102)
  have h₂ := slotPermCLM_field_contMDiff (I := I) perm4_0213 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x (Z x)) hpre120)
  have h₃ := slotPermCLM_field_contMDiff (I := I) perm4_2301 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => Z x) hZ)
  have h₄ := slotPermCLM_field_contMDiff (I := I) perm4_1302 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x (Z x)) hpre102)
  have h₅ := slotPermCLM_field_contMDiff (I := I) perm4_1203 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x (Z x)) hpre120)
  have hsum := ((((h₁.add_section h₂).add_section h₃).add_section h₄).add_section h₅).neg_section
  refine hsum.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem linearizedRicciConnDiffOrder0CLM_field_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 2 I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
        (linearizedRicciConnDiffOrder0CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x)
          ((covGrad (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀)).toSection x) (Z x))) := by
  have hAsm := (connDiffSection (I := I) g₁ g₀).toSection.contMDiff
  have hDAsm := (covGrad (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g₁ g₀)).toSection.contMDiff
  have hZswap := slotPermCLM_field_contMDiff (I := I) perm2_10 Z hZ
  have hinnJ := connContrCLM_field_contMDiff (I := I) 1 1
    (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
    (fun x => Z x) hZ
  have hinnJ' := connContrCLM_field_contMDiff (I := I) 1 1
    (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
    (fun x => slotPermCLM (I := I) perm2_10 x (Z x)) hZswap
  have hu₃ := slotPermCLM_field_contMDiff (I := I) perm4_3201 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x)))
      (slotPermCLM_field_contMDiff (I := I) perm3_102 _ hinnJ))
  have hu₄ := slotPermCLM_field_contMDiff (I := I) perm4_2301 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_102 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)
          (slotPermCLM (I := I) perm2_10 x (Z x))))
      (slotPermCLM_field_contMDiff (I := I) perm3_102 _ hinnJ'))
  have hu₅ := slotPermCLM_field_contMDiff (I := I) perm4_3102 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x)))
      (slotPermCLM_field_contMDiff (I := I) perm3_120 _ hinnJ))
  have hu₆ := slotPermCLM_field_contMDiff (I := I) perm4_1302 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)
        (slotPermCLM (I := I) perm2_10 x (Z x)))
      hinnJ')
  have hu₇ := slotPermCLM_field_contMDiff (I := I) perm4_1203 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => connContrCLM (I := I) 1 1 x
        ((connDiffSection (I := I) g₁ g₀).toSection x) (Z x))
      hinnJ)
  have hu₈ := slotPermCLM_field_contMDiff (I := I) perm4_2103 _
    (connContrCLM_field_contMDiff (I := I) 2 1
      (fun x => (connDiffSection (I := I) g₁ g₀).toSection x) hAsm
      (fun x => slotPermCLM (I := I) perm3_120 x
        (connContrCLM (I := I) 1 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)
          (slotPermCLM (I := I) perm2_10 x (Z x))))
      (slotPermCLM_field_contMDiff (I := I) perm3_120 _ hinnJ'))
  have hu₁ := slotPermCLM_field_contMDiff (I := I) perm4_3012 _
    (connContrCLM_field_contMDiff (I := I) 1 2
      (fun x => (covGrad (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) g₁ g₀)).toSection x) hDAsm
      (fun x => Z x) hZ)
  have hu₂ := slotPermCLM_field_contMDiff (I := I) perm4_2013 _
    (connContrCLM_field_contMDiff (I := I) 1 2
      (fun x => (covGrad (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) g₁ g₀)).toSection x) hDAsm
      (fun x => slotPermCLM (I := I) perm2_10 x (Z x)) hZswap)
  have hsum := (((((((hu₃.add_section hu₄).add_section hu₅).add_section
    hu₆).add_section hu₇).add_section hu₈).sub_section hu₁).sub_section hu₂)
  refine hsum.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem ricciCometricFourTraceCLM_field_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 4 I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        (ricciCometricFourTraceCLM (I := I) g₁ x (Z x))) := by
  have ha := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2)
    (slotPermCLM_field_contMDiff (I := I) perm4_0231 Z hZ)
  have hb := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2)
    (slotPermCLM_field_contMDiff (I := I) perm4_0321 Z hZ)
  have hc := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hZ
  have hd := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2)
    (slotPermCLM_field_contMDiff (I := I) perm4_2301 Z hZ)
  have hcomb := (((ha.add_section hb).sub_section hc).sub_section hd).const_smul_section
    (a := ((1 : ℝ) / 2))
  refine hcomb.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

noncomputable def linearizedRicciConnDiffOrder1CometricTracedCLM (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (ricciCometricFourTraceCLM (I := I) g₁ x).comp
    (linearizedRicciConnDiffOrder1CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x))

noncomputable def linearizedRicciConnDiffOrder0CometricTracedCLM (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (ricciCometricFourTraceCLM (I := I) g₁ x).comp
    (linearizedRicciConnDiffOrder0CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x)
      ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem linearizedRicciConnDiffOrder1CometricTracedCLM_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x : M => linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x)
  intro Y
  have hE1 := linearizedRicciConnDiffOrder1CLM_field_contMDiff (I := I) g₀ g₁
    (fun x => Y x) Y.contMDiff
  have hCK := ricciCometricFourTraceCLM_field_contMDiff (I := I) g₁
    (fun x => linearizedRicciConnDiffOrder1CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x) (Y x)) hE1
  refine hCK.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8000 in

omit [NeZero (Module.finrank ℝ E)] in
theorem linearizedRicciConnDiffOrder0CometricTracedCLM_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x : M => linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x)
  intro Y
  have hE0 := linearizedRicciConnDiffOrder0CLM_field_contMDiff (I := I) g₀ g₁
    (fun x => Y x) Y.contMDiff
  have hCK := ricciCometricFourTraceCLM_field_contMDiff (I := I) g₁
    (fun x => linearizedRicciConnDiffOrder0CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x)
      ((covGrad (I := I) (M := M) g₀ 1 2
          (connDiffSection (I := I) g₁ g₀)).toSection x) (Y x)) hE0
  refine hCK.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

noncomputable def linearizedRicciConnDiffOrder1CoeffField
    (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from
          linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x)
      contMDiff_toFun := linearizedRicciConnDiffOrder1CometricTracedCLM_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

noncomputable def linearizedRicciConnDiffOrder0CoeffField
    (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x)
      contMDiff_toFun := linearizedRicciConnDiffOrder0CometricTracedCLM_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem linearizedRicciConnDiffOrder1CoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x) := rfl


omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem linearizedRicciConnDiffOrder0CoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x) := rfl

def linearizedRicciConnDiffOrder1Coeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s)

def linearizedRicciConnDiffOrder0Coeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s)


theorem linearizedRicciConnDiffOrder0Coeff_eq_base_add_sub
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
            - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s) := by
  abel


theorem linearizedRicciConnDiffOrder1Coeff_eq_base_add_sub
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
            - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s) := by
  abel

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
