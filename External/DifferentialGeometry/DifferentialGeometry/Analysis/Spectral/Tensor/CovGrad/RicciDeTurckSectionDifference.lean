import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceKoszulSecondCovGrad
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferencePrincipalEndomorphismTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceSymmetrizedReindexedCoeff
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceReindexingArmSplitting
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceRiemannFrameFixedBicontraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceDeTurckLieBicontraction


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connDiffQuad_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q r : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q) r
      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) r
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r := by
  rw [connDiff_bilinear_diff_split (I := I) g₀ g₁ g₁' x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q)
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x p q]


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem block3LegSummand_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (Xv0 Xv1 Xei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xei Xv1 x) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xei Xv1 x) (Xv0 x)) =
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xv0 x)) (Xei x)
          + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xei x)) (Xv0 x)
            + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) := by
  have h1 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xv0 x) (Xei x)
  have h2 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xei x) (Xv0 x)
  change (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xei x)) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) = _
  rw [sub_sub_sub_comm, h1, h2]

def connDiffBiKernelBilin (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₀.inner x).comp
    ((PDE.DeTurck.connDiff (I := I) gj g₀ x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem connDiffBiKernelBilin_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q v0 v1 =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [connDiffBiKernelBilin, ContinuousLinearMap.comp_apply]

def connDiffBiSummandFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem connDiffBiSummandFib_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) (v 0)) (v 1) := by
  rw [connDiffBiSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def connDiffBiContrFibFixedFrame (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connDiffBiContrFibFixedFrame_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (B a x) (B b x)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [connDiffBiContrFibFixedFrame, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connDiffBiSummandFib_toModel]
  ring

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffBiKernelBilin_homSection_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x) (V0 x))
  intro W
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₁' hp hq
  have houter : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gj g₀ hinner V0.contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (p x) (q x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀
      ⟨fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b), houter⟩
      ⟨fun b => W b, W.contMDiff⟩
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connDiffBiKernelBilin_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffBiContrFibFixedFrame_apply_section_contMDiff
    (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))
      (connDiffBiKernelBilin_homSection_contMDiff (I := I) gj g₀ g₁ g₁' (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x)
          (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [connDiffBiContrFibFixedFrame, hStot_def]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffBiContrFibFixedFrame_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x)
  intro Y
  exact connDiffBiContrFibFixedFrame_apply_section_contMDiff (I := I) gj g₀ g₁ g₁' B hB Y

def frameConnDiffBiKernel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((PDE.DeTurck.connDiff (I := I) gj g₀ x).flip v0 |>.comp
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_smul c p, map_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem frameConnDiffBiKernel_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' x v0 v1 p q =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [frameConnDiffBiKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

def connDiffBiContrFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x) x

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connDiffBiContrFib_eq_fixedFrame_on_nbhd (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connDiffBiContrFib (I := I) gj g₀ g₁ g₁' y =
      connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel,
    connDiffBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (PDE.DeTurck.connDiff (I := I) gj g₀ y
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' y (Bf a) (Bf b)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnDiffBiKernel_apply (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
theorem connDiffBiContrFib_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁'
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    connDiffBiContrFibFixedFrame_contMDiff (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connDiffBiContrFib_eq_fixedFrame_on_nbhd (I := I) gj g₀ g₁ g₁' x₀ hy))

def connDiffBiContrCoeffField (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))
      contMDiff_toFun := connDiffBiContrFib_contMDiff (I := I) gj g₀ g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] theorem connDiffBiContrCoeffField_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x : M) :
    (connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

noncomputable def connDiffBiContrCoeff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁'

omit [I.Boundaryless] in
@[simp] theorem connDiffBiContrCoeff_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl


omit [I.Boundaryless] in
theorem connDiffBiContrCoeff_appCc_eq (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁') W)
        x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x
            (PDE.DeTurck.connDiff (I := I) gj g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₀ x b x)) (v 0)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₀ x a x
              else smoothOrthoFrame (I := I) g₀ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
