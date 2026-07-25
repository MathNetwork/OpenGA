import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
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

def connDiffIteratedCommKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0)
          - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p)
      map_add' := fun v0 v0' => by
        simp only [map_add, ContinuousLinearMap.add_apply]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply]
        simp only [map_smul, ContinuousLinearMap.smul_apply]
        rw [smul_sub] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connDiffAACommKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v0) v1
        - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) p) v1 := by
  rw [connDiffIteratedCommKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.sub_apply]

def frameConnDiffAACommKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        haveI : FiniteDimensional ℝ (TangentSpace I x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        LinearMap.toContinuousLinearMap
          { toFun := fun q => connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1
            map_add' := fun q q' => by
              rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply,
                connDiffAACommKernelBilin_apply]
              simp only [map_add, ContinuousLinearMap.add_apply]
              ring
            map_smul' := fun c q => by
              rw [RingHom.id_apply, connDiffAACommKernelBilin_apply,
                connDiffAACommKernelBilin_apply]
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring }
      map_add' := fun p p' => by
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply,
          connDiffAACommKernelBilin_apply]
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      map_smul' := fun c p => by
        rw [RingHom.id_apply]
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [connDiffAACommKernelBilin_apply, connDiffAACommKernelBilin_apply]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma frameConnDiffAACommKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (v0 v1 p q : TangentSpace I x) :
    frameConnDiffAACommKernel (I := I) g₀ g₁ x v0 v1 p q =
      connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q v0 v1 := by
  rw [frameConnDiffAACommKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def connDiffAACommSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connDiffAACommSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffAACommSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x p q (v 0) (v 1) := by
  rw [connDiffAACommSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def connDiffAACommBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma connDiffAACommBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [connDiffAACommBiContrFibFixedFrame, ContinuousLinearMap.sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connDiffAACommSummandFib_toModel]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffAACommKernelBilin_homSection_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x (p x) (q x) (V0 x))
  intro W
  have hAqp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hq hp
  have hAAqpV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b)) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hAqp V0.contMDiff
  have hAqV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hq V0.contMDiff
  have hAAqVp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b)) (p b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hAqV hp
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (p b)) (V0 b), hAAqpV⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (q b) (V0 b)) (p b), hAAqVp⟩
      ⟨fun b => W b, W.contMDiff⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (p x)) (V0 x)) (W x)
        - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q x) (V0 x)) (p x)) (W x)) :=
    hs1.sub hs2
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connDiffIteratedCommKernelBilin (I := I) g₀ g₁ y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connDiffAACommKernelBilin_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffAACommBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b' => Y b') Y.contMDiff
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
      (fun x => connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (connDiffAACommKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M =>
          connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  have hcoe1 : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), T2 a b) Finset.univ
  have hcoe2 : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((T2 a b : Π z : M, Tensor0SSpace 2 I z)) :=
    fun a => map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => T2 a b) Finset.univ
  have hStot := (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    T2 a b).contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  have hval : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) := by
    have h1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) x =
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  rw [connDiffAACommBiContrFibFixedFrame, ContinuousLinearMap.sum_apply]
  rw [show ∑ a : Fin (Module.finrank ℝ E), (∑ b : Fin (Module.finrank ℝ E),
      connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x)) (Y x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        connDiffAACommSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x) from
    Finset.sum_congr rfl (fun a _ => ContinuousLinearMap.sum_apply _ _ _)]
  rw [← hval]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connDiffAACommBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM
          (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact connDiffAACommBiContrFibFixedFrame_apply_section_contMDiff
    (I := I) g₀ g₁ B hB Y

def connDiffAACommBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₁ x) x


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma connDiffAACommBiContrFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffAACommBiContrFib (I := I) g₀ g₁ x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          connDiffIteratedCommKernelBilin (I := I) g₀ g₁ x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1) := by
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel]

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connDiffAACommBiContrFib_eq_fixedFrame_on_nbhd
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connDiffAACommBiContrFib (I := I) g₀ g₁ y =
      connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel,
    connDiffAACommBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          connDiffIteratedCommKernelBilin (I := I) g₀ g₁ y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnDiffAACommKernel (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnDiffAACommKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameConnDiffAACommKernel (I := I) g₀ g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
theorem connDiffAACommBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffAACommBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    connDiffAACommBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connDiffAACommBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

def ricciArmOrder0AACommCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x))
      contMDiff_toFun := connDiffAACommBiContrFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] theorem ricciArmOrder0AACommCoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffAACommBiContrFib (I := I) g₀ g₁ x)) := rfl


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem connDiffAACommBiContrFib_self (g₀ : SmoothRiemannianMetric I M) (x : M) :
    connDiffAACommBiContrFib (I := I) g₀ g₀ x = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffAACommBiContrFib, connDiffAACommBiContrFibFixedFrame_toModel]
  have hconn : PDE.DeTurck.connDiff (I := I) g₀ g₀ = 0 :=
    PDE.DeTurck.connDiff_self (I := I) g₀
  rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel D
        ![(smoothOrthoFrame (I := I) g₀ x a x : E),
          (smoothOrthoFrame (I := I) g₀ x b x : E)]) *
        connDiffIteratedCommKernelBilin (I := I) g₀ g₀ x
          (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₀ x b x)
          (v 0) (v 1)) = 0 from
    Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
      rw [connDiffAACommKernelBilin_apply]
      simp only [hconn, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero,
        sub_self, mul_zero]))]
  simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]


omit [I.Boundaryless] in
theorem ricciArmOrder0AACommCoeffField_self (g₀ : SmoothRiemannianMetric I M) :
    ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀ g₀ = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmOrder0AACommCoeffField_toSection, connDiffAACommBiContrFib_self]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
