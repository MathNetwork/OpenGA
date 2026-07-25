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
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsMetricPerturbation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsConnDiffCommutator
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsSharpGradientKoszul
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFieldsRicciFold


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

set_option maxHeartbeats 3200000

def ccTensorRank4EvalAtUnitZeroSec (g : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) : Π y : M, Tensor0SSpace 4 I y :=
  fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 4 I y from G.toSection y)
      (unitZeroSec (I := I) (M := M) y)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensorFourUnitValueSection_contMDiff (g : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g 0 4) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) y
        (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g G y)) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 4 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 4 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 4 I y from G.toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    G.toSection.contMDiff (unitZeroSec (I := I) (M := M)).contMDiff

private def refoldKernelArgumentPairEvalCLM (x : M) (v : Fin 2 → E) :
    Tensor0SSpace 2 I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma refoldKernelArgumentPairEvalCLM_apply (x : M) (v : Fin 2 → E)
    (D : Tensor0SSpace 2 I x) :
    refoldKernelArgumentPairEvalCLM (I := I) (M := M) x v D =
      Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

def curvatureRefoldMonomialFrameContraction (Gs : Π b : M, Tensor0SSpace 4 I b)
    (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    (refoldKernelArgumentPairEvalCLM (I := I) (M := M) x
        ![(B a x : E), (B b x : E)]).smulRight
      (tensorLeadingPairSlotEvalCLM (I := I) (M := M) 2 x (B a x) (B b x)
        (tensorRank4PermuteCLM (I := I) (M := M) x σ (Gs x)))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma refoldKernelContractionMonomialFibFixedFrame_apply
    (Gs : Π b : M, Tensor0SSpace 4 I b) (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) :
    curvatureRefoldMonomialFrameContraction (I := I) (M := M) Gs σ B x D =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        curvatureActionMonomialCLM (I := I) (M := M) x
          (Tensor0SSpace.toModel (𝕜 := ℝ) D ![(B a x : E), (B b x : E)]) σ
          (B a x) (B b x) (Gs x) := by
  rw [curvatureRefoldMonomialFrameContraction, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply, refoldKernelArgumentPairEvalCLM_apply,
    curvatureRefoldMonomialFib_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma refoldKernelContractionMonomialFibFixedFrame_toModel
    (Gs : Π b : M, Tensor0SSpace 4 I b) (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (curvatureRefoldMonomialFrameContraction (I := I) (M := M) Gs σ B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) D ![(B a x : E), (B b x : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ) (Gs x)
            (fun i => (Fin.cons ((B a x : E)) (Fin.cons ((B b x : E)) v) : Fin 4 → E)
              (σ i)) := by
  classical
  rw [refoldKernelContractionMonomialFibFixedFrame_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, curvatureRefoldMonomialFib_toModel]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem refoldKernelContractionMonomialFibFixedFrame_apply_section_contMDiff
    (Gs : Π b : M, Tensor0SSpace 4 I b)
    (hGs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) b (Gs b)))
    (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (curvatureRefoldMonomialFrameContraction (I := I) (M := M) Gs σ B x (Y x))) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  set Gσ : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun z : M => Tensor0SSpace 4 I z⟯ :=
    { toFun := fun x : M => tensorRank4PermuteCLM (I := I) (M := M) x σ (Gs x)
      contMDiff_toFun := by
        have h := slotPerm4Fib_apply_section_contMDiff (I := I) (M := M) σ
          ({ toFun := fun x : M => Gs x
             contMDiff_toFun := hGs } :
            Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun z : M => Tensor0SSpace 4 I z⟯)
        exact h }
    with hGσ_def
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          ((refoldKernelArgumentPairEvalCLM (I := I) (M := M) x
              ![(B a x : E), (B b x : E)]).smulRight
            (tensorLeadingPairSlotEvalCLM (I := I) (M := M) 2 x (B a x) (B b x)
              (tensorRank4PermuteCLM (I := I) (M := M) x σ (Gs x))) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (𝕜 := ℝ) (Y x) ![(B a x : E), (B b x : E)]) := by
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
    have hfeed1 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
          (E := fun z : M => Tensor0SSpace 3 I z) x
          (Tensor0SPartialEval.tensor0SPartialEval I M (s := 3)
            (fun z => Gσ z) (fun z => B a z) x)) :=
      Tensor0SPartialEval.contMDiff_tensor0SPartialEval I M (s := 3)
        (fun z => Gσ z) Gσ.contMDiff (fun z => B a z) (hB a)
    set Z3 : Cₛ^∞⟮I; Tensor0SModel 3 ℝ E, fun z : M => Tensor0SSpace 3 I z⟯ :=
      { toFun := fun x : M => Tensor0SPartialEval.tensor0SPartialEval I M (s := 3)
          (fun z => Gσ z) (fun z => B a z) x
        contMDiff_toFun := hfeed1 }
      with hZ3_def
    have hfeed2 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (Tensor0SPartialEval.tensor0SPartialEval I M (s := 2)
            (fun z => Z3 z) (fun z => B b z) x)) :=
      Tensor0SPartialEval.contMDiff_tensor0SPartialEval I M (s := 2)
        (fun z => Z3 z) Z3.contMDiff (fun z => B b z) (hB b)
    have hsmul := ContMDiff.smul_section
      (f := fun x : M => Tensor0SSpace.toModel (𝕜 := ℝ) (Y x) ![(B a x : E), (B b x : E)])
      (s := fun x : M => Tensor0SPartialEval.tensor0SPartialEval I M (s := 2)
        (fun z => Z3 z) (fun z => B b z) x)
      hscalar hfeed2
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M =>
          (refoldKernelArgumentPairEvalCLM (I := I) (M := M) x
              ![(B a x : E), (B b x : E)]).smulRight
            (tensorLeadingPairSlotEvalCLM (I := I) (M := M) 2 x (B a x) (B b x)
              (tensorRank4PermuteCLM (I := I) (M := M) x σ (Gs x))) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [curvatureRefoldMonomialFrameContraction, hStot_def]
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

private def kcInnerPairBilin (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (L X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_smul] }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma kcInnerPairBilin_apply (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    kcInnerPairBilin (I := I) x K L X Y Y' = K X Y * L X Y' := by
  rw [kcInnerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private def kcOuterPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l * K X (chartModelBasis E k)) •
          (ContinuousLinearMap.flip L (chartModelBasis E l))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma kcOuterPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    kcOuterPairBilin (I := I) g x K L X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (chartModelBasis E k) * L X' (chartModelBasis E l)) := by
  rw [kcOuterPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem kc_double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (chartModelBasis E m) (chartModelBasis E k) *
            L (chartModelBasis E n) (chartModelBasis E l))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      kcOuterPairBilin (I := I) g x K L (B a) (B a) := by
    intro a
    rw [kcOuterPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (kcInnerPairBilin (I := I) x K L (B a)) B hB
    simp only [kcInnerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (kcOuterPairBilin (I := I) g x K L) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [kcOuterPairBilin_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem kc_double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * L (C a) (C b) := by
  rw [kc_double_frame_bilin_trace_eq_fixed (I := I) g x K L B hB,
    kc_double_frame_bilin_trace_eq_fixed (I := I) g x K L C hC]

private def kcToModelEvalCLM (s : ℕ) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma kcToModelEvalCLM_apply (s : ℕ) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    kcToModelEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

private def kcPairFeedScalarCLM (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (kcToModelEvalCLM (I := I) (M := M) s x v).comp
        (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x
          ((tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          map_smul] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma kcPairFeedScalarCLM_apply (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) (p q : TangentSpace I x) :
    kcPairFeedScalarCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel (𝕜 := ℝ) G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [kcPairFeedScalarCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, kcToModelEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p) (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := G) (v0 := p) (vs := Fin.cons (q : E) v)]

def curvatureRefoldMonomialOrthonormalFrameBiContraction (g₁ : SmoothRiemannianMetric I M)
    (Gs : Π b : M, Tensor0SSpace 4 I b) (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  curvatureRefoldMonomialFrameContraction (I := I) (M := M) Gs σ
    (smoothOrthoFrame (I := I) g₁ x) x

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem refoldKernelContractionMonomialBiContrFib_eq_fixedFrame_on_nbhd
    (g₁ : SmoothRiemannianMetric I M) (Gs : Π b : M, Tensor0SSpace 4 I b)
    (σ : Equiv.Perm (Fin 4)) (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M) g₁ Gs σ y =
      curvatureRefoldMonomialFrameContraction (I := I) (M := M) Gs σ
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [curvatureRefoldMonomialOrthonormalFrameBiContraction,
    refoldKernelContractionMonomialFibFixedFrame_toModel,
    refoldKernelContractionMonomialFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) D ![(Bf a : E), (Bf b : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ) (Gs y)
            (fun i => (Fin.cons ((Bf a : E)) (Fin.cons ((Bf b : E)) v) : Fin 4 → E)
              (σ i)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        kcPairFeedScalarCLM (I := I) (M := M) 0 y D ![] (Bf a) (Bf b) *
          kcPairFeedScalarCLM (I := I) (M := M) 2 y
            (tensorRank4PermuteCLM (I := I) (M := M) y σ (Gs y)) v (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [kcPairFeedScalarCLM_apply, kcPairFeedScalarCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact kc_double_frame_bilin_trace_indep (I := I) g₁ y
    (kcPairFeedScalarCLM (I := I) (M := M) 0 y D ![])
    (kcPairFeedScalarCLM (I := I) (M := M) 2 y (tensorRank4PermuteCLM (I := I) (M := M) y σ (Gs y)) v)
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem refoldKernelContractionMonomialBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (Gs : Π b : M, Tensor0SSpace 4 I b)
    (hGs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) b (Gs b)))
    (σ : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M)
          g₁ Gs σ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (curvatureRefoldMonomialFrameContraction (I := I) (M := M)
          Gs σ (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ := by
    have h_glob : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
          (E := fun z : M => TensorRSSpace 2 2 I z) x
          (TensorRSSpace.ofCLM (curvatureRefoldMonomialFrameContraction (I := I) (M := M)
            Gs σ (smoothOrthoFrame (I := I) g₁ x₀) x))) := by
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
        (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
        (φ := fun x : M => curvatureRefoldMonomialFrameContraction (I := I) (M := M)
          Gs σ (smoothOrthoFrame (I := I) g₁ x₀) x)
      intro Y
      exact refoldKernelContractionMonomialFibFixedFrame_apply_section_contMDiff
        (I := I) (M := M) Gs hGs σ (smoothOrthoFrame (I := I) g₁ x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) Y
    exact h_glob x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (refoldKernelContractionMonomialBiContrFib_eq_fixedFrame_on_nbhd (I := I) (M := M)
        g₁ Gs σ x₀ hy))

def refoldKernelContractionMonomialField (g₀ g₁ : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g₀ 0 4) (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M)
            g₁ (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ x))
      contMDiff_toFun := refoldKernelContractionMonomialBiContrFib_contMDiff (I := I) (M := M)
        g₁ (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G)
        (ccTensorFourUnitValueSection_contMDiff (I := I) (M := M) g₀ G) σ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem refoldKernelContractionMonomialField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M)
          g₁ (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G) σ x)) := rfl

def refoldKernelContractionField (g₀ g₁ : SmoothRiemannianMetric I M)
    (G : SmoothCcTensor g₀ 0 4) (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g₀ 2 2 :=
  (1 / 2 : ℝ) •
    (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₁
      + refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₂
      - refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₃
      - refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₄)


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem refoldKernelContractionField_toSection_eq_kernelFib_sum
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (refoldKernelContractionField (I := I) (M := M)
          g₀ g₁ G σ₁ σ₂ σ₃ σ₄).toSection x) D =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        curvatureActionKernelCLM (I := I) (M := M) x
          (Tensor0SSpace.toModel (𝕜 := ℝ) D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)])
          σ₁ σ₂ σ₃ σ₄
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
          (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G x) := by
  classical
  rw [refoldKernelContractionField, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_add, Pi.add_apply]
  set Gs : Π b : M, Tensor0SSpace 4 I b :=
    ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ G with hGs_def
  set F : Equiv.Perm (Fin 4) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Tensor0SSpace 2 I x :=
    fun σ a b => curvatureActionMonomialCLM (I := I) (M := M) x
      (Tensor0SSpace.toModel (𝕜 := ℝ) D
        ![(smoothOrthoFrame (I := I) g₁ x a x : E),
          (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (Gs x) with hF_def
  have happly : ∀ σ : Equiv.Perm (Fin 4),
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ).toSection x) D =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ a b := by
    intro σ
    exact refoldKernelContractionMonomialFibFixedFrame_apply (I := I) (M := M) Gs σ
      (smoothOrthoFrame (I := I) g₁ x) x D
  change (1 / 2 : ℝ) •
      (((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₁).toSection x)
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₂).toSection x)
        - (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₃).toSection x)
        - (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ₄).toSection x))
        D) = _
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, happly σ₁, happly σ₂, happly σ₃, happly σ₄]
  have hker : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      curvatureActionKernelCLM (I := I) (M := M) x
        (Tensor0SSpace.toModel (𝕜 := ℝ) D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)])
        σ₁ σ₂ σ₃ σ₄
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (Gs x)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) • (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hF_def]
    rw [show curvatureActionKernelCLM (I := I) (M := M) x
        (Tensor0SSpace.toModel (𝕜 := ℝ) D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)])
        σ₁ σ₂ σ₃ σ₄
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) =
        (1 / 2 : ℝ) •
          (curvatureActionMonomialCLM (I := I) (M := M) x
              (Tensor0SSpace.toModel (𝕜 := ℝ) D
                ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                  (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₁
              (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            + curvatureActionMonomialCLM (I := I) (M := M) x
                (Tensor0SSpace.toModel (𝕜 := ℝ) D
                  ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                    (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₂
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            - curvatureActionMonomialCLM (I := I) (M := M) x
                (Tensor0SSpace.toModel (𝕜 := ℝ) D
                  ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                    (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₃
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            - curvatureActionMonomialCLM (I := I) (M := M) x
                (Tensor0SSpace.toModel (𝕜 := ℝ) D
                  ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                    (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ₄
                (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x))
        from rfl]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [hker]
  have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) • (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
      (1 / 2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.smul_sum]
  have hdist : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₁ a b)
        + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₂ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₃ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₄ a b) := by
    have hinner : ∀ a : Fin (Module.finrank ℝ E),
        (∑ b : Fin (Module.finrank ℝ E),
          (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
        (∑ b : Fin (Module.finrank ℝ E), F σ₁ a b)
          + (∑ b : Fin (Module.finrank ℝ E), F σ₂ a b)
          - (∑ b : Fin (Module.finrank ℝ E), F σ₃ a b)
          - (∑ b : Fin (Module.finrank ℝ E), F σ₄ a b) := by
      intro a
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsplit, hdist]

omit [I.Boundaryless] [BoundarylessManifold I M] in
theorem refoldKernelContractionField_zero_argument (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 4) σ₁ σ₂ σ₃ σ₄ = 0 := by
  classical
  have hmono : ∀ σ : Equiv.Perm (Fin 4),
      refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
        (0 : SmoothCcTensor g₀ 0 4) σ = 0 := by
    intro σ
    refine SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    rw [refoldKernelContractionMonomialField_toSection]
    have hGs : ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀
        (0 : SmoothCcTensor g₀ 0 4) x = 0 := by
      rw [ccTensorRank4EvalAtUnitZeroSec]
      rw [show ((0 : SmoothCcTensor g₀ 0 4).toSection x) = 0 from by
        rw [show (0 : SmoothCcTensor g₀ 0 4) =
            (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 4) from (zero_smul ℝ _).symm,
          SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
          zero_smul]]
      rfl
    have hzero : curvatureRefoldMonomialOrthonormalFrameBiContraction (I := I) (M := M) g₁
        (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀ (0 : SmoothCcTensor g₀ 0 4))
        σ x = 0 := by
      apply ContinuousLinearMap.ext
      intro D
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      rw [curvatureRefoldMonomialOrthonormalFrameBiContraction,
        refoldKernelContractionMonomialFibFixedFrame_toModel]
      rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel (𝕜 := ℝ) D
              ![(smoothOrthoFrame (I := I) g₁ x a x : E),
                (smoothOrthoFrame (I := I) g₁ x b x : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ)
              (ccTensorRank4EvalAtUnitZeroSec (I := I) (M := M) g₀
                (0 : SmoothCcTensor g₀ 0 4) x)
              (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
                (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) : Fin 4 → E)
                (σ i))) = 0 from
        Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
          rw [hGs, Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply,
            mul_zero]))]
      simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
        ContinuousMultilinearMap.zero_apply]
    rw [hzero]
    rfl
  rw [refoldKernelContractionField, hmono σ₁, hmono σ₂, hmono σ₃, hmono σ₄]
  rw [show (0 : SmoothCcTensor g₀ 2 2) + 0 - 0 - 0 = 0 from by abel, smul_zero]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem foldIteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma foldIteratedCovGrad_zero_arg (g₀ : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g₀ r s j (0 : SmoothCcTensor g₀ r s) = 0 := by
  rw [show (0 : SmoothCcTensor g₀ r s) = (0 : ℝ) • (0 : SmoothCcTensor g₀ r s) from
      (zero_smul ℝ _).symm,
    foldIteratedCovGrad_smul_real, zero_smul]

omit [BoundarylessManifold I M] in
theorem refoldKernelContractionField_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionField (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2 (0 : SmoothCcTensor g₀ 0 2)) σ₁ σ₂ σ₃ σ₄ = 0 := by
  rw [foldIteratedCovGrad_zero_arg (I := I) (M := M) g₀ 0 2 2,
    refoldKernelContractionField_zero_argument]

omit [BoundarylessManifold I M] in
theorem refoldKernelContractionField_self (g₀ : SmoothRiemannianMetric I M)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionField (I := I) (M := M) g₀ g₀
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (metricDifferenceCcTensor (I := I) (M := M) g₀ g₀)) σ₁ σ₂ σ₃ σ₄ = 0 := by
  rw [metricDifferenceCcTensor_self, refoldKernelContractionField_zero_weight]


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem appCc_refoldKernelContractionField
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g₀ 0 2) :
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (refoldKernelContractionField (I := I) (M := M) g₀ g₁ G σ₁ σ₂ σ₃ σ₄) W =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (curvatureActionKernelCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
          σ₁ σ₂ σ₃ σ₄) G := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  rw [unitModel, unitModel]
  refine congrArg Tensor0SSpace.toModel ?_
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (refoldKernelContractionField (I := I) (M := M) g₀ g₁ G σ₁ σ₂ σ₃ σ₄)
        W).toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (refoldKernelContractionField (I := I) (M := M) g₀ g₁ G σ₁ σ₂ σ₃ σ₄).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (operatorFieldApply (I := I) (M := M) g₀ 4 2
        (curvatureActionKernelCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
          σ₁ σ₂ σ₃ σ₄) G).toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (curvatureActionKernelCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W)
          σ₁ σ₂ σ₃ σ₄).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from G.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [refoldKernelContractionField_toSection_eq_kernelFib_sum (I := I) (M := M)
    g₀ g₁ G σ₁ σ₂ σ₃ σ₄ x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))]
  rw [curvatureRefoldKernelCoeffField_toSection_eq_kernelFib_sum (I := I) (M := M)
    g₀ g₁ (ccTensorUnitValueSection (I := I) (M := M) g₀ W)
    (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ W) σ₁ σ₂ σ₃ σ₄ x]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
