import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Tensor.Multilinear.ModelProductContinuousBilinear


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

def permOfImages {n : ℕ} (f g : Fin n → Fin n)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Equiv.Perm (Fin n) :=
  ⟨f, g, h₁, h₂⟩

def perm2_10 : Equiv.Perm (Fin 2) :=
  permOfImages ![1, 0] ![1, 0] (by decide) (by decide)

def perm3_102 : Equiv.Perm (Fin 3) :=
  permOfImages ![1, 0, 2] ![1, 0, 2] (by decide) (by decide)

def perm3_120 : Equiv.Perm (Fin 3) :=
  permOfImages ![1, 2, 0] ![2, 0, 1] (by decide) (by decide)

def perm4_0312 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 3, 1, 2] ![0, 2, 3, 1] (by decide) (by decide)

def perm4_0213 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 2, 1, 3] ![0, 2, 1, 3] (by decide) (by decide)

def perm4_2301 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide)

def perm4_1302 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 3, 0, 2] ![2, 0, 3, 1] (by decide) (by decide)

def perm4_1203 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 2, 0, 3] ![2, 0, 1, 3] (by decide) (by decide)

def perm4_3012 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 0, 1, 2] ![1, 2, 3, 0] (by decide) (by decide)

def perm4_2013 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 0, 1, 3] ![1, 2, 0, 3] (by decide) (by decide)

def perm4_3201 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 2, 0, 1] ![2, 3, 1, 0] (by decide) (by decide)

def perm4_3102 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 1, 0, 2] ![2, 1, 3, 0] (by decide) (by decide)

def perm4_2103 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 1, 0, 3] ![2, 1, 0, 3] (by decide) (by decide)

def perm4_0231 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 2, 3, 1] ![0, 3, 1, 2] (by decide) (by decide)

def perm4_0321 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 3, 2, 1] ![0, 3, 2, 1] (by decide) (by decide)

noncomputable def slotPermCLM {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x : M) :
    Tensor0SBundle.Tensor0SSpace d I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          ρ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) d x).toContinuousLinearMap)


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem slotPermCLM_apply {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace d I x) :
    slotPermCLM (I := I) ρ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [slotPermCLM]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def tensorProdWithCLM (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) :
    Tensor0SBundle.Tensor0SSpace k I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (m + k) I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I)
      (m + k) x).symm.toContinuousLinearMap.comp
    ((Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        (Tensor0SBundle.Tensor0SSpace.toModel P)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) k x).toContinuousLinearMap)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorProdWithCLM_apply (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) (Q : Tensor0SBundle.Tensor0SSpace k I x) :
    tensorProdWithCLM (I := I) m k x P Q =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
          (Tensor0SBundle.Tensor0SSpace.toModel P)
          (Tensor0SBundle.Tensor0SSpace.toModel Q)) := by
  rw [tensorProdWithCLM]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Bundle.continuousMultilinearMap.modelProductL_apply]
  rfl

noncomputable def tensorProdPairCLM (m k : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace m I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace k I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (m + k) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.Tensor0SSpace m I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun P => tensorProdWithCLM (I := I) m k x P
      map_add' := fun P₁ P₂ => by
        apply ContinuousLinearMap.ext
        intro Q
        have hsplit : Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
            (Tensor0SBundle.Tensor0SSpace.toModel P₁ + Tensor0SBundle.Tensor0SSpace.toModel P₂)
            (Tensor0SBundle.Tensor0SSpace.toModel Q) =
          Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P₁) (Tensor0SBundle.Tensor0SSpace.toModel Q)
            + Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P₂)
              (Tensor0SBundle.Tensor0SSpace.toModel Q) := by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.add_apply, add_mul]
        rw [ContinuousLinearMap.add_apply, tensorProdWithCLM_apply, tensorProdWithCLM_apply,
          tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_add, hsplit]
        exact map_add
          ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (m + k) x).symm) _ _
      map_smul' := fun c P => by
        apply ContinuousLinearMap.ext
        intro Q
        have hsplit : Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
            (c • Tensor0SBundle.Tensor0SSpace.toModel P)
            (Tensor0SBundle.Tensor0SSpace.toModel Q) =
          c • Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P)
              (Tensor0SBundle.Tensor0SSpace.toModel Q) := by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
            ContinuousMultilinearMap.smul_apply, smul_eq_mul]
          ring
        rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, tensorProdWithCLM_apply,
          tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul, hsplit]
        exact map_smul
          ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) (m + k) x).symm) c _ }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem tensorProdPairCLM_apply (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) :
    tensorProdPairCLM (I := I) m k x P = tensorProdWithCLM (I := I) m k x P := rfl

noncomputable def contractUnitCLM (n : ℕ) (x : M) :
    Tensor0SBundle.TensorRSSpace 1 (n + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace n I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) n x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply ℝ (Tensor0SBundle.Tensor0SModel n ℝ E)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))).comp
      ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 n x).toContinuousLinearMap.comp
        (show Tensor0SBundle.TensorRSSpace 1 (n + 1) I x →L[ℝ]
            Tensor0SBundle.TensorRSSpace 0 n I x from
          Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 n x)))

noncomputable def connContrCLM (m k : ℕ) (x : M)
    (B : Tensor0SBundle.TensorRSSpace 1 (k + 1) I x) :
    Tensor0SBundle.Tensor0SSpace (m + 1) I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace (m + 1 + k) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.Tensor0SSpace (m + 1) I x) := inferInstance
  (contractUnitCLM (I := I) (m + 1 + k) x).comp
    (LinearMap.toContinuousLinearMap
      { toFun := fun D =>
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)
        map_add' := fun D₁ D₂ => by
          simp only [← tensorProdPairCLM_apply]
          rw [map_add, ContinuousLinearMap.add_comp]
        map_smul' := fun c D => by
          simp only [← tensorProdPairCLM_apply, RingHom.id_apply]
          rw [map_smul, ContinuousLinearMap.smul_comp] })

noncomputable def linearizedRicciConnDiffOrder1CLM (x : M)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  -((slotPermCLM (I := I) perm4_0312 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_102 x))
      + (slotPermCLM (I := I) perm4_0213 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_120 x))
      + (slotPermCLM (I := I) perm4_2301 x).comp (connContrCLM (I := I) 2 1 x A)
      + (slotPermCLM (I := I) perm4_1302 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_102 x))
      + (slotPermCLM (I := I) perm4_1203 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3_120 x)))

noncomputable def linearizedRicciConnDiffOrder0CLM (x : M)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x)
    (DA : Tensor0SBundle.TensorRSSpace 1 3 I x) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  ((slotPermCLM (I := I) perm4_3201 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_102 x).comp (connContrCLM (I := I) 1 1 x A)))
      + (slotPermCLM (I := I) perm4_2301 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_102 x).comp
            ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm2_10 x))))
      + (slotPermCLM (I := I) perm4_3102 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_120 x).comp (connContrCLM (I := I) 1 1 x A)))
      + (slotPermCLM (I := I) perm4_1302 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm2_10 x)))
      + (slotPermCLM (I := I) perm4_1203 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (connContrCLM (I := I) 1 1 x A))
      + (slotPermCLM (I := I) perm4_2103 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3_120 x).comp
            ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm2_10 x)))))
    - (slotPermCLM (I := I) perm4_3012 x).comp (connContrCLM (I := I) 1 2 x DA)
    - (slotPermCLM (I := I) perm4_2013 x).comp
      ((connContrCLM (I := I) 1 2 x DA).comp (slotPermCLM (I := I) perm2_10 x))

noncomputable def ricciCometricFourTraceCLM (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ((1 : ℝ) / 2) •
    ((cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm4_0231 x)
      + (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm4_0321 x)
      - cometricDoubleTraceFib (I := I) g₁ 2 x
      - (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm4_2301 x))

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
