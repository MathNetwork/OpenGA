import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.VectorBundle.Basic
import Verified.ClosedSurface_DifferentialGeometry_Bundle_Section
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

noncomputable def modelInteriorProduct (s : ℕ) (v : E) :
    Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E :=
  (ContinuousLinearMap.apply 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v).comp
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def modelInteriorBilinear (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (s : ℕ) :
    E →L[𝕜] (Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def modelTensorWithCovectorFirst (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          add_apply, mul_add]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

noncomputable def modelTensorWithCovectorFirstBilinear (r : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        LinearMap.toContinuousLinearMap
          { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
            map_add' := fun β₁ β₂ => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                add_apply, mul_add]
            map_smul' := fun c β => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                smul_apply, smul_eq_mul, RingHom.id_apply]
              ring }
      map_add' := fun α₁ α₂ => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          add_apply, add_apply, add_mul]
      map_smul' := fun c α => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          smul_apply, smul_apply,
          smul_eq_mul, RingHom.id_apply]
        ring }

theorem model_tensorWithCovector_first_bilinear_apply (r : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (β : Tensor0SModel r 𝕜 E) :
    modelTensorWithCovectorFirstBilinear (𝕜 := 𝕜) (E := E) r α β =
      modelTensorWithCovectorFirst r α β := rfl

noncomputable def modelContractCovariantBilinear (r s : ℕ) :
    E →L[𝕜] (TensorRSModel r (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E)
      (Tensor0SModel (s + 1) 𝕜 E)
      (Tensor0SModel s 𝕜 E)).comp
    (modelInteriorBilinear 𝕜 E s)

omit [CompleteSpace 𝕜] in
theorem model_contract_covariant_bilinear_apply (r s : ℕ) (v : E)
    (T : TensorRSModel r (s + 1) 𝕜 E) :
    modelContractCovariantBilinear (𝕜 := 𝕜) (E := E) r s v T =
      (modelInteriorProduct s v).comp T := rfl

noncomputable def modelContractContravariantFirstBilinear (r s : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (TensorRSModel (1 + r) s 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E) (Tensor0SModel (1 + r) 𝕜 E) (Tensor0SModel s 𝕜 E)).flip.comp
    (modelTensorWithCovectorFirstBilinear (𝕜 := 𝕜) (E := E) r)

theorem model_contract_contravariant_first_bilinear_apply (r s : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (T : TensorRSModel (1 + r) s 𝕜 E) :
    modelContractContravariantFirstBilinear (𝕜 := 𝕜) (E := E) r s α T =
      T.comp (modelTensorWithCovectorFirst r α) := rfl

section FieldContraction

variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]

noncomputable def modelCovectorOfCLM :
    (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel 1 𝕜 E :=
  (continuousMultilinearCurryFin1 𝕜 E 𝕜).symm.toContinuousLinearMap

noncomputable def modelContractTrace (r s : ℕ) :
    TensorRSModel (1 + r) (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E :=
  let d := Module.finrank 𝕜 E
  let B : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) := B.cDualBasis
  ∑ i : Fin d,
    (modelContractCovariantBilinear (𝕜 := 𝕜) (E := E) r s (B i)).comp
      (modelContractContravariantFirstBilinear
        (𝕜 := 𝕜) (E := E) r (s + 1)
        (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) (b i)))

theorem model_contract_trace_apply (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    modelContractTrace (𝕜 := 𝕜) (E := E) r s T =
      ∑ i : Fin (Module.finrank 𝕜 E),
        (modelContractCovariantBilinear
          (𝕜 := 𝕜) (E := E) r s
          ((Module.finBasis 𝕜 E) i))
          ((modelContractContravariantFirstBilinear
            (𝕜 := 𝕜) (E := E) r (s + 1)
            (modelCovectorOfCLM (𝕜 := 𝕜) (E := E)
              ((Module.finBasis 𝕜 E).cDualBasis i))) T) := by
  simp [modelContractTrace]

noncomputable def contractTrace (r s : ℕ) (x : M) :
    TensorRSSpace (1 + r) (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((modelContractTrace (𝕜 := 𝕜) (E := E) r s).comp
      (tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) x).toContinuousLinearMap)

omit [IsManifold I ω M] in
theorem contract_trace_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T =
      (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm
        (modelContractTrace (𝕜 := 𝕜) (E := E) r s
          (tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) x T)) := by
  rfl

 theorem _root_.DifferentialGeometry.Tensor0SBundle.trace_bilinear_change_frame_coord_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F ((LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i))
          ((Module.finBasis 𝕜 E) i) := by
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  change (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
      (K (b i))) =
    ∑ i : Fin d, F (LinearMap.toContinuousLinearMap (b.coord i)) (b i)
  have h_cov : ∀ j : Fin d,
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) z
          = ∑ i : Fin d, b.coord j (K (b i)) * b.coord i (L z) := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Fin d, b.coord i (L z) • K (b i)) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j (K (∑ i : Fin d, b.coord i (L z) • b i)) := by
              congr 1
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
      _ = b.coord j (K (L z)) := by
              rw [show (∑ i : Fin d, b.coord i (L z) • b i) = L z from b.sum_repr (L z)]
      _ = b.coord j z := by rw [hKL z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i)))
        = ∑ i : Fin d, ∑ j : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i))
                = F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
                    (∑ j : Fin d, b.coord j (K (b i)) • b j) := by
                  rw [show (∑ j : Fin d, b.coord j (K (b i)) • b j) = K (b i) from
                    b.sum_repr (K (b i))]
            _ = ∑ j : Fin d, (b.coord j (K (b i))) •
                    F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin d, ∑ i : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin d, F
            (∑ i : Fin d, (b.coord j (K (b i))) •
              ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

 theorem _root_.DifferentialGeometry.Tensor0SBundle.trace_bilinear_change_frame_cdual_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
  simpa [Module.Basis.cDualBasis, Module.Basis.coe_dualBasis]
    using _root_.DifferentialGeometry.Tensor0SBundle.trace_bilinear_change_frame_coord_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (𝕜 := 𝕜) (E := E) L K hKL F

 noncomputable def _root_.DifferentialGeometry.Tensor0SBundle.model_trace_pairing_first_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E) :
    (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
  let covToTensor : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
    ((ContinuousLinearMap.apply 𝕜 (Tensor0SModel (1 + r) 𝕜 E) β).comp
      ((modelTensorWithCovectorFirstBilinear (𝕜 := 𝕜) (E := E) r).comp
        (modelCovectorOfCLM (𝕜 := 𝕜) (E := E))))
  let covToOutput : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (s + 1) 𝕜 E :=
    T.comp covToTensor
  let evalTail : Tensor0SModel s 𝕜 E →L[𝕜] 𝕜 :=
    ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin s => E) 𝕜 tail
  let curry :
      Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] Tensor0SModel s 𝕜 E :=
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
  let outputToPair : Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] 𝕜 :=
    ((ContinuousLinearMap.compL 𝕜 E (Tensor0SModel s 𝕜 E) 𝕜) evalTail).comp curry
  outputToPair.comp covToOutput

 theorem _root_.DifferentialGeometry.Tensor0SBundle.model_trace_pairing_first_apply_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E)
    (α : E →L[𝕜] 𝕜) (X : E) :
    _root_.DifferentialGeometry.Tensor0SBundle.model_trace_pairing_first_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (𝕜 := 𝕜) (E := E) r s T β tail α X =
      (modelInteriorProduct s X
        (T (modelTensorWithCovectorFirst r
          (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) α) β))) tail := by
  simp [_root_.DifferentialGeometry.Tensor0SBundle.model_trace_pairing_first_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract, model_tensorWithCovector_first_bilinear_apply,
    modelInteriorProduct]

noncomputable def modelCovariantChange (k : ℕ) (L : E →L[𝕜] E) :
    Tensor0SModel k 𝕜 E →L[𝕜] Tensor0SModel k 𝕜 E :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => L)

omit [CompleteSpace 𝕜] in
@[simp]
theorem model_covariantChange_apply (k : ℕ) (L : E →L[𝕜] E)
    (T : Tensor0SModel k 𝕜 E) (v : Fin k → E) :
    modelCovariantChange (𝕜 := 𝕜) (E := E) k L T v =
      T (fun i => L (v i)) := by
  rfl

omit [CompleteSpace 𝕜] in
 theorem _root_.DifferentialGeometry.Tensor0SBundle.model_interior_product_covariantChange_apply_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (s : ℕ)
    (L : E →L[𝕜] E) (X : E) (U : Tensor0SModel (s + 1) 𝕜 E)
    (v : Fin s → E) :
    (modelInteriorProduct s X
      (modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)) v =
    (modelInteriorProduct s (L X) U) (fun i => L (v i)) := by
  change (modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)
      (Fin.cons X v) =
    U (Fin.cons (L X) (fun i => L (v i)))
  rw [model_covariantChange_apply]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

 theorem _root_.DifferentialGeometry.Tensor0SBundle.model_covariantChange_tensorWithCovector_first_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (r : ℕ)
    (L : E →L[𝕜] E) (α : E →L[𝕜] 𝕜) (β : Tensor0SModel r 𝕜 E) :
    modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) L
      (modelTensorWithCovectorFirst r (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) α) β) =
    modelTensorWithCovectorFirst r
      (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (modelCovariantChange (𝕜 := 𝕜) (E := E) r L β) := by
  refine ContinuousMultilinearMap.ext fun w => ?_
  change (Bundle.continuousMultilinearMap.modelProduct 1 r
      (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) α) β)
      (fun i => L (w i)) =
    (Bundle.continuousMultilinearMap.modelProduct 1 r
      (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (modelCovariantChange (𝕜 := 𝕜) (E := E) r L β)) w
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1

theorem model_contract_trace_naturality
    (r s : ℕ) (L Linv : E →L[𝕜] E)
    (hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    modelContractTrace (𝕜 := 𝕜) (E := E) r s
      ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (T.comp (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv))) =
    (modelCovariantChange (𝕜 := 𝕜) (E := E) s L).comp
      ((modelContractTrace (𝕜 := 𝕜) (E := E) r s T).comp
        (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
  ext β v
  let β' : Tensor0SModel r 𝕜 E :=
    modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv β
  let tail : Fin s → E := fun i => L (v i)
  let F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
    _root_.DifferentialGeometry.Tensor0SBundle.model_trace_pairing_first_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (𝕜 := 𝕜) (E := E) r s T β' tail
  have hKL : ∀ z : E, L (Linv z) = z := by
    intro z
    have h := congrArg (fun f : E →L[𝕜] E => f z) hL
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    ((modelContractTrace (𝕜 := 𝕜) (E := E) r s
        ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
          (T.comp (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)))) β) v
        =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
          (L ((Module.finBasis 𝕜 E) i)) := by
          rw [model_contract_trace_apply]
          rw [sum_apply]
          rw [sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_contract_covariant_bilinear_apply]
          rw [model_contract_contravariant_first_bilinear_apply]
          change (modelInteriorProduct s ((Module.finBasis 𝕜 E) i)
              ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
                (T ((modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)
                  (modelTensorWithCovectorFirst r
                    (modelCovectorOfCLM (𝕜 := 𝕜) (E := E)
                      ((Module.finBasis 𝕜 E).cDualBasis i)) β))))) v =
            F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
              (L ((Module.finBasis 𝕜 E) i))
          rw [_root_.DifferentialGeometry.Tensor0SBundle.model_interior_product_covariantChange_apply_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract]
          rw [_root_.DifferentialGeometry.Tensor0SBundle.model_covariantChange_tensorWithCovector_first_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract]
          rw [_root_.DifferentialGeometry.Tensor0SBundle.model_trace_pairing_first_apply_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract]
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
          exact _root_.DifferentialGeometry.Tensor0SBundle.trace_bilinear_change_frame_cdual_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract (𝕜 := 𝕜) (E := E)
            (L := Linv) (K := L) hKL F
    _ =
      (((modelCovariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((modelContractTrace (𝕜 := 𝕜) (E := E) r s T).comp
          (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv))) β) v := by
          change ∑ i : Fin (Module.finrank 𝕜 E),
              F ((Module.finBasis 𝕜 E).cDualBasis i)
                ((Module.finBasis 𝕜 E) i) =
            (modelCovariantChange (𝕜 := 𝕜) (E := E) s L
              ((modelContractTrace (𝕜 := 𝕜) (E := E) r s T) β')) v
          rw [model_covariantChange_apply]
          rw [model_contract_trace_apply]
          rw [sum_apply]
          rw [sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [_root_.DifferentialGeometry.Tensor0SBundle.model_trace_pairing_first_apply_closedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract]
          rw [model_contract_covariant_bilinear_apply]
          rw [model_contract_contravariant_first_bilinear_apply]
          rfl

omit [IsManifold I ω M] in
theorem contract_trace_trivialization_eq
    {r s : ℕ} {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    (trivializationAt (TensorRSModel r s 𝕜 E)
      (TensorRSSpace r s I) x₀
      ⟨x, contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
    modelContractTrace (𝕜 := 𝕜) (E := E) r s
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (TensorRSSpace (1 + r) (s + 1) I) x₀
        ⟨x, T⟩).2) := by
  let L : E →L[𝕜] E := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x
  let Linv : E →L[𝕜] E :=
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
  let Tx : TensorRSModel (1 + r) (s + 1) 𝕜 E :=
    tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) x T
  have hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx z
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SSpace k I x) (v : Fin k → E),
      (trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).continuousLinearMapAt 𝕜 x U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply]
    rw [show ⇑((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel k 𝕜 E)
          (Tensor0SSpace k I) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SModel k 𝕜 E) (u : Fin k → E),
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).symmL 𝕜 x U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ z : E, L (Linv z) = z := by
      intro z
      have h := congrArg (fun f : E →L[𝕜] E => f z) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i
      exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).symmL 𝕜 x U) u
          = ((trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).symmL 𝕜 x U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SModel k 𝕜 E)
            (Tensor0SSpace k I) x₀).continuousLinearMapAt 𝕜 x
            ((trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).symmL 𝕜 x U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).continuousLinearMapAt_symmL
              (R := 𝕜) hx]
  have h_input :
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (TensorRSSpace (1 + r) (s + 1) I) x₀
        ⟨x, T⟩).2) =
      (modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (Tx.comp (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (Tensor0SSpace (s + 1) I) x₀).continuousLinearMapAt 𝕜 x
        (T ((trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (Tensor0SSpace (1 + r) I) x₀).symmL 𝕜 x β)) v =
      ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
        (Tx ((modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (Tensor0SSpace (1 + r) I) x₀).symmL 𝕜 x β =
          (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      exact h_symmL (1 + r) β u
    rw [hβ]
    rfl
  have h_output :
      (trivializationAt (TensorRSModel r s 𝕜 E)
        (TensorRSSpace r s I) x₀
        ⟨x, contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
      (modelCovariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((modelContractTrace (𝕜 := 𝕜) (E := E) r s Tx).comp
          (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel s 𝕜 E)
        (Tensor0SSpace s I) x₀).continuousLinearMapAt 𝕜 x
        ((contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T)
          ((trivializationAt (Tensor0SModel r 𝕜 E)
            (Tensor0SSpace r I) x₀).symmL 𝕜 x β)) v =
      ((modelCovariantChange (𝕜 := 𝕜) (E := E) s L)
        ((modelContractTrace (𝕜 := 𝕜) (E := E) r s Tx)
          ((modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    rw [contract_trace_apply]
    have hβ :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (Tensor0SSpace r I) x₀).symmL 𝕜 x β =
          (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      exact h_symmL r β u
    rw [hβ]
    rfl
  rw [h_input, h_output]
  exact (model_contract_trace_naturality (𝕜 := 𝕜) (E := E)
    r s L Linv hL Tx).symm

noncomputable def contractTensorRSFieldFun (r s : ℕ)
    (T : (x : M) → TensorRSSpace (1 + r) (s + 1) I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contractTrace r s x (T x)

noncomputable def contractTensorRSField (r s : ℕ)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
      (1 + r) (s + 1)) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨contractTensorRSFieldFun r s (fun x => T x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have hTrace :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => modelContractTrace (𝕜 := 𝕜) (E := E) r s
          ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
            (fun x => TensorRSSpace (1 + r) (s + 1) I x) x₀ ⟨x, T x⟩).2)) x₀ :=
    (modelContractTrace (𝕜 := 𝕜) (E := E) r s).contMDiffAt.comp x₀ hT
  refine hTrace.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  exact contract_trace_trivialization_eq
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) (x₀ := x₀) (x := x) hx (T x)

end FieldContraction

end

end Tensor0SBundle

end DifferentialGeometry
