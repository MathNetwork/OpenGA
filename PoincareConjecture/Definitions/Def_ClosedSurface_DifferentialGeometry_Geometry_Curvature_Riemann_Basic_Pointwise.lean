import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_PartialMfderiv_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_Section
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Basic
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Curvature_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_CotangentRiemannian
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Auxiliary_PredualBasis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_BundleSmoothEvaluation
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_CotangentRiemannian
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_Contract
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_LocalFrameRegularity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Tangent
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_TangentMetric
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
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
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian

open DifferentialGeometry.Geometry.Curvature

noncomputable section

set_option autoImplicit false

open Bundle DifferentialGeometry.Tensor0SBundle

open scoped BigOperators Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

variable {H : Type _} [TopologicalSpace H]

variable {I : ModelWithCorners ℝ E H}

variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

omit [FiniteDimensional ℝ E] in
 theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_add_first_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X₁ X₂ Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x (X₁ + X₂))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X₁)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X₂)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let X₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X₁
  let X₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X₂
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX₁ : MDiffAt (T% X₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x X₁
  have hX₂ : MDiffAt (T% X₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x X₂
  have hZX₁ : MDiffAt (T% (fun p : M => (cov Zc p) (X₁c p))) x := by
    simpa [X₁c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X₁
  have hZX₂ : MDiffAt (T% (fun p : M => (cov Zc p) (X₂c p))) x := by
    simpa [X₂c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X₂
  have hmid :
      (fun p : M => (cov Zc p) ((X₁c + X₂c) p)) =
        (fun p : M => (cov Zc p) (X₁c p)) +
          (fun p : M => (cov Zc p) (X₂c p)) := by
    funext p
    simp [Pi.add_apply, map_add]
  rw [tangentConstAt_add]
  change
    riemannCurvatureAux cov (X₁c + X₂c) Yc Zc x =
      riemannCurvatureAux cov X₁c Yc Zc x +
        riemannCurvatureAux cov X₂c Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.add hZX₁ hZX₂]
  rw [VectorField.mlieBracket_add_left (I := I) hX₁ hX₂]
  simp [Pi.add_apply, map_add]
  module

omit [FiniteDimensional ℝ E] in
 theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_smul_first_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x (a • X))
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hX : MDiffAt (T% Xc) x := mdifferentiableAt_tangentConstAt_self (I := I) x X
  have hZX : MDiffAt (T% (fun p : M => (cov Zc p) (Xc p))) x := by
    simpa [Xc, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X
  have hmid :
      (fun p : M => (cov Zc p) ((a • Xc) p)) =
        a • (fun p : M => (cov Zc p) (Xc p)) := by
    funext p
    simp [Pi.smul_apply, map_smul]
  rw [tangentConstAt_smul]
  change
    riemannCurvatureAux cov (a • Xc) Yc Zc x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZX]
  rw [VectorField.mlieBracket_const_smul_left (I := I) (c := a) hX]
  simp [Pi.smul_apply, map_smul]
  module

omit [FiniteDimensional ℝ E] in
 theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_add_second_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y₁ Y₂ Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (Y₁ + Y₂))
        (tangentConstAt (I := I) x Z) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₁)
          (tangentConstAt (I := I) x Z) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y₂)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Y₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y₁
  let Y₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y₂
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hY₁ : MDiffAt (T% Y₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y₁
  have hY₂ : MDiffAt (T% Y₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y₂
  have hZY₁ : MDiffAt (T% (fun p : M => (cov Zc p) (Y₁c p))) x := by
    simpa [Y₁c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y₁
  have hZY₂ : MDiffAt (T% (fun p : M => (cov Zc p) (Y₂c p))) x := by
    simpa [Y₂c, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y₂
  have hmid :
      (fun p : M => (cov Zc p) ((Y₁c + Y₂c) p)) =
        (fun p : M => (cov Zc p) (Y₁c p)) +
          (fun p : M => (cov Zc p) (Y₂c p)) := by
    funext p
    simp [Pi.add_apply, map_add]
  rw [tangentConstAt_add]
  change
    riemannCurvatureAux cov Xc (Y₁c + Y₂c) Zc x =
      riemannCurvatureAux cov Xc Y₁c Zc x +
        riemannCurvatureAux cov Xc Y₂c Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.add hZY₁ hZY₂]
  rw [VectorField.mlieBracket_add_right (I := I) hY₁ hY₂]
  simp [Pi.add_apply, map_add]
  module

omit [FiniteDimensional ℝ E] in
 theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_smul_second_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x (a • Y))
        (tangentConstAt (I := I) x Z) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  have hY : MDiffAt (T% Yc) x := mdifferentiableAt_tangentConstAt_self (I := I) x Y
  have hZY : MDiffAt (T% (fun p : M => (cov Zc p) (Yc p))) x := by
    simpa [Yc, Zc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y
  have hmid :
      (fun p : M => (cov Zc p) ((a • Yc) p)) =
        a • (fun p : M => (cov Zc p) (Yc p)) := by
    funext p
    simp [Pi.smul_apply, map_smul]
  rw [tangentConstAt_smul]
  change
    riemannCurvatureAux cov Xc (a • Yc) Zc x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hmid]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZY]
  rw [VectorField.mlieBracket_const_smul_right (I := I) (c := a) hY]
  simp [Pi.smul_apply, map_smul]
  module

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
 theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_add_third_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y Z₁ Z₂ : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (Z₁ + Z₂)) x =
      riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₁) x +
        riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z₂) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Z₁c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z₁
  let Z₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z₂
  let Z₁₂c : (p : M) → TangentSpace I p := tangentConstAt (I := I) x (Z₁ + Z₂)
  have hZ₁ : MDiffAt (T% Z₁c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z₁
  have hZ₂ : MDiffAt (T% Z₂c) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z₂
  have hZ₁₂Y : MDiffAt (T% (fun p : M => (cov Z₁₂c p) (Yc p))) x := by
    simpa [Z₁₂c, Yc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (Z₁ + Z₂) Y
  have hZ₁Y : MDiffAt (T% (fun p : M => (cov Z₁c p) (Yc p))) x := by
    simpa [Z₁c, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₁ Y
  have hZ₂Y : MDiffAt (T% (fun p : M => (cov Z₂c p) (Yc p))) x := by
    simpa [Z₂c, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₂ Y
  have hZ₁₂X : MDiffAt (T% (fun p : M => (cov Z₁₂c p) (Xc p))) x := by
    simpa [Z₁₂c, Xc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (Z₁ + Z₂) X
  have hZ₁X : MDiffAt (T% (fun p : M => (cov Z₁c p) (Xc p))) x := by
    simpa [Z₁c, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₁ X
  have hZ₂X : MDiffAt (T% (fun p : M => (cov Z₂c p) (Xc p))) x := by
    simpa [Z₂c, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z₂ X
  have hsumY :
      MDiffAt
        (T% ((fun p : M => (cov Z₁c p) (Yc p)) +
          fun p : M => (cov Z₂c p) (Yc p))) x :=
    mdifferentiableAt_add_section hZ₁Y hZ₂Y
  have hsumX :
      MDiffAt
        (T% ((fun p : M => (cov Z₁c p) (Xc p)) +
          fun p : M => (cov Z₂c p) (Xc p))) x :=
    mdifferentiableAt_add_section hZ₁X hZ₂X
  have hcongrY :
      cov (fun p : M => (cov Z₁₂c p) (Yc p)) x =
        cov ((fun p : M => (cov Z₁c p) (Yc p)) +
          fun p : M => (cov Z₂c p) (Yc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ₁₂Y hsumY
      (by simp)
      (by
        filter_upwards [cov_tangentConst_add_apply_eventuallyEq
          (I := I) cov x Z₁ Z₂ Y] with p hp
        simpa [Z₁₂c, Z₁c, Z₂c, Yc] using hp)
  have hcongrX :
      cov (fun p : M => (cov Z₁₂c p) (Xc p)) x =
        cov ((fun p : M => (cov Z₁c p) (Xc p)) +
          fun p : M => (cov Z₂c p) (Xc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ₁₂X hsumX
      (by simp)
      (by
        filter_upwards [cov_tangentConst_add_apply_eventuallyEq
          (I := I) cov x Z₁ Z₂ X] with p hp
        simpa [Z₁₂c, Z₁c, Z₂c, Xc] using hp)
  change
    riemannCurvatureAux cov Xc Yc Z₁₂c x =
      riemannCurvatureAux cov Xc Yc Z₁c x +
        riemannCurvatureAux cov Xc Yc Z₂c x
  unfold riemannCurvatureAux
  rw [hcongrY, hcongrX]
  rw [show Z₁₂c = Z₁c + Z₂c by
    simp [Z₁₂c, Z₁c, Z₂c]]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁Y hZ₂Y]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁X hZ₂X]
  rw [cov.isCovariantDerivativeOnUniv.add hZ₁ hZ₂]
  simp
  module

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
 theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_smul_third_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (a : Real) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov
        (tangentConstAt (I := I) x X)
        (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x (a • Z)) x =
      a • riemannCurvatureAux cov
          (tangentConstAt (I := I) x X)
          (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x := by
  let Xc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x X
  let Yc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Y
  let Zc : (p : M) → TangentSpace I p := tangentConstAt (I := I) x Z
  let Za : (p : M) → TangentSpace I p := tangentConstAt (I := I) x (a • Z)
  have hZ : MDiffAt (T% Zc) x := mdifferentiableAt_tangentConstAt_self (I := I) x Z
  have hZaY : MDiffAt (T% (fun p : M => (cov Za p) (Yc p))) x := by
    simpa [Za, Yc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (a • Z) Y
  have hZY : MDiffAt (T% (fun p : M => (cov Zc p) (Yc p))) x := by
    simpa [Zc, Yc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z Y
  have hZaX : MDiffAt (T% (fun p : M => (cov Za p) (Xc p))) x := by
    simpa [Za, Xc] using
      cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x (a • Z) X
  have hZX : MDiffAt (T% (fun p : M => (cov Zc p) (Xc p))) x := by
    simpa [Zc, Xc] using cov_tangentConst_apply_mdiffAt_self (I := I) cov hcov x Z X
  have hsmulY :
      MDiffAt (T% (a • fun p : M => (cov Zc p) (Yc p))) x :=
    mdifferentiableAt_const.smul_section hZY
  have hsmulX :
      MDiffAt (T% (a • fun p : M => (cov Zc p) (Xc p))) x :=
    mdifferentiableAt_const.smul_section hZX
  have hcongrY :
      cov (fun p : M => (cov Za p) (Yc p)) x =
        cov (a • fun p : M => (cov Zc p) (Yc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZaY hsmulY
      (by simp)
      (by
        filter_upwards [cov_tangentConst_smul_apply_eventuallyEq
          (I := I) cov x a Z Y] with p hp
        simpa [Za, Zc, Yc] using hp)
  have hcongrX :
      cov (fun p : M => (cov Za p) (Xc p)) x =
        cov (a • fun p : M => (cov Zc p) (Xc p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZaX hsmulX
      (by simp)
      (by
        filter_upwards [cov_tangentConst_smul_apply_eventuallyEq
          (I := I) cov x a Z X] with p hp
        simpa [Za, Zc, Xc] using hp)
  change
    riemannCurvatureAux cov Xc Yc Za x =
      a • riemannCurvatureAux cov Xc Yc Zc x
  unfold riemannCurvatureAux
  rw [hcongrY, hcongrX]
  rw [show Za = a • Zc by
    simp [Za, Zc]]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZY]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZX]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hZ]
  simp
  module

 noncomputable def _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureZCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  let _ : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Z =>
        cotangentToDualGen α
          (riemannCurvatureAux cov
            (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
            (tangentConstAt (I := I) x Z) x)
      map_add' := by
        intro Z₁ Z₂
        change
          cotangentToDualGen α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (Z₁ + Z₂)) x) =
            cotangentToDualGen α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₁) x) +
              cotangentToDualGen α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z₂) x)
        rw [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_add_third_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x X Y Z₁ Z₂]
        exact map_add (cotangentToDualGen α) _ _
      map_smul' := by
        intro a Z
        change
          cotangentToDualGen α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x (a • Z)) x) =
            a • cotangentToDualGen α
              (riemannCurvatureAux cov
                (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                (tangentConstAt (I := I) x Z) x)
        rw [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_smul_third_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x a X Y Z]
        exact map_smul (cotangentToDualGen α) a _ }

 noncomputable def _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureYZModel_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun Y =>
          (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
            (_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureZCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x α X Y)
        map_add' := by
          intro Y₁ Y₂
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDualGen α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (Y₁ + Y₂))
                  (tangentConstAt (I := I) x Z) x) =
              cotangentToDualGen α
                  (riemannCurvatureAux cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₁)
                    (tangentConstAt (I := I) x Z) x) +
                cotangentToDualGen α
                  (riemannCurvatureAux cov
                    (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y₂)
                    (tangentConstAt (I := I) x Z) x)
          rw [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_add_second_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x X Y₁ Y₂ Z]
          exact map_add (cotangentToDualGen α) _ _
        map_smul' := by
          intro a Y
          apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
          ext Z
          change
            cotangentToDualGen α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x (a • Y))
                  (tangentConstAt (I := I) x Z) x) =
              a • cotangentToDualGen α
                (riemannCurvatureAux cov
                  (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
                  (tangentConstAt (I := I) x Z) x)
          rw [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_smul_second_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x a X Y Z]
          exact map_smul (cotangentToDualGen α) a _ })

@[simp]  theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureYZModel_apply_vec2_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
  _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureYZModel_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x α X (vec2 Y Z) =
      cotangentToDualGen α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  unfold _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureYZModel_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureZCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x α X Y))
      (fun i : Fin 1 => vec2 Y Z i.succ) =
    cotangentToDualGen α
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x)
  rw [show (fun i : Fin 1 => vec2 Y Z i.succ) = fun _ : Fin 1 => Z by
    funext i
    fin_cases i
    simp [vec2]]
  rfl

 noncomputable def _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureModel_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := Real) (n := 2) (Ei := fun _ : Fin 3 => TangentSpace I x) (G := Real)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X => _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureYZModel_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x α X
        map_add' := by
          intro X₁ X₂
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureYZModel_apply_vec2_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise]
          rw [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_add_first_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x X₁ X₂ (v 0) (v 1)]
          exact map_add (cotangentToDualGen α) _ _
        map_smul' := by
          intro a X
          apply ContinuousMultilinearMap.ext
          intro v
          have hv : v = vec2 (v 0) (v 1) := by
            funext i
            fin_cases i <;> simp [vec2]
          rw [hv]
          simp only [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureYZModel_apply_vec2_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise]
          rw [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureAux_tangentConst_smul_first_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x a X (v 0) (v 1)]
          exact map_smul (cotangentToDualGen α) a _ })

noncomputable def riemannCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor13At (I := I) (M := M) x :=
  TensorRSSpace.ofModel (I := I) (x := x)
    (LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureModel_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x
          (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α)
      map_add' := by
        intro α β
        apply ContinuousMultilinearMap.ext
        intro v
        let R := riemannCurvatureAux cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDualGen (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β)) R =
          cotangentToDualGen (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R +
            cotangentToDualGen (I := I)
              (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β) R
        have hαβ :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (α + β) =
              Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α +
                Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) β := by
          exact map_add
            (tensor0SSpaceContinuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm α β
        rw [hαβ]
        rfl
      map_smul' := by
        intro c α
        apply ContinuousMultilinearMap.ext
        intro v
        let R := riemannCurvatureAux cov
          (tangentConstAt (I := I) x (v 0)) (tangentConstAt (I := I) x (v 1))
          (tangentConstAt (I := I) x (v 2)) x
        change cotangentToDualGen (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α)) R =
          c • cotangentToDualGen (I := I)
            (Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α) R
        have hα :
            Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) (c • α) =
              c • Tensor0SSpace.ofModel (𝕜 := Real) (I := I) (x := x) α := by
          exact map_smul
            (tensor0SSpaceContinuousLinearEquiv (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 x).symm c α
        rw [hα]
        rfl })

@[simp]
theorem riemannCurvatureAt_apply_const
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    riemannCurvatureAt cov hcov x α (vec3 X Y Z) =
      cotangentToDualGen α
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  change (_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvatureModel_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise cov hcov x α) (vec3 X Y Z) =
    cotangentToDualGen α
      (riemannCurvatureAux cov
        (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
        (tangentConstAt (I := I) x Z) x)
  rfl

 noncomputable def _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 1 => E) Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W =>
        (continuousMultilinearCurryFin1 Real E Real).symm
          (LinearMap.toContinuousLinearMap ((tangentFlatLinearGen (I := I) g x) W))
      map_add' := by
        intro W W'
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinearGen (I := I) g x) (W + W')) V =
            (((tangentFlatLinearGen (I := I) g x) W) +
              ((tangentFlatLinearGen (I := I) g x) W')) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinearGen (I := I) g x).map_add W W')
      map_smul' := by
        intro c W
        apply (continuousMultilinearCurryFin1 Real E Real).injective
        ext V
        change
          ((tangentFlatLinearGen (I := I) g x) (c • W)) V =
            (c • ((tangentFlatLinearGen (I := I) g x) W)) V
        exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L V)
          ((tangentFlatLinearGen (I := I) g x).map_smul c W) }

omit [CompleteSpace E] in
@[simp]  theorem _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_apply_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise
    (g : SmoothRiemannianMetric I M) (x : M) (W : TangentSpace I x) :
    _root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise (I := I) g x W =
      (continuousMultilinearCurryFin1 Real E Real).symm
        (LinearMap.toContinuousLinearMap ((tangentFlatLinearGen (I := I) g x) W)) := by
  simp [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise]

noncomputable def riemannCurvature04At
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  tensor04StdOfOutAt (I := I) (M := M)
    (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (ContinuousLinearMap.uncurryLeft
        (𝕜 := Real) (n := 3) (Ei := fun _ : Fin 4 => E) (G := Real)
        (((TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (riemannCurvatureAt cov hcov x)).comp
          (_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise (I := I) g x)) :
          E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real)))

@[simp]
theorem riemannCurvature04At_apply_const
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (X Y Z W : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 X Y Z W) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x) := by
  dsimp [riemannCurvature04At]
  rw [tensor04StdOfOutAt_apply]
  let modelVec : Fin 4 → E := fun i =>
    tangentSpaceModelContinuousLinearEquiv (I := I) x (vec4 W X Y Z i)
  change
    (ContinuousLinearMap.uncurryLeft
        (𝕜 := Real) (n := 3) (Ei := fun _ : Fin 4 => E) (G := Real)
        (((TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (riemannCurvatureAt cov hcov x)).comp
          (_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise (I := I) g x)) :
          E →L[Real] ContinuousMultilinearMap Real (fun _ : Fin 3 => E) Real))
        modelVec =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [ContinuousLinearMap.uncurryLeft_apply]
  rw [ContinuousLinearMap.comp_apply]
  unfold TensorRSSpace.toModel
  rw [tensorRSSpace_continuousLinearEquiv_apply_apply]
  change
    riemannCurvatureAt cov hcov x
        (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise (I := I) g x W))
        (fun i : Fin 3 => vec4 W X Y Z i.succ) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [show (fun i : Fin 3 => vec4 W X Y Z i.succ) = vec3 X Y Z by
    funext i
    fin_cases i <;> simp [vec3, vec4]]
  rw [riemannCurvatureAt_apply_const]
  rw [cotangentToDual_apply_gen]
  change
    (_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise (I := I) g x W)
        (fun _ : Fin 1 =>
          riemannCurvatureAux cov
            (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
            (tangentConstAt (I := I) x Z) x) =
      g.inner x W
        (riemannCurvatureAux cov
          (tangentConstAt (I := I) x X) (tangentConstAt (I := I) x Y)
          (tangentConstAt (I := I) x Z) x)
  rw [_root_.DifferentialGeometry.Geometry.Curvature.CovariantDerivative.tangentFlatCotangentModelCLM_apply_closedSurface_DifferentialGeometry_Geometry_Curvature_Riemann_Basic_Pointwise]
  rfl

noncomputable def ricciCurvatureAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  ricciFromRm13At (riemannCurvatureAt cov hcov x)

theorem riemannCurvature04At_eq_lower_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) {x : M}
    (X Y Z W : TangentSpace I x) :
    riemannCurvature04At g cov hcov x (vec4 X Y Z W) =
      riemannCurvatureAt cov hcov x (dualToCotangentGen ((tangentFlatLinearGen g x) W))
        (vec3 X Y Z) := by
  rw [riemannCurvature04At_apply_const, riemannCurvatureAt_apply_const]
  simp [tangentFlatLinear_apply_gen]

end CovariantDerivative

end DifferentialGeometry.Geometry.Curvature

end
