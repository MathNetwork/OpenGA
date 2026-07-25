import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRSNabla
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set IsManifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

section ModelFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

@[nolint unusedArguments]
def HomTensorRSModel (r a c : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :=
  TensorRSModel r a 𝕜 E →L[𝕜] TensorRSModel r c 𝕜 E

private instance tensor0SModel_smulCommClass (s : ℕ) :
    SMulCommClass 𝕜 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel; infer_instance

private instance tensorRSModel_smulCommClass (r c : ℕ) :
    SMulCommClass 𝕜 𝕜 (TensorRSModel r c 𝕜 E) := by
  letI nsr : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) := tensor0SModel_normedSpace r
  letI nsc : NormedSpace 𝕜 (Tensor0SModel c 𝕜 E) := tensor0SModel_normedSpace c
  unfold TensorRSModel
  infer_instance

instance homTensorRSModel_normedAddCommGroup (r a c : ℕ) :
    NormedAddCommGroup (HomTensorRSModel r a c 𝕜 E) := by
  unfold HomTensorRSModel
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_normedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_normedSpace r c
  exact @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (TensorRSModel r a 𝕜 E) (TensorRSModel r c 𝕜 E) _ _ _ _ nsU nsV _ _

instance homTensorRSModel_normedSpace (r a c : ℕ) :
    NormedSpace 𝕜 (HomTensorRSModel r a c 𝕜 E) := by
  unfold HomTensorRSModel
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_normedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_normedSpace r c
  letI scc : SMulCommClass 𝕜 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_smulCommClass r c
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (TensorRSModel r a 𝕜 E) (TensorRSModel r c 𝕜 E) _ _ _ _ _ _ _ _ 𝕜 _ nsV scc

noncomputable instance homTensorRSModel_finiteDimensional [CompleteSpace 𝕜] (r a c : ℕ) :
    FiniteDimensional 𝕜 (HomTensorRSModel r a c 𝕜 E) := by
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_normedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_normedSpace r c
  haveI iUf : FiniteDimensional 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_finiteDimensional r a
  haveI iVf : FiniteDimensional 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_finiteDimensional r c
  unfold HomTensorRSModel
  exact ContinuousLinearMap.finiteDimensional

end ModelFiber

section SpaceFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

@[nolint unusedArguments]
def HomTensorRSSpace (r a c : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) : Type _ :=
  TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x

instance homTensorRSSpace_topologicalSpace (r a c : ℕ) (x : M) :
    TopologicalSpace (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (TopologicalSpace (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_addCommGroup (r a c : ℕ) (x : M) :
    AddCommGroup (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (AddCommGroup (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_module (r a c : ℕ) (x : M) :
    Module 𝕜 (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (Module 𝕜 (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_isTopologicalAddGroup (r a c : ℕ) (x : M) :
    IsTopologicalAddGroup (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (IsTopologicalAddGroup (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_continuousAdd (r a c : ℕ) (x : M) :
    ContinuousAdd (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (ContinuousAdd (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

instance homTensorRSSpace_continuousSMul (r a c : ℕ) (x : M) :
    ContinuousSMul 𝕜 (HomTensorRSSpace r a c I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x))

noncomputable instance homTensorRSBundle_topology (r a c : ℕ) :
    TopologicalSpace (TotalSpace (HomTensorRSModel r a c 𝕜 E)
      (fun x : M => HomTensorRSSpace r a c I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

noncomputable instance homTensorRSBundle_fiber (r a c : ℕ) :
    @FiberBundle M (HomTensorRSModel r a c 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => HomTensorRSSpace r a c I x)
      (homTensorRSBundle_topology r a c) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

noncomputable instance homTensorRSBundle_vector (r a c : ℕ) :
    @VectorBundle 𝕜 M (HomTensorRSModel r a c 𝕜 E) (fun x : M => HomTensorRSSpace r a c I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (homTensorRSModel_normedAddCommGroup r a c) (homTensorRSModel_normedSpace r a c) _
      (homTensorRSBundle_topology r a c) _
      (homTensorRSBundle_fiber r a c) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

noncomputable instance homTensorRSBundle_smooth [CompleteSpace 𝕜] (n : WithTop ℕ∞)
    [IsManifold I (n + 1) M] (r a c : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (HomTensorRSModel r a c 𝕜 E)
      (fun x : M => HomTensorRSSpace r a c I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (homTensorRSBundle_topology r a c) _
      (homTensorRSBundle_fiber r a c)
      (homTensorRSBundle_vector r a c) :=
  ContMDiffVectorBundle.continuousLinearMap

end SpaceFiber

section CovDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open scoped ContDiff
open CovariantDerivative

noncomputable def homTensorRSCovariantDerivative (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (HomTensorRSModel r a c ℝ E)
      (fun x : M => HomTensorRSSpace r a c I x) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)

noncomputable instance homTensorRSCovariantDerivative_contMDiff (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (homTensorRSCovariantDerivative I M r a c cov) ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)

omit [CompleteSpace E] in
theorem homTensorRSCovariantDerivative_apply (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (Ψ : Cₛ^∞⟮I; HomTensorRSModel r a c ℝ E, (fun x : M => HomTensorRSSpace r a c I x)⟯)
    (W : Cₛ^∞⟮I; TensorRSModel r a ℝ E, (fun x : M => TensorRSSpace r a I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
        homTensorRSCovariantDerivative I M r a c cov Ψ x v) (W x) =
      TensorRSNabla.tensorRSCovariantDerivative I M r c cov
        (fun y =>
          (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W y)) x v -
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
        (TensorRSNabla.tensorRSCovariantDerivative I M r a cov W x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)
    Ψ W x v

omit [CompleteSpace E] in
theorem homTensorRSCovariantDerivative_apply_of_mdifferentiableAt (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : Π x : M, TensorRSSpace r a I x)
    (V_field : Π x : M, TangentSpace I x)
    {x : M}
    (hΨ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) y (Ψ y)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun z : M => TensorRSSpace r a I z) y (W y)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) y (V_field y)) x) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
        homTensorRSCovariantDerivative I M r a c cov Ψ x (V_field x)) (W x) =
      TensorRSNabla.tensorRSCovariantDerivative I M r c cov
        (fun y =>
          (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W y))
          x (V_field x) -
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
        (TensorRSNabla.tensorRSCovariantDerivative I M r a cov W x (V_field x)) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M
    (TensorRSModel r a ℝ E) (fun y : M => TensorRSSpace r a I y)
    (TensorRSModel r c ℝ E) (fun y : M => TensorRSSpace r c I y)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)
    Ψ hΨ hV hW

end CovDeriv

end DifferentialGeometry.Integral.Connection

end
