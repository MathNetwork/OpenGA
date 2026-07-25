import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion








noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


noncomputable def ccToHsLin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ) :
    SmoothCcTensor g 0 s →ₗ[ℝ] tensorHs (I := I) (M := M) g 0 s σ where
  toFun := ccTensorToHs (I := I) (M := M) g s σ
  map_add' := ccTensorToHs_add (I := I) (M := M) g s σ
  map_smul' := ccTensorToHs_smul (I := I) (M := M) g s σ


@[simp] theorem ccToHsLin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (S : SmoothCcTensor g 0 s) :
    ccToHsLin (I := I) (M := M) g s σ S =
      ccTensorToHs (I := I) (M := M) g s σ S :=
  rfl



theorem ccToHsLin_repr
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (v : tensorHs (I := I) (M := M) g 0 s σ)
    (hv : (Function.support v.coeff).Finite) :
    ccToHsLin (I := I) (M := M) g s σ
        (tensorHsSmoothRepr (I := I) (M := M) v hv) = v := by
  apply tensorHs.ext
  funext i
  simp only [ccToHsLin_apply, ccTensorToHs_coeff]
  rw [SmoothCcTensor.toL2_apply,
    tensorHsSmoothRepr_toL2 (I := I) (M := M) hσ v hv,
    tensorHsToL2_tensorL2Coeff (I := I) (M := M) hσ]



theorem ccToHs_eigen
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g 0 s) :
    ccTensorToHs (I := I) (M := M) g s σ
        (eigenvectorSmooth (I := I) (M := M) g 0 s i) =
      tensorHsBasisVec (I := I) (M := M)
        (g := g) (r := 0) (s := s) σ i := by
  classical
  let v := tensorHsBasisVec (I := I) (M := M)
    (g := g) (r := 0) (s := s) σ i
  have hv : (Function.support v.coeff).Finite := by
    refine Set.finite_singleton i |>.subset ?_
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · exact False.elim ((Function.mem_support.mp hj) (by simp [v, hji]))
  have hfin : hv.toFinset = {i} := by
    ext j
    simp only [Set.Finite.mem_toFinset,
      Function.mem_support, v, tensorHsBasisVec_coeff, ne_eq]
    by_cases hji : j = i <;> simp [hji]
  have hre : tensorHsSmoothRepr (I := I) (M := M) v hv =
      eigenvectorSmooth (I := I) (M := M) g 0 s i := by
    rw [tensorHsSmoothRepr_eq (I := I) (M := M) v hv, hfin]
    simp [v]
  rw [← hre, ← ccToHsLin_apply]
  exact ccToHsLin_repr (I := I) (M := M) g s hσ v hv



theorem ccToHsLin_dense
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    DenseRange (ccToHsLin (I := I) (M := M) g s σ) := by
  classical
  refine (tensorHsFiniteSupportSubmodule_dense
    (I := I) (M := M) (g := g) (r := 0) (s := s) (σ := σ)).mono ?_
  intro v hv
  have hvfs : (Function.support v.coeff).Finite :=
    (tensorHs.mem_finiteSupportSubmodule (I := I) (M := M) v).mp hv
  exact ⟨tensorHsSmoothRepr (I := I) (M := M) v hvfs,
    ccToHsLin_repr (I := I) (M := M) g s hσ v hvfs⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
