import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => (ζ : M → ℝ) x • w.toSection x
      contMDiff_toFun := by
        exact ContMDiff.smul_section ζ.contMDiff w.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact w.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport w.toFun ?_
    rw [Function.mem_support]
    intro hw_zero
    apply hx
    change TensorRSSpace.toModel ((ζ : M → ℝ) x • w.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (w.toSection x) = w.toFun x from rfl, hw_zero,
      smul_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma scalarSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toSection x =
      (ζ : M → ℝ) x • w.toSection x := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma scalarSmul_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toFun x =
      (ζ : M → ℝ) x • w.toFun x := by
  rw [SmoothCcTensor.toFun_apply, scalarSmul_toSection_apply,
    TensorRSSpace.toModel_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s
        (scalarSmul (I := I) (M := M) g r s ζ w) x v =
      (ζ : M → ℝ) x • tensorCovDerivAt (I := I) (M := M) g r s w x v +
        (extDerivFun (I := I) (ζ : M → ℝ) x v) • w.toSection x := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (scalarSmul (I := I) (M := M) g r s ζ w).toSection y) =
      (fun y : M => (ζ : M → ℝ) y) • (fun y : M => w.toSection y) := by
    funext y
    rw [scalarSmul_toSection_apply]
    rfl
  rw [hpt]
  have hζ_mdiff : MDiffAt (fun y : M => (ζ : M → ℝ) y) x :=
    (ζ.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
  have hw_mdiff :=
    (w.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt (x := x)
  have hcov_leibniz :=
    (tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := fun y : M => w.toSection y)
      (g := fun y : M => (ζ : M → ℝ) y)
      (hσ := hw_mdiff)
      (hg := hζ_mdiff)
      (hx := (by trivial : x ∈ (Set.univ : Set M)))
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      ((fun y : M => (ζ : M → ℝ) y) • fun y : M => w.toSection y) x v = _
  rw [hcov_leibniz]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]

noncomputable def tensorCovDerivCrossLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) j) *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s w x ((chartModelBasis E) i)))
          (S.toFun x))

noncomputable def tensorCovDerivCrossRight
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (w.toFun x)
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) j))))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivCrossLeft_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) j) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (S.toFun x)) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivCrossRight_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (w.toFun x)
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorCovDerivPointwiseInner_scalarSmul_left_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s
              (scalarSmul (I := I) (M := M) g r s ζ w) x ((chartModelBasis E) i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S x
              ((chartModelBasis E) j))) =
      (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) +
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (w.toFun x)
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) := by
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ w x
    ((chartModelBasis E) i)]
  simp only [TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul]
  have hwx : TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
  rw [hwx]
  rw [tensorInnerPointwise_add_left]
  simp only [tensorInnerPointwise_smul_left]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorCovDerivPointwiseInner_scalarSmul_right_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s w x ((chartModelBasis E) i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s
              (scalarSmul (I := I) (M := M) g r s ζ S) x
                ((chartModelBasis E) j))) =
      (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) +
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) j) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (S.toFun x)) := by
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ S x
    ((chartModelBasis E) j)]
  simp only [TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul]
  have hSx : TensorRSSpace.toModel (S.toSection x) = S.toFun x := rfl
  rw [hSx]
  rw [tensorInnerPointwise_add_right]
  simp only [tensorInnerPointwise_smul_right]
  ring

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma smul_const_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)))) =
      (ζ : M → ℝ) x *
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s w S x := by
  rw [tensorCovDerivPointwiseInner_def, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_scalarSmul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        (scalarSmul (I := I) (M := M) g r s ζ w) S x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s w
          (scalarSmul (I := I) (M := M) g r s ζ S) x -
        tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x +
        tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x := by
  classical
  have hLHS :
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ w) S x =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (ζ : M → ℝ) x *
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s w x
                      ((chartModelBasis E) i)))
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S x
                      ((chartModelBasis E) j))))) +
          tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x := by
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossRight_def,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact tensorCovDerivPointwiseInner_scalarSmul_left_summand
      (I := I) (M := M) g r s ζ w S x i j
  have hRHS :
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s w
          (scalarSmul (I := I) (M := M) g r s ζ S) x =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (ζ : M → ℝ) x *
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s w x
                      ((chartModelBasis E) i)))
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S x
                      ((chartModelBasis E) j))))) +
          tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x := by
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact tensorCovDerivPointwiseInner_scalarSmul_right_summand
      (I := I) (M := M) g r s ζ w S x i j
  rw [hLHS, hRHS]
  ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
