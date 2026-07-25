import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs
import DifferentialGeometry.Analysis.Elliptic.Operator.ChartLocalLaplacian


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem weightedInvGramEuclid_eq_weightedInvGramOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    weightedInvGramEuclid (I := I) g α k l =
      weightedInvGramOnEuclid (I := I) g α k l :=
  rfl

theorem exists_tensorPrincipalForm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) := by
  obtain ⟨_, _, _, _, _, B, hB_agree, hB_c⟩ :=
    exists_smooth_metric_extension (I := I) (M := M) g α hK hK_target
  exact ⟨B, hB_agree, hB_c⟩

def tensorPrincipalForm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
  Classical.choose (exists_tensorPrincipalForm (I := I) (M := M) g α hK hK_target)

theorem tensorPrincipalForm_spec
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
          weightedInvGramEuclid (I := I) g α i j y) ∧
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c =
        (fun _ : EuclN => (0 : ℝ)) :=
  Classical.choose_spec (exists_tensorPrincipalForm (I := I) (M := M) g α hK hK_target)

theorem tensorPrincipalForm_a_eq_weightedInvGramEuclid
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {y : EuclN} (hy : y ∈ K) (i j : Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
      weightedInvGramEuclid (I := I) g α i j y :=
  (tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target).1 y hy i j

theorem tensorPrincipalForm_c
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c =
      (fun _ : EuclN => (0 : ℝ)) :=
  (tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target).2

theorem tensorPrincipalForm_c_apply
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c y = 0 := by
  rw [tensorPrincipalForm_c (I := I) (M := M) g α hK hK_target]

theorem tensorPrincipalForm_eq_scalar_metric_form
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      B = tensorPrincipalForm (I := I) (M := M) g α hK hK_target ∧
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) :=
  ⟨tensorPrincipalForm (I := I) (M := M) g α hK hK_target, rfl,
    tensorPrincipalForm_spec (I := I) (M := M) g α hK hK_target⟩

theorem tensorPrincipalForm_symm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) (i j : Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y i j =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y j i :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).symm y i j

theorem tensorPrincipalForm_lam_pos
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    0 < (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).lam :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).hlam_pos

theorem tensorPrincipalForm_coercive
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (y : EuclN) (ξ : EuclN) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).lam * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a y) ξ⟫_ℝ :=
  (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).coercive y
    (Set.mem_univ y) ξ

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
