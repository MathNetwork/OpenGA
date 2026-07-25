import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

noncomputable def pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x
      contMDiff_toFun := by
        exact ContMDiff.smul_section
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff S.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport S.toFun ?_
    rw [Function.mem_support]
    intro hS_zero
    apply hx
    change TensorRSSpace.toModel
      (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (S.toSection x) = S.toFun x from rfl, hS_zero,
      smul_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma pouSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    (pouSmul (I := I) (M := M) g r s α S).toSection x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toSection x := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma pouSmul_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    (pouSmul (I := I) (M := M) g r s α S).toFun x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • S.toFun x := by
  rw [SmoothCcTensor.toFun_apply, pouSmul_toSection_apply,
    TensorRSSpace.toModel_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorTrivProj_pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (x : M) :
    tensorTrivProj (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        tensorTrivProj (I := I) (M := M) g r s S α x := by
  unfold tensorTrivProj
  rw [pouSmul_toSection_apply]
  exact map_smul _ _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentRaw_smul_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x := by
  funext x
  unfold tensorChartComponentRaw
  rw [tensorTrivProj_pouSmul (I := I) (M := M) g r s α S x, map_smul,
    smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx := by
  rw [tensorChartComponentRaw_smul_pou (I := I) (M := M) g r s α S Idx Jdx]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem pouSmul_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    tsupport (pouSmul (I := I) (M := M) g r s α S).toFun ⊆
      (chartAt H α).source := by
  classical
  have hfun_eq : (pouSmul (I := I) (M := M) g r s α S).toFun =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        S.toFun x := by
    funext x
    exact pouSmul_toFun_apply (I := I) (M := M) g r s α S x
  rw [hfun_eq]
  have h_supp_sub : Function.support
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x •
        S.toFun x) ⊆
      Function.support
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hweight_zero
    exact hx (by rw [hweight_zero, zero_smul])
  refine (closure_mono h_supp_sub).trans ?_
  exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
    I M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponent_eq_tensorComponentEuclid_pouSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (P₀ : CompIdx E r s) :
    tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 =
      tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀ := by
  rw [tensorComponentEuclid_def, tensorChartComponent_def,
    tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
      (I := I) (M := M) g r s α S P₀.1 P₀.2]

theorem tensorChartComponent_isSmoothWeakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hS_K : tsupport
        (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α S) v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2)
      (tensorComponentWeakRHS (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) F α hK hK_target P₀) := by
  classical
  have hcomp_eq :
      tensorChartComponent (I := I) (M := M) g r s S α P₀.1 P₀.2 =
        tensorComponentEuclid (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α P₀ :=
    tensorChartComponent_eq_tensorComponentEuclid_pouSmul
      (I := I) (M := M) g r s α S P₀
  have hpou_supp :
      tsupport (pouSmul (I := I) (M := M) g r s α S).toFun ⊆
        (chartAt H α).source :=
    pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α S
  have hpou_K :
      tsupport (tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀) ⊆ K := by
    rw [← hcomp_eq]; exact hS_K
  rw [hcomp_eq]
  exact tensorComponent_isSmoothWeakSolution (I := I) (M := M) g r s
    (pouSmul (I := I) (M := M) g r s α S) F α hK hK_target P₀
    hpou_supp hF_supp hpou_K hweak

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
