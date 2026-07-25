import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifferenceKoszulSecondCovGrad


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
theorem trace_eq_basis_repr_sum (G : E →ₗ[ℝ] E) :
    ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (G ((chartModelBasis E) i)) i =
      LinearMap.trace ℝ E G := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (chartModelBasis E), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cometricLmodel_finBasis_inner_eq_kronecker (g₁ : SmoothRiemannianMetric I M) (x : M)
    (j k : Fin (Module.finrank ℝ E)) :
    g₁.inner x
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) j) =
      if j = k then 1 else 0 := by
  classical
  have h1 : cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₁ x
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ x _ ((Module.finBasis ℝ E) j),
    cotangentToDualLinear_apply, cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => (Module.finBasis ℝ E) j) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => ((Module.finBasis ℝ E) j : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, Module.Basis.repr_self]
  rw [Finsupp.single_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem trace_eq_cometricLmodel_pairing_sum (g₁ : SmoothRiemannianMetric I M) (x : M) (G : E →ₗ[ℝ] E) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x
          (G (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k) =
      LinearMap.trace ℝ E G := by
  classical
  set d : Fin (Module.finrank ℝ E) → E := fun k =>
    cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hd
  set ε : Fin (Module.finrank ℝ E) → Module.Dual ℝ E := fun k =>
    ((g₁.inner x).flip ((Module.finBasis ℝ E) k)).toLinearMap with hε
  have hev_same : ∀ k, ε k (d k) = 1 := by
    intro k
    rw [hε, hd]
    change g₁.inner x (d k) ((Module.finBasis ℝ E) k) = 1
    rw [hd, cometricLmodel_finBasis_inner_eq_kronecker (I := I) g₁ x k k, if_pos rfl]
  have hev_ne : Pairwise fun i j => ε i (d j) = 0 := by
    intro i j hij
    rw [hε, hd]
    change g₁.inner x (d j) ((Module.finBasis ℝ E) i) = 0
    rw [hd, cometricLmodel_finBasis_inner_eq_kronecker (I := I) g₁ x i j, if_neg hij]
  have htot : ∀ {m₁ m₂ : E}, (∀ k, ε k m₁ = ε k m₂) → m₁ = m₂ := by
    intro m₁ m₂ hm
    apply SmoothRiemannianMetric.eq_of_inner_eq g₁ (x := x)
    intro ζ
    have hζ : ζ = ∑ k : Fin (Module.finrank ℝ E), (Module.finBasis ℝ E).repr ζ k • (Module.finBasis ℝ E) k :=
      ((Module.finBasis ℝ E).sum_repr ζ).symm
    rw [hζ]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hm k
    change (Module.finBasis ℝ E).repr ζ k * g₁.inner x m₁ ((Module.finBasis ℝ E) k) =
      (Module.finBasis ℝ E).repr ζ k * g₁.inner x m₂ ((Module.finBasis ℝ E) k)
    rw [g₁.symm x m₁, g₁.symm x m₂]
    have hk' : g₁.inner x m₁ ((Module.finBasis ℝ E) k) = g₁.inner x m₂ ((Module.finBasis ℝ E) k) := by
      have e1 : ε k m₁ = g₁.inner x m₁ ((Module.finBasis ℝ E) k) := by rw [hε]; rfl
      have e2 : ε k m₂ = g₁.inner x m₂ ((Module.finBasis ℝ E) k) := by rw [hε]; rfl
      rw [← e1, ← e2, hk]
    rw [g₁.symm x ((Module.finBasis ℝ E) k) m₁, g₁.symm x ((Module.finBasis ℝ E) k) m₂, hk']
  have hdual : Module.DualBases d ε :=
    { eval_same := hev_same, eval_of_ne := hev_ne, total := htot }
  rw [LinearMap.trace_eq_matrix_trace ℝ hdual.basis, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [Module.DualBases.coe_basis]
  have hrepr : hdual.basis.repr (G (d k)) k = ε k (G (d k)) := by
    rw [Module.DualBases.basis_repr_apply, Module.DualBases.coeffs_apply]
  rw [hrepr, hε]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma dualToCotangent_addC {x : M} (α β : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (α + β)
      = dualToCotangent (I := I) (x := x) α + dualToCotangent (I := I) (x := x) β := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_add, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma dualToCotangent_smulC {x : M} (c : ℝ) (α : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (c • α)
      = c • dualToCotangent (I := I) (x := x) α := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_smul, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma dualToCotangent_subC {x : M} (α β : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (α - β)
      = dualToCotangent (I := I) (x := x) α - dualToCotangent (I := I) (x := x) β := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_sub, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

private def alignedPrincipalEndo (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun v => inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun v v' => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (v + v') :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v' :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_add]]
    rw [dualToCotangent_addC]
    rw [map_add]
  map_smul' := fun c v => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (c • v) :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      c • (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_smul]]
    rw [dualToCotangent_smulC]
    rw [map_smul]; rfl

private def g1PrincipalVec (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₁)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))

private def alignedPrincipalCorrectionVec (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v +
                PDE.DeTurck.connDiff (I := I) g₁ g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma alignedPrincipalEndoC_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    alignedPrincipalEndo (I := I) (M := M) g₀ g₁ Z Y x v =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma g1Principal_splitC
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    g1PrincipalVec (I := I) (M := M) g₀ g₁ Z Y x v =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
        + alignedPrincipalCorrectionVec (I := I) (M := M) g₀ g₁ Z Y x v := by
  classical
  rw [g1PrincipalVec, alignedPrincipalCorrectionVec]
  rw [← map_add]
  congr 1
  rw [← dualToCotangent_addC]
  congr 1
  ext w
  rw [LinearMap.add_apply]
  set Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩ with hXfdef
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  have halign := covDerivConnDiff_principal_align (I := I) (M := M) g₀ g₁ Xf Y Z x w
  rw [hXfx] at halign
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, halign]
  rw [show ((-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v +
                PDE.DeTurck.connDiff (I := I) g₁ g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) w) =
      -(cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)) from rfl]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma alignedPrincipalEndoC_inner_secondKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v ζ : TangentSpace I x) :
    g₁.inner x (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ Z Y x v) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![v, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![v, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![v, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) := by
  classical
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  rw [alignedPrincipalEndoC_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ ζ, cotangentToDualLinear_apply]
  rw [← hXfx]
  have hbridge := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ g₁ S hbil Xf Y Z x ζ
  rw [hXfx]
  rw [hXfx] at hbridge
  rw [hbridge]

def secondKoszulFrameRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ k : Fin (Module.finrank ℝ E),
      (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
          ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
        - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), Y x]
        - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(Module.finBasis ℝ E) k, Z x,
              (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))])

omit [NeZero (Module.finrank ℝ E)] in
private lemma alignedPrincipalEndoC_trace_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ Z Y x) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![Z x, Y x]
        + secondKoszulFrameRemainder (I := I) (M := M) g₀ g₁ S Z Y x := by
  classical
  rw [← trace_eq_cometricLmodel_pairing_sum (I := I) (M := M) g₁ x (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ Z Y x)]
  rw [covDerivConnDiff_tracedPrincipal_eq_appCc (I := I) (M := M) g₀ g₁ S x ![Z x, Y x]]
  rw [secondKoszulFrameRemainder]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x
          (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ Z Y x
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), Z x, Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), Y x, Z x, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(Module.finBasis ℝ E) k, Z x,
                  (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))])) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact alignedPrincipalEndoC_inner_secondKoszul (I := I) (M := M) g₀ g₁ S hbil Z Y x
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1

def alignedPrincipalCorrectionTrace (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalCorrectionVec (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i

def palatiniTracedPrincipalRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  secondKoszulFrameRemainder (I := I) (M := M) g₀ g₁ S Z Y x
    + alignedPrincipalCorrectionTrace (I := I) (M := M) g₀ g₁ Z Y x

omit [NeZero (Module.finrank ℝ E)] in
theorem palatini_tracedPrincipal_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![Z x, Y x]
        + palatiniTracedPrincipalRemainder (I := I) (M := M) g₀ g₁ S Z Y x := by
  classical

  have hsumeq : (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignedPrincipalCorrectionVec (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit := g1Principal_splitC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)
    rw [g1PrincipalVec] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply]
    rw [← alignedPrincipalEndoC_apply]
  rw [hsumeq, Finset.sum_add_distrib]
  rw [trace_eq_basis_repr_sum (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ Z Y x)]
  rw [alignedPrincipalEndoC_trace_eq (I := I) (M := M) g₀ g₁ S hbil Z Y x]
  rw [palatiniTracedPrincipalRemainder, alignedPrincipalCorrectionTrace]
  ring

def koszulZSlotPerm1 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans ((Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1))

def koszulZSlotPerm2 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)

def koszulZSlotPerm3 : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2


private theorem zSlotPerm_apply :
    (koszulZSlotPerm1 0 = 2 ∧ koszulZSlotPerm1 1 = 0 ∧ koszulZSlotPerm1 2 = 3 ∧ koszulZSlotPerm1 3 = 1) ∧
    (koszulZSlotPerm2 0 = 2 ∧ koszulZSlotPerm2 1 = 3 ∧ koszulZSlotPerm2 2 = 0 ∧ koszulZSlotPerm2 3 = 1) ∧
    (koszulZSlotPerm3 0 = 2 ∧ koszulZSlotPerm3 1 = 1 ∧ koszulZSlotPerm3 2 = 0 ∧ koszulZSlotPerm3 3 = 3) := by
  unfold koszulZSlotPerm1 koszulZSlotPerm2 koszulZSlotPerm3
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

noncomputable def combinedTrace42ModelZSlot
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel 4 ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E :=
  (1 / 2 : ℝ) •
    ((modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            koszulZSlotPerm1).toContinuousLinearEquiv.toContinuousLinearMap)
      + (modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            koszulZSlotPerm2).toContinuousLinearEquiv.toContinuousLinearMap)
      - (modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            koszulZSlotPerm3).toContinuousLinearEquiv.toContinuousLinearMap))


omit [NeZero (Module.finrank ℝ E)] in
theorem combinedTrace42ModelZ_apply
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42ModelZSlot (E := E) L D m =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (D ![m 0, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)), m 1, (Module.finBasis ℝ E) k]
            + D ![m 0, m 1, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
            - D ![m 0, (Module.finBasis ℝ E) k, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), m 1]) := by
  classical
  have hcongr_eq : ∀ (σ : Equiv.Perm (Fin 4)) (D' : Tensor0SBundle.Tensor0SModel 4 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap D' =
        ContinuousMultilinearMap.domDomCongr σ D' := by
    intro σ D'
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl

  have htrace : ∀ (σ : Equiv.Perm (Fin 4)) (tup : Fin (Module.finrank ℝ E) → Fin 4 → E)
      (_htup : ∀ k, (fun j =>
        (![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, m 0, m 1] :
          Fin 4 → E) (σ j)) = tup k),
      modelDoubleTrace (E := E) 2 L
          (ContinuousMultilinearMap.domDomCongr σ D) m =
        ∑ k : Fin (Module.finrank ℝ E), D (tup k) := by
    intro σ tup htup
    rw [modelDoubleTrace_apply (E := E) 2 L _ m]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) m) : Fin 4 → E) =
        ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, m 0, m 1] from by
      funext j; fin_cases j <;> rfl]
    rw [← htup k]
  rw [combinedTrace42ModelZSlot]
  rw [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hcongr_eq, hcongr_eq, hcongr_eq]
  rw [htrace koszulZSlotPerm1 (fun k => ![m 0, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), m 1, (Module.finBasis ℝ E) k]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [koszulZSlotPerm1, Fin.isValue, Equiv.trans_apply, Equiv.swap_apply_def] <;> rfl)]
  rw [htrace koszulZSlotPerm2 (fun k => ![m 0, m 1, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [koszulZSlotPerm2, Fin.isValue, Equiv.trans_apply, Equiv.swap_apply_def] <;> rfl)]
  rw [htrace koszulZSlotPerm3 (fun k => ![m 0, (Module.finBasis ℝ E) k,
        L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), m 1]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [koszulZSlotPerm3, Fin.isValue, Equiv.swap_apply_def] <;> rfl)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

noncomputable def ricciArmPrincipalCoeffZSlotFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 2 x).symm.toContinuousLinearMap.comp
    ((combinedTrace42ModelZSlot (E := E) (cometricLmodel (I := I) g₁ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem ricciArmPrincipalCoeffZFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmPrincipalCoeffZSlotFib (I := I) g₁ x D) =
      combinedTrace42ModelZSlot (E := E) (cometricLmodel (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem ricciArmPrincipalCoeffZFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (ricciArmPrincipalCoeffZSlotFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => ricciArmPrincipalCoeffZSlotFib (I := I) g₁ x)
  intro Y

  have hreindex : ∀ (ρ : Equiv.Perm (Fin 4))
      (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 4 I x)
      (_hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x (Z x))),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr ρ
              (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
    intro ρ Z hZ
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
            Tensor0SBundle.Tensor0SSpace 4 I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Z x)).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr ρ
        (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl

  have hcdt : ∀ (ρ : Equiv.Perm (Fin 4)),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
          ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x)
            (Tensor0SBundle.Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.domDomCongr ρ
                (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))) := by
    intro ρ
    exact ContMDiff.clm_bundle_apply (b := id)
      (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) (hreindex ρ (fun x => Y x) Y.contMDiff)

  have hcomb := (((hcdt koszulZSlotPerm1).add_section (hcdt koszulZSlotPerm2)).sub_section
    (hcdt koszulZSlotPerm3)).const_smul_section (a := (1 / 2 : ℝ))
  refine hcomb.congr (fun x => ?_)
  have hfib : ricciArmPrincipalCoeffZSlotFib (I := I) g₁ x (Y x) =
      (1 / 2 : ℝ) •
        (((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr koszulZSlotPerm1
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))
            + (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
                (Tensor0SBundle.Tensor0SSpace.ofModel
                  (ContinuousMultilinearMap.domDomCongr koszulZSlotPerm2
                    (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
          - (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr koszulZSlotPerm3
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [ricciArmPrincipalCoeffZFib_toModel]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [combinedTrace42ModelZSlot]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) hfib.symm

noncomputable def ricciArmPrincipalCoeffZSlot (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffZSlotFib (I := I) g₁ x)
      contMDiff_toFun := ricciArmPrincipalCoeffZFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem ricciArmPrincipalCoeffZ_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffZSlotFib (I := I) g₁ x) := rfl


omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁) W) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 W x
              ![v 0, cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 W x
                ![v 0, v 1, cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 W x
                ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), v 1]) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeffZ_toSection, ricciArmPrincipalCoeffZFib_toModel,
    combinedTrace42ModelZ_apply (E := E) (cometricLmodel (I := I) g₁ x)]
  rfl

private def secondCovGradZSlotCovec (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e : TangentSpace I x) :
    TangentSpace I x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ζ => (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x])
      map_add' := by
        intro ζ ζ'
        have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, e, W x, ζ + ζ'] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ'] := by
          rw [show (![V x, e, W x, ζ + ζ'] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, e, W x, ζ] 3 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, e, W x, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, e, W x, ζ] 3 ζ' : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ'] from by
              funext j; fin_cases j <;> rfl]
        have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, W x, e, ζ + ζ'] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ'] := by
          rw [show (![V x, W x, e, ζ + ζ'] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, W x, e, ζ] 3 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, W x, e, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, W x, e, ζ] 3 ζ' : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ'] from by
              funext j; fin_cases j <;> rfl]
        have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, ζ + ζ', e, W x] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ', e, W x] := by
          rw [show (![V x, ζ + ζ', e, W x] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, ζ, e, W x] 1 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, ζ, e, W x] 1 ζ : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, ζ, e, W x] 1 ζ' : Fin 4 → TangentSpace I x) = ![V x, ζ', e, W x] from by
              funext j; fin_cases j <;> rfl]
        rw [h1, h2, h3]; ring
      map_smul' := by
        intro c ζ
        have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, e, W x, c • ζ] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ] := by
          rw [show (![V x, e, W x, c • ζ] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, e, W x, ζ] 3 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, e, W x, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
              funext j; fin_cases j <;> rfl]
        have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, W x, e, c • ζ] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ] := by
          rw [show (![V x, W x, e, c • ζ] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, W x, e, ζ] 3 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, W x, e, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
              funext j; fin_cases j <;> rfl]
        have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, c • ζ, e, W x] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x] := by
          rw [show (![V x, c • ζ, e, W x] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, ζ, e, W x] 1 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, ζ, e, W x] 1 ζ : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
              funext j; fin_cases j <;> rfl]
        rw [h1, h2, h3]
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma zPrincipalCovec_apply (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]) := rfl


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma zPrincipalCovec_add (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e e' : TangentSpace I x) :
    secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x (e + e') =
      secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e
        + secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e' := by
  ext ζ
  rw [ContinuousLinearMap.add_apply, zPrincipalCovec_apply, zPrincipalCovec_apply,
    zPrincipalCovec_apply]
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, e + e', W x, ζ] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e', W x, ζ] := by
    rw [show (![V x, e + e', W x, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, e, W x, ζ] 1 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, e, W x, ζ] 1 e : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, e, W x, ζ] 1 e' : Fin 4 → TangentSpace I x) = ![V x, e', W x, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, W x, e + e', ζ] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e', ζ] := by
    rw [show (![V x, W x, e + e', ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, W x, e, ζ] 2 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, W x, e, ζ] 2 e : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, W x, e, ζ] 2 e' : Fin 4 → TangentSpace I x) = ![V x, W x, e', ζ] from by
        funext j; fin_cases j <;> rfl]
  have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, ζ, e + e', W x] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e', W x] := by
    rw [show (![V x, ζ, e + e', W x] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, ζ, e, W x] 2 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, ζ, e, W x] 2 e : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, ζ, e, W x] 2 e' : Fin 4 → TangentSpace I x) = ![V x, ζ, e', W x] from by
        funext j; fin_cases j <;> rfl]
  rw [h1, h2, h3]; ring


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma zPrincipalCovec_smul (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (c : ℝ) (e : TangentSpace I x) :
    secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x (c • e) =
      c • secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e := by
  ext ζ
  rw [ContinuousLinearMap.smul_apply, zPrincipalCovec_apply, zPrincipalCovec_apply]
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, c • e, W x, ζ] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ] := by
    rw [show (![V x, c • e, W x, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, e, W x, ζ] 1 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, e, W x, ζ] 1 e : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, W x, c • e, ζ] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ] := by
    rw [show (![V x, W x, c • e, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, W x, e, ζ] 2 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, W x, e, ζ] 2 e : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, ζ, c • e, W x] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x] := by
    rw [show (![V x, ζ, c • e, W x] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, ζ, e, W x] 2 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, ζ, e, W x] 2 e : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
        funext j; fin_cases j <;> rfl]
  rw [h1, h2, h3]
  simp only [smul_eq_mul]; ring

def alignedPrincipalEndoZSlot (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun e => inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      ((secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun e e' => by
    rw [show ((secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x (e + e') :
          TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
        ((secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
          ((secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e' :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w
      rw [LinearMap.add_apply]
      change secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x (e + e') w =
        secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e w
          + secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e' w
      rw [zPrincipalCovec_add]; rfl]
    rw [dualToCotangent_addC, map_add]
  map_smul' := fun c e => by
    rw [show ((secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x (c • e) :
          TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
        c • ((secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w
      rw [LinearMap.smul_apply]
      change secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x (c • e) w =
        c • secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e w
      rw [zPrincipalCovec_smul]; rfl]
    rw [dualToCotangent_smulC, map_smul]; rfl


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma alignedPrincipalEndoCZ_inner (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    g₁.inner x (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x e) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]) := by
  change g₁.inner x (inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      ((secondCovGradZSlotCovec (I := I) (M := M) g₀ S V W x e :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) ζ = _
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ ζ, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent]
  exact zPrincipalCovec_apply (I := I) (M := M) g₀ S V W x e ζ


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma alignedPrincipalEndoCZ_trace_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![V x, W x] := by
  classical
  rw [← trace_eq_cometricLmodel_pairing_sum (I := I) (M := M) g₁ x (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x)]
  rw [ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x]]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [alignedPrincipalEndoCZ_inner (I := I) (M := M) g₀ g₁ S V W x
    (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]


omit [NeZero (Module.finrank ℝ E)] in
theorem alignedPrincipalEndoC_sub_endoCZ_inner (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    g₁.inner x
        (alignedPrincipalEndo (I := I) (M := M) g₀ g₁
            (⟨smoothExtensionTangent (I := I) x e, smoothExtensionTangent_contMDiff (I := I) x e⟩) W x (V x)
          - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x e) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), W x, ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![e, (LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x), ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x), e, ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![W x, (LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), ζ]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![ζ, (LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), W x]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![ζ, e, (LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x)]) := by
  classical
  set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x e, smoothExtensionTangent_contMDiff (I := I) x e⟩ with hei
  have heix : ei x = e := smoothExtensionTangent_eq (I := I) x e
  rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [alignedPrincipalEndoC_inner_secondKoszul (I := I) (M := M) g₀ g₁ S hbil ei W x (V x) ζ]
  rw [alignedPrincipalEndoCZ_inner (I := I) (M := M) g₀ g₁ S V W x e ζ]
  rw [heix]
  ring

def palatiniTracedPrincipalZRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalEndo (I := I) (M := M) g₀ g₁
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)
        - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i)
  + (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalCorrectionVec (I := I) (M := M) g₀ g₁
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)) i)


omit [NeZero (Module.finrank ℝ E)] in
theorem palatini_tracedPrincipal_Zslot_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![V x, W x]
        + palatiniTracedPrincipalZRemainder (I := I) (M := M) g₀ g₁ S V W x := by
  classical
  rw [← alignedPrincipalEndoCZ_trace_eq (I := I) (M := M) g₀ g₁ S V W x]
  rw [← trace_eq_basis_repr_sum (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x)]
  rw [palatiniTracedPrincipalZRemainder]

  have hsumeq : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
          + ((chartModelBasis E).repr
              (alignedPrincipalEndo (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)
                - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
            + (chartModelBasis E).repr
                (alignedPrincipalCorrectionVec (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)) i) := by
    intro i
    set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hei
    have hsplit := g1Principal_splitC (I := I) (M := M) g₀ g₁ ei W x (V x)
    rw [g1PrincipalVec] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply, ← alignedPrincipalEndoC_apply]
    rw [show (chartModelBasis E).repr
          (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ ei W x (V x)) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignedPrincipalEndo (I := I) (M := M) g₀ g₁ ei W x (V x)
                - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i from by
      rw [map_sub, Finsupp.sub_apply]; ring]
    rw [add_assoc]
  rw [Finset.sum_congr rfl fun i _ => hsumeq i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
