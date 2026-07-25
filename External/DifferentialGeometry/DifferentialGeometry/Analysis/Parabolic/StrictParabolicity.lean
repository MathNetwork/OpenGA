import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSymbol
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionSymbol
import DifferentialGeometry.Geometry.Flow.DeTurckOperator

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def deTurckSymbol (g g' : SmoothRiemannianMetric I M) : TensorSymbol (E := E) I M :=
  fun x ξ => (-2 : ℝ) • ricciSymbol (I := I) g x ξ +
    deTurckCorrectionSymbol (I := I) g g' x ξ

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckSymbol_def (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    deTurckSymbol (I := I) g g' x ξ =
      (-2 : ℝ) • ricciSymbol (I := I) g x ξ +
        deTurckCorrectionSymbol (I := I) g g' x ξ := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckSymbol_apply (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckSymbol (I := I) g g' x ξ t =
      (-2 : ℝ) • ricciSymbol (I := I) g x ξ t +
        deTurckCorrectionSymbol (I := I) g g' x ξ t := by
  rw [deTurckSymbol_def, LinearMap.add_apply, LinearMap.smul_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckSymbol_apply_apply (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    (deTurckSymbol (I := I) g g' x ξ t) v w =
      -2 * (ricciSymbol (I := I) g x ξ t) v w +
        (deTurckCorrectionSymbol (I := I) g g' x ξ t) v w := by
  rw [deTurckSymbol_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContraction_eq_snd_of_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ t k =
      raisedFormContractionSnd (I := I) g x ξ t k :=
  (raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht k).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_apply_apply_eq_isotropic_of_symm (g g' : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i k : Fin (Module.finrank ℝ E)) :
    (deTurckSymbol (I := I) g g' x ξ t)
        ((chartModelBasis E) i) ((chartModelBasis E) k) =
      metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k := by
  rw [deTurckSymbol_apply_apply]
  rw [ricciSymbol_apply_eq_closedForm (I := I) g x ξ t i k,
    deTurckCorrectionSymbol_apply_eq_closedForm (I := I) g g' x ξ t i k]
  rw [raisedFormContraction_eq_snd_of_symm (I := I) g x ξ t ht k]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_apply_eq_smul_of_symm (g g' : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g g' x ξ t =
      metricCovectorNormSq (I := I) g x ξ • t := by
  refine LinearMap.ext_basis (chartModelBasis E) (chartModelBasis E) (fun i k => ?_)
  calc (deTurckSymbol (I := I) g g' x ξ t)
          ((chartModelBasis E) i) ((chartModelBasis E) k)
      = metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k :=
        deTurckSymbol_apply_apply_eq_isotropic_of_symm (I := I) g g' x ξ t ht i k
    _ = (metricCovectorNormSq (I := I) g x ξ • t)
          ((chartModelBasis E) i) ((chartModelBasis E) k) := by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, formComp_def]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_isStrictlyParabolic_of_symm (g g' : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g g' x ξ t =
        metricCovectorNormSq (I := I) g x ξ • t ∧
      0 < metricCovectorNormSq (I := I) g x ξ :=
  ⟨deTurckSymbol_apply_eq_smul_of_symm (I := I) g g' x ξ t ht,
    metricCovectorNormSq_pos (I := I) g x hξ⟩

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_eq_neg_laplacianSymbolCoeff_smul_of_symm
    (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g g' x ξ t =
      (-(deTurckSymbolCoeff (I := I) g x ξ)) • t := by
  rw [deTurckSymbol_apply_eq_smul_of_symm (I := I) g g' x ξ t ht, deTurckSymbolCoeff_apply,
    neg_neg]

end DeTurck
end PDE
end DifferentialGeometry
