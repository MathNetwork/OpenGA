import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Linearization


namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRicciRHS_principalSymbol_eq_roughLaplacianSymbol [I.Boundaryless]
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
      σ = DifferentialGeometry.PDE.DeTurck.isotropicSymbol
            (E := E)
            (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
            (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) ∧
      DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        g₀ σ :=
  deturck_ricci_rhs_linearization_at_g0 (I := I) g_bg g₀

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckRicciRHS_symbolCoeff_eq_covectorNormSq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀ x ξ =
      -DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ :=
  DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply (I := I) g₀ x ξ

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckRicciRHS_principalSymbol_apply_eq_smul
    (g₀ : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = (-DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ)
          • t := by
  rw [DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deturck_ricci_principal_symbol_matches_rough_laplacian_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = - DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg x ξ t :=
  DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_principal_symbol_equals_deTurckSymbol
    (I := I) g₀ g_bg x ξ t ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
