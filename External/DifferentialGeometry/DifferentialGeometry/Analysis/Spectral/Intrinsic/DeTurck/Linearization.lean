import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionSymbol
import DifferentialGeometry.Analysis.Parabolic.StrictParabolicity
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic

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
theorem deturck_ricci_rhs_linearization_at_g0 [I.Boundaryless]
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
      σ = DifferentialGeometry.PDE.DeTurck.isotropicSymbol
            (E := E)
            (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
            (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) ∧
      DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        g₀ σ :=
  ⟨DifferentialGeometry.PDE.DeTurck.isotropicSymbol
      (E := E)
      (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
      (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀),
    rfl,
    DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_hasPrincipalSymbol_at_self g₀ g_bg⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
