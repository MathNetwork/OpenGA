import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.CompactResolvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalPartMatch


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def realizeToL2 (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2)) :
    tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2) →L[ℝ]
      TensorL2 0 2 g_bg :=
  tensorHsToL2 (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
    h_compact (by have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem realizeToL2_opNorm_le_one (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2)) :
    ‖realizeToL2 (I := I) (M := M) g_bg a h_compact‖ ≤ 1 :=
  tensorHsToL2_opNorm_le_one (I := I) (M := M)
    (g := g_bg) (r := 0) (s := 2)
    (by have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem realizeToL2_tensorL2Coeff_ofCompact
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2))
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2) :
    tensorL2Coeff (I := I) (M := M) h_compact
        (realizeToL2 (I := I) (M := M) g_bg a h_compact u) i = u.coeff i :=
  tensorHsToL2_tensorL2Coeff (I := I) (M := M)
    (by have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a; linarith) u i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem realizeToL2_zero (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (h_compact : IsCompactOperator
      (tensorResolventL2 (I := I) (M := M) g_bg 0 2)) :
    realizeToL2 (I := I) (M := M) g_bg a h_compact 0 = 0 :=
  map_zero _

def firstOrderRemainderInclusion (g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →L[ℝ]
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
  tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
    (by linarith : (a : ℝ) ≤ (a : ℝ) + 1)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem firstOrderRemainderInclusion_opNorm_le_one
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    ‖firstOrderRemainderInclusion (I := I) (M := M) g_bg a‖ ≤ 1 :=
  tensorHsInclusion_opNorm_le_one (I := I) (M := M)
    (g := g_bg) (r := 0) (s := 2) (by linarith)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem firstOrderRemainderInclusion_coeff
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (v : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (i : TensorEigenIdx (I := I) (M := M) g_bg 0 2) :
    (firstOrderRemainderInclusion (I := I) (M := M) g_bg a v).coeff i =
      v.coeff i :=
  tensorHsInclusion_coeff_apply (I := I) (M := M) (by linarith) v i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem firstOrderRemainder_lands_in_Ha
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (R : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2) →L[ℝ]
      tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1)) :
    ∃ R' : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2) →L[ℝ]
        tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ),
      (∀ u, (R' u).coeff = (R u).coeff) ∧ ‖R'‖ ≤ ‖R‖ := by
  refine ⟨(firstOrderRemainderInclusion (I := I) (M := M) g_bg a).comp R,
    ?_, ?_⟩
  · intro u
    funext i
    simp [firstOrderRemainderInclusion_coeff]
  · calc ‖(firstOrderRemainderInclusion (I := I) (M := M) g_bg a).comp R‖
        ≤ ‖firstOrderRemainderInclusion (I := I) (M := M) g_bg a‖ * ‖R‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖R‖ :=
          mul_le_mul_of_nonneg_right
            (firstOrderRemainderInclusion_opNorm_le_one (I := I) (M := M) g_bg a)
            (norm_nonneg _)
      _ = ‖R‖ := one_mul _

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem deTurckNonlinearitySpectral_principalPart_cancels
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = - DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg x ξ t :=
  deturck_ricci_principal_symbol_matches_rough_laplacian_of_symm
    (I := I) g₀ g_bg x ξ t ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
