import DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.Polarised


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BochnerPolarisedLpSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarised

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma contMDiff_phi_add_v
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) :=
  φ.contMDiff.add v.contMDiff

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma contMDiff_phi_sub_v
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) :=
  φ.contMDiff.sub v.contMDiff

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_g_inner_grad_phi_grad_v
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b
      (gradFun (I := I) g (φ : M → ℝ) b)
      (gradFun (I := I) g (v : M → ℝ) b)) := by
  have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
    (grad_g (I := I) g φ.contMDiff) (grad_g (I := I) g v.contMDiff)
  refine h.congr ?_
  intro b
  rw [grad_g_apply, grad_g_apply]

omit [CompactSpace M] in
theorem bochner_polarised_pointwise_smoothCase
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    Δ_g (I := I) g (contMDiff_g_inner_grad_phi_grad_v
        (I := I) (M := M) g φ v) x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
        g.inner x
          (gradFun (I := I) g (v : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x) +
        2 * hessPairingChart (I := I) g φ v x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) :=
  bochner_polarised_pointwise (I := I) (M := M) g φ v
    (contMDiff_phi_add_v (I := I) (M := M) φ v)
    (contMDiff_phi_sub_v (I := I) (M := M) φ v)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v) x

omit [CompactSpace M] in
theorem bochner_polarised_pointwise_oneSubLap_smoothCase
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) -
      Δ_g (I := I) g (contMDiff_g_inner_grad_phi_grad_v
        (I := I) (M := M) g φ v) x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (v : M → ℝ) x)
        - g.inner x
            (gradFun (I := I) g (v : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)
        - g.inner x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x)
        - 2 * hessPairingChart (I := I) g φ v x
        - 2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) :=
  bochner_polarised_pointwise_oneSubLap (I := I) (M := M) g φ v
    (contMDiff_phi_add_v (I := I) (M := M) φ v)
    (contMDiff_phi_sub_v (I := I) (M := M) φ v)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v) x

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerSmoothBundle_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (b : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) :=
  rfl

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (x : M) :
    Δ_g (I := I) g (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth x =
      Δ_g (I := I) g (contMDiff_g_inner_grad_phi_grad_v
        (I := I) (M := M) g φ ⟨v.toFun, v.smooth⟩) x := by
  apply Δ_g_congr_func

end BochnerPolarisedLpSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
