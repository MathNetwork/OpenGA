import DifferentialGeometry.Geometry.Metric.SmoothVectorFieldExtGlobal
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic














noncomputable section


open Set Function Filter Manifold Bundle
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [ConnectedSpace M] in
theorem exists_gradVariation
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (q pt : M) (u : TangentSpace I q) (L : ℝ) (hL : 0 < L)
    (hgL : intrinsicGeodesic (I := I) g hEnorm q u L = pt)
    (w : TangentSpace I q) :
    ∃ f : ℝ → ℝ → M, IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = intrinsicGeodesic (I := I) g hEnorm q u t) ∧
      (∀ s : ℝ, f s L = pt) ∧
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s 0) 0 (1 : ℝ) : E) = (w : E) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q u with hγ
  have hγ_geo : IsGeodesic (I := I) g γ := intrinsicGeodesic_isGeodesic (I := I) g hEnorm q u
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm q u
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := isGeodesic_contMDiff (I := I) g hγ_geo hγ_cont
  have hγ0 : γ 0 = q := intrinsicGeodesic_zero (I := I) g hEnorm q u
  obtain ⟨X, hXsm, hXq⟩ := exists_contMDiff_vectorField_eq (I := I) q w
  set V : ℝ → E := fun t => (1 - t / L) • (X (γ t) : E) with hV
  have hbase : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (γ t) (X (γ t))) :=
    hXsm.comp hγ_smooth
  have hχ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 - t / L) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  have hVbundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t : ℝ => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (γ t) (V t)) :=
    contMDiff_smul_bundleField (I := I) hγ_smooth hχ hbase
  have hVL : V L = 0 := by
    change (1 - L / L) • X (γ L) = 0
    rw [div_self hL.ne', sub_self, zero_smul]
  obtain ⟨f, hf, hf0, hfderiv, hfixL⟩ :=
    exists_expVar_fixEnd (I := I) g hEnorm γ V L hγ_smooth hVbundle hVL
  refine ⟨f, hf, hf0, ?_, ?_⟩
  · intro s
    rw [hfixL s, hγ]; exact hgL
  · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_refl _, le_of_lt hL⟩
    have hd := hfderiv 0 h0
    rw [hd, hV]
    simp only [zero_div, sub_zero, one_smul]
    rw [hγ0]
    exact hXq

end Riemannian
end Geometry
end DifferentialGeometry

end
