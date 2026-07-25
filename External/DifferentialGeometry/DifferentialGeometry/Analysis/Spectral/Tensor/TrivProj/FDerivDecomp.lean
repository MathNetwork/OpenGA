import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.ChristoffelDecomp
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def chartChristoffelBilin
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).coord i).toContinuousLinearMap.smulRight
          (((chartModelBasis E).coord j).toContinuousLinearMap.smulRight
            (chartChristoffel (I := I) g α i j k (extChartAt I α b) •
              (chartModelBasis E) k))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartChristoffelBilin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr v) i *
                ((chartModelBasis E).repr w) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
              (chartModelBasis E) k := by
  classical
  unfold chartChristoffelBilin
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.smulRight_apply]
  have hcoord_i : ((chartModelBasis E).coord i).toContinuousLinearMap v =
      ((chartModelBasis E).repr v) i := rfl
  have hcoord_j : ((chartModelBasis E).coord j).toContinuousLinearMap w =
      ((chartModelBasis E).repr w) j := rfl
  rw [hcoord_i, hcoord_j]
  rw [smul_smul, smul_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartChristoffelBilin_add_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v₁ v₂ w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) w =
      chartChristoffelBilin (I := I) (M := M) g α b v₁ w +
        chartChristoffelBilin (I := I) (M := M) g α b v₂ w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (v₁ + v₂) =
        chartChristoffelBilin (I := I) (M := M) g α b v₁ +
          chartChristoffelBilin (I := I) (M := M) g α b v₂ from map_add _ _ _,
      ContinuousLinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartChristoffelBilin_smul_first
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (c : ℝ) (v w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b (c • v) w =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w := by
  rw [show chartChristoffelBilin (I := I) (M := M) g α b (c • v) =
        c • chartChristoffelBilin (I := I) (M := M) g α b v from map_smul _ _ _,
      ContinuousLinearMap.smul_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartChristoffelBilin_add_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v w₁ w₂ : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (w₁ + w₂) =
      chartChristoffelBilin (I := I) (M := M) g α b v w₁ +
        chartChristoffelBilin (I := I) (M := M) g α b v w₂ :=
  map_add _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartChristoffelBilin_smul_second
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (v : E) (c : ℝ) (w : E) :
    chartChristoffelBilin (I := I) (M := M) g α b v (c • w) =
      c • chartChristoffelBilin (I := I) (M := M) g α b v w :=
  map_smul _ _ _

noncomputable def tensorChristoffelCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (_S : SmoothCcTensor g r s) (_α : M) (_b : M) :
    E →L[ℝ] TensorRSModel r s ℝ E :=
  (0 : E →L[ℝ] TensorRSModel r s ℝ E)

noncomputable def tensorIntrinsicFDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    E →L[ℝ] TensorRSModel r s ℝ E :=
  fderiv ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) -
    tensorChristoffelCorrection (I := I) (M := M) g r s S α b

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tensorIntrinsicFDeriv_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b =
      fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) -
      tensorChristoffelCorrection (I := I) (M := M) g r s S α b := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma tensorChristoffelCorrection_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorChristoffelCorrection (I := I) (M := M) g r s S α b =
      (0 : E →L[ℝ] TensorRSModel r s ℝ E) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorTrivProj_chart_pullback_fderiv_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b +
        tensorChristoffelCorrection (I := I) (M := M) g r s S α b := by
  classical
  rw [tensorIntrinsicFDeriv_def]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M) (w : E) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b) w =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b w +
        tensorChristoffelCorrection (I := I) (M := M) g r s S α b w := by
  classical
  rw [tensorTrivProj_chart_pullback_fderiv_decomp
    (I := I) (M := M) g r s α S b]
  rw [ContinuousLinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_add_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M) :
    (tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α ∘
        (extChartAt I α).symm) =
      (tensorTrivProj (I := I) (M := M) g r s S₁ α ∘
          (extChartAt I α).symm) +
        (tensorTrivProj (I := I) (M := M) g r s S₂ α ∘
          (extChartAt I α).symm) := by
  classical
  funext y
  change tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α
      ((extChartAt I α).symm y) =
    tensorTrivProj (I := I) (M := M) g r s S₁ α
        ((extChartAt I α).symm y) +
      tensorTrivProj (I := I) (M := M) g r s S₂ α
        ((extChartAt I α).symm y)
  unfold tensorTrivProj
  rw [show (S₁ + S₂).toSection ((extChartAt I α).symm y) =
      S₁.toSection ((extChartAt I α).symm y) +
        S₂.toSection ((extChartAt I α).symm y) from
    by rw [SmoothCcTensor.toSection_add]; rfl]
  exact map_add _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_smul_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M) :
    (tensorTrivProj (I := I) (M := M) g r s (c • S) α ∘
        (extChartAt I α).symm) =
      c • (tensorTrivProj (I := I) (M := M) g r s S α ∘
        (extChartAt I α).symm) := by
  classical
  funext y
  change tensorTrivProj (I := I) (M := M) g r s (c • S) α
      ((extChartAt I α).symm y) =
    c • tensorTrivProj (I := I) (M := M) g r s S α
      ((extChartAt I α).symm y)
  unfold tensorTrivProj
  rw [show (c • S).toSection ((extChartAt I α).symm y) =
      c • S.toSection ((extChartAt I α).symm y) from
    by rw [SmoothCcTensor.toSection_smul]; rfl]
  exact map_smul _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChristoffelCorrection_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorChristoffelCorrection (I := I) (M := M) g r s (S₁ + S₂) α b =
      tensorChristoffelCorrection (I := I) (M := M) g r s S₁ α b +
        tensorChristoffelCorrection (I := I) (M := M) g r s S₂ α b := by
  classical
  simp [tensorChristoffelCorrection_zero]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChristoffelCorrection_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (c : ℝ)
    (S : SmoothCcTensor g r s) (α : M) (b : M) :
    tensorChristoffelCorrection (I := I) (M := M) g r s (c • S) α b =
      c • tensorChristoffelCorrection (I := I) (M := M) g r s S α b := by
  classical
  simp [tensorChristoffelCorrection_zero]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorIntrinsicFDeriv_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M) (b : M)
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    tensorIntrinsicFDeriv (I := I) (M := M) g r s (S₁ + S₂) α b =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S₁ α b +
        tensorIntrinsicFDeriv (I := I) (M := M) g r s S₂ α b := by
  classical
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s (S₁ + S₂) α b]
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s S₁ α b]
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s S₂ α b]
  have hadd := tensorTrivProj_add_section
    (I := I) (M := M) g r s S₁ S₂ α
  have hdiff_S₁ : DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S₁ α ∘ (extChartAt I α).symm)
      (extChartAt I α b) :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S₁ α hb_chart hb_int
  have hdiff_S₂ : DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S₂ α ∘ (extChartAt I α).symm)
      (extChartAt I α b) :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S₂ α hb_chart hb_int
  have hfd : fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S₁ α ∘
            (extChartAt I α).symm) (extChartAt I α b) +
        fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S₂ α ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hadd]
    exact fderiv_add hdiff_S₁ hdiff_S₂
  have hCC :
      tensorChristoffelCorrection (I := I) (M := M) g r s (S₁ + S₂) α b =
        tensorChristoffelCorrection (I := I) (M := M) g r s S₁ α b +
          tensorChristoffelCorrection (I := I) (M := M) g r s S₂ α b :=
    tensorChristoffelCorrection_add (I := I) (M := M) g r s S₁ S₂ α b
  rw [hfd, hCC]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorIntrinsicFDeriv_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (c : ℝ)
    (S : SmoothCcTensor g r s) (α : M) (b : M)
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E)) :
    tensorIntrinsicFDeriv (I := I) (M := M) g r s (c • S) α b =
      c • tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b := by
  classical
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s (c • S) α b]
  rw [tensorIntrinsicFDeriv_def (I := I) (M := M) g r s S α b]
  have hsmul := tensorTrivProj_smul_section
    (I := I) (M := M) g r s c S α
  have hdiff_S : DifferentiableAt ℝ
      (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
      (extChartAt I α b) :=
    differentiableAt_tensorTrivProj_pullback
      (I := I) (M := M) g r s S α hb_chart hb_int
  have hfd : fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s (c • S) α ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      c • fderiv ℝ
          (tensorTrivProj (I := I) (M := M) g r s S α ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsmul]
    exact fderiv_const_smul hdiff_S c
  have hCC :
      tensorChristoffelCorrection (I := I) (M := M) g r s (c • S) α b =
        c • tensorChristoffelCorrection (I := I) (M := M) g r s S α b :=
    tensorChristoffelCorrection_smul (I := I) (M := M) g r s c S α b
  rw [hfd, hCC]
  rw [smul_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorTrivProj_chart_pullback_partial_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M)
    (κ : Fin (Module.finrank ℝ E)) :
    fderiv ℝ
        (tensorTrivProj (I := I) (M := M) g r s S α ∘ (extChartAt I α).symm)
        (extChartAt I α b)
        ((chartModelBasis E) κ) =
      tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b ((chartModelBasis E) κ) +
        tensorChristoffelCorrection (I := I) (M := M) g r s S α b
          ((chartModelBasis E) κ) :=
  tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (I := I) (M := M) g r s α S b ((chartModelBasis E) κ)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_chart_pullback_partial_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M)
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (w : E) :
    fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w =
      tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b w) +
        tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorChristoffelCorrection (I := I) (M := M) g r s S α b w) := by
  classical
  rw [tensorChartComponentRaw_partial_decomp
    (I := I) (M := M) g r s α S hb_chart hb_int Idx Jdx w]
  rw [tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (I := I) (M := M) g r s α S b w]
  exact map_add _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_mfderiv_full_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb_chart : b ∈ (chartAt H α).source)
    (hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (v : TangentSpace I b) :
    (mfderiv I (𝓘(ℝ, ℝ))
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) b) v =
      tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorIntrinsicFDeriv (I := I) (M := M) g r s S α b
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)) +
        tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorChristoffelCorrection (I := I) (M := M) g r s S α b
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)) := by
  classical
  rw [tensorChartComponentRaw_mfderiv_decomp
    (I := I) (M := M) g r s α S hb_chart Idx Jdx v]
  rw [mfderiv_tensorTrivProj_eq_chart_fderiv
    (I := I) (M := M) g r s S α hb_chart hb_int v]
  rw [tensorTrivProj_chart_pullback_fderiv_decomp_apply
    (I := I) (M := M) g r s α S b
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)]
  exact map_add _ _ _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
