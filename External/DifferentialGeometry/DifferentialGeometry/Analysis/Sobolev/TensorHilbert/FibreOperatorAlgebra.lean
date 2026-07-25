import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import DifferentialGeometry.Tensor.Auxiliary.BanachAlgebraSmoothness


noncomputable section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.FibreOperatorAlgebra

open DifferentialGeometry.Analysis.BanachAlgebraSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]

abbrev FibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) : Type _ :=
  Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀

instance instNormedRingFibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) :
    NormedRing (FibreOpL2Algebra (I := I) (M := M) g₀) :=
  inferInstanceAs (NormedRing (Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀))

instance instNormedAlgebraFibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) :
    NormedAlgebra ℝ (FibreOpL2Algebra (I := I) (M := M) g₀) :=
  inferInstanceAs (NormedAlgebra ℝ (Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀))

instance instCompleteSpaceFibreOpL2Algebra (g₀ : SmoothRiemannianMetric I M) :
    CompleteSpace (FibreOpL2Algebra (I := I) (M := M) g₀) :=
  inferInstanceAs (CompleteSpace (Integral.L2.TensorL2 0 2 g₀ →L[ℝ] Integral.L2.TensorL2 0 2 g₀))

section Neumann

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Dom : Type*} [NormedAddCommGroup Dom] [NormedSpace ℝ Dom]


omit [InnerProductSpace ℝ E] in
theorem contDiffOn_inverseGram_clm
    (g₀ : SmoothRiemannianMetric I M) {s : Set Dom}
    {L : Dom →L[ℝ] FibreOpL2Algebra (I := I) (M := M) g₀}
    {c : FibreOpL2Algebra (I := I) (M := M) g₀} {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x) * c) s :=
  contDiffOn_oneSub_inverse_clm_mul_const (A := FibreOpL2Algebra (I := I) (M := M) g₀) hlt

omit [InnerProductSpace ℝ E] in
theorem contDiffOn_inverseGram_entry_clm
    (g₀ : SmoothRiemannianMetric I M) {s : Set Dom}
    {L : Dom →L[ℝ] FibreOpL2Algebra (I := I) (M := M) g₀}
    {c : FibreOpL2Algebra (I := I) (M := M) g₀}
    (Φ : FibreOpL2Algebra (I := I) (M := M) g₀ →L[ℝ] F) {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Φ (Ring.inverse (1 - L x) * c)) s :=
  contDiffOn_continuousLinearMap_comp_oneSub_inverse_clm
    (A := FibreOpL2Algebra (I := I) (M := M) g₀) Φ hlt

omit [InnerProductSpace ℝ E] in
theorem contDiffOn_inverseGram_of_uniform_bound
    (g₀ : SmoothRiemannianMetric I M) {s : Set Dom}
    {L : Dom →L[ℝ] FibreOpL2Algebra (I := I) (M := M) g₀}
    {c : FibreOpL2Algebra (I := I) (M := M) g₀} {δ : ℝ} {n : WithTop ℕ∞}
    (hδ : δ < 1) (hbound : ∀ x ∈ s, ‖L x‖ ≤ δ) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x) * c) s :=
  contDiffOn_inverseGram_clm (I := I) (M := M) g₀
    (fun x hx => lt_of_le_of_lt (hbound x hx) hδ)

end Neumann

end DifferentialGeometry.Analysis.FibreOperatorAlgebra

end
