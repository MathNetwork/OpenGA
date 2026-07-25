import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeChartAlphaSummandSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSqSummandChartAlphaBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_le_raw_components_on_pouTsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s),
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b) ≤
            C *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨C₃, hC₃_nn, hN3⟩ :=
    riemannianFiberNormSq_le_chartAlpha_summand_sum_on_pouTsupport
      (I := I) (M := M) g r s α
  obtain ⟨C₂, hC₂_nn, hN2⟩ :=
    fiberNormSqSummand_chartAlpha_le_raw_components_sq
      (I := I) (M := M) g r s α
  set cardIJ : ℝ := (n : ℝ) ^ r * (n : ℝ) ^ s with hcardIJ_def
  set C : ℝ := C₃ * cardIJ * C₂ with hC_def
  have hcardIJ_nn : 0 ≤ cardIJ := by
    refine mul_nonneg ?_ ?_
    · exact pow_nonneg (Nat.cast_nonneg n) r
    · exact pow_nonneg (Nat.cast_nonneg n) s
  have hC_nonneg : 0 ≤ C := by
    refine mul_nonneg (mul_nonneg hC₃_nn hcardIJ_nn) hC₂_nn
  refine ⟨C, hC_nonneg, ?_⟩
  intro S b hb
  set RawSq : ℝ :=
    ∑ Idx' : Fin r → Fin n,
      ∑ Jdx' : Fin s → Fin n,
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx' b) ^ 2
      with hRawSq_def
  have hRawSq_nn : 0 ≤ RawSq := by
    rw [hRawSq_def]
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    exact sq_nonneg _
  have hA :
      riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b) ≤
        C₃ *
          (∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
                n
                (fun i : Fin n =>
                  chartBasisVecFiber (I := I) α i b)
                Idx Jdx) := hN3 S hb
  have hB_each : ∀ Idx : Fin r → Fin n, ∀ Jdx : Fin s → Fin n,
      fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
          n
          (fun i : Fin n => chartBasisVecFiber (I := I) α i b)
          Idx Jdx ≤
        C₂ * RawSq := by
    intro Idx Jdx
    rw [hRawSq_def]
    exact hN2 S hb Idx Jdx
  have hB_sum :
      (∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
            n
            (fun i : Fin n => chartBasisVecFiber (I := I) α i b)
            Idx Jdx) ≤
      (∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n, C₂ * RawSq) := by
    refine Finset.sum_le_sum ?_
    intro Idx _
    refine Finset.sum_le_sum ?_
    intro Jdx _
    exact hB_each Idx Jdx
  have hInner : ∀ _Idx : Fin r → Fin n,
      (∑ _Jdx : Fin s → Fin n, C₂ * RawSq) = ((n : ℝ) ^ s) * (C₂ * RawSq) := by
    intro _Idx
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  have hConstSum :
      (∑ _Idx : Fin r → Fin n,
        ∑ _Jdx : Fin s → Fin n, C₂ * RawSq) =
        cardIJ * (C₂ * RawSq) := by
    have hStep1 :
        (∑ _Idx : Fin r → Fin n,
          ∑ _Jdx : Fin s → Fin n, C₂ * RawSq) =
            ∑ _Idx : Fin r → Fin n, ((n : ℝ) ^ s) * (C₂ * RawSq) := by
      refine Finset.sum_congr rfl ?_
      intro Idx _
      exact hInner Idx
    rw [hStep1]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [hcardIJ_def]
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  have h_sum_nn :
      0 ≤ ∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
                n
                (fun i : Fin n => chartBasisVecFiber (I := I) α i b)
                Idx Jdx := by
    refine Finset.sum_nonneg (fun _ _ => ?_)
    refine Finset.sum_nonneg (fun _ _ => ?_)
    unfold fiberNormSqSummand
    exact sq_nonneg _
  have hAB_inner :
      (∑ Idx : Fin r → Fin n,
        ∑ Jdx : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
            n
            (fun i : Fin n => chartBasisVecFiber (I := I) α i b)
            Idx Jdx) ≤ cardIJ * (C₂ * RawSq) := by
    calc (∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
              n
              (fun i : Fin n => chartBasisVecFiber (I := I) α i b)
              Idx Jdx)
        ≤ (∑ _Idx : Fin r → Fin n,
            ∑ _Jdx : Fin s → Fin n, C₂ * RawSq) := hB_sum
      _ = cardIJ * (C₂ * RawSq) := hConstSum
  have hAB_scaled :
      C₃ *
        (∑ Idx : Fin r → Fin n,
          ∑ Jdx : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
              n
              (fun i : Fin n => chartBasisVecFiber (I := I) α i b)
              Idx Jdx) ≤
        C₃ * (cardIJ * (C₂ * RawSq)) :=
    mul_le_mul_of_nonneg_left hAB_inner hC₃_nn
  have h_final :
      riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b) ≤
        C₃ * (cardIJ * (C₂ * RawSq)) := hA.trans hAB_scaled
  have h_C_assoc : C₃ * (cardIJ * (C₂ * RawSq)) = C * RawSq := by
    rw [hC_def]; ring
  rw [h_C_assoc] at h_final
  rw [hRawSq_def] at h_final
  exact h_final

end Connection
end Integral
end DifferentialGeometry

end
