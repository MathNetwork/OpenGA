import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawConnLapChartCoeffsUniformBoundT0Uniform

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem rawTensorConnLap_riemannianFiberNormSq_le_chart_α_data_T0_uniform
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
          riemannianFiberNormSq (I := I) (M := M) g r s b
              (rawTensorConnLap (I := I) g r s
                (fun z : M => T₀.toSection z) b) ≤
            C *
              (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ((‖iteratedFDeriv ℝ 2
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
                      ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                  (‖fderiv ℝ
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))
                      ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                  (chartPushedRaw I α
                     (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)
                     ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨C_H, hC_H_nn, hH⟩ :=
    riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g r s α
  have hB_each : ∀ idx : Fin r → Fin n, ∀ jdx : Fin s → Fin n,
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ (T₀ : SmoothCcTensor g r s),
          ∀ (b : M),
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              chartLeviCivitaGoodSet (I := I) α →
            (tensorChartComponentRaw (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b) ^ 2 ≤
              K * (∑ Idx' : Fin r → Fin n,
                    ∑ Jdx' : Fin s → Fin n,
                      ((‖iteratedFDeriv ℝ 2
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                              T₀ α Idx' Jdx'))
                          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                      (‖fderiv ℝ
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                              T₀ α Idx' Jdx'))
                          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                      (chartPushedRaw I α
                         (tensorChartComponentRaw (I := I) (M := M) g r s
                           T₀ α Idx' Jdx')
                         ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) := by
    intro idx jdx
    exact rawTensorConnLap_chartα_coeffs_uniform_bound_on_pouTsupport_T0_uniform
      (I := I) (M := M) g r s α idx jdx
  choose K_fn hK_fn_nn hK_fn_bd using hB_each
  set IJ_set : Finset ((Fin r → Fin n) × (Fin s → Fin n)) := Finset.univ
  have hIJ_ne : IJ_set.Nonempty := Finset.univ_nonempty
  set K_max : ℝ := IJ_set.sup' hIJ_ne (fun p => K_fn p.1 p.2) with hKmax_def
  have hKmax_nn : 0 ≤ K_max := by
    rcases hIJ_ne with ⟨p₀, hp₀⟩
    exact (hK_fn_nn p₀.1 p₀.2).trans
      (Finset.le_sup'_of_le (fun p => K_fn p.1 p.2) hp₀ (le_refl _))
  have hKmax_bd : ∀ idx : Fin r → Fin n, ∀ jdx : Fin s → Fin n,
      K_fn idx jdx ≤ K_max := fun idx jdx =>
    Finset.le_sup'_of_le (fun p => K_fn p.1 p.2)
      (Finset.mem_univ (idx, jdx)) (le_refl _)
  set cardIJ : ℝ := (n : ℝ) ^ r * (n : ℝ) ^ s with hcardIJ_def
  have hcardIJ_nn : 0 ≤ cardIJ :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg n) r)
               (pow_nonneg (Nat.cast_nonneg n) s)
  set C : ℝ := C_H * cardIJ * K_max with hC_def
  have hC_nn : 0 ≤ C :=
    mul_nonneg (mul_nonneg hC_H_nn hcardIJ_nn) hKmax_nn
  refine ⟨C, hC_nn, ?_⟩
  intro T₀ b hb_inter
  set S : SmoothCcTensor g r s :=
    rawTensorConnLapSmooth (I := I) g r s T₀ with hS_def
  have hH_at := hH (S := S) (b := b) hb_inter.1
  have hS_value : S.toSection b =
      rawTensorConnLap (I := I) g r s (fun z : M => T₀.toSection z) b := by
    rw [hS_def]; exact rawTensorConnLapSmooth_toSection_apply (I := I) g r s T₀ b
  have hH_rewritten :
      riemannianFiberNormSq (I := I) (M := M) g r s b
          (rawTensorConnLap (I := I) g r s
            (fun z : M => T₀.toSection z) b) ≤
        C_H *
          (∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              (tensorChartComponentRaw (I := I) (M := M) g r s
                S α Idx Jdx b) ^ 2) := by
    rw [← hS_value]; exact hH_at
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  set DataIJ : (Fin r → Fin n) → (Fin s → Fin n) → ℝ :=
    fun Idx' Jdx' =>
      (‖iteratedFDeriv ℝ 2
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx' Jdx')) y‖) ^ 2 +
      (‖fderiv ℝ
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx' Jdx')) y‖) ^ 2 +
      (chartPushedRaw I α
         (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx' Jdx') y) ^ 2
    with hDataIJ_def
  have hDataIJ_nn : ∀ Idx' Jdx', 0 ≤ DataIJ Idx' Jdx' := by
    intro Idx' Jdx'
    rw [hDataIJ_def]
    have h1 : 0 ≤ (‖iteratedFDeriv ℝ 2
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx' Jdx')) y‖) ^ 2 :=
      sq_nonneg _
    have h2 : 0 ≤ (‖fderiv ℝ
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx' Jdx')) y‖) ^ 2 :=
      sq_nonneg _
    have h3 : 0 ≤ (chartPushedRaw I α
         (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx' Jdx') y) ^ 2 :=
      sq_nonneg _
    linarith
  set BigSum : ℝ :=
    ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n, DataIJ Idx' Jdx'
    with hBigSum_def
  have hBigSum_nn : 0 ≤ BigSum :=
    Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => hDataIJ_nn _ _))
  have hPerIJ_raw : ∀ idx : Fin r → Fin n, ∀ jdx : Fin s → Fin n,
      (tensorChartComponentRaw (I := I) (M := M) g r s
            S α idx jdx b) ^ 2 ≤ K_fn idx jdx * BigSum := by
    intro idx jdx
    have h := hK_fn_bd idx jdx T₀ b hb_inter
    have hS_lhs : (tensorChartComponentRaw (I := I) (M := M) g r s
            S α idx jdx b) ^ 2 =
        (tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b) ^ 2 := by
      rw [hS_def]
    rw [hS_lhs]
    have hRHS_eq : K_fn idx jdx * (∑ Idx' : Fin r → Fin n,
                    ∑ Jdx' : Fin s → Fin n,
                      ((‖iteratedFDeriv ℝ 2
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                              T₀ α Idx' Jdx'))
                          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                      (‖fderiv ℝ
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                              T₀ α Idx' Jdx'))
                          ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                      (chartPushedRaw I α
                         (tensorChartComponentRaw (I := I) (M := M) g r s
                           T₀ α Idx' Jdx')
                         ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) =
        K_fn idx jdx * BigSum := by
      rw [hBigSum_def, hDataIJ_def, hy_def]
    rw [← hRHS_eq]; exact h
  have hPerIJ_raw_max : ∀ idx : Fin r → Fin n, ∀ jdx : Fin s → Fin n,
      (tensorChartComponentRaw (I := I) (M := M) g r s
            S α idx jdx b) ^ 2 ≤ K_max * BigSum := by
    intro idx jdx
    calc (tensorChartComponentRaw (I := I) (M := M) g r s
            S α idx jdx b) ^ 2
        ≤ K_fn idx jdx * BigSum := hPerIJ_raw idx jdx
      _ ≤ K_max * BigSum :=
          mul_le_mul_of_nonneg_right (hKmax_bd idx jdx) hBigSum_nn
  have hSumIJ_rawCompSq :
      (∑ idx : Fin r → Fin n,
        ∑ jdx : Fin s → Fin n,
          (tensorChartComponentRaw (I := I) (M := M) g r s
            S α idx jdx b) ^ 2) ≤
      cardIJ * (K_max * BigSum) := by
    have h_le : (∑ idx : Fin r → Fin n,
        ∑ jdx : Fin s → Fin n,
          (tensorChartComponentRaw (I := I) (M := M) g r s
            S α idx jdx b) ^ 2) ≤
        ∑ _idx : Fin r → Fin n, ∑ _jdx : Fin s → Fin n, K_max * BigSum :=
      Finset.sum_le_sum (fun idx _ =>
        Finset.sum_le_sum (fun jdx _ => hPerIJ_raw_max idx jdx))
    have h_inner_const : ∀ _idx : Fin r → Fin n,
        (∑ _jdx : Fin s → Fin n, K_max * BigSum) =
          ((n : ℝ) ^ s) * (K_max * BigSum) := by
      intro _idx
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      push_cast
      rfl
    have h_const_sum :
        (∑ _idx : Fin r → Fin n, ∑ _jdx : Fin s → Fin n, K_max * BigSum) =
          cardIJ * (K_max * BigSum) := by
      have hStep1 :
          (∑ _idx : Fin r → Fin n,
            ∑ _jdx : Fin s → Fin n, K_max * BigSum) =
              ∑ _idx : Fin r → Fin n, ((n : ℝ) ^ s) * (K_max * BigSum) := by
        refine Finset.sum_congr rfl ?_
        intro idx _
        exact h_inner_const idx
      rw [hStep1]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [hcardIJ_def]
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      push_cast
      ring
    calc (∑ idx : Fin r → Fin n,
          ∑ jdx : Fin s → Fin n,
            (tensorChartComponentRaw (I := I) (M := M) g r s
              S α idx jdx b) ^ 2)
        ≤ (∑ _idx : Fin r → Fin n,
            ∑ _jdx : Fin s → Fin n, K_max * BigSum) := h_le
      _ = cardIJ * (K_max * BigSum) := h_const_sum
  calc riemannianFiberNormSq (I := I) (M := M) g r s b
        (rawTensorConnLap (I := I) g r s (fun z : M => T₀.toSection z) b)
      ≤ C_H *
          (∑ Idx : Fin r → Fin n,
            ∑ Jdx : Fin s → Fin n,
              (tensorChartComponentRaw (I := I) (M := M) g r s
                S α Idx Jdx b) ^ 2) := hH_rewritten
    _ ≤ C_H * (cardIJ * (K_max * BigSum)) :=
        mul_le_mul_of_nonneg_left hSumIJ_rawCompSq hC_H_nn
    _ = C * BigSum := by rw [hC_def]; ring

end Connection
end Integral
end DifferentialGeometry

end
