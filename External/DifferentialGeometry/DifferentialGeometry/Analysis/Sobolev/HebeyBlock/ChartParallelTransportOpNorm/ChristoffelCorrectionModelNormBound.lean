import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.ChristoffelCorrectionAtomL2Bound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def basisCoordSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)

private noncomputable def basisVecSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

private lemma basisCoordSup_nonneg : 0 ≤ basisCoordSup (E := E) := by
  unfold basisCoordSup
  set i₀ : Fin (Module.finrank ℝ E) := ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
  calc (0 : ℝ) ≤ ‖((chartModelBasis E).coord i₀).toContinuousLinearMap‖ := norm_nonneg _
    _ ≤ _ := Finset.le_sup' (f := fun i =>
        ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) (Finset.mem_univ i₀)

private lemma basisVecSup_nonneg : 0 ≤ basisVecSup (E := E) := by
  unfold basisVecSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  exact le_trans (norm_nonneg _)
    (Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

private lemma repr_coord_abs_le (x : E) (i : Fin (Module.finrank ℝ E)) :
    |((chartModelBasis E).repr x) i| ≤ basisCoordSup (E := E) * ‖x‖ := by
  have h_eq : (chartModelBasis E).repr x i =
      ((chartModelBasis E).coord i).toContinuousLinearMap x := rfl
  rw [h_eq, ← Real.norm_eq_abs]
  calc ‖((chartModelBasis E).coord i).toContinuousLinearMap x‖
      ≤ ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ basisCoordSup (E := E) * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact Finset.le_sup'
          (f := fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)
          (Finset.mem_univ _)

private lemma basis_vec_norm_le (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ basisVecSup (E := E) := by
  exact Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) (Finset.mem_univ _)

theorem christoffelCorrection_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (Y : E) (v : TangentSpace I b),
          ‖christoffelCorrection (I := I) g α b Y v‖ ≤
            C * ‖Y‖ * ‖trivToE (I := I) α b v‖ := by
  classical
  obtain ⟨CΓ, hCΓ_nn, hCΓ_le⟩ :=
    chartChristoffel_bdd_on_pou_tsupport (I := I) (M := M) g α
  set n : ℕ := Module.finrank ℝ E
  set Cc := basisCoordSup (E := E)
  set Cv := basisVecSup (E := E)
  refine ⟨(n : ℝ) ^ 3 * Cc ^ 2 * Cv * CΓ,
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
      (sq_nonneg _)) (basisVecSup_nonneg (E := E))) hCΓ_nn, ?_⟩
  intro b hb Y v
  have hb_image : extChartAt I α b ∈ (extChartAt I α) ''
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    ⟨b, hb, rfl⟩
  rw [christoffelCorrection_apply]
  set w : E := trivToE (I := I) α b v
  have h_step1 :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (((chartModelBasis E).repr w) i *
            ((chartModelBasis E).repr Y) j *
            chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
            (chartModelBasis E) k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          |((chartModelBasis E).repr w) i| *
          |((chartModelBasis E).repr Y) j| *
          |chartChristoffel (I := I) g α i j k (extChartAt I α b)| * Cv := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (basis_vec_norm_le k)
      (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
  have h_step2 :
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        |((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| *
        |chartChristoffel (I := I) g α i j k (extChartAt I α b)| * Cv ≤
      ∑ i : Fin n, ∑ j : Fin n, ∑ _k : Fin n,
        |((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| * CΓ * Cv :=
    Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => by
          have h1 := hCΓ_le _ hb_image i j k
          have hCv_nn := basisVecSup_nonneg (E := E)
          have hwi := abs_nonneg (((chartModelBasis E).repr w) i)
          have hYj := abs_nonneg (((chartModelBasis E).repr Y) j)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (mul_nonneg hwi hYj)) hCv_nn
  have h_step3 :
      ∑ i : Fin n, ∑ j : Fin n, ∑ _k : Fin n,
        |((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| * CΓ * Cv =
      (n : ℝ) * CΓ * Cv *
        (∑ i : Fin n, |((chartModelBasis E).repr w) i|) *
        (∑ j : Fin n, |((chartModelBasis E).repr Y) j|) := by
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    conv_lhs =>
      arg 2; ext i; arg 2; ext j
      rw [show (n : ℝ) * (|((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| * CΓ * Cv) =
        ((n : ℝ) * CΓ * Cv * |((chartModelBasis E).repr w) i|) *
        |((chartModelBasis E).repr Y) j| from by ring]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h_w_bound :
      (∑ i : Fin n, |((chartModelBasis E).repr w) i|) ≤ (n : ℝ) * Cc * ‖w‖ := by
    calc ∑ i : Fin n, |((chartModelBasis E).repr w) i|
        ≤ ∑ _i : Fin n, Cc * ‖w‖ :=
          Finset.sum_le_sum fun i _ => repr_coord_abs_le w i
      _ = (n : ℝ) * Cc * ‖w‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h_Y_bound :
      (∑ j : Fin n, |((chartModelBasis E).repr Y) j|) ≤ (n : ℝ) * Cc * ‖Y‖ := by
    calc ∑ j : Fin n, |((chartModelBasis E).repr Y) j|
        ≤ ∑ _j : Fin n, Cc * ‖Y‖ :=
          Finset.sum_le_sum fun j _ => repr_coord_abs_le Y j
      _ = (n : ℝ) * Cc * ‖Y‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (((chartModelBasis E).repr w) i *
            ((chartModelBasis E).repr Y) j *
            chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
            (chartModelBasis E) k‖
      ≤ (n : ℝ) * CΓ * Cv *
          (∑ i : Fin n, |((chartModelBasis E).repr w) i|) *
          (∑ j : Fin n, |((chartModelBasis E).repr Y) j|) := by
        linarith [h_step1, h_step2, h_step3.le]
    _ ≤ (n : ℝ) * CΓ * Cv * ((n : ℝ) * Cc * ‖w‖) * ((n : ℝ) * Cc * ‖Y‖) := by
        have hCv_nn := basisVecSup_nonneg (E := E)
        have hCc_nn := basisCoordSup_nonneg (E := E)
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left h_w_bound
            (mul_nonneg (mul_nonneg hn_nn hCΓ_nn) hCv_nn))
          h_Y_bound
          (Finset.sum_nonneg fun j _ => abs_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hn_nn hCΓ_nn) hCv_nn)
            (mul_nonneg (mul_nonneg hn_nn hCc_nn) (norm_nonneg _)))
    _ = (n : ℝ) ^ 3 * Cc ^ 2 * Cv * CΓ * ‖Y‖ * ‖w‖ := by ring

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
