import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBound
import DifferentialGeometry.Tensor.Auxiliary.DetOpNormBound
import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem sum_raw_α_sq_le_sum_raw_β_sq_on_pouInter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ K_swap : ℝ, 0 ≤ K_swap ∧
      ∀ (T : SmoothCcTensor g r s) (α β : M),
        ∀ b : M,
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            tsupport (fun x : M =>
              ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) ≤
            K_swap *
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by
  classical
  set N : ℝ := ((Finset.univ : Finset
        ((Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  obtain ⟨K_trans, hK_trans_nn, hK_trans_le⟩ :=
    transitionCoeff_le_uniform_on_pouTsupport (E := E) (I := I) (M := M) r s
  refine ⟨N * (N * K_trans ^ 2), ?_, ?_⟩
  · exact mul_nonneg hN_nn (mul_nonneg hN_nn (sq_nonneg _))
  intro T α β b hb
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ with hV_def
  have hbα : b ∈ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hb.1
  have hbβ : b ∈ (chartAt H β).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β hb.2
  have hb_inter_βα : b ∈ (chartAt H β).source ∩ (chartAt H α).source := ⟨hbβ, hbα⟩
  have h_trans : ∀ (P : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))),
      tensorChartComponentRaw (I := I) (M := M) g r s T α P.1 P.2 b =
        ∑ Q ∈ V,
          transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
            tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b := by
    intro P
    have h_sum := tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s T β α P hb_inter_βα
    convert h_sum using 1
  have h_per_pair : ∀ P ∈ V,
      (tensorChartComponentRaw (I := I) (M := M) g r s T α P.1 P.2 b) ^ 2 ≤
        N * K_trans ^ 2 *
          ∑ Q ∈ V,
            (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by
    intro P _
    rw [h_trans P]
    have h_coeff_abs_le : ∀ Q ∈ V,
        |transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
            tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| ≤
          K_trans *
            |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| := by
      intro Q _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hK_trans_le β α P Q b ⟨hb.2, hb.1⟩)
        (abs_nonneg _)
    have h_abs_sum_bound :
        |∑ Q ∈ V,
            transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
              tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| ≤
          K_trans *
            ∑ Q ∈ V,
              |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| := by
      calc |∑ Q ∈ V,
              transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
                tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b|
          ≤ ∑ Q ∈ V,
              |transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
                tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| :=
                Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ Q ∈ V,
              K_trans *
                |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| :=
                Finset.sum_le_sum h_coeff_abs_le
        _ = K_trans *
              ∑ Q ∈ V,
                |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| := by
                rw [← Finset.mul_sum]
    have h_sq_sum :
        (∑ Q ∈ V,
            transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
              tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 ≤
          (K_trans *
            ∑ Q ∈ V,
              |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b|) ^ 2 := by
      rw [show (∑ Q ∈ V,
            transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
              tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 =
          |∑ Q ∈ V,
            transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
              tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| ^ 2
        from (sq_abs _).symm]
      exact pow_le_pow_left₀ (abs_nonneg _) h_abs_sum_bound 2
    have h_CS : (∑ Q ∈ V,
          |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b|) ^ 2 ≤
        N * ∑ Q ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by
      have hbase := Finset.sum_mul_sq_le_sq_mul_sq V
        (fun _ : _ × _ => (1 : ℝ))
        (fun Q : _ × _ =>
          |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b|)
      simp only [one_mul, one_pow] at hbase
      have h_sum_one : (∑ _Q ∈ V, (1 : ℝ)) = N := by simp [hN_def, hV_def]
      rw [h_sum_one] at hbase
      rw [show (∑ Q ∈ V,
            |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b| ^ 2) =
          ∑ Q ∈ V,
            (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2
        from Finset.sum_congr rfl (fun Q _ => by rw [sq_abs])] at hbase
      exact hbase
    calc (∑ Q ∈ V,
            transitionCoeff (E := E) (I := I) (M := M) r s β α P Q b *
              tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2
        ≤ (K_trans *
            ∑ Q ∈ V,
              |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b|) ^ 2 := h_sq_sum
      _ = K_trans ^ 2 *
            (∑ Q ∈ V,
              |tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b|) ^ 2 := by ring
      _ ≤ K_trans ^ 2 *
            (N * ∑ Q ∈ V,
              (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2) :=
              mul_le_mul_of_nonneg_left h_CS (sq_nonneg _)
      _ = N * K_trans ^ 2 *
            ∑ Q ∈ V,
              (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by ring
  have h_α_pair_sum :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2) =
        ∑ P ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α P.1 P.2 b) ^ 2 := by
    rw [show V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
        (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) from
      Finset.univ_product_univ.symm]
    rw [Finset.sum_product
      (f := fun P : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        (tensorChartComponentRaw (I := I) (M := M) g r s T α P.1 P.2 b) ^ 2)]
  have h_β_pair_sum :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2) =
        ∑ Q ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by
    rw [show V = (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
        (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))) from
      Finset.univ_product_univ.symm]
    rw [Finset.sum_product
      (f := fun Q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
        (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2)]
  rw [h_α_pair_sum, h_β_pair_sum]
  calc (∑ P ∈ V,
          (tensorChartComponentRaw (I := I) (M := M) g r s T α P.1 P.2 b) ^ 2)
      ≤ ∑ P ∈ V,
          (N * K_trans ^ 2 *
            ∑ Q ∈ V,
              (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2) :=
            Finset.sum_le_sum h_per_pair
    _ = (V.card : ℝ) *
          (N * K_trans ^ 2 *
            ∑ Q ∈ V,
              (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ = N *
          (N * K_trans ^ 2 *
            ∑ Q ∈ V,
              (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2) := by
            rfl
    _ = N * (N * K_trans ^ 2) *
          ∑ Q ∈ V,
            (tensorChartComponentRaw (I := I) (M := M) g r s T β Q.1 Q.2 b) ^ 2 := by ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem pointwise_α_repr_le_sum_β_componentPou_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ K_pt : ℝ, 0 ≤ K_pt ∧
      ∀ (T : SmoothCcTensor g r s) (α : M) (b : M),
        (chartAtlasPOU I M α : M → ℝ) b *
          ‖tensorRSChartE_section_repr (I := I) r s α
              (fun z : M => T.toSection z) b‖ ^ 2 ≤
          K_pt *
            ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by
  classical
  set N : ℝ := ((Finset.univ : Finset
        ((Fin r → Fin (Module.finrank ℝ E)) ×
         (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ) with hN_def
  have hN_nn : 0 ≤ N := Nat.cast_nonneg _
  set Bnorm : ℝ := tensorChartBasisNormConstant (E := E) r s with hBnorm_def
  have hBnorm_nn : 0 ≤ Bnorm := tensorChartBasisNormConstant_nonneg (E := E) r s
  set N_pou : ℝ := ((chartAtlasPOU_finset (I := I) (M := M)).card : ℝ)
    with hN_pou_def
  have hN_pou_nn : 0 ≤ N_pou := Nat.cast_nonneg _
  obtain ⟨K_swap, hK_swap_nn, hK_swap_le⟩ :=
    sum_raw_α_sq_le_sum_raw_β_sq_on_pouInter
      (E := E) (I := I) (M := M) g r s
  refine ⟨N_pou * (N * Bnorm ^ 2) * K_swap, ?_, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hN_pou_nn (mul_nonneg hN_nn (sq_nonneg _))) hK_swap_nn
  intro T α b
  set ρα : ℝ := (chartAtlasPOU I M α : M → ℝ) b with hρα_def
  have hρα_nn : 0 ≤ ρα := (chartAtlasPOU I M).nonneg α b
  have hρα_le_one : ρα ≤ 1 := (chartAtlasPOU I M).le_one α b
  set V : ℝ := ‖tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => T.toSection z) b‖ with hV_def
  have hV_nn : 0 ≤ V := norm_nonneg _
  have hV_sq_nn : 0 ≤ V ^ 2 := sq_nonneg _
  by_cases hbα_tsupp :
      b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have h_repr_sq := reprNormSq_le_sum_components_sq
      (I := I) (M := M) g r s T α b
    have h_sum_one := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) b
    have h_one_sq : (1 : ℝ) ≤
        N_pou * ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 := by
      have hbase := Finset.sum_mul_sq_le_sq_mul_sq
        (chartAtlasPOU_finset (I := I) (M := M))
        (fun _ : M => (1 : ℝ))
        (fun β : M => (chartAtlasPOU I M β : M → ℝ) b)
      simp only [one_mul, one_pow] at hbase
      have h_card : (∑ _β ∈ chartAtlasPOU_finset (I := I) (M := M), (1 : ℝ)) = N_pou := by
        simp [hN_pou_def]
      rw [h_card] at hbase
      have h_sum_eq : ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            (chartAtlasPOU I M β : M → ℝ) b = 1 := h_sum_one
      have h_sum_sq_one : (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
            (chartAtlasPOU I M β : M → ℝ) b) ^ 2 = 1 := by
        rw [h_sum_eq]; norm_num
      rw [h_sum_sq_one] at hbase
      exact hbase
    have h_V_sq_bound : V ^ 2 ≤
        N_pou * ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 * V ^ 2 := by
      have h_mul := mul_le_mul_of_nonneg_right h_one_sq hV_sq_nn
      rw [one_mul] at h_mul
      rw [show N_pou * (∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ((chartAtlasPOU I M β : M → ℝ) b) ^ 2) * V ^ 2 =
            N_pou * ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 * V ^ 2 from by
        rw [mul_assoc, Finset.sum_mul]] at h_mul
      exact h_mul
    have h_step1 : ρα * V ^ 2 ≤ V ^ 2 := by
      nlinarith [hρα_nn, hρα_le_one, hV_sq_nn]
    have h_per_β : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 * V ^ 2 ≤
          (N * Bnorm ^ 2 * K_swap) *
            (((chartAtlasPOU I M β : M → ℝ) b) ^ 2 *
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2) := by
      intro β _
      by_cases hb_β_tsupp :
          b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      · have hb_inter :
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              tsupport (fun x : M =>
                ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
          ⟨hbα_tsupp, hb_β_tsupp⟩
        have h_swap := hK_swap_le T α β b hb_inter
        have h_chain : V ^ 2 ≤ N * Bnorm ^ 2 * K_swap *
            ∑ Idx, ∑ Jdx,
              (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by
          calc V ^ 2
              ≤ N * Bnorm ^ 2 *
                ∑ Idx, ∑ Jdx,
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 :=
                  h_repr_sq
            _ ≤ N * Bnorm ^ 2 *
                (K_swap *
                  ∑ Idx, ∑ Jdx,
                    (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2) :=
                  mul_le_mul_of_nonneg_left h_swap
                    (mul_nonneg hN_nn (sq_nonneg _))
            _ = N * Bnorm ^ 2 * K_swap *
                ∑ Idx, ∑ Jdx,
                  (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by ring
        have h_ρβ_sq_nn : 0 ≤ ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 := sq_nonneg _
        have h_mul := mul_le_mul_of_nonneg_left h_chain h_ρβ_sq_nn
        calc ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 * V ^ 2
            ≤ ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 *
                (N * Bnorm ^ 2 * K_swap *
                  ∑ Idx, ∑ Jdx,
                    (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2) := h_mul
          _ = (N * Bnorm ^ 2 * K_swap) *
                (((chartAtlasPOU I M β : M → ℝ) b) ^ 2 *
                  ∑ Idx, ∑ Jdx,
                    (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2) := by ring
      · have h_ρβ_zero : (chartAtlasPOU I M β : M → ℝ) b = 0 := by
          have hsub : Function.support
              ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
            tsupport ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
            subset_tsupport _
          by_contra hne
          have hne' : (chartAtlasPOU I M β : M → ℝ) b ≠ 0 := hne
          have hin : b ∈ Function.support
              ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
            change ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) b ≠ 0
            exact hne'
          exact hb_β_tsupp (hsub hin)
        rw [h_ρβ_zero]
        ring_nf
        exact le_refl 0
    have h_componentPou : ∀ β,
        ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 *
          (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2) =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by
      intro β
      have h_pt : ∀ Idx Jdx,
          ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 *
            (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 =
            (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by
        intro Idx Jdx
        unfold tensorChartComponentPou
        ring
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Idx _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun Jdx _ => h_pt Idx Jdx)
    calc ρα * V ^ 2
        ≤ V ^ 2 := h_step1
      _ ≤ N_pou * ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ((chartAtlasPOU I M β : M → ℝ) b) ^ 2 * V ^ 2 := h_V_sq_bound
      _ ≤ N_pou * ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ((N * Bnorm ^ 2 * K_swap) *
                (((chartAtlasPOU I M β : M → ℝ) b) ^ 2 *
                  ∑ Idx, ∑ Jdx,
                    (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ hN_pou_nn
              exact Finset.sum_le_sum h_per_β
      _ = N_pou * (N * Bnorm ^ 2) * K_swap *
            ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              (((chartAtlasPOU I M β : M → ℝ) b) ^ 2 *
                ∑ Idx, ∑ Jdx,
                  (tensorChartComponentRaw (I := I) (M := M) g r s T β Idx Jdx b) ^ 2) := by
            rw [← Finset.mul_sum]; ring
      _ = N_pou * (N * Bnorm ^ 2) * K_swap *
            ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  (tensorChartComponentPou (I := I) (M := M) g r s T β Idx Jdx b) ^ 2 := by
            congr 1
            refine Finset.sum_congr rfl (fun β _ => ?_)
            exact h_componentPou β
  · have h_ρα_zero : ρα = 0 := by
      have hsub : Function.support
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
        tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
        subset_tsupport _
      by_contra hne
      have hne' : (chartAtlasPOU I M α : M → ℝ) b ≠ 0 := hne
      have hin : b ∈ Function.support
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        change ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b ≠ 0
        exact hne'
      exact hbα_tsupp (hsub hin)
    rw [h_ρα_zero, zero_mul]
    refine mul_nonneg ?_ ?_
    · exact mul_nonneg
        (mul_nonneg hN_pou_nn (mul_nonneg hN_nn (sq_nonneg _))) hK_swap_nn
    · refine Finset.sum_nonneg (fun β _ => ?_)
      refine Finset.sum_nonneg (fun Idx _ => ?_)
      refine Finset.sum_nonneg (fun Jdx _ => ?_)
      exact sq_nonneg _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
