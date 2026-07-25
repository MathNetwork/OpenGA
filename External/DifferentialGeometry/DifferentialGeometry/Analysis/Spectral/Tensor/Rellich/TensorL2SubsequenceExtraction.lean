import DifferentialGeometry.Analysis.Spectral.Tensor.Rellich.Diagonal
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma tensorChartComponentScalar_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentScalar (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx =
      (fun x => tensorChartComponentScalar (I := I) (M := M)
          g r s S₁ α Idx Jdx x -
        tensorChartComponentScalar (I := I) (M := M)
          g r s S₂ α Idx Jdx x) := by
  have h_sub_eq : S₁ - S₂ = S₁ + ((-1 : ℝ) • S₂) := by
    rw [neg_one_smul]; abel
  rw [h_sub_eq]
  rw [tensorChartComponentScalar_add (I := I) (M := M)
    g r s S₁ ((-1 : ℝ) • S₂) α Idx Jdx]
  funext x
  rw [tensorChartComponentScalar_smul (I := I) (M := M)
    g r s (-1 : ℝ) S₂ α Idx Jdx]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tensorChartComponentScalar_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (tensorChartComponentScalar_contMDiff (I := I) (M := M)
    g r s S α Idx Jdx).continuous.aestronglyMeasurable

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma eLpNorm_diff_le_via_common_limit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {u_lim : M → ℝ}
    (h_lim_memLp :
      MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    eLpNorm
        (fun b => tensorChartComponentScalar (I := I) (M := M)
            g r s S₁ α Idx Jdx b -
          tensorChartComponentScalar (I := I) (M := M)
            g r s S₂ α Idx Jdx b)
        2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      eLpNorm
          (fun b => tensorChartComponentScalar (I := I) (M := M)
              g r s S₁ α Idx Jdx b - u_lim b)
          2 (riemannianVolumeMeasure (I := I) (M := M) g) +
        eLpNorm
            (fun b => tensorChartComponentScalar (I := I) (M := M)
                g r s S₂ α Idx Jdx b - u_lim b)
            2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  set f₁ : M → ℝ := tensorChartComponentScalar (I := I) (M := M)
    g r s S₁ α Idx Jdx
  set f₂ : M → ℝ := tensorChartComponentScalar (I := I) (M := M)
    g r s S₂ α Idx Jdx
  have hf₁ : AEStronglyMeasurable f₁ μ :=
    tensorChartComponentScalar_aestronglyMeasurable
      (I := I) (M := M) g r s S₁ α Idx Jdx
  have hf₂ : AEStronglyMeasurable f₂ μ :=
    tensorChartComponentScalar_aestronglyMeasurable
      (I := I) (M := M) g r s S₂ α Idx Jdx
  have h_u : AEStronglyMeasurable u_lim μ := h_lim_memLp.1
  have h_eq : (fun b => f₁ b - f₂ b) =
      (fun b => f₁ b - u_lim b) - (fun b => f₂ b - u_lim b) := by
    funext b
    simp only [Pi.sub_apply]
    ring
  rw [h_eq]
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  exact eLpNorm_sub_le (hf₁.sub h_u) (hf₂.sub h_u) hp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma eLpNorm_diff_tendsto_zero_of_tendsto_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {φ : ℕ → ℕ}
    {u_lim : M → ℝ}
    (h_lim_memLp :
      MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_tendsto :
      Filter.Tendsto
        (fun j => eLpNorm
            (fun b => tensorChartComponentScalar (I := I) (M := M)
              g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
            2 (riemannianVolumeMeasure (I := I) (M := M) g))
        Filter.atTop (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      eLpNorm
          (fun b => tensorChartComponentScalar (I := I) (M := M)
              g r s (S (φ i)).toCcTensor α Idx Jdx b -
            tensorChartComponentScalar (I := I) (M := M)
              g r s (S (φ j)).toCcTensor α Idx Jdx b)
          2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε := by
  have hε_half : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have h_eventually :
      ∀ᶠ j in Filter.atTop, eLpNorm
          (fun b => tensorChartComponentScalar (I := I) (M := M)
              g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
          2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε / 2 := by
    have h_open : (Set.Iic (ε / 2)) ∈ 𝓝 (0 : ℝ≥0∞) :=
      Iic_mem_nhds hε_half
    exact h_tendsto h_open
  rcases (Filter.eventually_atTop.mp h_eventually) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi j hj
  have h_tri := eLpNorm_diff_le_via_common_limit
    (I := I) (M := M) g r s (S (φ i)).toCcTensor (S (φ j)).toCcTensor
    α Idx Jdx h_lim_memLp
  have h_i_le : eLpNorm
      (fun b => tensorChartComponentScalar (I := I) (M := M)
          g r s (S (φ i)).toCcTensor α Idx Jdx b - u_lim b)
      2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε / 2 := hN i hi
  have h_j_le : eLpNorm
      (fun b => tensorChartComponentScalar (I := I) (M := M)
          g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
      2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε / 2 := hN j hj
  have h_sum : eLpNorm
        (fun b => tensorChartComponentScalar (I := I) (M := M)
            g r s (S (φ i)).toCcTensor α Idx Jdx b - u_lim b)
        2 (riemannianVolumeMeasure (I := I) (M := M) g) +
      eLpNorm
        (fun b => tensorChartComponentScalar (I := I) (M := M)
            g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
        2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε / 2 + ε / 2 :=
    add_le_add h_i_le h_j_le
  have h_half : ε / 2 + ε / 2 = ε := ENNReal.add_halves ε
  exact h_tri.trans (h_sum.trans (le_of_eq h_half))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tensorL2_diff_sq_le_const_mul_sum_componentDiff_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S₁ S₂ : SmoothCcTensor g r s),
        ‖(S₁ - S₂ : SmoothCcTensor g r s)‖ ^ 2 ≤
          C *
            ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
              ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                  ((eLpNorm
                      (fun b => tensorChartComponentScalar (I := I) (M := M)
                          g r s S₁ α Idx Jdx b -
                        tensorChartComponentScalar (I := I) (M := M)
                          g r s S₂ α Idx Jdx b) 2
                      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal)
                    ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq
      (I := I) (M := M) g r s
  refine ⟨C, hC_nn, ?_⟩
  intro S₁ S₂
  have h := h_bound (S₁ - S₂)
  rw [SmoothCcTensor.norm_def]
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC_nn
  refine Finset.sum_le_sum fun α _ => ?_
  refine Finset.sum_le_sum fun Idx _ => ?_
  refine Finset.sum_le_sum fun Jdx _ => ?_
  have h_sub :=
    tensorChartComponentScalar_sub (I := I) (M := M)
      g r s S₁ S₂ α Idx Jdx
  rw [h_sub]

private lemma cauchySeq_tensorL2_of_componentBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CauchySeq
        (fun j =>
          ((S (φ j)).toCcTensor : TensorL2 r s g)) := by
  classical
  obtain ⟨φ, hφ_mono, h_per_triple⟩ :=
    tensorChartComponent_rellich_extraction (I := I) (M := M) g r s
      (S := S) (R := R) hu_bdd
  refine ⟨φ, hφ_mono, ?_⟩
  obtain ⟨C, hC_nn, h_const_bound⟩ :=
    tensorL2_diff_sq_le_const_mul_sum_componentDiff_sq
      (I := I) (M := M) g r s
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set Sf : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  set K : ℕ := Sf.card *
      ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card) *
      ((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card)
  set δ : ℝ := (ε / 2) / Real.sqrt ((C + 1) * (K + 1 : ℝ))
  have hCK_pos : 0 < (C + 1) * (K + 1 : ℝ) :=
    mul_pos (by linarith) (by positivity)
  have h_sqrt_pos : 0 < Real.sqrt ((C + 1) * (K + 1 : ℝ)) :=
    Real.sqrt_pos.mpr hCK_pos
  have hε_half_pos : 0 < ε / 2 := by positivity
  have hδ_pos : 0 < δ := div_pos hε_half_pos h_sqrt_pos
  have hδ_ennreal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := by
    rw [ENNReal.ofReal_pos]; exact hδ_pos
  have h_per_N : ∀ α ∈ Sf,
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
          eLpNorm
              (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ i)).toCcTensor α Idx Jdx b -
                tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b)
              2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
            ENNReal.ofReal δ := by
    intro α hα Idx Jdx
    obtain ⟨u_lim, hu_lim_memLp, h_tendsto⟩ :=
      h_per_triple α hα Idx Jdx
    exact eLpNorm_diff_tendsto_zero_of_tendsto_zero
      (I := I) (M := M) g r s (S := S) α Idx Jdx (φ := φ)
      (u_lim := u_lim) hu_lim_memLp h_tendsto
      (ENNReal.ofReal δ) hδ_ennreal_pos
  let triples : Finset (M × (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) :=
    Sf ×ˢ ((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))) ×ˢ
      (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
  choose N hN using fun (t : M × (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) (ht : t ∈ triples) =>
    h_per_N t.1
      (by
        simp only [triples, Finset.mem_product] at ht
        exact ht.1) t.2.1 t.2.2
  let Nmax : ℕ := triples.attach.sup (fun ⟨t, ht⟩ => N t ht)
  refine ⟨Nmax, ?_⟩
  intro i hi j hj
  rw [dist_eq_norm,
    show ((S (φ i)).toCcTensor : TensorL2 r s g) -
            ((S (φ j)).toCcTensor : TensorL2 r s g) =
          (((S (φ i)).toCcTensor - (S (φ j)).toCcTensor :
              SmoothCcTensor g r s) : TensorL2 r s g) from
      (UniformSpace.Completion.coe_sub _ _).symm,
    UniformSpace.Completion.norm_coe]
  have h_norm_sq_le :=
    h_const_bound (S (φ i)).toCcTensor (S (φ j)).toCcTensor
  have h_K_delta_sq_eq :
      ∑ _α ∈ Sf, ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), δ ^ 2 =
        (K : ℝ) * δ ^ 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (Sf.card : ℝ) *
        (((Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card : ℝ) *
          (((Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℝ) *
            δ ^ 2)) =
        ((Sf.card *
            (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))).card *
            (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))).card : ℕ) : ℝ) *
          δ ^ 2
    push_cast
    ring
  have h_sum_le :
      ∑ α ∈ Sf, ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ((eLpNorm
              (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ i)).toCcTensor α Idx Jdx b -
                tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b) 2
              (riemannianVolumeMeasure (I := I) (M := M) g)).toReal) ^ 2 ≤
        (K : ℝ) * δ ^ 2 := by
    rw [← h_K_delta_sq_eq]
    refine Finset.sum_le_sum fun α hα => ?_
    refine Finset.sum_le_sum fun Idx _ => ?_
    refine Finset.sum_le_sum fun Jdx _ => ?_
    have ht_mem : (α, Idx, Jdx) ∈ triples :=
      Finset.mem_product.mpr ⟨hα,
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
    have h_N_le_Nmax : N (α, Idx, Jdx) ht_mem ≤ Nmax := by
      have := Finset.le_sup (s := triples.attach)
        (f := fun x : { x // x ∈ triples } => N x.1 x.2)
        (b := ⟨(α, Idx, Jdx), ht_mem⟩) (Finset.mem_attach _ _)
      simpa [Nmax] using this
    have h_eLp_le := hN (α, Idx, Jdx) ht_mem i
      (h_N_le_Nmax.trans hi) j (h_N_le_Nmax.trans hj)
    have h_toReal_le : (eLpNorm
        (fun b => tensorChartComponentScalar (I := I) (M := M)
            g r s (S (φ i)).toCcTensor α Idx Jdx b -
          tensorChartComponentScalar (I := I) (M := M)
            g r s (S (φ j)).toCcTensor α Idx Jdx b) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ≤ δ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_eLp_le
      rw [ENNReal.toReal_ofReal hδ_pos.le] at this
      exact this
    have h_toReal_nn : 0 ≤ (eLpNorm
        (fun b => tensorChartComponentScalar (I := I) (M := M)
            g r s (S (φ i)).toCcTensor α Idx Jdx b -
          tensorChartComponentScalar (I := I) (M := M)
            g r s (S (φ j)).toCcTensor α Idx Jdx b) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [h_toReal_le, h_toReal_nn, hδ_pos.le, sq_nonneg δ]
  have h_norm_sq_le' :
      ‖((S (φ i)).toCcTensor - (S (φ j)).toCcTensor :
          SmoothCcTensor g r s)‖ ^ 2 ≤ C * ((K : ℝ) * δ ^ 2) := by
    refine h_norm_sq_le.trans ?_
    exact mul_le_mul_of_nonneg_left h_sum_le hC_nn
  have h_norm_lt : ‖((S (φ i)).toCcTensor - (S (φ j)).toCcTensor :
      SmoothCcTensor g r s)‖ < ε := by
    have h_norm_nn : 0 ≤ ‖((S (φ i)).toCcTensor - (S (φ j)).toCcTensor :
        SmoothCcTensor g r s)‖ := norm_nonneg _
    have h_eps_sq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
    have h_target_sq : C * ((K : ℝ) * δ ^ 2) ≤ (ε / 2) ^ 2 := by
      have hδ_sq : δ ^ 2 = (ε / 2) ^ 2 / ((C + 1) * (K + 1 : ℝ)) := by
        change ((ε / 2) / Real.sqrt ((C + 1) * (K + 1 : ℝ))) ^ 2 =
          (ε / 2) ^ 2 / ((C + 1) * (K + 1 : ℝ))
        rw [div_pow, Real.sq_sqrt hCK_pos.le]
      rw [hδ_sq]
      have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      have h_C_K_le : C * (K : ℝ) ≤ (C + 1) * (K + 1 : ℝ) := by
        nlinarith [hC_nn, hK_nn]
      have h_C_step : C * ((K : ℝ) * ((ε / 2) ^ 2 / ((C + 1) * (K + 1 : ℝ)))) =
          (C * (K : ℝ) / ((C + 1) * (K + 1 : ℝ))) * (ε / 2) ^ 2 := by ring
      rw [h_C_step]
      have h_ratio_le : C * (K : ℝ) / ((C + 1) * (K + 1 : ℝ)) ≤ 1 :=
        (div_le_one hCK_pos).mpr h_C_K_le
      have hε_half_sq_nn : 0 ≤ (ε / 2) ^ 2 := sq_nonneg _
      nlinarith [h_ratio_le, hε_half_sq_nn,
        mul_le_mul_of_nonneg_right h_ratio_le hε_half_sq_nn]
    have h_sq_le : ‖((S (φ i)).toCcTensor - (S (φ j)).toCcTensor :
        SmoothCcTensor g r s)‖ ^ 2 ≤ (ε / 2) ^ 2 :=
      h_norm_sq_le'.trans h_target_sq
    have h_norm_le : ‖((S (φ i)).toCcTensor - (S (φ j)).toCcTensor :
        SmoothCcTensor g r s)‖ ≤ ε / 2 :=
      abs_le_of_sq_le_sq' h_sq_le hε_half_pos.le |>.2
    linarith [h_norm_le, hε.le]
  exact h_norm_lt

theorem tensorH1Compl_to_tensorL2_relatively_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s} {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ T_lim : TensorL2 r s g,
        Filter.Tendsto
          (fun j =>
            ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                (smoothToTensorH1Compl (I := I) (M := M) g r s
                  (S (φ j))) - T_lim‖)
          Filter.atTop (𝓝 0) := by
  classical
  obtain ⟨φ, hφ_mono, h_cauchy⟩ :=
    cauchySeq_tensorL2_of_componentBounded
      (I := I) (M := M) g r s (S := S) (R := R) hu_bdd
  obtain ⟨T_lim, h_tendsto_T⟩ := cauchySeq_tendsto_of_complete h_cauchy
  refine ⟨φ, hφ_mono, T_lim, ?_⟩
  have h_norm_tendsto : Filter.Tendsto
      (fun j => ‖((S (φ j)).toCcTensor : TensorL2 r s g) - T_lim‖)
      Filter.atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp h_tendsto_T
  refine Filter.Tendsto.congr (fun j => ?_) h_norm_tendsto
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
    (I := I) (M := M) g r s (S (φ j))]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
