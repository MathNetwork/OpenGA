import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging









noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem l2_bdd_of_raw {ι : Type*}
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : ι → SmoothCcTensor g r s) (B : ℝ) (hB : 0 ≤ B)
    (hraw : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
            |tensorChartComponentRaw (I := I) (M := M)
              g r s (S k) α Idx Jdx b| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ι, ‖S k‖ ≤ C := by
  classical
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let R : ℝ≥0∞ := μ Set.univ ^ ((2 : ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal B
  let A : ℝ := R.toReal
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hR_ne : R ≠ (⊤ : ℝ≥0∞) := by
    dsimp [R]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ Set.univ))
      ENNReal.ofReal_ne_top
  have hscalar : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b : M,
        ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
        ‖tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx b‖ ≤ B := by
    intro α hα k b Idx Jdx
    rw [Real.norm_eq_abs]
    by_cases hb : b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    · rw [tensorChartComponentScalar_def]
      unfold tensorChartComponentPou
      rw [abs_mul, abs_of_nonneg ((chartAtlasPOU I M).nonneg α b)]
      calc
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b *
              |tensorChartComponentRaw (I := I) (M := M)
                g r s (S k) α Idx Jdx b|
            ≤ 1 * B := mul_le_mul ((chartAtlasPOU I M).le_one α b)
              (hraw α hα k b hb Idx Jdx) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    · have hρ : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b = 0 :=
        image_eq_zero_of_notMem_tsupport hb
      simp [tensorChartComponentScalar_def, tensorChartComponentPou, hρ, hB]
  have hcomponent : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι,
        ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ((eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s (S k) α Idx Jdx) 2 μ).toReal) ^ 2 ≤ A ^ 2 := by
    intro α hα k Idx Jdx
    have hpt : ∀ b : M,
        ‖tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx b‖ ≤ B := by
      intro b
      exact hscalar α hα k b Idx Jdx
    have hlp : eLpNorm (tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx) 2 μ ≤ R := by
      dsimp [R]
      exact MeasureTheory.eLpNorm_le_of_ae_bound
        (μ := μ) (p := 2) (Filter.Eventually.of_forall hpt)
    have hreal : (eLpNorm (tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx) 2 μ).toReal ≤ A := by
      dsimp [A]
      exact ENNReal.toReal_mono hR_ne hlp
    exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 hreal
  obtain ⟨C₀, hC₀, hglobal⟩ :=
    tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq
      (I := I) (M := M) g r s
  let Q : ℝ :=
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), A ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg A
  refine ⟨Real.sqrt (C₀ * Q), Real.sqrt_nonneg _, fun k => ?_⟩
  rw [SmoothCcTensor.norm_def]
  have hnorm : 0 ≤ tensorL2Norm (I := I) (M := M) g r s (S k).toFun := by
    unfold tensorL2Norm
    exact Real.sqrt_nonneg _
  apply (Real.le_sqrt hnorm (mul_nonneg hC₀ hQ)).2
  refine (hglobal (S k)).trans (mul_le_mul_of_nonneg_left ?_ hC₀)
  dsimp [Q]
  refine Finset.sum_le_sum fun α hα => ?_
  refine Finset.sum_le_sum fun Idx _ => ?_
  exact Finset.sum_le_sum fun Jdx _ => hcomponent α hα k Idx Jdx





theorem l2_le_of_raw_sum [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (c N : ℕ) (v : ℕ → ℕ)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ∀ i, SmoothCcTensor g 0 (v i)) (S : SmoothCcTensor g 0 c),
        (∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ∀ b ∈ tsupport
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
            ∀ Jdx : Fin c → Fin (Module.finrank ℝ E),
              |tensorChartComponentRaw (I := I) (M := M)
                  g 0 c S α Idx Jdx b| ≤
                B * ∑ i ∈ Finset.range N,
                  Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
                    g 0 (v i) b ((T i).toSection b))) →
        ‖S‖ ≤ C * ∑ i ∈ Finset.range N, ‖T i‖ := by
  classical
  let Sf : Finset M := chartAtlasPOU_finset (I := I) (M := M)
  choose Cα hCα_nn hCα_bound using fun α (_ : α ∈ Sf) =>
    riemannianFiberNormSq_le_raw_components_on_pouTsupport
      (I := I) (M := M) g 0 c α
  let Cmax : ℝ := ∑ α ∈ Sf.attach, Cα α.val α.property
  have hCmax : 0 ≤ Cmax := by
    dsimp [Cmax]
    exact Finset.sum_nonneg fun α _ => hCα_nn α.val α.property
  let Q : ℝ :=
    ∑ _Idx : Fin 0 → Fin (Module.finrank ℝ E),
      ∑ _Jdx : Fin c → Fin (Module.finrank ℝ E), (1 : ℝ)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  let K : ℝ := Cmax * Q * B ^ 2 * (N : ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  let C : ℝ := Real.sqrt K
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro T S hraw
  apply tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum
    (I := I) (M := M) g N v T S C (Real.sqrt_nonneg _)
  intro x
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have hexists : ∃ α ∈ Sf,
      0 < ((chartAtlasPOU I M) α : C^∞⟮I, M; ℝ⟯) x := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ α ∈ Sf, ((chartAtlasPOU I M) α : M → ℝ) x = 0 := by
      intro α hα
      have hle := hcon α hα
      have hnn := (chartAtlasPOU I M).nonneg α x
      linarith
    change ∑ α ∈ Sf, ((chartAtlasPOU I M) α : C^∞⟮I, M; ℝ⟯) x = 1 at hsum
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsum
    exact absurd hsum (by norm_num)
  obtain ⟨α, hα, hαpos⟩ := hexists
  have hx_tsupp : x ∈ tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hαpos))
  set A : ℝ := ∑ i ∈ Finset.range N,
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
      g 0 (v i) x ((T i).toSection x)) with hA_def
  have hA : 0 ≤ A := by
    rw [hA_def]
    exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hCα_le : Cα α hα ≤ Cmax := by
    dsimp [Cmax]
    simpa using Finset.single_le_sum
      (fun β _ => hCα_nn β.val β.property)
      (Finset.mem_attach Sf ⟨α, hα⟩)
  have hraw_sq :
      (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin c → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M)
            g 0 c S α Idx Jdx x) ^ 2) ≤ Q * (B * A) ^ 2 := by
    calc
      (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin c → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M)
              g 0 c S α Idx Jdx x) ^ 2)
          ≤ ∑ _Idx : Fin 0 → Fin (Module.finrank ℝ E),
              ∑ _Jdx : Fin c → Fin (Module.finrank ℝ E), (B * A) ^ 2 := by
        refine Finset.sum_le_sum fun Idx _ => ?_
        refine Finset.sum_le_sum fun Jdx _ => ?_
        have habs := hraw α (by simpa [Sf] using hα) x hx_tsupp Idx Jdx
        rw [← hA_def] at habs
        have hsquare :
            |tensorChartComponentRaw (I := I) (M := M)
                g 0 c S α Idx Jdx x| ^ 2 ≤ (B * A) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB hA)).2 habs
        simpa only [sq_abs] using hsquare
      _ = Q * (B * A) ^ 2 := by
        dsimp [Q]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hpoint :
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (S.toSection x) ≤
        Cmax * Q * (B * A) ^ 2 := by
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (S.toSection x)
          ≤ Cα α hα *
              (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
                ∑ Jdx : Fin c → Fin (Module.finrank ℝ E),
                  (tensorChartComponentRaw (I := I) (M := M)
                    g 0 c S α Idx Jdx x) ^ 2) :=
        hCα_bound α hα S hx_tsupp
      _ ≤ Cα α hα * (Q * (B * A) ^ 2) :=
        mul_le_mul_of_nonneg_left hraw_sq (hCα_nn α hα)
      _ ≤ Cmax * (Q * (B * A) ^ 2) :=
        mul_le_mul_of_nonneg_right hCα_le (mul_nonneg hQ (sq_nonneg _))
      _ = Cmax * Q * (B * A) ^ 2 := by ring
  have hA_sq : A ^ 2 ≤ (N : ℝ) *
      ∑ i ∈ Finset.range N,
        riemannianFiberNormSq (I := I) (M := M)
          g 0 (v i) x ((T i).toSection x) := by
    rw [hA_def]
    have hcheb := sq_sum_le_card_mul_sum_sq (s := Finset.range N)
      (f := fun i => Real.sqrt (riemannianFiberNormSq (I := I) (M := M)
        g 0 (v i) x ((T i).toSection x)))
    rw [Finset.card_range] at hcheb
    refine hcheb.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Real.sq_sqrt (riemannianFiberNormSq_nonneg
      (I := I) (M := M) g 0 (v i) x _)
  have hcoef : 0 ≤ Cmax * Q * B ^ 2 := by positivity
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 c x (S.toSection x)
        ≤ Cmax * Q * (B * A) ^ 2 := hpoint
    _ = (Cmax * Q * B ^ 2) * A ^ 2 := by ring
    _ ≤ (Cmax * Q * B ^ 2) * ((N : ℝ) *
          ∑ i ∈ Finset.range N,
            riemannianFiberNormSq (I := I) (M := M)
              g 0 (v i) x ((T i).toSection x)) :=
      mul_le_mul_of_nonneg_left hA_sq hcoef
    _ = K * ∑ i ∈ Finset.range N,
          riemannianFiberNormSq (I := I) (M := M)
            g 0 (v i) x ((T i).toSection x) := by
      dsimp [K]
      ring
    _ = C ^ 2 * ∑ i ∈ Finset.range N,
          riemannianFiberNormSq (I := I) (M := M)
            g 0 (v i) x ((T i).toSection x) := by
      rw [show C ^ 2 = K by exact Real.sq_sqrt hK]

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
