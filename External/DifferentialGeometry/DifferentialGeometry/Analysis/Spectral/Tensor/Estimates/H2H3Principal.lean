import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.AppCcJetWindowTame
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes










namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
private theorem grad_icg2_norm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (U : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad (I := I) g 0 (s + 2) 1
        (iteratedCovGrad (I := I) g 0 s 2 U)‖ =
      ‖iteratedCovGrad (I := I) g 0 s 3 U‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g 0 (s + 2) 1
          (iteratedCovGrad (I := I) g 0 s 2 U)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 s 3 U‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g
        (iteratedCovGrad (I := I) g 0 (s + 2) 1
          (iteratedCovGrad (I := I) g 0 s 2 U)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g (iteratedCovGrad (I := I) g 0 s 3 U),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g ((s + 2) + 1)
        (iteratedCovGrad (I := I) g 0 (s + 2) 1
          (iteratedCovGrad (I := I) g 0 s 2 U)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
        (I := I) (M := M) g (s + 3)
        (iteratedCovGrad (I := I) g 0 s 3 U)]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => ?_))
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g 0 s 2 1 U x
  nlinarith [norm_nonneg
    (iteratedCovGrad (I := I) g 0 (s + 2) 1
      (iteratedCovGrad (I := I) g 0 s 2 U)),
    norm_nonneg (iteratedCovGrad (I := I) g 0 s 3 U)]




theorem appCc_grad_l2
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 2) c)
        (V : SmoothCcTensor g 0 (s + 1)) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              (V.toSection x) ≤ B ^ 2) →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) j V‖ ^ 2) ≤ B ^ 2 →
        ‖operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
            (covGrad (I := I) (M := M) g (s + 2) c Φ)
            (covGrad (I := I) (M := M) g 0 (s + 1) V)‖ ≤
          C * A * B := by
  classical
  obtain ⟨Cg, hCg, hgrid⟩ :=
    exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g (s + 2) 0 c (s + 1) 2
  refine ⟨Real.sqrt (2 * Cg), Real.sqrt_nonneg _, ?_⟩
  intro Φ V A B hA hB hΦsup hVsup hΦjet hVjet
  let grid : M → ℝ := fun x =>
    ∑ i ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g (s + 2) (c + i) x
          ((iteratedCovGrad (I := I) g (s + 2) c i Φ).toSection x) *
        ∑ l ∈ Finset.range (3 - i),
          riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + l) x
            ((iteratedCovGrad (I := I) g 0 (s + 1) l V).toSection x)
  obtain ⟨hgrid_int, hgrid_bound⟩ :=
    hgrid Φ V A B hA hB hΦsup hVsup
  have hgrid_int' : MeasureTheory.Integrable grid
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) g) := by
    simpa [grid] using hgrid_int
  have hgrid_bound' :
      (∫ x, grid x ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
        (I := I) (M := M) g)) ≤
        Cg * (B ^ 2 * ∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 +
            A ^ 2 * ∑ l ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 (s + 1) l V‖ ^ 2) := by
    simpa [grid] using hgrid_bound
  have hcross : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (s + 2) (c + 1) x
          ((covGrad (I := I) (M := M) g (s + 2) c Φ).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 2) x
          ((covGrad (I := I) (M := M) g 0 (s + 1) V).toSection x) ≤
        grid x := by
    intro x
    let f : ℕ → ℝ := fun i =>
      riemannianFiberNormSq (I := I) (M := M) g (s + 2) (c + i) x
        ((iteratedCovGrad (I := I) g (s + 2) c i Φ).toSection x)
    let q : ℕ → ℝ := fun l =>
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + l) x
        ((iteratedCovGrad (I := I) g 0 (s + 1) l V).toSection x)
    have hf : ∀ i, 0 ≤ f i := fun i =>
      riemannianFiberNormSq_nonneg
        (I := I) (M := M) g (s + 2) (c + i) x _
    have hq : ∀ l, 0 ≤ q l := fun l =>
      riemannianFiberNormSq_nonneg
        (I := I) (M := M) g 0 ((s + 1) + l) x _
    have hinner : q 1 ≤ ∑ l ∈ Finset.range (3 - 1), q l :=
      Finset.single_le_sum (fun l _ => hq l) (by norm_num)
    have houter :
        f 1 * (∑ l ∈ Finset.range (3 - 1), q l) ≤
          ∑ i ∈ Finset.range 3,
            f i * ∑ l ∈ Finset.range (3 - i), q l :=
      Finset.single_le_sum
        (f := fun i => f i * ∑ l ∈ Finset.range (3 - i), q l)
        (fun i _ => mul_nonneg (hf i) (Finset.sum_nonneg (fun l _ => hq l)))
        (by norm_num)
    have hpick : f 1 * q 1 ≤
        ∑ i ∈ Finset.range 3,
          f i * ∑ l ∈ Finset.range (3 - i), q l :=
      (mul_le_mul_of_nonneg_left hinner (hf 1)).trans houter
    simpa [grid, f, q, iteratedCovGrad_succ] using hpick
  let Z : SmoothCcTensor g 0 (c + 1) :=
    operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
      (covGrad (I := I) (M := M) g (s + 2) c Φ)
      (covGrad (I := I) (M := M) g 0 (s + 1) V)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (c + 1) x
          (Z.toSection x) ≤ grid x := by
    intro x
    dsimp [Z]
    exact (riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g 0 (s + 2) (c + 1) x _ _).trans (hcross x)
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 0 (c + 1) Z grid hgrid_int' hpt
  have hleft :
      B ^ 2 * (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2) ≤
        B ^ 2 * A ^ 2 :=
    mul_le_mul_of_nonneg_left hΦjet (sq_nonneg B)
  have hright :
      A ^ 2 * (∑ l ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) l V‖ ^ 2) ≤
        A ^ 2 * B ^ 2 :=
    mul_le_mul_of_nonneg_left hVjet (sq_nonneg A)
  have hsq' : ‖Z‖ ^ 2 ≤ 2 * Cg * A ^ 2 * B ^ 2 := by
    calc
      ‖Z‖ ^ 2 ≤ ∫ x, grid x
          ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            (I := I) (M := M) g) := hsq
      _ ≤ Cg * (B ^ 2 * ∑ i ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g (s + 2) c i Φ‖ ^ 2 +
            A ^ 2 * ∑ l ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 (s + 1) l V‖ ^ 2) := hgrid_bound'
      _ ≤ Cg * (2 * A ^ 2 * B ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hCg
        nlinarith [hleft, hright]
      _ = 2 * Cg * A ^ 2 * B ^ 2 := by ring
  change ‖Z‖ ≤ Real.sqrt (2 * Cg) * A * B
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Cg)]
  simpa [mul_assoc] using hsq'




theorem appCc_h2_h3_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (A : ℝ),
        0 ≤ A →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C * A * ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖ := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 1
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g s 3
  obtain ⟨Cgr, hCgr, hgr⟩ := hs3_grad_low2 (I := I) (M := M) hDim g s
  obtain ⟨Ccr, hCcr, hcr⟩ := appCc_grad_l2 (I := I) (M := M) g s c
  let d : ℝ := Module.finrank ℝ E
  let sd : ℝ := Real.sqrt d
  let K : ℝ := Cin + Ccr * Cgr + sd * Cin
  refine ⟨Csp * K, by
    dsimp [K, sd, d]
    positivity, ?_⟩
  intro Φ U A hA hΦsup hΦjet
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖
  let V : SmoothCcTensor g 0 (s + 1) :=
    covGrad (I := I) (M := M) g 0 s U
  let W : SmoothCcTensor g 0 (s + 2) :=
    iteratedCovGrad (I := I) g 0 s 2 U
  let Y : SmoothCcTensor g 0 c :=
    operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W
  have hN : 0 ≤ N := norm_nonneg _
  have hJ :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 s j U‖ ≤ Cin * N := by
    simpa [N] using hin U
  have hW0 : ‖W‖ ≤ Cin * N := by
    dsimp [W]
    exact (Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 s j U‖)
      (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
  have hW1 :
      ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ≤ Cin * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 s 3 U‖ ≤ Cin * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 s j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    rw [show ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ =
        ‖iteratedCovGrad (I := I) g 0 s 3 U‖ by
      exact grad_icg2_norm (I := I) (M := M) g s U]
    exact hpick
  have hVsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          (V.toSection x) ≤ (Cgr * N) ^ 2 := by
    simpa [V, N] using (hgr U).1
  have hVjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 (s + 1) j V‖ ^ 2) ≤
          (Cgr * N) ^ 2 := by
    simpa [V, N] using (hgr U).2
  have hcross :
      ‖operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
          (covGrad (I := I) (M := M) g (s + 2) c Φ) W‖ ≤
        Ccr * A * (Cgr * N) := by
    have hc := hcr Φ V A (Cgr * N) hA (mul_nonneg hCgr hN)
      hΦsup hVsup hΦjet hVjet
    simpa [V, W, iteratedCovGrad_succ] using hc
  have hslotSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          ((s + 2) + 1) (c + 1) x
          ((slotExtend (I := I) (M := M) g (s + 2) c Φ).toSection x) ≤
        (sd * A) ^ 2 := by
    intro x
    rw [rfns_slotExtend_eq (I := I) (M := M) g (s + 2) c Φ x]
    calc
      (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
            (Φ.toSection x)
          ≤ (Module.finrank ℝ E : ℝ) * A ^ 2 :=
        mul_le_mul_of_nonneg_left (hΦsup x) (Nat.cast_nonneg _)
      _ = (sd * A) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by dsimp [d]; positivity : 0 ≤ d)]
  have hY0 : ‖Y‖ ≤ Cin * A * N := by
    have h0 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g (s + 2) c Φ W A hA hΦsup
    dsimp [Y]
    calc
      ‖operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W‖ ≤ A * ‖W‖ := h0
      _ ≤ A * (Cin * N) := mul_le_mul_of_nonneg_left hW0 hA
      _ = Cin * A * N := by ring
  have hslot :
      ‖operatorFieldApply (I := I) (M := M) g ((s + 2) + 1) (c + 1)
          (slotExtend (I := I) (M := M) g (s + 2) c Φ)
          (covGrad (I := I) (M := M) g 0 (s + 2) W)‖ ≤
        sd * Cin * A * N := by
    have hs := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g ((s + 2) + 1) (c + 1)
      (slotExtend (I := I) (M := M) g (s + 2) c Φ)
      (covGrad (I := I) (M := M) g 0 (s + 2) W)
      (sd * A) (mul_nonneg (Real.sqrt_nonneg _) hA) hslotSup
    calc
      _ ≤ (sd * A) *
          ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ := hs
      _ ≤ (sd * A) * (Cin * N) :=
        mul_le_mul_of_nonneg_left hW1
          (mul_nonneg (Real.sqrt_nonneg _) hA)
      _ = sd * Cin * A * N := by ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g 0 c Y‖ ≤
        (Ccr * Cgr + sd * Cin) * A * N := by
    rw [show covGrad (I := I) (M := M) g 0 c Y =
        operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
            (covGrad (I := I) (M := M) g (s + 2) c Φ) W +
          operatorFieldApply (I := I) (M := M) g ((s + 2) + 1) (c + 1)
            (slotExtend (I := I) (M := M) g (s + 2) c Φ)
            (covGrad (I := I) (M := M) g 0 (s + 2) W) by
      dsimp [Y]
      exact covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 2) c Φ W]
    calc
      ‖operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
            (covGrad (I := I) (M := M) g (s + 2) c Φ) W +
          operatorFieldApply (I := I) (M := M) g ((s + 2) + 1) (c + 1)
            (slotExtend (I := I) (M := M) g (s + 2) c Φ)
            (covGrad (I := I) (M := M) g 0 (s + 2) W)‖
          ≤ ‖operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
              (covGrad (I := I) (M := M) g (s + 2) c Φ) W‖ +
            ‖operatorFieldApply (I := I) (M := M) g ((s + 2) + 1) (c + 1)
              (slotExtend (I := I) (M := M) g (s + 2) c Φ)
              (covGrad (I := I) (M := M) g 0 (s + 2) W)‖ := norm_add_le _ _
      _ ≤ Ccr * A * (Cgr * N) + sd * Cin * A * N :=
        add_le_add hcross hslot
      _ = (Ccr * Cgr + sd * Cin) * A * N := by ring
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤
        Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := by
    rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤ _
  calc
    ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖
        ≤ Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := hspec
    _ ≤ Csp * ((Cin + (Ccr * Cgr + sd * Cin)) * A * N) :=
      mul_le_mul_of_nonneg_left (by
        calc
          ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖
              ≤ Cin * A * N + (Ccr * Cgr + sd * Cin) * A * N :=
            add_le_add hY0 hY1
          _ = (Cin + (Ccr * Cgr + sd * Cin)) * A * N := by ring) hCsp
    _ = (Csp * K) * A * N := by dsimp [K]; ring



theorem appCc_c1_h2_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (U : SmoothCcTensor g 0 r) (B0 B1 : ℝ),
        0 ≤ B0 → 0 ≤ B1 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g r c x
              (Φ.toSection x) ≤ B0 ^ 2) →
        ‖covGrad (I := I) (M := M) g r c Φ‖ ≤ B1 →
        ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g r c Φ U)‖ ≤
          C * (B0 + B1) *
            ‖ccTensorToHs (I := I) (M := M) g r (2 : ℝ) U‖ := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 1
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g r 2
  obtain ⟨Cpt, hCpt, hpt⟩ := hs2_fiber_sq (I := I) (M := M) hDim g r
  let d : ℝ := Module.finrank ℝ E
  let sd : ℝ := Real.sqrt d
  let K : ℝ := Cin + Cpt + sd * Cin
  refine ⟨Csp * K, by
    dsimp [K, sd, d]
    positivity, ?_⟩
  intro Φ U B0 B1 hB0 hB1 hΦsup hΦ1
  let B : ℝ := B0 + B1
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g r (2 : ℝ) U‖
  let Y : SmoothCcTensor g 0 c := operatorFieldApply (I := I) (M := M) g r c Φ U
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hN : 0 ≤ N := norm_nonneg _
  have hB0sq : B0 ^ 2 ≤ B ^ 2 := by
    apply pow_le_pow_left₀ hB0 _ 2
    dsimp [B]
    linarith
  have hΦsupB : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r c x
          (Φ.toSection x) ≤ B ^ 2 := fun x => (hΦsup x).trans hB0sq
  have hΦ1B : ‖covGrad (I := I) (M := M) g r c Φ‖ ≤ B := by
    apply hΦ1.trans
    dsimp [B]
    linarith
  have hJ :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 r j U‖ ≤ Cin * N := by
    simpa [N] using hin U
  have hU0 : ‖U‖ ≤ Cin * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 r 0 U‖ ≤ Cin * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 r j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    simpa only [iteratedCovGrad_zero] using hpick
  have hU1 : ‖covGrad (I := I) (M := M) g 0 r U‖ ≤ Cin * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 r 1 U‖ ≤ Cin * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 r j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.zero_add] using hpick
  have hUsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 r x (U.toSection x) ≤
        (Cpt * N) ^ 2 := by
    intro x
    simpa only [N, mul_pow] using hpt U x
  have hcross :
      ‖operatorFieldApply (I := I) (M := M) g r (c + 1)
          (covGrad (I := I) (M := M) g r c Φ) U‖ ≤ Cpt * B * N := by
    have hc := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_right
      (I := I) (M := M) g r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) U
      (Cpt * N) (mul_nonneg hCpt hN) hUsup
    calc
      _ ≤ ‖covGrad (I := I) (M := M) g r c Φ‖ * (Cpt * N) := hc
      _ ≤ B * (Cpt * N) := mul_le_mul_of_nonneg_right hΦ1B (mul_nonneg hCpt hN)
      _ = Cpt * B * N := by ring
  have hslotSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (r + 1) (c + 1) x
          ((slotExtend (I := I) (M := M) g r c Φ).toSection x) ≤
        (sd * B) ^ 2 := by
    intro x
    rw [rfns_slotExtend_eq (I := I) (M := M) g r c Φ x]
    calc
      (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g r c x (Φ.toSection x)
          ≤ (Module.finrank ℝ E : ℝ) * B ^ 2 :=
        mul_le_mul_of_nonneg_left (hΦsupB x) (Nat.cast_nonneg _)
      _ = (sd * B) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by dsimp [d]; positivity : 0 ≤ d)]
  have hY0 : ‖Y‖ ≤ Cin * B * N := by
    have h0 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g r c Φ U B hB hΦsupB
    dsimp [Y]
    calc
      ‖operatorFieldApply (I := I) (M := M) g r c Φ U‖ ≤ B * ‖U‖ := h0
      _ ≤ B * (Cin * N) := mul_le_mul_of_nonneg_left hU0 hB
      _ = Cin * B * N := by ring
  have hslot :
      ‖operatorFieldApply (I := I) (M := M) g (r + 1) (c + 1)
          (slotExtend (I := I) (M := M) g r c Φ)
          (covGrad (I := I) (M := M) g 0 r U)‖ ≤ sd * Cin * B * N := by
    have hs := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ)
      (covGrad (I := I) (M := M) g 0 r U)
      (sd * B) (mul_nonneg (Real.sqrt_nonneg _) hB) hslotSup
    calc
      _ ≤ (sd * B) * ‖covGrad (I := I) (M := M) g 0 r U‖ := hs
      _ ≤ (sd * B) * (Cin * N) :=
        mul_le_mul_of_nonneg_left hU1 (mul_nonneg (Real.sqrt_nonneg _) hB)
      _ = sd * Cin * B * N := by ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g 0 c Y‖ ≤
        (Cpt + sd * Cin) * B * N := by
    rw [show covGrad (I := I) (M := M) g 0 c Y =
        operatorFieldApply (I := I) (M := M) g r (c + 1)
            (covGrad (I := I) (M := M) g r c Φ) U +
          operatorFieldApply (I := I) (M := M) g (r + 1) (c + 1)
            (slotExtend (I := I) (M := M) g r c Φ)
            (covGrad (I := I) (M := M) g 0 r U) by
      dsimp [Y]
      exact covGrad_operatorFieldApply_eq (I := I) (M := M) g r c Φ U]
    calc
      _ ≤ ‖operatorFieldApply (I := I) (M := M) g r (c + 1)
              (covGrad (I := I) (M := M) g r c Φ) U‖ +
            ‖operatorFieldApply (I := I) (M := M) g (r + 1) (c + 1)
              (slotExtend (I := I) (M := M) g r c Φ)
              (covGrad (I := I) (M := M) g 0 r U)‖ := norm_add_le _ _
      _ ≤ Cpt * B * N + sd * Cin * B * N := add_le_add hcross hslot
      _ = (Cpt + sd * Cin) * B * N := by ring
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤
        Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := by
    rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤ _
  calc
    _ ≤ Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := hspec
    _ ≤ Csp * ((Cin + (Cpt + sd * Cin)) * B * N) :=
      mul_le_mul_of_nonneg_left (by
        calc
          ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖
              ≤ Cin * B * N + (Cpt + sd * Cin) * B * N := add_le_add hY0 hY1
          _ = (Cin + (Cpt + sd * Cin)) * B * N := by ring) hCsp
    _ = (Csp * K) * (B0 + B1) * N := by dsimp [B, K]; ring



theorem appCc_h2_h2_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (U : SmoothCcTensor g 0 r) (A : ℝ),
        0 ≤ A →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g r c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g r c Φ U)‖ ≤
          C * A * ‖ccTensorToHs (I := I) (M := M) g r (2 : ℝ) U‖ := by
  obtain ⟨C, hC, hbound⟩ := appCc_c1_h2_h1 (I := I) (M := M) hDim g r c
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro Φ U A hA hΦsup hΦjet
  have hΦ1sq :
      ‖covGrad (I := I) (M := M) g r c Φ‖ ^ 2 ≤ A ^ 2 := by
    have hpick : ‖iteratedCovGrad (I := I) g r c 1 Φ‖ ^ 2 ≤
        ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2)
        (fun j _ => sq_nonneg _) (by norm_num)
    simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.zero_add] using
      hpick.trans hΦjet
  have hΦ1 : ‖covGrad (I := I) (M := M) g r c Φ‖ ≤ A := by
    nlinarith [norm_nonneg (covGrad (I := I) (M := M) g r c Φ)]
  calc
    _ ≤ C * (A + A) *
          ‖ccTensorToHs (I := I) (M := M) g r (2 : ℝ) U‖ :=
      hbound Φ U A A hA hA hΦsup hΦ1
    _ = (2 * C) * A *
          ‖ccTensorToHs (I := I) (M := M) g r (2 : ℝ) U‖ := by ring



theorem appCc_h2_cov_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 (s + 1))
        (A : ℝ),
        0 ≤ A →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ A ^ 2) →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ
              (covGrad (I := I) (M := M) g 0 (s + 1) U))‖ ≤
          C * A * ‖ccTensorToHs (I := I) (M := M) g (s + 1) (2 : ℝ) U‖ := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 1
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g (s + 1) 2
  obtain ⟨Cpt, hCpt, hpt⟩ := hs2_fiber_sq (I := I) (M := M) hDim g (s + 1)
  obtain ⟨Cjet, hCjet, hjet⟩ := hs2_low2 (I := I) (M := M) g (s + 1)
  obtain ⟨Ccr, hCcr, hcr⟩ := appCc_grad_l2 (I := I) (M := M) g s c
  let Cu : ℝ := Cpt + Cjet
  let d : ℝ := Module.finrank ℝ E
  let sd : ℝ := Real.sqrt d
  let K : ℝ := Cin + Ccr * Cu + sd * Cin
  refine ⟨Csp * K, by
    dsimp [K, sd, d, Cu]
    positivity, ?_⟩
  intro Φ U A hA hΦsup hΦjet
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g (s + 1) (2 : ℝ) U‖
  let W : SmoothCcTensor g 0 (s + 2) :=
    covGrad (I := I) (M := M) g 0 (s + 1) U
  let Y : SmoothCcTensor g 0 c :=
    operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W
  have hN : 0 ≤ N := norm_nonneg _
  have hCu : 0 ≤ Cu := by dsimp [Cu]; positivity
  have hCpt_le : Cpt ≤ Cu := by dsimp [Cu]; linarith
  have hCjet_le : Cjet ≤ Cu := by dsimp [Cu]; linarith
  have hJ :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 1) j U‖ ≤ Cin * N := by
    simpa [N] using hin U
  have hW0 : ‖W‖ ≤ Cin * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 (s + 1) 1 U‖ ≤ Cin * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 (s + 1) j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    simpa [W, iteratedCovGrad_succ] using hpick
  have hW1 :
      ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ≤ Cin * N := by
    have hpick : ‖iteratedCovGrad (I := I) g 0 (s + 1) 2 U‖ ≤ Cin * N :=
      (Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g 0 (s + 1) j U‖)
        (fun j _ => norm_nonneg _) (by norm_num)).trans hJ
    calc
      ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ =
          ‖iteratedCovGrad (I := I) g 0 ((s + 1) + 1) 1
            (iteratedCovGrad (I := I) g 0 (s + 1) 1 U)‖ := by
              simp only [W, iteratedCovGrad_succ, iteratedCovGrad_zero, Nat.add_zero]
      _ = ‖iteratedCovGrad (I := I) g 0 (s + 1) (1 + 1) U‖ :=
        icg_comp_norm (I := I) (M := M) g (s + 1) 1 1 U
      _ ≤ Cin * N := by norm_num at hpick ⊢; exact hpick
  have hUsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          (U.toSection x) ≤ (Cu * N) ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          (U.toSection x) ≤ Cpt ^ 2 * N ^ 2 := by simpa [N] using hpt U x
      _ = (Cpt * N) ^ 2 := by ring
      _ ≤ (Cu * N) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCpt hN)
          (mul_le_mul_of_nonneg_right hCpt_le hN) 2
  have hUjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 (s + 1) j U‖ ^ 2) ≤
          (Cu * N) ^ 2 := by
    calc
      _ ≤ (Cjet * N) ^ 2 := by simpa [N] using hjet U
      _ ≤ (Cu * N) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCjet hN)
          (mul_le_mul_of_nonneg_right hCjet_le hN) 2
  have hcross :
      ‖operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
          (covGrad (I := I) (M := M) g (s + 2) c Φ) W‖ ≤
        Ccr * A * (Cu * N) := by
    simpa [W] using hcr Φ U A (Cu * N) hA (mul_nonneg hCu hN)
      hΦsup hUsup hΦjet hUjet
  have hslotSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          ((s + 2) + 1) (c + 1) x
          ((slotExtend (I := I) (M := M) g (s + 2) c Φ).toSection x) ≤
        (sd * A) ^ 2 := by
    intro x
    rw [rfns_slotExtend_eq (I := I) (M := M) g (s + 2) c Φ x]
    calc
      (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
            (Φ.toSection x)
          ≤ (Module.finrank ℝ E : ℝ) * A ^ 2 :=
        mul_le_mul_of_nonneg_left (hΦsup x) (Nat.cast_nonneg _)
      _ = (sd * A) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by dsimp [d]; positivity : 0 ≤ d)]
  have hY0 : ‖Y‖ ≤ Cin * A * N := by
    have h0 := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g (s + 2) c Φ W A hA hΦsup
    dsimp [Y]
    calc
      ‖operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W‖ ≤ A * ‖W‖ := h0
      _ ≤ A * (Cin * N) := mul_le_mul_of_nonneg_left hW0 hA
      _ = Cin * A * N := by ring
  have hslot :
      ‖operatorFieldApply (I := I) (M := M) g ((s + 2) + 1) (c + 1)
          (slotExtend (I := I) (M := M) g (s + 2) c Φ)
          (covGrad (I := I) (M := M) g 0 (s + 2) W)‖ ≤
        sd * Cin * A * N := by
    have hs := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g ((s + 2) + 1) (c + 1)
      (slotExtend (I := I) (M := M) g (s + 2) c Φ)
      (covGrad (I := I) (M := M) g 0 (s + 2) W)
      (sd * A) (mul_nonneg (Real.sqrt_nonneg _) hA) hslotSup
    calc
      _ ≤ (sd * A) *
          ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ := hs
      _ ≤ (sd * A) * (Cin * N) :=
        mul_le_mul_of_nonneg_left hW1
          (mul_nonneg (Real.sqrt_nonneg _) hA)
      _ = sd * Cin * A * N := by ring
  have hY1 :
      ‖covGrad (I := I) (M := M) g 0 c Y‖ ≤
        (Ccr * Cu + sd * Cin) * A * N := by
    rw [show covGrad (I := I) (M := M) g 0 c Y =
        operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
            (covGrad (I := I) (M := M) g (s + 2) c Φ) W +
          operatorFieldApply (I := I) (M := M) g ((s + 2) + 1) (c + 1)
            (slotExtend (I := I) (M := M) g (s + 2) c Φ)
            (covGrad (I := I) (M := M) g 0 (s + 2) W) by
      dsimp [Y]
      exact covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 2) c Φ W]
    calc
      _ ≤ ‖operatorFieldApply (I := I) (M := M) g (s + 2) (c + 1)
              (covGrad (I := I) (M := M) g (s + 2) c Φ) W‖ +
            ‖operatorFieldApply (I := I) (M := M) g ((s + 2) + 1) (c + 1)
              (slotExtend (I := I) (M := M) g (s + 2) c Φ)
              (covGrad (I := I) (M := M) g 0 (s + 2) W)‖ := norm_add_le _ _
      _ ≤ Ccr * A * (Cu * N) + sd * Cin * A * N := add_le_add hcross hslot
      _ = (Ccr * Cu + sd * Cin) * A * N := by ring
  have hspec :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤
        Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := by
    rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) Y‖ ≤ _
  calc
    _ ≤ Csp * (‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖) := hspec
    _ ≤ Csp * ((Cin + (Ccr * Cu + sd * Cin)) * A * N) :=
      mul_le_mul_of_nonneg_left (by
        calc
          ‖Y‖ + ‖covGrad (I := I) (M := M) g 0 c Y‖
              ≤ Cin * A * N + (Ccr * Cu + sd * Cin) * A * N :=
            add_le_add hY0 hY1
          _ = (Cin + (Ccr * Cu + sd * Cin)) * A * N := by ring) hCsp
    _ = (Csp * K) * A * N := by dsimp [K]; ring



theorem appCc_h3_h1
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (B0 B1 : ℝ),
        0 ≤ B0 → 0 ≤ B1 →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) c x
              (Φ.toSection x) ≤ B0 ^ 2) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g (s + 2) (c + 1) x
              ((covGrad (I := I) (M := M) g (s + 2) c Φ).toSection x) ≤ B1 ^ 2) →
        ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ)
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C * (B0 + B1) *
            ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖ := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 1
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g s 3
  let G0 : ℝ := diagonalGridGrowthFactor (E := E) 0
  let G1 : ℝ := diagonalGridGrowthFactor (E := E) 1
  let C0 : ℝ := Real.sqrt G0
  let C1 : ℝ := Real.sqrt (3 * G1)
  refine ⟨Csp * (C0 + C1) * Cin, by positivity, ?_⟩
  intro Φ U B0 B1 hB0 hB1 hΦ0 hΦ1
  let B : ℝ := B0 + B1
  let J : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 s j U‖
  let W : SmoothCcTensor g 0 (s + 2) :=
    iteratedCovGrad (I := I) g 0 s 2 U
  let A : SmoothCcTensor g 0 c :=
    operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hB0sq : B0 ^ 2 ≤ B ^ 2 := by
    apply pow_le_pow_left₀ hB0 _ 2
    dsimp [B]
    linarith
  have hB1sq : B1 ^ 2 ≤ B ^ 2 := by
    apply pow_le_pow_left₀ hB1 _ 2
    dsimp [B]
    linarith
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hW0 : ‖W‖ ≤ J := by
    dsimp [W, J]
    refine Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 s j U‖)
      (fun _ _ => norm_nonneg _) ?_
    simp only [Finset.mem_range]
    omega
  have hW1 :
      ‖iteratedCovGrad (I := I) g 0 (s + 2) 1 W‖ ≤ J := by
    rw [show ‖iteratedCovGrad (I := I) g 0 (s + 2) 1 W‖ =
        ‖iteratedCovGrad (I := I) g 0 s 3 U‖ by
      exact grad_icg2_norm (I := I) (M := M) g s U]
    dsimp [J]
    refine Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 s j U‖)
      (fun _ _ => norm_nonneg _) ?_
    simp only [Finset.mem_range]
    omega
  have hW1' : ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ≤ J := by
    simpa only [iteratedCovGrad_succ, Nat.add_zero] using hW1
  let K : ℕ → ℝ := fun _ => B ^ 2
  have hK : ∀ i, i ≤ 1 → 0 ≤ K i := fun _ _ => sq_nonneg B
  have hΦK : ∀ i, i ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g (s + 2) (c + i) x
          ((iteratedCovGrad (I := I) g (s + 2) c i Φ).toSection x) ≤ K i := by
    intro i hi x
    interval_cases i
    · simpa [K] using (hΦ0 x).trans hB0sq
    · simpa [K, iteratedCovGrad_succ] using (hΦ1 x).trans hB1sq
  have hsq0raw := appCc_jet_l2Sq_le (I := I) (M := M) g (s + 2) c 0
    Φ W K (fun i hi => hK i (by omega))
    (fun i hi => hΦK i (by omega))
  have hsq1raw := appCc_jet_l2Sq_le (I := I) (M := M) g (s + 2) c 1
    Φ W K hK hΦK
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    Nat.add_zero, Nat.zero_add, Nat.reduceSub, iteratedCovGrad_zero,
    iteratedCovGrad_succ] at hsq0raw hsq1raw
  dsimp [K] at hsq0raw hsq1raw
  have hsq0raw' :
      ‖operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W‖ ^ 2 ≤
        diagonalGridGrowthFactor (E := E) 0 * (B ^ 2 * ‖W‖ ^ 2) := by
    simpa only [zero_add] using hsq0raw
  have hsq1raw' :
      ‖covGrad (I := I) (M := M) g 0 c
          (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2 ≤
        diagonalGridGrowthFactor (E := E) 1 *
          (B ^ 2 * (‖W‖ ^ 2 +
            ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ^ 2) +
            B ^ 2 * ‖W‖ ^ 2) := by
    simpa only [zero_add] using hsq1raw
  have hsq0 : ‖A‖ ^ 2 ≤ G0 * B ^ 2 * J ^ 2 := by
    dsimp [A]
    calc
      ‖operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W‖ ^ 2
          ≤ diagonalGridGrowthFactor (E := E) 0 * (B ^ 2 * ‖W‖ ^ 2) := hsq0raw'
      _ ≤ diagonalGridGrowthFactor (E := E) 0 * (B ^ 2 * J ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg W) hW0 2) (sq_nonneg B))
          (appCcGdiag_nonneg (E := E) 0)
      _ = G0 * B ^ 2 * J ^ 2 := by dsimp [G0]; ring
  have hsq1 :
      ‖iteratedCovGrad (I := I) g 0 c 1 A‖ ^ 2 ≤
        (3 * G1) * B ^ 2 * J ^ 2 := by
    have hW0sq := pow_le_pow_left₀ (norm_nonneg W) hW0 2
    have hW1sq := pow_le_pow_left₀
      (norm_nonneg (covGrad (I := I) (M := M) g 0 (s + 2) W)) hW1' 2
    dsimp [A]
    change ‖covGrad (I := I) (M := M) g 0 c
        (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2 ≤ _
    calc
      ‖covGrad (I := I) (M := M) g 0 c
          (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W)‖ ^ 2
          ≤ diagonalGridGrowthFactor (E := E) 1 *
              (B ^ 2 * (‖W‖ ^ 2 +
                ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ^ 2) +
                B ^ 2 * ‖W‖ ^ 2) := hsq1raw'
      _ ≤ diagonalGridGrowthFactor (E := E) 1 * (3 * B ^ 2 * J ^ 2) :=
        mul_le_mul_of_nonneg_left
          (show B ^ 2 * (‖W‖ ^ 2 +
                ‖covGrad (I := I) (M := M) g 0 (s + 2) W‖ ^ 2) +
                B ^ 2 * ‖W‖ ^ 2 ≤ 3 * B ^ 2 * J ^ 2 by
              nlinarith [sq_nonneg B, sq_nonneg J])
          (appCcGdiag_nonneg (E := E) 1)
      _ = (3 * G1) * B ^ 2 * J ^ 2 := by dsimp [G1]; ring
  have hA0 : ‖A‖ ≤ C0 * B * J := by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (appCcGdiag_nonneg (E := E) 0)]
    simpa [C0, G0, mul_assoc] using hsq0
  have hA1 : ‖iteratedCovGrad (I := I) g 0 c 1 A‖ ≤ C1 * B * J := by
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (appCcGdiag_nonneg (E := E) 1))]
    simpa [C1, G1, mul_assoc] using hsq1
  have hspA :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖ ≤
        Csp * (‖A‖ + ‖iteratedCovGrad (I := I) g 0 c 1 A‖) := by
    rw [← show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, iteratedCovGrad_zero, iteratedCovGrad_succ] using hsp A
  have hAJ :
      ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖ ≤
        Csp * ((C0 + C1) * B * J) := by
    refine le_trans hspA (mul_le_mul_of_nonneg_left ?_ hCsp)
    calc
      ‖A‖ + ‖iteratedCovGrad (I := I) g 0 c 1 A‖
          ≤ C0 * B * J + C1 * B * J := add_le_add hA0 hA1
      _ = (C0 + C1) * B * J := by ring
  have hJU : J ≤ Cin *
      ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖ := by
    simpa [J] using hin U
  change ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖ ≤ _
  calc
    ‖ccTensorToHs (I := I) (M := M) g c (1 : ℝ) A‖
        ≤ Csp * ((C0 + C1) * B * J) := hAJ
    _ ≤ Csp * ((C0 + C1) * B *
          (Cin * ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hJU
          (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hB))
        hCsp
    _ = (Csp * (C0 + C1) * Cin) * (B0 + B1) *
          ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖ := by
      dsimp [B]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
