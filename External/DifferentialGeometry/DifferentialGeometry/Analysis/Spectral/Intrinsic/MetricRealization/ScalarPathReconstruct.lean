import DifferentialGeometry.Analysis.Calculus.ContDiffOnTsum
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarEigenJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralSmoothRepresentative
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.RankZero
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Topology Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (eigenvectorSmooth scalar0_raw_eq
    toEuclidean_extChartAt_mem_chartTargetEuclid
    symm_toEuclidean_symm_toEuclidean_extChartAt)
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


noncomputable def scalarMode
    (g : SmoothRiemannianMetric I M)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    (α : M) (i : TensorEigenIdx (I := I) (M := M) g 0 0) :
    ℝ × EuclN → ℝ :=
  fun q => c i q.1 *
    tensorComponentEuclideanChart (I := I) (M := M) g 0 0
      (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
      α Fin.elim0 Fin.elim0 q.2



noncomputable def scalarSpecSum
    (g : SmoothRiemannianMetric I M)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ) :
    ℝ → M → ℝ :=
  fun t x =>
    ∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
      c i t * TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (eigenvectorSmooth (I := I) (M := M) g 0 0 i).toSection x



theorem scalarSpec_cc
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0) :
    scalarSpecSum (I := I) (M := M) g
        (fun i _ => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 0)
          (SmoothCcTensor.toL2 S) i) 0 =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection := by
  classical
  let σ : ℝ := ((Module.finrank ℝ E / 2 + 1 : ℕ) : ℝ)
  have hσ : 0 ≤ σ := by
    dsimp only [σ]
    positivity
  let V : tensorHs (I := I) (M := M) g 0 0 σ :=
    ccTensorToHs (I := I) (M := M) g 0 σ S
  let P : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) →
      SmoothCcTensor g 0 0 := fun F =>
    ∑ i ∈ F, V.coeff i •
      eigenvectorSmooth (I := I) (M := M) g 0 0 i
  have hP_hs (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0)) :
      ccTensorToHs (I := I) (M := M) g 0 σ (P F) =
        ∑ i ∈ F, V.coeff i •
          tensorHsBasisVec (I := I) (M := M)
            (g := g) (r := 0) (s := 0) σ i := by
    rw [← ccToHsLin_apply]
    simp only [P, map_sum, map_smul, ccToHsLin_apply,
      ccToHs_eigen (I := I) (M := M) g 0 hσ]
  have hP_tendsto : Tendsto
      (fun F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) =>
        ccTensorToHs (I := I) (M := M) g 0 σ (P F))
      atTop (𝓝 V) := by
    rw [show (fun F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) =>
        ccTensorToHs (I := I) (M := M) g 0 σ (P F)) =
      fun F => ∑ i ∈ F, V.coeff i •
        tensorHsBasisVec (I := I) (M := M)
          (g := g) (r := 0) (s := 0) σ i by
      funext F
      exact hP_hs F]
    exact tensorHs.hasSum_smul_basisVec (I := I) (M := M) V
  funext x
  obtain ⟨C, hC, heval⟩ := scalar0_abs_le_hs (I := I) (M := M) g
  have hscalar_tendsto : Tendsto
      (fun F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) =>
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) (P F).toSection x)
      atTop
      (𝓝 (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hdiff : Tendsto
        (fun F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) =>
          ccTensorToHs (I := I) (M := M) g 0 σ (P F) - V)
        atTop (𝓝 0) := by
      simpa only [sub_self] using hP_tendsto.sub
        (tendsto_const_nhds : Tendsto
          (fun _ : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) => V)
          atTop (𝓝 V))
    have hupper : Tendsto
        (fun F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) =>
          C * ‖ccTensorToHs (I := I) (M := M) g 0 σ (P F) - V‖)
        atTop (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hdiff.norm
    refine squeeze_zero (fun F => dist_nonneg) (fun F => ?_) hupper
    rw [Real.dist_eq]
    have h := heval (P F - S) x
    rw [SmoothCcTensor.toSection_sub, TensorRSField.scalar0_sub,
      Pi.sub_apply] at h
    change |TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) (P F).toSection x -
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x| ≤
      C * ‖ccToHsLin (I := I) (M := M) g 0 σ (P F - S)‖ at h
    rw [map_sub, ccToHsLin_apply, ccToHsLin_apply] at h
    change _ ≤ C * ‖ccTensorToHs (I := I) (M := M) g 0 σ (P F) - V‖ at h
    exact h
  have hP_scalar (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0)) :
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) (P F).toSection x =
        ∑ i ∈ F, V.coeff i *
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
            (eigenvectorSmooth (I := I) (M := M) g 0 0 i).toSection x := by
    induction F using Finset.induction_on with
    | empty => simp [P]
    | @insert i F hi ih =>
        simp [P, hi, ih, smul_eq_mul]
  have hsum : HasSum
      (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
        V.coeff i * TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
          (eigenvectorSmooth (I := I) (M := M) g 0 0 i).toSection x)
      (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x) := by
    change Tendsto
      (fun F : Finset (TensorEigenIdx (I := I) (M := M) g 0 0) =>
        ∑ i ∈ F, V.coeff i *
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
            (eigenvectorSmooth (I := I) (M := M) g 0 0 i).toSection x)
      atTop
      (𝓝 (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection x))
    simpa only [hP_scalar] using hscalar_tendsto
  unfold scalarSpecSum
  simpa only [V, ccTensorToHs_coeff] using hsum.tsum_eq

omit [BoundarylessManifold I M] in


lemma scalarMode_eq
    (g : SmoothRiemannianMetric I M)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    (α : M) (i : TensorEigenIdx (I := I) (M := M) g 0 0)
    {t : ℝ} {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    scalarMode (I := I) (M := M) g c α i (t, y) =
      c i t * TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (eigenvectorSmooth (I := I) (M := M) g 0 0 i).toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  unfold scalarMode
  rw [tensorComponentEuclideanChart, Function.comp_apply, Function.comp_apply]
  exact congrArg (c i t * ·)
    (scalar0_raw_eq (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 0 i) α
      (symm_toEuclidean_symm_mem_chartAtSource
        (I := I) (M := M) α hy))

omit [BoundarylessManifold I M] in


lemma scalarSpec_chart
    (g : SmoothRiemannianMetric I M)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    (α : M) {t : ℝ} {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
        scalarMode (I := I) (M := M) g c α i (t, y)) =
      scalarSpecSum (I := I) (M := M) g c t
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  unfold scalarSpecSum
  apply tsum_congr
  intro i
  exact scalarMode_eq (I := I) (M := M) g c α i hy



omit [BoundarylessManifold I M] in
lemma scalarMode_smooth
    (g : SmoothRiemannianMetric I M)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    (α : M) (i : TensorEigenIdx (I := I) (M := M) g 0 0)
    {U : Set ℝ} {N : WithTop ℕ∞}
    (hN : N ≤ (∞ : WithTop ℕ∞))
    (hc : ContDiffOn ℝ N (c i) U) :
    ContDiffOn ℝ N (scalarMode (I := I) (M := M) g c α i)
      (U ×ˢ chartTargetEuclid (I := I) (M := M) α) := by
  have ht : ContDiffOn ℝ N (fun q : ℝ × EuclN => c i q.1)
      (U ×ˢ chartTargetEuclid (I := I) (M := M) α) :=
    hc.comp contDiffOn_fst Set.mapsTo_fst_prod
  have hx : ContDiffOn ℝ N
      (fun q : ℝ × EuclN =>
        tensorComponentEuclideanChart (I := I) (M := M) g 0 0
          (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
          α Fin.elim0 Fin.elim0 q.2)
      (U ×ˢ chartTargetEuclid (I := I) (M := M) α) :=
    ((rawPullR_contDiffOn (I := I) (M := M) g 0 0
      (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
      α Fin.elim0 Fin.elim0).of_le
        hN).comp
        contDiffOn_snd Set.mapsTo_snd_prod
  exact ht.mul hx

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma weight_two_sq
    (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 0) (p : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (2 * p) =
      ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p) ^ 2 := by
  have hbase : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    linarith [tensor_lambda_nonneg (I := I) (M := M) i]
  unfold tensorSobolevWeight
  rw [show (2 : ℝ) * p = p * 2 by ring, Real.rpow_mul hbase.le,
    Real.rpow_two]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma abs_le_sqrt_wt
    (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 0) (p : ℝ) {v C : ℝ}
    (h : tensorSobolevWeight (I := I) (M := M) i (2 * p) * v ^ 2 ≤ C) :
    |v| ≤ Real.sqrt C *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p) := by
  have hbase : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    linarith [tensor_lambda_nonneg (I := I) (M := M) i]
  rw [weight_two_sq (I := I) (M := M) g i p] at h
  set W := (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p with hW_def
  have hW_pos : 0 < W := Real.rpow_pos_of_pos hbase _
  have hC_nn : 0 ≤ C := le_trans (by positivity) h
  have habs : |v| ≤ Real.sqrt C / W := by
    rw [le_div_iff₀ hW_pos]
    have hsq : (|v| * W) ^ 2 ≤ (Real.sqrt C) ^ 2 := by
      rw [Real.sq_sqrt hC_nn, mul_pow, sq_abs]
      nlinarith [h, hW_pos.le]
    nlinarith [Real.sqrt_nonneg C, hsq, mul_nonneg (abs_nonneg v) hW_pos.le,
      sq_nonneg (|v| * W - Real.sqrt C)]
  rw [Real.rpow_neg hbase.le]
  rw [div_eq_mul_inv] at habs
  rwa [← hW_def]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma sqrt_mul_tail
    (g : SmoothRiemannianMetric I M) (p : ℝ)
    (C : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ)
    (hC : Summable C) (hC_nn : ∀ i, 0 ≤ C i)
    (htail : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-p))) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
      Real.sqrt (C i) * tensorSobolevWeight (I := I) (M := M) i (-(p / 2))) := by
  have hbase : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 0,
      0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    linarith [tensor_lambda_nonneg (I := I) (M := M) i]
  have htail' : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
      tensorSobolevWeight (I := I) (M := M) i (-p)) := by
    simpa only [tensorSobolevWeight] using htail
  have hw_sq : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 0,
      tensorSobolevWeight (I := I) (M := M) i (-(p / 2)) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i (-p) := by
    intro i
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast
      ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(p / 2))) 2,
      ← Real.rpow_mul (hbase i).le]
    congr 1
    push_cast
    ring
  have hbound : ∀ i,
      Real.sqrt (C i) * tensorSobolevWeight (I := I) (M := M) i (-(p / 2)) ≤
        (C i + tensorSobolevWeight (I := I) (M := M) i (-p)) / 2 := by
    intro i
    have h : Real.sqrt (C i) *
          tensorSobolevWeight (I := I) (M := M) i (-(p / 2)) ≤
        (Real.sqrt (C i) ^ 2 +
          tensorSobolevWeight (I := I) (M := M) i (-(p / 2)) ^ 2) / 2 := by
      nlinarith [sq_nonneg
        (Real.sqrt (C i) - tensorSobolevWeight (I := I) (M := M) i (-(p / 2)))]
    rw [Real.sq_sqrt (hC_nn i), hw_sq i] at h
    exact h
  exact Summable.of_nonneg_of_le
    (fun i => mul_nonneg (Real.sqrt_nonneg _)
      (tensorSobolevWeight_nonneg (I := I) (M := M) i _))
    hbound ((hC.add htail').div_const 2)

private lemma clm_jet_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (i : ℕ) (hi : 1 ≤ i) (x : F) :
    ‖iteratedFDeriv ℝ i (fun y => L y) x‖ ≤ (‖L‖ + 1) ^ i := by
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · interval_cases i
    rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    simp only [pow_one]
    linarith [norm_nonneg L]
  · obtain ⟨j, rfl⟩ : ∃ j, i = (j + 1) + 1 := ⟨i - 2, by omega⟩
    have hz : ‖iteratedFDeriv ℝ ((j + 1) + 1) (fun y => L y) x‖ = 0 := by
      rw [← norm_iteratedFDeriv_fderiv]
      have hfd : fderiv ℝ (fun y => L y) = fun _ : F => (L : F →L[ℝ] G) := by
        funext y
        exact ContinuousLinearMap.fderiv L
      rw [hfd, iteratedFDeriv_const_of_ne (by omega) (L : F →L[ℝ] G)]
      simp
    rw [hz]
    positivity

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma jet_fst_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℝ → ℝ) {U : Set ℝ} {N : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    {A : Set ℝ} {B : Set X} (hAU : A ⊆ U)
    (hUD : UniqueDiffOn ℝ (A ×ˢ B))
    (n : ℕ) (hn : (n : WithTop ℕ∞) ≤ N)
    (q : ℝ × X) (hq : q ∈ A ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedDeriv j f q.1‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun y : ℝ × X => f y.1)
        (A ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C *
        (‖ContinuousLinearMap.fst ℝ ℝ X‖ + 1) ^ n := by
  classical
  let L : (ℝ × X) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ X
  have hmaps : Set.MapsTo (fun y : ℝ × X => y.1) (A ×ˢ B) U :=
    fun y hy => hAU hy.1
  have hbound := norm_iteratedFDerivWithin_comp_le
    (g := f) (f := fun y : ℝ × X => y.1)
    (n := n) (s := A ×ˢ B) (t := U) (x := q) (N := N)
    hf ((contDiff_fst (𝕜 := ℝ)).of_le le_top).contDiffOn hn
    hU.uniqueDiffOn hUD hmaps hq (C := C) (D := ‖L‖ + 1)
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen j hU (hmaps hq),
        norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC j hj)
    (fun j hj _ => by
      have heq : iteratedFDerivWithin ℝ j (fun y : ℝ × X => y.1)
          (A ×ˢ B) q =
          iteratedFDeriv ℝ j (fun y : ℝ × X => y.1) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_fst (𝕜 := ℝ)).contDiffAt.of_le le_top) hq
      rw [heq]
      exact clm_jet_le L j hj q)
  simpa only [L, Function.comp_apply] using hbound

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma jet_snd_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℝ) {O : Set X} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O)
    {A : Set ℝ} {B : Set X} (hBO : B ⊆ O)
    (hUD : UniqueDiffOn ℝ (A ×ˢ B))
    (n : ℕ) (q : ℝ × X) (hq : q ∈ A ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedFDerivWithin ℝ j f O q.2‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun y : ℝ × X => f y.2)
        (A ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C *
        (‖ContinuousLinearMap.snd ℝ ℝ X‖ + 1) ^ n := by
  classical
  let L : (ℝ × X) →L[ℝ] X := ContinuousLinearMap.snd ℝ ℝ X
  have hmaps : Set.MapsTo (fun y : ℝ × X => y.2) (A ×ˢ B) O :=
    fun y hy => hBO hy.2
  have hbound := norm_iteratedFDerivWithin_comp_le
    (g := f) (f := fun y : ℝ × X => y.2)
    (n := n) (s := A ×ˢ B) (t := O) (x := q) (N := (∞ : WithTop ℕ∞))
    hf ((contDiff_snd (𝕜 := ℝ)).contDiffOn) (by exact_mod_cast le_top)
    hO.uniqueDiffOn hUD hmaps hq (C := C) (D := ‖L‖ + 1)
    (fun j hj => hC j hj)
    (fun j hj _ => by
      have heq : iteratedFDerivWithin ℝ j (fun y : ℝ × X => y.2)
          (A ×ˢ B) q =
          iteratedFDeriv ℝ j (fun y : ℝ × X => y.2) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_snd (𝕜 := ℝ)).contDiffAt.of_le le_top) hq
      rw [heq]
      exact clm_jet_le L j hj q)
  simpa only [L, Function.comp_apply] using hbound

omit [BoundarylessManifold I M] in



omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem prodMode_majorant
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : SmoothRiemannianMetric I M)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 0)
    {a b : ℝ} (hab : a < b) (n : ℕ)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hIccU : Set.Icc a b ⊆ U)
    (hc : ∀ i, ContDiffOn ℝ (n : ℕ) (c i) U)
    (hmass : ∀ j : ℕ, j ≤ n → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i)
    (ψ : TensorEigenIdx (I := I) (M := M) g 0 0 → X → ℝ)
    {O B : Set X} (hO : IsOpen O)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) O)
    (hBuniq : UniqueDiffOn ℝ B) (hBO : B ⊆ O)
    (Csp : ℝ) (pSp : ℕ) (hCsp : 0 ≤ Csp)
    (hsp : ∀ m : ℕ, m ≤ n →
      ∀ i y, y ∈ B →
        ‖iteratedFDerivWithin ℝ m (ψ i) O y‖ ≤
          Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) :
    ∃ v : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
      Summable v ∧
      ∀ i q, q ∈ Set.Icc a b ×ˢ B →
        ‖iteratedFDerivWithin ℝ n
            (fun z : ℝ × X => c i z.1 * ψ i z.2)
            (Set.Icc a b ×ˢ B) q‖ ≤ v i := by
  classical
  set s : Set (ℝ × X) := Set.Icc a b ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hab).prod hBuniq
  obtain ⟨pTail, hpTail, htailSum⟩ := htail
  have htail0 : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-pTail)) :=
    htailSum
  obtain ⟨m0 : ℕ, hm0⟩ := exists_nat_gt (2 * (pSp : ℝ) + pTail)
  set qTail : ℝ := (m0 : ℝ) / 2 - (pSp : ℝ) with hqTail_def
  have hp_half_lt : pTail / 2 < qTail := by
    rw [hqTail_def]
    nlinarith
  have htail_q : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(2 * qTail))) := by
    refine Summable.of_nonneg_of_le
      (fun i => Real.rpow_nonneg
        (by linarith [tensor_lambda_nonneg (I := I) (M := M) i]) _) ?_ htail0
    intro i
    have hbase : (1 : ℝ) ≤
        1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      linarith [tensor_lambda_nonneg (I := I) (M := M) i]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have htime : ∀ j : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        j ≤ n → Summable Cm ∧
          ∀ i t, t ∈ Set.Icc a b →
            tensorSobolevWeight (I := I) (M := M) i (m0 : ℝ) *
              (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨Cm, hCm, hCm_bound⟩ := hmass j hj m0
      exact ⟨Cm, fun _ => ⟨hCm, hCm_bound⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hj⟩
  choose Cmf hCmf using htime
  have hCm_nn : ∀ j : ℕ, j ≤ n →
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 0, 0 ≤ Cmf j i := by
    intro j hj i
    have h := (hCmf j hj).2 i a (Set.left_mem_Icc.mpr hab.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i (m0 : ℝ)
    nlinarith [sq_nonneg (iteratedDeriv j (c i) a), hw.le]
  have htime_pt : ∀ j : ℕ, j ≤ n →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 0) t,
        t ∈ Set.Icc a b →
        |iteratedDeriv j (c i) t| ≤
          Real.sqrt (Cmf j i) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
              (-((m0 : ℝ) / 2)) := by
    intro j hj i t ht
    apply abs_le_sqrt_wt (I := I) (M := M) g i ((m0 : ℝ) / 2)
    simpa only [show (2 : ℝ) * ((m0 : ℝ) / 2) = (m0 : ℝ) by ring] using
      (hCmf j hj).2 i t ht
  have hsqrt_sum : ∀ j : ℕ, j ≤ n →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
        Real.sqrt (Cmf j i) *
          tensorSobolevWeight (I := I) (M := M) i (-qTail)) := by
    intro j hj
    have hsum := sqrt_mul_tail (I := I) (M := M) g (2 * qTail)
      (Cmf j) (hCmf j hj).1 (hCm_nn j hj) htail_q
    simpa only [show -(2 * qTail / 2) = -qTail by ring] using hsum
  set Dfst : ℝ := ‖ContinuousLinearMap.fst ℝ ℝ X‖ + 1 with hDfst_def
  set Dsnd : ℝ := ‖ContinuousLinearMap.snd ℝ ℝ X‖ + 1 with hDsnd_def
  set Kfun : ℕ → ℝ := fun j =>
    (n.choose j : ℝ) * (j.factorial : ℝ) * ((n - j).factorial : ℝ) *
      Dfst ^ j * Dsnd ^ (n - j) * Csp with hKfun_def
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-qTail) with hwfun_def
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ :=
    fun j i => Kfun j *
      ((∑ k ∈ Finset.range (j + 1), Real.sqrt (Cmf k i)) * wfun i)
    with htermf_def
  have hterm_sum : ∀ j : ℕ, j ≤ n → Summable (termf j) := by
    intro j hj
    refine Summable.mul_left (Kfun j) ?_
    have heq :
        (fun i : TensorEigenIdx (I := I) (M := M) g 0 0 =>
          (∑ k ∈ Finset.range (j + 1), Real.sqrt (Cmf k i)) * wfun i) =
        (fun i => ∑ k ∈ Finset.range (j + 1),
          Real.sqrt (Cmf k i) * wfun i) := by
      funext i
      rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun k hk => by
      rw [hwfun_def]
      exact hsqrt_sum k
        (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hj))
  refine ⟨fun i => ∑ j ∈ Finset.range (n + 1), termf j i, ?_, ?_⟩
  · exact summable_sum (fun j hj => hterm_sum j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc a b := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_pos : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      linarith [tensor_lambda_nonneg (I := I) (M := M) i]
    have htime_cd : ContDiffOn ℝ (n : ℕ)
        (fun z : ℝ × X => c i z.1) s :=
      (hc i).comp contDiffOn_fst (fun z hz => hIccU hz.1)
    have hspace_cd : ContDiffOn ℝ (n : ℕ)
        (fun z : ℝ × X => ψ i z.2) s := by
      refine ((hψ i).of_le (by exact_mod_cast le_top)).comp contDiffOn_snd ?_
      exact fun z hz => hBO hz.2
    have hleib := norm_iteratedFDerivWithin_mul_le
      htime_cd hspace_cd hUD hq (by exact_mod_cast le_rfl)
    refine hleib.trans ?_
    change _ ≤ ∑ j ∈ Finset.range (n + 1), termf j i
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    set Ssqrt : ℝ := ∑ k ∈ Finset.range (j + 1), Real.sqrt (Cmf k i)
      with hSsqrt_def
    set Ctime : ℝ := Ssqrt *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((m0 : ℝ) / 2))
      with hCtime_def
    have hCtime_nn : 0 ≤ Ctime := by
      rw [hCtime_def]
      exact mul_nonneg (Finset.sum_nonneg (fun k _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_pos.le _)
    have hfst := jet_fst_le (X := X) (c i) hU (hc i) hIccU hUD
      j (by exact_mod_cast hjn) q hq Ctime (fun k hk => by
        rw [Real.norm_eq_abs]
        refine (htime_pt k (le_trans hk hjn) i q.1 hqt).trans ?_
        rw [hCtime_def, hSsqrt_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_pos.le _)
        exact Finset.single_le_sum (fun l _ => Real.sqrt_nonneg (Cmf l i))
          (Finset.mem_range.mpr (by omega)))
    set Cspace : ℝ := Csp *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp
      with hCspace_def
    have hCspace_nn : 0 ≤ Cspace := by
      rw [hCspace_def]
      positivity
    have hsnd := jet_snd_le (X := X) (ψ i) hO (hψ i) hBO hUD
      (n - j) q hq Cspace (fun k hk => by
        rw [hCspace_def]
        exact hsp k (by omega) i q.2 hqB)
    have hprod :
        ‖iteratedFDerivWithin ℝ j (fun z : ℝ × X => c i z.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - j) (fun z : ℝ × X => ψ i z.2) s q‖ ≤
          ((j.factorial : ℝ) * Ctime * Dfst ^ j) *
            (((n - j).factorial : ℝ) * Cspace * Dsnd ^ (n - j)) := by
      exact mul_le_mul hfst hsnd (norm_nonneg _) (by positivity)
    have hchoose : 0 ≤ (n.choose j : ℝ) := by positivity
    have hcollapse :
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
            (-((m0 : ℝ) / 2)) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
        tensorSobolevWeight (I := I) (M := M) i (-qTail) := by
      unfold tensorSobolevWeight
      rw [← Real.rpow_natCast
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
        ← Real.rpow_add hbase_pos]
      congr 1
      rw [hqTail_def]
      ring
    calc
      (n.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j (fun z : ℝ × X => c i z.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - j) (fun z : ℝ × X => ψ i z.2) s q‖
          = (n.choose j : ℝ) *
              (‖iteratedFDerivWithin ℝ j (fun z : ℝ × X => c i z.1) s q‖ *
              ‖iteratedFDerivWithin ℝ (n - j)
                (fun z : ℝ × X => ψ i z.2) s q‖) := by ring
      _ ≤ (n.choose j : ℝ) *
            (((j.factorial : ℝ) * Ctime * Dfst ^ j) *
              (((n - j).factorial : ℝ) * Cspace * Dsnd ^ (n - j))) :=
        mul_le_mul_of_nonneg_left hprod hchoose
      _ = termf j i := by
        simp only [htermf_def, hKfun_def, hCtime_def, hCspace_def,
          hSsqrt_def, hwfun_def]
        calc
          (n.choose j : ℝ) *
                (((j.factorial : ℝ) *
                    ((∑ k ∈ Finset.range (j + 1), Real.sqrt (Cmf k i)) *
                      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                        (-((m0 : ℝ) / 2))) * Dfst ^ j) *
                  (((n - j).factorial : ℝ) *
                    (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                    Dsnd ^ (n - j))) =
              ((n.choose j : ℝ) * (j.factorial : ℝ) *
                  ((n - j).factorial : ℝ) * Dfst ^ j * Dsnd ^ (n - j) * Csp) *
                ((∑ k ∈ Finset.range (j + 1), Real.sqrt (Cmf k i)) *
                  ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                      (-((m0 : ℝ) / 2)) *
                    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by
            ring
          _ = ((n.choose j : ℝ) * (j.factorial : ℝ) *
                  ((n - j).factorial : ℝ) * Dfst ^ j * Dsnd ^ (n - j) * Csp) *
                ((∑ k ∈ Finset.range (j + 1), Real.sqrt (Cmf k i)) *
                  tensorSobolevWeight (I := I) (M := M) i (-qTail)) := by
            rw [hcollapse]



lemma scalar_jet_uniform
    (g : SmoothRiemannianMetric I M) (α : M) (n : ℕ)
    {K : Set EuclN} (hK : IsCompact K)
    (hKO : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ m : ℕ, m ≤ n →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 0) y,
          y ∈ K →
            ‖iteratedFDerivWithin ℝ m
                (tensorComponentEuclideanChart (I := I) (M := M) g 0 0
                  (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
                  α Fin.elim0 Fin.elim0)
                (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
              C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  set kE : ℕ := Module.finrank ℝ E + 2 * n + 1 with hkE_def
  have hper : ∀ m : ℕ, ∃ Cm : ℝ, m ≤ n →
      0 ≤ Cm ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 0) y,
        y ∈ K →
          ‖iteratedFDerivWithin ℝ m
              (tensorComponentEuclideanChart (I := I) (M := M) g 0 0
                (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
                α Fin.elim0 Fin.elim0)
              (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
            Cm * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
    intro m
    by_cases hm : m ≤ n
    · have hsuper : 2 * kE > Module.finrank ℝ E + 2 * m := by
        rw [hkE_def]
        omega
      obtain ⟨Cm, hCm, hbound⟩ :=
        scalarEig_jet_le (I := I) (M := M) g α m kE hsuper hK hKO
      exact ⟨Cm, fun _ => ⟨hCm, hbound⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose Cmf hCmf using hper
  set C : ℝ := ∑ m ∈ Finset.range (n + 1), Cmf m with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact Finset.sum_nonneg (fun m hm =>
      (hCmf m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))).1)
  refine ⟨C, 2 * kE, hC_nn, ?_⟩
  intro m hm i y hy
  have hCm_le : Cmf m ≤ C := by
    rw [hC_def]
    exact Finset.single_le_sum
      (fun j hj => (hCmf j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
      (Finset.mem_range.mpr (by omega))
  have hbase_nn : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    linarith [tensor_lambda_nonneg (I := I) (M := M) i]
  exact ((hCmf m hm).2 i y hy).trans
    (mul_le_mul_of_nonneg_right hCm_le (pow_nonneg hbase_nn _))



theorem scalarMode_majorant
    (g : SmoothRiemannianMetric I M)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 0)
    {a b : ℝ} (hab : a < b) (n : ℕ)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hIccU : Set.Icc a b ⊆ U)
    (hc : ∀ i, ContDiffOn ℝ (n : ℕ) (c i) U)
    (hmass : ∀ j : ℕ, j ≤ n → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i)
    (α : M) {K : Set EuclN} (hK : IsCompact K)
    (hKuniq : UniqueDiffOn ℝ K)
    (hKO : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ v : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
      Summable v ∧
      ∀ i q, q ∈ Set.Icc a b ×ˢ K →
        ‖iteratedFDerivWithin ℝ n
            (scalarMode (I := I) (M := M) g c α i)
            (Set.Icc a b ×ˢ K) q‖ ≤ v i := by
  obtain ⟨Csp, pSp, hCsp, hsp⟩ :=
    scalar_jet_uniform (I := I) (M := M) g α n hK hKO
  let ψ : TensorEigenIdx (I := I) (M := M) g 0 0 → EuclN → ℝ :=
    fun i => tensorComponentEuclideanChart (I := I) (M := M) g 0 0
      (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
      α Fin.elim0 Fin.elim0
  have hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i)
      (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    rawPullR_contDiffOn (I := I) (M := M) g 0 0
      (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
      α Fin.elim0 Fin.elim0
  simpa only [scalarMode, ψ] using
    (prodMode_majorant (I := I) (M := M) (X := EuclN) g htail hab n c
      hU hIccU hc hmass ψ
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hψ hKuniq hKO Csp pSp hCsp hsp)




theorem scalarTsum_chart
    (g : SmoothRiemannianMetric I M)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 0)
    {a b : ℝ} (hab : a < b) (N : ℕ)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hIccU : Set.Icc a b ⊆ U)
    (hc : ∀ i, ContDiffOn ℝ (N : ℕ) (c i) U)
    (hmass : ∀ j : ℕ, j ≤ N → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i)
    (α : M) {K : Set EuclN} (hK : IsCompact K)
    (hKuniq : UniqueDiffOn ℝ K) (hKconv : Convex ℝ K)
    (hKne : K.Nonempty)
    (hKO : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffOn ℝ (N : ℕ)
      (fun q : ℝ × EuclN =>
        ∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
          scalarMode (I := I) (M := M) g c α i q)
      (Set.Icc a b ×ˢ K) := by
  classical
  set s : Set (ℝ × EuclN) := Set.Icc a b ×ˢ K with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hab).prod hKuniq
  have hconv : Convex ℝ s := (convex_Icc a b).prod hKconv
  have hmode : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 0,
      ContDiffOn ℝ (N : ℕ)
        (scalarMode (I := I) (M := M) g c α i) s := by
    intro i
    exact (scalarMode_smooth (I := I) (M := M) g c α i
      (by exact_mod_cast le_top) (hc i)).mono (fun q hq =>
        ⟨hIccU hq.1, hKO hq.2⟩)
  have hmajor : ∀ k : ℕ,
      ∃ v : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        k ≤ N → Summable v ∧
          ∀ i q, q ∈ s →
            ‖iteratedFDerivWithin ℝ k
                (scalarMode (I := I) (M := M) g c α i) s q‖ ≤ v i := by
    intro k
    by_cases hk : k ≤ N
    · obtain ⟨v, hv, hv_bound⟩ := scalarMode_majorant
        (I := I) (M := M) g htail hab k c hU hIccU
        (fun i => (hc i).of_le (by exact_mod_cast hk))
        (fun j hj m => hmass j (le_trans hj hk) m)
        α hK hKuniq hKO
      exact ⟨v, fun _ => ⟨hv, hv_bound⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hk⟩
  choose v hv using hmajor
  obtain ⟨y₀, hy₀⟩ := hKne
  exact DifferentialGeometry.Analysis.contDiffOn_tsum
    hUD hconv hmode
    (fun k hk => (hv k (by exact_mod_cast hk)).1)
    (fun k i q hq hk => (hv k (by exact_mod_cast hk)).2 i q hq)
    (x₀ := (a, y₀)) ⟨Set.left_mem_Icc.mpr hab.le, hy₀⟩



theorem scalarTsum_smooth
    (g : SmoothRiemannianMetric I M)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 0)
    {a b : ℝ} (hab : a < b) (N : ℕ)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hIccU : Set.Icc a b ⊆ U)
    (hc : ∀ i, ContDiffOn ℝ (N : ℕ) (c i) U)
    (hmass : ∀ j : ℕ, j ≤ N → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i)
    (α : M) :
    ContDiffOn ℝ (N : ℕ)
      (fun q : ℝ × EuclN =>
        ∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
          scalarMode (I := I) (M := M) g c α i q)
      (Set.Icc a b ×ˢ chartTargetEuclid (I := I) (M := M) α) := by
  let Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  have hΩ : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨t₀, y₀⟩ hmem
  obtain ⟨_ht₀, hy₀⟩ := hmem
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ y₀ hy₀
  refine ⟨Set.univ ×ˢ Metric.ball y₀ (r / 2),
    isOpen_univ.prod Metric.isOpen_ball,
    ⟨Set.mem_univ t₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  set B : Set EuclN := Metric.ball y₀ (r / 2) with hB_def
  set Bc : Set EuclN := Metric.closedBall y₀ (r / 2) with hBc_def
  have hBBc : B ⊆ Bc := by
    simpa only [hB_def, hBc_def] using
      (Metric.ball_subset_closedBall :
        Metric.ball y₀ (r / 2) ⊆ Metric.closedBall y₀ (r / 2))
  have hBcΩ : Bc ⊆ Ω := by
    intro y hy
    exact hball (by
      rw [Metric.mem_ball]
      have hy' := hy
      rw [hBc_def, Metric.mem_closedBall] at hy'
      linarith)
  have hBΩ : B ⊆ Ω := hBBc.trans hBcΩ
  have hinter :
      (Set.Icc a b ×ˢ Ω) ∩ (Set.univ ×ˢ B) = Set.Icc a b ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_univ,
      Set.inter_eq_right.mpr hBΩ]
  rw [hinter]
  have hBc_compact : IsCompact Bc := isCompact_closedBall y₀ (r / 2)
  have hBc_int : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall y₀ (by positivity : r / 2 ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hBc_conv : Convex ℝ Bc := convex_closedBall y₀ (r / 2)
  have hBc_uniq : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex hBc_conv hBc_int
  have hBc_ne : Bc.Nonempty :=
    ⟨y₀, Metric.mem_closedBall_self (by positivity)⟩
  exact (scalarTsum_chart (I := I) (M := M) g htail hab N c
    hU hIccU hc hmass α hBc_compact hBc_uniq hBc_conv hBc_ne hBcΩ).mono
      (Set.prod_mono (le_refl _) hBBc)



theorem scalarSpec_local
    (g : SmoothRiemannianMetric I M)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 0)
    {a b : ℝ} (hab : a < b) (N : ℕ)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hIccU : Set.Icc a b ⊆ U)
    (hc : ∀ i, ContDiffOn ℝ (N : ℕ) (c i) U)
    (hmass : ∀ j : ℕ, j ≤ N → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i)
    (α : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (N : ℕ)
      (fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g c q.1 q.2)
      (Set.Icc a b ×ˢ (chartAt H α).source) := by
  set G : ℝ × EuclN → ℝ :=
    fun q => ∑' i : TensorEigenIdx (I := I) (M := M) g 0 0,
      scalarMode (I := I) (M := M) g c α i q with hG_def
  have hGEuclid : ContDiffOn ℝ (N : ℕ) G
      (Set.Icc a b ×ˢ chartTargetEuclid (I := I) (M := M) α) :=
    scalarTsum_smooth (I := I) (M := M) g htail hab N c
      hU hIccU hc hmass α
  set f : ℝ × M → ℝ × EuclN := fun q =>
    (q.1, toEuclidean (E := E) (extChartAt I α q.2)) with hf_def
  have hchart : ContMDiffOn I 𝓘(ℝ, EuclN) ∞
      (fun x : M => toEuclidean (E := E) (extChartAt I α x))
      (chartAt H α).source := by
    exact (toEuclidean (E := E)).toContinuousLinearMap.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt (I := I) (x := α))
  have hf_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × EuclN) (N : ℕ) f
      (Set.Icc a b ×ˢ (chartAt H α).source) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    exact (hchart.comp contMDiffOn_snd (fun q hq => hq.2)).of_le
      (by exact_mod_cast le_top)
  have hmaps : Set.MapsTo f
      (Set.Icc a b ×ˢ (chartAt H α).source)
      (Set.Icc a b ×ˢ chartTargetEuclid (I := I) (M := M) α) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    exact toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) α hx
  have heq : Set.EqOn
      (fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g c q.1 q.2)
      (G ∘ f)
      (Set.Icc a b ×ˢ (chartAt H α).source) := by
    rintro ⟨t, x⟩ ⟨_, hx⟩
    simp only [Function.comp_apply, hG_def, hf_def]
    rw [scalarSpec_chart (I := I) (M := M) g c α
      (toEuclidean_extChartAt_mem_chartTargetEuclid
        (I := I) (M := M) α hx),
      symm_toEuclidean_symm_toEuclidean_extChartAt
        (I := I) (M := M) α hx]
  intro q hq
  refine ContMDiffWithinAt.congr ?_ (fun y hy => heq hy) (heq hq)
  have hGf : ContDiffWithinAt ℝ (N : ℕ) G
      (Set.Icc a b ×ˢ chartTargetEuclid (I := I) (M := M) α) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps




theorem scalarSpec_d1
    (g : SmoothRiemannianMetric I M)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 0)
    {a b : ℝ} (hab : a < b)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hIccU : Set.Icc a b ⊆ U)
    (hc : ∀ i, ContDiffOn ℝ (1 : ℕ) (c i) U)
    (hmass : ∀ j : ℕ, j ≤ 1 → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i)
    (x : M) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt
      (fun s => scalarSpecSum (I := I) (M := M) g c s x)
      (scalarSpecSum (I := I) (M := M) g
        (fun i s => deriv (c i) s) t x)
      (Set.Icc a b) t := by
  classical
  let y₀ : EuclN := toEuclidean (E := E) (extChartAt I x x)
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hyΩ : y₀ ∈ chartTargetEuclid (I := I) (M := M) x := by
    simpa only [y₀] using
      toEuclidean_extChartAt_mem_chartTargetEuclid
        (I := I) (M := M) x hxsrc
  let Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) x
  have hΩ : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ y₀ hyΩ
  let K : Set EuclN := Metric.closedBall y₀ (r / 2)
  have hK : IsCompact K := isCompact_closedBall y₀ (r / 2)
  have hKint : (interior K).Nonempty := by
    change (interior (Metric.closedBall y₀ (r / 2))).Nonempty
    rw [interior_closedBall y₀ (by positivity : r / 2 ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hKconv : Convex ℝ K := convex_closedBall y₀ (r / 2)
  have hKuniq : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex hKconv hKint
  have hKO : K ⊆ chartTargetEuclid (I := I) (M := M) x := by
    intro y hy
    exact hball (by
      rw [Metric.mem_ball]
      have hy' := hy
      change y ∈ Metric.closedBall y₀ (r / 2) at hy'
      rw [Metric.mem_closedBall] at hy'
      linarith)
  have hyK : y₀ ∈ K := by
    exact Metric.mem_closedBall_self (by positivity)
  let dc : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ :=
    fun i s => deriv (c i) s
  have hdc : ∀ i, ContDiffOn ℝ (0 : ℕ) (dc i) U := by
    intro i
    simpa only [dc] using
      (hc i).deriv_of_isOpen hU (by norm_num)
  have hdmass : ∀ j : ℕ, j ≤ 0 → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i z, z ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (dc i) z) ^ 2 ≤ Cm i := by
    intro j hj m
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    obtain ⟨Cm, hCm, hCm_le⟩ := hmass 1 (by omega) m
    refine ⟨Cm, hCm, ?_⟩
    intro i z hz
    simpa only [dc, iteratedDeriv_zero, iteratedDeriv_one] using
      hCm_le i z hz
  obtain ⟨v0, hv0, hv0_le⟩ := scalarMode_majorant
    (I := I) (M := M) g htail hab 0 c hU hIccU
      (fun i => (hc i).of_le (by norm_num))
      (fun j hj m => hmass j (by omega) m)
      x hK hKuniq hKO
  obtain ⟨vd, hvd, hvd_le⟩ := scalarMode_majorant
    (I := I) (M := M) g htail hab 0 dc hU hIccU hdc hdmass
      x hK hKuniq hKO
  have hf0 : Summable
      (fun i => scalarMode (I := I) (M := M) g c x i (a, y₀)) := by
    refine Summable.of_norm_bounded hv0 (fun i => ?_)
    simpa only [norm_iteratedFDerivWithin_zero] using
      hv0_le i (a, y₀) ⟨Set.left_mem_Icc.mpr hab.le, hyK⟩
  have hterm : ∀ i z, z ∈ Set.Icc a b →
      HasDerivWithinAt
        (fun s => scalarMode (I := I) (M := M) g c x i (s, y₀))
        (scalarMode (I := I) (M := M) g dc x i (z, y₀))
        (Set.Icc a b) z := by
    intro i z hz
    have hd : HasDerivAt (c i) (deriv (c i) z) z :=
      (((hc i).differentiableOn (by norm_num) z (hIccU hz)).differentiableAt
        (hU.mem_nhds (hIccU hz))).hasDerivAt
    simpa only [scalarMode, dc] using
      (hd.mul_const
        (tensorComponentEuclideanChart (I := I) (M := M) g 0 0
          (eigenvectorSmooth (I := I) (M := M) g 0 0 i)
          x Fin.elim0 Fin.elim0 y₀)).hasDerivWithinAt
  have hdbd : ∀ i z, z ∈ Set.Icc a b →
      ‖ContinuousLinearMap.toSpanSingleton ℝ
        (scalarMode (I := I) (M := M) g dc x i (z, y₀))‖ ≤ vd i := by
    intro i z hz
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    simpa only [norm_iteratedFDerivWithin_zero] using
      hvd_le i (z, y₀) ⟨hz, hyK⟩
  have hF := DifferentialGeometry.Analysis.hasFDerivWithinAt_tsum
    (f := fun i z => scalarMode (I := I) (M := M) g c x i (z, y₀))
    (f' := fun i z => ContinuousLinearMap.toSpanSingleton ℝ
      (scalarMode (I := I) (M := M) g dc x i (z, y₀)))
    (u := vd) (s := Set.Icc a b)
    (fun i z hz => (hterm i z hz).hasFDerivWithinAt)
    hdbd hvd (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab.le) hf0 ht
  have hsumF : Summable fun i => ContinuousLinearMap.toSpanSingleton ℝ
      (scalarMode (I := I) (M := M) g dc x i (t, y₀)) := by
    refine Summable.of_norm_bounded hvd (fun i => hdbd i t ht)
  have heval :
      (∑' i, ContinuousLinearMap.toSpanSingleton ℝ
        (scalarMode (I := I) (M := M) g dc x i (t, y₀))) (1 : ℝ) =
      ∑' i, scalarMode (I := I) (M := M) g dc x i (t, y₀) := by
    rw [show
      (∑' i, ContinuousLinearMap.toSpanSingleton ℝ
        (scalarMode (I := I) (M := M) g dc x i (t, y₀))) (1 : ℝ) =
          (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
            (∑' i, ContinuousLinearMap.toSpanSingleton ℝ
              (scalarMode (I := I) (M := M) g dc x i (t, y₀))) from rfl,
      ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) hsumF]
    refine tsum_congr (fun i => ?_)
    simp [ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
  have hD : HasDerivWithinAt
      (fun z => ∑' i, scalarMode (I := I) (M := M) g c x i (z, y₀))
      (∑' i, scalarMode (I := I) (M := M) g dc x i (t, y₀))
      (Set.Icc a b) t := by
    have h := hF.hasDerivWithinAt
    rwa [heval] at h
  have hchart (z : ℝ) :
      (∑' i, scalarMode (I := I) (M := M) g c x i (z, y₀)) =
        scalarSpecSum (I := I) (M := M) g c z x := by
    rw [scalarSpec_chart (I := I) (M := M) g c x hyΩ,
      symm_toEuclidean_symm_toEuclidean_extChartAt
        (I := I) (M := M) x hxsrc]
  have hdchart :
      (∑' i, scalarMode (I := I) (M := M) g dc x i (t, y₀)) =
        scalarSpecSum (I := I) (M := M) g dc t x := by
    rw [scalarSpec_chart (I := I) (M := M) g dc x hyΩ,
      symm_toEuclidean_symm_toEuclidean_extChartAt
        (I := I) (M := M) x hxsrc]
  simpa only [dc] using
    (hD.congr (fun z _hz => (hchart z).symm) (hchart t).symm).congr_deriv hdchart




theorem scalar_path_recon
    (g : SmoothRiemannianMetric I M)
    (htail : EigenvalueTailSummable (I := I) (M := M) g 0 0)
    {a b : ℝ} (hab : a < b) (N : ℕ)
    (c : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hIccU : Set.Icc a b ⊆ U)
    (hc : ∀ i, ContDiffOn ℝ (N : ℕ) (c i) U)
    (hmass : ∀ j : ℕ, j ≤ N → ∀ m : ℕ,
      ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 0 → ℝ,
        Summable Cm ∧
        ∀ i t, t ∈ Set.Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
            (iteratedDeriv j (c i) t) ^ 2 ≤ Cm i) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) (N : ℕ)
      (fun q : ℝ × M => scalarSpecSum (I := I) (M := M) g c q.1 q.2)
      (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨t, x⟩ ⟨_, _⟩
  refine ⟨Set.univ ×ˢ (chartAt H x).source,
    isOpen_univ.prod (chartAt H x).open_source,
    ⟨Set.mem_univ t, mem_chart_source H x⟩, ?_⟩
  simpa only [Set.prod_inter_prod, Set.inter_univ, Set.univ_inter] using
    scalarSpec_local (I := I) (M := M) g htail hab N c
      hU hIccU hc hmass x

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
