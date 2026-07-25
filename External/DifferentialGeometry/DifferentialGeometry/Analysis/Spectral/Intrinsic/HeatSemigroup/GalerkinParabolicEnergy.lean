import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.ODE.EnergyHierarchy

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s₀ : ℕ}

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lambda_mul_tensorSobolevWeight
    (i : TensorEigenIdx (I := I) (M := M) g r s₀) (σ : ℝ) :
    TensorEigenIdx.lambda (I := I) (M := M) i *
        tensorSobolevWeight (I := I) (M := M) i σ =
      tensorSobolevWeight (I := I) (M := M) i (σ + 1) -
        tensorSobolevWeight (I := I) (M := M) i σ := by
  have hpos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  unfold tensorSobolevWeight
  rw [Real.rpow_add_one hpos.ne' σ]
  ring

noncomputable def galerkinEnergy
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ * (u t i) ^ 2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma galerkinEnergy_nonneg
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) (t : ℝ) :
    0 ≤ galerkinEnergy (I := I) (M := M) s u σ t := by
  unfold galerkinEnergy
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  positivity

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma galerkinEnergy_continuousOn
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) {J : Set ℝ}
    (hu : ∀ i ∈ s, ContinuousOn (fun t => u t i) J) :
    ContinuousOn (galerkinEnergy (I := I) (M := M) s u σ) J := by
  unfold galerkinEnergy
  refine continuousOn_finset_sum s (fun i hi => ?_)
  exact continuousOn_const.mul ((hu i hi).pow 2)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma galerkinEnergy_hasDerivWithinAt
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ)
    (du : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) {t : ℝ}
    (hu : ∀ i ∈ s,
      HasDerivWithinAt (fun s => u s i) (du t i) (Set.Ici t) t) :
    HasDerivWithinAt (galerkinEnergy (I := I) (M := M) s u σ)
      (∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ *
        (2 * u t i * du t i)) (Set.Ici t) t := by
  unfold galerkinEnergy
  apply HasDerivWithinAt.fun_sum
  intro i hi
  have hsq : HasDerivWithinAt (fun s => (u s i) ^ 2)
      (2 * u t i ^ 1 * du t i) (Set.Ici t) t :=
    (hu i hi).fun_pow 2
  have := hsq.const_mul (tensorSobolevWeight (I := I) (M := M) i σ)
  simpa [pow_one] using this

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem galerkinEnergy_deriv_identity
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ)
    (F : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) (t : ℝ) :
    (∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ *
        (2 * u t i *
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i))) =
      -2 * galerkinEnergy (I := I) (M := M) s u (σ + 1) t +
        2 * galerkinEnergy (I := I) (M := M) s u σ t +
        2 * ∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ * (u t i * F t i) := by
  have hterm : ∀ i ∈ s,
      tensorSobolevWeight (I := I) (M := M) i σ *
          (2 * u t i * (-(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i)) =
        -2 * (tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u t i) ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * (u t i) ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * (u t i * F t i)) := by
    intro i _
    have halg := lambda_mul_tensorSobolevWeight (I := I) (M := M) i σ
    have hwσ1 : tensorSobolevWeight (I := I) (M := M) i (σ + 1) =
        TensorEigenIdx.lambda (I := I) (M := M) i *
          tensorSobolevWeight (I := I) (M := M) i σ +
          tensorSobolevWeight (I := I) (M := M) i σ := by linarith [halg]
    rw [hwσ1]; ring
  rw [Finset.sum_congr rfl hterm]
  unfold galerkinEnergy
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem galerkinEnergy_hasDerivWithinAt_ode
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ)
    (F : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) {t : ℝ}
    (hu : ∀ i ∈ s,
      HasDerivWithinAt (fun s => u s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i)
        (Set.Ici t) t) :
    HasDerivWithinAt (galerkinEnergy (I := I) (M := M) s u σ)
      (-2 * galerkinEnergy (I := I) (M := M) s u (σ + 1) t +
        2 * galerkinEnergy (I := I) (M := M) s u σ t +
        2 * ∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ *
          (u t i * F t i)) (Set.Ici t) t := by
  have hderiv := galerkinEnergy_hasDerivWithinAt (I := I) (M := M)
    s u (fun t i => -(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i) σ hu
  have hid := galerkinEnergy_deriv_identity (I := I) (M := M) s u F σ t
  rwa [hid] at hderiv

theorem energy_hierarchy_explicit_bound
    {T c C : ℝ} {Mk Mk' : ℕ → ℝ → ℝ} {seed B0 : ℕ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t)
    (hcont : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t)
    (hdiss : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ -c * (Mk (k + 1) t) + C * (Mk k t) + seed k * Real.sqrt (Mk k t))
    (hinit : ∀ k, Mk k 0 ≤ B0 k) :
    ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mk k t ≤ gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) T := by
  intro k
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ r, Mk' k t < r →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (Mk k z - Mk k t) < r := by
    intro t ht r hr
    have := (hderiv k t ht).liminf_right_slope_le hr
    refine this.mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ (C + 1) * Mk k t + (seed k) ^ 2 / 4 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    have hMt : 0 ≤ Mk k t := hMnonneg k t htIcc
    have hMt1 : 0 ≤ Mk (k + 1) t := hMnonneg (k + 1) t htIcc
    have hneg : -c * (Mk (k + 1) t) ≤ 0 := by
      have : 0 ≤ c * (Mk (k + 1) t) := mul_nonneg hc.le hMt1
      linarith
    have hdiss' := hdiss k t ht
    have hyoung : seed k * Real.sqrt (Mk k t) ≤ (seed k) ^ 2 / 4 + Mk k t :=
      mul_sqrt_le_sq_div_four_add (seed k) hMt
    nlinarith [hneg, hdiss', hyoung]
  intro t htIcc
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T)
    (hcont k) hf' (by simpa using hinit k) hbound
  have hKnn : (0 : ℝ) ≤ C + 1 := by linarith
  have hεnn : (0 : ℝ) ≤ (seed k) ^ 2 / 4 := by positivity
  have hB0nn : 0 ≤ B0 k :=
    le_trans (hMnonneg k 0 ⟨le_refl 0, htIcc.1.trans htIcc.2⟩) (hinit k)
  have hmono : gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) (t - 0) ≤
      gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) T := by
    have hle : (t - 0) ≤ T := by simpa using htIcc.2
    exact gronwallBound_mono (δ := B0 k) (K := C + 1) (ε := (seed k) ^ 2 / 4)
      hB0nn hεnn hKnn hle
  calc Mk k t ≤ gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) (t - 0) := hgron t htIcc
    _ ≤ gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) T := hmono

theorem energy_hierarchy_explicit_bound_perScale
    {T c : ℝ} {C : ℕ → ℝ} {Mk Mk' : ℕ → ℝ → ℝ} {seed B0 : ℕ → ℝ}
    (hc : 0 < c) (hC : ∀ k, 0 ≤ C k)
    (hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t)
    (hcont : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t)
    (hdiss : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ -c * (Mk (k + 1) t) + C k * (Mk k t) + seed k * Real.sqrt (Mk k t))
    (hinit : ∀ k, Mk k 0 ≤ B0 k) :
    ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mk k t ≤ gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := by
  intro k
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ r, Mk' k t < r →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (Mk k z - Mk k t) < r := by
    intro t ht r hr
    have := (hderiv k t ht).liminf_right_slope_le hr
    refine this.mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ (C k + 1) * Mk k t + (seed k) ^ 2 / 4 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    have hMt : 0 ≤ Mk k t := hMnonneg k t htIcc
    have hMt1 : 0 ≤ Mk (k + 1) t := hMnonneg (k + 1) t htIcc
    have hneg : -c * (Mk (k + 1) t) ≤ 0 := by
      have : 0 ≤ c * (Mk (k + 1) t) := mul_nonneg hc.le hMt1
      linarith
    have hdiss' := hdiss k t ht
    have hyoung : seed k * Real.sqrt (Mk k t) ≤ (seed k) ^ 2 / 4 + Mk k t :=
      mul_sqrt_le_sq_div_four_add (seed k) hMt
    nlinarith [hneg, hdiss', hyoung]
  intro t htIcc
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T)
    (hcont k) hf' (by simpa using hinit k) hbound
  have hKnn : (0 : ℝ) ≤ C k + 1 := by linarith [hC k]
  have hεnn : (0 : ℝ) ≤ (seed k) ^ 2 / 4 := by positivity
  have hB0nn : 0 ≤ B0 k :=
    le_trans (hMnonneg k 0 ⟨le_refl 0, htIcc.1.trans htIcc.2⟩) (hinit k)
  have hmono : gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) (t - 0) ≤
      gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := by
    have hle : (t - 0) ≤ T := by simpa using htIcc.2
    exact gronwallBound_mono (δ := B0 k) (K := C k + 1) (ε := (seed k) ^ 2 / 4)
      hB0nn hεnn hKnn hle
  calc Mk k t ≤ gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) (t - 0) := hgron t htIcc
    _ ≤ gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := hmono

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem galerkin_energy_uniform_bound_perScale
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ₀ Cδ : ℝ} {Cmid seed B0 : ℕ → ℝ}
    (hCδ : Cδ < 2) (hCmid : ∀ k, 0 ≤ Cmid k)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          Cmid k * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          seed k *
            Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t))
    (hinit : ∀ (N : ℕ) (k : ℕ),
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) 0 ≤ B0 k) :
    ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t ≤ Bound := by
  set Mfam : ℕ → ℕ → ℝ → ℝ :=
    fun N k t => galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    with hMfam
  have hkey : ∀ N, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mfam N k t ≤ gronwallBound (B0 k) ((Cmid k + 2) + 1) ((seed k) ^ 2 / 4) T := by
    intro N
    set Mk : ℕ → ℝ → ℝ := fun k t => Mfam N k t with hMk
    set Mk' : ℕ → ℝ → ℝ :=
      fun k t =>
        -2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          2 * ∑ i ∈ sseq N,
            tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
              (U N t i * Fseq N t i)
      with hMk'
    have hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t := by
      intro k t _
      exact galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    have hcontk : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T) := by
      intro k
      exact galerkinEnergy_continuousOn (I := I) (M := M) (sseq N) (U N)
        (σ₀ + (k : ℝ)) (fun i hi => hcont N i hi)
    have hderivk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t := by
      intro k t ht
      exact galerkinEnergy_hasDerivWithinAt_ode (I := I) (M := M) (sseq N) (U N)
        (Fseq N) (σ₀ + (k : ℝ)) (fun i hi => hderiv N t ht i hi)
    have hdissk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        Mk' k t ≤ -(2 - Cδ) * (Mk (k + 1) t) + (Cmid k + 2) * (Mk k t) +
          seed k * Real.sqrt (Mk k t) := by
      intro k t ht
      have hcl := hclosure N k t ht
      have hMk1 : Mk (k + 1) t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t := by
        have hσ : σ₀ + ((k + 1 : ℕ) : ℝ) = σ₀ + (k : ℝ) + 1 := by push_cast; ring
        simp only [hMk, hMfam, hσ]
      have hMkk : Mk k t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t := by
        simp only [hMk, hMfam]
      rw [hMk', hMk1, hMkk]
      linarith [hcl]
    have hinitk : ∀ k, Mk k 0 ≤ B0 k := by
      intro k
      exact hinit N k
    have hc : (0 : ℝ) < 2 - Cδ := by linarith
    have hC : ∀ k, (0 : ℝ) ≤ Cmid k + 2 := by intro k; linarith [hCmid k]
    intro k t ht
    exact energy_hierarchy_explicit_bound_perScale (c := 2 - Cδ) (C := fun k => Cmid k + 2)
      (Mk := Mk) (Mk' := Mk') (seed := seed) (B0 := B0)
      hc hC hMnonneg hcontk hderivk hdissk hinitk k t ht
  refine fun k => ⟨gronwallBound (B0 k) ((Cmid k + 2) + 1) ((seed k) ^ 2 / 4) T,
    fun N t ht => ?_⟩
  exact hkey N k t ht

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem galerkin_energy_uniform_bound
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ₀ Cδ Cmid : ℝ} {seed B0 : ℕ → ℝ}
    (hCδ : Cδ < 2) (hCmid : 0 ≤ Cmid)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          Cmid * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          seed k *
            Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t))
    (hinit : ∀ (N : ℕ) (k : ℕ),
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) 0 ≤ B0 k) :
    ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t ≤ Bound := by
  set Mfam : ℕ → ℕ → ℝ → ℝ :=
    fun N k t => galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    with hMfam
  have hkey : ∀ N, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mfam N k t ≤ gronwallBound (B0 k) (Cmid + 2 + 1) ((seed k) ^ 2 / 4) T := by
    intro N
    set Mk : ℕ → ℝ → ℝ := fun k t => Mfam N k t with hMk
    set Mk' : ℕ → ℝ → ℝ :=
      fun k t =>
        -2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          2 * ∑ i ∈ sseq N,
            tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
              (U N t i * Fseq N t i)
      with hMk'
    have hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t := by
      intro k t _
      exact galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    have hcontk : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T) := by
      intro k
      exact galerkinEnergy_continuousOn (I := I) (M := M) (sseq N) (U N)
        (σ₀ + (k : ℝ)) (fun i hi => hcont N i hi)
    have hderivk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t := by
      intro k t ht
      exact galerkinEnergy_hasDerivWithinAt_ode (I := I) (M := M) (sseq N) (U N)
        (Fseq N) (σ₀ + (k : ℝ)) (fun i hi => hderiv N t ht i hi)
    have hdissk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        Mk' k t ≤ -(2 - Cδ) * (Mk (k + 1) t) + (Cmid + 2) * (Mk k t) +
          seed k * Real.sqrt (Mk k t) := by
      intro k t ht
      have hcl := hclosure N k t ht
      have hMk1 : Mk (k + 1) t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t := by
        have hσ : σ₀ + ((k + 1 : ℕ) : ℝ) = σ₀ + (k : ℝ) + 1 := by push_cast; ring
        simp only [hMk, hMfam, hσ]
      have hMkk : Mk k t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t := by
        simp only [hMk, hMfam]
      rw [hMk', hMk1, hMkk]
      linarith [hcl]
    have hinitk : ∀ k, Mk k 0 ≤ B0 k := by
      intro k
      exact hinit N k
    have hc : (0 : ℝ) < 2 - Cδ := by linarith
    have hC : (0 : ℝ) ≤ Cmid + 2 := by linarith
    intro k t ht
    exact energy_hierarchy_explicit_bound (c := 2 - Cδ) (C := Cmid + 2)
      (Mk := Mk) (Mk' := Mk') (seed := seed) (B0 := B0)
      hc hC hMnonneg hcontk hderivk hdissk hinitk k t ht
  refine fun k => ⟨gronwallBound (B0 k) (Cmid + 2 + 1) ((seed k) ^ 2 / 4) T,
    fun N t ht => ?_⟩
  exact hkey N k t ht

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
