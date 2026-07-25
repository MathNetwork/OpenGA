import DifferentialGeometry.Analysis.Sobolev.Hs.SpectralDefs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
lemma scalarSobolevWeight_mono {g : SmoothRiemannianMetric I M}
    (i : EigenIdx (I := I) (M := M) g) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    scalarSobolevWeight (I := I) (M := M) i τ ≤
      scalarSobolevWeight (I := I) (M := M) i σ := by
  unfold scalarSobolevWeight
  exact Real.rpow_le_rpow_of_exponent_le
    (one_le_one_add_lambda (I := I) (M := M) i) hτσ

namespace scalarHs

variable {g : SmoothRiemannianMetric I M}

omit [NeZero (Module.finrank ℝ E)] in
lemma weighted_summable_of_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le ?_ ?_ T.weighted_summable
  · intro i
    have hw : 0 ≤ scalarSobolevWeight (I := I) (M := M) i τ :=
      scalarSobolevWeight_nonneg (I := I) (M := M) i τ
    positivity
  · intro i
    have hmono : scalarSobolevWeight (I := I) (M := M) i τ ≤
        scalarSobolevWeight (I := I) (M := M) i σ :=
      scalarSobolevWeight_mono (I := I) (M := M) i hτσ
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

def inclusionFun {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    scalarHs (I := I) (M := M) g τ where
  coeff := T.coeff
  weighted_summable := weighted_summable_of_le (I := I) (M := M) hτσ T

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma inclusionFun_coeff {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    (inclusionFun (I := I) (M := M) hτσ T).coeff = T.coeff := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma inclusionFun_add {τ σ : ℝ} (hτσ : τ ≤ σ)
    (S T : scalarHs (I := I) (M := M) g σ) :
    inclusionFun (I := I) (M := M) hτσ (S + T) =
      inclusionFun (I := I) (M := M) hτσ S +
        inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, add_coeff]

omit [NeZero (Module.finrank ℝ E)] in
lemma inclusionFun_smul {τ σ : ℝ} (hτσ : τ ≤ σ) (c : ℝ)
    (T : scalarHs (I := I) (M := M) g σ) :
    inclusionFun (I := I) (M := M) hτσ (c • T) =
      c • inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, smul_coeff]

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_inclusionFun_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    ‖inclusionFun (I := I) (M := M) hτσ T‖ ≤ ‖T‖ := by
  have h_t_sq : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (inclusionFun (I := I) (M := M) hτσ T)
    rwa [inclusionFun_coeff] at h
  have h_s_sq : ‖T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_le_terms : ∀ i : EigenIdx (I := I) (M := M) g,
      scalarSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    exact mul_le_mul_of_nonneg_right
      (scalarSobolevWeight_mono (I := I) (M := M) i hτσ) (sq_nonneg _)
  have h_tsum_le :
      ∑' i, scalarSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms
      (weighted_summable_of_le (I := I) (M := M) hτσ T) T.weighted_summable
  have h_sq_le : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_t_sq, h_s_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖inclusionFun (I := I) (M := M) hτσ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end scalarHs

def scalarHsInclusion {g : SmoothRiemannianMetric I M} {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    scalarHs (I := I) (M := M) g σ →L[ℝ]
      scalarHs (I := I) (M := M) g τ :=
  LinearMap.mkContinuous
    { toFun := scalarHs.inclusionFun (I := I) (M := M) hτσ
      map_add' := scalarHs.inclusionFun_add (I := I) (M := M) hτσ
      map_smul' := fun c T =>
        scalarHs.inclusionFun_smul (I := I) (M := M) hτσ c T }
    1
    (fun T => by
      change ‖scalarHs.inclusionFun (I := I) (M := M) hτσ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact scalarHs.norm_inclusionFun_le (I := I) (M := M) hτσ T)

namespace scalarHs

variable {g : SmoothRiemannianMetric I M}

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma scalarHsInclusion_apply {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    scalarHsInclusion (I := I) (M := M) (g := g) hτσ T =
      inclusionFun (I := I) (M := M) hτσ T := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarHsInclusion_coeff_fun {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    (scalarHsInclusion (I := I) (M := M) (g := g) hτσ T).coeff =
      T.coeff := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarHsInclusion_coeff {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (scalarHsInclusion (I := I) (M := M) (g := g) hτσ T).coeff i =
      T.coeff i := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarHsInclusion_opNorm_le_one {τ σ : ℝ} (hτσ : τ ≤ σ) :
    ‖scalarHsInclusion (I := I) (M := M) (g := g) hτσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarHsInclusion_norm_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    ‖scalarHsInclusion (I := I) (M := M) (g := g) hτσ T‖ ≤ ‖T‖ :=
  norm_inclusionFun_le (I := I) (M := M) hτσ T

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarHsInclusion_injective {τ σ : ℝ} (hτσ : τ ≤ σ) :
    Function.Injective
      (scalarHsInclusion (I := I) (M := M) (g := g) hτσ) := by
  intro S T hST
  ext i
  have h := congrArg (fun U => scalarHs.coeff U i) hST
  simpa only [scalarHsInclusion_coeff] using h

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarHsInclusion_refl {σ : ℝ} :
    scalarHsInclusion (I := I) (M := M) (g := g) (le_refl σ) =
      ContinuousLinearMap.id ℝ
        (scalarHs (I := I) (M := M) g σ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  refine scalarHs.ext ?_
  funext i
  rw [scalarHsInclusion_coeff, ContinuousLinearMap.id_apply]

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem scalarHsInclusion_refl_apply {σ : ℝ}
    (T : scalarHs (I := I) (M := M) g σ) :
    scalarHsInclusion (I := I) (M := M) (g := g) (le_refl σ) T = T := by
  ext i
  simp only [scalarHsInclusion_coeff]

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarHsInclusion_trans {τ₁ σ τ₂ : ℝ}
    (h₁ : τ₁ ≤ σ) (h₂ : σ ≤ τ₂) :
    scalarHsInclusion (I := I) (M := M) (g := g) (h₁.trans h₂) =
      (scalarHsInclusion (I := I) (M := M) (g := g) h₁).comp
        (scalarHsInclusion (I := I) (M := M) (g := g) h₂) := by
  ext T i
  simp only [scalarHsInclusion_coeff, ContinuousLinearMap.coe_comp',
    Function.comp_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem scalarHsInclusion_trans_apply {τ₁ σ τ₂ : ℝ}
    (h₁ : τ₁ ≤ σ) (h₂ : σ ≤ τ₂)
    (T : scalarHs (I := I) (M := M) g τ₂) :
    scalarHsInclusion (I := I) (M := M) (g := g) (h₁.trans h₂) T =
      scalarHsInclusion (I := I) (M := M) (g := g) h₁
        (scalarHsInclusion (I := I) (M := M) (g := g) h₂ T) := by
  ext i
  simp only [scalarHsInclusion_coeff]

omit [NeZero (Module.finrank ℝ E)] in
lemma coeff_summable_sq_of_nonneg {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) ?_
    T.weighted_summable
  intro i
  have hw : 1 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
    one_le_scalarSobolevWeight (I := I) (M := M) i hσ
  have hsq : 0 ≤ (T.coeff i) ^ 2 := sq_nonneg _
  nlinarith [hw, hsq]

def toL2Seq {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    lp (fun _ : EigenIdx (I := I) (M := M) g => ℝ) 2 :=
  ⟨T.coeff, by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h_eq :
        (fun i : EigenIdx (I := I) (M := M) g =>
          ‖T.coeff i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => (T.coeff i) ^ 2) := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [h_eq]
    exact coeff_summable_sq_of_nonneg (I := I) (M := M) hσ T⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma toL2Seq_apply {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (toL2Seq (I := I) (M := M) hσ T : _ → ℝ) i = T.coeff i := rfl

def toL2Fun {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (resolventHilbertEigenbasisSigma (I := I) (M := M) g).repr.symm
    (toL2Seq (I := I) (M := M) hσ T)

@[simp] lemma scalarL2Coeff_toL2Fun {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    scalarL2Coeff (I := I) (M := M)
        (toL2Fun (I := I) (M := M) hσ T) i = T.coeff i := by
  unfold scalarL2Coeff toL2Fun
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma toL2Seq_add {σ : ℝ} (hσ : 0 ≤ σ)
    (S T : scalarHs (I := I) (M := M) g σ) :
    toL2Seq (I := I) (M := M) hσ (S + T) =
      toL2Seq (I := I) (M := M) hσ S + toL2Seq (I := I) (M := M) hσ T := by
  apply lp.ext
  funext i
  simp only [toL2Seq_apply, lp.coeFn_add, Pi.add_apply, add_coeff]

omit [NeZero (Module.finrank ℝ E)] in
lemma toL2Seq_smul {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ)
    (T : scalarHs (I := I) (M := M) g σ) :
    toL2Seq (I := I) (M := M) hσ (c • T) =
      c • toL2Seq (I := I) (M := M) hσ T := by
  apply lp.ext
  funext i
  simp only [toL2Seq_apply, lp.coeFn_smul, Pi.smul_apply, smul_coeff,
    smul_eq_mul]

lemma toL2Fun_add {σ : ℝ} (hσ : 0 ≤ σ)
    (S T : scalarHs (I := I) (M := M) g σ) :
    toL2Fun (I := I) (M := M) hσ (S + T) =
      toL2Fun (I := I) (M := M) hσ S + toL2Fun (I := I) (M := M) hσ T := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_seq : toL2Seq (I := I) (M := M) hσ (S + T) =
      toL2Seq (I := I) (M := M) hσ S + toL2Seq (I := I) (M := M) hσ T :=
    toL2Seq_add (I := I) (M := M) hσ S T
  have h_map :
      b.repr.symm (toL2Seq (I := I) (M := M) hσ S +
          toL2Seq (I := I) (M := M) hσ T) =
        b.repr.symm (toL2Seq (I := I) (M := M) hσ S) +
          b.repr.symm (toL2Seq (I := I) (M := M) hσ T) :=
    b.repr.symm.map_add _ _
  calc toL2Fun (I := I) (M := M) hσ (S + T)
      = b.repr.symm (toL2Seq (I := I) (M := M) hσ (S + T)) := rfl
    _ = b.repr.symm (toL2Seq (I := I) (M := M) hσ S +
          toL2Seq (I := I) (M := M) hσ T) := by rw [h_seq]
    _ = b.repr.symm (toL2Seq (I := I) (M := M) hσ S) +
          b.repr.symm (toL2Seq (I := I) (M := M) hσ T) := h_map
    _ = toL2Fun (I := I) (M := M) hσ S +
          toL2Fun (I := I) (M := M) hσ T := rfl

lemma toL2Fun_smul {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ)
    (T : scalarHs (I := I) (M := M) g σ) :
    toL2Fun (I := I) (M := M) hσ (c • T) =
      c • toL2Fun (I := I) (M := M) hσ T := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_seq : toL2Seq (I := I) (M := M) hσ (c • T) =
      c • toL2Seq (I := I) (M := M) hσ T :=
    toL2Seq_smul (I := I) (M := M) hσ c T
  have h_map :
      b.repr.symm (c • toL2Seq (I := I) (M := M) hσ T) =
        c • b.repr.symm (toL2Seq (I := I) (M := M) hσ T) :=
    b.repr.symm.map_smul _ _
  calc toL2Fun (I := I) (M := M) hσ (c • T)
      = b.repr.symm (toL2Seq (I := I) (M := M) hσ (c • T)) := rfl
    _ = b.repr.symm (c • toL2Seq (I := I) (M := M) hσ T) := by rw [h_seq]
    _ = c • b.repr.symm (toL2Seq (I := I) (M := M) hσ T) := h_map
    _ = c • toL2Fun (I := I) (M := M) hσ T := rfl

private lemma scalarParseval_norm_sq
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖u‖ ^ 2 =
      ∑' i : EigenIdx (I := I) (M := M) g,
        ‖⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            u⟫_ℝ‖ ^ 2 := by
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
  have h_par := b.tsum_inner_mul_inner u u
  have h_sq : ⟪u, u⟫_ℝ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have h_eq : (fun i : EigenIdx (I := I) (M := M) g =>
        ⟪u, b i⟫_ℝ * ⟪b i, u⟫_ℝ) =
      (fun i => ‖⟪b i, u⟫_ℝ‖ ^ 2) := by
    funext i
    rw [show ⟪u, b i⟫_ℝ = ⟪b i, u⟫_ℝ from real_inner_comm _ _,
        Real.norm_eq_abs, sq_abs, sq]
  rw [h_eq] at h_par
  linarith [h_par, h_sq]

lemma norm_toL2Fun_le {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    ‖toL2Fun (I := I) (M := M) hσ T‖ ≤ ‖T‖ := by
  have h_l2_sq : ‖toL2Fun (I := I) (M := M) hσ T‖ ^ 2 =
      ∑' i, (T.coeff i) ^ 2 := by
    have h_par := scalarParseval_norm_sq (I := I) (M := M)
      (toL2Fun (I := I) (M := M) hσ T)
    have h_eq :
        (fun i : EigenIdx (I := I) (M := M) g =>
          ‖⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            toL2Fun (I := I) (M := M) hσ T⟫_ℝ‖ ^ 2) =
        (fun i => (T.coeff i) ^ 2) := by
      funext i
      have h_coeff : scalarL2Coeff (I := I) (M := M)
          (toL2Fun (I := I) (M := M) hσ T) i = T.coeff i :=
        scalarL2Coeff_toL2Fun (I := I) (M := M) hσ T i
      have h_inner : (⟪resolventHilbertEigenbasisSigma
            (I := I) (M := M) g i,
          toL2Fun (I := I) (M := M) hσ T⟫_ℝ : ℝ) =
          scalarL2Coeff (I := I) (M := M)
            (toL2Fun (I := I) (M := M) hσ T) i := by
        unfold scalarL2Coeff
        exact (HilbertBasis.repr_apply_apply _ _ _).symm
      rw [h_inner, h_coeff, Real.norm_eq_abs, sq_abs]
    rwa [h_eq] at h_par
  have h_hs_sq : ‖T‖ ^ 2 =
      ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
        (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_summ_unweighted :
      Summable (fun i : EigenIdx (I := I) (M := M) g =>
        (T.coeff i) ^ 2) :=
    coeff_summable_sq_of_nonneg (I := I) (M := M) hσ T
  have h_le_terms : ∀ i : EigenIdx (I := I) (M := M) g,
      (T.coeff i) ^ 2 ≤
        scalarSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    have hw : 1 ≤ scalarSobolevWeight (I := I) (M := M) i σ :=
      one_le_scalarSobolevWeight (I := I) (M := M) i hσ
    nlinarith [hw, sq_nonneg (T.coeff i)]
  have h_tsum_le :
      ∑' i, (T.coeff i) ^ 2 ≤
        ∑' i, scalarSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms h_summ_unweighted T.weighted_summable
  have h_sq_le : ‖toL2Fun (I := I) (M := M) hσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_l2_sq, h_hs_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖toL2Fun (I := I) (M := M) hσ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end scalarHs

def scalarHsToL2 {g : SmoothRiemannianMetric I M} {σ : ℝ} (hσ : 0 ≤ σ) :
    scalarHs (I := I) (M := M) g σ →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  LinearMap.mkContinuous
    { toFun := scalarHs.toL2Fun (I := I) (M := M) hσ
      map_add' := scalarHs.toL2Fun_add (I := I) (M := M) hσ
      map_smul' := fun c T => scalarHs.toL2Fun_smul (I := I) (M := M) hσ c T }
    1
    (fun T => by
      change ‖scalarHs.toL2Fun (I := I) (M := M) hσ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact scalarHs.norm_toL2Fun_le (I := I) (M := M) hσ T)

namespace scalarHs

variable {g : SmoothRiemannianMetric I M}

@[simp] lemma scalarHsToL2_apply {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    scalarHsToL2 (I := I) (M := M) (g := g) hσ T =
      toL2Fun (I := I) (M := M) hσ T := rfl

theorem scalarHsToL2_opNorm_le_one {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖scalarHsToL2 (I := I) (M := M) (g := g) hσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

@[simp] theorem scalarL2Coeff_scalarHsToL2 {σ : ℝ} (hσ : 0 ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    scalarL2Coeff (I := I) (M := M)
        (scalarHsToL2 (I := I) (M := M) (g := g) hσ T) i = T.coeff i := by
  rw [scalarHsToL2_apply]
  exact scalarL2Coeff_toL2Fun (I := I) (M := M) hσ T i

theorem scalarHsToL2_injective {σ : ℝ} (hσ : 0 ≤ σ) :
    Function.Injective
      (scalarHsToL2 (I := I) (M := M) (g := g) hσ) := by
  intro S T hST
  ext i
  have hS := scalarL2Coeff_scalarHsToL2 (I := I) (M := M) hσ S i
  have hT := scalarL2Coeff_scalarHsToL2 (I := I) (M := M) hσ T i
  rw [← hS, ← hT, hST]

end scalarHs

def scalarHsZeroEquivL2 (g : SmoothRiemannianMetric I M) :
    scalarHs (I := I) (M := M) g 0 ≃ₗᵢ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (scalarHs.rescaleEquivL2 (I := I) (M := M)
    (g := g) (σ := 0)).trans
    (resolventHilbertEigenbasisSigma (I := I) (M := M) g).repr.symm

namespace scalarHs

variable {g : SmoothRiemannianMetric I M}

theorem scalarHsZeroEquivL2_scalarL2Coeff
    (T : scalarHs (I := I) (M := M) g 0)
    (i : EigenIdx (I := I) (M := M) g) :
    scalarL2Coeff (I := I) (M := M)
        (scalarHsZeroEquivL2 (I := I) (M := M) g T) i =
      T.coeff i := by
  unfold scalarHsZeroEquivL2 scalarL2Coeff
  rw [LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change (scalarHs.rescaleEquivL2 (I := I) (M := M) T : _ → ℝ) i = T.coeff i
  rw [scalarHs.rescaleEquivL2_apply]
  simp only [scalarSobolevWeight_zero, Real.sqrt_one, one_mul]

@[simp] theorem scalarHsZeroEquivL2_symm_coeff
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : EigenIdx (I := I) (M := M) g) :
    ((scalarHsZeroEquivL2 (I := I) (M := M) g).symm u).coeff i =
      scalarL2Coeff (I := I) (M := M) u i := by
  have h := scalarHsZeroEquivL2_scalarL2Coeff (I := I) (M := M)
    ((scalarHsZeroEquivL2 (I := I) (M := M) g).symm u) i
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

end scalarHs

theorem scalarHsToL2_comp_scalarHsInclusion
    {g : SmoothRiemannianMetric I M} {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    (scalarHsToL2 (I := I) (M := M) (g := g) hτ).comp
        (scalarHsInclusion (I := I) (M := M) (g := g) hτσ) =
      scalarHsToL2 (I := I) (M := M) (g := g) (hτ.trans hτσ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  refine (resolventHilbertEigenbasisSigma
    (I := I) (M := M) g).repr.injective ?_
  ext i
  have hlhs : ((resolventHilbertEigenbasisSigma
        (I := I) (M := M) g).repr
      ((scalarHsToL2 (I := I) (M := M) (g := g) hτ).comp
        (scalarHsInclusion (I := I) (M := M) (g := g) hτσ) T)) i =
      T.coeff i := by
    have h := scalarHs.scalarL2Coeff_scalarHsToL2 (I := I) (M := M) hτ
      (scalarHsInclusion (I := I) (M := M) (g := g) hτσ T) i
    rw [scalarHs.scalarHsInclusion_coeff] at h
    simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      scalarL2Coeff] using h
  have hrhs : ((resolventHilbertEigenbasisSigma
        (I := I) (M := M) g).repr
      (scalarHsToL2 (I := I) (M := M) (g := g) (hτ.trans hτσ) T)) i =
      T.coeff i := by
    have h := scalarHs.scalarL2Coeff_scalarHsToL2 (I := I) (M := M)
      (hτ.trans hτσ) T i
    simpa only [scalarL2Coeff] using h
  rw [hlhs, hrhs]

theorem scalarHsToL2_scalarHsInclusion
    {g : SmoothRiemannianMetric I M} {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ)
    (T : scalarHs (I := I) (M := M) g σ) :
    scalarHsToL2 (I := I) (M := M) (g := g) hτ
        (scalarHsInclusion (I := I) (M := M) (g := g) hτσ T) =
      scalarHsToL2 (I := I) (M := M) (g := g) (hτ.trans hτσ) T := by
  have h := scalarHsToL2_comp_scalarHsInclusion (I := I) (M := M)
    (g := g) hτ hτσ
  exact congrArg (fun L => L T) h

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
