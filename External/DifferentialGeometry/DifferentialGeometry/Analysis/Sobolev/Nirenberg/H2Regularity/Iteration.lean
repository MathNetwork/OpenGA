import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergIteration

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in

private lemma contDiff_partial
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (l : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single l 1)) := by
  have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_apply_smooth.comp h_fderiv_smooth

omit [NeZero d] in

private lemma contDiff_partial_partial
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (l i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ
        (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single l 1)) y)
          (EuclideanSpace.single i 1)) :=
  contDiff_partial (contDiff_partial hu l) i

omit [NeZero d] in

private lemma integral_partial_eq_zero_of_compactSupport
    {F : E → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF_supp : HasCompactSupport F)
    (l : Fin d) :
    ∫ x, (fderiv ℝ F x) (EuclideanSpace.single l 1) = 0 := by
  have hF_diff : Differentiable ℝ F := hF.differentiable (by simp)
  have h_const_diff : ∀ x : E, DifferentiableAt ℝ (fun _ : E => (1 : ℝ)) x :=
    fun x => differentiableAt_const _
  have h_F_partial_cont : Continuous
      (fun x : E => (fderiv ℝ F x) (EuclideanSpace.single l 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_F_partial_supp : HasCompactSupport
      (fun x : E => (fderiv ℝ F x) (EuclideanSpace.single l 1)) :=
    hF_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
  have h_F_cont : Continuous F := hF.continuous
  have h_fg_int : Integrable (fun x : E => F x * (1 : ℝ)) := by
    have h_supp : HasCompactSupport (fun x : E => F x * (1 : ℝ)) := by
      have : (fun x : E => F x * (1 : ℝ)) = F := by funext x; ring
      rw [this]; exact hF_supp
    exact (h_F_cont.mul continuous_const).integrable_of_hasCompactSupport h_supp
  have h_f'g_int : Integrable
      (fun x : E => (fderiv ℝ F x) (EuclideanSpace.single l 1) * (1 : ℝ)) := by
    have h_supp : HasCompactSupport
        (fun x : E => (fderiv ℝ F x) (EuclideanSpace.single l 1) * (1 : ℝ)) := by
      have : (fun x : E => (fderiv ℝ F x) (EuclideanSpace.single l 1) * (1 : ℝ)) =
          (fun x : E => (fderiv ℝ F x) (EuclideanSpace.single l 1)) := by
        funext x; ring
      rw [this]; exact h_F_partial_supp
    exact (h_F_partial_cont.mul continuous_const).integrable_of_hasCompactSupport h_supp
  have h_fg'_int : Integrable
      (fun x : E => F x * (fderiv ℝ (fun _ : E => (1 : ℝ)) x) (EuclideanSpace.single l 1))
        := by
    have h_zero : (fun x : E => F x *
        (fderiv ℝ (fun _ : E => (1 : ℝ)) x) (EuclideanSpace.single l 1)) =
        (fun _ : E => (0 : ℝ)) := by
      funext x
      have hd : fderiv ℝ (fun _ : E => (1 : ℝ)) x = 0 := fderiv_const_apply (1 : ℝ)
      rw [hd]
      simp
    rw [h_zero]
    exact integrable_zero _ _ _
  have h_ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure E))
    (f := F) (g := fun _ : E => (1 : ℝ))
    (v := EuclideanSpace.single l 1)
    h_f'g_int h_fg'_int h_fg_int
    (fun x _ => hF_diff x) (fun x _ => h_const_diff x)
  have hLHS : ∫ x : E, F x *
      (fderiv ℝ (fun _ : E => (1 : ℝ)) x) (EuclideanSpace.single l 1) = 0 := by
    have heq : (fun x : E => F x *
        (fderiv ℝ (fun _ : E => (1 : ℝ)) x) (EuclideanSpace.single l 1)) =
        (fun _ : E => (0 : ℝ)) := by
      funext x
      have hd : fderiv ℝ (fun _ : E => (1 : ℝ)) x = 0 := fderiv_const_apply (1 : ℝ)
      rw [hd]
      simp
    rw [heq, integral_zero]
  rw [hLHS] at h_ibp
  have hRHS : ∫ x : E, (fderiv ℝ F x) (EuclideanSpace.single l 1) * (1 : ℝ) =
      ∫ x : E, (fderiv ℝ F x) (EuclideanSpace.single l 1) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  rw [hRHS] at h_ibp
  linarith

omit [NeZero d] in

private lemma setIntegral_partial_eq_zero_of_compactSupport_subset
    {F : E → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF_supp : HasCompactSupport F)
    {Ω : Set E} (h_supp_Ω : tsupport F ⊆ Ω) (l : Fin d) :
    ∫ x in Ω, (fderiv ℝ F x) (EuclideanSpace.single l 1) = 0 := by
  have h_partial_tsupp : tsupport (fun x : E =>
      (fderiv ℝ F x) (EuclideanSpace.single l 1)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single l 1)).trans
      h_supp_Ω
  have h_outside_zero : ∀ x, x ∉ Ω →
      (fderiv ℝ F x) (EuclideanSpace.single l 1) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport (fun y : E =>
        (fderiv ℝ F y) (EuclideanSpace.single l 1)) :=
      fun h => hx (h_partial_tsupp h)
    exact image_eq_zero_of_notMem_tsupport (f := fun y : E =>
      (fderiv ℝ F y) (EuclideanSpace.single l 1)) hx_notin
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_outside_zero]
  exact integral_partial_eq_zero_of_compactSupport hF hF_supp l

omit [NeZero d] in

private lemma fderiv_triple_mul_apply_diff
    {a b c : E → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hc : DifferentiableAt ℝ c x) (l : Fin d) :
    (fderiv ℝ (fun y => a y * b y * c y) x) (EuclideanSpace.single l 1) =
      (fderiv ℝ a x) (EuclideanSpace.single l 1) * b x * c x +
        a x * (fderiv ℝ b x) (EuclideanSpace.single l 1) * c x +
        a x * b x * (fderiv ℝ c x) (EuclideanSpace.single l 1) := by
  have hab_diff : DifferentiableAt ℝ (fun y => a y * b y) x := ha.mul hb
  have h_prod_rule_outer : fderiv ℝ (fun y => a y * b y * c y) x =
      (a x * b x) • fderiv ℝ c x + c x • fderiv ℝ (fun y => a y * b y) x :=
    fderiv_fun_mul hab_diff hc
  have h_prod_rule_inner : fderiv ℝ (fun y => a y * b y) x =
      a x • fderiv ℝ b x + b x • fderiv ℝ a x :=
    fderiv_fun_mul ha hb
  rw [h_prod_rule_outer, h_prod_rule_inner]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

omit [NeZero d] in

private lemma fderiv_triple_mul_apply
    {a b c : E → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (x : E) (l : Fin d) :
    (fderiv ℝ (fun y => a y * b y * c y) x) (EuclideanSpace.single l 1) =
      (fderiv ℝ a x) (EuclideanSpace.single l 1) * b x * c x +
        a x * (fderiv ℝ b x) (EuclideanSpace.single l 1) * c x +
        a x * b x * (fderiv ℝ c x) (EuclideanSpace.single l 1) :=
  fderiv_triple_mul_apply_diff (ha.differentiable (by simp) x)
    (hb.differentiable (by simp) x) (hc.differentiable (by simp) x) l

omit [NeZero d] in

private lemma fderiv_binary_mul_apply_diff
    {a b : E → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (l : Fin d) :
    (fderiv ℝ (fun y => a y * b y) x) (EuclideanSpace.single l 1) =
      (fderiv ℝ a x) (EuclideanSpace.single l 1) * b x +
        a x * (fderiv ℝ b x) (EuclideanSpace.single l 1) := by
  have h_prod_rule : fderiv ℝ (fun y => a y * b y) x =
      a x • fderiv ℝ b x + b x • fderiv ℝ a x :=
    fderiv_fun_mul ha hb
  rw [h_prod_rule]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

omit [NeZero d] in

private lemma fderiv_binary_mul_apply
    {a b : E → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (x : E) (l : Fin d) :
    (fderiv ℝ (fun y => a y * b y) x) (EuclideanSpace.single l 1) =
      (fderiv ℝ a x) (EuclideanSpace.single l 1) * b x +
        a x * (fderiv ℝ b x) (EuclideanSpace.single l 1) :=
  fderiv_binary_mul_apply_diff (ha.differentiable (by simp) x)
    (hb.differentiable (by simp) x) l

private lemma contDiff_principal_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u ψ : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      B.a y i j * (fderiv ℝ u y) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) := by
  have h_a : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => B.a y i j) := B.contDiff_a i j
  have h_du : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    contDiff_partial hu i
  have h_dψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    contDiff_partial hψ j
  exact (h_a.mul h_du).mul h_dψ

private lemma hasCompactSupport_principal_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u ψ : E → ℝ}
    (hψ_supp : HasCompactSupport ψ) (i j : Fin d) :
    HasCompactSupport (fun y : E =>
      B.a y i j * (fderiv ℝ u y) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) := by
  have h_dψ_supp : HasCompactSupport (fun y : E =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  exact h_dψ_supp.mul_left

private lemma tsupport_principal_summand_subset_tsupport_ψ
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u ψ : E → ℝ} (i j : Fin d) :
    tsupport (fun y : E =>
        B.a y i j * (fderiv ℝ u y) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) ⊆ tsupport ψ := by
  have h_dψ_tsupp : tsupport (fun y : E =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single j 1)
  refine subset_trans ?_ h_dψ_tsupp
  refine subset_trans (closure_mono ?_) (subset_refl _)
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h0
  apply hx
  rw [h0]; ring

private lemma principal_summand_partial_decomp
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u ψ : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j l : Fin d) (x : E) :
    (fderiv ℝ (fun y : E =>
        B.a y i j * (fderiv ℝ u y) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
      (EuclideanSpace.single l 1) =
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
        B.a x i j *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single l 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
        B.a x i j * (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
            (EuclideanSpace.single l 1) := by
  have h_a : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => B.a y i j) := B.contDiff_a i j
  have h_du : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    contDiff_partial hu i
  have h_dψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    contDiff_partial hψ j
  exact fderiv_triple_mul_apply h_a h_du h_dψ x l

private lemma principal_summand_integral_zero
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u ψ : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (i j l : Fin d) :
    (∫ x in Ω, (fderiv ℝ (fun y : E => B.a y i j) x)
            (EuclideanSpace.single l 1) *
          (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) +
      (∫ x in Ω, B.a x i j *
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single l 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) +
      (∫ x in Ω, B.a x i j *
          (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
            (EuclideanSpace.single l 1)) = 0 := by
  set F : E → ℝ := fun y =>
    B.a y i j * (fderiv ℝ u y) (EuclideanSpace.single i 1) *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) with hF_def
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_principal_summand B hu hψ i j
  have hF_supp : HasCompactSupport F :=
    hasCompactSupport_principal_summand B hψ_supp i j
  have hF_tsub : tsupport F ⊆ Ω :=
    (tsupport_principal_summand_subset_tsupport_ψ B (u := u) (ψ := ψ) i j).trans
      hψ_tsub
  have hzero := setIntegral_partial_eq_zero_of_compactSupport_subset
    (F := F) (l := l) hF_smooth hF_supp hF_tsub
  have h_pointwise : ∀ x : E,
      (fderiv ℝ F x) (EuclideanSpace.single l 1) =
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
          B.a x i j *
              (fderiv ℝ (fun y : E =>
                (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
                (EuclideanSpace.single l 1) *
              (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
          B.a x i j * (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single l 1) :=
    fun x => principal_summand_partial_decomp B hu hψ i j l x
  have h_int_eq :
      ∫ x in Ω, (fderiv ℝ F x) (EuclideanSpace.single l 1) =
        (∫ x in Ω,
          (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
              (fderiv ℝ u x) (EuclideanSpace.single i 1) *
              (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
            B.a x i j *
                (fderiv ℝ (fun y : E =>
                  (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
                  (EuclideanSpace.single l 1) *
                (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
            B.a x i j * (fderiv ℝ u x) (EuclideanSpace.single i 1) *
              (fderiv ℝ (fun y : E =>
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
                (EuclideanSpace.single l 1)) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise x
  rw [h_int_eq] at hzero
  have h_smooth_T1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) := by
    have h_dla : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1)) :=
      contDiff_partial (B.contDiff_a i j) l
    have h_du : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
        (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
      contDiff_partial hu i
    have h_dψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
      contDiff_partial hψ j
    exact (h_dla.mul h_du).mul h_dψ
  have h_smooth_T2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        B.a x i j *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single l 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) := by
    have h_a : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => B.a y i j) := B.contDiff_a i j
    have h_dlu_du : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1)) :=
      contDiff_partial (contDiff_partial hu i) l
    have h_dψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
      contDiff_partial hψ j
    exact (h_a.mul h_dlu_du).mul h_dψ
  have h_smooth_T3 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single l 1)) := by
    have h_a : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => B.a y i j) := B.contDiff_a i j
    have h_du : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
        (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
      contDiff_partial hu i
    have h_dlψ_dψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single l 1)) :=
      contDiff_partial (contDiff_partial hψ j) l
    exact (h_a.mul h_du).mul h_dlψ_dψ
  have h_supp_T1 : HasCompactSupport (fun x : E =>
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) := by
    have h_dψ_supp : HasCompactSupport (fun y : E =>
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
      hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact h_dψ_supp.mul_left
  have h_supp_T2 : HasCompactSupport (fun x : E =>
        B.a x i j *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single l 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) := by
    have h_dψ_supp : HasCompactSupport (fun y : E =>
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
      hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact h_dψ_supp.mul_left
  have h_supp_T3 : HasCompactSupport (fun x : E =>
        B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single l 1)) := by
    have h_dlψ_supp : HasCompactSupport (fun y : E =>
        (fderiv ℝ (fun y' : E =>
          (fderiv ℝ ψ y') (EuclideanSpace.single j 1)) y)
          (EuclideanSpace.single l 1)) := by
      have hψ_dj_supp : HasCompactSupport (fun y : E =>
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
        hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
      exact hψ_dj_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
    exact h_dlψ_supp.mul_left
  have h_int_T1 : Integrable (fun x : E =>
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
      (volume.restrict Ω) :=
    (h_smooth_T1.continuous.integrable_of_hasCompactSupport h_supp_T1).restrict
  have h_int_T2 : Integrable (fun x : E =>
        B.a x i j *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single l 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
      (volume.restrict Ω) :=
    (h_smooth_T2.continuous.integrable_of_hasCompactSupport h_supp_T2).restrict
  have h_int_T3 : Integrable (fun x : E =>
        B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single l 1))
      (volume.restrict Ω) :=
    (h_smooth_T3.continuous.integrable_of_hasCompactSupport h_supp_T3).restrict
  have hsplit_outer : ∫ x in Ω,
      ((fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
        B.a x i j *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single l 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) +
        B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single l 1) =
      (∫ x in Ω,
        ((fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1) +
          B.a x i j *
              (fderiv ℝ (fun y : E =>
                (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
                (EuclideanSpace.single l 1) *
              (fderiv ℝ ψ x) (EuclideanSpace.single j 1))) +
      ∫ x in Ω,
        B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single l 1) :=
    integral_add (h_int_T1.add h_int_T2) h_int_T3
  rw [hsplit_outer] at hzero
  rw [integral_add h_int_T1 h_int_T2] at hzero
  exact hzero

private lemma zeroth_summand_integral_zero
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u ψ : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (l : Fin d) :
    (∫ x in Ω, (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) +
      (∫ x in Ω, B.c x *
          (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x) +
      (∫ x in Ω, B.c x * u x *
          (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) = 0 := by
  set F : E → ℝ := fun y => B.c y * u y * ψ y with hF_def
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    (B.smooth_c.mul hu).mul hψ
  have hF_supp : HasCompactSupport F := by
    exact hψ_supp.mul_left
  have hF_tsub : tsupport F ⊆ Ω := by
    refine subset_trans ?_ hψ_tsub
    refine subset_trans (closure_mono ?_) (subset_refl _)
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    change B.c x * u x * ψ x = 0
    rw [h0]; ring
  have hzero := setIntegral_partial_eq_zero_of_compactSupport_subset
    (F := F) (l := l) hF_smooth hF_supp hF_tsub
  have h_pointwise : ∀ x : E,
      (fderiv ℝ F x) (EuclideanSpace.single l 1) =
        (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
          B.c x * (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x +
          B.c x * u x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1) :=
    fun x => fderiv_triple_mul_apply B.smooth_c hu hψ x l
  have h_int_eq :
      ∫ x in Ω, (fderiv ℝ F x) (EuclideanSpace.single l 1) =
        (∫ x in Ω,
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
            B.c x * (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x +
            B.c x * u x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise x
  rw [h_int_eq] at hzero
  have h_smooth_T1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) := by
    have h_dlc : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ B.c x) (EuclideanSpace.single l 1)) :=
      contDiff_partial B.smooth_c l
    exact (h_dlc.mul hu).mul hψ
  have h_smooth_T2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        B.c x * (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x) := by
    have h_dlu : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ u x) (EuclideanSpace.single l 1)) :=
      contDiff_partial hu l
    exact (B.smooth_c.mul h_dlu).mul hψ
  have h_smooth_T3 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        B.c x * u x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) := by
    have h_dlψ : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) :=
      contDiff_partial hψ l
    exact (B.smooth_c.mul hu).mul h_dlψ
  have h_supp_T1 : HasCompactSupport (fun x : E =>
        (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) :=
    hψ_supp.mul_left
  have h_supp_T2 : HasCompactSupport (fun x : E =>
        B.c x * (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x) :=
    hψ_supp.mul_left
  have h_supp_T3 : HasCompactSupport (fun x : E =>
        B.c x * u x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) := by
    have h_dlψ_supp : HasCompactSupport (fun x : E =>
        (fderiv ℝ ψ x) (EuclideanSpace.single l 1)) :=
      hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
    exact h_dlψ_supp.mul_left
  have h_int_T1 : Integrable (fun x : E =>
        (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x)
      (volume.restrict Ω) :=
    (h_smooth_T1.continuous.integrable_of_hasCompactSupport h_supp_T1).restrict
  have h_int_T2 : Integrable (fun x : E =>
        B.c x * (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x)
      (volume.restrict Ω) :=
    (h_smooth_T2.continuous.integrable_of_hasCompactSupport h_supp_T2).restrict
  have h_int_T3 : Integrable (fun x : E =>
        B.c x * u x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1))
      (volume.restrict Ω) :=
    (h_smooth_T3.continuous.integrable_of_hasCompactSupport h_supp_T3).restrict
  have hsplit_outer : ∫ x in Ω,
      ((fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
        B.c x * (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x) +
        B.c x * u x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1) =
      (∫ x in Ω,
        ((fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
          B.c x * (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x)) +
      ∫ x in Ω,
        B.c x * u x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1) :=
    integral_add (h_int_T1.add h_int_T2) h_int_T3
  rw [hsplit_outer] at hzero
  rw [integral_add h_int_T1 h_int_T2] at hzero
  exact hzero

def perturbedSource
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u f : E → ℝ) (l : Fin d) (x : E) : ℝ :=
  (fderiv ℝ f x) (EuclideanSpace.single l 1) -
    (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x +
  ∑ i : Fin d, ∑ j : Fin d,
    (fderiv ℝ (fun y : E =>
      (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
        (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
      (EuclideanSpace.single j 1)

private lemma contDiff_perturbedSource
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (l : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (perturbedSource B u f l) := by
  unfold perturbedSource
  have h_dlf : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ f x) (EuclideanSpace.single l 1)) :=
    contDiff_partial hf l
  have h_dlc : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ B.c x) (EuclideanSpace.single l 1)) :=
    contDiff_partial B.smooth_c l
  have h_dlc_u : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x) :=
    h_dlc.mul hu
  refine (h_dlf.sub h_dlc_u).add ?_
  refine ContDiff.sum ?_
  intro i _
  refine ContDiff.sum ?_
  intro j _
  have h_dla : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) :=
    contDiff_partial (B.contDiff_a i j) l
  have h_diu : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    contDiff_partial hu i
  exact contDiff_partial (h_dla.mul h_diu) j

omit [NeZero d] in

private lemma ibp_smooth_against_test
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (l : Fin d) :
    ∫ x in Ω, f x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1) =
      -∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x := by
  have hf_C1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast)
  have h_weak := DeGiorgi.HasWeakPartialDeriv.of_contDiff (d := d) hΩ
    (i := l) (f := f) hf_C1
  exact h_weak ψ hψ hψ_supp hψ_tsub

private lemma ibp_principal_correction
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (l i j : Fin d) :
    ∫ x in Ω,
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1) =
      -∫ x in Ω, (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1) * ψ x := by
  have h_dla : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) :=
    contDiff_partial (B.contDiff_a i j) l
  have h_diu : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    contDiff_partial hu i
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
        (fderiv ℝ u y) (EuclideanSpace.single i 1)) := h_dla.mul h_diu
  exact ibp_smooth_against_test (l := j) hg_smooth hΩ hψ hψ_supp hψ_tsub

private lemma bilin_integrand_pieces_integrable
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u v : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hv_supp : HasCompactSupport v) :
    (Integrable (fun x => B.principalIntegrand u v x) (volume.restrict Ω)) ∧
    (Integrable (fun x => B.c x * u x * v x) (volume.restrict Ω)) ∧
    (∀ i j : Fin d, Integrable (fun x => B.a x i j *
        (fderiv ℝ u x) (EuclideanSpace.single i 1) *
        (fderiv ℝ v x) (EuclideanSpace.single j 1)) (volume.restrict Ω)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_cont : Continuous (B.principalIntegrand u v) :=
      B.continuous_principalIntegrand (hu.of_le (by norm_cast)) (hv.of_le (by norm_cast))
    have h_supp : HasCompactSupport (B.principalIntegrand u v) := by
      unfold SmoothEllipticBilinearForm.principalIntegrand
      have h_dv_supp : ∀ j : Fin d, HasCompactSupport (fun x : E =>
          (fderiv ℝ v x) (EuclideanSpace.single j 1)) :=
        fun j => hv_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
      apply HasCompactSupport.intro' hv_supp (isClosed_tsupport _)
      intro x hx
      have hx_eq : v =ᶠ[𝓝 x] 0 :=
        (isClosed_tsupport (f := v)).isOpen_compl.eventually_mem hx |>.mono
          (fun y hy => image_eq_zero_of_notMem_tsupport hy)
      have h_dv_zero : ∀ j : Fin d,
          (fderiv ℝ v x) (EuclideanSpace.single j 1) = 0 := by
        intro j
        rw [Filter.EventuallyEq.fderiv_eq hx_eq]
        simp
      rw [Finset.sum_eq_zero]
      intro i _
      rw [Finset.sum_eq_zero]
      intro j _
      rw [h_dv_zero j]
      ring
    exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict
  · have h_cont : Continuous (fun x => B.c x * u x * v x) :=
      (B.continuous_c.mul hu.continuous).mul hv.continuous
    have h_supp : HasCompactSupport (fun x => B.c x * u x * v x) :=
      hv_supp.mul_left
    exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict
  · intro i j
    have h_cont : Continuous (fun x : E =>
        B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ v x) (EuclideanSpace.single j 1)) := by
      refine ((B.continuous_a i j).mul ?_).mul ?_
      · exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
      · exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const
    have h_supp : HasCompactSupport (fun x : E =>
        B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ v x) (EuclideanSpace.single j 1)) := by
      have h_dv_supp : HasCompactSupport (fun x : E =>
          (fderiv ℝ v x) (EuclideanSpace.single j 1)) :=
        hv_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
      exact h_dv_supp.mul_left
    exact (h_cont.integrable_of_hasCompactSupport h_supp).restrict

private lemma bilin_decomp
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u v : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hv_supp : HasCompactSupport v) :
    B.bilin u v =
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ u x) (EuclideanSpace.single i 1) *
        (fderiv ℝ v x) (EuclideanSpace.single j 1)) +
      ∫ x in Ω, B.c x * u x * v x := by
  classical
  obtain ⟨h_princ_int, h_zero_int, h_summand_int⟩ :=
    bilin_integrand_pieces_integrable B hu hv hv_supp
  unfold SmoothEllipticBilinearForm.bilin
  rw [integral_add h_princ_int h_zero_int]
  congr 1
  unfold SmoothEllipticBilinearForm.principalIntegrand
  rw [integral_finset_sum (s := Finset.univ) (f := fun (i : Fin d) (x : E) =>
      ∑ j : Fin d, B.a x i j *
        (fderiv ℝ u x) (EuclideanSpace.single i 1) *
        (fderiv ℝ v x) (EuclideanSpace.single j 1))
    (fun i _ => integrable_finset_sum _ (fun j _ => h_summand_int i j))]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [integral_finset_sum (s := Finset.univ) (f := fun (j : Fin d) (x : E) =>
      B.a x i j *
        (fderiv ℝ u x) (EuclideanSpace.single i 1) *
        (fderiv ℝ v x) (EuclideanSpace.single j 1))
    (fun j _ => h_summand_int i j)]

omit [NeZero d] in

private lemma mixed_partial_symm
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : E) (i l : Fin d) :
    (fderiv ℝ (fun y : E =>
        (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single l 1) =
      (fderiv ℝ (fun y : E =>
        (fderiv ℝ u y) (EuclideanSpace.single l 1)) x)
        (EuclideanSpace.single i 1) := by
  set f' : E → (E →L[ℝ] ℝ) := fderiv ℝ u with hf'_def
  set f'' : E →L[ℝ] (E →L[ℝ] ℝ) := fderiv ℝ f' x with hf''_def
  have hu_diff : Differentiable ℝ u := hu.differentiable (by simp)
  have hf'_diff : Differentiable ℝ f' :=
    (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have h_hasFDerivAt_u : ∀ y : E, HasFDerivAt u (f' y) y :=
    fun y => (hu_diff y).hasFDerivAt
  have h_hasFDerivAt_f' : HasFDerivAt f' f'' x := (hf'_diff x).hasFDerivAt
  have h_symm := second_derivative_symmetric (𝕜 := ℝ) (f' := f')
    h_hasFDerivAt_u h_hasFDerivAt_f' (EuclideanSpace.single l 1)
    (EuclideanSpace.single i 1)
  have h_apply_e_i : HasFDerivAt
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))
      (f' x) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt
  have h_apply_e_l : HasFDerivAt
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ)))
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ)))
      (f' x) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).hasFDerivAt
  have h_lhs_HasFDerivAt :
      HasFDerivAt (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))
        ((ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).comp f'') x :=
    h_apply_e_i.comp x h_hasFDerivAt_f'
  have h_rhs_HasFDerivAt :
      HasFDerivAt (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single l 1))
        ((ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single l (1 : ℝ))).comp f'') x :=
    h_apply_e_l.comp x h_hasFDerivAt_f'
  rw [h_lhs_HasFDerivAt.fderiv, h_rhs_HasFDerivAt.fderiv]
  change (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))
        (f'' (EuclideanSpace.single l 1)) =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ)))
        (f'' (EuclideanSpace.single i 1))
  simp only [ContinuousLinearMap.apply_apply]
  exact h_symm

private theorem bilin_partial_eq_integral_perturbed
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ} (h_weak : B.IsSmoothWeakSolution u f)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : HasCompactSupport ψ) (hψ_tsub : tsupport ψ ⊆ Ω)
    (l : Fin d) :
    B.bilin (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single l 1)) ψ =
      ∫ x in Ω, perturbedSource B u f l x * ψ x := by
  classical
  obtain ⟨hu, hu_test⟩ := h_weak
  have hu_l : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ u y) (EuclideanSpace.single l 1)) := contDiff_partial hu l
  have hψ_l : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := contDiff_partial hψ l
  have hψ_l_supp : HasCompactSupport (fun y : E =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
    hψ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
  have hψ_l_tsub : tsupport (fun y : E =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single l 1)).trans
      hψ_tsub
  have h_lhs := bilin_decomp B hu_l hψ hψ_supp
  have h_orig := bilin_decomp B hu hψ_l hψ_l_supp
  have h_orig_eq : B.bilin u (fun y : E =>
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) =
      ∫ x in Ω, f x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1) :=
    hu_test (fun y : E => (fderiv ℝ ψ y) (EuclideanSpace.single l 1))
      hψ_l hψ_l_supp hψ_l_tsub
  have h_ibp_f : ∫ x in Ω, f x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1) =
      -∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x :=
    ibp_smooth_against_test hf hΩ hψ hψ_supp hψ_tsub l
  have h_ibp_corr : ∀ i j : Fin d,
      ∫ x in Ω,
        (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
          (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1) =
      -∫ x in Ω, (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1) * ψ x :=
    fun i j => ibp_principal_correction hΩ B hu hψ hψ_supp hψ_tsub l i j
  have h_princ_zero := fun i j =>
    principal_summand_integral_zero B hu hψ hψ_supp hψ_tsub i j l
  have h_zero_zero := zeroth_summand_integral_zero B hu hψ hψ_supp hψ_tsub l
  rw [h_lhs]
  have h_princ_substitute : ∀ i j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1) =
      (-∫ x in Ω, (fderiv ℝ (fun y : E => B.a y i j) x)
          (EuclideanSpace.single l 1) *
        (fderiv ℝ u x) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) -
      ∫ x in Ω, B.a x i j *
        (fderiv ℝ u x) (EuclideanSpace.single i 1) *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
          (EuclideanSpace.single l 1) := by
    intro i j
    have := h_princ_zero i j
    linarith
  have h_lhs_swap : ∀ i j : Fin d,
      ∫ x in Ω, B.a x i j *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1) =
      ∫ x in Ω, B.a x i j *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1) := by
    intro i j
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    change B.a x i j * (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1) =
      B.a x i j * (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)
    rw [(mixed_partial_symm hu x i l).symm]
  have h_lhs_swap_sum :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) =
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact h_lhs_swap i j
  rw [h_lhs_swap_sum]
  set S₁ : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω,
      (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
      (fderiv ℝ u x) (EuclideanSpace.single i 1) *
      (fderiv ℝ ψ x) (EuclideanSpace.single j 1) with hS₁_def
  set S₂ : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
      (fderiv ℝ u x) (EuclideanSpace.single i 1) *
      (fderiv ℝ (fun y : E =>
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
        (EuclideanSpace.single l 1) with hS₂_def
  set Z₁ : ℝ := ∫ x in Ω, B.c x *
      (fderiv ℝ u x) (EuclideanSpace.single l 1) * ψ x with hZ₁_def
  set Z₂ : ℝ := ∫ x in Ω, B.c x * u x *
      (fderiv ℝ ψ x) (EuclideanSpace.single l 1) with hZ₂_def
  set Z₃ : ℝ := ∫ x in Ω, (fderiv ℝ B.c x) (EuclideanSpace.single l 1) *
      u x * ψ x with hZ₃_def
  have h_principal_sum_eq :
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single l 1) *
        (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) = -S₁ - S₂ := by
    rw [hS₁_def, hS₂_def]
    have hsubst : ∀ i j : Fin d,
        (∫ x in Ω, B.a x i j *
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single l 1) *
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) =
        ((-∫ x in Ω, (fderiv ℝ (fun y : E => B.a y i j) x)
              (EuclideanSpace.single l 1) *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) -
          ∫ x in Ω, B.a x i j *
            (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
              (EuclideanSpace.single l 1)) := h_princ_substitute
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => hsubst i j))]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [h_principal_sum_eq]
  have h_Z : Z₁ = -Z₃ - Z₂ := by
    rw [hZ₁_def, hZ₂_def, hZ₃_def]
    have := h_zero_zero
    linarith
  change -S₁ - S₂ + Z₁ = ∫ x in Ω, perturbedSource B u f l x * ψ x
  rw [h_Z]
  have h_orig_combined : S₂ + Z₂ =
      ∫ x in Ω, f x * (fderiv ℝ ψ x) (EuclideanSpace.single l 1) := by
    have h_S₂_swap : S₂ = ∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, B.a x i j *
        (fderiv ℝ u x) (EuclideanSpace.single i 1) *
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) x)
          (EuclideanSpace.single j 1) := by
      rw [hS₂_def]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change B.a x i j * (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) x)
            (EuclideanSpace.single l 1) =
        B.a x i j * (fderiv ℝ u x) (EuclideanSpace.single i 1) *
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) x)
            (EuclideanSpace.single j 1)
      rw [mixed_partial_symm hψ x j l]
    have h_eq : S₂ + Z₂ = B.bilin u (fun y : E =>
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
      rw [h_orig, h_S₂_swap, hZ₂_def]
    rw [h_eq, h_orig_eq]
  have h_S₂_Z₂ : S₂ + Z₂ =
      -∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x := by
    rw [h_orig_combined, h_ibp_f]
  have h_S₁_eq_neg_corr : S₁ = -(∑ i : Fin d, ∑ j : Fin d,
      ∫ x in Ω, (fderiv ℝ (fun y : E =>
        (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) * ψ x) := by
    rw [hS₁_def]
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω,
              (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
              (fderiv ℝ u x) (EuclideanSpace.single i 1) *
              (fderiv ℝ ψ x) (EuclideanSpace.single j 1)) =
        ∑ i : Fin d, ∑ j : Fin d, -(-(∫ x in Ω,
              (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
              (fderiv ℝ u x) (EuclideanSpace.single i 1) *
              (fderiv ℝ ψ x) (EuclideanSpace.single j 1))) by simp]
    rw [show (∑ i : Fin d, ∑ j : Fin d, -(-(∫ x in Ω,
              (fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single l 1) *
              (fderiv ℝ u x) (EuclideanSpace.single i 1) *
              (fderiv ℝ ψ x) (EuclideanSpace.single j 1)))) =
        ∑ i : Fin d, ∑ j : Fin d, -(∫ x in Ω,
              (fderiv ℝ (fun y : E =>
                (fderiv ℝ (fun z : E => B.a z i j) y)
                  (EuclideanSpace.single l 1) *
                (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
                (EuclideanSpace.single j 1) * ψ x) by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      have h := h_ibp_corr i j
      linarith]
    simp only [Finset.sum_neg_distrib]
  rw [h_S₁_eq_neg_corr]
  have h_dlf : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ f x) (EuclideanSpace.single l 1)) :=
    contDiff_partial hf l
  have h_dlc_u : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
      (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x) :=
    (contDiff_partial B.smooth_c l).mul hu
  have h_pert_ψ_int :
      Integrable (fun x : E => perturbedSource B u f l x * ψ x)
        (volume.restrict Ω) := by
    have h_pert_smooth : ContDiff ℝ (⊤ : ℕ∞) (perturbedSource B u f l) :=
      contDiff_perturbedSource B hu hf l
    have h_supp : HasCompactSupport (fun x : E =>
        perturbedSource B u f l x * ψ x) := hψ_supp.mul_left
    exact ((h_pert_smooth.continuous.mul hψ.continuous).integrable_of_hasCompactSupport
      h_supp).restrict
  have h_pert_decomp : ∫ x in Ω, perturbedSource B u f l x * ψ x =
      (∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x) -
      (∫ x in Ω, (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω,
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) * ψ x := by
    have hpw : ∀ x : E, perturbedSource B u f l x * ψ x =
        (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
        (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
        (∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1)) * ψ x := by
      intro x
      unfold perturbedSource
      ring
    have h_int_eq : ∫ x in Ω, perturbedSource B u f l x * ψ x =
        ∫ x in Ω, ((fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
          (∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1)) * ψ x) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall hpw
    rw [h_int_eq]
    have h_T1_int : Integrable (fun x : E =>
        (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x)
        (volume.restrict Ω) :=
      ((h_dlf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport
        hψ_supp.mul_left).restrict
    have h_T2_int : Integrable (fun x : E =>
        (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x)
        (volume.restrict Ω) :=
      ((h_dlc_u.continuous.mul hψ.continuous).integrable_of_hasCompactSupport
        hψ_supp.mul_left).restrict
    have h_corr_smooth : ∀ i j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) * ψ x) := by
      intro i j
      have h_dla : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1)) :=
        contDiff_partial (B.contDiff_a i j) l
      have h_diu : ContDiff ℝ (⊤ : ℕ∞) (fun y : E =>
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
        contDiff_partial hu i
      have h_pj : ContDiff ℝ (⊤ : ℕ∞) (fun x : E =>
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1)) :=
        contDiff_partial (h_dla.mul h_diu) j
      exact h_pj.mul hψ
    have h_corr_int : ∀ i j : Fin d, Integrable (fun x : E =>
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) * ψ x) (volume.restrict Ω) := by
      intro i j
      exact (((h_corr_smooth i j).continuous).integrable_of_hasCompactSupport
        hψ_supp.mul_left).restrict
    have h_sum_int : Integrable (fun x : E =>
        (∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1)) * ψ x) (volume.restrict Ω) := by
      have heq : (fun x : E =>
          (∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1)) * ψ x) =
        (fun x : E => ∑ i : Fin d, ∑ j : Fin d,
          (fderiv ℝ (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1) * ψ x) := by
        funext x; rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
      rw [heq]
      exact integrable_finset_sum _
        (fun i _ => integrable_finset_sum _ (fun j _ => h_corr_int i j))
    have h_form_eq : (fun x : E =>
          (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
          (∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1)) * ψ x) =
        (fun x : E =>
          ((fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) +
          (∑ i : Fin d, ∑ j : Fin d,
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
                (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single j 1) * ψ x)) := by
      funext x
      rw [Finset.sum_mul]
      refine congrArg (fun e =>
          (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
            (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x + e)
        ?_
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_mul]
    rw [show (∫ x in Ω,
          (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
          (∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fun y : E =>
            (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
              (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single j 1)) * ψ x) =
        ∫ x in Ω,
          ((fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) +
          (∑ i : Fin d, ∑ j : Fin d,
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
                (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single j 1) * ψ x) by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      have := congr_fun h_form_eq x
      exact this]
    have h_corr_sum_int : Integrable (fun x : E => ∑ i : Fin d, ∑ j : Fin d,
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) * ψ x) (volume.restrict Ω) :=
      integrable_finset_sum _
        (fun i _ => integrable_finset_sum _ (fun j _ => h_corr_int i j))
    have hLHS : ∫ x in Ω,
          (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x +
          (∑ i : Fin d, ∑ j : Fin d,
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
                (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single j 1) * ψ x) =
        (∫ x in Ω,
          (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x -
          (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) +
        (∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
            (fderiv ℝ (fun y : E =>
              (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
                (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single j 1) * ψ x) :=
      integral_add (h_T1_int.sub h_T2_int) h_corr_sum_int
    rw [hLHS]
    rw [integral_sub h_T1_int h_T2_int]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
        (fun j _ => h_corr_int i j))]
    refine congrArg (fun e =>
        ((∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x) -
          ∫ x in Ω, (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x) + e)
      ?_
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_corr_int i j)]
  rw [h_pert_decomp]
  change -(-(∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω,
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) * ψ x)) - S₂ + (-Z₃ - Z₂) =
      ((∫ x in Ω, (fderiv ℝ f x) (EuclideanSpace.single l 1) * ψ x) -
      (∫ x in Ω, (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x)) +
      ∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω,
        (fderiv ℝ (fun y : E =>
          (fderiv ℝ (fun z : E => B.a z i j) y) (EuclideanSpace.single l 1) *
            (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single j 1) * ψ x
  have hZ₃_explicit : Z₃ =
      ∫ x in Ω, (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x * ψ x := by
    rw [hZ₃_def]
  rw [hZ₃_explicit]
  linarith

theorem partial_smooth_weak_solution
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ} (h_weak : B.IsSmoothWeakSolution u f)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : Fin d) :
    B.IsSmoothWeakSolution
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single l 1))
      (perturbedSource B u f l) := by
  refine ⟨contDiff_partial h_weak.1 l, ?_⟩
  intro ψ hψ hψ_supp hψ_tsub
  exact bilin_partial_eq_integral_perturbed hΩ B h_weak hf hψ hψ_supp hψ_tsub l

theorem partial_u_in_h2_loc
    {Ω : Set E} (hΩ : IsOpen Ω) (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ} (h_weak : B.IsSmoothWeakSolution u f)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_in_Ω : closure Ω'' ⊆ Ω)
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω) (l : Fin d) :
    ∀ i k : Fin d, ∃ g : E → ℝ,
      MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ
          (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single l 1)) y)
            (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set E, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧ closure Ω' ⊆ Ω ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(volume : Measure E) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin d, ((fderiv ℝ
                    (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single l 1)) x)
                    (EuclideanSpace.single j 1))^2
                ∂(volume : Measure E) +
              ∫ x in Ω', ((fderiv ℝ u x) (EuclideanSpace.single l 1))^2
                ∂(volume : Measure E) +
              ∫ x in Ω', (perturbedSource B u f l x)^2 ∂(volume : Measure E)) := by
  classical
  have h_part_weak : B.IsSmoothWeakSolution
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single l 1))
      (perturbedSource B u f l) :=
    partial_smooth_weak_solution hΩ B h_weak hf l
  have h_pert_l2 : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp (perturbedSource B u f l) 2 (volume.restrict Ω') := by
    intro Ω' hΩ'_cc
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞) (perturbedSource B u f l) :=
      contDiff_perturbedSource B h_weak.1 hf l
    have h_cont : Continuous (perturbedSource B u f l) := h_smooth.continuous
    have h_volume_lt_top : volume Ω' < ⊤ :=
      lt_of_le_of_lt (measure_mono subset_closure) hΩ'_cc.measure_lt_top
    haveI : IsFiniteMeasure (volume.restrict Ω') := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact h_volume_lt_top
    obtain ⟨M, hM⟩ := hΩ'_cc.bddAbove_image h_cont.abs.continuousOn
    refine MemLp.of_bound h_cont.aestronglyMeasurable (max M 0) ?_
    rw [ae_restrict_iff (μ := volume) (s := Ω')
      ((isClosed_le (h_cont.norm) continuous_const).measurableSet)]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_closure : x ∈ closure Ω' := subset_closure hx
    have h := hM (Set.mem_image_of_mem _ hx_closure)
    rw [Real.norm_eq_abs]
    exact h.trans (le_max_left _ _)
  obtain ⟨C, hC_nn, h_eng⟩ := loc_smooth_solution (d := d) B
    hΩ'' hΩ''_compact_closure hΩ''_in_Ω h_room
  intro i k
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ := h_eng h_part_weak h_pert_l2 i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

end DifferentialGeometry.Analysis.Sobolev.NirenbergIteration
