import DifferentialGeometry.Analysis.Heat.Semigroup.Defs
import DifferentialGeometry.Geometry.Operator.HessianTrace
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Geometry.Operator.VossWeyl
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Compact


noncomputable section

open Bundle Manifold MeasureTheory Set Filter SignType
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private lemma isHermitian_real_entry
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (i j : n) :
    A i j = ∑ k : n,
        (hA.eigenvectorUnitary : Matrix n n ℝ) i k *
          hA.eigenvalues k *
          (hA.eigenvectorUnitary : Matrix n n ℝ) j k := by
  classical
  have hspec : A = ((hA.eigenvectorUnitary : Matrix n n ℝ) *
      (Matrix.diagonal hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ)) := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hcomp : (RCLike.ofReal (K := ℝ)) ∘ hA.eigenvalues = hA.eigenvalues := by
      funext k; simp
    rw [hcomp] at h
    exact h
  have h := congr_fun (congr_fun hspec i) j
  rw [h]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq]
    have hstar : (star (hA.eigenvectorUnitary : Matrix n n ℝ)) k j =
        (hA.eigenvectorUnitary : Matrix n n ℝ) j k := by
      change star ((hA.eigenvectorUnitary : Matrix n n ℝ) j k) = _
      exact star_trivial _
    rw [hstar]
  · intro ℓ _ hℓ
    rw [Matrix.diagonal_apply_ne _ hℓ]
    ring
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma sum_posSemidef_mul_neg_semidef_le_zero
    {n : Type*} [Fintype n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef)
    {H : Matrix n n ℝ}
    (hH_neg : ∀ v : n → ℝ, v ⬝ᵥ (H *ᵥ v) ≤ 0) :
    ∑ i, ∑ j, M i j * H i j ≤ 0 := by
  classical
  have h_lambda_nn : ∀ k : n, 0 ≤ hM.isHermitian.eigenvalues k :=
    fun k => Matrix.PosSemidef.eigenvalues_nonneg hM k
  let U : Matrix n n ℝ := (hM.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  have h1 : ∑ i, ∑ j, M i j * H i j =
      ∑ k, hM.isHermitian.eigenvalues k *
        (∑ i, ∑ j, U i k * U j k * H i j) := by
    have step1 : ∀ i j : n, M i j * H i j =
        ∑ k, hM.isHermitian.eigenvalues k * (U i k * U j k * H i j) := by
      intros i j
      rw [isHermitian_real_entry hM.isHermitian i j]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intros k _
      ring
    have step2 : ∑ i, ∑ j, M i j * H i j =
        ∑ i, ∑ j, ∑ k,
          hM.isHermitian.eigenvalues k * (U i k * U j k * H i j) := by
      refine Finset.sum_congr rfl ?_
      intros i _
      refine Finset.sum_congr rfl ?_
      intros j _
      exact step1 i j
    rw [step2]
    rw [Finset.sum_comm_cycle (s := Finset.univ) (t := Finset.univ) (u := Finset.univ)
        (f := fun i j k =>
          hM.isHermitian.eigenvalues k * (U i k * U j k * H i j))]
    refine Finset.sum_congr rfl ?_
    intros k _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intros i _
    rw [Finset.mul_sum]
  rw [h1]
  apply Finset.sum_nonpos
  intro k _
  have h_quad : ∑ i, ∑ j, U i k * U j k * H i j =
      (fun i => U i k) ⬝ᵥ (H *ᵥ (fun i => U i k)) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [h_quad]
  exact mul_nonpos_of_nonneg_of_nonpos (h_lambda_nn k) (hH_neg _)

private lemma deriv_deriv_nonpos_of_isLocalMax_at_zero
    {g : ℝ → ℝ} (hg_max : IsLocalMax g 0)
    (hg_C2 : ContDiffAt ℝ 2 g 0) :
    deriv (deriv g) 0 ≤ 0 := by
  classical
  by_contra h_pos
  push Not at h_pos
  have h_deriv_zero : deriv g 0 = 0 := hg_max.deriv_eq_zero
  have h_sign : ∀ᶠ x in 𝓝 (0 : ℝ), sign (deriv g x) = sign (x - 0) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos h_pos h_deriv_zero
  have h_sign' : ∀ᶠ x in 𝓝 (0 : ℝ), sign (deriv g x) = sign x := by
    filter_upwards [h_sign] with x hx
    simpa using hx
  rw [Metric.eventually_nhds_iff] at h_sign'
  obtain ⟨ε₁, hε₁_pos, hε₁_sign⟩ := h_sign'
  obtain ⟨u, hu_mem_nhd, hu_C2⟩ := hg_C2.contDiffOn (n := 2) le_rfl
    (by intro h; exfalso; revert h; decide)
  have hu_C1 : ContDiffOn ℝ 1 g u := hu_C2.of_le (by norm_num)
  have hg_diff_on : DifferentiableOn ℝ g u := hu_C1.differentiableOn (by norm_num)
  have hg_cont_on : ContinuousOn g u := hu_C1.continuousOn
  obtain ⟨ε₂, hε₂_pos, hε₂_sub⟩ := Metric.mem_nhds_iff.mp hu_mem_nhd
  set ε := min ε₁ ε₂ / 2 with hε_def
  have hε_pos : 0 < ε := by
    have : 0 < min ε₁ ε₂ := lt_min hε₁_pos hε₂_pos
    linarith
  have hε_lt_ε₁ : ε < ε₁ := by
    have h := min_le_left ε₁ ε₂
    linarith
  have hε_lt_ε₂ : ε < ε₂ := by
    have h := min_le_right ε₁ ε₂
    linarith
  have hIcc_sub_u : Set.Icc (0 : ℝ) ε ⊆ u := by
    intro x hx
    apply hε₂_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2]
  have hg_cont_Icc : ContinuousOn g (Set.Icc (0 : ℝ) ε) := hg_cont_on.mono hIcc_sub_u
  have hderiv_pos : ∀ x ∈ Set.Ioo (0 : ℝ) ε, 0 < deriv g x := by
    intro x hx
    have hx_lt : dist x 0 < ε₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_of_lt hx.1)]
      linarith [hx.2]
    have h_signx : sign (deriv g x) = sign x := hε₁_sign hx_lt
    have hsignx : sign x = 1 := sign_pos hx.1
    rw [hsignx] at h_signx
    rwa [sign_eq_one_iff] at h_signx
  have hMono : StrictMonoOn g (Set.Icc (0 : ℝ) ε) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hg_cont_Icc ?_
    intro x hx
    rw [interior_Icc] at hx
    exact hderiv_pos x hx
  rw [show (IsLocalMax g 0) = (∀ᶠ x in 𝓝 (0 : ℝ), g x ≤ g 0) from rfl,
    Metric.eventually_nhds_iff] at hg_max
  obtain ⟨δ, hδ_pos, hδ_le⟩ := hg_max
  set t := min (ε / 2) (δ / 2) with ht_def
  have ht_pos : 0 < t := lt_min (by linarith) (by linarith)
  have ht_le_ε : t ≤ ε / 2 := min_le_left _ _
  have ht_le_δ : t ≤ δ / 2 := min_le_right _ _
  have ht_in_Icc : t ∈ Set.Icc (0 : ℝ) ε := ⟨le_of_lt ht_pos, by linarith [hε_pos]⟩
  have ht_in_ball : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_of_lt ht_pos)]
    linarith
  have ht_le_g0 : g t ≤ g 0 := hδ_le ht_in_ball
  have ht_lt : g 0 < g t := hMono (left_mem_Icc.mpr (le_of_lt hε_pos)) ht_in_Icc ht_pos
  linarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sndFDeriv_apply_self_nonpos_of_isLocalMax
    {ftilde : E → ℝ} {y₀ : E} (hf_max : IsLocalMax ftilde y₀)
    (hf_C2 : ContDiffAt ℝ 2 ftilde y₀) (v : E) :
    (fderiv ℝ (fderiv ℝ ftilde) y₀ v) v ≤ 0 := by
  classical
  set g : ℝ → ℝ := fun t => ftilde (y₀ + t • v) with hg_def
  set φ : ℝ → E := fun t => y₀ + t • v with hφ_def
  have hφ_smooth : ContDiff ℝ ∞ φ :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hφ_zero : φ 0 = y₀ := by simp [hφ_def]
  have hg_eq : g = ftilde ∘ φ := by funext t; rfl
  have hg_C2 : ContDiffAt ℝ 2 g 0 := by
    rw [hg_eq]
    refine ContDiffAt.comp 0 ?_ (hφ_smooth.contDiffAt.of_le ?_)
    · rw [hφ_zero]; exact hf_C2
    · have h1 : (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) := by norm_cast
      have h2 : ((⊤ : ℕ∞) : WithTop ℕ∞) = (∞ : WithTop ℕ∞) := rfl
      rw [h1]
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hg_max : IsLocalMax g 0 := by
    have hf_max_filter : ∀ᶠ y in 𝓝 y₀, ftilde y ≤ ftilde y₀ := hf_max
    have h_pre : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ {y | ftilde y ≤ ftilde y₀} := by
      have : Tendsto φ (𝓝 0) (𝓝 y₀) := by
        rw [← hφ_zero]; exact hφ_cont.continuousAt
      exact this hf_max_filter
    change ∀ᶠ t in 𝓝 (0 : ℝ), g t ≤ g 0
    have hg_eval0 : g 0 = ftilde y₀ := by
      change ftilde (φ 0) = ftilde y₀
      rw [hφ_zero]
    rw [hg_eval0]
    exact h_pre
  have h_g_2nd : deriv (deriv g) 0 ≤ 0 :=
    deriv_deriv_nonpos_of_isLocalMax_at_zero hg_max hg_C2
  obtain ⟨w, hw_nhd, hw_C2⟩ := hf_C2.contDiffOn (n := 2) le_rfl
    (by intro h; exfalso; revert h; decide)
  have hw_open : interior w ∈ 𝓝 y₀ := interior_mem_nhds.mpr hw_nhd
  have hf_C1 : ContDiffOn ℝ 1 ftilde (interior w) :=
    (hw_C2.of_le (by norm_num)).mono interior_subset
  have hf_diff_w : DifferentiableOn ℝ ftilde (interior w) :=
    hf_C1.differentiableOn (by norm_num)
  have hφ_in_int_w : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ interior w := by
    rw [← hφ_zero] at hw_open
    exact hφ_cont.continuousAt.preimage_mem_nhds hw_open
  have hf_diff_near : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ ftilde (φ t) := by
    filter_upwards [hφ_in_int_w] with t ht
    exact (hf_diff_w (φ t) ht).differentiableAt (isOpen_interior.mem_nhds ht)
  have h_deriv_g_eq : ∀ᶠ t in 𝓝 (0 : ℝ),
      deriv g t = fderiv ℝ ftilde (φ t) v := by
    filter_upwards [hf_diff_near] with t hf_diff
    have hφ_deriv : HasDerivAt φ v t := by
      have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by
        simpa using (hasDerivAt_id t).smul_const v
      simpa using (hasDerivAt_const t y₀).add h1
    have hf_hasFDeriv : HasFDerivAt ftilde (fderiv ℝ ftilde (φ t)) (φ t) := hf_diff.hasFDerivAt
    have hcomp := hf_hasFDeriv.comp_hasDerivAt t hφ_deriv
    have hg_hasDeriv : HasDerivAt g (fderiv ℝ ftilde (φ t) v) t := by
      simpa [hg_eq] using hcomp
    exact hg_hasDeriv.deriv
  have h_deriv_deriv_g_eq : deriv (deriv g) 0 =
      deriv (fun t : ℝ => fderiv ℝ ftilde (φ t) v) 0 :=
    Filter.EventuallyEq.deriv_eq h_deriv_g_eq
  have h_chain : HasDerivAt (fun t : ℝ => fderiv ℝ ftilde (φ t) v)
      ((fderiv ℝ (fderiv ℝ ftilde) y₀ v) v) 0 := by
    set L_v : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v with hLv_def
    have heq : (fun t : ℝ => fderiv ℝ ftilde (φ t) v) = L_v ∘ (fderiv ℝ ftilde) ∘ φ := by
      funext t; rfl
    have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ ftilde) y₀ := by
      have h1 : ContDiffAt ℝ 1 (fderiv ℝ ftilde) y₀ :=
        hf_C2.fderiv_right (m := 1) (by norm_num)
      exact h1.differentiableAt one_ne_zero
    have hfderiv_hasFDeriv : HasFDerivAt (fderiv ℝ ftilde)
        (fderiv ℝ (fderiv ℝ ftilde) y₀) y₀ := hfderiv_diff.hasFDerivAt
    have hφ_hasDeriv : HasDerivAt φ v 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
      simpa using (hasDerivAt_const (0 : ℝ) y₀).add h1
    have h_inner : HasDerivAt ((fderiv ℝ ftilde) ∘ φ)
        ((fderiv ℝ (fderiv ℝ ftilde) y₀) v) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (hl := hfderiv_hasFDeriv)
        (hf := hφ_hasDeriv) (hy := hφ_zero.symm)
    have h_outer : HasDerivAt (L_v ∘ (fderiv ℝ ftilde) ∘ φ)
        (L_v ((fderiv ℝ (fderiv ℝ ftilde) y₀) v)) 0 :=
      HasFDerivAt.comp_hasDerivAt (hl := L_v.hasFDerivAt) (hf := h_inner)
    rw [heq]
    exact h_outer
  rw [h_deriv_deriv_g_eq, h_chain.deriv] at h_g_2nd
  exact h_g_2nd

omit [NeZero (Module.finrank ℝ E)] in
private lemma sndFDeriv_apply_self_eq_sum_of_basis
    {ftilde : E → ℝ} {y₀ : E} (hf_diff : DifferentiableAt ℝ (fderiv ℝ ftilde) y₀)
    (v : E) :
    (fderiv ℝ (fderiv ℝ ftilde) y₀ v) v =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) i *
          ((chartModelBasis E).repr v) j *
          partialDeriv (E := E) i (partialDeriv (E := E) j ftilde) y₀ := by
  classical
  have h_outer_inner : ∀ i j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (partialDeriv (E := E) j ftilde) y₀ =
        (fderiv ℝ (fderiv ℝ ftilde) y₀ ((chartModelBasis E) i))
          ((chartModelBasis E) j) := by
    intros i j
    set L_j : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j) with hLj_def
    have heq : partialDeriv (E := E) j ftilde = L_j ∘ (fderiv ℝ ftilde) := by
      funext y
      rfl
    rw [partialDeriv]
    rw [show (partialDeriv (E := E) j ftilde) = L_j ∘ (fderiv ℝ ftilde) from heq]
    have hcomp_fderiv : fderiv ℝ (L_j ∘ (fderiv ℝ ftilde)) y₀ =
        (fderiv ℝ (L_j) (fderiv ℝ ftilde y₀)).comp
          (fderiv ℝ (fderiv ℝ ftilde) y₀) :=
      fderiv_comp y₀ L_j.differentiableAt hf_diff
    rw [hcomp_fderiv]
    rw [L_j.fderiv]
    rfl
  set b := chartModelBasis E with hb_def
  set B : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ ftilde) y₀ with hB_def
  have hv_decomp : v = ∑ i : Fin (Module.finrank ℝ E),
      ((b.repr v) i) • b i := by
    conv_lhs => rw [← b.linearCombination_repr v]
    simp [Finsupp.linearCombination, Finsupp.sum_fintype]
  have h_bil : B v v =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (b.repr v) i * (b.repr v) j * (B (b i) (b j)) := by
    have step1 : B v = ∑ i : Fin (Module.finrank ℝ E),
        (b.repr v) i • (B (b i)) := by
      conv_lhs => rw [hv_decomp]
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    have step2 : ∀ i : Fin (Module.finrank ℝ E),
        (B (b i)) v = ∑ j : Fin (Module.finrank ℝ E),
          (b.repr v) j • (B (b i)) (b j) := by
      intro i
      conv_lhs => rw [hv_decomp]
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul]
    calc B v v = (∑ i, (b.repr v) i • (B (b i))) v := by
            rw [step1]
      _ = ∑ i, (b.repr v) i • ((B (b i)) v) := by
            rw [ContinuousLinearMap.sum_apply]
            simp only [ContinuousLinearMap.smul_apply]
      _ = ∑ i, (b.repr v) i • (∑ j, (b.repr v) j • (B (b i)) (b j)) := by
            refine Finset.sum_congr rfl ?_
            intros i _
            rw [step2 i]
      _ = ∑ i, ∑ j, (b.repr v) i * (b.repr v) j * (B (b i)) (b j) := by
            refine Finset.sum_congr rfl ?_
            intros i _
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl ?_
            intros j _
            simp only [smul_eq_mul]
            ring
  rw [h_bil]
  refine Finset.sum_congr rfl ?_
  intros i _
  refine Finset.sum_congr rfl ?_
  intros j _
  rw [h_outer_inner i j]

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartHessianTensor_quad_form_nonpos_at_max
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x_max : M} (h_max : ∀ x : M, f x ≤ f x_max)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    ∑ i, ∑ j, c i * c j *
        chartHessianTensor (I := I) g x_max f i j x_max ≤ 0 := by
  classical
  set α : M := x_max with hα_def
  set ftilde : E → ℝ := scalarOnE (I := I) α f with hftilde_def
  set y₀ : E := extChartAt I α x_max with hy₀_def
  have hx_in_src : x_max ∈ (chartAt H α).source := mem_chart_source H α
  have hx_in_extSrc : x_max ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_in_src
  have hx_in_baseSet : x_max ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_in_src
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_in_extSrc
  have h_target_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have hy₀_target_nhds : (extChartAt I α).target ∈ 𝓝 y₀ :=
    h_target_open.mem_nhds hy₀_target
  have hftilde_smooth_on : ContDiffOn ℝ ∞ ftilde (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hftilde_C2_at : ContDiffAt ℝ 2 ftilde y₀ := by
    have h := (hftilde_smooth_on.contDiffAt hy₀_target_nhds)
    refine h.of_le ?_
    have h1 : (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) := by norm_cast
    rw [h1]
    exact_mod_cast (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))
  have hftilde_max : IsLocalMax ftilde y₀ := by
    change ∀ᶠ y in 𝓝 y₀, ftilde y ≤ ftilde y₀
    filter_upwards [hy₀_target_nhds] with y hy_target
    change f ((extChartAt I α).symm y) ≤ ftilde y₀
    have h1 : ftilde y₀ = f x_max := by
      change f ((extChartAt I α).symm y₀) = f x_max
      rw [(extChartAt I α).left_inv hx_in_extSrc]
    rw [h1]
    exact h_max _
  have h_partial_zero : ∀ k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k ftilde y₀ = 0 := by
    intro k
    have hfderiv_zero : fderiv ℝ ftilde y₀ = 0 := hftilde_max.fderiv_eq_zero
    rw [partialDeriv, hfderiv_zero]
    rfl
  have h_hessian_at_max : ∀ i j : Fin (Module.finrank ℝ E),
      chartHessianTensor (I := I) g α f i j x_max =
        chartIteratedPartialDeriv (I := I) α f i j y₀ := by
    intros i j
    rw [chartHessianTensor_def]
    have h_christ_term :
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k (extChartAt I α x_max) *
            partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x_max) =
          0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [show (extChartAt I α x_max) = y₀ from rfl]
      rw [show (scalarOnE (I := I) α f) = ftilde from rfl, h_partial_zero k]
      ring
    rw [h_christ_term, sub_zero]
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  set v : E := ∑ i : Fin (Module.finrank ℝ E), c i • b i with hv_def
  have h_repr_v : ∀ k : Fin (Module.finrank ℝ E), (b.repr v) k = c k := by
    intro k
    rw [hv_def]
    rw [map_sum]
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single k]
    · rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, b.repr_self_apply]
      simp [smul_eq_mul]
    · intros j _ hjk
      rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, b.repr_self_apply]
      have hne : ¬ (j = k) := hjk
      rw [if_neg hne]
      simp
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have h1 : ∑ i, ∑ j, c i * c j *
      chartHessianTensor (I := I) g α f i j x_max =
      ∑ i, ∑ j, (b.repr v) i * (b.repr v) j *
        partialDeriv (E := E) i (partialDeriv (E := E) j ftilde) y₀ := by
    refine Finset.sum_congr rfl ?_
    intros i _
    refine Finset.sum_congr rfl ?_
    intros j _
    rw [h_hessian_at_max i j, h_repr_v i, h_repr_v j]
    rfl
  rw [h1]
  have hftilde_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ ftilde) y₀ := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ ftilde) y₀ :=
      hftilde_C2_at.fderiv_right (m := 1) (by norm_num)
    exact h1.differentiableAt one_ne_zero
  have h2 : ∑ i, ∑ j,
      (b.repr v) i * (b.repr v) j *
        partialDeriv (E := E) i (partialDeriv (E := E) j ftilde) y₀ =
      (fderiv ℝ (fderiv ℝ ftilde) y₀ v) v :=
    (sndFDeriv_apply_self_eq_sum_of_basis hftilde_fderiv_diff v).symm
  rw [h2]
  exact sndFDeriv_apply_self_nonpos_of_isLocalMax hftilde_max hftilde_C2_at v

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacian_nonpos_at_max
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x_max : M} (h_max : ∀ x : M, f x ≤ f x_max) :
    Δ_g (I := I) g hf x_max ≤ 0 := by
  classical
  have h_trace_eq :=
    chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x_max
  rw [← h_trace_eq, chartHessTrace_def]
  set α : M := x_max with hα_def
  set Mmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      chartInvGramMatrix (I := I) g α x_max with hMmat_def
  set Hmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        chartHessianTensor (I := I) g α f i j x_max) with hHmat_def
  have hx_in_baseSet : x_max ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact mem_chart_source H α
  have hG_PD : (chartGramMatrix (I := I) g α x_max).PosDef :=
    chartGramMatrix_posDef (I := I) g α hx_in_baseSet
  have hMmat_PD : Mmat.PosDef := by
    rw [hMmat_def]
    unfold chartInvGramMatrix
    exact hG_PD.inv
  have hMmat_PSD : Mmat.PosSemidef := hMmat_PD.posSemidef
  have hHmat_neg : ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ⬝ᵥ (Hmat *ᵥ v) ≤ 0 := by
    intro v
    have h_expand : v ⬝ᵥ (Hmat *ᵥ v) =
        ∑ i, ∑ j, v i * v j *
          chartHessianTensor (I := I) g α f i j x_max := by
      rw [dotProduct]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Matrix.of_apply, hHmat_def]
      ring
    rw [h_expand]
    exact chartHessianTensor_quad_form_nonpos_at_max (I := I) g hf h_max v
  have h_main := sum_posSemidef_mul_neg_semidef_le_zero hMmat_PSD hHmat_neg
  have h_eq : ∑ i, ∑ j, Mmat i j * Hmat i j =
      ∑ i, ∑ j,
        chartInvGramMatrix (I := I) g α x_max i j *
          chartHessianTensor (I := I) g α f i j x_max := by
    refine Finset.sum_congr rfl ?_
    intros i _
    refine Finset.sum_congr rfl ?_
    intros j _
    simp only [hMmat_def, hHmat_def, Matrix.of_apply]
  rw [← h_eq]
  exact h_main

section MaxPrinciple

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem weak_maximum_principle_of_closed
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (u : ℝ → M → ℝ)
    (hu_smooth : ∀ t : ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hu_cont : ContinuousOn (fun p : ℝ × M => u p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (Du : ℝ → M → ℝ)
    (h_t_diff : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasDerivAt (fun s : ℝ => u s x) (Du t x) t)
    (h_ineq : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      Du t x ≤ Δ_g (I := I) g (hu_smooth t) x)
    (h_init : ∀ x : M, u 0 x ≤ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, u t x ≤ 0 := by
  classical
  have key : ∀ {δ : ℝ}, 0 < δ → ∀ {η : ℝ}, 0 < η → η < T →
      ∀ t ∈ Set.Icc (0 : ℝ) (T - η), ∀ x : M, u t x ≤ δ * (t + 1) := by
    intros δ hδ η hη hηT
    intros t ht x
    set K : Set (ℝ × M) := Set.Icc (0 : ℝ) (T - η) ×ˢ (Set.univ : Set M) with hK_def
    have hK_compact : IsCompact K :=
      (isCompact_Icc (a := (0 : ℝ)) (b := T - η)).prod (CompactSpace.isCompact_univ)
    have hK_nonempty : K.Nonempty :=
      ⟨(t, x), Set.mk_mem_prod ht (Set.mem_univ x)⟩
    have hK_sub : K ⊆ Set.Icc (0 : ℝ) T ×ˢ Set.univ := by
      intro p hp
      refine ⟨?_, hp.2⟩
      refine ⟨hp.1.1, ?_⟩
      exact le_trans hp.1.2 (by linarith)
    set v_δ : ℝ × M → ℝ := fun p => u p.1 p.2 - δ * (p.1 + 1) with hv_def
    have hv_cont : ContinuousOn v_δ K := by
      apply ContinuousOn.sub (hu_cont.mono hK_sub)
      refine continuous_const.continuousOn.mul ?_
      exact (continuous_fst.add continuous_const).continuousOn
    obtain ⟨p₀, hp₀_mem, hp₀_max⟩ := hK_compact.exists_isMaxOn hK_nonempty hv_cont
    suffices h_max_nonpos : v_δ p₀ ≤ 0 by
      have hmem : (t, x) ∈ K := Set.mk_mem_prod ht (Set.mem_univ x)
      have h := hp₀_max hmem
      have : u t x - δ * (t + 1) ≤ 0 := by
        calc u t x - δ * (t + 1)
            = v_δ (t, x) := rfl
          _ ≤ v_δ p₀ := h
          _ ≤ 0 := h_max_nonpos
      linarith
    by_contra h_pos
    push Not at h_pos
    have hp₀_t_pos : 0 < p₀.1 := by
      by_contra h_neg
      push Not at h_neg
      have hp_t_zero : p₀.1 = 0 := le_antisymm h_neg hp₀_mem.1.1
      have hu0 : u 0 p₀.2 ≤ 0 := h_init p₀.2
      have hv_at : v_δ p₀ = u p₀.1 p₀.2 - δ * (p₀.1 + 1) := rfl
      have : v_δ p₀ ≤ -δ := by
        rw [hv_at, hp_t_zero]
        linarith
      linarith
    have hp₀_t_lt_T : p₀.1 < T := lt_of_le_of_lt hp₀_mem.1.2 (by linarith)
    have hp₀_t_Ioo : p₀.1 ∈ Set.Ioo (0 : ℝ) T := ⟨hp₀_t_pos, hp₀_t_lt_T⟩
    have h_spatial_max : ∀ y : M, u p₀.1 y ≤ u p₀.1 p₀.2 := by
      intro y
      have hmem_y : (p₀.1, y) ∈ K := Set.mk_mem_prod hp₀_mem.1 (Set.mem_univ y)
      have h : v_δ (p₀.1, y) ≤ v_δ p₀ := hp₀_max hmem_y
      have hv1 : v_δ (p₀.1, y) = u p₀.1 y - δ * (p₀.1 + 1) := rfl
      have hv2 : v_δ p₀ = u p₀.1 p₀.2 - δ * (p₀.1 + 1) := rfl
      rw [hv1, hv2] at h
      linarith
    have h_laplacian_nonpos :
        Δ_g (I := I) g (hu_smooth p₀.1) p₀.2 ≤ 0 :=
      laplacian_nonpos_at_max (I := I) g (hu_smooth p₀.1) h_spatial_max
    have h_y_in_cone : -(p₀.1 / 2) ∈ posTangentConeAt
        (Set.Icc (0 : ℝ) (T - η)) p₀.1 := by
      have h := mem_posTangentConeAt_of_segment_subset
        (x := p₀.1) (y := -(p₀.1 / 2))
        (s := Set.Icc (0 : ℝ) (T - η)) ?_
      · exact h
      · have h_segment_eq :
            segment ℝ p₀.1 (p₀.1 + -(p₀.1 / 2)) = Set.Icc (p₀.1 / 2) p₀.1 := by
          have h_le : p₀.1 + -(p₀.1 / 2) ≤ p₀.1 := by linarith
          rw [segment_symm]
          rw [segment_eq_Icc h_le]
          congr 1
          ring
        rw [h_segment_eq]
        intro y hy
        refine ⟨by linarith [hy.1, hp₀_t_pos], ?_⟩
        exact le_trans hy.2 hp₀_mem.1.2
    set f : ℝ → ℝ := fun s => u s p₀.2 - δ * (s + 1) with hf_def
    have h_isMaxOn : IsMaxOn f (Set.Icc (0 : ℝ) (T - η)) p₀.1 := by
      intro s hs
      have hmem_s : (s, p₀.2) ∈ K := Set.mk_mem_prod hs (Set.mem_univ p₀.2)
      have h : v_δ (s, p₀.2) ≤ v_δ p₀ := hp₀_max hmem_s
      have hv1 : v_δ (s, p₀.2) = u s p₀.2 - δ * (s + 1) := rfl
      have hv2 : v_δ p₀ = u p₀.1 p₀.2 - δ * (p₀.1 + 1) := rfl
      change f s ≤ f p₀.1
      simp only [hf_def]
      rw [hv1, hv2] at h
      linarith
    have h_isLocalMaxOn : IsLocalMaxOn f (Set.Icc (0 : ℝ) (T - η)) p₀.1 :=
      h_isMaxOn.localize
    have hf_deriv : HasDerivAt f (Du p₀.1 p₀.2 - δ) p₀.1 := by
      have h1 : HasDerivAt (fun s : ℝ => u s p₀.2) (Du p₀.1 p₀.2) p₀.1 :=
        h_t_diff p₀.1 hp₀_t_Ioo p₀.2
      have h2 : HasDerivAt (fun s : ℝ => δ * (s + 1)) δ p₀.1 := by
        have hid : HasDerivAt (fun s : ℝ => s + 1) 1 p₀.1 :=
          (hasDerivAt_id _).add_const 1
        simpa using hid.const_mul δ
      exact h1.sub h2
    have hf_hasFDeriv : HasFDerivAt f
        (ContinuousLinearMap.toSpanSingleton ℝ (Du p₀.1 p₀.2 - δ)) p₀.1 :=
      hf_deriv.hasFDerivAt
    have hf_hasFDerivWithin : HasFDerivWithinAt f
        (ContinuousLinearMap.toSpanSingleton ℝ (Du p₀.1 p₀.2 - δ))
        (Set.Icc (0 : ℝ) (T - η)) p₀.1 :=
      hf_hasFDeriv.hasFDerivWithinAt
    have h_fermat := h_isLocalMaxOn.hasFDerivWithinAt_nonpos
      hf_hasFDerivWithin h_y_in_cone
    have h_eval : (ContinuousLinearMap.toSpanSingleton ℝ (Du p₀.1 p₀.2 - δ))
        (-(p₀.1 / 2)) = (-(p₀.1 / 2)) * (Du p₀.1 p₀.2 - δ) := by
      simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
    rw [h_eval] at h_fermat
    have h_neg_div : -(p₀.1 / 2) < 0 := by linarith
    have h_Du_ge_delta : Du p₀.1 p₀.2 - δ ≥ 0 := by
      by_contra h_lt
      push Not at h_lt
      have h_pos_prod : 0 < -(p₀.1 / 2) * (Du p₀.1 p₀.2 - δ) :=
        mul_pos_of_neg_of_neg h_neg_div h_lt
      linarith
    have h_chain : δ ≤ 0 := by
      have h_Du_le_lap := h_ineq p₀.1 hp₀_t_Ioo p₀.2
      linarith
    linarith
  have step_Ico : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, u t x ≤ 0 := by
    intros t ht x
    have h_ineq_delta : ∀ δ > (0 : ℝ), u t x ≤ δ * (t + 1) := by
      intros δ hδ
      set η := (T - t) / 2 with hη_def
      have hη_pos : 0 < η := by
        have : t < T := ht.2
        linarith
      have hη_lt_T : η < T := by
        have h_t_nonneg : 0 ≤ t := ht.1
        have h_t_lt_T : t < T := ht.2
        have : T - t < 2 * T := by linarith
        have : η < T := by linarith
        exact this
      have h_t_in : t ∈ Set.Icc (0 : ℝ) (T - η) := by
        refine ⟨ht.1, ?_⟩
        have : t = T - (T - t) := by ring
        nlinarith [ht.2]
      exact key hδ hη_pos hη_lt_T t h_t_in x
    have : u t x ≤ 0 := by
      by_contra h_lt
      push Not at h_lt
      have h_t_nonneg : 0 ≤ t := ht.1
      have h_pos : 0 < t + 1 := by linarith
      set δ : ℝ := u t x / (2 * (t + 1)) with hδ_def
      have hδ_pos : 0 < δ := by
        rw [hδ_def]
        positivity
      have h_Δ_eq : δ * (t + 1) = u t x / 2 := by
        rw [hδ_def]
        field_simp
      have h_le : u t x ≤ u t x / 2 := by
        rw [← h_Δ_eq]
        exact h_ineq_delta δ hδ_pos
      linarith
    exact this
  intros t ht x
  rcases eq_or_lt_of_le ht.2 with htT | htT
  · have h_t_eq : t = T := htT
    rw [h_t_eq]
    have hT_in : (T, x) ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M) :=
      ⟨right_mem_Icc.mpr (le_of_lt hT), Set.mem_univ x⟩
    have h_cont_at := hu_cont (T, x) hT_in
    have h_tend : Filter.Tendsto (fun s : ℝ => u s x)
        (𝓝[<] T) (𝓝 (u T x)) := by
      have h_pair : Filter.Tendsto (fun s : ℝ => (s, x))
          (𝓝[<] T) (𝓝 (T, x)) := by
        refine Filter.Tendsto.prodMk_nhds ?_ tendsto_const_nhds
        exact nhdsWithin_le_nhds
      have h_evt : ∀ᶠ s in 𝓝[<] T,
          (s, x) ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M) := by
        have h0 : Set.Ioi (0 : ℝ) ∈ 𝓝 T := Ioi_mem_nhds hT
        have h0' : Set.Ioi (0 : ℝ) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
        filter_upwards [h0', self_mem_nhdsWithin] with s hs hs_lt
        refine ⟨⟨le_of_lt hs, le_of_lt hs_lt⟩, Set.mem_univ x⟩
      have h_pair_within : Filter.Tendsto (fun s : ℝ => (s, x))
          (𝓝[<] T) (𝓝[Set.Icc 0 T ×ˢ Set.univ] (T, x)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨h_pair, h_evt⟩
      exact h_cont_at.tendsto.comp h_pair_within
    have h_evt_le : ∀ᶠ s in 𝓝[<] T, u s x ≤ 0 := by
      have h0 : Set.Ioi (0 : ℝ) ∈ 𝓝 T := Ioi_mem_nhds hT
      have h0' : Set.Ioi (0 : ℝ) ∈ 𝓝[<] T := nhdsWithin_le_nhds h0
      filter_upwards [h0', self_mem_nhdsWithin] with s hs hs_lt
      exact step_Ico s ⟨le_of_lt hs, hs_lt⟩ x
    have h_neBot : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
    exact le_of_tendsto h_tend h_evt_le
  · have h_t_in_Ico : t ∈ Set.Ico (0 : ℝ) T := ⟨ht.1, htT⟩
    exact step_Ico t h_t_in_Ico x

end MaxPrinciple

end HeatEquation
end Analysis
end DifferentialGeometry
