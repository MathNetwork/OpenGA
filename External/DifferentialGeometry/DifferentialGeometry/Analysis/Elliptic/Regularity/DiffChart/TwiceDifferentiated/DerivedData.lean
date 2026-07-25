import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThreeSmooth
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThree
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedData
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TwiceDerivedChartBilinearH1ComplData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThreeSmooth
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplData
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contDiff_fderiv_apply_single_aux
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => fderiv ℝ ψ y) :=
    (contDiff_infty_iff_fderiv.1 hψ).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.comp h_fderiv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma hasCompactSupport_fderiv_apply_single_aux
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma tsupport_fderiv_apply_single_subset_aux
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma mixed_smooth_classical_partial_swap_aux
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i l : Fin (Module.finrank ℝ E)) (x : EuclN) :
    (fderiv ℝ (fun y : EuclN =>
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) x)
        (EuclideanSpace.single i 1) =
      (fderiv ℝ (fun y : EuclN =>
        (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single l 1) := by
  classical
  set f' : EuclN → (EuclN →L[ℝ] ℝ) := fderiv ℝ ψ with hf'_def
  set f'' : EuclN →L[ℝ] (EuclN →L[ℝ] ℝ) := fderiv ℝ f' x with hf''_def
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hf'_diff : Differentiable ℝ f' :=
    (hψ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have h_hasFDerivAt_ψ : ∀ y : EuclN, HasFDerivAt ψ (f' y) y :=
    fun y => (hψ_diff y).hasFDerivAt
  have h_hasFDerivAt_f' : HasFDerivAt f' f'' x := (hf'_diff x).hasFDerivAt
  have h_symm := second_derivative_symmetric (𝕜 := ℝ) (f' := f')
    h_hasFDerivAt_ψ h_hasFDerivAt_f' (EuclideanSpace.single i 1)
    (EuclideanSpace.single l 1)
  have h_apply_e_l : HasFDerivAt
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ)))
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ)))
      (f' x) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).hasFDerivAt
  have h_apply_e_i : HasFDerivAt
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))
      (f' x) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt
  have h_lhs_HasFDerivAt :
      HasFDerivAt (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1))
        ((ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single l (1 : ℝ))).comp f'') x :=
    h_apply_e_l.comp x h_hasFDerivAt_f'
  have h_rhs_HasFDerivAt :
      HasFDerivAt (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single i 1))
        ((ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).comp f'') x :=
    h_apply_e_i.comp x h_hasFDerivAt_f'
  rw [h_lhs_HasFDerivAt.fderiv, h_rhs_HasFDerivAt.fderiv]
  change (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ)))
        (f'' (EuclideanSpace.single i 1)) =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))
        (f'' (EuclideanSpace.single l 1))
  simp only [ContinuousLinearMap.apply_apply]
  exact h_symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integral_chosenSecond_mul_eq_integral_u_mixed_aux
    {u : EuclN → ℝ} {Ω : Set EuclN} (_hΩ_open : IsOpen Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) 2 2 u Ω)
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω) :
    ∫ y in Ω,
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y
        ∂(volume : Measure EuclN) =
    ∫ y in Ω,
        u y *
          (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
            (EuclideanSpace.single i 1)
        ∂(volume : Measure EuclN) := by
  classical
  set ψj : EuclN → ℝ := fun y =>
    (fderiv ℝ ψ y) (EuclideanSpace.single j 1) with hψj_def
  have hψj_smooth : ContDiff ℝ (⊤ : ℕ∞) ψj :=
    contDiff_fderiv_apply_single_aux (ψ := ψ) hψ_smooth j
  have hψj_cs : HasCompactSupport ψj :=
    hasCompactSupport_fderiv_apply_single_aux (ψ := ψ) hψ_cs j
  have hψj_supp : tsupport ψj ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset_aux ψ j).trans hψ_supp
  have h_u_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω := hu.memW1p
  set g_i : EuclN → ℝ :=
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω with hg_i_def
  have h_g_i_isWeakPartial :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i g_i u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem h_u_memW1p i
  have h_g_i_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 g_i Ω := by
    have h_step := hu.chosenWeakPartial_mem i
    rw [MemWkp.one_iff_memW1p] at h_step
    exact h_step
  have h_outer_isWeakPartial :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j g_i Ω) g_i Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem h_g_i_memW1p j
  have h_ibp_outer := h_outer_isWeakPartial ψ hψ_smooth hψ_cs hψ_supp
  have h_ibp_inner := h_g_i_isWeakPartial ψj hψj_smooth hψj_cs hψj_supp
  have hA_eq : ∫ y in Ω, g_i y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, g_i y * ψj y ∂(volume : Measure EuclN) := rfl
  linarith [h_ibp_outer, h_ibp_inner, hA_eq]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integral_u_mixed_partial_swap_aux
    {u : EuclN → ℝ} {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∫ y in Ω,
        u y *
          (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
            (EuclideanSpace.single i 1)
        ∂(volume : Measure EuclN) =
    ∫ y in Ω,
        u y *
          (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) y)
            (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) := by
  classical
  refine setIntegral_congr_fun hΩ_open.measurableSet (fun y _hy => ?_)
  rw [mixed_smooth_classical_partial_swap_aux (ψ := ψ) hψ_smooth i j y]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma integral_chosenSecond_mul_swap_aux
    {u : EuclN → ℝ} {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) 2 2 u Ω)
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ Ω) :
    ∫ y in Ω,
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y
        ∂(volume : Measure EuclN) =
    ∫ y in Ω,
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y
        ∂(volume : Measure EuclN) := by
  classical
  rw [integral_chosenSecond_mul_eq_integral_u_mixed_aux hΩ_open hu i j
      hψ_smooth hψ_cs hψ_supp]
  rw [integral_u_mixed_partial_swap_aux (u := u) hΩ_open i j hψ_smooth]
  rw [← integral_chosenSecond_mul_eq_integral_u_mixed_aux hΩ_open hu j i
      hψ_smooth hψ_cs hψ_supp]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecond_locallyIntegrableOn_of_memWkp_two
    {u : EuclN → ℝ} {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) 2 2 u Ω)
    (i j : Fin (Module.finrank ℝ E)) :
    LocallyIntegrableOn
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) Ω
      (volume : Measure EuclN) := by
  classical
  have h_inner_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω := by
    have h_step := hu.chosenWeakPartial_mem i
    rw [MemWkp.one_iff_memW1p] at h_step
    exact h_step
  have h_outer_memLp :
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) 2
        ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartial'_memLp_of_mem h_inner_memW1p j
  intro x hx
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hΩ_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2) with hB_def
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset : B ⊆ Ω := by
    intro y hy
    apply hr_subset
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith [hy, hr_pos]
  have hB_meas : MeasurableSet B := hB_compact.isClosed.measurableSet
  have h_restrict :
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) 2
        (((volume : Measure EuclN).restrict Ω).restrict B) :=
    h_outer_memLp.restrict B
  have h_double_restrict :
      ((volume : Measure EuclN).restrict Ω).restrict B =
        (volume : Measure EuclN).restrict B := by
    rw [Measure.restrict_restrict hB_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hB_subset
  rw [h_double_restrict] at h_restrict
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI hB_isFin : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) B
      (volume : Measure EuclN) :=
    h_restrict.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartial'_swap_ae_of_memWkp_two
    {u : EuclN → ℝ} {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) 2 2 u Ω)
    (i j : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω =ᵐ[
        (volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω := by
  classical
  set d_fn : EuclN → ℝ := fun y =>
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y -
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y
    with hd_fn_def
  have h_first_li : LocallyIntegrableOn
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) Ω
      (volume : Measure EuclN) :=
    chosenSecond_locallyIntegrableOn_of_memWkp_two hΩ_open hu i j
  have h_second_li : LocallyIntegrableOn
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω) Ω
      (volume : Measure EuclN) :=
    chosenSecond_locallyIntegrableOn_of_memWkp_two hΩ_open hu j i
  have h_d_li : LocallyIntegrableOn d_fn Ω (volume : Measure EuclN) := by
    intro x hx
    obtain ⟨t₁, ht₁_nhd, ht₁_int⟩ := h_first_li x hx
    obtain ⟨t₂, ht₂_nhd, ht₂_int⟩ := h_second_li x hx
    refine ⟨t₁ ∩ t₂, Filter.inter_mem ht₁_nhd ht₂_nhd, ?_⟩
    have h_sub₁ : t₁ ∩ t₂ ⊆ t₁ := Set.inter_subset_left
    have h_sub₂ : t₁ ∩ t₂ ⊆ t₂ := Set.inter_subset_right
    have h1 : IntegrableOn (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω)
        (t₁ ∩ t₂) (volume : Measure EuclN) :=
      ht₁_int.mono_set h_sub₁
    have h2 : IntegrableOn (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω)
        (t₁ ∩ t₂) (volume : Measure EuclN) :=
      ht₂_int.mono_set h_sub₂
    exact h1.sub h2
  have h_zero : ∀ (ψ : EuclN → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → ∫ y, ψ y • d_fn y ∂(volume : Measure EuclN) = 0 := by
    intro ψ hψ_smooth hψ_cs hψ_supp
    have h_vanish_off_Ω : ∀ y, y ∉ Ω → ψ y • d_fn y = 0 := by
      intro y hy
      have : ψ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_t => hy (hψ_supp hy_t))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_vanish_off_Ω]
    have h_smul_eq : ∀ y : EuclN, ψ y • d_fn y = d_fn y * ψ y := by
      intro y; simp [smul_eq_mul, mul_comm]
    simp_rw [h_smul_eq]
    set K : Set EuclN := tsupport ψ with hK_def
    have hK_compact : IsCompact K := hψ_cs
    have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
    have hK_subset : K ⊆ Ω := hψ_supp
    have hK_finite : (volume : Measure EuclN) K < ⊤ := hK_compact.measure_lt_top
    haveI hK_isFin : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hK_finite
    have h_int_first : IntegrableOn (fun y =>
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y)
        Ω (volume : Measure EuclN) := by
      have h_int_on_K : IntegrableOn (fun y =>
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y)
        K (volume : Measure EuclN) := by
        have h_inner_memW1p :
            DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω := by
          have h_step := hu.chosenWeakPartial_mem i
          rw [MemWkp.one_iff_memW1p] at h_step
          exact h_step
        have h_memLp_Ω :
            MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) 2
              ((volume : Measure EuclN).restrict Ω) :=
          chosenWeakPartial'_memLp_of_mem h_inner_memW1p j
        have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
            (volume : Measure EuclN).restrict K := by
          rw [Measure.restrict_restrict hK_meas]
          congr 1
          exact Set.inter_eq_self_of_subset_left hK_subset
        have h_memLp_K : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) 2
            ((volume : Measure EuclN).restrict K) := by
          have := h_memLp_Ω.restrict K
          rw [h_eq] at this
          exact this
        have h_int_K : IntegrableOn
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω) K
            (volume : Measure EuclN) :=
          h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        exact h_int_K.mul_continuousOn hψ_smooth.continuous.continuousOn hK_compact
      have h_vanish_off_K : ∀ y, y ∉ K →
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y = 0 := by
        intro y hy
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [this]
      have h_eq_ind : (fun y =>
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y) =
          K.indicator (fun y =>
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y) := by
        funext y
        by_cases hy : y ∈ K
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy, h_vanish_off_K y hy]
      have h_ind_int : Integrable (K.indicator (fun y =>
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y))
          (volume : Measure EuclN) :=
        (integrable_indicator_iff hK_meas).mpr h_int_on_K
      have h_full_int : Integrable (fun y =>
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y)
            (volume : Measure EuclN) := by
        rw [h_eq_ind]; exact h_ind_int
      exact h_full_int.restrict
    have h_int_second : IntegrableOn (fun y =>
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y)
        Ω (volume : Measure EuclN) := by
      have h_int_on_K : IntegrableOn (fun y =>
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y)
        K (volume : Measure EuclN) := by
        have h_inner_memW1p :
            DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω := by
          have h_step := hu.chosenWeakPartial_mem j
          rw [MemWkp.one_iff_memW1p] at h_step
          exact h_step
        have h_memLp_Ω :
            MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω) 2
              ((volume : Measure EuclN).restrict Ω) :=
          chosenWeakPartial'_memLp_of_mem h_inner_memW1p i
        have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
            (volume : Measure EuclN).restrict K := by
          rw [Measure.restrict_restrict hK_meas]
          congr 1
          exact Set.inter_eq_self_of_subset_left hK_subset
        have h_memLp_K : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω) 2
            ((volume : Measure EuclN).restrict K) := by
          have := h_memLp_Ω.restrict K
          rw [h_eq] at this
          exact this
        have h_int_K : IntegrableOn
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω) K
            (volume : Measure EuclN) :=
          h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        exact h_int_K.mul_continuousOn hψ_smooth.continuous.continuousOn hK_compact
      have h_vanish_off_K : ∀ y, y ∉ K →
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y = 0 := by
        intro y hy
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [this]
      have h_eq_ind : (fun y =>
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y) =
          K.indicator (fun y =>
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y) := by
        funext y
        by_cases hy : y ∈ K
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy, h_vanish_off_K y hy]
      have h_ind_int : Integrable (K.indicator (fun y =>
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y))
          (volume : Measure EuclN) :=
        (integrable_indicator_iff hK_meas).mpr h_int_on_K
      have h_full_int : Integrable (fun y =>
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y)
            (volume : Measure EuclN) := by
        rw [h_eq_ind]; exact h_ind_int
      exact h_full_int.restrict
    have h_d_mul : ∀ y : EuclN, d_fn y * ψ y =
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) Ω y * ψ y -
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j u Ω) Ω y * ψ y := by
      intro y; simp [hd_fn_def]; ring
    simp_rw [h_d_mul]
    rw [integral_sub h_int_first h_int_second]
    rw [integral_chosenSecond_mul_swap_aux hΩ_open hu i j hψ_smooth hψ_cs hψ_supp]
    ring
  have h_ae_d_zero : ∀ᵐ x ∂(volume : Measure EuclN), x ∈ Ω → d_fn x = 0 :=
    hΩ_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_d_li h_zero
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ_open.measurableSet]
  filter_upwards [h_ae_d_zero] with x hx hx_in
  have : d_fn x = 0 := hx hx_in
  simp [hd_fn_def] at this
  linarith

private lemma chartPushedFirstPartial_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) 2 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₁
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h3 :=
    ChartPushedMemWkpThreeSmooth.chartPushed_memWkp_three_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
  exact h3.chosenWeakPartial_mem l₁

theorem chosenWeakPartial_chosenSecondPartialChartPushedU_eq_chosenThirdMixedPartialChartPushedU_ae
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l₁ l₂ : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂)
        (chartTargetEuclid (I := I) (M := M) α) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set f : EuclN → ℝ := chartPushed (I := I) (M := M)
    (chartAtlasPOU I M) α
    ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) with hf_def
  set g_l₁ : EuclN → ℝ :=
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₁ f Ω with hg_l₁_def
  have h_g_l₁_memWkp_2 :
      MemWkp (d := Module.finrank ℝ E) 2 2 g_l₁ Ω :=
    chartPushedFirstPartial_memWkp_two_two (I := I) (M := M) g α hu_h l₁
  have h_swap1 :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂ g_l₁ Ω) Ω =ᵐ[
        (volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i g_l₁ Ω) Ω := by
    have h := chosenWeakPartial'_swap_ae_of_memWkp_two hΩ_open
      h_g_l₁_memWkp_2 l₂ i
    exact h
  have h_second_eq_l₁l₂ :
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂ g_l₁ Ω := by
    unfold chosenSecondPartialChartPushedU
    rfl
  have h_second_eq_l₁i :
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ i =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i g_l₁ Ω := by
    unfold chosenSecondPartialChartPushedU
    rfl
  have h_swap2 :
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ i =ᵐ[
        (volume : Measure EuclN).restrict Ω]
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ :=
    chosenSecondPartialChartPushedU_swap_ae
      (I := I) (M := M) g α hu_h l₁ i
  have h_third_unfold :
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁) Ω := by
    unfold chosenThirdMixedPartialChartPushedU
    rfl
  rw [h_third_unfold]
  rw [h_second_eq_l₁l₂]
  have h_aux : chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i g_l₁ Ω) Ω =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ i) Ω := by
    rw [h_second_eq_l₁i]
  have h_congr := chosenWeakPartial'_ae_congr
    (d := Module.finrank ℝ E) (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ_open h_swap2 l₂
  calc chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂ g_l₁ Ω) Ω
      =ᵐ[(volume : Measure EuclN).restrict Ω]
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i g_l₁ Ω) Ω := h_swap1
    _ = chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂
          (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ i) Ω := h_aux
    _ =ᵐ[(volume : Measure EuclN).restrict Ω]
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂
          (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁) Ω :=
        h_congr

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPulledWeighted_le_volume_on_compact
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        ENNReal.ofReal c • ((volume : Measure EuclN).restrict K) := by
  classical
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, lt_of_lt_of_le hc_min_pos hc_le, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply,
    Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTarget_diff_chartImagePOUTsupport_isOpen (α : M) :
    IsOpen ((chartTargetEuclid (I := I) (M := M) α) \
      chartImagePOUTsupport (I := I) (M := M) α) :=
  (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartTarget_diff_chartImagePOUTsupport_subset
    (α : M) :
    (chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  Set.diff_subset

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_ae_zero_off_inline
    {Ω U : Set EuclN} (hΩ_open : IsOpen Ω) (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ω)
    {f w : EuclN → ℝ}
    (i : Fin (Module.finrank ℝ E))
    (hw_isWeak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i w f Ω)
    (hw_li : LocallyIntegrableOn w U (volume : Measure EuclN))
    (hf_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict U), f y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict U), w y = 0 := by
  classical
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hf_ae_zero_vol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → f y = 0 := by
    rw [← ae_restrict_iff' hU_meas]; exact hf_ae_zero
  have h_target : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → w y = 0 := by
    apply hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw_li
    intro ψ hψ_smooth hψ_cs hψ_supp
    have hψ_supp_Ω : tsupport ψ ⊆ Ω := hψ_supp.trans hU_sub
    have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
    have h_weak := hw_isWeak ψ hψ_smooth hψ_cs hψ_supp_Ω
    have h_f_supp_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1) = 0 := by
      refine (ae_restrict_iff' hΩ_meas).mpr ?_
      filter_upwards [hf_ae_zero_vol] with y hy _hyΩ
      by_cases hy_U : y ∈ U
      · rw [hy hy_U]; ring
      · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
          (isClosed_tsupport _).isOpen_compl
        have h_y_not_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp h)
        have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds h_y_not_supp] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
          have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
          rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
        rw [h_fderiv_zero]; simp
    have h_zero_lhs :
        ∫ y in Ω, f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
          ∂(volume : Measure EuclN) = 0 := by
      rw [MeasureTheory.integral_congr_ae h_f_supp_ae]; simp
    rw [h_zero_lhs] at h_weak
    have h_rhs_zero :
        ∫ y in Ω, w y * ψ y ∂(volume : Measure EuclN) = 0 := by linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • w x = 0 := fun x hx => by
      have hx_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_Ω h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_rhs_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target] with y hy hy_U
  exact hy hy_U

omit [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrableOn_of_memLp_two_chartTarget_inline
    (α : M) {f : EuclN → ℝ}
    (hf : MemLp f 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :
    LocallyIntegrableOn f
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_chartImagePOUTsupport_isOpen (I := I) (M := M) α
  intro x hx
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2) with hB_def
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset_U : B ⊆ (chartTargetEuclid (I := I) (M := M) α) \
      chartImagePOUTsupport (I := I) (M := M) α := by
    intro y hy
    apply hr_subset
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith [hy, hr_pos]
  have hB_subset_Ω : B ⊆ chartTargetEuclid (I := I) (M := M) α :=
    hB_subset_U.trans
      (chartTarget_diff_chartImagePOUTsupport_subset (I := I) (M := M) α)
  have hB_meas : MeasurableSet B := hB_compact.isClosed.measurableSet
  have h_restrict : MemLp f 2
      (((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict B) := hf.restrict B
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict B =
        (volume : Measure EuclN).restrict B := by
    rw [Measure.restrict_restrict hB_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hB_subset_Ω
  rw [h_eq] at h_restrict
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI hB_isFin : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn f B (volume : Measure EuclN) :=
    h_restrict.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α)),
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y = 0 := by
  classical
  have h_diff_meas : MeasurableSet
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartTarget_diff_chartImagePOUTsupport_isOpen (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _
    hy.1 hy.2

private lemma chosenFirstPartial_chartPushed_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α)),
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) y = 0 := by
  classical
  have h_w1p :=
    chartPushed_memW1p_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
  have h_isWeak :=
    chosenWeakPartial'_isWeakPartial_of_mem h_w1p i
  have h_pushed_zero :=
    chartPushed_ae_zero_off_chartImagePOUTsupport (I := I) (M := M) g α u_h
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_chartImagePOUTsupport_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_chartImagePOUTsupport_subset (I := I) (M := M) α
  have h_chosen_memLp := chosenWeakPartial'_memLp_of_mem h_w1p i
  have hw_li := locallyIntegrableOn_of_memLp_two_chartTarget_inline
    (I := I) (M := M) (α := α) (f := _) h_chosen_memLp
  exact weakPartial_ae_zero_off_inline hΩ_open hU_open hU_sub (i := i)
    h_isWeak hw_li h_pushed_zero

private lemma chosenSecondPartial_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α)),
      chosenSecondPartialChartPushedU
        (I := I) (M := M) g α u_h l₁ l₂ y = 0 := by
  classical
  set g_l₁ : EuclN → ℝ :=
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₁
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) with hg_l₁_def
  have h_g_l₁_ae_zero :=
    chosenFirstPartial_chartPushed_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α hu_h l₁
  have h_unfold : chosenSecondPartialChartPushedU
        (I := I) (M := M) g α u_h l₁ l₂ =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l₂ g_l₁
        (chartTargetEuclid (I := I) (M := M) α) := rfl
  rw [h_unfold]
  have h_g_l₁_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 g_l₁
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_step :=
      (laplacianDomainPow_two_chartPushed_memWkp_two_two
        (I := I) (M := M) g α hu_h).chosenWeakPartial_mem l₁
    rw [MemWkp.one_iff_memW1p] at h_step
    exact h_step
  have h_isWeak :=
    chosenWeakPartial'_isWeakPartial_of_mem h_g_l₁_memW1p l₂
  have h_chosen_memLp :=
    chosenWeakPartial'_memLp_of_mem h_g_l₁_memW1p l₂
  have hw_li := locallyIntegrableOn_of_memLp_two_chartTarget_inline
    (I := I) (M := M) (α := α) (f := _) h_chosen_memLp
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_chartImagePOUTsupport_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_chartImagePOUTsupport_subset (I := I) (M := M) α
  exact weakPartial_ae_zero_off_inline hΩ_open hU_open hU_sub (i := l₂)
    h_isWeak hw_li h_g_l₁_ae_zero

private noncomputable def twiceDerived_u_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (u_h : H1Compl (I := I) (M := M) g) : EuclN → ℝ :=
  chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂

private noncomputable def twiceDerived_f_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : EuclN → ℝ :=
  effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h

private noncomputable def twiceDerived_weak_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (u_h : H1Compl (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
    (twiceDerived_u_chart (I := I) (M := M) g α l₁ l₂ u_h)
    (chartTargetEuclid (I := I) (M := M) α)

private lemma twiceDerived_u_chart_memLp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (twiceDerived_u_chart (I := I) (M := M) g α l₁ l₂ u_h) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  unfold twiceDerived_u_chart
  have h_memW1p :=
    chosenSecondPartialChartPushedU_memW1p_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h l₁ l₂
  have h_global : MemLp
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    h_memW1p.1
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_ae_zero_off_K_raw :=
    chosenSecondPartial_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α hu_h l₁ l₂
  have h_ae_zero_off_K :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ K → chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h l₁ l₂ y = 0 := by
    have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      h_open.measurableSet
    have hU_meas : MeasurableSet
        ((chartTargetEuclid (I := I) (M := M) α) \ K) :=
      (chartTarget_diff_chartImagePOUTsupport_isOpen (I := I) (M := M) α).measurableSet
    rw [ae_restrict_iff' hΩ_meas]
    have h_raw_vol := (ae_restrict_iff' hU_meas).mp h_ae_zero_off_K_raw
    filter_upwards [h_raw_vol] with y hy hyΩ hy_notK
    have hy_in_diff : y ∈ (chartTargetEuclid (I := I) (M := M) α) \ K :=
      ⟨hyΩ, hy_notK⟩
    exact hy hy_in_diff
  set u_chart : EuclN → ℝ :=
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ with hu_chart_def
  have h_u_eq_ind :
      u_chart =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)] K.indicator u_chart := by
    filter_upwards [h_ae_zero_off_K] with y hy
    by_cases hy_K : y ∈ K
    · simp [Set.indicator_of_mem hy_K]
    · rw [Set.indicator_of_notMem hy_K, hy hy_K]
  have h_global_K : MemLp u_chart 2
      ((volume : Measure EuclN).restrict K) := by
    have h_restrict := h_global.restrict K
    have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_eq] at h_restrict
    exact h_restrict
  obtain ⟨c, _hc_pos, h_le⟩ :=
    chartPulledWeighted_le_volume_on_compact
      (I := I) (M := M) (g := g) α hK_compact hK_meas hK_in
  have h_u_weighted_K : MemLp u_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict K) :=
    h_global_K.of_measure_le_smul (c := ENNReal.ofReal c)
      ENNReal.ofReal_ne_top h_le
  have h_indicator_memLp_weighted :
      MemLp (K.indicator u_chart) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [memLp_indicator_iff_restrict hK_meas]
    have h_double_restrict :
        ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (chartPulledWeightedMeasure (I := I) g α).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_double_restrict]
    exact h_u_weighted_K
  have h_absCont :
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) := by
    refine Measure.AbsolutelyContinuous.restrict ?_ _
    unfold chartPulledWeightedMeasure
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_u_eq_ind_weighted :
      u_chart =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)] K.indicator u_chart :=
    h_absCont.ae_eq h_u_eq_ind
  exact (memLp_congr_ae h_u_eq_ind_weighted).mpr h_indicator_memLp_weighted

private lemma twiceDerived_f_chart_memLp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (twiceDerived_f_chart (I := I) (M := M) g α l₁ l₂ hu_h) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold twiceDerived_f_chart
  exact fChartEffTwice_memLp_two_weighted (I := I) (M := M)
    (g := g) (α := α) (l₁ := l₁) (l₂ := l₂) (u_h := u_h) (hu_h := hu_h)

private lemma twiceDerived_weak_partial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (twiceDerived_weak_partial (I := I) (M := M) g α l₁ l₂ u_h i) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  unfold twiceDerived_weak_partial twiceDerived_u_chart
  have h_u_memW1p :=
    chosenSecondPartialChartPushedU_memW1p_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h l₁ l₂
  have h_global :
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂)
        (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    chosenWeakPartial'_memLp_of_mem h_u_memW1p i
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

private lemma twiceDerived_weak_partial_isWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (twiceDerived_weak_partial (I := I) (M := M) g α l₁ l₂ u_h i)
      (twiceDerived_u_chart (I := I) (M := M) g α l₁ l₂ u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold twiceDerived_weak_partial twiceDerived_u_chart
  exact chosenWeakPartial'_isWeakPartial_of_mem
    (chosenSecondPartialChartPushedU_memW1p_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h l₁ l₂) i

noncomputable def twiceDerivedChartBilinearH1ComplData
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_twice_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN))
        + (∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
            ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
          ∂(volume : Measure EuclN)) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart := twiceDerived_u_chart (I := I) (M := M) g α l₁ l₂ u_h
  f_chart := twiceDerived_f_chart (I := I) (M := M) g α l₁ l₂ hu_h
  weak_partial := twiceDerived_weak_partial (I := I) (M := M) g α l₁ l₂ u_h
  u_chart_memLp_weighted :=
    twiceDerived_u_chart_memLp_weighted (I := I) (M := M) g α l₁ l₂ hu_h
  f_chart_memLp_weighted :=
    twiceDerived_f_chart_memLp_weighted (I := I) (M := M) g α l₁ l₂ hu_h
  weak_partial_locally_memLp := fun i _K hK_compact hK_in =>
    twiceDerived_weak_partial_locally_memLp (I := I) (M := M) g α l₁ l₂ hu_h i
      hK_compact hK_in
  weak_partial_isWeakPartial := fun i =>
    twiceDerived_weak_partial_isWeakPartial (I := I) (M := M) g α l₁ l₂ hu_h i
  variational_identity := by
    intro ψ hψ hψ_cs hψ_supp
    classical
    have h_in := h_twice_identity ψ hψ hψ_cs hψ_supp
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hK_compact : IsCompact (tsupport ψ) := hψ_cs
    have hK_meas : MeasurableSet (tsupport ψ) :=
      (isClosed_tsupport ψ).measurableSet
    have h_swap_ae := fun i =>
      chosenWeakPartial_chosenSecondPartialChartPushedU_eq_chosenThirdMixedPartialChartPushedU_ae
        (I := I) (M := M) g α hu_h i l₁ l₂
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    have h_lhs_eq :
        (∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) =
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                twiceDerived_weak_partial
                  (I := I) (M := M) g α l₁ l₂ u_h i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_combined : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
          ∀ i : Fin (Module.finrank ℝ E),
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y =
            twiceDerived_weak_partial
              (I := I) (M := M) g α l₁ l₂ u_h i y := by
        rw [ae_all_iff]
        intro i
        have h := (h_swap_ae i).symm
        filter_upwards [h_swap_ae i] with y hy
        unfold twiceDerived_weak_partial twiceDerived_u_chart
        exact hy.symm
      filter_upwards [h_combined] with y hy
      refine Finset.sum_congr rfl ?_
      intro i _hi
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hy i]
    rw [h_lhs_eq] at h_in
    exact h_in

end TwiceDerivedChartBilinearH1ComplData
end Laplacian
end Analysis
end DifferentialGeometry

end
