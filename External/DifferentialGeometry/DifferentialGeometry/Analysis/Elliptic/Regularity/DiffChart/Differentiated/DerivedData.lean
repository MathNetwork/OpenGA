import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DerivedChartBilinearH1ComplData

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
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.FChartEffDef
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contDiff_fderiv_apply_single
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
private lemma hasCompactSupport_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma tsupport_fderiv_apply_single_subset_ψ
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma mixed_smooth_classical_partial_swap
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

private lemma integral_chosenSecondPartial_mul_eq_integral_chartPushed_mixed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y * ψ y
        ∂(volume : Measure EuclN) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) y *
          (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
            (EuclideanSpace.single i 1)
        ∂(volume : Measure EuclN) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set ψl : EuclN → ℝ := fun y =>
    (fderiv ℝ ψ y) (EuclideanSpace.single l 1) with hψl_def
  have hψl_smooth : ContDiff ℝ (⊤ : ℕ∞) ψl :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth l
  have hψl_cs : HasCompactSupport ψl :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs l
  have hψl_supp : tsupport ψl ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset_ψ ψ l).trans hψ_supp
  set u_chart : EuclN → ℝ := chartPushed (I := I) (M := M)
    (chartAtlasPOU I M) α
    ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) with hu_chart_def
  have h_u_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u_chart Ω :=
    (laplacianDomainPow_two_chartPushed_memWkp_two_two
      (I := I) (M := M) g α hu_h).memW1p
  set g_i : EuclN → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 i u_chart Ω with hg_i_def
  have h_g_i_isWeakPartial :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i g_i u_chart Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      h_u_chart_memW1p i
  have h_second_eq :
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l g_i Ω := by
    unfold chosenSecondPartialChartPushedU; rfl
  have h_g_i_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 g_i Ω := by
    have h_step := (laplacianDomainPow_two_chartPushed_memWkp_two_two
      (I := I) (M := M) g α hu_h).chosenWeakPartial_mem i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h_step
    exact h_step
  have h_second_isWeakPartial :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l) g_i Ω := by
    rw [h_second_eq]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      h_g_i_memW1p l
  have h_ibp_outer := h_second_isWeakPartial ψ hψ_smooth hψ_cs hψ_supp
  have h_ibp_inner := h_g_i_isWeakPartial ψl hψl_smooth hψl_cs hψl_supp
  have hA_eq : ∫ y in Ω, g_i y * (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, g_i y * ψl y ∂(volume : Measure EuclN) := rfl
  linarith [h_ibp_outer, h_ibp_inner, hA_eq]

omit [NeZero (Module.finrank ℝ E)] in
private lemma integral_chartPushed_mixed_partial_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) y *
          (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
            (EuclideanSpace.single i 1)
        ∂(volume : Measure EuclN) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) y *
          (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) y)
            (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN) := by
  classical
  refine setIntegral_congr_fun
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet)
    (fun y _hy => ?_)
  rw [mixed_smooth_classical_partial_swap (ψ := ψ) hψ_smooth i l y]

private lemma integral_chosenSecondPartial_mul_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y * ψ y
        ∂(volume : Measure EuclN) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i y * ψ y
        ∂(volume : Measure EuclN) := by
  classical
  rw [integral_chosenSecondPartial_mul_eq_integral_chartPushed_mixed
      (I := I) (M := M) g α hu_h i l hψ_smooth hψ_cs hψ_supp]
  rw [integral_chartPushed_mixed_partial_swap (I := I) (M := M) g α u_h i l hψ_smooth]
  rw [← integral_chosenSecondPartial_mul_eq_integral_chartPushed_mixed
      (I := I) (M := M) g α hu_h l i hψ_smooth hψ_cs hψ_supp]

private lemma chosenSecondPartialChartPushedU_locallyIntegrableOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E)) :
    LocallyIntegrableOn
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
      (chartTargetEuclid (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  intro x hx_in
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hΩ_open x hx_in
  set B : Set EuclN := Metric.closedBall x (r / 2) with hB_def
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset : B ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    apply hr_subset
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith [hy, hr_pos]
  have h_memLp : MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
      2 ((volume : Measure EuclN).restrict B) :=
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l hB_compact hB_subset
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI hB_isFin : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
      B (volume : Measure EuclN) :=
    h_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall

theorem chosenSecondPartialChartPushedU_swap_ae
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E)) :
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set d : EuclN → ℝ := fun y =>
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y -
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i y with hd_def
  have h_first_li : LocallyIntegrableOn
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l) Ω
      (volume : Measure EuclN) :=
    chosenSecondPartialChartPushedU_locallyIntegrableOn (I := I) (M := M) g α hu_h i l
  have h_second_li : LocallyIntegrableOn
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i) Ω
      (volume : Measure EuclN) :=
    chosenSecondPartialChartPushedU_locallyIntegrableOn (I := I) (M := M) g α hu_h l i
  have h_d_li : LocallyIntegrableOn d Ω (volume : Measure EuclN) := by
    intro x hx
    obtain ⟨t₁, ht₁_nhd, ht₁_int⟩ := h_first_li x hx
    obtain ⟨t₂, ht₂_nhd, ht₂_int⟩ := h_second_li x hx
    refine ⟨t₁ ∩ t₂, Filter.inter_mem ht₁_nhd ht₂_nhd, ?_⟩
    have h_sub₁ : t₁ ∩ t₂ ⊆ t₁ := Set.inter_subset_left
    have h_sub₂ : t₁ ∩ t₂ ⊆ t₂ := Set.inter_subset_right
    have h1 : IntegrableOn (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
        (t₁ ∩ t₂) (volume : Measure EuclN) :=
      ht₁_int.mono_set h_sub₁
    have h2 : IntegrableOn (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i)
        (t₁ ∩ t₂) (volume : Measure EuclN) :=
      ht₂_int.mono_set h_sub₂
    exact h1.sub h2
  have h_zero : ∀ (ψ : EuclN → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → ∫ y, ψ y • d y ∂(volume : Measure EuclN) = 0 := by
    intro ψ hψ_smooth hψ_cs hψ_supp
    have h_vanish_off_Ω : ∀ y, y ∉ Ω → ψ y • d y = 0 := by
      intro y hy
      have : ψ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_t => hy (hψ_supp hy_t))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_vanish_off_Ω]
    have h_smul_eq : ∀ y : EuclN, ψ y • d y = d y * ψ y := by
      intro y; simp [smul_eq_mul, mul_comm]
    simp_rw [h_smul_eq]
    have h_d_mul : ∀ y : EuclN, d y * ψ y =
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y * ψ y -
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i y * ψ y := by
      intro y; simp [hd_def]; ring
    simp_rw [h_d_mul]
    have h_K : tsupport ψ ⊆ Ω := hψ_supp
    have hK_compact : IsCompact (tsupport ψ) := hψ_cs
    have hK_meas : MeasurableSet (tsupport ψ) := (isClosed_tsupport ψ).measurableSet
    have hK_finite : (volume : Measure EuclN) (tsupport ψ) < ⊤ := hK_compact.measure_lt_top
    haveI hK_isFin : IsFiniteMeasure ((volume : Measure EuclN).restrict (tsupport ψ)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hK_finite
    have int_factor : ∀ (j : Fin (Module.finrank ℝ E)),
        IntegrableOn (fun y =>
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
          Ω (volume : Measure EuclN) := by
      intro j
      have h_memLp_K : MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j)
          2 ((volume : Measure EuclN).restrict (tsupport ψ)) :=
        chosenSecondPartialChartPushedU_locally_memLp (I := I) (M := M) g α hu_h i j
          hK_compact h_K
      have h_int_K : IntegrableOn (chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h i j) (tsupport ψ) (volume : Measure EuclN) :=
        h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_mul_K : IntegrableOn (fun y =>
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y)
          (tsupport ψ) (volume : Measure EuclN) :=
        h_int_K.mul_continuousOn hψ_smooth.continuous.continuousOn hK_compact
      have h_vanish_off_K : ∀ y, y ∉ tsupport ψ →
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y = 0 := by
        intro y hy
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [this]
      have h_eq_ind : (fun y => chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h i j y * ψ y) =
          (tsupport ψ).indicator (fun y => chosenSecondPartialChartPushedU
            (I := I) (M := M) g α u_h i j y * ψ y) := by
        funext y
        by_cases hy : y ∈ tsupport ψ
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy, h_vanish_off_K y hy]
      have h_ind_int : Integrable ((tsupport ψ).indicator (fun y =>
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y * ψ y))
          (volume : Measure EuclN) :=
        (integrable_indicator_iff hK_meas).mpr h_mul_K
      have h_full_int : Integrable (fun y => chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h i j y * ψ y) (volume : Measure EuclN) := by
        rw [h_eq_ind]; exact h_ind_int
      exact h_full_int.restrict
    have int_factor' : ∀ (j : Fin (Module.finrank ℝ E)),
        IntegrableOn (fun y =>
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h j i y * ψ y)
          Ω (volume : Measure EuclN) := by
      intro j
      have h_memLp_K : MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h j i)
          2 ((volume : Measure EuclN).restrict (tsupport ψ)) :=
        chosenSecondPartialChartPushedU_locally_memLp (I := I) (M := M) g α hu_h j i
          hK_compact h_K
      have h_int_K : IntegrableOn (chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h j i) (tsupport ψ) (volume : Measure EuclN) :=
        h_memLp_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_mul_K : IntegrableOn (fun y =>
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h j i y * ψ y)
          (tsupport ψ) (volume : Measure EuclN) :=
        h_int_K.mul_continuousOn hψ_smooth.continuous.continuousOn hK_compact
      have h_vanish_off_K : ∀ y, y ∉ tsupport ψ →
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h j i y * ψ y = 0 := by
        intro y hy
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [this]
      have h_eq_ind : (fun y => chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h j i y * ψ y) =
          (tsupport ψ).indicator (fun y => chosenSecondPartialChartPushedU
            (I := I) (M := M) g α u_h j i y * ψ y) := by
        funext y
        by_cases hy : y ∈ tsupport ψ
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy, h_vanish_off_K y hy]
      have h_ind_int : Integrable ((tsupport ψ).indicator (fun y =>
          chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h j i y * ψ y))
          (volume : Measure EuclN) :=
        (integrable_indicator_iff hK_meas).mpr h_mul_K
      have h_full_int : Integrable (fun y => chosenSecondPartialChartPushedU
          (I := I) (M := M) g α u_h j i y * ψ y) (volume : Measure EuclN) := by
        rw [h_eq_ind]; exact h_ind_int
      exact h_full_int.restrict
    rw [integral_sub (int_factor l) (int_factor' l)]
    rw [integral_chosenSecondPartial_mul_swap (I := I) (M := M) g α hu_h i l
      hψ_smooth hψ_cs hψ_supp]
    ring
  have h_ae_d_zero : ∀ᵐ x ∂(volume : Measure EuclN), x ∈ Ω → d x = 0 :=
    hΩ_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_d_li h_zero
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ_open.measurableSet]
  filter_upwards [h_ae_d_zero] with x hx hx_in
  have : d x = 0 := hx hx_in
  simp [hd_def] at this
  linarith

private noncomputable def derived_u_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : EuclN → ℝ :=
  (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h)).weak_partial l

private noncomputable def derived_f_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : EuclN → ℝ :=
  diffChartForcing (I := I) (M := M) g α l hu_h

private noncomputable def derived_weak_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l

private lemma derived_weak_partial_isWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (derived_weak_partial (I := I) (M := M) g α l hu_h i)
      (derived_u_chart (I := I) (M := M) g α l hu_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold derived_weak_partial derived_u_chart
  have h_swap_ae := chosenSecondPartialChartPushedU_swap_ae
    (I := I) (M := M) g α hu_h i l
  have h_base_eq := chartBilinearH1ComplData_of_laplacianDomain_weak_partial_def
    (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h) l
  rw [h_base_eq]
  have h_bridge :=
    chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
      (I := I) (M := M) g α hu_h l i
  intro φ hφ_smooth hφ_cs hφ_supp
  have h_id_bridge := h_bridge φ hφ_smooth hφ_cs hφ_supp
  have h_ae_integrand : (fun y : EuclN =>
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i y * φ y) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN =>
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y * φ y) := by
    filter_upwards [h_swap_ae.symm] with y hy
    rw [hy]
  have h_integral_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l i y * φ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y * φ y
        ∂(volume : Measure EuclN) :=
    MeasureTheory.integral_congr_ae h_ae_integrand
  rw [h_integral_eq] at h_id_bridge
  exact h_id_bridge

private lemma derived_u_chart_memLp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (derived_u_chart (I := I) (M := M) g α l hu_h) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold derived_u_chart
  rw [chartBilinearH1ComplData_of_laplacianDomain_weak_partial_def
    (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) l]
  exact Lp.memLp _

private lemma derived_f_chart_memLp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (derived_f_chart (I := I) (M := M) g α l hu_h) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold derived_f_chart
  exact diffChartForcing_memLp_two_weighted (I := I) (M := M)
    (g := g) (α := α) (l := l) (u_h := u_h) (hu_h := hu_h)

private lemma derived_weak_partial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (derived_weak_partial (I := I) (M := M) g α l hu_h i) 2
      ((volume : Measure EuclN).restrict K) := by
  unfold derived_weak_partial
  exact chosenSecondPartialChartPushedU_locally_memLp
    (I := I) (M := M) g α hu_h i l hK_compact hK_in

noncomputable def derivedChartBilinearH1ComplData
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_var_id :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                derived_weak_partial (I := I) (M := M) g α l hu_h i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            derived_u_chart (I := I) (M := M) g α l hu_h y * ψ y
          ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            derived_f_chart (I := I) (M := M) g α l hu_h y * ψ y
          ∂(volume : Measure EuclN)) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart := derived_u_chart (I := I) (M := M) g α l hu_h
  f_chart := derived_f_chart (I := I) (M := M) g α l hu_h
  weak_partial := derived_weak_partial (I := I) (M := M) g α l hu_h
  u_chart_memLp_weighted :=
    derived_u_chart_memLp_weighted (I := I) (M := M) g α l hu_h
  f_chart_memLp_weighted :=
    derived_f_chart_memLp_weighted (I := I) (M := M) g α l hu_h
  weak_partial_locally_memLp := fun i _K hK_compact hK_in =>
    derived_weak_partial_locally_memLp (I := I) (M := M) g α l hu_h i
      hK_compact hK_in
  weak_partial_isWeakPartial := fun i =>
    derived_weak_partial_isWeakPartial (I := I) (M := M) g α l hu_h i
  variational_identity := h_var_id

end DerivedChartBilinearH1ComplData
end Laplacian
end Analysis
end DifferentialGeometry

end
