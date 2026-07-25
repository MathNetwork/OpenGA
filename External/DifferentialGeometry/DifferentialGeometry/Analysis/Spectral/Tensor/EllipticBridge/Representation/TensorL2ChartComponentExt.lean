import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPull


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def smoothFnSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : M → ℝ) (hφ : ContMDiff I (𝓘(ℝ, ℝ)) ∞ φ)
    (S : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => φ x • S.toSection x
      contMDiff_toFun := ContMDiff.smul_section hφ S.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport S.toFun ?_
    rw [Function.mem_support]
    intro hS_zero
    apply hx
    change TensorRSSpace.toModel (φ x • S.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (S.toSection x) = S.toFun x from rfl, hS_zero,
      smul_zero]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma smoothFnSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : M → ℝ) (hφ : ContMDiff I (𝓘(ℝ, ℝ)) ∞ φ)
    (S : SmoothCcTensor g r s) (x : M) :
    (smoothFnSmul (I := I) (M := M) g r s φ hφ S).toSection x =
      φ x • S.toSection x := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartAtlasPOU_finset_sum_eq_one (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) α x) = 1 := by
  classical
  have h_finsum : ∑ᶠ α : M, ((chartAtlasPOU I M) α x) = 1 :=
    (chartAtlasPOU I M).sum_eq_one (Set.mem_univ x)
  have h_supp : Function.support (fun α : M => ((chartAtlasPOU I M) α x)) ⊆
      (chartAtlasPOU_finset (I := I) (M := M) : Set M) := by
    intro α hα
    rw [Function.mem_support] at hα
    rw [Finset.mem_coe, chartAtlasPOU_finset_mem]
    exact ⟨x, hα⟩
  rw [← h_finsum, finsum_eq_sum_of_support_subset _ h_supp]

private def pouSq (x : M) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma contMDiff_pouSq :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞ (pouSq (I := I) (M := M)) := by
  classical
  refine contMDiff_finset_sum (fun α _ => ?_)
  exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).mul
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouSq_pos (x : M) : 0 < pouSq (I := I) (M := M) x := by
  classical
  have h_sum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have h_nonneg : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      0 ≤ ((chartAtlasPOU I M) α x) := fun α _ => (chartAtlasPOU I M).nonneg α x
  have h_sum_lt :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), (0 : ℝ) <
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), ((chartAtlasPOU I M) α x) := by
    rw [Finset.sum_const_zero, h_sum]
    exact zero_lt_one
  obtain ⟨α₀, hα₀_mem, hα₀_pos⟩ :=
    Finset.exists_lt_of_sum_lt h_sum_lt
  refine lt_of_lt_of_le (mul_pos hα₀_pos hα₀_pos) ?_
  refine Finset.single_le_sum (f := fun α : M =>
    ((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x))
    (fun α hα => mul_nonneg (h_nonneg α hα) (h_nonneg α hα)) hα₀_mem

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouSq_ne_zero (x : M) : pouSq (I := I) (M := M) x ≠ 0 :=
  (pouSq_pos (I := I) (M := M) x).ne'

private def pouSqRecip (x : M) : ℝ := (pouSq (I := I) (M := M) x)⁻¹

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma contMDiff_pouSqRecip :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞ (pouSqRecip (I := I) (M := M)) :=
  (contMDiff_pouSq (I := I) (M := M)).inv₀ (pouSq_ne_zero (I := I) (M := M))

private def reconSeed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  smoothFnSmul (I := I) (M := M) g r s
    (pouSqRecip (I := I) (M := M)) (contMDiff_pouSqRecip (I := I) (M := M)) T

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma sum_pouSmul_pouSmul_reconSeed_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        pouSmul (I := I) (M := M) g r s α
          (pouSmul (I := I) (M := M) g r s α
            (reconSeed (I := I) (M := M) g r s T)) = T := by
  classical
  refine SmoothCcTensor.ext (ContMDiffSection.ext (fun x => ?_))
  have h_eval :
      (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection x =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection x := by
    have h_sum_section :
        (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            pouSmul (I := I) (M := M) g r s α
              (pouSmul (I := I) (M := M) g r s α
                (reconSeed (I := I) (M := M) g r s T))).toSection =
          ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            (pouSmul (I := I) (M := M) g r s α
              (pouSmul (I := I) (M := M) g r s α
                (reconSeed (I := I) (M := M) g r s T))).toSection :=
      map_sum (SmoothCcTensor.toSectionAddHom (I := I) (M := M) (g := g)
        (r := r) (s := s)) _ _
    rw [h_sum_section]
    have h_coe : ⇑(∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ⇑(pouSmul (I := I) (M := M) g r s α
            (pouSmul (I := I) (M := M) g r s α
              (reconSeed (I := I) (M := M) g r s T))).toSection :=
      map_sum (ContMDiffSection.coeAddHom I (TensorRSModel r s ℝ E) ∞
        (fun x : M => TensorRSSpace r s I x)) _ _
    have h_eval' := congrFun h_coe x
    rw [Finset.sum_apply] at h_eval'
    exact h_eval'
  rw [h_eval]
  have h_summand : ∀ α : M,
      (pouSmul (I := I) (M := M) g r s α
          (pouSmul (I := I) (M := M) g r s α
            (reconSeed (I := I) (M := M) g r s T))).toSection x =
        (((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x) *
            pouSqRecip (I := I) (M := M) x) • T.toSection x := by
    intro α
    rw [pouSmul_toSection_apply, pouSmul_toSection_apply]
    rw [show (reconSeed (I := I) (M := M) g r s T) =
        smoothFnSmul (I := I) (M := M) g r s
          (pouSqRecip (I := I) (M := M)) (contMDiff_pouSqRecip (I := I) (M := M))
          T from rfl,
      smoothFnSmul_toSection_apply, smul_smul, smul_smul]
  rw [Finset.sum_congr rfl (fun α _ => h_summand α), ← Finset.sum_smul]
  have h_weight :
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          ((chartAtlasPOU I M) α x) * ((chartAtlasPOU I M) α x) *
            pouSqRecip (I := I) (M := M) x = 1 := by
    rw [← Finset.sum_mul]
    change pouSq (I := I) (M := M) x * (pouSq (I := I) (M := M) x)⁻¹ = 1
    exact mul_inv_cancel₀ (pouSq_ne_zero (I := I) (M := M) x)
  rw [h_weight, one_smul]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma inner_pouSmul_eq_zero_of_chartComponent_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (w : TensorL2 r s g)
    (hw : ∀ Q : CompIdx E r s,
      tensorL2ChartComponent (I := I) (M := M) g r s w α Q = 0) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), w⟫_ℝ : ℝ) = 0 := by
  classical
  rw [tensorL2Inner_pouSmul_tensorL2ChartComponent_pull
    (I := I) (M := M) g r s α w Sg hSg]
  have h_each : ∀ Q : CompIdx E r s,
      ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)] 0 := by
    intro Q
    have h0 : ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α] 0 := by
      rw [hw Q]
      exact Lp.coeFn_zero (E := ℝ) (p := 2)
        (μ := chartL2Measure (I := I) (M := M) α)
    exact h0
  have h_integrand_ae :
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                y)) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)] 0 := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        ∀ Q : CompIdx E r s,
          ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [MeasureTheory.ae_all_iff]
      intro Q
      filter_upwards [h_each Q] with y hy using hy
    filter_upwards [h_all] with y hy
    change densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
              y) = 0
    have h_sum_zero :
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s w α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
              y) = 0 := by
      refine Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ => ?_))
      rw [hy Q, mul_zero]
    rw [h_sum_zero, mul_zero]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  rw [setIntegral_congr_ae hctE_meas
    ((ae_restrict_iff' hctE_meas).mp h_integrand_ae)]
  exact integral_zero EuclN ℝ

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2_eq_zero_of_chartComponent_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (w : TensorL2 r s g)
    (hw : ∀ (α : M) (Q : CompIdx E r s),
      tensorL2ChartComponent (I := I) (M := M) g r s w α Q = 0) :
    w = 0 := by
  classical
  refine inner_self_eq_zero (𝕜 := ℝ) |>.mp ?_
  have h_dense : DenseRange ((↑) :
      SmoothCcTensor g r s → UniformSpace.Completion (SmoothCcTensor g r s)) :=
    UniformSpace.Completion.denseRange_coe
  have h_on_smooth : ∀ T : SmoothCcTensor g r s,
      (⟪w, (T : TensorL2 r s g)⟫_ℝ : ℝ) = 0 := by
    intro T
    have h_recon :
        (T : TensorL2 r s g) =
          ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            ((pouSmul (I := I) (M := M) g r s α
              (pouSmul (I := I) (M := M) g r s α
                (reconSeed (I := I) (M := M) g r s T))) : TensorL2 r s g) := by
      have h_map := map_sum
        (UniformSpace.Completion.toComplL :
          SmoothCcTensor g r s →L[ℝ] TensorL2 r s g)
        (fun α : M => pouSmul (I := I) (M := M) g r s α
          (pouSmul (I := I) (M := M) g r s α
            (reconSeed (I := I) (M := M) g r s T)))
        (chartAtlasPOU_finset (I := I) (M := M))
      rw [sum_pouSmul_pouSmul_reconSeed_eq (I := I) (M := M) g r s T] at h_map
      rw [show ((T : TensorL2 r s g)) =
          (UniformSpace.Completion.toComplL :
            SmoothCcTensor g r s →L[ℝ] TensorL2 r s g) T from rfl, h_map]
      rfl
    rw [h_recon, inner_sum]
    refine Finset.sum_eq_zero (fun α _ => ?_)
    have hSg : tsupport
        (pouSmul (I := I) (M := M) g r s α
          (reconSeed (I := I) (M := M) g r s T)).toFun ⊆ (chartAt H α).source :=
      pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α
        (reconSeed (I := I) (M := M) g r s T)
    rw [real_inner_comm]
    exact inner_pouSmul_eq_zero_of_chartComponent_eq_zero
      (I := I) (M := M) g r s α
      (pouSmul (I := I) (M := M) g r s α (reconSeed (I := I) (M := M) g r s T))
      hSg w (fun Q => hw α Q)
  have h_zero : (fun x : TensorL2 r s g => (⟪w, x⟫_ℝ : ℝ)) =
      (fun _ : TensorL2 r s g => (0 : ℝ)) := by
    refine h_dense.equalizer ?_ continuous_const ?_
    · exact (innerSL ℝ w).continuous
    · funext T
      exact h_on_smooth T
  exact congrFun h_zero w

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2_eq_of_chartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u v : TensorL2 r s g)
    (h : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ =
      tensorL2ChartComponent (I := I) (M := M) g r s v α P₀) :
    u = v := by
  classical
  rw [← sub_eq_zero]
  refine tensorL2_eq_zero_of_chartComponent_eq_zero (I := I) (M := M)
    g r s (u - v) (fun α P₀ => ?_)
  rw [← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀,
    map_sub, tensorL2ChartComponentCLM_apply, tensorL2ChartComponentCLM_apply,
    h α P₀, sub_self]

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (u v : TensorL2 r s g)
    (h : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s),
      tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ =
      tensorL2ChartComponent (I := I) (M := M) g r s v α P₀) :
    u = v :=
  tensorL2_eq_of_chartComponent_eq (I := I) (M := M) g r s u v h

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
