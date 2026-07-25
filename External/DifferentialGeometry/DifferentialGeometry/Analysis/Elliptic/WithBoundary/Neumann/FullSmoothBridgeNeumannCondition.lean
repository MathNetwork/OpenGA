import DifferentialGeometry.Analysis.Elliptic.WithBoundary.Neumann.FullH1Compl
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.Neumann.FullSmoothBridgeInteriorSupport
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.GreenFull
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.BoundaryContribution.SurfaceIntegralIdentification


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [CompactSpace M] in
private lemma localDivergenceWithin_mul_pou_continuous
    (g : SmoothRiemannianMetric (I_half n) M) (α : M)
    (X : Cₛ^∞⟮(I_half n); EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    Continuous (fun x : M => localDivergenceWithin (I := I_half n) g α X x *
      ((chartAtlasPOU (I_half n) M) α : M → ℝ) x) := by
  classical
  set ρ : SmoothPartitionOfUnity M (I_half n) M (univ : Set M) :=
    chartAtlasPOU (I_half n) M with hρ_def
  have hρsub : ρ.IsSubordinate
      (fun α : M => (chartAt (EuclideanHalfSpace n) α).source) :=
    chartAtlasPOU_isSubordinate (I_half n) M
  have hsupp_each : tsupport ((ρ α : M → ℝ)) ⊆
      (chartAt (EuclideanHalfSpace n) α).source := hρsub α
  have hα_cont_on_source : ContinuousOn
      (localDivergenceWithin (I := I_half n) g α X)
      (chartAt (EuclideanHalfSpace n) α).source :=
    localDivergenceWithin_continuousOn (I := I_half n) g α X
  have hρα_cont : Continuous ((ρ α : M → ℝ)) := (ρ α).contMDiff.continuous
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source
  · have h_locDiv_at : ContinuousAt
        (localDivergenceWithin (I := I_half n) g α X) x :=
      (hα_cont_on_source x hx).continuousAt
        ((chartAt (EuclideanHalfSpace n) α).open_source.mem_nhds hx)
    exact h_locDiv_at.mul hρα_cont.continuousAt
  · have hx_nots : x ∉ tsupport ((ρ α : M → ℝ)) :=
      fun h => hx (hsupp_each h)
    have h_open : IsOpen (tsupport ((ρ α : M → ℝ)))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have hev : (fun y : M => localDivergenceWithin (I := I_half n) g α X y *
          (ρ α : M → ℝ) y) =ᶠ[nhds x] (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_nots] with y hy
      have hρy : (ρ α : M → ℝ) y = 0 := by
        by_contra hne
        exact hy (subset_tsupport _ hne)
      change localDivergenceWithin (I := I_half n) g α X y *
        (ρ α : M → ℝ) y = 0
      rw [hρy, mul_zero]
    exact (continuousAt_const (y := (0 : ℝ))).congr hev.symm

noncomputable def divergence_g_with_boundary_pou
    (g : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮(I_half n); EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) : M → ℝ :=
  fun x => ∑ α ∈ chartAtlasPOU_finset (I := I_half n) (M := M),
    localDivergenceWithin (I := I_half n) g α X x *
      ((chartAtlasPOU (I_half n) M) α : M → ℝ) x

lemma divergence_g_with_boundary_pou_continuous
    (g : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮(I_half n); EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    Continuous (divergence_g_with_boundary_pou (n := n) (M := M) g X) := by
  classical
  unfold divergence_g_with_boundary_pou
  exact continuous_finset_sum _ (fun α _ =>
    localDivergenceWithin_mul_pou_continuous (n := n) (M := M) g α X)

omit [CompactSpace M] in
private lemma divergence_g_with_boundary_mul_pou_chart_local_ae
    (g : SmoothRiemannianMetric (I_half n) M) (α : M)
    (X : Cₛ^∞⟮(I_half n); EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    (fun x : M => divergence_g_with_boundary (I := I_half n) g X x *
        ((chartAtlasPOU (I_half n) M) α : M → ℝ) x)
      =ᵐ[chartLocalMeasure (I := I_half n) g α]
      (fun x : M => localDivergenceWithin (I := I_half n) g α X x *
        ((chartAtlasPOU (I_half n) M) α : M → ℝ) x) := by
  classical
  set ρ : SmoothPartitionOfUnity M (I_half n) M (univ : Set M) :=
    chartAtlasPOU (I_half n) M with hρ_def
  have hρsub : ρ.IsSubordinate
      (fun α : M => (chartAt (EuclideanHalfSpace n) α).source) :=
    chartAtlasPOU_isSubordinate (I_half n) M
  have hsupp_each : tsupport ((ρ α : M → ℝ)) ⊆
      (chartAt (EuclideanHalfSpace n) α).source := hρsub α
  set bad : Set M := (chartAt (EuclideanHalfSpace n) α).source ∩
    (I_half n).boundary M with hbad_def
  have h_bad_measzero :
      chartLocalMeasure (I := I_half n) g α bad = 0 :=
    chartLocalMeasure_chart_boundary_zero (I := I_half n) g α
  refine MeasureTheory.ae_iff.mpr ?_
  apply MeasureTheory.measure_mono_null _ h_bad_measzero
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_cases hx_chart : x ∈ (chartAt (EuclideanHalfSpace n) α).source
  · by_cases hx_int : x ∈ (I_half n).interior M
    · exfalso; apply hx
      have hd_eq : divergence_g_with_boundary (I := I_half n) g X x =
          localDivergenceWithin (I := I_half n) g α X x :=
        voss_weyl_divergence_with_boundary_formula
          (I := I_half n) g α X hx_chart hx_int
      rw [hd_eq]
    · refine ⟨hx_chart, ?_⟩
      rw [← (I_half n).compl_interior]
      exact hx_int
  · exfalso; apply hx
    have hx_nots : x ∉ tsupport ((ρ α : M → ℝ)) :=
      fun h => hx_chart (hsupp_each h)
    have hρ_zero : ((chartAtlasPOU (I_half n) M) α : M → ℝ) x = 0 := by
      by_contra hne
      exact hx_nots (subset_tsupport _ hne)
    rw [hρ_zero, mul_zero, mul_zero]

lemma divergence_g_with_boundary_ae_pou
    (g : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮(I_half n); EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯) :
    (fun x : M => divergence_g_with_boundary (I := I_half n) g X x)
      =ᵐ[riemannianVolumeMeasure (I := I_half n) (M := M) g]
      divergence_g_with_boundary_pou (n := n) (M := M) g X := by
  classical
  set ρ : SmoothPartitionOfUnity M (I_half n) M (univ : Set M) :=
    chartAtlasPOU (I_half n) M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I_half n) (M := M) with hS_def
  have hVol_eq :
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        ∑ α ∈ S,
          (chartLocalMeasure (I := I_half n) g α).withDensity
            (fun x : M => ENNReal.ofReal ((ρ α : M → ℝ) x)) := by
    rw [hS_def]; exact riemannianVolumeMeasure_eq_finset_sum (I := I_half n) (M := M) g
  refine (Filter.EventuallyEq.refl _ _).trans ?_
  show (fun x : M => divergence_g_with_boundary (I := I_half n) g X x)
      =ᵐ[riemannianVolumeMeasure (I := I_half n) (M := M) g]
      divergence_g_with_boundary_pou (n := n) (M := M) g X
  rw [hVol_eq]
  rw [Filter.EventuallyEq, ae_finsetSum_measure_iff]
  intro α _hα
  have hρα_meas : Measurable
      (fun y : M => ENNReal.ofReal ((ρ α : M → ℝ) y)) :=
    ENNReal.measurable_ofReal.comp (ρ α).contMDiff.continuous.measurable
  rw [ae_withDensity_iff hρα_meas]
  have hae_per_α :
      (fun x : M => divergence_g_with_boundary (I := I_half n) g X x *
          ((chartAtlasPOU (I_half n) M) α : M → ℝ) x)
        =ᵐ[chartLocalMeasure (I := I_half n) g α]
        (fun x : M => localDivergenceWithin (I := I_half n) g α X x *
          ((chartAtlasPOU (I_half n) M) α : M → ℝ) x) :=
    divergence_g_with_boundary_mul_pou_chart_local_ae (n := n) (M := M) g α X
  have hsupp_each :
      tsupport ((ρ α : M → ℝ)) ⊆
        (chartAt (EuclideanHalfSpace n) α).source := by
    have hρsub : ρ.IsSubordinate
        (fun α : M => (chartAt (EuclideanHalfSpace n) α).source) :=
      chartAtlasPOU_isSubordinate (I_half n) M
    exact hρsub α
  set bad : Set M := (chartAt (EuclideanHalfSpace n) α).source ∩
    (I_half n).boundary M with hbad_def
  have h_bad_measzero :
      chartLocalMeasure (I := I_half n) g α bad = 0 :=
    chartLocalMeasure_chart_boundary_zero (I := I_half n) g α
  refine MeasureTheory.ae_iff.mpr ?_
  apply MeasureTheory.measure_mono_null _ h_bad_measzero
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  rw [Classical.not_imp] at hx
  obtain ⟨hρne, hne⟩ := hx
  by_cases hx_chart : x ∈ (chartAt (EuclideanHalfSpace n) α).source
  · by_cases hx_int : x ∈ (I_half n).interior M
    · exfalso
      apply hne
      unfold divergence_g_with_boundary_pou
      have h_sum_collapse : ∑ β ∈ S,
            localDivergenceWithin (I := I_half n) g β X x *
              ((chartAtlasPOU (I_half n) M) β : M → ℝ) x =
            divergence_g_with_boundary (I := I_half n) g X x := by
        have h_each : ∀ β ∈ S,
            localDivergenceWithin (I := I_half n) g β X x *
              ((chartAtlasPOU (I_half n) M) β : M → ℝ) x =
            divergence_g_with_boundary (I := I_half n) g X x *
              ((chartAtlasPOU (I_half n) M) β : M → ℝ) x := by
          intro β _hβ
          by_cases hβ_supp : ((chartAtlasPOU (I_half n) M) β : M → ℝ) x = 0
          · rw [hβ_supp, mul_zero, mul_zero]
          · have hx_in_supp : x ∈ tsupport ((ρ β : M → ℝ)) :=
              subset_tsupport _ hβ_supp
            have hβsub : ρ.IsSubordinate
                (fun β : M => (chartAt (EuclideanHalfSpace n) β).source) :=
              chartAtlasPOU_isSubordinate (I_half n) M
            have hx_chart_β : x ∈ (chartAt (EuclideanHalfSpace n) β).source :=
              hβsub β hx_in_supp
            have hd_eq :
                divergence_g_with_boundary (I := I_half n) g X x =
                  localDivergenceWithin (I := I_half n) g β X x :=
              voss_weyl_divergence_with_boundary_formula
                (I := I_half n) g β X hx_chart_β hx_int
            rw [hd_eq]
        rw [Finset.sum_congr rfl h_each]
        rw [← Finset.mul_sum]
        have h_supp_subset :
            Function.support (fun β : M => (ρ β : M → ℝ) x) ⊆ (S : Set M) := by
          intro β hβ
          by_contra hβS
          have hzero :
              ((chartAtlasPOU (I_half n) M) β : M → ℝ) x = 0 :=
            chartAtlasPOU_weight_zero_of_notMem
              (I := I_half n) (M := M) hβS x
          exact hβ hzero
        have h_finsum_eq_sum :
            (∑ᶠ β : M, (ρ β : M → ℝ) x) =
              ∑ β ∈ S, (ρ β : M → ℝ) x :=
          finsum_eq_sum_of_support_subset _ h_supp_subset
        have h_sum_one : (∑ᶠ β : M, (ρ β : M → ℝ) x) = 1 :=
          ρ.sum_eq_one (Set.mem_univ x)
        rw [← h_finsum_eq_sum, h_sum_one, mul_one]
      exact h_sum_collapse.symm
    · refine ⟨hx_chart, ?_⟩
      rw [← (I_half n).compl_interior]
      exact hx_int
  · exfalso
    apply hρne
    have hx_nots : x ∉ tsupport ((ρ α : M → ℝ)) :=
      fun h => hx_chart (hsupp_each h)
    have hρ_zero : ((chartAtlasPOU (I_half n) M) α : M → ℝ) x = 0 := by
      by_contra hne'
      exact hx_nots (subset_tsupport _ hne')
    rw [hρ_zero]
    simp

noncomputable def FullSmoothScalar.oneSubLapClassicalRep
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g) : M → ℝ :=
  fun x => u.toFun x -
    divergence_g_with_boundary_pou (n := n) (M := M) g
      (grad_g_full_section (M := M) (n := n) g u.smooth) x

lemma FullSmoothScalar.oneSubLapClassicalRep_continuous
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g) :
    Continuous (u.oneSubLapClassicalRep) := by
  unfold FullSmoothScalar.oneSubLapClassicalRep
  exact u.smooth.continuous.sub
    (divergence_g_with_boundary_pou_continuous (n := n) (M := M) g
      (grad_g_full_section (M := M) (n := n) g u.smooth))

lemma FullSmoothScalar.oneSubLapClassicalRep_memLp
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g) :
    MemLp u.oneSubLapClassicalRep 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact u.oneSubLapClassicalRep_continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def FullSmoothScalar.oneSubLapClassicalLp
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  u.oneSubLapClassicalRep_memLp.toLp _

lemma FullSmoothScalar.coeFn_oneSubLapClassicalLp
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g) :
    (u.oneSubLapClassicalLp :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
      u.oneSubLapClassicalRep :=
  MemLp.coeFn_toLp u.oneSubLapClassicalRep_memLp

lemma FullSmoothScalar.oneSubLapClassicalLp_ae_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M} (u : FullSmoothScalar g) :
    (u.oneSubLapClassicalLp :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
      (fun x : M => u.toFun x - Δ_g_classical (M := M) (n := n) g u.smooth x) := by
  have hcoe := u.coeFn_oneSubLapClassicalLp
  have hpou := divergence_g_with_boundary_ae_pou (n := n) (M := M) g
    (grad_g_full_section (M := M) (n := n) g u.smooth)
  filter_upwards [hcoe, hpou] with x hcoe_x hpou_x
  rw [hcoe_x]
  change u.toFun x -
      divergence_g_with_boundary_pou (n := n) (M := M) g
        (grad_g_full_section (M := M) (n := n) g u.smooth) x =
      u.toFun x - Δ_g_classical (M := M) (n := n) g u.smooth x
  rw [show Δ_g_classical (M := M) (n := n) g u.smooth x =
      divergence_g_with_boundary (I := I_half n) g
        (grad_g_full_section (M := M) (n := n) g u.smooth) x from rfl]
  rw [hpou_x]

theorem fullSmoothScalarH1Inner_eq_integral_oneSubLapClassical_mul_neumann
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : FullSmoothScalar g)
    (h_neumann : ∀ x : (I_half n).boundary M,
      g.inner x.val
        (outwardNormal (I := I_half n) (M := M) g x :
          TangentSpace _ x.val)
        (gradFun (I := I_half n) g u.toFun x.val) = 0)
    (h_chart_iden : ∀ α ∈ chartAtlasPOU_finset
        (I := I_half n) (M := M),
      chartFaceIntegralEqualsSurfaceIntegralOnChart (n := n) (M := M)
        g α
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (grad_g_full_section (M := M) (n := n) g u.smooth))
        ((chartAtlasPOU (I_half n) M) α : M → ℝ))
    (h_int : Integrable
      (fun b : BoundaryManifold (I_half n) M =>
        g.inner b.val
          (outwardNormal
              (I := I_half n) (M := M) g b :
            TangentSpace _ b.val)
          ((smoothSmul (I := I_half n) v.toFun v.smooth
              (grad_g_full_section (M := M) (n := n) g u.smooth)) b.val))
      (surfaceMeasure
        (I := I_half n) (M := M) g)) :
    fullSmoothScalarH1Inner u v =
      ∫ x, (u.toFun x -
              Δ_g_classical (M := M) (n := n) g u.smooth x) *
            v.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  classical
  haveI : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) g
  have h_green :=
    green_first_eq_boundary_surface_integral (M := M) (n := n) g v.smooth u.smooth h_chart_iden h_int
  have h_bdy_zero : ∀ x : (I_half n).boundary M,
      v.toFun x.val *
        g.inner x.val
          (outwardNormal (I := I_half n) (M := M) g x :
            TangentSpace _ x.val)
          (gradFun (I := I_half n) g u.toFun x.val) = 0 := by
    intro x
    rw [h_neumann x, mul_zero]
  have h_bdy_int_zero :
      ∫ x : (I_half n).boundary M,
          v.toFun x.val *
            g.inner x.val
              (outwardNormal (I := I_half n) (M := M) g x :
                TangentSpace _ x.val)
              (gradFun (I := I_half n) g u.toFun x.val)
        ∂(surfaceMeasure (I := I_half n) (M := M) g) = 0 := by
    rw [show (fun x : (I_half n).boundary M =>
        v.toFun x.val *
          g.inner x.val
            (outwardNormal (I := I_half n) (M := M) g x :
              TangentSpace _ x.val)
            (gradFun (I := I_half n) g u.toFun x.val)) =
        (fun _ : (I_half n).boundary M => (0 : ℝ)) from funext h_bdy_zero]
    exact integral_zero _ _
  rw [h_bdy_int_zero] at h_green
  have h_symm : ∀ x : M,
      g.inner x (gradFun (I := I_half n) g v.toFun x)
        (gradFun (I := I_half n) g u.toFun x) =
        g.inner x (gradFun (I := I_half n) g u.toFun x)
          (gradFun (I := I_half n) g v.toFun x) := by
    intro x; exact g.symm x _ _
  have h_int_symm :
      ∫ x, g.inner x (gradFun (I := I_half n) g v.toFun x)
            (gradFun (I := I_half n) g u.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        ∫ x, g.inner x (gradFun (I := I_half n) g u.toFun x)
              (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall h_symm)
  rw [h_int_symm] at h_green
  have h_grad_eq :
      ∫ x, g.inner x (gradFun (I := I_half n) g u.toFun x)
            (gradFun (I := I_half n) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) =
        -∫ x, v.toFun x *
              Δ_g_classical (M := M) (n := n) g u.smooth x
            ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    linarith
  unfold fullSmoothScalarH1Inner
  have hu_cont : Continuous u.toFun := u.smooth.continuous
  have hv_cont : Continuous v.toFun := v.smooth.continuous
  have h_uv_int : Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hΔu_pou_cont : Continuous
      (divergence_g_with_boundary_pou (n := n) (M := M) g
        (grad_g_full_section (M := M) (n := n) g u.smooth)) :=
    divergence_g_with_boundary_pou_continuous (n := n) (M := M) g _
  have hvΔu_pou_int : Integrable
      (fun x : M => v.toFun x *
        divergence_g_with_boundary_pou (n := n) (M := M) g
          (grad_g_full_section (M := M) (n := n) g u.smooth) x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    (hv_cont.mul hΔu_pou_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpou_ae :
      (fun x : M => Δ_g_classical (M := M) (n := n) g u.smooth x)
        =ᵐ[riemannianVolumeMeasure (I := I_half n) (M := M) g]
      divergence_g_with_boundary_pou (n := n) (M := M) g
        (grad_g_full_section (M := M) (n := n) g u.smooth) :=
    divergence_g_with_boundary_ae_pou (n := n) (M := M) g _
  have hvΔu_int : Integrable
      (fun x : M => v.toFun x *
        Δ_g_classical (M := M) (n := n) g u.smooth x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
    refine hvΔu_pou_int.congr ?_
    filter_upwards [hpou_ae] with x hx
    rw [hx]
  have hpt : ∀ x : M,
      (u.toFun x -
          Δ_g_classical (M := M) (n := n) g u.smooth x) *
          v.toFun x =
        u.toFun x * v.toFun x -
          v.toFun x *
            Δ_g_classical (M := M) (n := n) g u.smooth x := by
    intro x; ring
  rw [show (fun x : M =>
        (u.toFun x -
          Δ_g_classical (M := M) (n := n) g u.smooth x) *
          v.toFun x) =
      (fun x : M =>
          u.toFun x * v.toFun x -
            v.toFun x *
              Δ_g_classical (M := M) (n := n) g u.smooth x)
      from funext hpt]
  rw [integral_sub h_uv_int hvΔu_int]
  rw [h_grad_eq]
  ring

theorem fullSmoothScalarH1Inner_eq_lpInner_oneSubLapClassical_neumann
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : FullSmoothScalar g)
    (h_neumann : ∀ x : (I_half n).boundary M,
      g.inner x.val
        (outwardNormal (I := I_half n) (M := M) g x :
          TangentSpace _ x.val)
        (gradFun (I := I_half n) g u.toFun x.val) = 0)
    (h_chart_iden : ∀ α ∈ chartAtlasPOU_finset
        (I := I_half n) (M := M),
      chartFaceIntegralEqualsSurfaceIntegralOnChart (n := n) (M := M)
        g α
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (grad_g_full_section (M := M) (n := n) g u.smooth))
        ((chartAtlasPOU (I_half n) M) α : M → ℝ))
    (h_int : Integrable
      (fun b : BoundaryManifold (I_half n) M =>
        g.inner b.val
          (outwardNormal
              (I := I_half n) (M := M) g b :
            TangentSpace _ b.val)
          ((smoothSmul (I := I_half n) v.toFun v.smooth
              (grad_g_full_section (M := M) (n := n) g u.smooth)) b.val))
      (surfaceMeasure
        (I := I_half n) (M := M) g)) :
    fullSmoothScalarH1Inner u v =
      ⟪u.oneSubLapClassicalLp, smoothToLpFullNeumann g v⟫_ℝ := by
  rw [fullSmoothScalarH1Inner_eq_integral_oneSubLapClassical_mul_neumann
    (u := u) (v := v) h_neumann h_chart_iden h_int]
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)]
  have hae_lhs := u.oneSubLapClassicalLp_ae_oneSubLap
  have hae_rhs : (smoothToLpFullNeumann g v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
        v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine integral_congr_ae ?_
  filter_upwards [hae_lhs, hae_rhs] with x hl hr
  rw [hl, hr]
  show (u.toFun x -
        Δ_g_classical (M := M) (n := n) g u.smooth x) * v.toFun x = _
  rw [show @inner ℝ _ _
        (u.toFun x -
            Δ_g_classical (M := M) (n := n) g u.smooth x)
        (v.toFun x) =
      v.toFun x *
        (u.toFun x -
            Δ_g_classical (M := M) (n := n) g u.smooth x)
      from RCLike.inner_apply _ _]
  ring

theorem fullSmoothScalar_bilin_eq_lpFunctional_smooth_neumann
    {g : SmoothRiemannianMetric (I_half n) M}
    (u v : FullSmoothScalar g)
    (h_neumann : ∀ x : (I_half n).boundary M,
      g.inner x.val
        (outwardNormal (I := I_half n) (M := M) g x :
          TangentSpace _ x.val)
        (gradFun (I := I_half n) g u.toFun x.val) = 0)
    (h_chart_iden : ∀ α ∈ chartAtlasPOU_finset
        (I := I_half n) (M := M),
      chartFaceIntegralEqualsSurfaceIntegralOnChart (n := n) (M := M)
        g α
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (grad_g_full_section (M := M) (n := n) g u.smooth))
        ((chartAtlasPOU (I_half n) M) α : M → ℝ))
    (h_int : Integrable
      (fun b : BoundaryManifold (I_half n) M =>
        g.inner b.val
          (outwardNormal
              (I := I_half n) (M := M) g b :
            TangentSpace _ b.val)
          ((smoothSmul (I := I_half n) v.toFun v.smooth
              (grad_g_full_section (M := M) (n := n) g u.smooth)) b.val))
      (surfaceMeasure
        (I := I_half n) (M := M) g)) :
    H1ComplFullNeumannBilin g
        (smoothToH1ComplFullNeumann g u)
        (smoothToH1ComplFullNeumann g v) =
      lpFunctionalCLMFullNeumann g u.oneSubLapClassicalLp
        (smoothToH1ComplFullNeumann g v) := by
  rw [H1ComplFullNeumannBilin_smoothToH1ComplFullNeumann_smoothToH1ComplFullNeumann,
    fullSmoothScalarH1Inner_eq_lpInner_oneSubLapClassical_neumann
      (u := u) (v := v) h_neumann h_chart_iden h_int]
  rw [lpFunctionalCLMFullNeumann_apply,
    H1ComplFullNeumannToLp_smoothToH1ComplFullNeumann]
  exact real_inner_comm _ _

theorem smoothToH1ComplFullNeumann_bilin_eq_lpFunctional_neumann
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : FullSmoothScalar g)
    (h_neumann : ∀ x : (I_half n).boundary M,
      g.inner x.val
        (outwardNormal (I := I_half n) (M := M) g x :
          TangentSpace _ x.val)
        (gradFun (I := I_half n) g u.toFun x.val) = 0)
    (h_chart_iden : ∀ (v : FullSmoothScalar g),
      ∀ α ∈ chartAtlasPOU_finset (I := I_half n) (M := M),
      chartFaceIntegralEqualsSurfaceIntegralOnChart (n := n) (M := M)
        g α
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (grad_g_full_section (M := M) (n := n) g u.smooth))
        ((chartAtlasPOU (I_half n) M) α : M → ℝ))
    (h_int : ∀ (v : FullSmoothScalar g),
      Integrable
        (fun b : BoundaryManifold (I_half n) M =>
          g.inner b.val
            (outwardNormal
                (I := I_half n) (M := M) g b :
              TangentSpace _ b.val)
            ((smoothSmul (I := I_half n) v.toFun v.smooth
                (grad_g_full_section (M := M) (n := n) g u.smooth)) b.val))
        (surfaceMeasure
          (I := I_half n) (M := M) g))
    (w : H1ComplFullNeumann g) :
    H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u) w =
      lpFunctionalCLMFullNeumann g u.oneSubLapClassicalLp w := by
  let L : H1ComplFullNeumann g → ℝ := fun w =>
    H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u) w
  let R : H1ComplFullNeumann g → ℝ := fun w =>
    lpFunctionalCLMFullNeumann g u.oneSubLapClassicalLp w
  change L w = R w
  have hL_cont : Continuous L :=
    (H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u)).continuous
  have hR_cont : Continuous R :=
    (lpFunctionalCLMFullNeumann g u.oneSubLapClassicalLp).continuous
  have hLR_smooth :
      L ∘ (smoothToH1ComplFullNeumann g) = R ∘ (smoothToH1ComplFullNeumann g) := by
    funext v
    exact fullSmoothScalar_bilin_eq_lpFunctional_smooth_neumann
      u v h_neumann (h_chart_iden v) (h_int v)
  exact congrFun
    ((denseRange_smoothToH1ComplFullNeumann g).equalizer hL_cont hR_cont
      hLR_smooth) w

theorem smoothToH1ComplFullNeumann_eq_resolventFullNeumann_oneSubLap_neumann
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : FullSmoothScalar g)
    (h_neumann : ∀ x : (I_half n).boundary M,
      g.inner x.val
        (outwardNormal (I := I_half n) (M := M) g x :
          TangentSpace _ x.val)
        (gradFun (I := I_half n) g u.toFun x.val) = 0)
    (h_chart_iden : ∀ (v : FullSmoothScalar g),
      ∀ α ∈ chartAtlasPOU_finset (I := I_half n) (M := M),
      chartFaceIntegralEqualsSurfaceIntegralOnChart (n := n) (M := M)
        g α
        (smoothSmul (I := I_half n) v.toFun v.smooth
          (grad_g_full_section (M := M) (n := n) g u.smooth))
        ((chartAtlasPOU (I_half n) M) α : M → ℝ))
    (h_int : ∀ (v : FullSmoothScalar g),
      Integrable
        (fun b : BoundaryManifold (I_half n) M =>
          g.inner b.val
            (outwardNormal
                (I := I_half n) (M := M) g b :
              TangentSpace _ b.val)
            ((smoothSmul (I := I_half n) v.toFun v.smooth
                (grad_g_full_section (M := M) (n := n) g u.smooth)) b.val))
        (surfaceMeasure
          (I := I_half n) (M := M) g)) :
    smoothToH1ComplFullNeumann g u =
      resolventFullNeumann g u.oneSubLapClassicalLp := by
  apply ext_inner_right ℝ
  intro w
  rw [show ⟪smoothToH1ComplFullNeumann g u, w⟫_ℝ =
        H1ComplFullNeumannBilin g (smoothToH1ComplFullNeumann g u) w from rfl]
  rw [smoothToH1ComplFullNeumann_bilin_eq_lpFunctional_neumann
    u h_neumann h_chart_iden h_int w]
  rw [resolventFullNeumann_inner_eq_lpFunctional]
  rw [lpFunctionalCLMFullNeumann_apply]

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
