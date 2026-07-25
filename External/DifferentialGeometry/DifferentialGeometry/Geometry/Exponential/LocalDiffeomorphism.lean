import DifferentialGeometry.Geometry.Exponential.Smoothness.MfderivZero
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace



noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

section LocalDiffeomorph

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

private def chartedExpAt (g : SmoothRiemannianMetric I M) (p : M) : E → E :=
  fun v => (extChartAt I p) (expMap (I := I) g p (show TangentSpace I p from v))

private lemma chartedExpAt_contMDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (chartedExpAt (I := I) g p) (0 : E) := by
  classical
  have hexp : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
    expMap_contMDiffAt_zero (I := I) g p
  have hext : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I p)
      (expMap (I := I) g p (show TangentSpace I p from (0 : E))) := by
    have hpt : expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p :=
      expMap_zero (I := I) g p
    rw [hpt]
    exact contMDiffAt_extChartAt (I := I) (x := p) (n := 1)
  exact hext.comp (0 : E) hexp

private lemma chartedExpAt_contDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 1 (chartedExpAt (I := I) g p) (0 : E) :=
  (chartedExpAt_contMDiffAt_zero (I := I) g p).contDiffAt

private lemma chartedExpAt_hasFDerivAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    HasFDerivAt (chartedExpAt (I := I) g p) (ContinuousLinearMap.id ℝ E) (0 : E) := by
  classical
  have hexp_mfd : HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) (ContinuousLinearMap.id ℝ E) := by
    have hm := ((expMap_contMDiffAt_zero (I := I) g p).mdifferentiableAt
      one_ne_zero).hasMFDerivAt
    rw [mfderiv_expMap_at_zero (I := I) g p] at hm
    exact hm
  have hext_hasMFD : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
      (ContinuousLinearMap.id ℝ E) := by
    have hm := ((contMDiffAt_extChartAt (I := I) (x := p) (n := 1)).mdifferentiableAt
      one_ne_zero).hasMFDerivAt
    rw [mfderiv_extChartAt_self (I := I) (x := p)] at hm
    exact hm
  have hpt : (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) 0 = p := by
    change expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p
    exact expMap_zero (I := I) g p
  have hext_at_pt :
      HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p)
        ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) 0)
        (ContinuousLinearMap.id ℝ E) := by rw [hpt]; exact hext_hasMFD
  have hcomp_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      ((extChartAt I p) ∘
        (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)))
      (0 : E) ((ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.id ℝ E)) :=
    hext_at_pt.comp (0 : E) hexp_mfd
  rw [ContinuousLinearMap.id_comp] at hcomp_mfd
  exact hasMFDerivAt_iff_hasFDerivAt.mp hcomp_mfd

private lemma chartedExpAt_hasFDerivAt_refl
    (g : SmoothRiemannianMetric I M) (p : M) :
    HasFDerivAt (chartedExpAt (I := I) g p)
      ((ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)) (0 : E) := by
  have h := chartedExpAt_hasFDerivAt_zero (I := I) g p
  have hcoe : (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E := by
    ext v; simp
  rw [hcoe]; exact h

private def chartedExpAtIFTHomeomorph
    (g : SmoothRiemannianMetric I M) (p : M) : OpenPartialHomeomorph E E :=
  ContDiffAt.toOpenPartialHomeomorph (𝕂 := ℝ)
    (f := chartedExpAt (I := I) g p)
    (f' := ContinuousLinearEquiv.refl ℝ E)
    (chartedExpAt_contDiffAt_zero (I := I) g p)
    (chartedExpAt_hasFDerivAt_refl (I := I) g p)
    one_ne_zero

private lemma zero_mem_chartedExpAtIFTHomeomorph_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ (chartedExpAtIFTHomeomorph (I := I) g p).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source
    (chartedExpAt_contDiffAt_zero (I := I) g p) _ one_ne_zero

private lemma chartedExpAt_zero_mem_IFT_target
    (g : SmoothRiemannianMetric I M) (p : M) :
    chartedExpAt (I := I) g p (0 : E) ∈
      (chartedExpAtIFTHomeomorph (I := I) g p).target :=
  ContDiffAt.image_mem_toOpenPartialHomeomorph_target
    (chartedExpAt_contDiffAt_zero (I := I) g p) _ one_ne_zero

private lemma chartedExpAtIFTHomeomorph_symm_eq_localInverse
    (g : SmoothRiemannianMetric I M) (p : M) :
    (chartedExpAtIFTHomeomorph (I := I) g p).symm =
      (chartedExpAt_contDiffAt_zero (I := I) g p).localInverse
        (chartedExpAt_hasFDerivAt_refl (I := I) g p) one_ne_zero := rfl

private lemma chartedExpAtIFTHomeomorph_symm_contDiffAt
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 1 (chartedExpAtIFTHomeomorph (I := I) g p).symm
      (chartedExpAt (I := I) g p (0 : E)) := by
  classical
  have hinv := (chartedExpAt_contDiffAt_zero (I := I) g p).to_localInverse
    (chartedExpAt_hasFDerivAt_refl (I := I) g p) one_ne_zero
  rw [chartedExpAtIFTHomeomorph_symm_eq_localInverse]
  exact hinv

private theorem exists_nice_open_nhds
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (U : Set E) (W : Set E),
      IsOpen U ∧ (0 : E) ∈ U ∧
      U ⊆ (chartedExpAtIFTHomeomorph (I := I) g p).source ∧
      ContMDiffOn 𝓘(ℝ, E) I 1
        (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) U ∧
      (∀ v ∈ U,
        (expMap (I := I) g p (show TangentSpace I p from v) : M)
          ∈ (extChartAt I p).source) ∧
      IsOpen W ∧
      W ⊆ (chartedExpAtIFTHomeomorph (I := I) g p).target ∧
      ContDiffOn ℝ 1 (chartedExpAtIFTHomeomorph (I := I) g p).symm W ∧
      chartedExpAt (I := I) g p '' U ⊆ W := by
  classical
  have hsymm_at := chartedExpAtIFTHomeomorph_symm_contDiffAt (I := I) g p
  obtain ⟨u_W, hu_W_nhd, hu_W_on⟩ : ∃ u ∈ 𝓝 (chartedExpAt (I := I) g p (0 : E)),
      ContDiffOn ℝ 1 (chartedExpAtIFTHomeomorph (I := I) g p).symm u :=
    hsymm_at.contDiffOn (le_refl _) (by decide)
  rcases _root_.mem_nhds_iff.mp hu_W_nhd with ⟨u_W_open, hu_W_sub, hu_W_isOpen, hu_W_mem⟩
  set W : Set E := u_W_open ∩ (chartedExpAtIFTHomeomorph (I := I) g p).target with hW_def
  have hW_open : IsOpen W :=
    hu_W_isOpen.inter (chartedExpAtIFTHomeomorph (I := I) g p).open_target
  have hW0 : chartedExpAt (I := I) g p (0 : E) ∈ W :=
    ⟨hu_W_mem, chartedExpAt_zero_mem_IFT_target (I := I) g p⟩
  have hW_sub_target : W ⊆ (chartedExpAtIFTHomeomorph (I := I) g p).target := fun _ h => h.2
  have hW_smooth : ContDiffOn ℝ 1 (chartedExpAtIFTHomeomorph (I := I) g p).symm W :=
    hu_W_on.mono (fun w hw => hu_W_sub hw.1)
  have hexp : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
    expMap_contMDiffAt_zero (I := I) g p
  haveI : IsManifold I 1 M := by
    have : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (by decide : (1 : ℕ∞) ≤ ⊤)
    exact IsManifold.of_le this
  have hone_ne_top : (1 : WithTop ℕ∞) ≠ ∞ := by decide
  obtain ⟨u_smooth, hu_smooth_nhd, hu_smooth_on⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds hone_ne_top).mp hexp
  rcases _root_.mem_nhds_iff.mp hu_smooth_nhd with
    ⟨u_open, hu_open_sub, hu_open_isOpen, hu_open_mem⟩
  have hIFT_source_isOpen : IsOpen (chartedExpAtIFTHomeomorph (I := I) g p).source :=
    (chartedExpAtIFTHomeomorph (I := I) g p).open_source
  have h0_IFT : (0 : E) ∈ (chartedExpAtIFTHomeomorph (I := I) g p).source :=
    zero_mem_chartedExpAtIFTHomeomorph_source (I := I) g p
  have hcont_on_uopen : ContinuousOn
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) u_open :=
    ContMDiffOn.continuousOn (hu_smooth_on.mono hu_open_sub)
  have h_extSrc_open : IsOpen ((extChartAt I p).source) :=
    isOpen_extChartAt_source (I := I) (x := p)
  have h0_in_extSrc : (expMap (I := I) g p (show TangentSpace I p from (0 : E)) : M)
      ∈ (extChartAt I p).source := by
    have hpt : expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p :=
      expMap_zero (I := I) g p
    rw [hpt]
    exact mem_extChartAt_source (I := I) p
  obtain ⟨w_open, hw_open_isOpen, hw_open_eq⟩ :=
    continuousOn_iff'.mp hcont_on_uopen (extChartAt I p).source h_extSrc_open
  have hcont_chartedExp : ContinuousOn (chartedExpAt (I := I) g p)
      (chartedExpAtIFTHomeomorph (I := I) g p).source := by
    have := (chartedExpAtIFTHomeomorph (I := I) g p).continuousOn_toFun
    exact this
  obtain ⟨w_chart, hw_chart_isOpen, hw_chart_eq⟩ :=
    continuousOn_iff'.mp hcont_chartedExp W hW_open
  set U : Set E := (chartedExpAtIFTHomeomorph (I := I) g p).source ∩ u_open ∩ w_open ∩ w_chart
    with hU_def
  have hU_isOpen : IsOpen U :=
    ((hIFT_source_isOpen.inter hu_open_isOpen).inter hw_open_isOpen).inter hw_chart_isOpen
  have h0_w_open : (0 : E) ∈ w_open := by
    have h0_preim : (0 : E) ∈
        ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
          ⁻¹' (extChartAt I p).source) ∩ u_open := ⟨h0_in_extSrc, hu_open_mem⟩
    rw [hw_open_eq] at h0_preim
    exact h0_preim.1
  have h0_w_chart : (0 : E) ∈ w_chart := by
    have h0_preim : (0 : E) ∈
        (chartedExpAt (I := I) g p) ⁻¹' W ∩
          (chartedExpAtIFTHomeomorph (I := I) g p).source := ⟨hW0, h0_IFT⟩
    rw [hw_chart_eq] at h0_preim
    exact h0_preim.1
  have h0U : (0 : E) ∈ U := ⟨⟨⟨h0_IFT, hu_open_mem⟩, h0_w_open⟩, h0_w_chart⟩
  have hU_sub_IFT : U ⊆ (chartedExpAtIFTHomeomorph (I := I) g p).source :=
    fun _ h => h.1.1.1
  have hU_smooth : ContMDiffOn 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) U := by
    apply hu_smooth_on.mono
    intro v hv
    exact hu_open_sub hv.1.1.2
  have hU_extSrc : ∀ v ∈ U,
      (expMap (I := I) g p (show TangentSpace I p from v) : M)
        ∈ (extChartAt I p).source := by
    intro v hv
    have hv_wu : v ∈ w_open ∩ u_open := ⟨hv.1.2, hv.1.1.2⟩
    have hv_inv : v ∈
        ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
          ⁻¹' (extChartAt I p).source) ∩ u_open := by
      rw [hw_open_eq]; exact hv_wu
    exact hv_inv.1
  have hU_chartedExp_W : chartedExpAt (I := I) g p '' U ⊆ W := by
    rintro y ⟨v, hv, rfl⟩
    have hv_wIFT : v ∈ w_chart ∩ (chartedExpAtIFTHomeomorph (I := I) g p).source :=
      ⟨hv.2, hU_sub_IFT hv⟩
    have hv_inv : v ∈ (chartedExpAt (I := I) g p) ⁻¹' W ∩
        (chartedExpAtIFTHomeomorph (I := I) g p).source := by
      rw [hw_chart_eq]; exact hv_wIFT
    exact hv_inv.1
  exact ⟨U, W, hU_isOpen, h0U, hU_sub_IFT, hU_smooth, hU_extSrc, hW_open, hW_sub_target,
    hW_smooth, hU_chartedExp_W⟩

private def expLocalDiffeoSource (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  (Classical.choose (exists_nice_open_nhds (I := I) g p))

private def niceSymmDomain (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  Classical.choose
    (Classical.choose_spec (exists_nice_open_nhds (I := I) g p))

private lemma niceSource_spec (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (expLocalDiffeoSource (I := I) g p) ∧
    (0 : E) ∈ expLocalDiffeoSource (I := I) g p ∧
    expLocalDiffeoSource (I := I) g p ⊆ (chartedExpAtIFTHomeomorph (I := I) g p).source ∧
    ContMDiffOn 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (expLocalDiffeoSource (I := I) g p) ∧
    (∀ v ∈ expLocalDiffeoSource (I := I) g p,
      (expMap (I := I) g p (show TangentSpace I p from v) : M)
        ∈ (extChartAt I p).source) ∧
    IsOpen (niceSymmDomain (I := I) g p) ∧
    niceSymmDomain (I := I) g p ⊆ (chartedExpAtIFTHomeomorph (I := I) g p).target ∧
    ContDiffOn ℝ 1 (chartedExpAtIFTHomeomorph (I := I) g p).symm
      (niceSymmDomain (I := I) g p) ∧
    chartedExpAt (I := I) g p '' (expLocalDiffeoSource (I := I) g p) ⊆
      niceSymmDomain (I := I) g p :=
  Classical.choose_spec
    (Classical.choose_spec (exists_nice_open_nhds (I := I) g p))

private lemma niceSource_isOpen (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (expLocalDiffeoSource (I := I) g p) := (niceSource_spec (I := I) g p).1

private lemma zero_mem_niceSource (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ expLocalDiffeoSource (I := I) g p := (niceSource_spec (I := I) g p).2.1

private lemma niceSource_sub_IFT_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    expLocalDiffeoSource (I := I) g p ⊆ (chartedExpAtIFTHomeomorph (I := I) g p).source :=
  (niceSource_spec (I := I) g p).2.2.1

private lemma niceSource_smoothOn (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (expLocalDiffeoSource (I := I) g p) :=
  (niceSource_spec (I := I) g p).2.2.2.1

private lemma niceSource_extSrc (g : SmoothRiemannianMetric I M) (p : M) :
    ∀ v ∈ expLocalDiffeoSource (I := I) g p,
      (expMap (I := I) g p (show TangentSpace I p from v) : M)
        ∈ (extChartAt I p).source :=
  (niceSource_spec (I := I) g p).2.2.2.2.1

private lemma niceSymmDomain_contDiffOn
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffOn ℝ 1 (chartedExpAtIFTHomeomorph (I := I) g p).symm
      (niceSymmDomain (I := I) g p) :=
  (niceSource_spec (I := I) g p).2.2.2.2.2.2.2.1

private lemma chartedExp_niceSource_sub_niceSymmDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    chartedExpAt (I := I) g p '' (expLocalDiffeoSource (I := I) g p) ⊆
      niceSymmDomain (I := I) g p :=
  (niceSource_spec (I := I) g p).2.2.2.2.2.2.2.2

private def expLocalDiffeoTarget (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
    '' (expLocalDiffeoSource (I := I) g p)

private lemma chartedExp_image_niceSource_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (chartedExpAt (I := I) g p '' (expLocalDiffeoSource (I := I) g p)) := by
  classical
  have hsub : expLocalDiffeoSource (I := I) g p ⊆
      (chartedExpAtIFTHomeomorph (I := I) g p).source :=
    niceSource_sub_IFT_source (I := I) g p
  have hopen : IsOpen (expLocalDiffeoSource (I := I) g p) := niceSource_isOpen (I := I) g p
  have heq : chartedExpAt (I := I) g p '' (expLocalDiffeoSource (I := I) g p) =
      (chartedExpAtIFTHomeomorph (I := I) g p) '' (expLocalDiffeoSource (I := I) g p) := rfl
  rw [heq]
  exact (chartedExpAtIFTHomeomorph (I := I) g p).isOpen_image_of_subset_source hopen hsub

private lemma niceTarget_eq_source_inter_preimage
    (g : SmoothRiemannianMetric I M) (p : M) :
    expLocalDiffeoTarget (I := I) g p =
      (extChartAt I p).source ∩
        (extChartAt I p) ⁻¹'
          (chartedExpAt (I := I) g p '' (expLocalDiffeoSource (I := I) g p)) := by
  classical
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨niceSource_extSrc (I := I) g p v hv, ?_⟩
    refine ⟨v, hv, rfl⟩
  · rintro ⟨hq_src, hq_pre⟩
    rcases hq_pre with ⟨v, hv, hwv⟩
    refine ⟨v, hv, ?_⟩
    have h_eq : (extChartAt I p) q =
        (extChartAt I p)
          (expMap (I := I) g p (show TangentSpace I p from v)) := by
      rw [← hwv]; rfl
    have hexp_src : (expMap (I := I) g p (show TangentSpace I p from v) : M)
        ∈ (extChartAt I p).source := niceSource_extSrc (I := I) g p v hv
    have hinj := (extChartAt I p).injOn hq_src hexp_src h_eq
    exact hinj.symm

private lemma niceTarget_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (expLocalDiffeoTarget (I := I) g p) := by
  classical
  rw [niceTarget_eq_source_inter_preimage (I := I) g p]
  exact isOpen_extChartAt_preimage' (I := I) (x := p)
    (chartedExp_image_niceSource_isOpen (I := I) g p)

private lemma niceTarget_sub_extChartSource
    (g : SmoothRiemannianMetric I M) (p : M) :
    expLocalDiffeoTarget (I := I) g p ⊆ (extChartAt I p).source := by
  classical
  rintro q ⟨v, hv, rfl⟩
  exact niceSource_extSrc (I := I) g p v hv

private lemma niceTarget_sub_chartSource
    (g : SmoothRiemannianMetric I M) (p : M) :
    expLocalDiffeoTarget (I := I) g p ⊆ (chartAt H p).source := by
  intro q hq
  have := niceTarget_sub_extChartSource (I := I) g p hq
  rwa [extChartAt_source I] at this

private lemma extChartAt_niceTarget_sub_niceSymmDomain
    (g : SmoothRiemannianMetric I M) (p : M) :
    (extChartAt I p) '' (expLocalDiffeoTarget (I := I) g p) ⊆ niceSymmDomain (I := I) g p := by
  classical
  rintro w ⟨q, hq, rfl⟩
  rcases hq with ⟨v, hv, rfl⟩
  have hin : chartedExpAt (I := I) g p v ∈ niceSymmDomain (I := I) g p := by
    exact chartedExp_niceSource_sub_niceSymmDomain (I := I) g p ⟨v, hv, rfl⟩
  exact hin

private def expLocalDiffeoInvFun (g : SmoothRiemannianMetric I M) (p : M) : M → E :=
  fun q => (chartedExpAtIFTHomeomorph (I := I) g p).symm ((extChartAt I p) q)

private lemma niceInvFun_left_inv
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : v ∈ expLocalDiffeoSource (I := I) g p) :
    expLocalDiffeoInvFun (I := I) g p
      (expMap (I := I) g p (show TangentSpace I p from v)) = v := by
  classical
  unfold expLocalDiffeoInvFun
  show (chartedExpAtIFTHomeomorph (I := I) g p).symm
      ((extChartAt I p)
        (expMap (I := I) g p (show TangentSpace I p from v))) = v
  have heq : (extChartAt I p)
      (expMap (I := I) g p (show TangentSpace I p from v)) =
        chartedExpAt (I := I) g p v := rfl
  rw [heq]
  have hv_IFT : v ∈ (chartedExpAtIFTHomeomorph (I := I) g p).source :=
    niceSource_sub_IFT_source (I := I) g p hv
  have := (chartedExpAtIFTHomeomorph (I := I) g p).left_inv hv_IFT
  rwa [show ((chartedExpAtIFTHomeomorph (I := I) g p) : E → E) v =
        chartedExpAt (I := I) g p v from rfl] at this

private lemma niceInvFun_mapsTo_niceSource
    (g : SmoothRiemannianMetric I M) (p : M) {q : M}
    (hq : q ∈ expLocalDiffeoTarget (I := I) g p) :
    expLocalDiffeoInvFun (I := I) g p q ∈ expLocalDiffeoSource (I := I) g p := by
  classical
  rcases hq with ⟨v, hv, rfl⟩
  rw [niceInvFun_left_inv (I := I) g p hv]
  exact hv

private lemma niceInvFun_right_inv
    (g : SmoothRiemannianMetric I M) (p : M) {q : M}
    (hq : q ∈ expLocalDiffeoTarget (I := I) g p) :
    (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (expLocalDiffeoInvFun (I := I) g p q) = q := by
  classical
  rcases hq with ⟨v, hv, rfl⟩
  change (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (expLocalDiffeoInvFun (I := I) g p
        (expMap (I := I) g p (show TangentSpace I p from v))) =
    expMap (I := I) g p (show TangentSpace I p from v)
  rw [niceInvFun_left_inv (I := I) g p hv]

private lemma niceInvFun_contMDiffOn
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn I 𝓘(ℝ, E) 1 (expLocalDiffeoInvFun (I := I) g p) (expLocalDiffeoTarget (I := I) g p) := by
  classical
  have hext : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I p) (chartAt H p).source :=
    contMDiffOn_extChartAt (I := I) (x := p) (n := 1)
  have hext_on : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I p) (expLocalDiffeoTarget (I := I) g p) :=
    hext.mono (niceTarget_sub_chartSource (I := I) g p)
  have hsymm_contDiff : ContDiffOn ℝ 1 (chartedExpAtIFTHomeomorph (I := I) g p).symm
      (niceSymmDomain (I := I) g p) := niceSymmDomain_contDiffOn (I := I) g p
  have hsymm_contMDiff : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (chartedExpAtIFTHomeomorph (I := I) g p).symm
      (niceSymmDomain (I := I) g p) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hsymm_contDiff
  have hmaps : MapsTo (extChartAt I p) (expLocalDiffeoTarget (I := I) g p)
      (niceSymmDomain (I := I) g p) := by
    intro q hq
    exact extChartAt_niceTarget_sub_niceSymmDomain (I := I) g p ⟨q, hq, rfl⟩
  have := hsymm_contMDiff.comp hext_on hmaps
  exact this

private def expMapPartialDiffeomorph
    (g : SmoothRiemannianMetric I M) (p : M) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M 1 where
  toFun := fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)
  invFun := expLocalDiffeoInvFun (I := I) g p
  source := expLocalDiffeoSource (I := I) g p
  target := expLocalDiffeoTarget (I := I) g p
  map_source' := by
    intro v hv
    exact ⟨v, hv, rfl⟩
  map_target' := by
    intro q hq
    exact niceInvFun_mapsTo_niceSource (I := I) g p hq
  left_inv' := by
    intro v hv
    exact niceInvFun_left_inv (I := I) g p hv
  right_inv' := by
    intro q hq
    exact niceInvFun_right_inv (I := I) g p hq
  open_source := niceSource_isOpen (I := I) g p
  open_target := niceTarget_isOpen (I := I) g p
  contMDiffOn_toFun := niceSource_smoothOn (I := I) g p
  contMDiffOn_invFun := niceInvFun_contMDiffOn (I := I) g p

private lemma zero_mem_expMapPartialDiffeomorph_source
    (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : E) ∈ (expMapPartialDiffeomorph (I := I) g p).source :=
  zero_mem_niceSource (I := I) g p

theorem expMap_isLocalDiffeomorphAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) := by
  classical
  refine ⟨expMapPartialDiffeomorph (I := I) g p,
    zero_mem_expMapPartialDiffeomorph_source (I := I) g p, ?_⟩
  intro v _hv
  rfl

theorem exists_open_nhds_expMap_diffeoOn
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1,
      (0 : E) ∈ Φ.source ∧
      ∀ v ∈ Φ.source,
        Φ v = (expMap (I := I) g p (show TangentSpace I p from v) : M) :=
  ⟨expMapPartialDiffeomorph (I := I) g p,
    zero_mem_expMapPartialDiffeomorph_source (I := I) g p,
    fun _ _ => rfl⟩



theorem exists_exp_pd_chart
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1,
      (0 : E) ∈ Φ.source ∧
      (∀ v ∈ Φ.source,
        Φ v = (expMap (I := I) g p (show TangentSpace I p from v) : M)) ∧
      Φ.target ⊆ (chartAt H p).source := by
  refine ⟨expMapPartialDiffeomorph (I := I) g p,
    zero_mem_expMapPartialDiffeomorph_source (I := I) g p, fun _ _ => rfl, ?_⟩
  exact niceTarget_sub_chartSource (I := I) g p

end LocalDiffeomorph

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
