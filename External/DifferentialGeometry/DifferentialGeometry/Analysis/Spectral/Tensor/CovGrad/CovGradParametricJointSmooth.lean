import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartPulledCovApplyExplicitFormula
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartKernel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Interval
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad covGrad_toSection_apply
  pathIntegralCoeffField pathIntegralFib pathIntegralCoeffField_toSection
  pathIntegralCoeffField_toModel pathIntegralFib_toModel tensorCovDerivAt tensorCovDerivAt_def)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (contMDiffOn_clm_section_of_pointwise_joint_manifold_time
  jointContMDiff_toModel_continuous_slice)
open Tensor0SBundle TensorRSNabla

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem chartRepr_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) r s α (fun z : M => (F p.2).toSection z) p.1)
      (((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) := by
  have hrepr :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
        (fun p : M × ℝ =>
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α)
            ⟨p.1, (F p.2).toSection p.1⟩).2)
        (((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) := by
    intro p hp
    obtain ⟨hx, hs⟩ := hp
    have hsub : (((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) ⊆
        ((Set.univ : Set M) ×ˢ S) := by
      intro q hq; exact ⟨Set.mem_univ _, hq.2⟩
    have hFwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
          TotalSpace (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z)))
        (((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S) p :=
      (hF p (hsub ⟨hx, hs⟩)).mono hsub
    have hsource : (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z)) ∈
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).source := by
      rw [Bundle.Trivialization.mem_source]
      exact hx
    exact ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
      (f := fun p : M × ℝ => (⟨p.1, (F p.2).toSection p.1⟩ :
        TotalSpace (TensorRSModel r s ℝ E)
          (fun z : M => TensorRSSpace r s I z)))
      (s := ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet) ×ˢ S)
      (x₀ := p)
      (e := trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) hsource).mp hFwithin).2
  refine hrepr.congr ?_
  intro p hp
  obtain ⟨hx, _hs⟩ := hp
  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
  change (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ p.1
      ((F p.2).toSection p.1) = _
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hx]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem chartRepr_euclid_jointContDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {y₀ : E} (ht₀ : t₀ ∈ S)
    (hy₀ : y₀ ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, y₀) := by
  classical
  have hbase := chartRepr_jointContMDiffOn (I := I) g₀ r s F S α hF
  have hbaseSet_eq :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  rw [hbaseSet_eq] at hbase
  set φ := extChartAt I α with hφ
  have hx0src : φ.symm y₀ ∈ (chartAt H α).source := by
    have := φ.map_target hy₀
    rwa [extChartAt_source] at this
  have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hmove : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) (t₀, y₀) := by
    refine ContMDiffWithinAt.prodMk ?_ ?_
    · have hsymm_w : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm φ.target y₀ := hsymm_on y₀ hy₀
      exact hsymm_w.comp (t₀, y₀) contMDiffWithinAt_snd (fun q hq => hq.2)
    · exact contMDiffWithinAt_fst
  have hbase_w : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F p.2).toSection z) p.1)
      ((chartAt H α).source ×ˢ S) ((φ.symm y₀ : M), t₀) :=
    hbase ((φ.symm y₀ : M), t₀) ⟨hx0src, ht₀⟩
  have hmaps : Set.MapsTo (fun q : ℝ × E => ((φ.symm q.2 : M), q.1))
      (S ×ˢ φ.target) ((chartAt H α).source ×ˢ S) := by
    intro q hq
    obtain ⟨hqS, hqtgt⟩ := hq
    refine ⟨?_, hqS⟩
    have := φ.map_target hqtgt
    rwa [extChartAt_source] at this
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) :=
    hbase_w.comp (t₀, y₀) hmove hmaps
  have hself : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) (φ.symm q.2))
      (S ×ˢ φ.target) (t₀, y₀) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
    exact hcomp
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hself
  exact hself

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covApply_chartRepr_euclid_jointContDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    {t₀ : ℝ} {b : M} (ht₀ : t₀ ∈ S)
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) (t₀, extChartAt I α b) := by
  classical
  set φ := extChartAt I α with hφ
  set chartRep : ℝ → E → TensorRSModel r s ℝ E :=
    fun t y => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => (F t).toSection z) (φ.symm y) with hchartRep
  set U : Set E := φ '' chartLeviCivitaGoodSet (I := I) α with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : φ b ∈ U := ⟨b, hb_good, rfl⟩
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
  have hyb_tgt : φ b ∈ φ.target :=
    φ.map_source (by rw [hφ, extChartAt_source]; exact hb_src)
  have hchartRep_w : ∀ y₀ : E, y₀ ∈ φ.target →
      ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2) (S ×ˢ φ.target) (t₀, y₀) := by
    intro y₀ hy₀
    exact chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α hF ht₀ hy₀
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := B.contMDiff.contMDiffOn
  have hvec_cd : ContDiffOn ℝ ∞
      (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun ∘ φ.symm) U :=
    chartE_pullback_contDiffOn_goodSet (I := I) α hB_on
  have hvec_at : ContDiffAt ℝ ∞
      (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun ∘ φ.symm)
      (φ b) :=
    (hvec_cd (φ b) hx_mem).contDiffAt (hU_open.mem_nhds hx_mem)
  have hvec_q : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.chartE_section_repr
        (I := I) α B.toFun (φ.symm q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
    (hvec_at.comp (t₀, φ b) contDiffAt_snd).contDiffWithinAt
  have h_intrinsic : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
        (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun (φ.symm q.2)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    have huncurry : ContDiffWithinAt ℝ ∞
        (Function.uncurry (fun (q : ℝ × E) (y' : E) => chartRep q.1 y'))
        ((S ×ˢ φ.target) ×ˢ φ.target)
        ((t₀, φ b), (fun q : ℝ × E => q.2) (t₀, φ b)) := by
      have hbrick : ContDiffWithinAt ℝ ∞ (fun r : ℝ × E => chartRep r.1 r.2)
          (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_tgt
      have hproj : ContDiffWithinAt ℝ ∞
          (fun r : (ℝ × E) × E => (r.1.1, r.2))
          ((S ×ˢ φ.target) ×ˢ φ.target) ((t₀, φ b), φ b) :=
        (contDiffWithinAt_fst.fst).prodMk contDiffWithinAt_snd
      refine hbrick.comp ((t₀, φ b), φ b) hproj ?_
      rintro ⟨⟨t, y⟩, y'⟩ ⟨⟨ht, _⟩, hy'⟩
      exact ⟨ht, hy'⟩
    have hg : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      contDiffWithinAt_snd
    have htgt_open : IsOpen φ.target := isOpen_extChartAt_target (I := I) α
    have hud : UniqueDiffOn ℝ φ.target := htgt_open.uniqueDiffOn
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    have hsub : (S ×ˢ φ.target) ⊆ (fun q : ℝ × E => q.2) ⁻¹' φ.target := by
      intro q hq; exact hq.2
    have hfdw := ContDiffWithinAt.fderivWithin huncurry hg hud h_le ⟨ht₀, hyb_tgt⟩ hsub
    have hfd_eq : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => fderiv ℝ (fun y' : E => chartRep q.1 y') q.2) (S ×ˢ φ.target) (t₀, φ b) := by
      refine hfdw.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact (fderivWithin_of_isOpen htgt_open hq.2).symm
      · exact (fderivWithin_of_isOpen htgt_open hyb_tgt).symm
    exact hfd_eq.clm_apply hvec_q
  have hchartRep_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => chartRep q.1 q.2)
      (S ×ˢ φ.target) (t₀, φ b) := hchartRep_w (φ b) hyb_tgt
  have h_input : ∀ k : Fin r, ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          (φ.symm q.2)
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) k))
      (S ×ˢ φ.target) (t₀, φ b) := by
    intro k
    obtain ⟨Ker, hKer, hK_at⟩ :
        ∃ Ker : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E),
          (Ker = fun y : E => DifferentialGeometry.Integral.Connection.inputSlotChartKernel
            (I := I) g₀ r s α B.toFun k (φ.symm y)) ∧
          ContDiffAt ℝ ∞ Ker (φ b) :=
      ⟨_, rfl, inputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g₀ r s α B k hb_good⟩
    have hK_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => Ker q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      (ContDiffAt.comp (t₀, φ b) hK_at contDiffAt_snd).contDiffWithinAt
    have h_apply : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Ker q.2 (chartRep q.1 q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
      hK_q.clm_apply hchartRep_q
    refine h_apply.congr_of_eventuallyEq ?_ ?_
    · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
        (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
      refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
      rintro ⟨t, y⟩ hq
      have hy : y ∈ U := hq.2
      obtain ⟨x', hx'_good, hx'y⟩ := hy
      have hx'_src : x' ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
      have hx'_extsrc : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx'_src
      have hx'_inv : φ.symm y = x' := by rw [← hx'y]; exact φ.left_inv hx'_extsrc
      change _ = Ker y (chartRep t y)
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t).toSection b') B.toFun
        (b := φ.symm y) (by rw [hx'_inv]; exact hx'_src) k)
    · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
      change _ = Ker (φ b) (chartRep t₀ (φ b))
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t₀).toSection b') B.toFun
        (b := φ.symm (φ b)) (by rw [hgood_inv]; exact hb_src) k)
  have h_output : ∀ l : Fin s, ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
          (φ.symm q.2)
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l))
      (S ×ˢ φ.target) (t₀, φ b) := by
    intro l
    obtain ⟨Ker, hKer, hK_at⟩ :
        ∃ Ker : E → (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E),
          (Ker = fun y : E => DifferentialGeometry.Integral.Connection.outputSlotChartKernel
            (I := I) g₀ r s α B.toFun l (φ.symm y)) ∧
          ContDiffAt ℝ ∞ Ker (φ b) :=
      ⟨_, rfl, outputSlotChartKernel_contDiffAt_chart_pulled (I := I) (M := M) g₀ r s α B l hb_good⟩
    have hK_q : ContDiffWithinAt ℝ ∞ (fun q : ℝ × E => Ker q.2) (S ×ˢ φ.target) (t₀, φ b) :=
      (ContDiffAt.comp (t₀, φ b) hK_at contDiffAt_snd).contDiffWithinAt
    have h_apply : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Ker q.2 (chartRep q.1 q.2)) (S ×ˢ φ.target) (t₀, φ b) :=
      hK_q.clm_apply hchartRep_q
    refine h_apply.congr_of_eventuallyEq ?_ ?_
    · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
        (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
      refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
      rintro ⟨t, y⟩ hq
      have hy : y ∈ U := hq.2
      obtain ⟨x', hx'_good, hx'y⟩ := hy
      have hx'_src : x' ∈ (chartAt H α).source :=
        chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
      have hx'_extsrc : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx'_src
      have hx'_inv : φ.symm y = x' := by rw [← hx'y]; exact φ.left_inv hx'_extsrc
      change _ = Ker y (chartRep t y)
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t).toSection b') B.toFun
        (b := φ.symm y) (by rw [hx'_inv]; exact hx'_src) l)
    · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
      change _ = Ker (φ b) (chartRep t₀ (φ b))
      rw [hKer, hchartRep]
      simp only []
      exact (chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
        (fun b' : M => (F t₀).toSection b') B.toFun
        (b := φ.symm (φ b)) (by rw [hgood_inv]; exact hb_src) l)
  have h_sum : ContDiffWithinAt ℝ ∞
      (fun q : ℝ × E =>
        fderiv ℝ (fun y' : E => chartRep q.1 y') q.2
          (DifferentialGeometry.Integral.Connection.chartE_section_repr (I := I) α B.toFun (φ.symm q.2))
        + (∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) k))
        - (∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ
              (φ.symm q.2)
              (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
                (fun z : M => (F q.1).toSection z) B.toFun (φ.symm q.2) l)))
      (S ×ˢ φ.target) (t₀, φ b) := by
    refine (h_intrinsic.add (ContDiffWithinAt.sum (fun k _ => h_input k))).sub
      (ContDiffWithinAt.sum (fun l _ => h_output l))
  refine h_sum.congr_of_eventuallyEq ?_ ?_
  · have hUprod : (Set.univ : Set ℝ) ×ˢ U ∈ nhds (t₀, φ b) :=
      (isOpen_univ.prod hU_open).mem_nhds ⟨Set.mem_univ _, hx_mem⟩
    refine Filter.eventually_of_mem (nhdsWithin_le_nhds hUprod) ?_
    rintro ⟨t, y⟩ hq
    have hy : y ∈ U := hq.2
    obtain ⟨x', hx'_good, hx'y⟩ := hy
    have hx'_extsrc : x' ∈ φ.source := by
      rw [hφ, extChartAt_source]; exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx'_good
    have hy_tgt : y ∈ φ.target := hx'y ▸ φ.map_source hx'_extsrc
    have hy_good : φ.symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [← hx'y, φ.left_inv hx'_extsrc]; exact hx'_good
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (F t) B hy_tgt hy_good
    change DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t).toSection z)) (φ.symm y) = _
    rw [hchartRep]
    simp only [Function.comp_apply] at hform
    exact hform
  · have hgood_inv : φ.symm (φ b) = b := φ.left_inv (by rw [hφ, extChartAt_source]; exact hb_src)
    have hform := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (F t₀) B hyb_tgt (by rw [hgood_inv]; exact hb_good)
    change DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F t₀).toSection z)) (φ.symm (φ b)) = _
    rw [hchartRep]
    simp only [Function.comp_apply] at hform
    exact hform

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covApply_chartRepr_manifold_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) := by
  classical
  set φ := extChartAt I α with hφ
  intro p hp
  obtain ⟨hpx, hps⟩ := hp
  have hpx_good : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source]; exact hpx
  have hEu := covApply_chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α B hF hps hpx_good
  have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
      (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hmoveOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun q : M × ℝ => (q.2, φ q.1))
        ((chartAt H α).source ×ˢ S) := by
      refine ContMDiffOn.prodMk contMDiffOn_snd ?_
      exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun q hq => hq.1)
    have hm := hmoveOn p ⟨hpx, hps⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  have hEuM : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun q : ℝ × E =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F q.1).toSection z)) (φ.symm q.2))
      (S ×ˢ φ.target) (p.2, φ p.1) := by
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact hEu
  have hmaps : Set.MapsTo (fun q : M × ℝ => (q.2, φ q.1))
      ((chartAt H α).source ×ˢ S) (S ×ˢ φ.target) := by
    intro q hq
    obtain ⟨hqx, hqs⟩ := hq
    refine ⟨hqs, ?_⟩
    exact φ.map_source (by rw [hφ, extChartAt_source]; exact hqx)
  have hcomp := hEuM.comp p hmove hmaps
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨hqx, _⟩ := hq
    have hqsrc : q.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hqx
    simp only [Function.comp_apply]
    rw [φ.left_inv hqsrc]
  · simp only [Function.comp_apply]
    have hpsrc : p.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hpx
    rw [φ.left_inv hpsrc]

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covApply_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (F p.2).toSection z) p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ S) ∩ ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ S := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hCR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (F p.2).toSection z)) p.1)
      ((chartAt H α).source ×ˢ S) :=
    covApply_chartRepr_manifold_jointContMDiffOn (I := I) g₀ r s F S α B hF
  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        rw [hα]; exact hx₀src
  have hsource : (⟨p₀.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p₀.2).toSection z) p₀.1⟩ :
      TotalSpace (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z)) ∈
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun p : M × ℝ =>
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α)
          ⟨p.1,
            covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
              B.toFun (fun z : M => (F p.2).toSection z) p.1⟩).2)
      ((chartAt H α).source ×ˢ S) p₀ := by
    refine (hCR p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      obtain ⟨hpx, _⟩ := hp
      have hpbase : p.1 ∈ (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet := by
        change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace r I y) α).baseSet) ∩
            ((trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
              (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet)
        refine ⟨?_, ?_⟩ <;>
          · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
            rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
              TangentBundle.trivializationAt_baseSet (I := I) α]
            exact hpx
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    · rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet]
  refine ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1,
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
        B.toFun (fun z : M => (F p.2).toSection z) p.1⟩ :
      TotalSpace (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z)))
    (s := (chartAt H α).source ×ˢ S) (x₀ := p₀)
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_step_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r sIdx (Ψ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  set φfield : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TensorRSSpace r sIdx I p.1 :=
    fun p => tensorRSCovariantDerivative I M r sIdx (LeviCivita (I := I) g₀)
      (fun y : M => (Ψ p.2).toSection y) p.1 with hφfield
  have hCLM : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r sIdx ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] TensorRSModel r sIdx ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TensorRSSpace r sIdx I x) p.1 (φfield p))
      ((Set.univ : Set M) ×ˢ S) := by
    refine contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := TensorRSModel r sIdx ℝ E) (V₂ := fun x : M => TensorRSSpace r sIdx I x)
      (φ := φfield) (S := S) ?_
    intro Y
    have hYapply := covApply_section_jointContMDiffOn (I := I) g₀ r sIdx Ψ S Y hjoint
    refine hYapply.congr ?_
    rintro ⟨x, t⟩ -
    rfl
  have hcomp := (covGradBundleSmoothEquiv (I := I) (M := M) r sIdx).toDiffeomorph.contMDiff.comp_contMDiffOn
    hCLM
  refine hcomp.congr ?_
  rintro ⟨x, t⟩ -
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r sIdx x (φfield (x, t))]
  rw [covGrad_toSection_apply]

section PathIntegralComm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem toModel_section_intervalIntegrable
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) :
    IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) volume 0 1 :=
  ((jointContMDiff_toModel_continuous_slice (I := I) g₀ r s Φ S hjoint x).mono hSI).intervalIntegrable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem chartRepr_pathIntegralCoeffField_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (α b : M) :
    DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection y) b =
      ∫ t in (0 : ℝ)..1,
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => (Φ t).toSection y) b := by
  set L : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b).comp
      (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s b).symm.toContinuousLinearMap
    with hL
  have hIIm : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection b)) volume 0 1 :=
    toModel_section_intervalIntegrable (I := I) g₀ r s Φ S hSI hjoint b
  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
  have hLHS : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection b) =
      L (∫ t in (0 : ℝ)..1, TensorRSSpace.toModel ((Φ t).toSection b)) := by
    rw [hL, ContinuousLinearMap.comp_apply]
    congr 1
  rw [hLHS, ← ContinuousLinearMap.intervalIntegral_comp_comm L hIIm]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply, hL,
    ContinuousLinearMap.comp_apply]
  congr 1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem chartRepr_comp_symm_jointContDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (α : M)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm q.2))
      (S ×ˢ (extChartAt I α).target) := by
  intro q hq
  obtain ⟨hqS, hqtgt⟩ := hq
  exact chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α hF hqS hqtgt

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem fderiv_chartRepr_jointContinuousOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : ℝ → SmoothCcTensor g₀ r s)
    (S : Set ℝ) (_hS : IsOpen S) (α : M) {U : Set E} (hU : IsOpen U)
    (hUtgt : U ⊆ (extChartAt I α).target)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((F p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn
      (fun q : ℝ × E => fderiv ℝ (fun y : E =>
          DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) r s α (fun z : M => (F q.1).toSection z) ((extChartAt I α).symm y)) q.2)
      (S ×ˢ U) := by
  intro q hq
  obtain ⟨hqS, hqU⟩ := hq
  set G : ℝ × E → E → TensorRSModel r s ℝ E :=
    fun p y => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
      (I := I) r s α (fun z : M => (F p.1).toSection z) ((extChartAt I α).symm y) with hG
  have huncurry : ContDiffWithinAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => G p y))
      ((S ×ˢ U) ×ˢ U) ((q, (fun p : ℝ × E => p.2) q)) := by
    have hbrick : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => G p p.2)
        (S ×ˢ (extChartAt I α).target) q :=
      chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s F S α hF hqS (hUtgt hqU)
    have hproj : ContDiffWithinAt ℝ ∞
        (fun w : (ℝ × E) × E => (w.1.1, w.2))
        ((S ×ˢ U) ×ˢ U) (q, q.2) :=
      (contDiffWithinAt_fst.fst).prodMk contDiffWithinAt_snd
    refine hbrick.comp (q, q.2) hproj ?_
    rintro ⟨⟨t, y⟩, y'⟩ ⟨⟨ht, _⟩, hy'⟩
    exact ⟨ht, hUtgt hy'⟩
  have hg : ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => p.2) (S ×ˢ U) q := contDiffWithinAt_snd
  have hud : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  have hsub : (S ×ˢ U) ⊆ (fun p : ℝ × E => p.2) ⁻¹' U := by intro p hp; exact hp.2
  have hfdw := ContDiffWithinAt.fderivWithin huncurry hg hud h_le ⟨hqS, hqU⟩ hsub
  have hcont := hfdw.continuousWithinAt
  refine hcont.congr ?_ ?_
  · intro p hp
    exact (fderivWithin_of_isOpen hU hp.2).symm
  · exact (fderivWithin_of_isOpen hU hqU).symm

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem hasFDerivAt_chartRepr_pathIntegral
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (α : M) {y₀ : E} (hy₀ : y₀ ∈ interior ((extChartAt I α).target : Set E)) :
    HasFDerivAt
      (fun y : E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α
        (fun z : M =>
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
        ((extChartAt I α).symm y))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E =>
          DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y)) y₀)
      y₀ := by
  classical
  set Gfn : ℝ → E → TensorRSModel r s ℝ E :=
    fun t y => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
      (I := I) r s α (fun z : M => (Φ t).toSection z) ((extChartAt I α).symm y) with hGfn
  set F : E → ℝ → TensorRSModel r s ℝ E := fun y t => Gfn t y with hF
  set F' : E → ℝ → E →L[ℝ] TensorRSModel r s ℝ E :=
    fun y t => fderiv ℝ (Gfn t) y with hF'
  have hInt_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have hInt_sub : interior ((extChartAt I α).target : Set E) ⊆ (extChartAt I α).target :=
    interior_subset
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hInt_open y₀ hy₀
  set ε2 : ℝ := ε / 2 with hε2
  have hε2_pos : 0 < ε2 := by positivity
  have hclosed_sub : Metric.closedBall y₀ ε2 ⊆ interior ((extChartAt I α).target : Set E) := by
    intro y hy
    apply hε_ball
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    calc dist y y₀ ≤ ε2 := hy
      _ < ε := by rw [hε2]; linarith
  have hball_sub : Metric.ball y₀ ε2 ⊆ interior ((extChartAt I α).target : Set E) :=
    (Metric.ball_subset_closedBall).trans hclosed_sub
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall y₀ ε2) :=
    isCompact_Icc.prod (isCompact_closedBall y₀ ε2)
  have hfderiv_cont : ContinuousOn
      (fun q : ℝ × E => F' q.2 q.1)
      (S ×ˢ interior ((extChartAt I α).target : Set E)) := by
    have := fderiv_chartRepr_jointContinuousOn (I := I) g₀ r s Φ S hS α
      (U := interior ((extChartAt I α).target : Set E)) hInt_open hInt_sub hjoint
    exact this
  have hfderiv_cont_swap : ContinuousOn
      (fun q : ℝ × E => F' q.2 q.1)
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall y₀ ε2) := by
    refine hfderiv_cont.mono ?_
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨hSI ((Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)).symm ▸ ht), hclosed_sub hy⟩
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hfderiv_cont_swap
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Metric.closedBall y₀ ε2, ‖F' y t‖ ≤ C := by
    intro t ht y hy
    exact hC (t, y) ⟨ht, hy⟩
  have hdiff_all : ∀ t : ℝ, t ∈ S → ∀ y ∈ interior ((extChartAt I α).target : Set E),
      HasFDerivAt (fun y => F y t) (F' y t) y := by
    intro t ht y hy
    have hy_tgt : y ∈ (extChartAt I α).target := hInt_sub hy
    have hjoint_at : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Gfn q.1 q.2) (S ×ˢ (extChartAt I α).target) (t, y) :=
      chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s Φ S α hjoint ht hy_tgt
    have hslice : ContDiffWithinAt ℝ ∞ (fun y' : E => Gfn t y')
        (extChartAt I α).target y := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun y' : E => (t, y'))
          (extChartAt I α).target y :=
        contDiffWithinAt_const.prodMk contDiffWithinAt_id
      have hmaps : Set.MapsTo (fun y' : E => (t, y')) (extChartAt I α).target
          (S ×ˢ (extChartAt I α).target) := fun y' hy' => ⟨ht, hy'⟩
      have hc := ContDiffWithinAt.comp (𝕜 := ℝ) (n := ∞)
        (g := fun q : ℝ × E => Gfn q.1 q.2) (f := fun y' : E => (t, y'))
        y hjoint_at hcomp hmaps
      exact hc
    have htgt_nhds : (extChartAt I α).target ∈ 𝓝 y :=
      Filter.mem_of_superset (hInt_open.mem_nhds hy) hInt_sub
    have hslice_at : ContDiffAt ℝ ∞ (fun y' : E => Gfn t y') y :=
      hslice.contDiffAt htgt_nhds
    exact (hslice_at.differentiableAt (by norm_num)).hasFDerivAt
  set μ : Measure ℝ := volume with hμ
  have hGfn_slice_cont : ∀ y ∈ interior ((extChartAt I α).target : Set E),
      ContinuousOn (fun t : ℝ => Gfn t y) (Set.uIcc (0:ℝ) 1) := by
    intro y hy
    have hy_tgt : y ∈ (extChartAt I α).target := hInt_sub hy
    intro t ht
    have hts : t ∈ S := hSI ht
    have hjoint_at : ContDiffWithinAt ℝ ∞
        (fun q : ℝ × E => Gfn q.1 q.2) (S ×ˢ (extChartAt I α).target) (t, y) :=
      chartRepr_euclid_jointContDiffWithinAt (I := I) g₀ r s Φ S α hjoint hts hy_tgt
    have hsliceT : ContDiffWithinAt ℝ ∞ (fun t' : ℝ => Gfn t' y) S t := by
      have hcomp : ContDiffWithinAt ℝ ∞ (fun t' : ℝ => (t', y)) S t :=
        contDiffWithinAt_id.prodMk contDiffWithinAt_const
      have hmaps : Set.MapsTo (fun t' : ℝ => (t', y)) S
          (S ×ˢ (extChartAt I α).target) := fun t' ht' => ⟨ht', hy_tgt⟩
      have hc := ContDiffWithinAt.comp (𝕜 := ℝ) (n := ∞)
        (g := fun q : ℝ × E => Gfn q.1 q.2) (f := fun t' : ℝ => (t', y))
        t hjoint_at hcomp hmaps
      exact hc
    have hsliceAt : ContDiffAt ℝ ∞ (fun t' : ℝ => Gfn t' y) t :=
      hsliceT.contDiffAt (hS.mem_nhds hts)
    exact hsliceAt.continuousAt.continuousWithinAt
  have hF_meas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (F y) (μ.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [hInt_open.mem_nhds hy₀] with y hy_mem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (hGfn_slice_cont y hy_mem).mono ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self
  have hF_int : IntervalIntegrable (F y₀) μ 0 1 :=
    (hGfn_slice_cont y₀ hy₀).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (F' y₀) (μ.restrict (Ι (0:ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    have hcont : ContinuousOn (fun t : ℝ => F' y₀ t) (Set.Icc (0:ℝ) 1) := by
      have hmapsto : Set.MapsTo (fun t : ℝ => (t, y₀))
          (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall y₀ ε2) :=
        fun t ht => ⟨ht, Metric.mem_closedBall_self hε2_pos.le⟩
      have hmap_cont : ContinuousOn (fun t : ℝ => (t, y₀)) (Set.Icc (0:ℝ) 1) :=
        (continuous_id.prodMk continuous_const).continuousOn
      exact (hfderiv_cont_swap.comp hmap_cont hmapsto)
    exact hcont.mono Set.Ioc_subset_Icc_self
  have h_bound : ∀ᵐ t ∂μ.restrict (Ι (0:ℝ) 1), ∀ y ∈ Metric.ball y₀ ε2, ‖F' y t‖ ≤ C := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro t ht y hy
    exact hbound t (Set.Ioc_subset_Icc_self ht) y (Metric.ball_subset_closedBall hy)
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) μ 0 1 :=
    intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂μ.restrict (Ι (0:ℝ) 1), ∀ y ∈ Metric.ball y₀ ε2,
      HasFDerivAt (fun y => F y t) (F' y t) y := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro t _ht y hy
    exact hdiff_all t (hSI (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact Set.Ioc_subset_Icc_self _ht))
      y (hball_sub hy)
  have hsmem : Metric.ball y₀ ε2 ∈ 𝓝 y₀ := Metric.ball_mem_nhds y₀ hε2_pos
  have hkey := hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := F) (F' := F') (bound := fun _ => C) (a := 0) (b := 1) (μ := μ) (x₀ := y₀)
    (s := Metric.ball y₀ ε2) hsmem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hLHSeq : (fun y : E => ∫ t in (0:ℝ)..1, F y t ∂μ) =
      (fun y : E => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α
        (fun z : M =>
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)
        ((extChartAt I α).symm y)) := by
    funext y
    rw [hF, hGfn]
    exact (chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint α
      ((extChartAt I α).symm y)).symm
  rw [hLHSeq] at hkey
  exact hkey

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem chartE_repr_slice_continuousOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (α x : M) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S) :
    ContinuousOn
      (fun t : ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) r s α (fun z : M => (Φ t).toSection z) x) (Set.uIcc (0:ℝ) 1) := by
  set L : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ x).comp
      (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap
    with hL
  have hm : ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.uIcc (0:ℝ) 1) :=
    (jointContMDiff_toModel_continuous_slice (I := I) g₀ r s Φ S hjoint x).mono hSI
  refine ContinuousOn.congr (L.continuous.comp_continuousOn hm) ?_
  intro t _
  change DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
      (I := I) r s α (fun z : M => (Φ t).toSection z) x = L (TensorRSSpace.toModel ((Φ t).toSection x))
  rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply, hL,
    ContinuousLinearMap.comp_apply]
  congr 1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem intervalIntegrable_slotInput
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hx_src : x ∈ (chartAt H x).source) (k : Fin r) :
    IntervalIntegrable
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x k)) volume 0 1 := by
  have hcont : ContinuousOn
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x k)) (Set.uIcc (0:ℝ) 1) := by
    have hbase := chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint x x hSI
    refine ContinuousOn.congr
      (((DifferentialGeometry.Integral.Connection.inputSlotChartKernel
        (I := I) g₀ r s x B.toFun k x).continuous).comp_continuousOn hbase) ?_
    intro t _
    change (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x k) =
        DifferentialGeometry.Integral.Connection.inputSlotChartKernel (I := I) g₀ r s x B.toFun k x
          (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) r s x (fun z : M => (Φ t).toSection z) x)
    rw [chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
      (fun z : M => (Φ t).toSection z) B.toFun hx_src k,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
  exact hcont.intervalIntegrable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem intervalIntegrable_slotOutput
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hx_src : x ∈ (chartAt H x).source) (l : Fin s) :
    IntervalIntegrable
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x l)) volume 0 1 := by
  have hcont : ContinuousOn
      (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x l)) (Set.uIcc (0:ℝ) 1) := by
    have hbase := chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint x x hSI
    refine ContinuousOn.congr
      (((DifferentialGeometry.Integral.Connection.outputSlotChartKernel
        (I := I) g₀ r s x B.toFun l x).continuous).comp_continuousOn hbase) ?_
    intro t _
    change (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') x).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ x
            (fun z : M => (Φ t).toSection z) B.toFun x l) =
        DifferentialGeometry.Integral.Connection.outputSlotChartKernel (I := I) g₀ r s x B.toFun l x
          (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) r s x (fun z : M => (Φ t).toSection z) x)
    rw [chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s x
      (fun z : M => (Φ t).toSection z) B.toFun hx_src l,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
  exact hcont.intervalIntegrable

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covApply_chartE_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun
          (fun z : M =>
            (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection z)) x =
      ∫ t in (0 : ℝ)..1,
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x := by
  classical
  set α : M := x with hα
  set φ := extChartAt I α with hφ
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet (I := I) α
  have hx_src : x ∈ (chartAt H α).source :=
    DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_mem_chartAt_source
      (I := I) hx_good
  have hx_tgt : φ x ∈ φ.target := φ.map_source (by rw [hφ, extChartAt_source]; exact hx_src)
  have hx_round : φ.symm (φ x) = x := φ.left_inv (by rw [hφ, extChartAt_source]; exact hx_src)
  have hx_int : φ x ∈ interior ((φ).target : Set E) := by
    rw [hφ, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hx_tgt
  set W : SmoothCcTensor g₀ r s :=
    pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint with hW
  have hform_W := chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
    g₀ r s α W B hx_tgt (by rw [hx_round]; exact hx_good)
  have hform_Φ : ∀ t : ℝ,
      (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) ∘ φ.symm) (φ x) =
        fderiv ℝ
          (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
            (fun z : M => (Φ t).toSection z) ∘ φ.symm) (φ x)
          (DifferentialGeometry.Integral.Connection.trivToE (I := I) α (φ.symm (φ x))
            (B.toFun (φ.symm (φ x))))
        + ∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ (φ.symm (φ x))
              (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun (φ.symm (φ x)) k)
        - ∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ (φ.symm (φ x))
              (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun (φ.symm (φ x)) l) := fun t =>
    chart_pulled_covApply_explicit_formula_target_smoothCc (I := I) (M := M)
      g₀ r s α (Φ t) B hx_tgt (by rw [hx_round]; exact hx_good)
  set dir : E := DifferentialGeometry.Integral.Connection.trivToE (I := I) α x (B.toFun x) with hdir
  set Wchart : E → TensorRSModel r s ℝ E :=
    fun y => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => W.toSection z) (φ.symm y) with hWchart
  set Φchart : ℝ → E → TensorRSModel r s ℝ E :=
    fun t y => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s α
      (fun z : M => (Φ t).toSection z) (φ.symm y) with hΦchart
  have hfderiv_comm :
      fderiv ℝ Wchart (φ x) dir =
        ∫ t in (0 : ℝ)..1, fderiv ℝ (Φchart t) (φ x) dir := by
    have hhas := hasFDerivAt_chartRepr_pathIntegral (I := I) g₀ r s Φ S hS hSI hjoint α hx_int
    have hfd : fderiv ℝ Wchart (φ x) =
        ∫ t in (0 : ℝ)..1, fderiv ℝ (Φchart t) (φ x) := hhas.fderiv
    have hIIfderiv : IntervalIntegrable
        (fun t : ℝ => fderiv ℝ (Φchart t) (φ x)) volume 0 1 := by
      have hcont : ContinuousOn (fun t : ℝ => fderiv ℝ (Φchart t) (φ x))
          (Set.uIcc (0 : ℝ) 1) := by
        have hjc := fderiv_chartRepr_jointContinuousOn (I := I) g₀ r s Φ S hS α
          (U := interior ((φ).target : Set E)) isOpen_interior interior_subset hjoint
        have hmaps : Set.MapsTo (fun t : ℝ => (t, φ x)) (Set.uIcc (0:ℝ) 1)
            (S ×ˢ interior ((φ).target : Set E)) := fun t ht => ⟨hSI ht, hx_int⟩
        exact hjc.comp ((continuous_id.prodMk continuous_const).continuousOn) hmaps
      exact hcont.intervalIntegrable
    rw [hfd, ContinuousLinearMap.intervalIntegral_apply hIIfderiv dir]
  have hWchart_eq : ∀ y : E, Wchart y =
      ∫ t in (0 : ℝ)..1, Φchart t y := by
    intro y
    rw [hWchart, hΦchart]
    exact chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint α (φ.symm y)
  have hinput_comm : ∀ k : Fin r,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
        (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
          (fun z : M => W.toSection z) B.toFun x k) =
      ∫ t in (0 : ℝ)..1,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x k) := by
    intro k
    have hIIΦ : IntervalIntegrable
        (fun t : ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) r s α (fun z : M => (Φ t).toSection z) x) volume 0 1 :=
      (chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint α x hSI).intervalIntegrable
    rw [chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
      (fun z : M => W.toSection z) B.toFun hx_src k,
      ← DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply (I := I) r s α
        (fun z : M => W.toSection z) x,
      chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint α x]
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (DifferentialGeometry.Integral.Connection.inputSlotChartKernel (I := I) g₀ r s α B.toFun k x) hIIΦ]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [chartTensorRSInputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
      (fun z : M => (Φ t).toSection z) B.toFun hx_src k,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
  have houtput_comm : ∀ l : Fin s,
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
        (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
          (fun z : M => W.toSection z) B.toFun x l) =
      ∫ t in (0 : ℝ)..1,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x l) := by
    intro l
    have hIIΦ : IntervalIntegrable
        (fun t : ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) r s α (fun z : M => (Φ t).toSection z) x) volume 0 1 :=
      (chartE_repr_slice_continuousOn (I := I) g₀ r s Φ S hjoint α x hSI).intervalIntegrable
    rw [chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
      (fun z : M => W.toSection z) B.toFun hx_src l,
      ← DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply (I := I) r s α
        (fun z : M => W.toSection z) x,
      chartRepr_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint α x]
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (DifferentialGeometry.Integral.Connection.outputSlotChartKernel (I := I) g₀ r s α B.toFun l x) hIIΦ]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [chartTensorRSOutputSlotCorrection_chart_kernel_factorization (I := I) (M := M) g₀ r s α
      (fun z : M => (Φ t).toSection z) B.toFun hx_src l,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
  have hLHS_eq : DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => W.toSection z)) x =
      fderiv ℝ Wchart (φ x) dir
        + (∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
                (fun z : M => W.toSection z) B.toFun x k))
        - (∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
                (fun z : M => W.toSection z) B.toFun x l)) := by
    have h := hform_W
    rw [← hφ] at h
    simp only [Function.comp_apply] at h
    rw [hx_round] at h
    rw [hWchart, hdir]
    exact h
  have hRHS_eq : ∀ t : ℝ,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z)) x =
      fderiv ℝ (Φchart t) (φ x) dir
        + (∑ k : Fin r,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun x k))
        - (∑ l : Fin s,
            (trivializationAt (TensorRSModel r s ℝ E)
                (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
              (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
                (fun z : M => (Φ t).toSection z) B.toFun x l)) := by
    intro t
    have h := hform_Φ t
    simp only [Function.comp_apply] at h
    rw [hx_round] at h
    rw [hΦchart, hdir]
    exact h
  rw [hLHS_eq, hfderiv_comm]
  have hsum_input : (∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
            (fun z : M => W.toSection z) B.toFun x k)) =
      ∫ t in (0 : ℝ)..1, ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x k) := by
    rw [intervalIntegral.integral_finset_sum]
    · exact Finset.sum_congr rfl (fun k _ => hinput_comm k)
    · intro k _
      exact (intervalIntegrable_slotInput (I := I) g₀ r s Φ S hjoint B x hSI hx_src k)
  have hsum_output : (∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
            (fun z : M => W.toSection z) B.toFun x l)) =
      ∫ t in (0 : ℝ)..1, ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x l) := by
    rw [intervalIntegral.integral_finset_sum]
    · exact Finset.sum_congr rfl (fun l _ => houtput_comm l)
    · intro l _
      exact (intervalIntegrable_slotOutput (I := I) g₀ r s Φ S hjoint B x hSI hx_src l)
  rw [hsum_input, hsum_output]
  have hII_fderivApply : IntervalIntegrable
      (fun t : ℝ => fderiv ℝ (Φchart t) (φ x) dir) volume 0 1 := by
    have hcont : ContinuousOn (fun t : ℝ => fderiv ℝ (Φchart t) (φ x) dir)
        (Set.uIcc (0 : ℝ) 1) := by
      have hfc := fderiv_chartRepr_jointContinuousOn (I := I) g₀ r s Φ S hS α
        (U := interior ((φ).target : Set E)) isOpen_interior interior_subset hjoint
      have hcomp : ContinuousOn (fun t : ℝ => fderiv ℝ (Φchart t) (φ x))
          (Set.uIcc (0 : ℝ) 1) := by
        refine ContinuousOn.comp (g := fun q : ℝ × E => fderiv ℝ (Φchart q.1) q.2)
          (f := fun t : ℝ => (t, φ x)) hfc
          ((continuous_id.prodMk continuous_const).continuousOn) ?_
        intro t ht
        exact ⟨hSI ht, hx_int⟩
      exact (ContinuousLinearMap.apply ℝ (TensorRSModel r s ℝ E) dir).continuous.comp_continuousOn hcomp
    exact hcont.intervalIntegrable
  have hII_inputSum : IntervalIntegrable
      (fun t : ℝ => ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x k)) volume 0 1 := by
    have hsum := IntervalIntegrable.sum (Finset.univ : Finset (Fin r))
      (fun k _ => intervalIntegrable_slotInput (I := I) g₀ r s Φ S hjoint B x hSI hx_src k)
    have heq : (fun t : ℝ => ∑ k : Fin r,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x k)) =
        ∑ k : Fin r, fun t : ℝ =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
            (DifferentialGeometry.Integral.Connection.chartTensorRSInputSlotCorrection (I := I) r s g₀ α
              (fun z : M => (Φ t).toSection z) B.toFun x k) := by
      funext t; rw [Finset.sum_apply]
    rw [heq]; exact hsum
  have hII_outputSum : IntervalIntegrable
      (fun t : ℝ => ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x l)) volume 0 1 := by
    have hsum := IntervalIntegrable.sum (Finset.univ : Finset (Fin s))
      (fun l _ => intervalIntegrable_slotOutput (I := I) g₀ r s Φ S hjoint B x hSI hx_src l)
    have heq : (fun t : ℝ => ∑ l : Fin s,
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
          (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
            (fun z : M => (Φ t).toSection z) B.toFun x l)) =
        ∑ l : Fin s, fun t : ℝ =>
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y' : M => TensorRSSpace r s I y') α).continuousLinearMapAt ℝ x
            (DifferentialGeometry.Integral.Connection.chartTensorRSOutputSlotCorrection (I := I) r s g₀ α
              (fun z : M => (Φ t).toSection z) B.toFun x l) := by
      funext t; rw [Finset.sum_apply]
    rw [heq]; exact hsum
  rw [← intervalIntegral.integral_add hII_fderivApply hII_inputSum,
    ← intervalIntegral.integral_sub (hII_fderivApply.add hII_inputSum) hII_outputSum]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hRHS_eq t]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_pathIntegralCoeffField_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (v : E) :
    TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint) x v) =
      ∫ t in (0 : ℝ)..1,
        TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) := by
  classical
  set W : SmoothCcTensor g₀ r s :=
    pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint with hW
  obtain ⟨B, hB⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (show TangentSpace I x from v)
  have hBx : B.toFun x = v := hB
  set e := trivializationAt (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) x with he
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hcomm := covApply_chartE_pathIntegral_comm (I := I) g₀ r s Φ S hS hSI hjoint B x
  have hjapply := covApply_section_jointContMDiffOn (I := I) g₀ r s Φ S B hjoint
  have hfibre_model : ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) := by
    have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) :=
      (contMDiff_const).prodMk contMDiff_id
    have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) (Set.uIcc (0:ℝ) 1) ((Set.univ : Set M) ×ˢ S) :=
      fun t ht => ⟨Set.mem_univ _, hSI ht⟩
    have hsliceTot : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun t : ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) :=
      hjapply.comp hmap.contMDiffOn hmaps
    have hchart : ContinuousOn (fun t : ℝ =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) := by
      have hcoord : ContinuousOn (fun t : ℝ =>
          (e (TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) x
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
              B.toFun (fun z : M => (Φ t).toSection z) x))).2) (Set.uIcc (0:ℝ) 1) :=
        continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp hsliceTot.continuousOn
          (fun t _ => e.mem_source.mpr hxbase))
      refine hcoord.congr (fun t _ => ?_)
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hxbase]
    set K' : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
      (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap.comp
        (e.symmL ℝ x) with hK'
    refine ContinuousOn.congr (K'.continuous.comp_continuousOn hchart) ?_
    intro t _
    change TensorRSSpace.toModel
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x) =
        K' ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x))
    rw [hK', ContinuousLinearMap.comp_apply,
      Bundle.Trivialization.symmL_continuousLinearMapAt e hxbase]
    rfl
  set K : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap.comp
      (e.symmL ℝ x) with hK
  have hKbridge : ∀ (Y : SmoothCcTensor g₀ r s),
      TensorRSSpace.toModel
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => Y.toSection z) x) =
      K (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => Y.toSection z)) x) := by
    intro Y
    rw [hK, ContinuousLinearMap.comp_apply,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
      Bundle.Trivialization.symmL_continuousLinearMapAt e hxbase]
    rfl
  have hII_chartΦ : IntervalIntegrable
      (fun t : ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z)) x) volume 0 1 := by
    have hcont : ContinuousOn
        (fun t : ℝ => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x) (Set.uIcc (0:ℝ) 1) := by
      set Lc : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x).comp
          (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap
        with hLc
      refine ContinuousOn.congr (Lc.continuous.comp_continuousOn hfibre_model) ?_
      intro t _
      change DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x =
          Lc (TensorRSSpace.toModel
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
                B.toFun (fun z : M => (Φ t).toSection z) x))
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply, hLc,
        ContinuousLinearMap.comp_apply]
      congr 1
    exact hcont.intervalIntegrable
  have hgoalL : TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x v) =
      K (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => W.toSection z)) x) := by
    rw [← hKbridge W]
    change TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x v) =
        TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x (B.toFun x))
    rw [hBx]
  have hgoalΦ : ∀ t : ℝ,
      TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) =
      K (DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) r s x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z)) x) := by
    intro t
    rw [← hKbridge (Φ t)]
    change TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) =
        TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (B.toFun x))
    rw [hBx]
  rw [hgoalL, hcomm, ← ContinuousLinearMap.intervalIntegral_comp_comm K hII_chartΦ]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  exact (hgoalΦ t).symm

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGradParametric_tcd_toModel_continuousOn
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (v : E) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S) :
    ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v))
      (Set.uIcc (0:ℝ) 1) := by
  classical
  obtain ⟨B, hB⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (show TangentSpace I x from v)
  have hBx : B.toFun x = v := hB
  set e := trivializationAt (TensorRSModel r s ℝ E) (fun y : M => TensorRSSpace r s I y) x with he
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hjapply := covApply_section_jointContMDiffOn (I := I) g₀ r s Φ S B hjoint
  have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) :=
    (contMDiff_const).prodMk contMDiff_id
  have hmaps : Set.MapsTo (fun t : ℝ => (x, t)) (Set.uIcc (0:ℝ) 1) ((Set.univ : Set M) ×ˢ S) :=
    fun t ht => ⟨Set.mem_univ _, hSI ht⟩
  have hsliceTot : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun t : ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) :=
    hjapply.comp hmap.contMDiffOn hmaps
  have hchart : ContinuousOn (fun t : ℝ =>
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x)) (Set.uIcc (0:ℝ) 1) := by
    have hcoord : ContinuousOn (fun t : ℝ =>
        (e (TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) x
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
            B.toFun (fun z : M => (Φ t).toSection z) x))).2) (Set.uIcc (0:ℝ) 1) :=
      continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp hsliceTot.continuousOn
        (fun t _ => e.mem_source.mpr hxbase))
    refine hcoord.congr (fun t _ => ?_)
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.coe_linearMapAt_of_mem _ hxbase]
  set K' : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) r s x).toContinuousLinearMap.comp
      (e.symmL ℝ x) with hK'
  refine ContinuousOn.congr (K'.continuous.comp_continuousOn hchart) ?_
  intro t _
  change TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x v) =
      K' ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) x).continuousLinearMapAt ℝ x
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g₀))
          B.toFun (fun z : M => (Φ t).toSection z) x))
  rw [hK', ContinuousLinearMap.comp_apply,
    Bundle.Trivialization.symmL_continuousLinearMapAt e hxbase, ← hBx]
  rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem toModel_covGrad_pathIntegralCoeffField_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hjg : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r s (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) :
    TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g₀ r s
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint)).toSection x) =
      ∫ t in (0 : ℝ)..1,
        TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ r s :=
    pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint with hW
  apply ContinuousLinearMap.ext
  intro D
  apply ContinuousMultilinearMap.ext
  intro v
  have hkeyW : (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s W).toSection x) D) v =
      (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s W x (v 0)) D)
        (Matrix.vecTail v) :=
    covGrad_toSection_apply_eval (I := I) (M := M) g₀ r s W x D v
  have hkeyΦ : ∀ t : ℝ,
      (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x) D) v =
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)) D)
          (Matrix.vecTail v) := fun t =>
    covGrad_toSection_apply_eval (I := I) (M := M) g₀ r s (Φ t) x D v
  have hcore := tensorCovDerivAt_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint x (v 0)
  have hcontcd : ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)))
      (Set.uIcc (0:ℝ) 1) :=
    covGradParametric_tcd_toModel_continuousOn (I := I) g₀ r s Φ S hjoint x (v 0) hSI
  have hIIcd : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)))
      volume 0 1 := hcontcd.intervalIntegrable
  have hIIcdD : IntervalIntegrable
      (fun t : ℝ =>
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0))) D)
      volume 0 1 := by
    have hc : ContinuousOn
        ((fun w : TensorRSModel r s ℝ E => w D) ∘
          (fun t : ℝ => TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0))))
        (Set.uIcc (0:ℝ) 1) :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) D).continuous.comp_continuousOn hcontcd
    exact hc.intervalIntegrable
  have hcontgrad : ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x))
      (Set.uIcc (0:ℝ) 1) :=
    (jointContMDiff_toModel_continuous_slice (I := I) g₀ r (s + 1)
      (fun t => covGrad (I := I) (M := M) g₀ r s (Φ t)) S hjg x).mono hSI
  have hIIgrad : IntervalIntegrable
      (fun t : ℝ => TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x))
      volume 0 1 := hcontgrad.intervalIntegrable
  have hIIgradD : IntervalIntegrable
      (fun t : ℝ => (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x)) D)
      volume 0 1 := by
    have hc : ContinuousOn
        ((fun w : TensorRSModel r (s + 1) ℝ E => w D) ∘
          (fun t : ℝ => TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x)))
        (Set.uIcc (0:ℝ) 1) :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel (s + 1) ℝ E) D).continuous.comp_continuousOn hcontgrad
    exact hc.intervalIntegrable
  have hLHSval : ((TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s W).toSection x)) D) v =
      ∫ t in (0:ℝ)..1,
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g₀ r s (Φ t) x (v 0)) D)
          (Matrix.vecTail v) := by
    rw [hkeyW, hcore, ContinuousLinearMap.intervalIntegral_apply hIIcd D]
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ (Matrix.vecTail v)) hIIcdD).symm
  have hRHSval : ((∫ t in (0:ℝ)..1,
        TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x)) D) v =
      ∫ t in (0:ℝ)..1,
        (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g₀ r s (Φ t)).toSection x) D) v := by
    rw [ContinuousLinearMap.intervalIntegral_apply hIIgrad D]
    exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (s + 1) => E) ℝ v) hIIgradD).symm
  rw [hLHSval, hRHSval]
  refine (intervalIntegral.integral_congr (fun t _ => ?_))
  exact (hkeyΦ t).symm

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hjg : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + 1) I z) q.1
        ((covGrad (I := I) (M := M) g₀ r s (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    covGrad (I := I) (M := M) g₀ r s
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (s + 1)
        (fun t => covGrad (I := I) (M := M) g₀ r s (Φ t)) S hS hSI hjg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply Tensor0SBundle.TensorRSSpace.toModel_injective
  change TensorRSSpace.toModel
      ((covGrad (I := I) (M := M) g₀ r s
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint)).toSection x) =
    TensorRSSpace.toModel
      ((pathIntegralCoeffField (I := I) (M := M) g₀ r (s + 1)
        (fun t => covGrad (I := I) (M := M) g₀ r s (Φ t)) S hS hSI hjg).toSection x)
  rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]
  exact toModel_covGrad_pathIntegralCoeffField_eq (I := I) g₀ r s Φ S hS hSI hjoint hjg x

end PathIntegralComm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
