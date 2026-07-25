import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Comp


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

universe u

section ModelKernel

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]


private theorem tube_bound {W : Type*} [NormedAddCommGroup W] (Φ : H × ℝ → W) (U : Set H)
    (hU : IsOpen U) (a b : ℝ) (S : Set ℝ) (hSI : Set.uIcc a b ⊆ S) (y₀ : H) (hy₀ : y₀ ∈ U)
    (hΦ : ContinuousOn Φ (U ×ˢ S)) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 y₀, ∀ t ∈ Ι a b, ‖Φ (y, t)‖ ≤ C := by
  obtain ⟨K, ⟨hKnhds, hKcomp⟩, hKU⟩ := (compact_basis_nhds y₀).mem_iff.1 (hU.mem_nhds hy₀)
  have hcompact : IsCompact (K ×ˢ Set.uIcc a b) := hKcomp.prod isCompact_uIcc
  have hsub : K ×ˢ Set.uIcc a b ⊆ U ×ˢ S := fun p hp => ⟨hKU hp.1, hSI hp.2⟩
  obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn (hΦ.mono hsub).norm).bddAbove
  exact ⟨C, by filter_upwards [hKnhds] with y hyK t ht
                  using hC ⟨(y,t), ⟨hyK, uIoc_subset_uIcc ht⟩, rfl⟩⟩


omit [NormedSpace ℝ H] [FiniteDimensional ℝ H] in
private theorem slice_continuousOn {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : H × ℝ → F) (U : Set H) (hU : IsOpen U) (S : Set ℝ) (hS : IsOpen S)
    (hGc : ContinuousOn G (U ×ˢ S)) (y' : H) (hy' : y' ∈ U) :
    ContinuousOn (fun t : ℝ => G (y', t)) S := by
  intro t ht
  refine (hGc.continuousAt ((hU.prod hS).mem_nhds ⟨hy', ht⟩)).comp_continuousWithinAt ?_
  exact (continuousWithinAt_const.prodMk continuousWithinAt_id)


omit [FiniteDimensional ℝ H] in
private theorem fderiv_fst_contDiffOn {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : H × ℝ → F) (U : Set H) (hU : IsOpen U) (S : Set ℝ) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G (U ×ˢ S)) :
    ContDiffOn ℝ ∞ (fun p : H × ℝ => fderiv ℝ (fun z => G (z, p.2)) p.1) (U ×ˢ S) := by
  have hopen : IsOpen (U ×ˢ S) := hU.prod hS
  rw [hopen.contDiffOn_iff] at hG ⊢
  intro p hp
  apply ContDiffAt.fderiv (n := (∞ : WithTop ℕ∞)) (m := (∞ : WithTop ℕ∞))
  · exact (hG hp).comp _
      (by fun_prop : ContDiffAt ℝ ∞ (fun w : (H × ℝ) × H => (w.2, w.1.2)) (p, p.1))
  · fun_prop
  · exact le_refl _

private theorem contDiffAt_param_aux :
    ∀ (n : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (G : H × ℝ → F) (U : Set H) (_hU : IsOpen U) (a b : ℝ) (S : Set ℝ) (_hS : IsOpen S)
      (_hSI : Set.uIcc a b ⊆ S) (y₀ : H) (_hy₀ : y₀ ∈ U)
      (_hG : ContDiffOn ℝ ∞ G (U ×ˢ S)),
    ContDiffAt ℝ (n : WithTop ℕ∞) (fun y => ∫ t in a..b, G (y, t)) y₀ := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ G U hU a b S hS hSI y₀ hy₀ hG
    have hGc := hG.continuousOn
    have hopen : IsOpen (U ×ˢ S) := hU.prod hS
    rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiffAt_zero]
    refine ⟨U, hU.mem_nhds hy₀, fun y hy => ?_⟩
    apply ContinuousAt.continuousWithinAt
    obtain ⟨C, hCbound⟩ := tube_bound G U hU a b S hSI y hy hGc
    apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C)
    · filter_upwards [hU.mem_nhds hy] with y' hy'
      exact ((slice_continuousOn G U hU S hS hGc y' hy').mono
        (fun t ht => hSI (Set.uIoc_subset_uIcc ht))).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hCbound] with y' hy' using ae_of_all _ (fun t ht => hy' t ht)
    · exact intervalIntegrable_const
    · refine ae_of_all _ (fun t ht => ?_)
      exact (hGc.continuousAt (hopen.mem_nhds ⟨hy, hSI (Set.uIoc_subset_uIcc ht)⟩)).comp
        (by fun_prop)
  | succ k ih =>
    intro F _ _ _ G U hU a b S hS hSI y₀ hy₀ hG
    have hopen : IsOpen (U ×ˢ S) := hU.prod hS
    have hGc := hG.continuousOn
    set Gp : H × ℝ → (H →L[ℝ] F) := fun p => fderiv ℝ (fun z => G (z, p.2)) p.1 with hGpdef
    have hGp_cd : ContDiffOn ℝ ∞ Gp (U ×ˢ S) := fderiv_fst_contDiffOn G U hU S hS hG
    have hGpc := hGp_cd.continuousOn
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; ring,
      contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun y => ∫ t in a..b, Gp (y, t), ⟨U, hU.mem_nhds hy₀, fun y hy => ?_⟩,
      ih Gp U hU a b S hS hSI y₀ hy₀ hGp_cd⟩
    obtain ⟨C, hCbound⟩ := tube_bound Gp U hU a b S hSI y hy hGpc
    set s : Set H := {y' | ∀ t ∈ Ι a b, ‖Gp (y', t)‖ ≤ C} ∩ U with hsdef
    have hsnhds : s ∈ 𝓝 y := Filter.inter_mem hCbound (hU.mem_nhds hy)
    have hsU : s ⊆ U := Set.inter_subset_right
    have hIcc : (∀ t ∈ Ι a b, t ∈ S) := fun t ht => hSI (Set.uIoc_subset_uIcc ht)
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun y t => G (y, t)) (F' := fun y t => Gp (y, t)) (bound := fun _ => C)
      (x₀ := y) (s := s) (a := a) (b := b) hsnhds
      ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hU.mem_nhds hy] with y' hy'
      exact ((slice_continuousOn G U hU S hS hGc y' hy').mono
        (fun t ht => hSI (Set.uIoc_subset_uIcc ht))).aestronglyMeasurable measurableSet_uIoc
    · exact ((slice_continuousOn G U hU S hS hGc y hy).mono hSI).intervalIntegrable
    · exact ((slice_continuousOn Gp U hU S hS hGpc y hy).mono
        (fun t ht => hSI (Set.uIoc_subset_uIcc ht))).aestronglyMeasurable measurableSet_uIoc
    · rw [ae_restrict_iff' measurableSet_uIoc]
      exact ae_of_all _ (fun t ht y' hy' => hy'.1 t ht)
    · rw [ae_restrict_iff' measurableSet_uIoc]
      refine ae_of_all _ (fun t ht y' hy' => ?_)
      have hslice : ContDiffAt ℝ ∞ (fun z => G (z, t)) y' :=
        (hG.contDiffAt (hopen.mem_nhds ⟨hsU hy', hIcc t ht⟩)).comp _
          (by fun_prop : ContDiffAt ℝ ∞ (fun z : H => (z, t)) y')
      exact (hslice.differentiableAt (by simp)).hasFDerivAt

private theorem contDiffAt_param {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (G : H × ℝ → F) (U : Set H) (hU : IsOpen U)
    (a b : ℝ) (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc a b ⊆ S) (y₀ : H) (hy₀ : y₀ ∈ U)
    (hG : ContDiffOn ℝ ∞ G (U ×ˢ S)) :
    ContDiffAt ℝ ∞ (fun y => ∫ t in a..b, G (y, t)) y₀ := by
  rw [contDiffAt_infty]
  exact fun n => contDiffAt_param_aux n G U hU a b S hS hSI y₀ hy₀ hG

end ModelKernel

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem contMDiffAt_manifold_param {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (g : M × ℝ → F) (a b : ℝ) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc a b ⊆ S) (V : Set M) (hV : IsOpen V) (x₀ : M) (hx₀ : x₀ ∈ V)
    (hg : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ g (V ×ˢ S)) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun x => ∫ t in a..b, g (x, t)) x₀ := by
  rw [contMDiffAt_iff_source, I.range_eq_univ, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  set chart := extChartAt I x₀ with hchart
  set U' : Set E := chart.target ∩ chart.symm ⁻¹' V with hU'def
  have hsymmCont : ContinuousOn chart.symm chart.target := continuousOn_extChartAt_symm x₀
  have hU'open : IsOpen U' := hsymmCont.isOpen_inter_preimage (isOpen_extChartAt_target x₀) hV
  have hy₀mem : chart x₀ ∈ U' := by
    refine ⟨mem_extChartAt_target x₀, ?_⟩
    simp only [Set.mem_preimage]
    rw [hchart, extChartAt_to_inv]
    exact hx₀
  have hG : ContDiffOn ℝ ∞ (fun p : E × ℝ => g (chart.symm p.1, p.2)) (U' ×ˢ S) := by
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ chart.symm chart.target := contMDiffOn_extChartAt_symm x₀
    have hsymmU' : ContMDiffOn 𝓘(ℝ, E) I ∞ chart.symm U' := hsymm.mono Set.inter_subset_left
    have hfst : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ (Prod.fst : E × ℝ → E)
        (U' ×ˢ S) := contDiff_fst.contMDiff.contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) ∞ (Prod.snd : E × ℝ → ℝ)
        (U' ×ˢ S) := contDiff_snd.contMDiff.contMDiffOn
    have hφ : ContMDiffOn 𝓘(ℝ, E × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun p : E × ℝ => (chart.symm p.1, p.2)) (U' ×ˢ S) :=
      (hsymmU'.comp hfst (fun p hp => hp.1)).prodMk hsnd
    have hφmaps : Set.MapsTo (fun p : E × ℝ => (chart.symm p.1, p.2)) (U' ×ˢ S)
        (V ×ˢ S) := by
      rintro ⟨y, t⟩ ⟨hy, ht⟩; exact ⟨hy.2, ht⟩
    exact (hg.comp hφ hφmaps).contDiffOn
  have hkey := contDiffAt_param (H := E) (F := F)
    (fun p : E × ℝ => g (chart.symm p.1, p.2)) U' hU'open a b S hS hSI (chart x₀) hy₀mem hG
  refine hkey.congr_of_eventuallyEq ?_
  filter_upwards [hU'open.mem_nhds hy₀mem] with y hy
  rfl

def pathIntegralFib (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (x : M) : TensorRSSpace r s I x :=
  TensorRSSpace.ofModel (∫ t in (0 : ℝ)..1, (TensorRSSpace.toModel ((Φ t).toSection x)))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma pathIntegralFib_toModel (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (x : M) :
    TensorRSSpace.toModel (pathIntegralFib (I := I) (M := M) g₀ r s Φ x) =
      ∫ t in (0 : ℝ)..1, (TensorRSSpace.toModel ((Φ t).toSection x)) := by
  rw [pathIntegralFib, TensorRSSpace.toModel_ofModel]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_pathIntegralFib_of_jointContMDiff
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))
      ((univ : Set M) ×ˢ S)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (pathIntegralFib (I := I) (M := M) g₀ r s Φ x)) := by
  intro x₀
  rw [Bundle.contMDiffAt_section]
  set e := trivializationAt (TensorRSModel r s ℝ E) (fun z : M => TensorRSSpace r s I z) x₀ with hedef
  set g : M × ℝ → TensorRSModel r s ℝ E :=
    fun p : M × ℝ => (e ⟨p.1, (Φ p.2).toSection p.1⟩).2 with hgdef
  have hbase : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hbaseOpen : IsOpen e.baseSet := e.open_baseSet
  have hgContMDiffOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel r s ℝ E) ∞ g
      (e.baseSet ×ˢ S) := by
    intro p hp
    have hsource : (TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1)) ∈ e.source := by
      rw [Trivialization.mem_source]; exact hp.1
    have hjp : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
        ((univ : Set M) ×ˢ S) p := hjoint p ⟨mem_univ _, hp.2⟩
    have hjpAt : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1)) p :=
      hjp.contMDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _, hp.2⟩)
    exact ((e.contMDiffAt_iff (f := fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
          (x₀ := p) hsource).1 hjpAt).2.contMDiffWithinAt
  have hintegral : ContMDiffAt I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun x => ∫ t in (0:ℝ)..1, g (x, t)) x₀ :=
    contMDiffAt_manifold_param g 0 1 S hS hSI e.baseSet hbaseOpen x₀ hbase hgContMDiffOn
  refine hintegral.congr_of_eventuallyEq ?_
  filter_upwards [hbaseOpen.mem_nhds hbase] with x hx
  have hgx_cont : ContinuousOn (fun t : ℝ => g (x, t)) S := by
    intro t ht
    have hgAt : ContinuousAt g (x, t) :=
      (hgContMDiffOn (x, t) ⟨hx, ht⟩).continuousWithinAt.continuousAt
        ((hbaseOpen.prod hS).mem_nhds ⟨hx, ht⟩)
    exact (hgAt.comp (by fun_prop : ContinuousAt (fun t : ℝ => (x, t)) t)).continuousWithinAt
  set Lx := e.continuousLinearEquivAt ℝ x hx with hLx
  have hreadoff : ∀ T : TensorRSSpace r s I x, (e ⟨x, T⟩).2 = Lx T := fun T => rfl
  have hgx_eq : (fun t : ℝ => g (x, t)) = (fun t : ℝ => Lx ((Φ t).toSection x)) := by
    funext t
    change (e ⟨x, (Φ t).toSection x⟩).2 = Lx ((Φ t).toSection x)
    rw [hreadoff]
  have hslice_cont : ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) S := by
    have hLxslice : ContinuousOn (fun t : ℝ => Lx ((Φ t).toSection x)) S := hgx_eq ▸ hgx_cont
    have hfibre : ContinuousOn (fun t : ℝ => ((Φ t).toSection x : TensorRSSpace r s I x)) S := by
      refine (Lx.symm.continuous.comp_continuousOn hLxslice).congr (fun t _ => ?_)
      exact (Lx.symm_apply_apply _).symm
    exact (tensorRSSpace_continuousLinearEquiv (I := I) r s x).continuous.comp_continuousOn hfibre
  have hIIm : IntervalIntegrable (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      volume 0 1 := (hslice_cont.mono hSI).intervalIntegrable
  change (e ⟨x, pathIntegralFib (I := I) (M := M) g₀ r s Φ x⟩).2 = ∫ t in (0:ℝ)..1, g (x, t)
  rw [hreadoff]
  set K : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E :=
    (Lx.toContinuousLinearMap).comp
      (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap with hK
  rw [pathIntegralFib]
  have hLxofM : Lx (TensorRSSpace.ofModel (I := I) (x := x)
      (∫ t in (0:ℝ)..1, TensorRSSpace.toModel ((Φ t).toSection x)))
      = K (∫ t in (0:ℝ)..1, TensorRSSpace.toModel ((Φ t).toSection x)) := rfl
  rw [hLxofM]
  have hRHS : (fun t : ℝ => g (x, t))
      = (fun t : ℝ => K (TensorRSSpace.toModel ((Φ t).toSection x))) := by
    funext t
    change (e ⟨x, (Φ t).toSection x⟩).2 = K (TensorRSSpace.toModel ((Φ t).toSection x))
    rw [hreadoff, hK, ContinuousLinearMap.comp_apply]
    change Lx ((Φ t).toSection x) = Lx _
    rw [show (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap
          (TensorRSSpace.toModel ((Φ t).toSection x)) = (Φ t).toSection x from
        (tensorRSSpace_continuousLinearEquiv (I := I) r s x).symm_apply_apply _]
  rw [hRHS, ContinuousLinearMap.intervalIntegral_comp_comm K hIIm]

def pathIntegralCoeffField (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))
      ((univ : Set M) ×ˢ S)) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M => pathIntegralFib (I := I) (M := M) g₀ r s Φ x
      contMDiff_toFun :=
        contMDiff_pathIntegralFib_of_jointContMDiff (I := I) (M := M) g₀ r s Φ S hS hSI hjoint }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma pathIntegralCoeffField_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))
      ((univ : Set M) ×ˢ S))
    (x : M) :
    (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x =
      pathIntegralFib (I := I) (M := M) g₀ r s Φ x := rfl


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma pathIntegralCoeffField_toModel (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 ((Φ p.2).toSection p.1))
      ((univ : Set M) ×ˢ S))
    (x : M) :
    TensorRSSpace.toModel
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) =
      ∫ t in (0 : ℝ)..1, (TensorRSSpace.toModel ((Φ t).toSection x)) := by
  rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem pathIntegralCoeffField_appCc_eq (g₀ : SmoothRiemannianMetric I M) (r s' : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s') (W : SmoothCcTensor g₀ 0 r)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s' ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s' ℝ E)
        (E := fun z : M => TensorRSSpace r s' I z) p.1 ((Φ p.2).toSection p.1))
      ((univ : Set M) ×ˢ S))
    (hcont : ∀ x : M, ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) S)
    (x : M) (v : Fin s' → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s'
        (operatorFieldApply (I := I) (M := M) g₀ r s'
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s' Φ S hS hSI hjoint) W) x v =
      ∫ t in (0 : ℝ)..1,
        unitModel (I := I) (M := M) g₀ s' (operatorFieldApply (I := I) (M := M) g₀ r s' (Φ t) W) x v := by

  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu

  have hIIm : IntervalIntegrable (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) volume 0 1 :=
    ((hcont x).mono hSI).intervalIntegrable

  have key : ∀ Ψ : SmoothCcTensor g₀ r s',
      unitModel (I := I) (M := M) g₀ s' (operatorFieldApply (I := I) (M := M) g₀ r s' Ψ W) x v =
        ((TensorRSSpace.toModel (Ψ.toSection x)) (Tensor0SSpace.toModel u)) v := by
    intro Ψ
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r s' x (Ψ.toSection x) u]

  rw [show unitModel (I := I) (M := M) g₀ s'
        (operatorFieldApply (I := I) (M := M) g₀ r s'
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s' Φ S hS hSI hjoint) W) x v =
      ((TensorRSSpace.toModel
            ((pathIntegralCoeffField (I := I) (M := M) g₀ r s' Φ S hS hSI hjoint).toSection x))
          (Tensor0SSpace.toModel u)) v from key _]

  rw [pathIntegralCoeffField_toModel]

  rw [ContinuousLinearMap.intervalIntegral_apply hIIm (Tensor0SSpace.toModel u)]

  have hcontApp : ContinuousOn (fun t : ℝ =>
      (TensorRSSpace.toModel ((Φ t).toSection x)) (Tensor0SSpace.toModel u)) S :=
    (ContinuousLinearMap.apply ℝ (Tensor0SModel s' ℝ E)
        (Tensor0SSpace.toModel u)).continuous.comp_continuousOn (hcont x)
  have hIIapp : IntervalIntegrable (fun t : ℝ =>
      (TensorRSSpace.toModel ((Φ t).toSection x)) (Tensor0SSpace.toModel u)) volume 0 1 :=
    (hcontApp.mono hSI).intervalIntegrable

  rw [show (fun t : ℝ => unitModel (I := I) (M := M) g₀ s'
          (operatorFieldApply (I := I) (M := M) g₀ r s' (Φ t) W) x v) =
        (fun t : ℝ => ((TensorRSSpace.toModel ((Φ t).toSection x)) (Tensor0SSpace.toModel u)) v) from
    funext (fun t => key (Φ t))]

  exact (ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s' => E) ℝ v) hIIapp).symm
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem coeffApp_integrable
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (W : SmoothCcTensor g₀ 0 r)
    (S : Set ℝ) (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hcont : ∀ x : M, ContinuousOn
      (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x)) S)
    (x : M) (v : Fin s → TangentSpace I x) :
    IntervalIntegrable
      (fun t : ℝ => unitModel (I := I) (M := M) g₀ s
        (operatorFieldApply (I := I) (M := M) g₀ r s (Φ t) W) x v)
      volume 0 1 := by
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  have hkey : ∀ t : ℝ,
      unitModel (I := I) (M := M) g₀ s
          (operatorFieldApply (I := I) (M := M) g₀ r s (Φ t) W) x v =
        ((TensorRSSpace.toModel ((Φ t).toSection x))
          (Tensor0SSpace.toModel u)) v := by
    intro t
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r s x ((Φ t).toSection x) u]
  have hcontApp : ContinuousOn (fun t : ℝ =>
      ((TensorRSSpace.toModel ((Φ t).toSection x))
        (Tensor0SSpace.toModel u)) v) S := by
    have hstep : ContinuousOn (fun t : ℝ =>
        (TensorRSSpace.toModel ((Φ t).toSection x)) (Tensor0SSpace.toModel u)) S :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E)
        (Tensor0SSpace.toModel u)).continuous.comp_continuousOn (hcont x)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ v).continuous.comp_continuousOn
      hstep
  have hcontFinal : ContinuousOn (fun t : ℝ =>
      unitModel (I := I) (M := M) g₀ s
        (operatorFieldApply (I := I) (M := M) g₀ r s (Φ t) W) x v) S := by
    refine hcontApp.congr (fun t _ => ?_)
    exact (hkey t).symm
  exact (hcontFinal.mono hSI).intervalIntegrable


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
