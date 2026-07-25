import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderReduction
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.NablaTensor.NablaTensorFormula
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCkBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradChartIdentity


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Sobolev.Chart
  DifferentialGeometry.Analysis.Laplacian.TensorRegularity in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradCompPull_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s T) α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm)
      (fun y =>
        DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial
            (E := E) (Jdx 0)
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx
                (Matrix.vecTail Jdx))) y
          + DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covDerivLowerOrderTerm
              (I := I) (M := M) g r s T α (Jdx 0) Idx (Matrix.vecTail Jdx) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  exact tensorChartComponentRaw_covGrad (I := I) (M := M) g r s T α Idx Jdx hy

section AnalyticCore

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.Analysis.Sobolev.Chart
  DifferentialGeometry.Analysis.Laplacian.TensorRegularity

private def rawPull (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
    ∘ (extChartAt I α).symm
    ∘ (toEuclidean (E := E)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rawPull_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) =
      rawPull (I := I) (M := M) g r s T α Idx Jdx := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rawPull_contDiffOn (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (rawPull (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  refine (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
    g r s T α Idx Jdx).congr (fun y hy => ?_)
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma rawPull_contDiffAt (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (rawPull (I := I) (M := M) g r s T α Idx Jdx) y :=
  (rawPull_contDiffOn (I := I) (M := M) g r s T α Idx Jdx).contDiffAt
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_iteratedFDeriv_eq (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) (j : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    iteratedFDeriv ℝ j
        (rawPull (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s T) α Idx Jdx) y =
      iteratedFDeriv ℝ j
        (fun z =>
          euclidPartial (E := E) (Jdx 0)
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx
                  (Matrix.vecTail Jdx))) z
            + covDerivLowerOrderTerm (I := I) (M := M) g r s T α (Jdx 0) Idx
                (Matrix.vecTail Jdx) z) y := by
  have h_eqOn := covGradCompPull_eqOn (I := I) (M := M) g r s T α Idx Jdx
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_evEq :
      (rawPull (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s T) α Idx Jdx) =ᶠ[nhds y]
        (fun z =>
          euclidPartial (E := E) (Jdx 0)
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx
                  (Matrix.vecTail Jdx))) z
            + covDerivLowerOrderTerm (I := I) (M := M) g r s T α (Jdx 0) Idx
                (Matrix.vecTail Jdx) z) := by
    filter_upwards [h_open.mem_nhds hy] with z hz using h_eqOn hz
  exact (Filter.EventuallyEq.iteratedFDeriv ℝ h_evEq j).self_of_nhds

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_eventuallyEq_rawPull (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)) =ᶠ[nhds y]
      rawPull (I := I) (M := M) g r s T α Idx Jdx := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  filter_upwards [h_open.mem_nhds hy] with z hz
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartial_term_iteratedFDeriv_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Idx : Fin r → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E))
    (Jdx' : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ j
        (fun z =>
          euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx')) z) y‖ ≤
      ‖iteratedFDeriv ℝ (j + 1)
        (rawPull (I := I) (M := M) g r s T α Idx Jdx') y‖ := by
  set u : EuclN → ℝ := rawPull (I := I) (M := M) g r s T α Idx Jdx' with hu_def
  have h_ev :
      (fun z =>
          euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx')) z) =ᶠ[nhds y]
        (fun z => fderiv ℝ u z (EuclideanSpace.single m 1)) := by
    have h_fderiv_ev :
        (fun z => fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx')) z) =ᶠ[nhds y]
          (fun z => fderiv ℝ u z) := by
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      filter_upwards [h_open.mem_nhds hy] with z hz
      have h_evz := chartPushedRaw_eventuallyEq_rawPull (I := I) (M := M)
        g r s T α Idx Jdx' hz
      exact Filter.EventuallyEq.fderiv_eq h_evz
    filter_upwards [h_fderiv_ev] with z hz
    simp only [euclidPartial_def, hz]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_ev j).self_of_nhds]
  have h_cdAt : ContDiffAt ℝ ∞ u y :=
    rawPull_contDiffAt (I := I) (M := M) g r s T α Idx Jdx' hy
  have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun z => fderiv ℝ u z) y := by
    have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
    have h := h_cdAt.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
    simpa using h
  have h_clm := norm_iteratedFDeriv_clm_apply_const
    (𝕜 := ℝ) (f := fun z => fderiv ℝ u z) (c := EuclideanSpace.single m 1)
    (x := y) (n := j) h_fderiv_cdAt (by exact_mod_cast le_top)
  have h_single_norm : ‖(EuclideanSpace.single m (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single]; simp
  have h_fderiv_iter : ‖iteratedFDeriv ℝ j (fun z => fderiv ℝ u z) y‖ =
      ‖iteratedFDeriv ℝ (j + 1) u y‖ := norm_iteratedFDeriv_fderiv
  calc ‖iteratedFDeriv ℝ j
          (fun z => (fderiv ℝ u z) (EuclideanSpace.single m 1)) y‖
      ≤ ‖(EuclideanSpace.single m (1 : ℝ))‖ *
          ‖iteratedFDeriv ℝ j (fun z => fderiv ℝ u z) y‖ := h_clm
    _ = ‖iteratedFDeriv ℝ j (fun z => fderiv ℝ u z) y‖ := by
        rw [h_single_norm, one_mul]
    _ = ‖iteratedFDeriv ℝ (j + 1) u y‖ := h_fderiv_iter

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivLowerOrderCoeff_contDiffAt (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (m : Fin (Module.finrank ℝ E))
    (Idx Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx Idx'
      Jdx Jdx') y :=
  (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx Idx'
    Jdx Jdx').contDiffAt ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_iteratedFDeriv_norm_bound_on_compact
    {f : EuclN → ℝ} {s : Set EuclN} (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s)
    {K : Set EuclN} (hK : IsCompact K) (hKs : K ⊆ s) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l ≤ N, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ l f y‖ ≤ C := by
  classical
  have h_uniq : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have h_per_order : ∀ l : ℕ, ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ y ∈ K,
      ‖iteratedFDeriv ℝ l f y‖ ≤ Cl := by
    intro l
    by_cases hKne : K.Nonempty
    · have h_iter_contOn : ContinuousOn (fun y => iteratedFDerivWithin ℝ l f s y) s :=
        hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) h_uniq
      have h_iter_K : ContinuousOn (iteratedFDerivWithin ℝ l f s) K :=
        h_iter_contOn.mono hKs
      have h_norm_K : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ l f s y‖) K :=
        continuous_norm.comp_continuousOn h_iter_K
      obtain ⟨y₀, _, hy₀_max⟩ := hK.exists_isMaxOn hKne h_norm_K
      refine ⟨‖iteratedFDerivWithin ℝ l f s y₀‖, norm_nonneg _, fun y hy => ?_⟩
      have h₁ : ‖iteratedFDerivWithin ℝ l f s y‖ ≤
          ‖iteratedFDerivWithin ℝ l f s y₀‖ := hy₀_max hy
      rwa [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) l hs (hKs hy)] at h₁
    · exact ⟨0, le_refl _, fun y hy => absurd ⟨y, hy⟩ hKne⟩
  choose Cl hCl_nn hCl using h_per_order
  refine ⟨(Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ Cl, ?_, ?_⟩
  · exact le_trans (hCl_nn 0)
      (Finset.le_sup' Cl (Finset.mem_range.mpr (Nat.succ_pos N)))
  · intro l hl y hy
    exact (hCl l y hy).trans
      (Finset.le_sup' Cl (Finset.mem_range.mpr (by omega)))

omit [BoundarylessManifold I M] in
private lemma exists_lowerOrderCoeff_uniform_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx' : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ N, ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2) y‖ ≤ C := by
  classical
  have hK_compact : IsCompact (chartImagePOUTsupport (I := I) (M := M) α) :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : chartImagePOUTsupport (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_per : ∀ (w : Fin (Module.finrank ℝ E) ×
      (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)) ×
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))),
      ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ l ≤ N, ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
        ‖iteratedFDeriv ℝ l
          (covDerivLowerOrderCoeff (I := I) (M := M) g r s α w.1 w.2.1
            w.2.2.2.1 w.2.2.1 w.2.2.2.2) y‖ ≤ Cw :=
    fun w => exists_iteratedFDeriv_norm_bound_on_compact
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α w.1 w.2.1
        w.2.2.2.1 w.2.2.1 w.2.2.2.2)
      h_open hK_compact hK_sub N
  choose Cw hCw_nn hCw using h_per
  refine ⟨(Finset.univ : Finset (Fin (Module.finrank ℝ E) ×
      (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)) ×
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))))).sup'
      ⟨⟨0, fun _ => 0, fun _ => 0, ⟨fun _ => 0, fun _ => 0⟩⟩, Finset.mem_univ _⟩ Cw, ?_, ?_⟩
  · refine le_trans (hCw_nn ⟨0, fun _ => 0, fun _ => 0, ⟨fun _ => 0, fun _ => 0⟩⟩) ?_
    exact Finset.le_sup' Cw (Finset.mem_univ _)
  · intro m Idx Jdx' p l hl y hy
    exact (hCw ⟨m, Idx, Jdx', p⟩ l hl y hy).trans
      (Finset.le_sup' Cw (Finset.mem_univ ⟨m, Idx, Jdx', p⟩))

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma lowerOrderTerm_iteratedFDeriv_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx' : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ j
        (fun z => covDerivLowerOrderTerm (I := I) (M := M) g r s T α m Idx Jdx' z) y‖ ≤
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ l ∈ Finset.range (j + 1),
          (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l
              (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2) y‖ *
            ‖iteratedFDeriv ℝ (j - l)
              (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖ := by
  classical
  set s_set : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_set
  have h_open : IsOpen s_set := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_uniq : UniqueDiffOn ℝ s_set := h_open.uniqueDiffOn
  set Lfun : EuclN → ℝ := fun z =>
    ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2 z *
        rawPull (I := I) (M := M) g r s T α p.1 p.2 z with hLfun_def
  have hL_eq : (fun z => covDerivLowerOrderTerm (I := I) (M := M) g r s T α m Idx Jdx' z)
      = Lfun := by
    funext z
    rw [hLfun_def, covDerivLowerOrderTerm_def]
    rfl
  rw [hL_eq]
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Lfun) j h_open hy]
  have h_coeff_cdwa : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffWithinAt ℝ j
        (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2)
        s_set y := fun p =>
    ((covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1
      Jdx' p.2).of_le (by exact_mod_cast le_top)) y hy
  have h_raw_cdwa : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffWithinAt ℝ j (rawPull (I := I) (M := M) g r s T α p.1 p.2)
        s_set y := fun p =>
    ((rawPull_contDiffOn (I := I) (M := M) g r s T α p.1 p.2).of_le
      (by exact_mod_cast le_top)) y hy
  have h_prod_cdwa : ∀ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffWithinAt ℝ j
        (fun z => covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2 z *
          rawPull (I := I) (M := M) g r s T α p.1 p.2 z) s_set y := fun p =>
    (h_coeff_cdwa p).mul (h_raw_cdwa p)
  rw [iteratedFDerivWithin_fun_sum_apply h_uniq hy (fun p _ => h_prod_cdwa p)]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p _ => ?_))
  have h_coeff_cdon : ContDiffOn ℝ j
      (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2) s_set :=
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α m Idx p.1
      Jdx' p.2).of_le (by exact_mod_cast le_top)
  have h_raw_cdon : ContDiffOn ℝ j
      (rawPull (I := I) (M := M) g r s T α p.1 p.2) s_set :=
    (rawPull_contDiffOn (I := I) (M := M) g r s T α p.1 p.2).of_le
      (by exact_mod_cast le_top)
  have hmul := norm_iteratedFDerivWithin_mul_le h_coeff_cdon h_raw_cdon h_uniq hy
    (le_refl (j : WithTop ℕ∞))
  refine le_trans hmul (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx' p.2)
        l h_open hy,
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := rawPull (I := I) (M := M) g r s T α p.1 p.2) (j - l) h_open hy]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma pouPull_eq_zero_off_kernel (α : M) (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ chartImagePOUTsupport (I := I) (M := M) α) :
    (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  by_contra hne
  have hb_supp : b ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    subset_tsupport _ (by simpa [Function.mem_support] using hne)
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have h_round : (extChartAt I α) b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  apply hy_off
  refine ⟨(extChartAt I α) b, ⟨b, hb_supp, rfl⟩, ?_⟩
  rw [h_round]; simp

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_component_iteratedFDeriv_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Γbd : ℝ) (_hΓbd_nn : 0 ≤ Γbd)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) (j : ℕ)
    (hΓ : ∀ (m : Fin (Module.finrank ℝ E))
        (Idx0 : Fin r → Fin (Module.finrank ℝ E))
        (Jdx0 : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ j, ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx0 p.1 Jdx0 p.2) z‖ ≤ Γbd)
    {y : EuclN} (hy_K : y ∈ chartImagePOUTsupport (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ j
        (rawPull (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s T) α Idx Jdx) y‖ ≤
      ‖iteratedFDeriv ℝ (j + 1)
          (rawPull (I := I) (M := M) g r s T α Idx (Matrix.vecTail Jdx)) y‖ +
        Γbd * ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ l ∈ Finset.range (j + 1),
              (j.choose l : ℝ) *
                ‖iteratedFDeriv ℝ (j - l)
                  (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖ := by
  classical
  have hy : y ∈ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α hy_K
  rw [covGrad_iteratedFDeriv_eq (I := I) (M := M) g r s T α Idx Jdx j hy]
  set fE : EuclN → ℝ := fun z =>
    euclidPartial (E := E) (Jdx 0)
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx
          (Matrix.vecTail Jdx))) z with hfE_def
  set fL : EuclN → ℝ := fun z =>
    covDerivLowerOrderTerm (I := I) (M := M) g r s T α (Jdx 0) Idx
      (Matrix.vecTail Jdx) z with hfL_def
  have h_cdAt_fE : ContDiffAt ℝ ∞ fE y := by
    set u : EuclN → ℝ := rawPull (I := I) (M := M) g r s T α Idx (Matrix.vecTail Jdx)
      with hu_def
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_ev : fE =ᶠ[nhds y] (fun z => fderiv ℝ u z (EuclideanSpace.single (Jdx 0) 1)) := by
      have h_fderiv_ev :
          (fun z => fderiv ℝ
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx
                  (Matrix.vecTail Jdx))) z) =ᶠ[nhds y] (fun z => fderiv ℝ u z) := by
        filter_upwards [h_open.mem_nhds hy] with z hz
        exact Filter.EventuallyEq.fderiv_eq
          (chartPushedRaw_eventuallyEq_rawPull (I := I) (M := M) g r s T α Idx
            (Matrix.vecTail Jdx) hz)
      filter_upwards [h_fderiv_ev] with z hz
      simp only [hfE_def, euclidPartial_def, hz]
    have h_u_cdAt : ContDiffAt ℝ ∞ u y :=
      rawPull_contDiffAt (I := I) (M := M) g r s T α Idx (Matrix.vecTail Jdx) hy
    have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun z => fderiv ℝ u z) y := by
      have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
        rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
      have h := h_u_cdAt.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
      simpa using h
    have h_eval_cdAt : ContDiffAt ℝ ∞
        (fun z => fderiv ℝ u z (EuclideanSpace.single (Jdx 0) 1)) y :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single (Jdx 0) (1 : ℝ))).contDiff.contDiffAt.comp y h_fderiv_cdAt
    exact h_eval_cdAt.congr_of_eventuallyEq h_ev
  have h_cdAt_fL : ContDiffAt ℝ ∞ fL y := by
    rw [hfL_def]
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_cdOn := covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M)
      g r s T α (Jdx 0) Idx (Matrix.vecTail Jdx)
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s T α Idx' Jdx')
    exact h_cdOn.contDiffAt (h_open.mem_nhds hy)
  have h_add : iteratedFDeriv ℝ j (fun z => fE z + fL z) y =
      iteratedFDeriv ℝ j fE y + iteratedFDeriv ℝ j fL y := by
    have hjle : (j : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact_mod_cast le_top (α := ℕ∞)
    have h1 : ContDiffAt ℝ (j : WithTop ℕ∞) fE y := h_cdAt_fE.of_le hjle
    have h2 : ContDiffAt ℝ (j : WithTop ℕ∞) fL y := h_cdAt_fL.of_le hjle
    rw [fun_iteratedFDeriv_add_apply h1 h2]
  rw [show (fun z =>
      euclidPartial (E := E) (Jdx 0)
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx
            (Matrix.vecTail Jdx))) z
      + covDerivLowerOrderTerm (I := I) (M := M) g r s T α (Jdx 0) Idx
          (Matrix.vecTail Jdx) z) = fun z => fE z + fL z from rfl, h_add]
  refine le_trans (norm_add_le _ _) ?_
  have h_euclid := euclidPartial_term_iteratedFDeriv_norm_le (I := I) (M := M)
    g r s T α Idx (Jdx 0) (Matrix.vecTail Jdx) j hy
  have h_lower := lowerOrderTerm_iteratedFDeriv_norm_le (I := I) (M := M)
    g r s T α (Jdx 0) Idx (Matrix.vecTail Jdx) j hy
  refine add_le_add ?_ ?_
  · exact h_euclid
  · refine le_trans h_lower ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hl_le : l ≤ j := by have := Finset.mem_range.mp hl; omega
    have hΓ_bd : ‖iteratedFDeriv ℝ l
        (covDerivLowerOrderCoeff (I := I) (M := M) g r s α (Jdx 0) Idx p.1
          (Matrix.vecTail Jdx) p.2) y‖ ≤ Γbd :=
      hΓ (Jdx 0) Idx (Matrix.vecTail Jdx) p l hl_le y hy_K
    have h_raw_nn : 0 ≤ ‖iteratedFDeriv ℝ (j - l)
        (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖ := norm_nonneg _
    have h_choose_nn : 0 ≤ (j.choose l : ℝ) := by positivity
    calc (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ l
              (covDerivLowerOrderCoeff (I := I) (M := M) g r s α (Jdx 0) Idx p.1
                (Matrix.vecTail Jdx) p.2) y‖ *
            ‖iteratedFDeriv ℝ (j - l)
              (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖
        ≤ (j.choose l : ℝ) * Γbd *
            ‖iteratedFDeriv ℝ (j - l)
              (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖ := by
          apply mul_le_mul_of_nonneg_right _ h_raw_nn
          exact mul_le_mul_of_nonneg_left hΓ_bd h_choose_nn
      _ = Γbd * ((j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ (j - l)
              (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖) := by ring

private def rhsHsContent (g : SmoothRiemannianMetric I M) (r s σ : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (y : EuclN) : ℝ :=
  ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    ∑ l ∈ Finset.range (2 * (σ + 1) + 1),
      ∑ bIdx : Fin l → Fin (Module.finrank ℝ E),
        |(iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rhsHsContent_nonneg (g : SmoothRiemannianMetric I M) (r s σ : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (y : EuclN) :
    0 ≤ rhsHsContent (I := I) (M := M) g r s σ T α y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rawPull_iteratedFDeriv_norm_sq_le_rhsHsContent
    (g : SmoothRiemannianMetric I M) (r s σ : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (l : ℕ) (hl : l ≤ 2 * (σ + 1)) (y : EuclN) :
    ‖iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2 ≤
      rhsHsContent (I := I) (M := M) g r s σ T α y := by
  classical
  set basisSum : ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) → ℕ → ℝ :=
    fun q' l' => ∑ bIdx : Fin l' → Fin (Module.finrank ℝ E),
      |(iteratedFDeriv ℝ l' (rawPull (I := I) (M := M) g r s T α q'.1 q'.2) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 with hbasisSum_def
  have hbasisSum_nn : ∀ q' l', 0 ≤ basisSum q' l' :=
    fun q' l' => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_op : ‖iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2 ≤
      basisSum q l :=
    ContinuousMultilinearMap.opNorm_sq_le_sum_sq_basisEval
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ)
      (iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2) y)
  refine le_trans h_op ?_
  have h_unfold : rhsHsContent (I := I) (M := M) g r s σ T α y =
      ∑ q' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ l' ∈ Finset.range (2 * (σ + 1) + 1), basisSum q' l' := rfl
  rw [h_unfold]
  have hl_mem : l ∈ Finset.range (2 * (σ + 1) + 1) := Finset.mem_range.mpr (by omega)
  have h_inner : basisSum q l ≤ ∑ l' ∈ Finset.range (2 * (σ + 1) + 1), basisSum q l' :=
    Finset.single_le_sum (f := fun l' => basisSum q l')
      (fun l' _ => hbasisSum_nn q l') hl_mem
  refine le_trans h_inner ?_
  exact Finset.single_le_sum
    (f := fun q' => ∑ l' ∈ Finset.range (2 * (σ + 1) + 1), basisSum q' l')
    (fun q' _ => Finset.sum_nonneg (fun l' _ => hbasisSum_nn q' l'))
    (Finset.mem_univ q)

omit [BoundarylessManifold I M] in
private lemma covGradComp_basisSum_le_rhsHsContent
    (g : SmoothRiemannianMetric I M) (r s σ : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Γbd : ℝ) (hΓbd_nn : 0 ≤ Γbd)
    (hΓ : ∀ (m : Fin (Module.finrank ℝ E))
        (Idx0 : Fin r → Fin (Module.finrank ℝ E))
        (Jdx0 : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ 2 * σ, ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx0 p.1 Jdx0 p.2) z‖ ≤ Γbd)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin (s + 1) → Fin (Module.finrank ℝ E)) (j : ℕ) (hj : j ≤ 2 * σ)
    {y : EuclN} (hy_K : y ∈ chartImagePOUTsupport (I := I) (M := M) α) :
    (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
        |(iteratedFDeriv ℝ j
              (rawPull (I := I) (M := M) g r (s + 1)
                (covGrad (I := I) (M := M) g r s T) α Idx Jdx) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
      ((Module.finrank ℝ E) ^ (2 * σ) : ℝ) *
        (1 + Γbd * (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * (2 : ℝ) ^ (2 * σ)) ^ 2 *
        rhsHsContent (I := I) (M := M) g r s σ T α y := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let Np : ℕ := Fintype.card ((Fin r → Fin n) × (Fin s → Fin n))
  let R : ℝ := rhsHsContent (I := I) (M := M) g r s σ T α y
  have hR_nn : 0 ≤ R := rhsHsContent_nonneg (I := I) (M := M) g r s σ T α y
  have hsqrtR_nn : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  let F : EuclN → ℝ := rawPull (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s T) α Idx Jdx
  let Fop : ℝ := ‖iteratedFDeriv ℝ j F y‖
  let B0 : ℝ := 1 + Γbd * (Np : ℝ) * (2 : ℝ) ^ (2 * σ)
  have hB0_nn : 0 ≤ B0 := by
    have : 0 ≤ Γbd * (Np : ℝ) * (2 : ℝ) ^ (2 * σ) := by positivity
    change 0 ≤ 1 + Γbd * (Np : ℝ) * (2 : ℝ) ^ (2 * σ); linarith
  have hFop_le : Fop ≤ B0 * Real.sqrt R := by
    have h_comb := covGrad_component_iteratedFDeriv_norm_le (I := I) (M := M)
      g r s T α Γbd hΓbd_nn Idx Jdx j
      (fun m Idx0 Jdx0 p l hl z hz => hΓ m Idx0 Jdx0 p l (by omega) z hz) hy_K
    have h_lead : ‖iteratedFDeriv ℝ (j + 1)
        (rawPull (I := I) (M := M) g r s T α Idx (Matrix.vecTail Jdx)) y‖ ≤ Real.sqrt R := by
      have hsq := rawPull_iteratedFDeriv_norm_sq_le_rhsHsContent (I := I) (M := M)
        g r s σ T α ⟨Idx, Matrix.vecTail Jdx⟩ (j + 1) (by omega) y
      calc ‖iteratedFDeriv ℝ (j + 1)
            (rawPull (I := I) (M := M) g r s T α Idx (Matrix.vecTail Jdx)) y‖
          = Real.sqrt (‖iteratedFDeriv ℝ (j + 1)
              (rawPull (I := I) (M := M) g r s T α Idx (Matrix.vecTail Jdx)) y‖ ^ 2) := by
            rw [Real.sqrt_sq (norm_nonneg _)]
        _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hsq
    have h_low_le : (∑ p : (Fin r → Fin n) × (Fin s → Fin n),
        ∑ l ∈ Finset.range (j + 1),
          (j.choose l : ℝ) *
            ‖iteratedFDeriv ℝ (j - l)
              (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖) ≤
        (Np : ℝ) * (2 : ℝ) ^ (2 * σ) * Real.sqrt R := by
      have h_per : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
          (∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) *
              ‖iteratedFDeriv ℝ (j - l)
                (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖) ≤
          (2 : ℝ) ^ (2 * σ) * Real.sqrt R := by
        intro p
        have h1 : (∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) *
              ‖iteratedFDeriv ℝ (j - l)
                (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖) ≤
            ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * Real.sqrt R := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          have hraw_le : ‖iteratedFDeriv ℝ (j - l)
              (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖ ≤ Real.sqrt R := by
            have hsq := rawPull_iteratedFDeriv_norm_sq_le_rhsHsContent (I := I) (M := M)
              g r s σ T α p (j - l) (by omega) y
            calc ‖iteratedFDeriv ℝ (j - l)
                  (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖
                = Real.sqrt (‖iteratedFDeriv ℝ (j - l)
                    (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖ ^ 2) := by
                  rw [Real.sqrt_sq (norm_nonneg _)]
              _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hsq
          exact mul_le_mul_of_nonneg_left hraw_le (by positivity)
        have h2 : (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ)) = (2 : ℝ) ^ j := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
        calc (∑ l ∈ Finset.range (j + 1),
              (j.choose l : ℝ) *
                ‖iteratedFDeriv ℝ (j - l)
                  (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖)
            ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * Real.sqrt R := h1
          _ = ((2 : ℝ) ^ j) * Real.sqrt R := by rw [← Finset.sum_mul, h2]
          _ ≤ (2 : ℝ) ^ (2 * σ) * Real.sqrt R := by
              apply mul_le_mul_of_nonneg_right _ hsqrtR_nn
              exact pow_le_pow_right₀ (by norm_num) hj
      calc (∑ p : (Fin r → Fin n) × (Fin s → Fin n),
            ∑ l ∈ Finset.range (j + 1),
              (j.choose l : ℝ) *
                ‖iteratedFDeriv ℝ (j - l)
                  (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖)
          ≤ ∑ _p : (Fin r → Fin n) × (Fin s → Fin n),
              (2 : ℝ) ^ (2 * σ) * Real.sqrt R :=
            Finset.sum_le_sum (fun p _ => h_per p)
        _ = (Np : ℝ) * (2 : ℝ) ^ (2 * σ) * Real.sqrt R := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    calc Fop ≤ ‖iteratedFDeriv ℝ (j + 1)
            (rawPull (I := I) (M := M) g r s T α Idx (Matrix.vecTail Jdx)) y‖ +
          Γbd * ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
              ∑ l ∈ Finset.range (j + 1),
                (j.choose l : ℝ) *
                  ‖iteratedFDeriv ℝ (j - l)
                    (rawPull (I := I) (M := M) g r s T α p.1 p.2) y‖ := h_comb
      _ ≤ Real.sqrt R + Γbd * ((Np : ℝ) * (2 : ℝ) ^ (2 * σ) * Real.sqrt R) := by
          refine add_le_add h_lead ?_
          exact mul_le_mul_of_nonneg_left h_low_le hΓbd_nn
      _ = B0 * Real.sqrt R := by
          change _ = (1 + Γbd * (Np : ℝ) * (2 : ℝ) ^ (2 * σ)) * Real.sqrt R; ring
  have hFop_sq_le : Fop ^ 2 ≤ B0 ^ 2 * R := by
    have h1 : Fop ^ 2 ≤ (B0 * Real.sqrt R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hFop_le 2
    calc Fop ^ 2 ≤ (B0 * Real.sqrt R) ^ 2 := h1
      _ = B0 ^ 2 * (Real.sqrt R ^ 2) := by ring
      _ = B0 ^ 2 * R := by rw [Real.sq_sqrt hR_nn]
  have h_eval_le : ∀ bIdx : Fin j → Fin n,
      |(iteratedFDeriv ℝ j F y)
          (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2 ≤ Fop ^ 2 := by
    intro bIdx
    have h_le : |(iteratedFDeriv ℝ j F y)
        (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ≤ Fop := by
      have h := (iteratedFDeriv ℝ j F y).le_opNorm
        (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))
      have hprod : (∏ i : Fin j, ‖EuclideanSpace.basisFun (Fin n) ℝ (bIdx i)‖) = 1 := by
        refine Finset.prod_eq_one (fun i _ => ?_)
        rw [EuclideanSpace.basisFun_apply, PiLp.norm_single]; simp
      rw [hprod, mul_one] at h
      rw [← Real.norm_eq_abs]; exact h
    have h_abs_nn : 0 ≤ |(iteratedFDeriv ℝ j F y)
        (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| := abs_nonneg _
    exact pow_le_pow_left₀ h_abs_nn h_le 2
  have h_card : (Fintype.card (Fin j → Fin n) : ℝ) = (n : ℝ) ^ j := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  have key : (∑ bIdx : Fin j → Fin n,
        |(iteratedFDeriv ℝ j F y)
            (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2) ≤
      (n : ℝ) ^ (2 * σ) * B0 ^ 2 * R := by
    calc (∑ bIdx : Fin j → Fin n,
          |(iteratedFDeriv ℝ j F y)
              (fun i => EuclideanSpace.basisFun (Fin n) ℝ (bIdx i))| ^ 2)
        ≤ ∑ _bIdx : Fin j → Fin n, Fop ^ 2 := Finset.sum_le_sum (fun bIdx _ => h_eval_le bIdx)
      _ = (n : ℝ) ^ j * Fop ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h_card]
      _ ≤ (n : ℝ) ^ j * (B0 ^ 2 * R) :=
          mul_le_mul_of_nonneg_left hFop_sq_le (by positivity)
      _ ≤ (n : ℝ) ^ (2 * σ) * (B0 ^ 2 * R) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
            have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
            exact_mod_cast this
          exact pow_le_pow_right₀ hn1 hj
      _ = (n : ℝ) ^ (2 * σ) * B0 ^ 2 * R := by ring
  exact key

private def combinedConst (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (r s σ : ℕ) (Γbd : ℝ) : ℝ :=
  (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin (s + 1) → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * σ + 1 : ℕ) : ℝ) *
    ((Module.finrank ℝ E) ^ (2 * σ) : ℝ) *
    (1 + Γbd * (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * (2 : ℝ) ^ (2 * σ)) ^ 2

private lemma combinedConst_nonneg (r s σ : ℕ) {Γbd : ℝ} (hΓbd_nn : 0 ≤ Γbd) :
    0 ≤ combinedConst E r s σ Γbd := by
  unfold combinedConst; positivity

omit [BoundarylessManifold I M] in
private lemma covGrad_pointwise_integrand_le
    (g : SmoothRiemannianMetric I M) (r s σ : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Γbd : ℝ) (hΓbd_nn : 0 ≤ Γbd)
    (hΓ : ∀ (m : Fin (Module.finrank ℝ E))
        (Idx0 : Fin r → Fin (Module.finrank ℝ E))
        (Jdx0 : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ 2 * σ, ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx0 p.1 Jdx0 p.2) z‖ ≤ Γbd)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + 1) → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * σ + 1),
            ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
              |(iteratedFDeriv ℝ j
                    (rawPull (I := I) (M := M) g r (s + 1)
                      (covGrad (I := I) (M := M) g r s T) α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
      combinedConst E r s σ Γbd *
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          rhsHsContent (I := I) (M := M) g r s σ T α y) := by
  classical
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
  set R : ℝ := rhsHsContent (I := I) (M := M) g r s σ T α y with hR_def
  have hR_nn : 0 ≤ R := rhsHsContent_nonneg (I := I) (M := M) g r s σ T α y
  set LHSsum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin (s + 1) → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * σ + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j
                (rawPull (I := I) (M := M) g r (s + 1)
                  (covGrad (I := I) (M := M) g r s T) α IJ.1 IJ.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 with hLHSsum_def
  have hLHSsum_nn : 0 ≤ LHSsum :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  by_cases hyK : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · have h_LHSsum_le : LHSsum ≤ combinedConst E r s σ Γbd * R := by
      have h_perIJ : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + 1) → Fin (Module.finrank ℝ E)),
          (∑ j ∈ Finset.range (2 * σ + 1),
            ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
              |(iteratedFDeriv ℝ j
                    (rawPull (I := I) (M := M) g r (s + 1)
                      (covGrad (I := I) (M := M) g r s T) α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
          ((2 * σ + 1 : ℕ) : ℝ) *
            (((Module.finrank ℝ E) ^ (2 * σ) : ℝ) *
              (1 + Γbd * (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * (2 : ℝ) ^ (2 * σ)) ^ 2 * R) := by
        intro IJ
        calc (∑ j ∈ Finset.range (2 * σ + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                |(iteratedFDeriv ℝ j
                      (rawPull (I := I) (M := M) g r (s + 1)
                        (covGrad (I := I) (M := M) g r s T) α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ≤ ∑ _j ∈ Finset.range (2 * σ + 1),
                ((Module.finrank ℝ E) ^ (2 * σ) : ℝ) *
                  (1 + Γbd * (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * (2 : ℝ) ^ (2 * σ)) ^ 2 * R := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              have hj_le : j ≤ 2 * σ := by have := Finset.mem_range.mp hj; omega
              have := covGradComp_basisSum_le_rhsHsContent (I := I) (M := M)
                g r s σ T α Γbd hΓbd_nn hΓ IJ.1 IJ.2 j hj_le hyK
              rw [← hR_def] at this
              exact this
          _ = ((2 * σ + 1 : ℕ) : ℝ) *
                (((Module.finrank ℝ E) ^ (2 * σ) : ℝ) *
                  (1 + Γbd * (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * (2 : ℝ) ^ (2 * σ)) ^ 2 * R) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc LHSsum
          ≤ ∑ _IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin (s + 1) → Fin (Module.finrank ℝ E)),
              ((2 * σ + 1 : ℕ) : ℝ) *
                (((Module.finrank ℝ E) ^ (2 * σ) : ℝ) *
                  (1 + Γbd * (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * (2 : ℝ) ^ (2 * σ)) ^ 2 * R) :=
            Finset.sum_le_sum (fun IJ _ => h_perIJ IJ)
        _ = combinedConst E r s σ Γbd * R := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            unfold combinedConst; push_cast; ring
    calc ρ * LHSsum ≤ ρ * (combinedConst E r s σ Γbd * R) :=
          mul_le_mul_of_nonneg_left h_LHSsum_le hρ_nn
      _ = combinedConst E r s σ Γbd * (ρ * R) := by ring
  · have hρ0 : ρ = 0 :=
      pouPull_eq_zero_off_kernel (I := I) (M := M) α y hy hyK
    rw [hρ0]; simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma pouPullCont (α : M) :
    ContinuousOn
      (fun y : EuclN =>
        (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hPOU_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).continuous
  have hSymmCont : ContinuousOn ((extChartAt I α).symm) (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have h_inner : ContinuousOn
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hSymmCont.comp (toEuclidean (E := E)).symm.continuous.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact hPOU_cont.comp_continuousOn h_inner

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma rawPullIntegrand_aemeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (l : ℕ)
    (bIdx : Fin l → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclN => ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_iter_contOn :
      ContinuousOn (iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    have h_cd : ContDiffAt ℝ ∞ (rawPull (I := I) (M := M) g r s T α q.1 q.2) y :=
      rawPull_contDiffAt (I := I) (M := M) g r s T α q.1 q.2 hy
    exact (h_cd.continuousAt_iteratedFDeriv (k := l)
      (by exact_mod_cast le_top)).continuousWithinAt
  have h_eval : ContinuousOn
      (fun y : EuclN => (iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2) y)
          (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (continuous_eval_const _).comp_continuousOn h_iter_contOn
  have h_real : ContinuousOn
      (fun y : EuclN => ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawPull (I := I) (M := M) g r s T α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (pouPullCont (I := I) (M := M) α).mul (h_eval.abs.pow 2)
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (h_real.aestronglyMeasurable h_open.measurableSet).aemeasurable

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma sumIntegrals_eq_integral_sum
    (g : SmoothRiemannianMetric I M) (r' s' : ℕ) (S : SmoothCcTensor g r' s')
    (α : M) (K : ℕ) :
    (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
          (Fin s' → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
                  (Fin s' → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range K,
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  |(iteratedFDeriv ℝ j
                        (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
  classical
  have h_bIdx : ∀ (IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
        (Fin s' → Fin (Module.finrank ℝ E))) (j : ℕ),
      (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
          ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
    intro IJ j
    rw [MeasureTheory.lintegral_finset_sum' _
      (fun bIdx _ => rawPullIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)]
  have h_j : ∀ (IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
        (Fin s' → Fin (Module.finrank ℝ E))),
      (∑ j ∈ Finset.range K,
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
    intro IJ
    have hmeas : ∀ j ∈ Finset.range K,
        AEMeasurable (fun y : EuclN =>
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
      intro j _
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
        (fun bIdx (_ : bIdx ∈ Finset.univ) =>
          rawPullIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)
      refine h.congr (Filter.EventuallyEq.of_eq (funext (fun y => ?_)))
      rw [Finset.sum_apply]
    rw [MeasureTheory.lintegral_finset_sum' _ hmeas]
  calc (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
          (Fin s' → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range K,
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN))
      = ∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
            (Fin s' → Fin (Module.finrank ℝ E)),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ j ∈ Finset.range K,
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
            ∂(volume : Measure EuclN) := by
        refine Finset.sum_congr rfl (fun IJ _ => ?_)
        rw [← h_j IJ]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← h_bIdx IJ j]
    _ = ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
              (Fin s' → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range K,
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN) := by
        have hmeas2 : ∀ IJ ∈ (Finset.univ : Finset ((Fin r' → Fin (Module.finrank ℝ E)) ×
            (Fin s' → Fin (Module.finrank ℝ E)))),
            AEMeasurable (fun y : EuclN =>
              ∑ j ∈ Finset.range K,
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
              ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
          intro IJ _
          have h := Finset.aemeasurable_sum (Finset.range K)
            (fun j (_ : j ∈ Finset.range K) =>
              (Finset.aemeasurable_sum
                (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
                (fun bIdx (_ : bIdx ∈ Finset.univ) =>
                  rawPullIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)).congr
                (Filter.EventuallyEq.of_eq (funext (fun y => by rw [Finset.sum_apply]))))
          refine h.congr (Filter.EventuallyEq.of_eq (funext (fun y => ?_)))
          rw [Finset.sum_apply]
        rw [MeasureTheory.lintegral_finset_sum' _ hmeas2]
    _ = ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              (∑ IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
                    (Fin s' → Fin (Module.finrank ℝ E)),
                ∑ j ∈ Finset.range K,
                  ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                    |(iteratedFDeriv ℝ j
                          (rawPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN) := by
        refine setLIntegral_congr_fun
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet (fun y _ => ?_)
        set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
        have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg
            (fun IJ _ => mul_nonneg hρ_nn (Finset.sum_nonneg
              (fun j _ => Finset.sum_nonneg (fun bIdx _ => sq_nonneg _))))]
        refine Finset.sum_congr rfl (fun IJ _ => ?_)
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg
            (fun j _ => mul_nonneg hρ_nn (Finset.sum_nonneg (fun bIdx _ => sq_nonneg _)))]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum,
          ENNReal.ofReal_sum_of_nonneg (fun bIdx _ => mul_nonneg hρ_nn (sq_nonneg _))]

omit [BoundarylessManifold I M] in
private lemma covGrad_per_alpha_inner_bound
    (g : SmoothRiemannianMetric I M) (r s σ : ℕ) (T : SmoothCcTensor g r s)
    (α : M) (Γfun : M → ℝ) (Γmax : ℝ) (hΓmax_nn : 0 ≤ Γmax)
    (_hΓfun_nn : ∀ α : M, 0 ≤ Γfun α)
    (hΓfun : ∀ (α : M) (m : Fin (Module.finrank ℝ E))
        (Idx0 : Fin r → Fin (Module.finrank ℝ E))
        (Jdx0 : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ 2 * σ, ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx0 p.1 Jdx0 p.2) z‖
            ≤ Γfun α)
    (hΓmax_ge : ∀ α ∈ chartAtlasPOU_activeFinset I M, Γfun α ≤ Γmax)
    (Cmax : ℝ) (hCmax_def : Cmax = combinedConst E r s σ Γmax)
    {lhsInner rhsInner : M → ℝ≥0∞}
    (hlhsInner_def : lhsInner = fun α =>
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin (s + 1) → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * σ + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
                            (covGrad (I := I) (M := M) g r s T) α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN))
    (hrhsInner_def : rhsInner = fun α =>
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (σ + 1) + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN)) :
    lhsInner α ≤ ENNReal.ofReal Cmax * rhsInner α := by
  classical
  subst hlhsInner_def hrhsInner_def
  simp only
  have hCmax_nn_aux : 0 ≤ combinedConst E r s σ Γmax :=
    combinedConst_nonneg (E := E) r s σ hΓmax_nn
  simp only [rawPull_eq (I := I) (M := M)]
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · have hΓ : ∀ (m : Fin (Module.finrank ℝ E))
        (Idx0 : Fin r → Fin (Module.finrank ℝ E))
        (Jdx0 : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ 2 * σ, ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx0 p.1 Jdx0 p.2) z‖
            ≤ Γmax :=
      fun m Idx0 Jdx0 p l hl z hz =>
        (hΓfun α m Idx0 Jdx0 p l hl z hz).trans (hΓmax_ge α hα)
    rw [sumIntegrals_eq_integral_sum (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s T) α (2 * σ + 1)]
    rw [sumIntegrals_eq_integral_sum (I := I) (M := M) g r s T α (2 * (σ + 1) + 1)]
    rw [hCmax_def]
    rw [show (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range (2 * (σ + 1) + 1),
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  |(iteratedFDeriv ℝ j
                        (rawPull (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ∂(volume : Measure EuclN)) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              rhsHsContent (I := I) (M := M) g r s σ T α y)
          ∂(volume : Measure EuclN) from rfl]
    rw [← MeasureTheory.lintegral_const_mul' _ _
      (ENNReal.ofReal_ne_top (r := combinedConst E r s σ Γmax))]
    refine setLIntegral_mono_ae'
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      (Filter.Eventually.of_forall (fun y hy => ?_))
    have hpt := covGrad_pointwise_integrand_le (I := I) (M := M) g r s σ T α
      Γmax hΓmax_nn hΓ hy
    have h_rhs_nn : 0 ≤ ((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          rhsHsContent (I := I) (M := M) g r s σ T α y :=
      mul_nonneg ((chartAtlasPOU I M).nonneg α _)
        (rhsHsContent_nonneg (I := I) (M := M) g r s σ T α y)
    rw [← ENNReal.ofReal_mul hCmax_nn_aux]
    exact ENNReal.ofReal_le_ofReal hpt
  · have hρ0 : ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
    have hzero : (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin (s + 1) → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * σ + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (rawPull (I := I) (M := M) g r (s + 1)
                          (covGrad (I := I) (M := M) g r s T) α IJ.1 IJ.2)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN)) = 0 := by
      refine Finset.sum_eq_zero (fun IJ _ => Finset.sum_eq_zero (fun j _ =>
        Finset.sum_eq_zero (fun bIdx _ => ?_)))
      refine MeasureTheory.setLIntegral_eq_zero
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet (fun y _ => ?_)
      simp only [Pi.zero_apply]
      rw [hρ0, zero_mul, ENNReal.ofReal_zero]
    rw [hzero]
    exact zero_le _

omit [BoundarylessManifold I M] in
theorem exists_covGrad_tensorPouSobolevHsNorm_le
    (g : SmoothRiemannianMetric I M) (r s σ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        tensorPouSobolevHsNorm (I := I) (M := M) g σ
            (covGrad (I := I) (M := M) g r s T) ≤
          ENNReal.ofReal C *
            tensorPouSobolevHsNorm (I := I) (M := M) g (σ + 1) T := by
  classical
  have hΓexists : ∀ α : M, ∃ Γ : ℝ, 0 ≤ Γ ∧
      ∀ (m : Fin (Module.finrank ℝ E))
        (Idx0 : Fin r → Fin (Module.finrank ℝ E))
        (Jdx0 : Fin s → Fin (Module.finrank ℝ E))
        (p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))),
        ∀ l ≤ 2 * σ, ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
            (covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx0 p.1 Jdx0 p.2) z‖ ≤ Γ :=
    fun α => exists_lowerOrderCoeff_uniform_bound (I := I) (M := M) g r s α (2 * σ)
  choose Γfun hΓfun_nn hΓfun using hΓexists
  set actF : Finset M := chartAtlasPOU_activeFinset I M with hactF_def
  set Γmax : ℝ := ∑ α ∈ actF, Γfun α with hΓmax_def
  have hΓmax_nn : 0 ≤ Γmax := Finset.sum_nonneg (fun α _ => hΓfun_nn α)
  have hΓmax_ge : ∀ α ∈ actF, Γfun α ≤ Γmax :=
    fun α hα => Finset.single_le_sum (fun β _ => hΓfun_nn β) hα
  set Cmax : ℝ := combinedConst E r s σ Γmax with hCmax_def
  have hCmax_nn : 0 ≤ Cmax := combinedConst_nonneg (E := E) r s σ hΓmax_nn
  refine ⟨Real.sqrt Cmax, Real.sqrt_nonneg _, fun T => ?_⟩
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevHsNorm_eq]
  set lhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin (s + 1) → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * σ + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r (s + 1)
                          (covGrad (I := I) (M := M) g r s T) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN) with hlhsInner_def
  set rhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * (σ + 1) + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN) with hrhsInner_def
  have h_main : (∑' α : M, lhsInner α) ≤
      ENNReal.ofReal Cmax * ∑' α : M, rhsInner α := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun α => ?_)
    exact covGrad_per_alpha_inner_bound (I := I) (M := M) g r s σ T α
      Γfun Γmax hΓmax_nn (fun α' => hΓfun_nn α') hΓfun hΓmax_ge Cmax hCmax_def
      hlhsInner_def hrhsInner_def
  have h_rpow : (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal Cmax * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h_main (by norm_num)
  calc (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal Cmax * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := h_rpow
    _ = ENNReal.ofReal (Real.sqrt Cmax) * (∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg hCmax_nn (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← Real.sqrt_eq_rpow]

omit [BoundarylessManifold I M] in
theorem covGrad_toHs_norm_le
    (g : SmoothRiemannianMetric I M) (r s σ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + 1) σ
            (covGrad (I := I) (M := M) g r s T)‖ ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (σ + 1) T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_covGrad_tensorPouSobolevHsNorm_le (I := I) (M := M) g r s σ
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  have hle := hC T
  have h_rhs_ne_top :
      ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (σ + 1) T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (σ + 1) T).ne
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g σ
          (covGrad (I := I) (M := M) g r s T)).toReal
      ≤ (ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (σ + 1) T).toReal :=
        ENNReal.toReal_mono h_rhs_ne_top hle
    _ = (ENNReal.ofReal C).toReal *
          (tensorPouSobolevHsNorm (I := I) (M := M) g (σ + 1) T).toReal := by
        rw [ENNReal.toReal_mul]
    _ = C * (tensorPouSobolevHsNorm (I := I) (M := M) g (σ + 1) T).toReal := by
        rw [ENNReal.toReal_ofReal hC_nn]

omit [BoundarylessManifold I M] in
theorem iteratedCovGrad_toHs_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (j σ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) σ
            (iteratedCovGrad g r s j T)‖ ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (σ + j) T‖ := by
  induction j generalizing σ with
  | zero =>
      refine ⟨1, zero_le_one, fun T => ?_⟩
      simp only [iteratedCovGrad_zero, Nat.add_zero, one_mul, le_refl]
  | succ j ih =>
      obtain ⟨Cj, hCj_nn, hCj⟩ := ih (σ + 1)
      obtain ⟨C1, hC1_nn, hC1⟩ :=
        covGrad_toHs_norm_le (I := I) (M := M) g r (s + j) σ
      refine ⟨C1 * Cj, mul_nonneg hC1_nn hCj_nn, fun T => ?_⟩
      have hstep := hC1 (iteratedCovGrad g r s j T)
      have hih := hCj T
      have hval : s + (j + 1) = (s + j) + 1 := by ring
      have hord : σ + 1 + j = σ + (j + 1) := by ring
      calc ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + (j + 1)) σ
              (iteratedCovGrad g r s (j + 1) T)‖
          = ‖SmoothCcTensor.toHs (g := g) (r := r) (s := (s + j) + 1) σ
              (covGrad (I := I) (M := M) g r (s + j)
                (iteratedCovGrad g r s j T))‖ := by
            rw [iteratedCovGrad_succ]
        _ ≤ C1 * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (σ + 1)
              (iteratedCovGrad g r s j T)‖ := hstep
        _ ≤ C1 * (Cj *
              ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (σ + 1 + j) T‖) :=
            mul_le_mul_of_nonneg_left hih hC1_nn
        _ = C1 * Cj *
              ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (σ + (j + 1)) T‖ := by
            rw [hord]; ring

omit [BoundarylessManifold I M] in
theorem iteratedCovGradSobolevNorm_le_baseSpectral
    (g : SmoothRiemannianMetric I M) (r s k j : ℕ) (hjk : j ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        iteratedCovGradSobolevNorm g r s k j T ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    iteratedCovGrad_toHs_norm_le (I := I) (M := M) g r s j (2 * (k - j))
  refine ⟨C, hC_nn, fun T => ?_⟩
  have hstep := hC T
  have hord_le : 2 * (k - j) + j ≤ 2 * k := by omega
  have hmono :
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * (k - j) + j) T‖ ≤
        ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ :=
    toHs_norm_mono_order (I := I) (M := M) g hord_le T
  calc iteratedCovGradSobolevNorm g r s k j T
      = ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s + j) (2 * (k - j))
          (iteratedCovGrad g r s j T)‖ := rfl
    _ ≤ C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * (k - j) + j) T‖ :=
        hstep
    _ ≤ C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ :=
        mul_le_mul_of_nonneg_left hmono hC_nn

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem iteratedCovGrad_toSobolev_embedding_Cm_singleNorm
    (g : SmoothRiemannianMetric I M) (r s k m : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        (∑ j ∈ Finset.range (m + 1),
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r (s + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + j)
            ‖(iteratedCovGrad g r s j T).toSection x‖)) ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  classical
  obtain ⟨C0, hC0_pos, hC0⟩ :=
    iteratedCovGrad_toSobolev_embedding_Cm (I := I) (M := M) g r s k m h_super
  have hmk : m ≤ k := by omega
  have h_perdeg : ∀ j : ℕ, ∃ Cj : ℝ, 0 ≤ Cj ∧ (j ≤ m →
      ∀ T : SmoothCcTensor g r s,
        iteratedCovGradSobolevNorm g r s k j T ≤
          Cj * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖) := by
    intro j
    by_cases hjm : j ≤ m
    · have hjk : j ≤ k := le_trans hjm hmk
      obtain ⟨Cj, hCj_nn, hCj⟩ :=
        iteratedCovGradSobolevNorm_le_baseSpectral (I := I) (M := M) g r s k j hjk
      exact ⟨Cj, hCj_nn, fun _ => hCj⟩
    · exact ⟨0, le_refl 0, fun h => absurd h hjm⟩
  choose Cfun hCfun_nn hCfun using h_perdeg
  set Csum : ℝ := ∑ j ∈ Finset.range (m + 1), Cfun j with hCsum_def
  have hCsum_nn : 0 ≤ Csum :=
    Finset.sum_nonneg (fun j _ => hCfun_nn j)
  refine ⟨C0 * (Csum + 1), by positivity, fun T x => ?_⟩
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have h_sum_le :
      (∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T) ≤
        Csum * N := by
    rw [hCsum_def, Finset.sum_mul]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
    exact hCfun j hjm T
  refine le_trans (hC0 T x) ?_
  calc C0 * ∑ j ∈ Finset.range (m + 1), iteratedCovGradSobolevNorm g r s k j T
      ≤ C0 * (Csum * N) :=
        mul_le_mul_of_nonneg_left h_sum_le (le_of_lt hC0_pos)
    _ ≤ C0 * (Csum + 1) * N := by nlinarith [hN_nn, hC0_pos.le, hCsum_nn]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem iteratedCovGrad_toSobolev_embedding_C2_singleNorm
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g 0 2) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + j)
            ‖(iteratedCovGrad g 0 2 j T).toSection x‖)) ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) T‖ := by
  have h_super' : 2 * k > Module.finrank ℝ E + 2 * 2 := by omega
  exact iteratedCovGrad_toSobolev_embedding_Cm_singleNorm (I := I) (M := M)
    g 0 2 k 2 h_super'

end AnalyticCore

end DifferentialGeometry.PDE.RicciFlow

end
