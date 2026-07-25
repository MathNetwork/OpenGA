import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.ChartFrameNorm
import DifferentialGeometry.Tensor.Multilinear.HsBoundOp


namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff BigOperators ENNReal
open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma toEucl_symm_preimage_target (α : M) :
    ((toEuclidean (E := E)).symm) ⁻¹' (extChartAt I α).target =
      chartTargetEuclid (I := I) (M := M) α := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · refine ⟨(toEuclidean (E := E)).symm y, hy, ?_⟩
    exact (toEuclidean (E := E)).apply_symm_apply y
  · rcases hy with ⟨z, hz_tgt, hz_eq⟩
    have h_eq : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [Set.mem_preimage, h_eq]; exact hz_tgt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma raw_pull_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_pull_contDiffOn :
      ContDiffOn ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
    have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
        ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm α
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
      refine h_raw_smoothOn.comp h_extSymm ?_
      intro y hy
      change (extChartAt I α).symm y ∈ (chartAt H α).source
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target hy
    exact h_comp_mdiff.contDiffOn
  have h_toEucl_symm_smooth :
      ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_tgt, hz_eq⟩
    have h_eq : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [h_eq]; exact hz_tgt
  exact h_raw_pull_contDiffOn.comp
    h_toEucl_symm_smooth.contDiffOn h_maps

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma iteratedFDeriv_chain_rule
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y =
      (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)).compContinuousLinearMap
        (fun _ : Fin j => ((toEuclidean (E := E)).symm
          : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)) := by
  classical
  set f : E → ℝ :=
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
      ∘ (extChartAt I α).symm with hf_def
  set L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    (toEuclidean (E := E)).symm with hL_def
  have hpre : L ⁻¹' (extChartAt I α).target =
      chartTargetEuclid (I := I) (M := M) α :=
    toEucl_symm_preimage_target α
  have hLy : L y ∈ (extChartAt I α).target := by
    rw [← hpre] at hy; exact hy
  have hOpenT : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have hOpenCT : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hUniqT : UniqueDiffOn ℝ (extChartAt I α).target :=
    hOpenT.uniqueDiffOn
  have h_chain : iteratedFDerivWithin ℝ j (f ∘ L)
      (L ⁻¹' (extChartAt I α).target) y =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDerivWithin ℝ j f (extChartAt I α).target (L y))
        (fun _ : Fin j => (L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)) :=
    ContinuousLinearEquiv.iteratedFDerivWithin_comp_right
      (g := L) (f := f) hUniqT hLy j
  have h_swap_left :
      iteratedFDerivWithin ℝ j (f ∘ L)
          (L ⁻¹' (extChartAt I α).target) y =
        iteratedFDeriv ℝ j (f ∘ L) y := by
    rw [hpre]
    exact iteratedFDerivWithin_of_isOpen j hOpenCT hy
  have h_swap_right :
      iteratedFDerivWithin ℝ j f (extChartAt I α).target (L y) =
        iteratedFDeriv ℝ j f (L y) :=
    iteratedFDerivWithin_of_isOpen j hOpenT hLy
  rw [h_swap_left, h_swap_right] at h_chain
  exact h_chain

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma opNorm_sq_le_basis_sum_sq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm)
          ((toEuclidean (E := E)).symm y)‖ ^ 2 ≤
      (‖((toEuclidean (E := E)) :
            E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j)) *
        ∑ idx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun k => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (idx k))| ^ 2 := by
  classical
  set f : E → ℝ :=
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
      ∘ (extChartAt I α).symm with hf_def
  set Leq : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (E := E) with hLeq_def
  set A : ContinuousMultilinearMap ℝ
      (fun _ : Fin j => E) ℝ := iteratedFDeriv ℝ j f (Leq.symm y) with hA_def
  set B : ContinuousMultilinearMap ℝ
      (fun _ : Fin j => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ :=
    iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y with hB_def
  have hBeq : B =
      A.compContinuousLinearMap
        (fun _ : Fin j => (Leq.symm
          : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)) := by
    rw [hB_def, hA_def]
    exact iteratedFDeriv_chain_rule
      (I := I) (M := M) g r s T α Idx Jdx j hy
  have hAeq : A =
      B.compContinuousLinearMap
        (fun _ : Fin j => (Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [hBeq]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  have hLnonneg : 0 ≤
      ‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ :=
    norm_nonneg _
  have hA_le : ‖A‖ ≤ ‖B‖ *
      (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ j) := by
    calc ‖A‖
        = ‖B.compContinuousLinearMap
            (fun _ : Fin j => (Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))‖ := by
          rw [hAeq]
      _ ≤ ‖B‖ * ∏ _ : Fin j,
          ‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖B‖ * (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ j) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hAnonneg : 0 ≤ ‖A‖ := norm_nonneg _
  have hBnonneg : 0 ≤ ‖B‖ := norm_nonneg _
  have hA_sq_le : ‖A‖ ^ 2 ≤
      (‖B‖ ^ 2) *
        (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j)) := by
    have h1 : ‖A‖ ^ 2 ≤
        (‖B‖ * (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ j)) ^ 2 :=
      pow_le_pow_left₀ hAnonneg hA_le 2
    have h2 :
        (‖B‖ * (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ j)) ^ 2 =
          (‖B‖ ^ 2) *
            (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j)) := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, mul_comm j 2]
    rw [h2] at h1
    exact h1
  have hB_sq_le : ‖B‖ ^ 2 ≤
      ∑ idx : Fin j → Fin (Module.finrank ℝ E),
        |B (fun k => EuclideanSpace.basisFun
          (Fin (Module.finrank ℝ E)) ℝ (idx k))| ^ 2 :=
    ContinuousMultilinearMap.opNorm_sq_le_sum_sq_basisEval
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ) B
  have hLpow2_nonneg :
      0 ≤ (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j)) :=
    pow_nonneg hLnonneg _
  calc ‖A‖ ^ 2
      ≤ (‖B‖ ^ 2) *
          (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j)) :=
        hA_sq_le
    _ ≤ (∑ idx : Fin j → Fin (Module.finrank ℝ E),
          |B (fun k => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (idx k))| ^ 2) *
          (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j)) := by
        exact mul_le_mul_of_nonneg_right hB_sq_le hLpow2_nonneg
    _ = (‖(Leq : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j)) *
          (∑ idx : Fin j → Fin (Module.finrank ℝ E),
            |B (fun k => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (idx k))| ^ 2) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma pouPull_contOn (α : M) :
    ContinuousOn
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hPOU_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).continuous
  have hSymmCont : ContinuousOn ((extChartAt I α).symm)
      (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have h_toEucl_cont : Continuous
      ((toEuclidean (E := E)).symm : _ → _) :=
    (toEuclidean (E := E)).symm.continuous
  have h_inner : ContinuousOn
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hSymmCont.comp h_toEucl_cont.continuousOn ?_
    intro y hy
    rcases hy with ⟨z, hz_tgt, hz_eq⟩
    rw [← hz_eq]
    change (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
    rw [(toEuclidean (E := E)).symm_apply_apply]
    exact hz_tgt
  exact hPOU_cont.comp_continuousOn' h_inner

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma iteratedFDeriv_basisEval_contOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_cdOn := raw_pull_contDiffOn (I := I) (M := M) g r s T α Idx Jdx
  have h_iter_contOn :
      ContinuousOn (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    have h_cd : ContDiffAt ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y :=
      h_cdOn.contDiffAt (h_open.mem_nhds hy)
    exact (h_cd.continuousAt_iteratedFDeriv (k := j)
      (by exact_mod_cast le_top)).continuousWithinAt
  have h_apply : Continuous
      (fun A : ContinuousMultilinearMap ℝ
          (fun _ : Fin j => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ =>
        A (fun i => EuclideanSpace.basisFun
          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))) :=
    continuous_eval_const _
  exact h_apply.comp_continuousOn h_iter_contOn

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hsIntegrand_real_contOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_pou := pouPull_contOn (I := I) (M := M) α
  have h_eval := iteratedFDeriv_basisEval_contOn
    (I := I) (M := M) g r s T α Idx Jdx j basisIdx
  exact h_pou.mul (h_eval.abs.pow 2)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hsIntegrand_real_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
      ((volume :
        Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_cont := hsIntegrand_real_contOn
    (I := I) (M := M) g r s T α Idx Jdx j basisIdx
  have h_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  exact h_cont.aestronglyMeasurable h_meas

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hsIntegrand_aemeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2))
      ((volume :
        Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (hsIntegrand_real_aestronglyMeasurable
      (I := I) (M := M) g r s T α Idx Jdx j basisIdx).aemeasurable

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma per_alpha_j_integral_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (CE : ℝ)
    (hCE : ‖((toEuclidean (E := E)) :
        E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j) ≤ CE)
    (hCE_nn : 0 ≤ CE) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ≤
      ENNReal.ofReal CE *
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          Idx Jdx
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm)
              ((toEuclidean (E := E)).symm y)‖ ^ 2) ≤
        ENNReal.ofReal CE *
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          Idx Jdx
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) := by
    intro y hy
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    set normsqA : ℝ := ‖iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        ((toEuclidean (E := E)).symm y)‖ ^ 2 with hnormsqA_def
    have hnormsqA_nn : 0 ≤ normsqA := sq_nonneg _
    set HSsum : ℝ := ∑ idx : Fin j → Fin (Module.finrank ℝ E),
        |(iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun k => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (idx k))| ^ 2 with hHSsum_def
    have hHSsum_nn : 0 ≤ HSsum :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hpt : normsqA ≤ CE * HSsum := by
      have h_op := opNorm_sq_le_basis_sum_sq (I := I) (M := M) g r s T α Idx Jdx j hy
      calc normsqA = _ := rfl
        _ ≤ ‖((toEuclidean (E := E)) :
              E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ (2 * j) *
                HSsum := h_op
        _ ≤ CE * HSsum :=
            mul_le_mul_of_nonneg_right hCE hHSsum_nn
    have hmul : ρ * normsqA ≤ ρ * (CE * HSsum) :=
      mul_le_mul_of_nonneg_left hpt hρ_nn
    have hofReal_le : ENNReal.ofReal (ρ * normsqA) ≤
        ENNReal.ofReal (ρ * (CE * HSsum)) :=
      ENNReal.ofReal_le_ofReal hmul
    have hCρhs_eq : ρ * (CE * HSsum) = CE * (ρ * HSsum) := by ring
    have hρHS_nn : 0 ≤ ρ * HSsum := mul_nonneg hρ_nn hHSsum_nn
    have h_per_term_nn : ∀ idx : Fin j → Fin (Module.finrank ℝ E),
        0 ≤ ρ *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun k => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (idx k))| ^ 2 :=
      fun idx => mul_nonneg hρ_nn (sq_nonneg _)
    have h_ofReal_split :
        ENNReal.ofReal (ρ * (CE * HSsum)) =
          ENNReal.ofReal CE *
            ∑ idx : Fin j → Fin (Module.finrank ℝ E),
              ENNReal.ofReal (ρ *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          Idx Jdx
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm) y)
                    (fun k => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (idx k))| ^ 2) := by
      rw [hCρhs_eq, ENNReal.ofReal_mul hCE_nn]
      congr 1
      rw [hHSsum_def, Finset.mul_sum,
        ENNReal.ofReal_sum_of_nonneg
          (fun idx _ => mul_nonneg hρ_nn (sq_nonneg _))]
    rw [h_ofReal_split] at hofReal_le
    exact hofReal_le
  have h_meas_set : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_set_le :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm)
                ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ≤
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal CE *
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          Idx Jdx
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    refine MeasureTheory.setLIntegral_mono_ae' h_meas_set ?_
    refine ae_of_all _ ?_
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact fun _ => h_pt y hy
    · intro hy'; exact absurd hy' hy
  have h_pull_const :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal CE *
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            Idx Jdx
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ENNReal.ofReal CE *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          Idx Jdx
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h_swap_sum :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          Idx Jdx
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        Idx Jdx
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    refine MeasureTheory.lintegral_finset_sum' _ ?_
    intro basisIdx _
    exact hsIntegrand_aemeasurable
      (I := I) (M := M) g r s T α Idx Jdx j basisIdx
  calc _
      ≤ _ := h_set_le
    _ = _ := h_pull_const
    _ = _ := by rw [h_swap_sum]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem uniform_chart_bounds_from_compactness
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal := by
  classical
  set Lnorm : ℝ :=
    ‖((toEuclidean (E := E)) :
      E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ with hLnorm_def
  have hLnorm_nonneg : 0 ≤ Lnorm := norm_nonneg _
  set CE : ℝ := 1 + Lnorm ^ (4 * k) with hCE_def
  have hCE_nonneg : 0 ≤ CE := by
    have h1 : (0 : ℝ) ≤ Lnorm ^ (4 * k) := pow_nonneg hLnorm_nonneg _
    linarith
  have hCE_dom : ∀ j ∈ Finset.range (2 * k + 1), Lnorm ^ (2 * j) ≤ CE := by
    intro j hj
    have hj_le : j ≤ 2 * k := by
      have : j < 2 * k + 1 := Finset.mem_range.mp hj
      omega
    by_cases hL_ge_one : 1 ≤ Lnorm
    · have h2j_le_4k : 2 * j ≤ 4 * k := by omega
      have hpow_le : Lnorm ^ (2 * j) ≤ Lnorm ^ (4 * k) :=
        pow_le_pow_right₀ hL_ge_one h2j_le_4k
      have hpow_pos : (0 : ℝ) ≤ Lnorm ^ (4 * k) := pow_nonneg hLnorm_nonneg _
      linarith
    · have hL_lt : Lnorm < 1 := lt_of_not_ge hL_ge_one
      have h_le_one : Lnorm ^ (2 * j) ≤ 1 :=
        pow_le_one₀ hLnorm_nonneg (le_of_lt hL_lt)
      have hpow_pos : (0 : ℝ) ≤ Lnorm ^ (4 * k) := pow_nonneg hLnorm_nonneg _
      linarith
  refine ⟨Real.sqrt CE, Real.sqrt_nonneg _, ?_⟩
  intro T
  have hHs_lt_top :
      tensorPouSobolevHsNorm (I := I) (M := M) g k T < ⊤ :=
    tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g k T
  have hHs_ne_top :
      tensorPouSobolevHsNorm (I := I) (M := M) g k T ≠ ⊤ := hHs_lt_top.ne
  rw [tensorPouSobolevNorm_eq, tensorPouSobolevHsNorm_eq]
  set tsumPou : ℝ≥0∞ :=
    ∑' α : M,
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm)
                    ((toEuclidean (E := E)).symm y)‖ ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    with htsumPou_def
  set tsumHs : ℝ≥0∞ :=
    ∑' α : M,
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    with htsumHs_def
  have h_main : tsumPou ≤ ENNReal.ofReal CE * tsumHs := by
    rw [htsumPou_def, htsumHs_def]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun α => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun IJ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact per_alpha_j_integral_bound
      (I := I) (M := M) g r s T α IJ.1 IJ.2 j CE (hCE_dom j hj) hCE_nonneg
  have h_rpow_le : tsumPou ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal CE * tsumHs) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h_main (by norm_num)
  have h_split :
      (ENNReal.ofReal CE * tsumHs) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt CE) * tsumHs ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
    congr 1
    rw [ENNReal.ofReal_rpow_of_nonneg hCE_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    rw [← Real.sqrt_eq_rpow]
  rw [h_split] at h_rpow_le
  have h_tsumHs_eq_normSq :
      tsumHs = tensorPouSobolevHsNormSq (I := I) (M := M) g k T := by
    rw [htsumHs_def]
    exact (tensorPouSobolevHsNormSq_eq_inner_sum (I := I) (M := M) g k T).symm
  have h_tsumHs_ne_top : tsumHs ≠ ⊤ := by
    rw [h_tsumHs_eq_normSq]
    exact (tensorPouSobolevHsNormSq_lt_top (I := I) (M := M) g k T).ne
  have h_tsumPou_rpow_ne_top :
      tsumPou ^ (1 / 2 : ℝ) ≠ ⊤ := by
    have h_finRHS : ENNReal.ofReal CE * tsumHs ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_tsumHs_ne_top
    have h_tsumPou_ne_top : tsumPou ≠ ⊤ :=
      ne_top_of_le_ne_top h_finRHS h_main
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
      h_tsumPou_ne_top).ne
  have h_RHS_split_ne_top :
      ENNReal.ofReal (Real.sqrt CE) * tsumHs ^ (1 / 2 : ℝ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
      h_tsumHs_ne_top).ne
  have h_toReal_mono :
      (tsumPou ^ (1 / 2 : ℝ)).toReal ≤
        (ENNReal.ofReal (Real.sqrt CE) * tsumHs ^ (1 / 2 : ℝ)).toReal :=
    ENNReal.toReal_mono h_RHS_split_ne_top h_rpow_le
  calc (tsumPou ^ (1 / 2 : ℝ)).toReal
      ≤ (ENNReal.ofReal (Real.sqrt CE) * tsumHs ^ (1 / 2 : ℝ)).toReal :=
        h_toReal_mono
    _ = (ENNReal.ofReal (Real.sqrt CE)).toReal * (tsumHs ^ (1 / 2 : ℝ)).toReal := by
        rw [ENNReal.toReal_mul]
    _ = Real.sqrt CE * (tsumHs ^ (1 / 2 : ℝ)).toReal := by
        rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
