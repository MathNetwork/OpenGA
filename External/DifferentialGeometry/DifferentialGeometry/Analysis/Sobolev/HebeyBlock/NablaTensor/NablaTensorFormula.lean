import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Inclusion
import DifferentialGeometry.Tensor.Multilinear.HsBoundOp

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle DifferentialGeometry
open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection Tensor0SBundle
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff BigOperators ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem nabla_equals_partial_plus_christoffel_on_tensors
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)
        + (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        - (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) :=
  chartTensorRSCovariantDerivative_def (I := I) r s g α T X b

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma nabla_tensor_toEucl_symm_preimage_target (α : M) :
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
private lemma nabla_tensor_raw_pull_contDiffOn
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
private lemma nabla_tensor_iteratedFDeriv_chain_rule
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
    nabla_tensor_toEucl_symm_preimage_target α
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
private lemma basis_sum_sq_le_opNorm_sq_E
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
      |(iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 ≤
      ((Module.finrank ℝ E : ℝ) ^ j) *
        (‖((toEuclidean (E := E)).symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ ^ (2 * j)) *
        ‖iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm)
            ((toEuclidean (E := E)).symm y)‖ ^ 2 := by
  classical
  set Lsymm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E :=
    ((toEuclidean (E := E)).symm
      : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E) with hLsymm_def
  set A : ContinuousMultilinearMap ℝ
      (fun _ : Fin j => E) ℝ :=
    iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        ((toEuclidean (E := E)).symm y) with hA_def
  set B : ContinuousMultilinearMap ℝ
      (fun _ : Fin j => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ :=
    iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y with hB_def
  have hBeq : B =
      A.compContinuousLinearMap (fun _ : Fin j => Lsymm) := by
    rw [hB_def, hA_def, hLsymm_def]
    exact nabla_tensor_iteratedFDeriv_chain_rule
      (I := I) (M := M) g r s T α Idx Jdx j hy
  have hLsymm_nonneg : 0 ≤ ‖Lsymm‖ := norm_nonneg _
  have hB_norm_le : ‖B‖ ≤ ‖A‖ * (‖Lsymm‖ ^ j) := by
    calc ‖B‖
        = ‖A.compContinuousLinearMap (fun _ : Fin j => Lsymm)‖ := by rw [hBeq]
      _ ≤ ‖A‖ * ∏ _ : Fin j, ‖Lsymm‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖A‖ * (‖Lsymm‖ ^ j) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hAnn : 0 ≤ ‖A‖ := norm_nonneg _
  have hBnn : 0 ≤ ‖B‖ := norm_nonneg _
  have hB_sq_le : ‖B‖ ^ 2 ≤ (‖A‖ ^ 2) * (‖Lsymm‖ ^ (2 * j)) := by
    have h1 : ‖B‖ ^ 2 ≤ (‖A‖ * (‖Lsymm‖ ^ j)) ^ 2 :=
      pow_le_pow_left₀ hBnn hB_norm_le 2
    have h2 : (‖A‖ * (‖Lsymm‖ ^ j)) ^ 2 =
        (‖A‖ ^ 2) * (‖Lsymm‖ ^ (2 * j)) := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, mul_comm j 2]
    rw [h2] at h1
    exact h1
  have h_per_basis : ∀ (basisIdx : Fin j → Fin (Module.finrank ℝ E)),
      |B (fun i => EuclideanSpace.basisFun
          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 ≤ ‖B‖ ^ 2 := by
    intro basisIdx
    have h_abs_eq :
        |B (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| =
        ‖B (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))‖ :=
      (Real.norm_eq_abs _).symm
    have h_opNorm : ‖B (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))‖ ≤
        ‖B‖ * ∏ i : Fin j, ‖EuclideanSpace.basisFun
          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)‖ :=
      B.le_opNorm _
    have h_prod_one : ∏ i : Fin j, ‖EuclideanSpace.basisFun
          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)‖ = 1 := by
      refine Finset.prod_eq_one ?_
      intro i _
      exact OrthonormalBasis.norm_eq_one _ _
    rw [h_prod_one, mul_one] at h_opNorm
    have h_apply_nn : 0 ≤ ‖B (fun i => EuclideanSpace.basisFun
          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))‖ := norm_nonneg _
    rw [h_abs_eq]
    have := pow_le_pow_left₀ h_apply_nn h_opNorm 2
    exact this
  have h_card : (Finset.univ :
      Finset (Fin j → Fin (Module.finrank ℝ E))).card =
      (Module.finrank ℝ E) ^ j := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_sum_le : ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
      |B (fun i => EuclideanSpace.basisFun
          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 ≤
        ((Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E))).card : ℝ) *
          ‖B‖ ^ 2 := by
    have h_le_const :
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          |B (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 ≤
        ∑ _ : Fin j → Fin (Module.finrank ℝ E), ‖B‖ ^ 2 :=
      Finset.sum_le_sum (fun basisIdx _ => h_per_basis basisIdx)
    rw [Finset.sum_const, nsmul_eq_mul] at h_le_const
    exact h_le_const
  rw [h_card] at h_sum_le
  have hnj_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ j := by
    positivity
  have h_combine : ((Module.finrank ℝ E : ℝ) ^ j) * ‖B‖ ^ 2 ≤
      ((Module.finrank ℝ E : ℝ) ^ j) *
        ((‖A‖ ^ 2) * (‖Lsymm‖ ^ (2 * j))) :=
    mul_le_mul_of_nonneg_left hB_sq_le hnj_nn
  have h_cast : ((Finset.univ :
      Finset (Fin j → Fin (Module.finrank ℝ E))).card : ℝ) =
      ((Module.finrank ℝ E) ^ j : ℝ) := by
    rw [h_card]; push_cast; rfl
  calc ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
        |B (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2
      ≤ (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) * ‖B‖ ^ 2 := by
        exact_mod_cast h_sum_le
    _ = ((Module.finrank ℝ E : ℝ) ^ j) * ‖B‖ ^ 2 := by push_cast; rfl
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ j) *
          ((‖A‖ ^ 2) * (‖Lsymm‖ ^ (2 * j))) := h_combine
    _ = ((Module.finrank ℝ E : ℝ) ^ j) *
          (‖Lsymm‖ ^ (2 * j)) * ‖A‖ ^ 2 := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private lemma nabla_tensor_pouPull_contOn (α : M) :
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
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma per_alpha_j_basis_integral_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (CE : ℝ)
    (hCE : ((Module.finrank ℝ E : ℝ) ^ j) *
        (‖((toEuclidean (E := E)).symm :
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ ^ (2 * j))
            ≤ CE)
    (hCE_nn : 0 ≤ CE) :
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
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) ≤
      ENNReal.ofReal CE *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  have h_pt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
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
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) ≤
        ENNReal.ofReal CE *
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2) := by
    intro y hy
    set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
    have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
    set Asq : ℝ := ‖iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        ((toEuclidean (E := E)).symm y)‖ ^ 2 with hAsq_def
    have hAsq_nn : 0 ≤ Asq := sq_nonneg _
    have h_per_term_nn : ∀ basisIdx : Fin j → Fin (Module.finrank ℝ E),
        0 ≤ ρ *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α
                    Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 :=
      fun _ => mul_nonneg hρ_nn (sq_nonneg _)
    have h_sum_ofReal :
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          ENNReal.ofReal
            (ρ *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        Idx Jdx
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) =
        ENNReal.ofReal
          (∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ρ *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        Idx Jdx
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) :=
      (ENNReal.ofReal_sum_of_nonneg (fun b _ => h_per_term_nn b)).symm
    have h_factor_rho :
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          ρ *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 =
        ρ * ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        Idx Jdx
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    have h_basis_bound := basis_sum_sq_le_opNorm_sq_E
      (I := I) (M := M) g r s T α Idx Jdx j hy
    have h_inner_le : ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
        |(iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 ≤
        CE * Asq := by
      calc ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm) y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2
          ≤ ((Module.finrank ℝ E : ℝ) ^ j) *
              (‖((toEuclidean (E := E)).symm :
                  EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ ^
                  (2 * j)) * Asq := h_basis_bound
        _ ≤ CE * Asq :=
            mul_le_mul_of_nonneg_right hCE hAsq_nn
    have h_rho_le : ρ * ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 ≤
        ρ * (CE * Asq) :=
      mul_le_mul_of_nonneg_left h_inner_le hρ_nn
    have h_rearr : ρ * (CE * Asq) = CE * (ρ * Asq) := by ring
    have hρAsq_nn : 0 ≤ ρ * Asq := mul_nonneg hρ_nn hAsq_nn
    rw [h_sum_ofReal, h_factor_rho]
    have h_ofReal_le : ENNReal.ofReal (ρ * (CE * Asq)) =
        ENNReal.ofReal CE * ENNReal.ofReal (ρ * Asq) := by
      rw [h_rearr, ENNReal.ofReal_mul hCE_nn]
    calc ENNReal.ofReal (ρ * _)
        ≤ ENNReal.ofReal (ρ * (CE * Asq)) := ENNReal.ofReal_le_ofReal h_rho_le
      _ = ENNReal.ofReal CE * ENNReal.ofReal (ρ * Asq) := h_ofReal_le
  have h_meas_set : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_basis_aem : ∀ basisIdx : Fin j → Fin (Module.finrank ℝ E),
      AEMeasurable
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
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
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2))
        ((volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
    intro basisIdx
    have h_pou := nabla_tensor_pouPull_contOn (I := I) (M := M) α
    have h_cdOn := nabla_tensor_raw_pull_contDiffOn
      (I := I) (M := M) g r s T α Idx Jdx
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_iter_contOn : ContinuousOn
        (iteratedFDeriv ℝ j
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
    have h_eval_contOn := h_apply.comp_continuousOn h_iter_contOn
    have h_full_cont : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_pou.mul (h_eval_contOn.abs.pow 2)
    have h_aesm : AEStronglyMeasurable
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ((volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
      h_full_cont.aestronglyMeasurable h_meas_set
    exact ENNReal.measurable_ofReal.comp_aemeasurable h_aesm.aemeasurable
  have h_swap_sum :
      (∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
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
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
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
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [MeasureTheory.lintegral_finset_sum' _ (fun basisIdx _ => h_basis_aem basisIdx)]
  have h_pt_le :
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
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ≤
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal CE *
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
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
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ENNReal.ofReal CE *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm)
                  ((toEuclidean (E := E)).symm y)‖ ^ 2)
          ∂(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc _
      = _ := h_swap_sum
    _ ≤ _ := h_pt_le
    _ = _ := h_pull_const

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem hs_le_pou_uniform
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal := by
  classical
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : 0 ≤ n := by
    rw [hn_def]; exact Nat.cast_nonneg _
  set Msym : ℝ :=
    ‖((toEuclidean (E := E)).symm :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖ with hMsym_def
  have hMsym_nn : 0 ≤ Msym := norm_nonneg _
  set D : ℝ := (1 + n ^ (2 * k)) * (1 + Msym ^ (4 * k)) with hD_def
  have hD_nn : 0 ≤ D := by
    have h1 : (0 : ℝ) ≤ 1 + n ^ (2 * k) := by
      have hpos : (0 : ℝ) ≤ n ^ (2 * k) := pow_nonneg hn_nn _
      linarith
    have h2 : (0 : ℝ) ≤ 1 + Msym ^ (4 * k) := by
      have hpos : (0 : ℝ) ≤ Msym ^ (4 * k) := pow_nonneg hMsym_nn _
      linarith
    exact mul_nonneg h1 h2
  have hD_dom : ∀ j ∈ Finset.range (2 * k + 1),
      n ^ j * Msym ^ (2 * j) ≤ D := by
    intro j hj
    have hj_le : j ≤ 2 * k := by
      have : j < 2 * k + 1 := Finset.mem_range.mp hj
      omega
    have h_n_dom : n ^ j ≤ 1 + n ^ (2 * k) := by
      by_cases h_n_ge_one : 1 ≤ n
      · have h1 : n ^ j ≤ n ^ (2 * k) :=
          pow_le_pow_right₀ h_n_ge_one hj_le
        have hpos : (0 : ℝ) ≤ n ^ (2 * k) := pow_nonneg hn_nn _
        linarith
      · have h_n_lt : n < 1 := lt_of_not_ge h_n_ge_one
        have h_le_one : n ^ j ≤ 1 := pow_le_one₀ hn_nn (le_of_lt h_n_lt)
        have hpos : (0 : ℝ) ≤ n ^ (2 * k) := pow_nonneg hn_nn _
        linarith
    have h_Msym_dom : Msym ^ (2 * j) ≤ 1 + Msym ^ (4 * k) := by
      by_cases h_M_ge_one : 1 ≤ Msym
      · have h2j_le_4k : 2 * j ≤ 4 * k := by omega
        have h1 : Msym ^ (2 * j) ≤ Msym ^ (4 * k) :=
          pow_le_pow_right₀ h_M_ge_one h2j_le_4k
        have hpos : (0 : ℝ) ≤ Msym ^ (4 * k) := pow_nonneg hMsym_nn _
        linarith
      · have h_M_lt : Msym < 1 := lt_of_not_ge h_M_ge_one
        have h_le_one : Msym ^ (2 * j) ≤ 1 :=
          pow_le_one₀ hMsym_nn (le_of_lt h_M_lt)
        have hpos : (0 : ℝ) ≤ Msym ^ (4 * k) := pow_nonneg hMsym_nn _
        linarith
    have h_nj_nn : (0 : ℝ) ≤ n ^ j := pow_nonneg hn_nn _
    have h_Mj_nn : (0 : ℝ) ≤ Msym ^ (2 * j) := pow_nonneg hMsym_nn _
    have h_1pn_nn : (0 : ℝ) ≤ 1 + n ^ (2 * k) := by
      have := pow_nonneg hn_nn (2 * k); linarith
    have h_1pM_nn : (0 : ℝ) ≤ 1 + Msym ^ (4 * k) := by
      have := pow_nonneg hMsym_nn (4 * k); linarith
    calc n ^ j * Msym ^ (2 * j)
        ≤ (1 + n ^ (2 * k)) * Msym ^ (2 * j) :=
          mul_le_mul_of_nonneg_right h_n_dom h_Mj_nn
      _ ≤ (1 + n ^ (2 * k)) * (1 + Msym ^ (4 * k)) :=
          mul_le_mul_of_nonneg_left h_Msym_dom h_1pn_nn
  refine ⟨Real.sqrt D, Real.sqrt_nonneg _, ?_⟩
  intro T
  have hpou_ne_top :
      tensorPouSobolevNorm (I := I) (M := M) g k T ≠ ⊤ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevNorm_ne_top
      (I := I) (M := M) g k T
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
  have h_main : tsumHs ≤ ENNReal.ofReal D * tsumPou := by
    rw [htsumHs_def, htsumPou_def]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun α => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun IJ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact per_alpha_j_basis_integral_bound
      (I := I) (M := M) g r s T α IJ.1 IJ.2 j D (hD_dom j hj) hD_nn
  have h_rpow_le : tsumHs ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal D * tsumPou) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h_main (by norm_num)
  have h_split :
      (ENNReal.ofReal D * tsumPou) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt D) * tsumPou ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
    congr 1
    rw [ENNReal.ofReal_rpow_of_nonneg hD_nn (by norm_num : (0:ℝ) ≤ 1 / 2)]
    rw [← Real.sqrt_eq_rpow]
  rw [h_split] at h_rpow_le
  have h_tsumPou_ne_top : tsumPou ≠ ⊤ := by
    have hpou_lt_top : tensorPouSobolevNorm (I := I) (M := M) g k T < ⊤ :=
      lt_of_le_of_ne le_top hpou_ne_top
    rw [tensorPouSobolevNorm_eq, ← htsumPou_def] at hpou_lt_top
    intro h_top
    rw [h_top] at hpou_lt_top
    have hrw := ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1/2)
    rw [hrw] at hpou_lt_top
    exact hpou_lt_top.ne rfl
  have h_RHS_split_ne_top :
      ENNReal.ofReal (Real.sqrt D) * tsumPou ^ (1 / 2 : ℝ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
      h_tsumPou_ne_top).ne
  have h_toReal_mono :
      (tsumHs ^ (1 / 2 : ℝ)).toReal ≤
        (ENNReal.ofReal (Real.sqrt D) * tsumPou ^ (1 / 2 : ℝ)).toReal :=
    ENNReal.toReal_mono h_RHS_split_ne_top h_rpow_le
  calc (tsumHs ^ (1 / 2 : ℝ)).toReal
      ≤ (ENNReal.ofReal (Real.sqrt D) * tsumPou ^ (1 / 2 : ℝ)).toReal :=
        h_toReal_mono
    _ = (ENNReal.ofReal (Real.sqrt D)).toReal * (tsumPou ^ (1 / 2 : ℝ)).toReal := by
        rw [ENNReal.toReal_mul]
    _ = Real.sqrt D * (tsumPou ^ (1 / 2 : ℝ)).toReal := by
        rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nabla_tensor_single_step_formula
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal :=
  hs_le_pou_uniform (I := I) (M := M) g r s k

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nabla_tensor_iterated_Hk_formula
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal :=
  hs_le_pou_uniform (I := I) (M := M) g r s k

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
