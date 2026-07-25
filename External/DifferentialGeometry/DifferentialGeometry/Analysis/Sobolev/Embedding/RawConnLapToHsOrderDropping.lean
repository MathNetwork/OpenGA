import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartComponentSecondCovDerivFormula
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.SecondCovDerivChartProjEuclidGlobal
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartCoordFormulaT0Linear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapMinusInvGramPrincipalSmoothCoeff
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import DifferentialGeometry.Tensor.Multilinear.HsBoundOp
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound
import DifferentialGeometry.Geometry.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.CovApplyFrameToCoordExpansion
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentFormula
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDroppingCentredFrameInvGramExpansion
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDroppingComponentL2NormHsZeroBound


namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

section InnerProductSpaceModel

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

section RawConnLapOrderDrop

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor
open Tensor0SBundle

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def rawConnLapPull (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
    ∘ (extChartAt I α).symm
    ∘ (toEuclidean (E := E)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rawConnLapPull_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) =
      rawConnLapPull (I := I) (M := M) g r s T α Idx Jdx := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rawConnLapPull_contDiffOn (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  refine (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
    g r s T α Idx Jdx).congr (fun y hy => ?_)
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma rawConnLapPull_contDiffAt (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α Idx Jdx) y :=
  (rawConnLapPull_contDiffOn (I := I) (M := M) g r s T α Idx Jdx).contDiffAt
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy)

private noncomputable def rawConnLapRhsHsContent (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M) (y : EuclN) : ℝ :=
  ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    ∑ l ∈ Finset.range (2 * (k + 1) + 1),
      ∑ bIdx : Fin l → Fin (Module.finrank ℝ E),
        |(iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rawConnLapRhsHsContent_nonneg (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M) (y : EuclN) :
    0 ≤ rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rawConnLapPull_iteratedFDeriv_norm_sq_le_rhsContent
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (l : ℕ) (hl : l ≤ 2 * (k + 1)) (y : EuclN) :
    ‖iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2 ≤
      rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y := by
  classical
  set basisSum : ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) → ℕ → ℝ :=
    fun q' l' => ∑ bIdx : Fin l' → Fin (Module.finrank ℝ E),
      |(iteratedFDeriv ℝ l' (rawConnLapPull (I := I) (M := M) g r s T α q'.1 q'.2) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 with hbasisSum_def
  have hbasisSum_nn : ∀ q' l', 0 ≤ basisSum q' l' :=
    fun q' l' => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_op : ‖iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2 ≤
      basisSum q l :=
    ContinuousMultilinearMap.opNorm_sq_le_sum_sq_basisEval
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ)
      (iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
  refine le_trans h_op ?_
  have h_unfold : rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y =
      ∑ q' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ l' ∈ Finset.range (2 * (k + 1) + 1), basisSum q' l' := rfl
  rw [h_unfold]
  have hl_mem : l ∈ Finset.range (2 * (k + 1) + 1) := Finset.mem_range.mpr (by omega)
  have h_inner : basisSum q l ≤ ∑ l' ∈ Finset.range (2 * (k + 1) + 1), basisSum q l' :=
    Finset.single_le_sum (f := fun l' => basisSum q l')
      (fun l' _ => hbasisSum_nn q l') hl_mem
  refine le_trans h_inner ?_
  exact Finset.single_le_sum
    (f := fun q' => ∑ l' ∈ Finset.range (2 * (k + 1) + 1), basisSum q' l')
    (fun q' _ => Finset.sum_nonneg (fun l' _ => hbasisSum_nn q' l'))
    (Finset.mem_univ q)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eq_fderiv_apply (l : Fin (Module.finrank ℝ E)) (u : EuclN → ℝ) :
    euclidPartial (E := E) l u = fun z => fderiv ℝ u z (EuclideanSpace.single l 1) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_contDiffAt
    (l : Fin (Module.finrank ℝ E)) {u : EuclN → ℝ} {y : EuclN}
    (hu : ContDiffAt ℝ ∞ u y) :
    ContDiffAt ℝ ∞ (euclidPartial (E := E) l u) y := by
  have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun z => fderiv ℝ u z) y := by
    have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
    simpa using hu.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
  rw [euclidPartial_eq_fderiv_apply (E := E) l u]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single l (1 : ℝ))).contDiff.contDiffAt.comp y h_fderiv_cdAt

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_iteratedFDeriv_norm_le
    (l : Fin (Module.finrank ℝ E)) {u : EuclN → ℝ} {y : EuclN}
    (hu : ContDiffAt ℝ ∞ u y) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (euclidPartial (E := E) l u) y‖ ≤
      ‖iteratedFDeriv ℝ (m + 1) u y‖ := by
  have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun z => fderiv ℝ u z) y := by
    have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
    simpa using hu.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
  rw [euclidPartial_eq_fderiv_apply (E := E) l u]
  have h_clm := norm_iteratedFDeriv_clm_apply_const
    (𝕜 := ℝ) (f := fun z => fderiv ℝ u z) (c := EuclideanSpace.single l 1)
    (x := y) (n := m) h_fderiv_cdAt (by exact_mod_cast le_top)
  have h_single_norm : ‖(EuclideanSpace.single l (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single]; simp
  have h_fderiv_iter : ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ u z) y‖ =
      ‖iteratedFDeriv ℝ (m + 1) u y‖ := norm_iteratedFDeriv_fderiv
  calc ‖iteratedFDeriv ℝ m (fun z => (fderiv ℝ u z) (EuclideanSpace.single l 1)) y‖
      ≤ ‖(EuclideanSpace.single l (1 : ℝ))‖ *
          ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ u z) y‖ := h_clm
    _ = ‖iteratedFDeriv ℝ (m + 1) u y‖ := by rw [h_single_norm, one_mul, h_fderiv_iter]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contDiffAt_of_contDiffOn_chartTarget (α : M)
    {C : EuclN → ℝ} (hC : ContDiffOn ℝ ∞ C (chartTargetEuclid (I := I) (M := M) α))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ C y :=
  hC.contDiffAt ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rawConnLapProductSummand_iteratedFDeriv_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (C : EuclN → ℝ) (hC : ContDiffOn ℝ ∞ C (chartTargetEuclid (I := I) (M := M) α))
    (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (Fa : EuclN → ℝ) (a : ℕ)
    (hFa_cd : ∀ z : EuclN, z ∈ chartTargetEuclid (I := I) (M := M) α →
        ContDiffAt ℝ ∞ Fa z)
    (hFa_bd : ∀ (m : ℕ) (z : EuclN), z ∈ chartTargetEuclid (I := I) (M := M) α →
        ‖iteratedFDeriv ℝ m Fa z‖ ≤
          ‖iteratedFDeriv ℝ (m + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖)
    (j : ℕ) {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ j (fun z => C z * Fa z) y‖ ≤
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
          ‖iteratedFDeriv ℝ ((j - i) + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ := by
  classical
  set s_set : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_set
  have h_open : IsOpen s_set := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_uniq : UniqueDiffOn ℝ s_set := h_open.uniqueDiffOn
  have hC_cdon : ContDiffOn ℝ (j : WithTop ℕ∞) C s_set := hC.of_le (by exact_mod_cast le_top)
  have hFa_cdon : ContDiffOn ℝ (j : WithTop ℕ∞) Fa s_set := by
    intro z hz
    exact (hFa_cd z hz).of_le (by exact_mod_cast le_top) |>.contDiffWithinAt
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => C z * Fa z) j h_open hy]
  have hmul := norm_iteratedFDerivWithin_mul_le hC_cdon hFa_cdon h_uniq hy
    (le_refl (j : WithTop ℕ∞))
  refine le_trans hmul ?_
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi_le : i ≤ j := by have := Finset.mem_range.mp hi; omega
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := C) i h_open hy,
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Fa) (j - i) h_open hy]
  have hFa_le := hFa_bd (j - i) y hy
  have h_coeff_nn : 0 ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ := by positivity
  calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ * ‖iteratedFDeriv ℝ (j - i) Fa y‖
      ≤ (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
          ‖iteratedFDeriv ℝ ((j - i) + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ :=
        mul_le_mul_of_nonneg_left hFa_le h_coeff_nn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_eventuallyEq_rawConnLapPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) =ᶠ[nhds y]
      rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2 := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  filter_upwards [h_open.mem_nhds hy] with z hz
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma rawConnLapPull_contDiffAt'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y :=
  rawConnLapPull_contDiffAt (I := I) (M := M) g r s T α q.1 q.2 hy

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartialIter_chartPushedRaw_norm_le_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (m : ℕ) {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ m
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) z‖ ≤
      ‖iteratedFDeriv ℝ (m + 0)
        (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖ := by
  rw [Nat.add_zero,
    (chartPushedRaw_eventuallyEq_rawConnLapPull (I := I) (M := M) g r s T α q hz).iteratedFDeriv
      ℝ m |>.self_of_nhds]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartialIter_chartPushedRaw_norm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (k : Fin (Module.finrank ℝ E))
    (m : ℕ) {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ m
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) z‖ ≤
      ‖iteratedFDeriv ℝ (m + 1)
        (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖ := by
  have hev : euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) =ᶠ[nhds z]
      euclidPartial (E := E) k (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) := by
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_fderiv_ev :
        (fun w => fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) w) =ᶠ[nhds z]
          (fun w => fderiv ℝ (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) w) := by
      filter_upwards [h_open.mem_nhds hz] with w hw
      exact Filter.EventuallyEq.fderiv_eq
        (chartPushedRaw_eventuallyEq_rawConnLapPull (I := I) (M := M) g r s T α q hw)
    filter_upwards [h_fderiv_ev] with w hw
    simp only [euclidPartial_def, hw]
  rw [(hev.iteratedFDeriv ℝ m).self_of_nhds]
  exact euclidPartial_iteratedFDeriv_norm_le (E := E) k
    (rawConnLapPull_contDiffAt' (I := I) (M := M) g r s T α q hz) m

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartialIter_chartPushedRaw_norm_le_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (k l : Fin (Module.finrank ℝ E))
    (m : ℕ) {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ‖iteratedFDeriv ℝ m
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)))) z‖ ≤
      ‖iteratedFDeriv ℝ (m + 2)
        (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖ := by
  set u : EuclN → ℝ := rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2 with hu_def
  have hu_cdAt : ∀ {w : EuclN}, w ∈ chartTargetEuclid (I := I) (M := M) α →
      ContDiffAt ℝ ∞ u w := fun hw =>
    rawConnLapPull_contDiffAt' (I := I) (M := M) g r s T α q hw
  have hev_inner : euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) =ᶠ[nhds z]
      euclidPartial (E := E) k u := by
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_fderiv_ev :
        (fun w => fderiv ℝ
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) w) =ᶠ[nhds z]
          (fun w => fderiv ℝ u w) := by
      filter_upwards [h_open.mem_nhds hz] with w hw
      exact Filter.EventuallyEq.fderiv_eq
        (chartPushedRaw_eventuallyEq_rawConnLapPull (I := I) (M := M) g r s T α q hw)
    filter_upwards [h_fderiv_ev] with w hw
    simp only [euclidPartial_def, hw]
  have hev_outer : euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) =ᶠ[nhds z]
      euclidPartial (E := E) l (euclidPartial (E := E) k u) := by
    have h_fderiv_ev :
        (fun w => fderiv ℝ
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) w) =ᶠ[nhds z]
          (fun w => fderiv ℝ (euclidPartial (E := E) k u) w) :=
      hev_inner.fderiv
    filter_upwards [h_fderiv_ev] with w hw
    simp only [euclidPartial_def, hw]
  rw [(hev_outer.iteratedFDeriv ℝ m).self_of_nhds]
  calc ‖iteratedFDeriv ℝ m (euclidPartial (E := E) l (euclidPartial (E := E) k u)) z‖
      ≤ ‖iteratedFDeriv ℝ (m + 1) (euclidPartial (E := E) k u) z‖ :=
        euclidPartial_iteratedFDeriv_norm_le (E := E) l
          (euclidPartial_contDiffAt (E := E) k (hu_cdAt hz)) m
    _ ≤ ‖iteratedFDeriv ℝ (m + 1 + 1) u z‖ :=
        euclidPartial_iteratedFDeriv_norm_le (E := E) k (hu_cdAt hz) (m + 1)
    _ = ‖iteratedFDeriv ℝ (m + 2) u z‖ := by ring_nf

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_raw_contDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)) z :=
  (chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g r s T α q.1 q.2).contDiffAt
    ((chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hz)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartialIter1_chartPushedRaw_contDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (k : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2))) z :=
  euclidPartial_contDiffAt (E := E) k
    (chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α q hz)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma euclidPartialIter2_chartPushedRaw_contDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (k l : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞
      (euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α q.1 q.2)))) z :=
  euclidPartial_contDiffAt (E := E) l
    (euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M) g r s T α q k hz)

private noncomputable def invGramCoeffPull
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y => chartInvGramMatrix (I := I) g α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k l

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private lemma invGramCoeffPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (invGramCoeffPull (I := I) (M := M) g α k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartInvGramMatrix_pullback_contDiffOn_chartTarget (I := I) (M := M) g α k l

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma invGramCoeffPull_at_b
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    invGramCoeffPull (I := I) (M := M) g α k l
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      chartInvGramMatrix (I := I) g α b k l := by
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  unfold invGramCoeffPull
  rw [(toEuclidean (E := E)).symm_apply_apply, (extChartAt I α).left_inv hb_src]

private noncomputable def naiveSecondCovDerivGlobalCorr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Classical.choose
    (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
      (I := I) (M := M) g r s α Idx Jdx k l) I' J' m

private noncomputable def naiveSecondCovDerivGlobalCorr0
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Classical.choose
    (Classical.choose_spec
      (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
        (I := I) (M := M) g r s α Idx Jdx k l)) I' J'

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma naiveSecondCovDerivGlobalCorr_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (naiveSecondCovDerivGlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
          (I := I) (M := M) g r s α Idx Jdx k l))).1 I' J' m

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma naiveSecondCovDerivGlobalCorr0_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (I' : Fin r → Fin (Module.finrank ℝ E))
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (naiveSecondCovDerivGlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J')
      (chartTargetEuclid (I := I) (M := M) α) :=
  (Classical.choose_spec
      (Classical.choose_spec
        (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
          (I := I) (M := M) g r s α Idx Jdx k l))).2.1 I' J'

theorem rawTensorConnLap_chartα_raw_eq_invGram_naiveSecondCovDeriv_proj_on_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (A_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (A_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ),
      (∀ I' J' m, ContDiffOn ℝ ∞ (A_1 I' J' m) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (A_0 I' J') (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : Integral.L2.SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
            (∑ k, ∑ l,
              chartInvGramMatrix (I := I) g α b k l *
                (euclidPartial (E := E) l
                    (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
                    ((toEuclidean (E := E)) ((extChartAt I α) b)) +
                  (∑ I' : Fin r → Fin (Module.finrank ℝ E),
                    ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                    ∑ m,
                    naiveSecondCovDerivGlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m
                        ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                      euclidPartial (E := E) m
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                        ((toEuclidean (E := E)) ((extChartAt I α) b))) +
                  (∑ I' : Fin r → Fin (Module.finrank ℝ E),
                    ∑ J' : Fin s → Fin (Module.finrank ℝ E),
                    naiveSecondCovDerivGlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J'
                        ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                      chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                        ((toEuclidean (E := E)) ((extChartAt I α) b))))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              A_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              A_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  obtain ⟨B_1, B_0, hB1cd, hB0cd, hBform⟩ :=
    rawTensorConnLap_chartα_proj_eq_invGramPrincipalSum_on_goodSet
      (I := I) (M := M) g r s α Idx Jdx
  refine ⟨B_1, B_0, hB1cd, hB0cd, ?_⟩
  intro T₀ b hb
  rw [hBform T₀ hb]
  congr 1
  congr 1
  rw [chartInvGramPrincipalSum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  congr 1
  exact
    (Classical.choose_spec
      (Classical.choose_spec
        (secondCovDeriv_chartα_proj_eq_iteratedFDeriv_T₀_eqOn
          (I := I) (M := M) g r s α Idx Jdx k l))).2.2 T₀ hb

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma invGram_reorder_firstDeriv
    {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (c : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (d : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ι → κ → μ → ℝ)
    (p : ι → κ → μ → ℝ) :
    (∑ k, ∑ l, c k l * (∑ i : ι, ∑ j : κ, ∑ m : μ, d k l i j m * p i j m)) =
      ∑ i : ι, ∑ j : κ, ∑ m : μ, (∑ k, ∑ l, c k l * d k l i j m) * p i j m := by
  classical
  have hdist :
      (∑ k, ∑ l, c k l * (∑ i : ι, ∑ j : κ, ∑ m : μ, d k l i j m * p i j m)) =
      ∑ k, ∑ l, ∑ i : ι, ∑ j : κ, ∑ m : μ, c k l * (d k l i j m * p i j m) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  rw [hdist, ← Finset.sum_product'
      (f := fun k l => ∑ i : ι, ∑ j : κ, ∑ m : μ, c k l * (d k l i j m * p i j m)),
      Finset.univ_product_univ]
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
    (f := fun kl (i : ι) => ∑ j : κ, ∑ m : μ,
      c kl.1 kl.2 * (d kl.1 kl.2 i j m * p i j m))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
    (f := fun kl (j : κ) => ∑ m : μ, c kl.1 kl.2 * (d kl.1 kl.2 i j m * p i j m))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
    (f := fun kl (m : μ) => c kl.1 kl.2 * (d kl.1 kl.2 i j m * p i j m))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show (∑ kl : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        c kl.1 kl.2 * (d kl.1 kl.2 i j m * p i j m))
        = ∑ kl : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (c kl.1 kl.2 * d kl.1 kl.2 i j m) * p i j m from
      Finset.sum_congr rfl (fun kl _ => by ring)]
  rw [← Finset.sum_mul]
  congr 1
  rw [← Finset.sum_product' (f := fun k l => c k l * d k l i j m),
    Finset.univ_product_univ]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma invGram_reorder_zeroth
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (d : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ι → κ → ℝ)
    (q : ι → κ → ℝ) :
    (∑ k, ∑ l, c k l * (∑ i : ι, ∑ j : κ, d k l i j * q i j)) =
      ∑ i : ι, ∑ j : κ, (∑ k, ∑ l, c k l * d k l i j) * q i j := by
  classical
  have hdist :
      (∑ k, ∑ l, c k l * (∑ i : ι, ∑ j : κ, d k l i j * q i j)) =
      ∑ k, ∑ l, ∑ i : ι, ∑ j : κ, c k l * (d k l i j * q i j) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hdist, ← Finset.sum_product'
      (f := fun k l => ∑ i : ι, ∑ j : κ, c k l * (d k l i j * q i j)),
      Finset.univ_product_univ]
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
    (f := fun kl (i : ι) => ∑ j : κ, c kl.1 kl.2 * (d kl.1 kl.2 i j * q i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
    (f := fun kl (j : κ) => c kl.1 kl.2 * (d kl.1 kl.2 i j * q i j))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (∑ kl : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        c kl.1 kl.2 * (d kl.1 kl.2 i j * q i j))
        = ∑ kl : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (c kl.1 kl.2 * d kl.1 kl.2 i j) * q i j from
      Finset.sum_congr rfl (fun kl _ => by ring)]
  rw [← Finset.sum_mul]
  congr 1
  rw [← Finset.sum_product' (f := fun k l => c k l * d k l i j),
    Finset.univ_product_univ]

theorem rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_on_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (C_2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (C_1 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) →
              Fin (Module.finrank ℝ E) → EuclN → ℝ),
    ∃ (C_0 : (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) → EuclN → ℝ),
      (∀ k l, ContDiffOn ℝ ∞ (C_2 k l) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J' m, ContDiffOn ℝ ∞ (C_1 I' J' m) (chartTargetEuclid (I := I) (M := M) α)) ∧
      (∀ I' J', ContDiffOn ℝ ∞ (C_0 I' J') (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ (T₀ : Integral.L2.SmoothCcTensor g r s),
        ∀ {b : M}, b ∈ chartLeviCivitaGoodSet (I := I) α →
          tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
            (∑ k, ∑ l,
              C_2 k l ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) l
                  (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              ∑ m,
              C_1 I' J' m ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                euclidPartial (E := E) m
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) +
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              C_0 I' J' ((toEuclidean (E := E)) ((extChartAt I α) b)) *
                chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')
                  ((toEuclidean (E := E)) ((extChartAt I α) b))) := by
  classical
  obtain ⟨A_1, A_0, hA1cd, hA0cd, hAform⟩ :=
    rawTensorConnLap_chartα_raw_eq_invGram_naiveSecondCovDeriv_proj_on_goodSet
      (I := I) (M := M) g r s α Idx Jdx
  refine ⟨invGramCoeffPull (I := I) (M := M) g α,
          fun I' J' m y =>
            (∑ k, ∑ l, invGramCoeffPull (I := I) (M := M) g α k l y *
                naiveSecondCovDerivGlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m y) +
              A_1 I' J' m y,
          fun I' J' y =>
            (∑ k, ∑ l, invGramCoeffPull (I := I) (M := M) g α k l y *
                naiveSecondCovDerivGlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J' y) +
              A_0 I' J' y,
          fun k l => invGramCoeffPull_contDiffOn (I := I) (M := M) g α k l, ?_, ?_, ?_⟩
  · intro I' J' m
    refine ContDiffOn.add ?_ (hA1cd I' J' m)
    refine ContDiffOn.sum (fun k _ => ?_)
    refine ContDiffOn.sum (fun l _ => ?_)
    exact (invGramCoeffPull_contDiffOn (I := I) (M := M) g α k l).mul
      (naiveSecondCovDerivGlobalCorr_contDiffOn (I := I) (M := M) g r s α Idx Jdx k l I' J' m)
  · intro I' J'
    refine ContDiffOn.add ?_ (hA0cd I' J')
    refine ContDiffOn.sum (fun k _ => ?_)
    refine ContDiffOn.sum (fun l _ => ?_)
    exact (invGramCoeffPull_contDiffOn (I := I) (M := M) g α k l).mul
      (naiveSecondCovDerivGlobalCorr0_contDiffOn (I := I) (M := M) g r s α Idx Jdx k l I' J')
  · intro T₀ b hb
    set y : EuclN := (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    set P : (Fin r → Fin (Module.finrank ℝ E)) →
            (Fin s → Fin (Module.finrank ℝ E)) →
            Fin (Module.finrank ℝ E) → ℝ :=
      fun I' J' m =>
        euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y
      with hP_def
    set R : (Fin r → Fin (Module.finrank ℝ E)) →
            (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
      fun I' J' =>
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y
      with hR_def
    set PP : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun k l =>
        euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y
      with hPP_def
    set IG : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
      fun k l => invGramCoeffPull (I := I) (M := M) g α k l y
      with hIG_def
    set GC : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
             (Fin r → Fin (Module.finrank ℝ E)) →
             (Fin s → Fin (Module.finrank ℝ E)) →
             Fin (Module.finrank ℝ E) → ℝ :=
      fun k l I' J' m =>
        naiveSecondCovDerivGlobalCorr (I := I) (M := M) g r s α Idx Jdx k l I' J' m y
      with hGC_def
    set GC0 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
              (Fin r → Fin (Module.finrank ℝ E)) →
              (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
      fun k l I' J' =>
        naiveSecondCovDerivGlobalCorr0 (I := I) (M := M) g r s α Idx Jdx k l I' J' y
      with hGC0_def
    set A1 : (Fin r → Fin (Module.finrank ℝ E)) →
             (Fin s → Fin (Module.finrank ℝ E)) →
             Fin (Module.finrank ℝ E) → ℝ :=
      fun I' J' m => A_1 I' J' m y with hA1_def
    set A0 : (Fin r → Fin (Module.finrank ℝ E)) →
             (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
      fun I' J' => A_0 I' J' y with hA0_def
    rw [hAform T₀ hb]
    have hIGb : ∀ k l, chartInvGramMatrix (I := I) g α b k l = IG k l := by
      intro k l
      rw [hIG_def]
      exact (invGramCoeffPull_at_b (I := I) (M := M) g α k l hb).symm
    have hPrincipal :
        (∑ k, ∑ l,
          chartInvGramMatrix (I := I) g α b k l *
            (PP k l + (∑ I', ∑ J', ∑ m, GC k l I' J' m * P I' J' m)
                    + (∑ I', ∑ J', GC0 k l I' J' * R I' J'))) =
          ∑ k, ∑ l,
            IG k l * (PP k l + (∑ I', ∑ J', ∑ m, GC k l I' J' m * P I' J' m)
                            + (∑ I', ∑ J', GC0 k l I' J' * R I' J')) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hIGb k l]
    rw [hPrincipal]
    have hC1_distrib :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ m, ((∑ k, ∑ l, IG k l * GC k l I' J' m) + A1 I' J' m) * P I' J' m) =
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ m, (∑ k, ∑ l, IG k l * GC k l I' J' m) * P I' J' m) +
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ∑ m, A1 I' J' m * P I' J' m) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    rw [hC1_distrib]
    have hC0_distrib :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          ((∑ k, ∑ l, IG k l * GC0 k l I' J') + A0 I' J') * R I' J') =
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          (∑ k, ∑ l, IG k l * GC0 k l I' J') * R I' J') +
        (∑ I' : Fin r → Fin (Module.finrank ℝ E),
          ∑ J' : Fin s → Fin (Module.finrank ℝ E), A0 I' J' * R I' J') := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun J' _ => ?_)
      ring
    rw [hC0_distrib]
    have hPrincipal_distrib :
        (∑ k, ∑ l,
            IG k l * (PP k l + (∑ I', ∑ J', ∑ m, GC k l I' J' m * P I' J' m)
                            + (∑ I', ∑ J', GC0 k l I' J' * R I' J'))) =
        (∑ k, ∑ l, IG k l * PP k l) +
        (∑ k, ∑ l, IG k l *
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m,
                GC k l I' J' m * P I' J' m)) +
        (∑ k, ∑ l, IG k l *
            (∑ I' : Fin r → Fin (Module.finrank ℝ E),
              ∑ J' : Fin s → Fin (Module.finrank ℝ E), GC0 k l I' J' * R I' J')) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hPrincipal_distrib]
    rw [invGram_reorder_firstDeriv (E := E) IG GC P,
        invGram_reorder_zeroth (E := E) IG GC0 R]
    abel

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_iteratedFDeriv_norm_bound_on_compact
    {f : EuclN → ℝ} {sset : Set EuclN} (hf : ContDiffOn ℝ ∞ f sset) (hs : IsOpen sset)
    {K : Set EuclN} (hK : IsCompact K) (hKs : K ⊆ sset) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l ≤ N, ∀ y ∈ K, ‖iteratedFDeriv ℝ l f y‖ ≤ C := by
  classical
  have h_uniq : UniqueDiffOn ℝ sset := hs.uniqueDiffOn
  have h_per_order : ∀ l : ℕ, ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ y ∈ K,
      ‖iteratedFDeriv ℝ l f y‖ ≤ Cl := by
    intro l
    by_cases hKne : K.Nonempty
    · have h_iter_contOn : ContinuousOn (fun y => iteratedFDerivWithin ℝ l f sset y) sset :=
        hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) h_uniq
      have h_iter_K : ContinuousOn (iteratedFDerivWithin ℝ l f sset) K :=
        h_iter_contOn.mono hKs
      have h_norm_K : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ l f sset y‖) K :=
        continuous_norm.comp_continuousOn h_iter_K
      obtain ⟨y₀, _, hy₀_max⟩ := hK.exists_isMaxOn hKne h_norm_K
      refine ⟨‖iteratedFDerivWithin ℝ l f sset y₀‖, norm_nonneg _, fun y hy => ?_⟩
      have h₁ : ‖iteratedFDerivWithin ℝ l f sset y‖ ≤
          ‖iteratedFDerivWithin ℝ l f sset y₀‖ := hy₀_max hy
      rwa [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) l hs (hKs hy)] at h₁
    · exact ⟨0, le_refl _, fun y hy => absurd ⟨y, hy⟩ hKne⟩
  choose Cl hCl_nn hCl using h_per_order
  refine ⟨(Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ Cl, ?_, ?_⟩
  · exact le_trans (hCl_nn 0)
      (Finset.le_sup' Cl (Finset.mem_range.mpr (Nat.succ_pos N)))
  · intro l hl y hy
    exact (hCl l y hy).trans
      (Finset.le_sup' Cl (Finset.mem_range.mpr (by omega)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTargetEuclid_preimage_mem_goodSet
    (α : M) {y : EuclN} (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ chartLeviCivitaGoodSet (I := I) α ∧
      (toEuclidean (E := E)) ((extChartAt I α)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
    exact hy_target
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_src : b ∈ (extChartAt I α).source := (extChartAt I α).map_target hy_pre
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I)]; exact hb_src
  refine ⟨hb_good, ?_⟩
  have h_round : (extChartAt I α) b = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_pre
  rw [h_round]; simp

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma block_iteratedFDeriv_norm_le
    {ι : Type*} [Fintype ι] (α : M) (Cf Faf : ι → EuclN → ℝ) {y : EuclN}
    (hCf_cd : ∀ i : ι, ContDiffOn ℝ ∞ (Cf i) (chartTargetEuclid (I := I) (M := M) α))
    (hFaf_cd : ∀ i : ι, ContDiffAt ℝ ∞ (Faf i) y)
    (Mb : ℝ) (j : ℕ)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hsummand : ∀ i : ι,
        ‖iteratedFDeriv ℝ j (fun z => Cf i z * Faf i z) y‖ ≤ Mb) :
    ‖iteratedFDeriv ℝ j (fun z => ∑ i : ι, Cf i z * Faf i z) y‖ ≤
      (Fintype.card ι : ℝ) * Mb := by
  classical
  set s_set : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_set
  have h_open : IsOpen s_set := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_uniq : UniqueDiffOn ℝ s_set := h_open.uniqueDiffOn
  have h_prod_cdwa : ∀ i : ι,
      ContDiffWithinAt ℝ j (fun z => Cf i z * Faf i z) s_set y := by
    intro i
    have hC : ContDiffWithinAt ℝ j (Cf i) s_set y :=
      ((hCf_cd i).of_le (by exact_mod_cast le_top)) y hy
    have hF : ContDiffWithinAt ℝ j (Faf i) s_set y :=
      ((hFaf_cd i).of_le (by exact_mod_cast le_top)).contDiffWithinAt
    exact hC.mul hF
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun z => ∑ i : ι, Cf i z * Faf i z) j h_open hy]
  rw [iteratedFDerivWithin_fun_sum_apply h_uniq hy (fun i _ => h_prod_cdwa i)]
  refine le_trans (norm_sum_le _ _) ?_
  have hsummand' : ∀ i ∈ (Finset.univ : Finset ι),
      ‖iteratedFDerivWithin ℝ j (fun z => Cf i z * Faf i z) s_set y‖ ≤ Mb := by
    intro i _
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => Cf i z * Faf i z) j h_open hy]
    exact hsummand i
  refine le_trans (Finset.sum_le_sum hsummand') ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private lemma exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent_perAlpha
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (j : ℕ), j ≤ 2 * k →
        ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) y‖ ^ 2 ≤
            Bα * rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y := by
  classical
  obtain ⟨C_2, C_1, C_0, hC2cd, hC1cd, hC0cd, hform⟩ :=
    rawTensorConnLap_chartα_raw_eq_T₀_linear_formula_on_goodSet (I := I) (M := M) g r s α Idx Jdx
  let n : ℕ := Module.finrank ℝ E
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α

  obtain ⟨B2, hB2_nn, hB2⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k' l' : Fin n), ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_2 k' l') y‖ ≤ C := by
    have h_each : ∀ p : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_2 p.1 p.2) y‖ ≤ C := fun p =>
      exists_iteratedFDeriv_norm_bound_on_compact (hC2cd p.1 p.2) h_open hK_compact hK_sub (2 * k)
    choose Cf hCf_nn hCf using h_each
    refine ⟨(Finset.univ : Finset (Fin n × Fin n)).sup' Finset.univ_nonempty Cf, ?_, ?_⟩
    · obtain ⟨p₀, _⟩ := Finset.univ_nonempty (α := Fin n × Fin n)
      exact (hCf_nn p₀).trans (Finset.le_sup'_of_le Cf (Finset.mem_univ p₀) le_rfl)
    · intro k' l' i hi y hy
      exact (hCf ⟨k', l'⟩ i hi y hy).trans
        (Finset.le_sup'_of_le Cf (Finset.mem_univ (⟨k', l'⟩ : Fin n × Fin n)) le_rfl)
  obtain ⟨B1, hB1_nn, hB1⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I' : Fin r → Fin n) (J' : Fin s → Fin n) (m : Fin n), ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_1 I' J' m) y‖ ≤ C := by
    have h_each : ∀ p : (Fin r → Fin n) × (Fin s → Fin n) × Fin n,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ 2 * k, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ i (C_1 p.1 p.2.1 p.2.2) y‖ ≤ C := fun p =>
      exists_iteratedFDeriv_norm_bound_on_compact (hC1cd p.1 p.2.1 p.2.2)
        h_open hK_compact hK_sub (2 * k)
    choose Cf hCf_nn hCf using h_each
    refine ⟨(Finset.univ : Finset ((Fin r → Fin n) × (Fin s → Fin n) × Fin n)).sup'
        Finset.univ_nonempty Cf, ?_, ?_⟩
    · obtain ⟨p₀, _⟩ := Finset.univ_nonempty (α := (Fin r → Fin n) × (Fin s → Fin n) × Fin n)
      exact (hCf_nn p₀).trans (Finset.le_sup'_of_le Cf (Finset.mem_univ p₀) le_rfl)
    · intro I' J' m i hi y hy
      exact (hCf ⟨I', J', m⟩ i hi y hy).trans
        (Finset.le_sup'_of_le Cf (Finset.mem_univ
          (⟨I', J', m⟩ : (Fin r → Fin n) × (Fin s → Fin n) × Fin n)) le_rfl)
  obtain ⟨B0, hB0_nn, hB0⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I' : Fin r → Fin n) (J' : Fin s → Fin n), ∀ i ≤ 2 * k, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ i (C_0 I' J') y‖ ≤ C := by
    have h_each : ∀ p : (Fin r → Fin n) × (Fin s → Fin n),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ 2 * k, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ i (C_0 p.1 p.2) y‖ ≤ C := fun p =>
      exists_iteratedFDeriv_norm_bound_on_compact (hC0cd p.1 p.2) h_open hK_compact hK_sub (2 * k)
    choose Cf hCf_nn hCf using h_each
    refine ⟨(Finset.univ : Finset ((Fin r → Fin n) × (Fin s → Fin n))).sup'
        Finset.univ_nonempty Cf, ?_, ?_⟩
    · obtain ⟨p₀, _⟩ := Finset.univ_nonempty (α := (Fin r → Fin n) × (Fin s → Fin n))
      exact (hCf_nn p₀).trans (Finset.le_sup'_of_le Cf (Finset.mem_univ p₀) le_rfl)
    · intro I' J' i hi y hy
      exact (hCf ⟨I', J'⟩ i hi y hy).trans
        (Finset.le_sup'_of_le Cf (Finset.mem_univ
          (⟨I', J'⟩ : (Fin r → Fin n) × (Fin s → Fin n))) le_rfl)

  set Bmax : ℝ := max B2 (max B1 B0) with hBmax_def
  have hBmax_nn : 0 ≤ Bmax := le_trans hB2_nn (le_max_left _ _)
  have hB2_le : B2 ≤ Bmax := le_max_left _ _
  have hB1_le : B1 ≤ Bmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hB0_le : B0 ≤ Bmax := le_trans (le_max_right _ _) (le_max_right _ _)
  set NP : ℕ := Fintype.card ((Fin r → Fin n) × (Fin s → Fin n)) with hNP_def
  set Ntot : ℕ := n * n + NP * n + NP with hNtot_def
  set Ktot : ℝ := (Ntot : ℝ) * (2 : ℝ) ^ (2 * k) * Bmax with hKtot_def
  have hKtot_nn : 0 ≤ Ktot := by rw [hKtot_def]; positivity
  refine ⟨Ktot ^ 2, by positivity, ?_⟩
  intro T j hj y hyK
  set R : ℝ := rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y with hR_def
  have hR_nn : 0 ≤ R := rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y
  have hsqrtR_nn : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK

  set Δpull : EuclN → ℝ := rawConnLapPull (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx with hΔpull_def
  set RHSfun : EuclN → ℝ := fun z =>
    (∑ k', ∑ l',
      C_2 k' l' z *
        euclidPartial (E := E) l'
          (euclidPartial (E := E) k'
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z) +
    (∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n, ∑ m,
      C_1 I' J' m z *
        euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J')) z) +
    (∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n,
      C_0 I' J' z *
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J') z) with hRHSfun_def
  have h_evEq : Δpull =ᶠ[nhds y] RHSfun := by
    filter_upwards [h_open.mem_nhds hy_target] with z hz
    obtain ⟨hb_good, hb_round⟩ := chartTargetEuclid_preimage_mem_goodSet (I := I) (M := M) α hz
    have hform_z := hform T hb_good
    rw [hΔpull_def]
    change tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = RHSfun z
    rw [hform_z, hb_round, hRHSfun_def]
  rw [(h_evEq.iteratedFDeriv ℝ j).self_of_nhds]

  have hraw_sqrt : ∀ (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (m : ℕ), m ≤ 2 * (k + 1) →
      ‖iteratedFDeriv ℝ m (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ≤
        Real.sqrt R := by
    intro q m hm
    have hsq := rawConnLapPull_iteratedFDeriv_norm_sq_le_rhsContent (I := I) (M := M)
      g r s k T α q m hm y
    calc ‖iteratedFDeriv ℝ m (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖
        = Real.sqrt (‖iteratedFDeriv ℝ m
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ^ 2) := by
          rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hsq
  have h_summand : ∀ (C : EuclN → ℝ)
      (hC : ContDiffOn ℝ ∞ C (chartTargetEuclid (I := I) (M := M) α))
      (hCbd : ∀ i ≤ 2 * k, ∀ z ∈ K, ‖iteratedFDeriv ℝ i C z‖ ≤ Bmax)
      (q : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)))
      (Fa : EuclN → ℝ) (a : ℕ) (ha : a ≤ 2)
      (hFa_cd : ∀ z : EuclN, z ∈ chartTargetEuclid (I := I) (M := M) α →
          ContDiffAt ℝ ∞ Fa z)
      (hFa_bd : ∀ (m : ℕ) (z : EuclN), z ∈ chartTargetEuclid (I := I) (M := M) α →
          ‖iteratedFDeriv ℝ m Fa z‖ ≤
            ‖iteratedFDeriv ℝ (m + a)
              (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) z‖),
      ‖iteratedFDeriv ℝ j (fun z => C z * Fa z) y‖ ≤ (2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R := by
    intro C hC hCbd q Fa a ha hFa_cd hFa_bd
    have hbound := rawConnLapProductSummand_iteratedFDeriv_norm_le (I := I) (M := M)
      g r s T α C hC q Fa a hFa_cd hFa_bd j hy_target
    refine le_trans hbound ?_
    have h_per : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
          ‖iteratedFDeriv ℝ ((j - i) + a)
            (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ≤
        (j.choose i : ℝ) * (Bmax * Real.sqrt R) := by
      intro i hi
      have hi_le : i ≤ 2 * k := by have := Finset.mem_range.mp hi; omega
      have hC_le : ‖iteratedFDeriv ℝ i C y‖ ≤ Bmax := hCbd i hi_le y hyK
      have hord : (j - i) + a ≤ 2 * (k + 1) := by omega
      have hraw_le := hraw_sqrt q ((j - i) + a) hord
      have h1 : (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
            ‖iteratedFDeriv ℝ ((j - i) + a)
              (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖ ≤
          (j.choose i : ℝ) * Bmax * Real.sqrt R := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hC_le (by positivity)) hraw_le
          (norm_nonneg _) (by positivity)
      calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i C y‖ *
            ‖iteratedFDeriv ℝ ((j - i) + a)
              (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y‖
          ≤ (j.choose i : ℝ) * Bmax * Real.sqrt R := h1
        _ = (j.choose i : ℝ) * (Bmax * Real.sqrt R) := by ring
    refine le_trans (Finset.sum_le_sum h_per) ?_
    rw [← Finset.sum_mul]
    have hsum_choose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    rw [hsum_choose]
    have h2j_le : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (2 * k) := pow_le_pow_right₀ (by norm_num) hj
    calc (2 : ℝ) ^ j * (Bmax * Real.sqrt R)
        ≤ (2 : ℝ) ^ (2 * k) * (Bmax * Real.sqrt R) :=
          mul_le_mul_of_nonneg_right h2j_le (by positivity)
      _ = (2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R := by ring

  have h_block2_le :
      ‖iteratedFDeriv ℝ j (fun z =>
        ∑ p : Fin n × Fin n,
          C_2 p.1 p.2 z *
            euclidPartial (E := E) p.2
              (euclidPartial (E := E) p.1
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z) y‖ ≤
        (n * n : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) := by
    have hcardN : (Fintype.card (Fin n × Fin n) : ℝ) = (n * n : ℝ) := by
      have : Fintype.card (Fin n × Fin n) = n * n := by
        simp [Fintype.card_prod, Fintype.card_fin]
      rw [this]; push_cast; ring
    rw [show (n * n : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) =
        (Fintype.card (Fin n × Fin n) : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) by
      rw [hcardN]]
    refine block_iteratedFDeriv_norm_le (I := I) (M := M) α
      (fun p : Fin n × Fin n => C_2 p.1 p.2)
      (fun p : Fin n × Fin n =>
        euclidPartial (E := E) p.2
          (euclidPartial (E := E) p.1
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))))
      (fun p => hC2cd p.1 p.2)
      (fun p => euclidPartialIter2_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α ⟨Idx, Jdx⟩ p.1 p.2 hy_target)
      _ j hy_target (fun p => ?_)
    exact h_summand (C_2 p.1 p.2) (hC2cd p.1 p.2)
      (fun i hi z hz => le_trans (hB2 p.1 p.2 i hi z hz) hB2_le)
      ⟨Idx, Jdx⟩ _ 2 le_rfl
      (fun z hz => euclidPartialIter2_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α ⟨Idx, Jdx⟩ p.1 p.2 hz)
      (fun m z hz => euclidPartialIter_chartPushedRaw_norm_le_two (I := I) (M := M)
        g r s T α ⟨Idx, Jdx⟩ p.1 p.2 m hz)
  have h_block1_le :
      ‖iteratedFDeriv ℝ j (fun z =>
        ∑ p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n,
          C_1 p.1.1 p.1.2 p.2 z *
            euclidPartial (E := E) p.2
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1.1 p.1.2)) z) y‖ ≤
        ((NP : ℝ) * n) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) := by
    have hcardN : (Fintype.card (((Fin r → Fin n) × (Fin s → Fin n)) × Fin n) : ℝ) =
        ((NP : ℝ) * n) := by
      rw [Fintype.card_prod, hNP_def]
      simp [Fintype.card_fin]
    rw [show ((NP : ℝ) * n) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) =
        (Fintype.card (((Fin r → Fin n) × (Fin s → Fin n)) × Fin n) : ℝ) *
          ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) by rw [hcardN]]
    refine block_iteratedFDeriv_norm_le (I := I) (M := M) α
      (fun p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n => C_1 p.1.1 p.1.2 p.2)
      (fun p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n =>
        euclidPartial (E := E) p.2
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1.1 p.1.2)))
      (fun p => hC1cd p.1.1 p.1.2 p.2)
      (fun p => euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α p.1 p.2 hy_target)
      _ j hy_target (fun p => ?_)
    exact h_summand (C_1 p.1.1 p.1.2 p.2) (hC1cd p.1.1 p.1.2 p.2)
      (fun i hi z hz => le_trans (hB1 p.1.1 p.1.2 p.2 i hi z hz) hB1_le)
      p.1 _ 1 (by norm_num)
      (fun z hz => euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M)
        g r s T α p.1 p.2 hz)
      (fun m z hz => euclidPartialIter_chartPushedRaw_norm_le_one (I := I) (M := M)
        g r s T α p.1 p.2 m hz)
  have h_block0_le :
      ‖iteratedFDeriv ℝ j (fun z =>
        ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
          C_0 p.1 p.2 z *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2) z) y‖ ≤
        (NP : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) := by
    rw [show (NP : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) =
        (Fintype.card ((Fin r → Fin n) × (Fin s → Fin n)) : ℝ) *
          ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) by rw [← hNP_def]]
    refine block_iteratedFDeriv_norm_le (I := I) (M := M) α
      (fun p : (Fin r → Fin n) × (Fin s → Fin n) => C_0 p.1 p.2)
      (fun p : (Fin r → Fin n) × (Fin s → Fin n) =>
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2))
      (fun p => hC0cd p.1 p.2)
      (fun p => chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α p hy_target)
      _ j hy_target (fun p => ?_)
    exact h_summand (C_0 p.1 p.2) (hC0cd p.1 p.2)
      (fun i hi z hz => le_trans (hB0 p.1 p.2 i hi z hz) hB0_le)
      p _ 0 (by norm_num)
      (fun z hz => chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α p hz)
      (fun m z hz => euclidPartialIter_chartPushedRaw_norm_le_zero (I := I) (M := M)
        g r s T α p m hz)

  have h_norm_le : ‖iteratedFDeriv ℝ j RHSfun y‖ ≤ Ktot * Real.sqrt R := by
    set b2fn : EuclN → ℝ := fun z =>
      ∑ p : Fin n × Fin n,
        C_2 p.1 p.2 z *
          euclidPartial (E := E) p.2
            (euclidPartial (E := E) p.1
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z with hb2fn_def
    set b1fn : EuclN → ℝ := fun z =>
      ∑ p : ((Fin r → Fin n) × (Fin s → Fin n)) × Fin n,
        C_1 p.1.1 p.1.2 p.2 z *
          euclidPartial (E := E) p.2
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1.1 p.1.2)) z with hb1fn_def
    set b0fn : EuclN → ℝ := fun z =>
      ∑ p : (Fin r → Fin n) × (Fin s → Fin n),
        C_0 p.1 p.2 z *
          chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α p.1 p.2) z with hb0fn_def
    have hb2_cd : ContDiffAt ℝ (j : WithTop ℕ∞) b2fn y := by
      rw [hb2fn_def]
      refine ContDiffAt.sum (fun p _ => ?_)
      exact ((contDiffAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (hC2cd p.1 p.2) hy_target).mul
        (euclidPartialIter2_chartPushedRaw_contDiffAt (I := I) (M := M)
          g r s T α ⟨Idx, Jdx⟩ p.1 p.2 hy_target)).of_le (by exact_mod_cast le_top)
    have hb1_cd : ContDiffAt ℝ (j : WithTop ℕ∞) b1fn y := by
      rw [hb1fn_def]
      refine ContDiffAt.sum (fun p _ => ?_)
      exact ((contDiffAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (hC1cd p.1.1 p.1.2 p.2) hy_target).mul
        (euclidPartialIter1_chartPushedRaw_contDiffAt (I := I) (M := M)
          g r s T α p.1 p.2 hy_target)).of_le (by exact_mod_cast le_top)
    have hb0_cd : ContDiffAt ℝ (j : WithTop ℕ∞) b0fn y := by
      rw [hb0fn_def]
      refine ContDiffAt.sum (fun p _ => ?_)
      exact ((contDiffAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (hC0cd p.1 p.2) hy_target).mul
        (chartPushedRaw_raw_contDiffAt (I := I) (M := M) g r s T α p hy_target)).of_le
        (by exact_mod_cast le_top)
    have he2 : ∀ z, b2fn z =
        ∑ k', ∑ l',
          C_2 k' l' z *
            euclidPartial (E := E) l'
              (euclidPartial (E := E) k'
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))) z := by
      intro z; rw [hb2fn_def]; dsimp only; rw [Fintype.sum_prod_type]
    have he1 : ∀ z, b1fn z =
        ∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n, ∑ m,
          C_1 I' J' m z *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J')) z := by
      intro z
      rw [hb1fn_def]
      dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    have he0 : ∀ z, b0fn z =
        ∑ I' : Fin r → Fin n, ∑ J' : Fin s → Fin n,
          C_0 I' J' z *
            chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α I' J') z := by
      intro z; rw [hb0fn_def]; dsimp only; rw [Fintype.sum_prod_type]
    have hRHS_eq : RHSfun = fun z => (b2fn z + b1fn z) + b0fn z := by
      funext z
      rw [he2 z, he1 z, he0 z, hRHSfun_def]
    have hadd : iteratedFDeriv ℝ j RHSfun y =
        iteratedFDeriv ℝ j b2fn y + (iteratedFDeriv ℝ j b1fn y + iteratedFDeriv ℝ j b0fn y) := by
      rw [hRHS_eq,
        fun_iteratedFDeriv_add_apply (hb2_cd.add hb1_cd) hb0_cd,
        fun_iteratedFDeriv_add_apply hb2_cd hb1_cd]
      exact add_assoc _ _ _
    rw [hadd]
    have hsplit : ‖iteratedFDeriv ℝ j b2fn y +
          (iteratedFDeriv ℝ j b1fn y + iteratedFDeriv ℝ j b0fn y)‖ ≤
        ‖iteratedFDeriv ℝ j b2fn y‖ +
          (‖iteratedFDeriv ℝ j b1fn y‖ + ‖iteratedFDeriv ℝ j b0fn y‖) := by
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      exact norm_add_le _ _
    refine le_trans hsplit ?_
    have h3 := add_le_add h_block2_le (add_le_add h_block1_le h_block0_le)
    refine le_trans h3 ?_
    rw [hKtot_def]
    have : ((Ntot : ℝ) * (2 : ℝ) ^ (2 * k) * Bmax) * Real.sqrt R =
        (n * n : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) +
        (((NP : ℝ) * n) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R) +
          (NP : ℝ) * ((2 : ℝ) ^ (2 * k) * Bmax * Real.sqrt R)) := by
      rw [hNtot_def]; push_cast; ring
    rw [this]
  calc ‖iteratedFDeriv ℝ j RHSfun y‖ ^ 2
      ≤ (Ktot * Real.sqrt R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h_norm_le 2
    _ = Ktot ^ 2 * R := by rw [mul_pow, Real.sq_sqrt hR_nn]

theorem exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ), j ≤ 2 * k →
        ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) y‖ ^ 2 ≤
            B * rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y := by
  classical

  have hperα : ∀ w : M × (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)), ∃ Bα : ℝ, 0 ≤ Bα ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (j : ℕ), j ≤ 2 * k →
        ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) w.1,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) w.1 w.2.1 w.2.2) y‖ ^ 2 ≤
            Bα * rawConnLapRhsHsContent (I := I) (M := M) g r s k T w.1 y := fun w =>
    exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent_perAlpha
      (I := I) (M := M) g r s k w.1 w.2.1 w.2.2
  choose Bfun hBfun_nn hBfun using hperα
  set actF : Finset M := chartAtlasPOU_activeFinset I M with hactF_def
  refine ⟨∑ α ∈ actF, ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx, Jdx⟩,
    Finset.sum_nonneg (fun α _ => Finset.sum_nonneg (fun Idx _ =>
      Finset.sum_nonneg (fun Jdx _ => hBfun_nn ⟨α, Idx, Jdx⟩))), ?_⟩
  intro T α Idx Jdx j hj y hyK
  by_cases hα : α ∈ actF
  · have hBle : Bfun ⟨α, Idx, Jdx⟩ ≤
        ∑ α' ∈ actF, ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α', Idx', Jdx'⟩ := by
      have h_inner : Bfun ⟨α, Idx, Jdx⟩ ≤
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx, Jdx'⟩ :=
        Finset.single_le_sum (f := fun Jdx' => Bfun ⟨α, Idx, Jdx'⟩)
          (fun Jdx' _ => hBfun_nn ⟨α, Idx, Jdx'⟩) (Finset.mem_univ Jdx)
      have h_mid : (∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx, Jdx'⟩) ≤
          ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx', Jdx'⟩ :=
        Finset.single_le_sum
          (f := fun Idx' => ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx', Jdx'⟩)
          (fun Idx' _ => Finset.sum_nonneg (fun Jdx' _ => hBfun_nn ⟨α, Idx', Jdx'⟩))
          (Finset.mem_univ Idx)
      have h_outer : (∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α, Idx', Jdx'⟩) ≤
          ∑ α' ∈ actF, ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α', Idx', Jdx'⟩ :=
        Finset.single_le_sum
          (f := fun α' => ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E), Bfun ⟨α', Idx', Jdx'⟩)
          (fun α' _ => Finset.sum_nonneg (fun Idx' _ =>
            Finset.sum_nonneg (fun Jdx' _ => hBfun_nn ⟨α', Idx', Jdx'⟩))) hα
      exact le_trans h_inner (le_trans h_mid h_outer)
    have hpt := hBfun ⟨α, Idx, Jdx⟩ T j hj y hyK
    refine le_trans hpt ?_
    exact mul_le_mul_of_nonneg_right hBle
      (rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y)
  · exfalso
    have hρ0 : ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
    have h_tsupp_empty : tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
      rw [tsupport, Function.support]
      simp only [hρ0, ne_eq, not_true_eq_false, Set.setOf_false, closure_empty]
    have hyK' : y ∈ chartImagePOUTsupport (I := I) (M := M) α := hyK
    rw [chartImagePOUTsupport] at hyK'
    obtain ⟨z, ⟨x, hx_supp, _⟩, _⟩ := hyK'
    rw [h_tsupp_empty] at hx_supp
    exact hx_supp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma rawConnLapPouPull_eq_zero_off_kernel (α : M) (y : EuclN)
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
private lemma rawConnLapPouPullCont (α : M) :
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
private lemma rawConnLapPullIntegrand_aemeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) (l : ℕ)
    (bIdx : Fin l → Fin (Module.finrank ℝ E)) :
    AEMeasurable
      (fun y : EuclN => ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_iter_contOn :
      ContinuousOn (iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro y hy
    have h_cd : ContDiffAt ℝ ∞ (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y :=
      rawConnLapPull_contDiffAt (I := I) (M := M) g r s T α q.1 q.2 hy
    exact (h_cd.continuousAt_iteratedFDeriv (k := l)
      (by exact_mod_cast le_top)).continuousWithinAt
  have h_eval : ContinuousOn
      (fun y : EuclN => (iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
          (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (continuous_eval_const _).comp_continuousOn h_iter_contOn
  have h_real : ContinuousOn
      (fun y : EuclN => ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ l (rawConnLapPull (I := I) (M := M) g r s T α q.1 q.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (rawConnLapPouPullCont (I := I) (M := M) α).mul (h_eval.abs.pow 2)
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (h_real.aestronglyMeasurable h_open.measurableSet).aemeasurable

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma rawConnLapSumIntegrals_eq_integral_sum
    (g : SmoothRiemannianMetric I M) (r' s' : ℕ) (S : Integral.L2.SmoothCcTensor g r' s')
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
                        (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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
                        (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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
                    (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
          ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN) := by
    intro IJ j
    rw [MeasureTheory.lintegral_finset_sum' _
      (fun bIdx _ => rawConnLapPullIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)]
  have h_j : ∀ (IJ : (Fin r' → Fin (Module.finrank ℝ E)) ×
        (Fin s' → Fin (Module.finrank ℝ E))),
      (∑ j ∈ Finset.range K,
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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
                      (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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
                      (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
          ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
      intro j _
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
        (fun bIdx (_ : bIdx ∈ Finset.univ) =>
          rawConnLapPullIntegrand_aemeasurable (I := I) (M := M) g r' s' S α IJ j bIdx)
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
                        (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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
                          (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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
                          (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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
                            (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
              ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
          intro IJ _
          have h := Finset.aemeasurable_sum (Finset.range K)
            (fun j (_ : j ∈ Finset.range K) =>
              (Finset.aemeasurable_sum
                (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E)))
                (fun bIdx (_ : bIdx ∈ Finset.univ) =>
                  rawConnLapPullIntegrand_aemeasurable
                    (I := I) (M := M) g r' s' S α IJ j bIdx)).congr
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
                          (rawConnLapPull (I := I) (M := M) g r' s' S α IJ.1 IJ.2) y)
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

omit [CompactSpace M] [I.Boundaryless] in
private lemma rawConnLap_pointwise_integrand_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ), j ≤ 2 * k →
        ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) z‖ ^ 2 ≤
            B * rawConnLapRhsHsContent (I := I) (M := M) g r s k T α z)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
              |(iteratedFDeriv ℝ j
                    (rawConnLapPull (I := I) (M := M) g r s
                      (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
      ((Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
          ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B) *
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y) := by
  classical
  set ρ : ℝ := (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hρ_def
  have hρ_nn : 0 ≤ ρ := (chartAtlasPOU I M).nonneg α _
  set R : ℝ := rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y with hR_def
  have hR_nn : 0 ≤ R := rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y
  set Ccomb : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
      ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B with hCcomb_def
  set LHSsum : ℝ := ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j
                (rawConnLapPull (I := I) (M := M) g r s
                  (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 with hLHSsum_def
  change ρ * LHSsum ≤ Ccomb * (ρ * R)
  by_cases hyK : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · have h_perIJorder : ∀ (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) (j : ℕ), j ≤ 2 * k →
        (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j
                (rawConnLapPull (I := I) (M := M) g r s
                  (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
          ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R) := by
      intro IJ j hj
      set F : EuclN → ℝ := rawConnLapPull (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2 with hF_def
      set Fop : ℝ := ‖iteratedFDeriv ℝ j F y‖ with hFop_def
      have hFop_sq_le : Fop ^ 2 ≤ B * R := hB IJ.1 IJ.2 j hj y hyK
      have h_eval_le : ∀ bIdx : Fin j → Fin (Module.finrank ℝ E),
          |(iteratedFDeriv ℝ j F y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2 ≤ Fop ^ 2 := by
        intro bIdx
        have h_le : |(iteratedFDeriv ℝ j F y)
            (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ≤ Fop := by
          have h := (iteratedFDeriv ℝ j F y).le_opNorm
            (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i))
          have hprod : (∏ i : Fin j,
              ‖EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (bIdx i)‖) = 1 := by
            refine Finset.prod_eq_one (fun i _ => ?_)
            rw [EuclideanSpace.basisFun_apply, PiLp.norm_single]; simp
          rw [hprod, mul_one] at h
          rw [← Real.norm_eq_abs]; exact h
        exact pow_le_pow_left₀ (abs_nonneg _) h_le 2
      have h_card : (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ) =
          (Module.finrank ℝ E : ℝ) ^ j := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
      calc (∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            |(iteratedFDeriv ℝ j F y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
          ≤ ∑ _bIdx : Fin j → Fin (Module.finrank ℝ E), Fop ^ 2 :=
            Finset.sum_le_sum (fun bIdx _ => h_eval_le bIdx)
        _ = (Module.finrank ℝ E : ℝ) ^ j * Fop ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h_card]
        _ ≤ (Module.finrank ℝ E : ℝ) ^ j * (B * R) :=
            mul_le_mul_of_nonneg_left hFop_sq_le (by positivity)
        _ ≤ ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hB_nn hR_nn)
            have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
              have : 1 ≤ Module.finrank ℝ E :=
                Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
              exact_mod_cast this
            exact pow_le_pow_right₀ hn1 hj
    have h_LHSsum_le : LHSsum ≤ Ccomb * R := by
      have h_perIJ : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          (∑ j ∈ Finset.range (2 * k + 1),
            ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
              |(iteratedFDeriv ℝ j
                    (rawConnLapPull (I := I) (M := M) g r s
                      (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2) ≤
          ((2 * k + 1 : ℕ) : ℝ) * (((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R)) := by
        intro IJ
        calc (∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r s
                        (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ≤ ∑ _j ∈ Finset.range (2 * k + 1),
                ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R) := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              exact h_perIJorder IJ j (by have := Finset.mem_range.mp hj; omega)
          _ = ((2 * k + 1 : ℕ) : ℝ) * (((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc LHSsum
          ≤ ∑ _IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
              ((2 * k + 1 : ℕ) : ℝ) * (((Module.finrank ℝ E : ℝ) ^ (2 * k)) * (B * R)) :=
            Finset.sum_le_sum (fun IJ _ => h_perIJ IJ)
        _ = Ccomb * R := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hCcomb_def]
            ring
    calc ρ * LHSsum ≤ ρ * (Ccomb * R) := mul_le_mul_of_nonneg_left h_LHSsum_le hρ_nn
      _ = Ccomb * (ρ * R) := by ring
  · have hρ0 : ρ = 0 :=
      rawConnLapPouPull_eq_zero_off_kernel (I := I) (M := M) α y hy hyK
    rw [hρ0]; simp

omit [CompactSpace M] in
private lemma rawConnLap_per_alpha_inner_bound
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : Integral.L2.SmoothCcTensor g r s)
    (α : M) (B : ℝ) (hB_nn : 0 ≤ B)
    (hB : ∀ (T' : Integral.L2.SmoothCcTensor g r s) (α' : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (j : ℕ), j ≤ 2 * k →
        ∀ z ∈ chartImagePOUTsupport (I := I) (M := M) α',
          ‖iteratedFDeriv ℝ j
              (rawConnLapPull (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T') α' Idx Jdx) z‖ ^ 2 ≤
            B * rawConnLapRhsHsContent (I := I) (M := M) g r s k T' α' z)
    (Ccomb : ℝ)
    (hCcomb_def : Ccomb = (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
        ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B)
    {lhsInner rhsInner : ℝ≥0∞}
    (hlhsInner_def : lhsInner =
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                            (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
              ∂(volume : Measure EuclN))
    (hrhsInner_def : rhsInner =
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (k + 1) + 1),
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
    lhsInner ≤ ENNReal.ofReal Ccomb * rhsInner := by
  classical
  subst hlhsInner_def hrhsInner_def
  have hCcomb_nn : 0 ≤ Ccomb := by rw [hCcomb_def]; positivity
  simp only [rawConnLapPull_eq (I := I) (M := M)]
  rw [rawConnLapSumIntegrals_eq_integral_sum (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s T) α (2 * k + 1)]
  rw [rawConnLapSumIntegrals_eq_integral_sum (I := I) (M := M) g r s T α (2 * (k + 1) + 1)]
  rw [show (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * (k + 1) + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                |(iteratedFDeriv ℝ j
                      (rawConnLapPull (I := I) (M := M) g r s T α IJ.1 IJ.2) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2))
        ∂(volume : Measure EuclN)) =
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y)
        ∂(volume : Measure EuclN) from rfl]
  rw [← MeasureTheory.lintegral_const_mul' _ _
    (ENNReal.ofReal_ne_top (r := Ccomb))]
  refine setLIntegral_mono_ae'
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    (Filter.Eventually.of_forall (fun y hy => ?_))
  have hpt := rawConnLap_pointwise_integrand_le (I := I) (M := M) g r s k T α B hB_nn
    (fun Idx Jdx j hj z hz => hB T α Idx Jdx j hj z hz) hy
  rw [← hCcomb_def] at hpt
  have h_rhs_nn : 0 ≤ ((chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        rawConnLapRhsHsContent (I := I) (M := M) g r s k T α y :=
    mul_nonneg ((chartAtlasPOU I M).nonneg α _)
      (rawConnLapRhsHsContent_nonneg (I := I) (M := M) g r s k T α y)
  rw [← ENNReal.ofReal_mul hCcomb_nn]
  exact ENNReal.ofReal_le_ofReal hpt

theorem exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (α : M),
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                                (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
                  ∂(volume : Measure EuclN)) ≤
          ENNReal.ofReal C *
            (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range (2 * (k + 1) + 1),
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
                    ∂(volume : Measure EuclN)) := by
  classical
  obtain ⟨B, hB_nn, hB⟩ :=
    exists_rawConnLapComp_iteratedFDeriv_norm_sq_le_rawConnLapRhsHsContent
      (I := I) (M := M) g r s k
  refine ⟨(Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) * ((2 * k + 1 : ℕ) : ℝ) *
      ((Module.finrank ℝ E : ℝ) ^ (2 * k)) * B, by positivity, fun T α => ?_⟩
  refine rawConnLap_per_alpha_inner_bound (I := I) (M := M) g r s k T α B hB_nn hB _ rfl ?_ ?_
  · rfl
  · rfl

theorem exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        tensorPouSobolevHsNorm (I := I) (M := M) g k
            (rawTensorConnLapSmooth (I := I) g r s T) ≤
          ENNReal.ofReal C *
            tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart (I := I) (M := M) g r s k
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun T => ?_⟩
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevHsNorm_eq]
  set lhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN) with hlhsInner_def
  set rhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * (k + 1) + 1),
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
  have h_main : (∑' α : M, lhsInner α) ≤ ENNReal.ofReal C * ∑' α : M, rhsInner α := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun α => ?_)
    rw [hlhsInner_def, hrhsInner_def]
    exact hC T α
  have h_rpow : (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal C * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h_main (by norm_num)
  calc (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal C * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := h_rpow
    _ = ENNReal.ofReal (Real.sqrt C) * (∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg hC_nn (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← Real.sqrt_eq_rpow]

end RawConnLapOrderDrop

theorem exists_rawConnLapSmooth_toHs_le_toHs_succ
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1) T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le (I := I) (M := M) g 0 2 k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  have hle := hC T
  have h_rhs_ne_top :
      ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (k + 1) T).ne
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (rawTensorConnLapSmooth (I := I) g 0 2 T)).toReal
      ≤ (ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal :=
        ENNReal.toReal_mono h_rhs_ne_top hle
    _ = (ENNReal.ofReal C).toReal *
          (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_mul]
    _ = C * (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_ofReal hC_nn]

theorem exists_rawConnLapIter_toHs_le_toHs
    (g : SmoothRiemannianMetric I M) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapIter (I := I) g 0 2 i T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + i) T‖ := by
  induction i generalizing k with
  | zero =>
      refine ⟨1, zero_le_one, fun T => ?_⟩
      simp only [rawTensorConnLapIter_zero, Nat.add_zero, one_mul, le_refl]
  | succ i ih =>
      obtain ⟨Ci, hCi_nn, hCi⟩ := ih (k + 1)
      obtain ⟨C1, hC1_nn, hC1⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g k
      refine ⟨C1 * Ci, mul_nonneg hC1_nn hCi_nn, fun T => ?_⟩

      have hpeel : rawTensorConnLapIter (I := I) g 0 2 (i + 1) T
          = rawTensorConnLapSmooth (I := I) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 i T) := by
        rw [rawTensorConnLapIter_succ]
      rw [hpeel]
      have hstep := hC1 (rawTensorConnLapIter (I := I) g 0 2 i T)
      have hih := hCi T
      have hord : k + 1 + i = k + (i + 1) := by ring
      rw [hord] at hih
      refine le_trans hstep ?_
      calc C1 * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1)
              (rawTensorConnLapIter (I := I) g 0 2 i T)‖
          ≤ C1 * (Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖) := mul_le_mul_of_nonneg_left hih hC1_nn
        _ = C1 * Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖ := by ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem toHs_norm_mono (g : SmoothRiemannianMetric I M) {r s : ℕ} {m n : ℕ} (hmn : m ≤ n)
    (T : Integral.L2.SmoothCcTensor g r s) :
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) m T‖ ≤
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) n T‖ := by
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  refine ENNReal.toReal_mono (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g n T).ne ?_

  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => simp
  | succ d ihd =>
      refine le_trans ihd ?_
      have : m + d + 1 = m + (d + 1) := by ring
      rw [← this]
      exact tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g (m + d) T

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem SmoothCcTensor.toHs_add {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ + R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        + IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_add]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem SmoothCcTensor.toHs_sub {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ - R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        - IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_sub]
  rfl

end InnerProductSpaceModel

section LinearityT2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Connection Bundle Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
private lemma rawConnLap_smooth_witness (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : Integral.L2.SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => Bundle.TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)) :=
  rawTensorConnLap_contMDiff (I := I) g r s
    (fun z : M => T.toSection z) T.toSection.contMDiff_toFun

omit [CompactSpace M] [I.Boundaryless] in
theorem rawTensorConnLapSmooth_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T T' : Integral.L2.SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (T - T')
      = rawTensorConnLapSmooth (I := I) g r s T - rawTensorConnLapSmooth (I := I) g r s T' := by
  have hsub_eq : (T - T' : Integral.L2.SmoothCcTensor g r s) = T + (-1 : ℝ) • T' := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  have h_smul : rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')
      = (-1 : ℝ) • rawTensorConnLapSmooth (I := I) g r s T' := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsmul := tensorConnLaplacian_of_contMDiff_smul (I := I) g r s (-1 : ℝ) T'
      (rawConnLap_smooth_witness (I := I) g T')
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    have hRHS : (rawTensorConnLapSmooth (I := I) g r s T').toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T'
          (rawConnLap_smooth_witness (I := I) g T')).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, hRHS, hsmul]
  have h_add : rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')
      = rawTensorConnLapSmooth (I := I) g r s T
        + rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T') := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsum := tensorConnLaplacian_of_contMDiff_add (I := I) g r s T ((-1 : ℝ) • T')
      (rawConnLap_smooth_witness (I := I) g T)
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))
      (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s (T + (-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T'))).toSection x := rfl
    have hRHS₁ : (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T
          (rawConnLap_smooth_witness (I := I) g T)).toSection x := rfl
    have hRHS₂ : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
      Pi.add_apply, hRHS₁, hRHS₂, hsum]
  rw [hsub_eq, h_add, h_smul, neg_one_smul, ← sub_eq_add_neg]

end LinearityT2

section InnerProductSpaceModel

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
theorem exists_l2Norm_le_tensorPouSobolevHsNorm_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        ‖T‖ ≤ C * (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq
      (I := I) (M := M) (E := E) g r s
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero (I := I) (M := M) g r s
  refine ⟨Real.sqrt (C₁ * C₂), Real.sqrt_nonneg _, fun T => ?_⟩

  set L : ℝ := tensorL2Norm (I := I) (M := M) g r s T.toFun with hL_def
  have hL_eq : ‖T‖ = L := (tensorL2Norm_toFun_eq_norm (I := I) (M := M) g T).symm
  set N : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have hNormSq_toReal : (tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T).toReal = N ^ 2 := by
    unfold tensorPouSobolevHsNormSq
    rw [ENNReal.toReal_pow]
  set S : ℝ := ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ((MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                (I := I) (M := M) g r s T α Idx Jdx) 2
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                (I := I) (M := M) g)).toReal) ^ 2 with hS_def
  have hS_le : L ^ 2 ≤ C₁ * S := hC₁ T
  have hcomp_le : S ≤ C₂ * N ^ 2 := by
    have := hC₂ T
    rwa [hNormSq_toReal] at this
  have hL_nn : 0 ≤ L := tensorL2Norm_nonneg (I := I) (M := M) g r s T.toFun
  have h_sq_le : L ^ 2 ≤ C₁ * C₂ * N ^ 2 := by
    calc L ^ 2 ≤ C₁ * S := hS_le
      _ ≤ C₁ * (C₂ * N ^ 2) := mul_le_mul_of_nonneg_left hcomp_le hC₁_nn
      _ = C₁ * C₂ * N ^ 2 := by ring
  rw [hL_eq]
  calc L = Real.sqrt (L ^ 2) := (Real.sqrt_sq hL_nn).symm
    _ ≤ Real.sqrt (C₁ * C₂ * N ^ 2) := Real.sqrt_le_sqrt h_sq_le
    _ = Real.sqrt (C₁ * C₂) * N := by
        rw [Real.sqrt_mul (mul_nonneg hC₁_nn hC₂_nn), Real.sqrt_sq hN_nn]

omit [BoundarylessManifold I M] in
theorem exists_l2Norm_le_toHs_zero
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖Integral.L2.SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) T‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0 T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_l2Norm_le_tensorPouSobolevHsNorm_zero (I := I) (M := M) g 0 2
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [Integral.L2.SmoothCcTensor.norm_toL2, tensorPouSobolevHilbert_norm_eq]
  exact hC T

end InnerProductSpaceModel

end DifferentialGeometry.PDE.RicciFlow
