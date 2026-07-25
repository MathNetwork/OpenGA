import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

structure SmoothCcTensorHs (g : SmoothRiemannianMetric I M) (r s k : ℕ) where

  toCcTensor : SmoothCcTensor g r s

namespace SmoothCcTensorHs

variable {g : SmoothRiemannianMetric I M} {r s k : ℕ}

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[ext] theorem ext {S T : SmoothCcTensorHs g r s k}
    (h : S.toCcTensor = T.toCcTensor) : S = T := by
  cases S; cases T; congr

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toCcTensor_injective :
    Function.Injective
      (fun S : SmoothCcTensorHs g r s k => S.toCcTensor) := by
  intro S T h
  exact ext h

instance : Zero (SmoothCcTensorHs g r s k) := ⟨⟨0⟩⟩
instance : Add (SmoothCcTensorHs g r s k) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩
instance : Neg (SmoothCcTensorHs g r s k) := ⟨fun S => ⟨-S.toCcTensor⟩⟩
instance : Sub (SmoothCcTensorHs g r s k) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩
instance : SMul ℝ (SmoothCcTensorHs g r s k) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorHs g r s k).toCcTensor = 0 := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_add (S T : SmoothCcTensorHs g r s k) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_neg (S : SmoothCcTensorHs g r s k) :
    (-S).toCcTensor = -S.toCcTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorHs g r s k) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorHs g r s k) :
    (c • S).toCcTensor = c • S.toCcTensor := rfl

instance : SMul ℕ (SmoothCcTensorHs g r s k) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothCcTensorHs g r s k) := ⟨zsmulRec⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorHs g r s k) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toCcTensor = (0 : ℕ) • S.toCcTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toCcTensor = (n + 1) • S.toCcTensor
      change (nsmulRec n S + S).toCcTensor = (n + 1) • S.toCcTensor
      have hn : (nsmulRec n S).toCcTensor = n • S.toCcTensor := ih
      rw [toCcTensor_add, hn, succ_nsmul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorHs g r s k) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor := by
  rcases z with n | n
  · change (n • S).toCcTensor = (Int.ofNat n) • S.toCcTensor
    rw [toCcTensor_nsmul]; simp
  · change (-((n + 1) • S)).toCcTensor = (Int.negSucc n) • S.toCcTensor
    rw [toCcTensor_neg, toCcTensor_nsmul]
    show -((n + 1) • S.toCcTensor) = Int.negSucc n • S.toCcTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothCcTensorHs g r s k) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul

def toCcTensorAddHom :
    SmoothCcTensorHs g r s k →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

instance : Module ℝ (SmoothCcTensorHs g r s k) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

end SmoothCcTensorHs


private noncomputable def hkIntegrand
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : ℝ :=
  ((chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
    ((iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s
                T.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) *
      (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s
                S.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))


private noncomputable def hkOneTerm
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) : ℝ :=
  ∫ y in chartTargetEuclid (I := I) (M := M) α,
    hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y
    ∂(volume :
      Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))


private noncomputable def sobolevHkInner
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          hkOneTerm (I := I) (M := M) T S α IJ j basisIdx


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hkIntegrand_continuousOn
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold hkIntegrand
  have hPOU_smooth :
      ContMDiff I (𝓘(ℝ, ℝ)) ∞
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hPOU_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    hPOU_smooth.continuous
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
    unfold chartTargetEuclid at hy
    obtain ⟨z, hz_tgt, hz_eq⟩ := hy
    rw [← hz_eq]
    change (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
    rw [(toEuclidean (E := E)).symm_apply_apply]
    exact hz_tgt
  have hPOU_pull_cont :
      ContinuousOn (fun y : EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E)) =>
          (chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm
              ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
    hPOU_cont.comp_continuousOn' h_inner
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_eval_contOn : ∀ (U : SmoothCcTensor g r s),
      ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm)
              y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro U
    have h_cdOn : ContDiffOn ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm)
        (chartTargetEuclid (I := I) (M := M) α) := by
      classical
      have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2)
          ((chartAt H α).source) :=
        tensorChartComponentRaw_contMDiffOn_chart_source
          (I := I) (M := M) g r s U α IJ.1 IJ.2
      have h_raw_pull_contDiffOn :
          ContDiffOn ℝ ∞
            (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2
              ∘ (extChartAt I α).symm)
            (extChartAt I α).target := by
        have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
            ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
          contMDiffOn_extChartAt_symm α
        have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
            (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2
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
    have h_iter_contOn : ContinuousOn
        (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm))
        (chartTargetEuclid (I := I) (M := M) α) := by
      intro y hy
      have h_cd : ContDiffAt ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm) y :=
        h_cdOn.contDiffAt (h_open.mem_nhds hy)
      have h_cont_iter : ContinuousAt
          (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s U α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)) y :=
        h_cd.continuousAt_iteratedFDeriv (k := j) (by exact_mod_cast le_top)
      exact h_cont_iter.continuousWithinAt
    have h_apply : Continuous
        fun A : ContinuousMultilinearMap ℝ
            (fun _ : Fin j => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ =>
          A (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) :=
      continuous_eval_const _
    exact h_apply.comp_continuousOn h_iter_contOn
  exact hPOU_pull_cont.mul ((h_eval_contOn T.toCcTensor).mul
    (h_eval_contOn S.toCcTensor))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hkIntegrand_zero_off_compact
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ chartImagePOUTsupport (I := I) (M := M) α) :
    hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y = 0 := by
  classical
  have hpush_zero :
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        α (fun _ : M => (1 : ℝ)) y = 0 :=
    chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
      α (fun _ => 1) hy_target hy_off
  have hpush_unfold :
      chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
          α (fun _ : M => (1 : ℝ)) y =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
    simp [chartPushed]
  have hPOU_y : (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
    rw [← hpush_unfold]; exact hpush_zero
  unfold hkIntegrand
  rw [hPOU_y, zero_mul]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma hkIntegrand_zero_of_notMem_finset
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y = 0 := by
  have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
    fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  unfold hkIntegrand
  rw [hPOU_zero, zero_mul]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma hkOneTerm_zero_of_notMem_finset
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    hkOneTerm (I := I) (M := M) T S α IJ j basisIdx = 0 := by
  unfold hkOneTerm
  have h : (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y) =
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
    funext y
    exact hkIntegrand_zero_of_notMem_finset
      (I := I) (M := M) T S hα IJ j basisIdx y
  rw [h]
  simp


omit [NeZero (Module.finrank ℝ E)] in
private lemma hkIntegrand_integrableOn
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    IntegrableOn
      (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y)
      (chartTargetEuclid (I := I) (M := M) α)
      (volume :
        Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have hT_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_cont :
      ContinuousOn (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    hkIntegrand_continuousOn (I := I) (M := M) T S α IJ j basisIdx
  have h_int_K : IntegrableOn
      (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y) K
      (volume :
        Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    have h_cont_K : ContinuousOn
        (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y) K :=
      h_cont.mono hK_sub
    exact h_cont_K.integrableOn_compact hK_compact
  have h_zero_off : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ K → hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y = 0 := by
    intro y hyT hyK
    exact hkIntegrand_zero_off_compact
      (I := I) (M := M) T S α IJ j basisIdx hyT hyK
  have h_indicator_eq :
      Set.indicator (chartTargetEuclid (I := I) (M := M) α)
          (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y) =
        Set.indicator K
          (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y) := by
    funext y
    by_cases hyK : y ∈ K
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK
      simp [Set.indicator_of_mem, hyK, hyT]
    · by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
      · have hf0 := h_zero_off y hyT hyK
        rw [Set.indicator_of_mem hyT, Set.indicator_of_notMem hyK, hf0]
      · simp [Set.indicator_of_notMem, hyT, hyK]
  have h_int_T : Integrable
      (Set.indicator (chartTargetEuclid (I := I) (M := M) α)
        (fun y => hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y))
      (volume :
        Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [h_indicator_eq]
    rw [← MeasureTheory.integrable_indicator_iff hK_meas] at h_int_K
    exact h_int_K
  rw [← MeasureTheory.integrable_indicator_iff hT_meas]
  exact h_int_T


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma hkIntegrand_symm
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y =
      hkIntegrand (I := I) (M := M) S T α IJ j basisIdx y := by
  unfold hkIntegrand
  ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hkIntegrand_add_left
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T₁ T₂ S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    hkIntegrand (I := I) (M := M) (T₁ + T₂) S α IJ j basisIdx y =
      hkIntegrand (I := I) (M := M) T₁ S α IJ j basisIdx y +
      hkIntegrand (I := I) (M := M) T₂ S α IJ j basisIdx y := by
  unfold hkIntegrand
  have htoCc : (T₁ + T₂).toCcTensor =
      T₁.toCcTensor + T₂.toCcTensor :=
    SmoothCcTensorHs.toCcTensor_add T₁ T₂
  rw [htoCc]
  have hadd :=
    DifferentialGeometry.Analysis.Sobolev.Tensor.iteratedFDeriv_basisEval_add_eq
      (I := I) (M := M) g r s T₁.toCcTensor T₂.toCcTensor α IJ.1 IJ.2 j basisIdx hy
  rw [hadd]
  ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hkIntegrand_smul_left
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (c : ℝ) (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    hkIntegrand (I := I) (M := M) (c • T) S α IJ j basisIdx y =
      c * hkIntegrand (I := I) (M := M) T S α IJ j basisIdx y := by
  unfold hkIntegrand
  have htoCc : (c • T).toCcTensor = c • T.toCcTensor :=
    SmoothCcTensorHs.toCcTensor_smul c T
  rw [htoCc]
  have hsmul :=
    DifferentialGeometry.Analysis.Sobolev.Tensor.iteratedFDeriv_basisEval_smul_eq
      (I := I) (M := M) g r s c T.toCcTensor α IJ.1 IJ.2 j basisIdx hy
  rw [hsmul]
  simp only [smul_eq_mul]
  ring


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hkOneTerm_symm
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    hkOneTerm (I := I) (M := M) T S α IJ j basisIdx =
      hkOneTerm (I := I) (M := M) S T α IJ j basisIdx := by
  unfold hkOneTerm
  refine MeasureTheory.setIntegral_congr_fun
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
  intro y _
  exact hkIntegrand_symm (I := I) (M := M) T S α IJ j basisIdx y


omit [NeZero (Module.finrank ℝ E)] in
private lemma hkOneTerm_add_left
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T₁ T₂ S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    hkOneTerm (I := I) (M := M) (T₁ + T₂) S α IJ j basisIdx =
      hkOneTerm (I := I) (M := M) T₁ S α IJ j basisIdx +
      hkOneTerm (I := I) (M := M) T₂ S α IJ j basisIdx := by
  unfold hkOneTerm
  rw [← MeasureTheory.integral_add
    (hkIntegrand_integrableOn (I := I) (M := M) T₁ S α IJ j basisIdx)
    (hkIntegrand_integrableOn (I := I) (M := M) T₂ S α IJ j basisIdx)]
  refine MeasureTheory.setIntegral_congr_fun
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
  intro y hy
  exact hkIntegrand_add_left (I := I) (M := M) T₁ T₂ S α IJ j basisIdx hy


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hkOneTerm_smul_left
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (c : ℝ) (T S : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    hkOneTerm (I := I) (M := M) (c • T) S α IJ j basisIdx =
      c * hkOneTerm (I := I) (M := M) T S α IJ j basisIdx := by
  unfold hkOneTerm
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
  intro y hy
  exact hkIntegrand_smul_left (I := I) (M := M) c T S α IJ j basisIdx hy


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma hkOneTerm_self_nonneg
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    0 ≤ hkOneTerm (I := I) (M := M) T T α IJ j basisIdx := by
  unfold hkOneTerm
  refine MeasureTheory.setIntegral_nonneg
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
  intro y _
  unfold hkIntegrand
  have hPOU_nn : 0 ≤ (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
    (chartAtlasPOU I M).nonneg α _
  have hsq_nn : (0 : ℝ) ≤
      (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) *
      (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) := by
    have h := sq_nonneg
      ((iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
    simpa [sq] using h
  exact mul_nonneg hPOU_nn hsq_nn


omit [NeZero (Module.finrank ℝ E)] in
private lemma hkOneTerm_self_eq_lintegral_toReal
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T : SmoothCcTensorHs g r s k) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    hkOneTerm (I := I) (M := M) T T α IJ j basisIdx =
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                      T.toCcTensor α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm) y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E))))).toReal := by
  classical
  unfold hkOneTerm
  have h_pt_eq : ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      hkIntegrand (I := I) (M := M) T T α IJ j basisIdx y =
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s
                    T.toCcTensor α IJ.1 IJ.2
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 := by
    intro y
    unfold hkIntegrand
    have h : ∀ a : ℝ, a * a = |a| ^ 2 := by
      intro a; rw [sq_abs]; ring
    have := h ((iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T.toCcTensor α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
    rw [this]
  have h_int_congr :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          hkIntegrand (I := I) (M := M) T T α IJ j basisIdx y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                      T.toCcTensor α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm) y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    refine MeasureTheory.setIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
    intro y _; exact h_pt_eq y
  rw [h_int_congr]
  have h_nn_ae : ∀ᵐ y ∂(volume.restrict (chartTargetEuclid (I := I) (M := M) α)),
      0 ≤ ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s
                    T.toCcTensor α IJ.1 IJ.2
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro y
    refine mul_nonneg ?_ ?_
    · exact (chartAtlasPOU I M).nonneg α _
    · exact sq_nonneg _
  have h_int : IntegrableOn
      (fun y => ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s
                    T.toCcTensor α IJ.1 IJ.2
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
      (chartTargetEuclid (I := I) (M := M) α)
      (volume :
        Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    have hint := hkIntegrand_integrableOn (I := I) (M := M) T T α IJ j basisIdx
    have hcongr : ∀ y, hkIntegrand (I := I) (M := M) T T α IJ j basisIdx y =
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s
                    T.toCcTensor α IJ.1 IJ.2
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 := h_pt_eq
    exact hint.congr (Filter.Eventually.of_forall fun y => hcongr y)
  have h_int_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                      T.toCcTensor α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm) y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) =
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                      T.toCcTensor α IJ.1 IJ.2
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm) y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E))))).toReal := by
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nn_ae ?_
    exact h_int.aestronglyMeasurable
  exact h_int_eq


omit [NeZero (Module.finrank ℝ E)] in
private lemma hkInner_self_eq_normSq_toReal
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (T : SmoothCcTensorHs g r s k) :
    sobolevHkInner (I := I) (M := M) T T =
      (tensorPouSobolevHsNormSq (I := I) (M := M) g k T.toCcTensor).toReal := by
  classical
  rw [tensorPouSobolevHsNormSq_eq_inner_sum]
  have htsum_eq :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                              T.toCcTensor α IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                              T.toCcTensor α IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))) := by
    refine tsum_eq_sum ?_
    intro α hα
    have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    refine Finset.sum_eq_zero ?_
    intro IJ _
    refine Finset.sum_eq_zero ?_
    intro j _
    refine Finset.sum_eq_zero ?_
    intro basisIdx _
    have h_integrand_zero :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s
                        T.toCcTensor α IJ.1 IJ.2
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm) y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) = 0 := by
      intro y _
      rw [hPOU_zero, zero_mul, ENNReal.ofReal_zero]
    rw [MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      h_integrand_zero]
    simp
  rw [htsum_eq]
  unfold sobolevHkInner
  have h_each_lt_top :
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
      IJ ∈ (Finset.univ :
        Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)))) →
      ∀ j ∈ Finset.range (2 * k + 1),
      ∀ basisIdx : Fin j → Fin (Module.finrank ℝ E),
      basisIdx ∈ (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E))) →
        (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          T.toCcTensor α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm) y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ
                (Fin (Module.finrank ℝ E))))) ≠ ⊤ := by
    intro α _ IJ _ j _ basisIdx _
    exact (tensorPouSobolevHsNorm_inner_integral_lt_top'
      (I := I) (M := M) g r s T.toCcTensor α IJ.1 IJ.2 j basisIdx).ne
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro α hα
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl ?_
      intro IJ hIJ
      rw [ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl ?_
        intro j hj
        rw [ENNReal.toReal_sum]
        · refine Finset.sum_congr rfl ?_
          intro basisIdx hbasisIdx
          exact hkOneTerm_self_eq_lintegral_toReal
            (I := I) (M := M) T α IJ j basisIdx
        · intro basisIdx hbasisIdx
          exact h_each_lt_top α hα IJ hIJ j hj basisIdx hbasisIdx
      · intro j hj
        rw [ENNReal.sum_ne_top]
        intro basisIdx hbasisIdx
        exact h_each_lt_top α hα IJ hIJ j hj basisIdx hbasisIdx
    · intro IJ hIJ
      rw [ENNReal.sum_ne_top]
      intro j hj
      rw [ENNReal.sum_ne_top]
      intro basisIdx hbasisIdx
      exact h_each_lt_top α hα IJ hIJ j hj basisIdx hbasisIdx
  · intro α hα
    rw [ENNReal.sum_ne_top]
    intro IJ hIJ
    rw [ENNReal.sum_ne_top]
    intro j hj
    rw [ENNReal.sum_ne_top]
    intro basisIdx hbasisIdx
    exact h_each_lt_top α hα IJ hIJ j hj basisIdx hbasisIdx


noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorHs g r s k) where
  inner T S := sobolevHkInner (I := I) (M := M) T S
  conj_inner_symm T S := by
    change (sobolevHkInner (I := I) (M := M) S T : ℝ) =
      sobolevHkInner (I := I) (M := M) T S
    unfold sobolevHkInner
    refine Finset.sum_congr rfl ?_
    intro α _
    refine Finset.sum_congr rfl ?_
    intro IJ _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro basisIdx _
    exact hkOneTerm_symm (I := I) (M := M) S T α IJ j basisIdx
  re_inner_nonneg T := by
    change (0 : ℝ) ≤ sobolevHkInner (I := I) (M := M) T T
    unfold sobolevHkInner
    refine Finset.sum_nonneg ?_
    intro α _
    refine Finset.sum_nonneg ?_
    intro IJ _
    refine Finset.sum_nonneg ?_
    intro j _
    refine Finset.sum_nonneg ?_
    intro basisIdx _
    exact hkOneTerm_self_nonneg (I := I) (M := M) T α IJ j basisIdx
  add_left T₁ T₂ S := by
    change sobolevHkInner (I := I) (M := M) (T₁ + T₂) S =
      sobolevHkInner (I := I) (M := M) T₁ S +
        sobolevHkInner (I := I) (M := M) T₂ S
    unfold sobolevHkInner
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro IJ _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro basisIdx _
    exact hkOneTerm_add_left (I := I) (M := M) T₁ T₂ S α IJ j basisIdx
  smul_left T S c := by
    change sobolevHkInner (I := I) (M := M) (c • T) S =
      (c : ℝ) * sobolevHkInner (I := I) (M := M) T S
    unfold sobolevHkInner
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro α _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro IJ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro basisIdx _
    exact hkOneTerm_smul_left (I := I) (M := M) c T S α IJ j basisIdx


noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorHs g r s k) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)


noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s k : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorHs g r s k) :=
  InnerProductSpace.ofCore _

abbrev TensorPouSobolevHilbert
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) : Type _ :=
  UniformSpace.Completion (SmoothCcTensorHs g r s k)

namespace SmoothCcTensor

noncomputable def toHs {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    TensorPouSobolevHilbert (I := I) (M := M) g r s k :=
  ((⟨T⟩ : SmoothCcTensorHs g r s k) : TensorPouSobolevHilbert g r s k)

end SmoothCcTensor


omit [NeZero (Module.finrank ℝ E)] in
theorem tensorPouSobolevHilbert_norm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T‖ =
      (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal := by
  classical
  change ‖((⟨T⟩ : SmoothCcTensorHs g r s k) :
      TensorPouSobolevHilbert g r s k)‖ = _
  rw [UniformSpace.Completion.norm_coe]
  have h_norm_eq :
      ‖(⟨T⟩ : SmoothCcTensorHs g r s k)‖ =
        Real.sqrt
          (sobolevHkInner (I := I) (M := M)
            (⟨T⟩ : SmoothCcTensorHs g r s k)
            (⟨T⟩ : SmoothCcTensorHs g r s k)) := by
    rfl
  rw [h_norm_eq]
  have hdiag := hkInner_self_eq_normSq_toReal
    (I := I) (M := M) (⟨T⟩ : SmoothCcTensorHs g r s k)
  rw [hdiag]
  unfold tensorPouSobolevHsNormSq
  rw [ENNReal.toReal_pow]
  exact Real.sqrt_sq (ENNReal.toReal_nonneg)

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
