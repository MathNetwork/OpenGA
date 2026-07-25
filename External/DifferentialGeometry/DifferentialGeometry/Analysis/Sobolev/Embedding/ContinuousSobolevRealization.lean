import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SmoothCcDense
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.Completion


noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle Topology Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_add_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : SmoothCcTensor g r s) (x : M) :
    (S + T).toSection x = S.toSection x + T.toSection x := by
  rw [SmoothCcTensor.toSection_add]; rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_smul_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (c : ℝ) (T : SmoothCcTensor g r s) (x : M) :
    (c • T).toSection x = c • (T.toSection x) := by
  rw [SmoothCcTensor.toSection_smul]; rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_neg_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) (x : M) :
    (-T).toSection x = -(T.toSection x) := by
  rw [SmoothCcTensor.toSection_neg]; rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma smoothCcTensor_toSection_zero_apply
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (x : M) :
    (0 : SmoothCcTensor g r s).toSection x = 0 := by
  rw [SmoothCcTensor.toSection_zero]; rfl

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

def gSupVal (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  ⨆ x : M, ‖T.toSection x‖

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
lemma bddAbove_section_norm_range
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (T : SmoothCcTensor g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    BddAbove (Set.range (fun x : M => ‖T.toSection x‖)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, _, hC⟩ := tensorPouSobolevHilbert_embedding_Ck (I := I) (M := M)
    (g := g) (r := r) (s := s) (k := k) (m := 0) (by omega)
  exact ⟨C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖,
    by rintro _ ⟨x, rfl⟩; exact hC T x⟩

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma gSupVal_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) : 0 ≤ gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [gSupVal, Real.iSup_of_isEmpty]
  · rw [gSupVal]; exact Real.iSup_nonneg (fun x => norm_nonneg _)

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma gSupVal_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    gSupVal (I := I) (M := M) g r s 0 = 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [gSupVal]
  have hz : (fun x : M => ‖(0 : SmoothCcTensor g r s).toSection x‖)
      = fun _ => (0 : ℝ) := by
    funext x; rw [smoothCcTensor_toSection_zero_apply, norm_zero]
  rw [hz]
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Real.iSup_of_isEmpty]
  · rw [ciSup_const]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma gSupVal_neg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (-T) = gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [gSupVal, gSupVal]
  congr 1; funext x
  rw [smoothCcTensor_toSection_neg_apply, norm_neg]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
lemma gSupVal_add_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (S T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (S + T) ≤
      gSupVal (I := I) (M := M) g r s S + gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]; norm_num
  · have hbS := bddAbove_section_norm_range (I := I) (M := M) g r s k hk S
    have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (add_nonneg (gSupVal_nonneg (I := I) (M := M) g r s S)
        (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(S + T).toSection x‖ ≤ ‖S.toSection x‖ + ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_add_apply]; exact norm_add_le _ _
    exact le_trans hpt (add_le_add (le_ciSup hbS x) (le_ciSup hbT x))

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
lemma gSupVal_smul_le (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (c : ℝ) (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (c • T) ≤
      |c| * gSupVal (I := I) (M := M) g r s T := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [gSupVal]
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, mul_zero]
  · have hbT := bddAbove_section_norm_range (I := I) (M := M) g r s k hk T
    rw [gSupVal, gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (mul_nonneg (abs_nonneg c) (gSupVal_nonneg (I := I) (M := M) g r s T))
    have hpt : ‖(c • T).toSection x‖ = |c| * ‖T.toSection x‖ := by
      rw [smoothCcTensor_toSection_smul_apply, norm_smul, Real.norm_eq_abs]
    rw [hpt]
    exact mul_le_mul_of_nonneg_left (le_ciSup hbT x) (abs_nonneg c)

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
lemma gSupVal_smul (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (c : ℝ) (T : SmoothCcTensor g r s) :
    gSupVal (I := I) (M := M) g r s (c • T) =
      |c| * gSupVal (I := I) (M := M) g r s T := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [zero_smul, gSupVal_zero, abs_zero, zero_mul]
  · refine le_antisymm (gSupVal_smul_le (I := I) (M := M) g r s k hk c T) ?_
    have hstep := gSupVal_smul_le (I := I) (M := M) g r s k hk c⁻¹ (c • T)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hstep
    have hcpos : 0 < |c| := abs_pos.mpr hc
    rw [abs_inv] at hstep
    have h2 : |c| * gSupVal (I := I) (M := M) g r s T ≤
        |c| * (|c|⁻¹ * gSupVal (I := I) (M := M) g r s (c • T)) :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt hcpos)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at h2

structure CSupTensor (g : SmoothRiemannianMetric I M) (r s k : ℕ) where

  toHsTensor : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)

namespace CSupTensor

variable {g : SmoothRiemannianMetric I M} {r s k : ℕ}

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[ext] theorem ext {S T : CSupTensor g r s k}
    (h : S.toHsTensor = T.toHsTensor) : S = T := by
  cases S; cases T; congr

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toHsTensor_injective :
    Function.Injective
      (fun S : CSupTensor g r s k => S.toHsTensor) := by
  intro S T h; exact ext h

instance : Zero (CSupTensor g r s k) := ⟨⟨0⟩⟩
instance : Add (CSupTensor g r s k) :=
  ⟨fun S T => ⟨S.toHsTensor + T.toHsTensor⟩⟩
instance : Neg (CSupTensor g r s k) := ⟨fun S => ⟨-S.toHsTensor⟩⟩
instance : Sub (CSupTensor g r s k) :=
  ⟨fun S T => ⟨S.toHsTensor - T.toHsTensor⟩⟩
instance : SMul ℝ (CSupTensor g r s k) :=
  ⟨fun c S => ⟨c • S.toHsTensor⟩⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_zero :
    (0 : CSupTensor g r s k).toHsTensor = 0 := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_add (S T : CSupTensor g r s k) :
    (S + T).toHsTensor = S.toHsTensor + T.toHsTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_neg (S : CSupTensor g r s k) :
    (-S).toHsTensor = -S.toHsTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_sub (S T : CSupTensor g r s k) :
    (S - T).toHsTensor = S.toHsTensor - T.toHsTensor := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toHsTensor_smul (c : ℝ) (S : CSupTensor g r s k) :
    (c • S).toHsTensor = c • S.toHsTensor := rfl

instance : SMul ℕ (CSupTensor g r s k) := ⟨nsmulRec⟩
instance : SMul ℤ (CSupTensor g r s k) := ⟨zsmulRec⟩

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
@[simp] lemma toHsTensor_nsmul (S : CSupTensor g r s k) (n : ℕ) :
    (n • S).toHsTensor = n • S.toHsTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toHsTensor = (0 : ℕ) • S.toHsTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toHsTensor = (n + 1) • S.toHsTensor
      change (nsmulRec n S + S).toHsTensor = (n + 1) • S.toHsTensor
      have hn : (nsmulRec n S).toHsTensor = n • S.toHsTensor := ih
      rw [toHsTensor_add, hn, succ_nsmul]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
@[simp] lemma toHsTensor_zsmul (S : CSupTensor g r s k) (z : ℤ) :
    (z • S).toHsTensor = z • S.toHsTensor := by
  rcases z with n | n
  · change (n • S).toHsTensor = (Int.ofNat n) • S.toHsTensor
    rw [toHsTensor_nsmul]; simp
  · change (-((n + 1) • S)).toHsTensor = (Int.negSucc n) • S.toHsTensor
    rw [toHsTensor_neg, toHsTensor_nsmul]
    show -((n + 1) • S.toHsTensor) = Int.negSucc n • S.toHsTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (CSupTensor g r s k) :=
  toHsTensor_injective.addCommGroup
    (fun S => S.toHsTensor)
    toHsTensor_zero
    toHsTensor_add
    toHsTensor_neg
    toHsTensor_sub
    toHsTensor_nsmul
    toHsTensor_zsmul

def toHsTensorAddHom :
    CSupTensor g r s k →+ IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) where
  toFun := fun S => S.toHsTensor
  map_zero' := toHsTensor_zero
  map_add' := toHsTensor_add

instance : Module ℝ (CSupTensor g r s k) :=
  toHsTensor_injective.module ℝ toHsTensorAddHom toHsTensor_smul

def ofHs :
    IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →ₗ[ℝ] CSupTensor g r s k where
  toFun := fun S => ⟨S⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
@[simp] lemma ofHs_apply
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    (ofHs (g := g) (r := r) (s := s) (k := k) S).toHsTensor = S := rfl

def toCc (S : CSupTensor g r s k) : SmoothCcTensor g r s :=
  S.toHsTensor.toCcTensor

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_zero : (0 : CSupTensor g r s k).toCc = 0 := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_add (S T : CSupTensor g r s k) :
    (S + T).toCc = S.toCc + T.toCc := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_neg (S : CSupTensor g r s k) : (-S).toCc = -S.toCc := rfl
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma toCc_smul (c : ℝ) (S : CSupTensor g r s k) :
    (c • S).toCc = c • S.toCc := rfl

end CSupTensor

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

def gSupAddGroupSeminorm (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    AddGroupSeminorm (CSupTensor g r s k) where
  toFun := fun S => gSupVal (I := I) (M := M) g r s S.toCc
  map_zero' := by
    change gSupVal (I := I) (M := M) g r s (0 : CSupTensor g r s k).toCc = 0
    rw [CSupTensor.toCc_zero, gSupVal_zero]
  add_le' := fun S T => by
    change gSupVal (I := I) (M := M) g r s (S + T).toCc ≤
      gSupVal (I := I) (M := M) g r s S.toCc +
        gSupVal (I := I) (M := M) g r s T.toCc
    rw [CSupTensor.toCc_add]
    exact gSupVal_add_le (I := I) (M := M) g r s k hk S.toCc T.toCc
  neg' := fun S => by
    change gSupVal (I := I) (M := M) g r s (-S).toCc =
      gSupVal (I := I) (M := M) g r s S.toCc
    rw [CSupTensor.toCc_neg, gSupVal_neg]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

@[reducible] noncomputable def csupSeminormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    SeminormedAddCommGroup (CSupTensor g r s k) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    (gSupAddGroupSeminorm (I := I) (M := M) g r s k hk)

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
lemma csupSeminormedAddCommGroup_norm
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) (S : CSupTensor g r s k) :
    @norm _ (csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk).toNorm S =
      gSupVal (I := I) (M := M) g r s S.toCc := rfl

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

@[reducible] noncomputable def csupNormedSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
    NormedSpace ℝ (CSupTensor g r s k) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  NormedSpace.mk (𝕜 := ℝ) (E := CSupTensor g r s k) fun c S => by
    have h1 : ‖c • S‖ = gSupVal (I := I) (M := M) g r s (c • S).toCc :=
      csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk (c • S)
    have h2 : ‖S‖ = gSupVal (I := I) (M := M) g r s S.toCc :=
      csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk S
    rw [h1, h2, CSupTensor.toCc_smul,
      gSupVal_smul (I := I) (M := M) g r s k hk c S.toCc, Real.norm_eq_abs]

noncomputable def CSupBanach (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) : Type _ :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  UniformSpace.Completion (CSupTensor g r s k)

noncomputable instance instCSupBanachNormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    NormedAddCommGroup (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  (inferInstance :
    NormedAddCommGroup (UniformSpace.Completion (CSupTensor g r s k)))

noncomputable instance instCSupBanachNormedSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    NormedSpace ℝ (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  (inferInstance :
    NormedSpace ℝ (UniformSpace.Completion (CSupTensor g r s k)))

instance instCSupBanachCompleteSpace
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    CompleteSpace (CSupBanach (I := I) (M := M) g r s k hk) :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  (inferInstance :
    CompleteSpace (UniformSpace.Completion (CSupTensor g r s k)))

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

noncomputable def smoothToC0Lin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →ₗ[ℝ]
      CSupBanach (I := I) (M := M) g r s k hk :=
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  (UniformSpace.Completion.toComplL :
    CSupTensor g r s k →L[ℝ]
      UniformSpace.Completion (CSupTensor g r s k)).toLinearMap.comp
    (CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k))

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
lemma norm_smoothToC0Lin
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E)
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ =
      gSupVal (I := I) (M := M) g r s S.toCcTensor := by
  letI := csupSeminormedAddCommGroup (I := I) (M := M) g r s k hk
  letI := csupNormedSpace (I := I) (M := M) g r s k hk
  have hiso :=
    (UniformSpace.Completion.toComplₗᵢ :
        CSupTensor g r s k →ₗᵢ[ℝ]
          UniformSpace.Completion (CSupTensor g r s k)).norm_map
      (CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k) S)
  have hval : ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ =
      ‖(CSupTensor.ofHs (g := g) (r := r) (s := s) (k := k) S :
        CSupTensor g r s k)‖ := hiso
  rw [hval, csupSeminormedAddCommGroup_norm (I := I) (M := M) g r s k hk]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma norm_coe_toCompl_eq_toHs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    ‖(S : TensorPouSobolevHilbert g r s (2 * k))‖ =
      ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S.toCcTensor‖ := by
  have hrhs : SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) S.toCcTensor =
      ((⟨S.toCcTensor⟩ : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
        TensorPouSobolevHilbert g r s (2 * k)) := rfl
  have hS : (⟨S.toCcTensor⟩ : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) = S := by
    cases S; rfl
  rw [hrhs, hS]

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
lemma exists_smoothToC0Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k),
        ‖smoothToC0Lin (I := I) (M := M) g r s k hk S‖ ≤
          C * ‖(S : TensorPouSobolevHilbert g r s (2 * k))‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨C, hCpos, hC⟩ := tensorPouSobolevHilbert_embedding_Ck (I := I) (M := M)
    (g := g) (r := r) (s := s) (k := k) (m := 0) (by omega)
  refine ⟨C, hCpos, fun S => ?_⟩
  rw [norm_smoothToC0Lin (I := I) (M := M) g r s k hk S,
    norm_coe_toCompl_eq_toHs (I := I) (M := M) g r s k S]
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [gSupVal, Real.iSup_of_isEmpty]
    exact mul_nonneg (le_of_lt hCpos) (norm_nonneg _)
  · rw [gSupVal]
    refine Real.iSup_le (fun x => ?_)
      (mul_nonneg (le_of_lt hCpos) (norm_nonneg _))
    exact hC S.toCcTensor x

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

noncomputable def tensorHsToC0
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    TensorPouSobolevHilbert g r s (2 * k) →L[ℝ]
      CSupBanach (I := I) (M := M) g r s k hk :=
  (smoothToC0Lin (I := I) (M := M) g r s k hk).extendOfNorm
    (UniformSpace.Completion.toComplL :
      IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
        TensorPouSobolevHilbert g r s (2 * k)).toLinearMap

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma denseRange_toComplL_toLinearMap
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    DenseRange
      ⇑(UniformSpace.Completion.toComplL :
        IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
          TensorPouSobolevHilbert g r s (2 * k)).toLinearMap := by
  have hcoe : ⇑(UniformSpace.Completion.toComplL :
        IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
          TensorPouSobolevHilbert g r s (2 * k)).toLinearMap =
      ((↑) : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →
        UniformSpace.Completion (IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k))) := by
    funext S; rfl
  rw [hcoe]
  exact UniformSpace.Completion.denseRange_coe

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem tensorHsToC0_coe
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E)
    (S : IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k)) :
    tensorHsToC0 (I := I) (M := M) g r s k hk
        (S : TensorPouSobolevHilbert g r s (2 * k)) =
      smoothToC0Lin (I := I) (M := M) g r s k hk S := by
  obtain ⟨C, _, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  have h := LinearMap.extendOfNorm_eq
    (f := smoothToC0Lin (I := I) (M := M) g r s k hk)
    (e := (UniformSpace.Completion.toComplL :
      IntrinsicSobolev.SmoothCcTensorHs g r s (2 * k) →L[ℝ]
        TensorPouSobolevHilbert g r s (2 * k)).toLinearMap)
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k)
    ⟨C, hC⟩ S
  exact h

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem tensorHsToC0_norm_apply_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : TensorPouSobolevHilbert g r s (2 * k),
        ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hCpos, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, fun u => ?_⟩
  exact LinearMap.norm_extendOfNorm_apply_le
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k) C hC u

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem tensorHsToC0_opNorm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ‖tensorHsToC0 (I := I) (M := M) g r s k hk‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_smoothToC0Lin_norm_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, ?_⟩
  exact LinearMap.opNorm_extendOfNorm_le
    (denseRange_toComplL_toLinearMap (I := I) (M := M) g r s k)
    (le_of_lt hCpos) hC

set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem tensorHsToC0_norm_le_of_norm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (hk : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : TensorPouSobolevHilbert g r s (2 * k)) (B : ℝ), ‖u‖ ≤ B →
        ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * B := by
  obtain ⟨C, hCpos, hC⟩ := tensorHsToC0_norm_apply_le (I := I) (M := M) g r s k hk
  refine ⟨C, hCpos, fun u B hB => ?_⟩
  calc ‖tensorHsToC0 (I := I) (M := M) g r s k hk u‖ ≤ C * ‖u‖ := hC u
    _ ≤ C * B := mul_le_mul_of_nonneg_left hB (le_of_lt hCpos)

end InnerProductSpaceModel

end DifferentialGeometry.PDE.RicciFlow

end
