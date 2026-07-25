import DifferentialGeometry.Analysis.Integration.L2.CompactSupport
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Topology.Algebra.Support
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Manifold Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def compactlySupportedSmoothTensorSections
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (r s : ℕ) :
    Submodule ℝ (Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) where
  carrier :=
    { S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        (fun x : M => TensorRSSpace r s I x)⟯ |
        HasCompactSupport
          (fun x : M => TensorRSSpace.toModel (S x)) }
  zero_mem' := by
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
      funext x
      simp [ContMDiffSection.coe_zero,
        TensorRSSpace.toModel_zero]
    rw [h]
    exact HasCompactSupport.zero
  add_mem' := by
    intro S T hS hT
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((S + T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((S + T : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun x : M => TensorRSSpace.toModel (S x)) +
          (fun x : M => TensorRSSpace.toModel (T x)) := by
      funext x
      simp [ContMDiffSection.coe_add, Pi.add_apply,
        TensorRSSpace.toModel_add]
    rw [h]
    exact hS.add hT
  smul_mem' := by
    intro c S hS
    change HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        ((c • S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x))
    have h : (fun x : M => TensorRSSpace.toModel
        ((c • S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
          (fun x : M => TensorRSSpace r s I x)⟯) x)) =
        (fun _ : M => c) •
          (fun x : M => TensorRSSpace.toModel (S x)) := by
      funext x
      simp [ContMDiffSection.coe_smul, Pi.smul_apply,
        TensorRSSpace.toModel_smul]
    rw [h]
    exact hS.smul_left

@[simp]
lemma mem_compactlySupportedSmoothTensorSections {r s : ℕ}
    {S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯} :
    S ∈ compactlySupportedSmoothTensorSections I M r s ↔
      HasCompactSupport
        (fun x : M => TensorRSSpace.toModel (S x)) := Iff.rfl

structure SmoothCcTensor (g : SmoothRiemannianMetric I M) (r s : ℕ) where

  toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
    (fun x : M => TensorRSSpace r s I x)⟯

  hasCompactSupport :
    HasCompactSupport (fun x : M => TensorRSSpace.toModel (toSection x))

namespace SmoothCcTensor


def toFun {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) : M → TensorRSModel r s ℝ E :=
  fun x => TensorRSSpace.toModel (S.toSection x)

@[simp] lemma toFun_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (x : M) :
    S.toFun x = TensorRSSpace.toModel (S.toSection x) := rfl

@[ext] lemma ext
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S T : SmoothCcTensor g r s} (h : S.toSection = T.toSection) :
    S = T := by
  cases S; cases T; congr

end SmoothCcTensor

section Algebra

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

instance : Zero (SmoothCcTensor g r s) where
  zero :=
    { toSection := 0
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
          funext x
          simp [ContMDiffSection.coe_zero,
            TensorRSSpace.toModel_zero]
        rw [h]
        exact HasCompactSupport.zero }

instance : Add (SmoothCcTensor g r s) where
  add S T :=
    { toSection := S.toSection + T.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((S.toSection + T.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun x : M => TensorRSSpace.toModel (S.toSection x)) +
              (fun x : M => TensorRSSpace.toModel (T.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_add, Pi.add_apply,
            TensorRSSpace.toModel_add]
        rw [h]
        exact S.hasCompactSupport.add T.hasCompactSupport }

instance : Neg (SmoothCcTensor g r s) where
  neg S :=
    { toSection := -S.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((-S.toSection : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            -(fun x : M => TensorRSSpace.toModel (S.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_neg, Pi.neg_apply,
            TensorRSSpace.toModel_neg]
        rw [h]
        exact S.hasCompactSupport.neg }

instance : Sub (SmoothCcTensor g r s) where
  sub S T :=
    { toSection := S.toSection - T.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((S.toSection - T.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun x : M => TensorRSSpace.toModel (S.toSection x)) -
              (fun x : M => TensorRSSpace.toModel (T.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_sub, Pi.sub_apply,
            TensorRSSpace.toModel_sub]
        rw [h]
        exact S.hasCompactSupport.sub T.hasCompactSupport }

instance : SMul ℝ (SmoothCcTensor g r s) where
  smul c S :=
    { toSection := c • S.toSection
      hasCompactSupport := by
        have h : (fun x : M => TensorRSSpace.toModel
            ((c • S.toSection :
              Cₛ^∞⟮I; TensorRSModel r s ℝ E,
              (fun x : M => TensorRSSpace r s I x)⟯) x)) =
            (fun _ : M => c) •
              (fun x : M => TensorRSSpace.toModel (S.toSection x)) := by
          funext x
          simp [ContMDiffSection.coe_smul, Pi.smul_apply,
            TensorRSSpace.toModel_smul]
        rw [h]
        exact S.hasCompactSupport.smul_left }


lemma SmoothCcTensor.toSection_injective :
    Function.Injective (fun S : SmoothCcTensor g r s => S.toSection) := by
  intro S T h
  exact SmoothCcTensor.ext h

@[simp] lemma SmoothCcTensor.toSection_zero :
    (0 : SmoothCcTensor g r s).toSection = 0 := rfl

@[simp] lemma SmoothCcTensor.toSection_add (S T : SmoothCcTensor g r s) :
    (S + T).toSection = S.toSection + T.toSection := rfl

@[simp] lemma SmoothCcTensor.toSection_neg (S : SmoothCcTensor g r s) :
    (-S).toSection = -S.toSection := rfl

@[simp] lemma SmoothCcTensor.toSection_sub (S T : SmoothCcTensor g r s) :
    (S - T).toSection = S.toSection - T.toSection := rfl

@[simp] lemma SmoothCcTensor.toSection_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (c • S).toSection = c • S.toSection := rfl

instance : SMul ℕ (SmoothCcTensor g r s) := ⟨nsmulRec⟩

instance : SMul ℤ (SmoothCcTensor g r s) := ⟨zsmulRec⟩

@[simp] lemma SmoothCcTensor.toSection_nsmul (S : SmoothCcTensor g r s) (n : ℕ) :
    (n • S).toSection = n • S.toSection := by
  induction n with
  | zero =>
    change (nsmulRec 0 S).toSection = (0 : ℕ) • S.toSection
    simp [nsmulRec]
  | succ n ih =>
    change (nsmulRec (n + 1) S).toSection = (n + 1) • S.toSection
    change (nsmulRec n S + S).toSection = (n + 1) • S.toSection
    have hn : (nsmulRec n S).toSection = n • S.toSection := ih
    rw [SmoothCcTensor.toSection_add, hn, succ_nsmul]

@[simp] lemma SmoothCcTensor.toSection_zsmul (S : SmoothCcTensor g r s) (z : ℤ) :
    (z • S).toSection = z • S.toSection := by
  rcases z with n | n
  · change (n • S).toSection = (Int.ofNat n) • S.toSection
    rw [SmoothCcTensor.toSection_nsmul]
    simp
  · change (-((n + 1) • S)).toSection = (Int.negSucc n) • S.toSection
    rw [SmoothCcTensor.toSection_neg, SmoothCcTensor.toSection_nsmul]
    show -((n + 1) • S.toSection) =
      Int.negSucc n • S.toSection
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothCcTensor g r s) :=
  SmoothCcTensor.toSection_injective.addCommGroup
    (fun S => S.toSection)
    SmoothCcTensor.toSection_zero
    SmoothCcTensor.toSection_add
    SmoothCcTensor.toSection_neg
    SmoothCcTensor.toSection_sub
    SmoothCcTensor.toSection_nsmul
    SmoothCcTensor.toSection_zsmul


def SmoothCcTensor.toSectionAddHom :
    SmoothCcTensor g r s →+ Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯ where
  toFun := fun S => S.toSection
  map_zero' := SmoothCcTensor.toSection_zero
  map_add' := SmoothCcTensor.toSection_add

instance : Module ℝ (SmoothCcTensor g r s) :=
  SmoothCcTensor.toSection_injective.module ℝ
    SmoothCcTensor.toSectionAddHom
    SmoothCcTensor.toSection_smul

@[simp] lemma SmoothCcTensor.toFun_zero :
    (0 : SmoothCcTensor g r s).toFun = 0 := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_zero,
    ContMDiffSection.coe_zero, TensorRSSpace.toModel_zero]

@[simp] lemma SmoothCcTensor.toFun_add (S T : SmoothCcTensor g r s) :
    (S + T).toFun = S.toFun + T.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply, TensorRSSpace.toModel_add]

@[simp] lemma SmoothCcTensor.toFun_neg (S : SmoothCcTensor g r s) :
    (-S).toFun = -S.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_neg,
    ContMDiffSection.coe_neg, Pi.neg_apply, TensorRSSpace.toModel_neg]

@[simp] lemma SmoothCcTensor.toFun_sub (S T : SmoothCcTensor g r s) :
    (S - T).toFun = S.toFun - T.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]

@[simp] lemma SmoothCcTensor.toFun_smul (c : ℝ) (S : SmoothCcTensor g r s) :
    (c • S).toFun = c • S.toFun := by
  funext x
  simp [SmoothCcTensor.toFun, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply, TensorRSSpace.toModel_smul]

end Algebra

end L2
end Integral
end DifferentialGeometry

end
