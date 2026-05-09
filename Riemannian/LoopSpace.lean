import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Riemannian.LoopSpace

Basic loop-space primitives.

This file defines:

* `Riemannian.BasedLoop X base`: continuous loops in `X` based at `base`;
* `Riemannian.FreeLoop X`: continuous loops in `X` with no chosen basepoint.

Both are represented as continuous maps from the closed interval `[0, 1]`.
This is intentionally topological rather than Riemannian: manifolds and
Riemannian manifolds can consume the same definitions through their underlying
topology.
-/

namespace Riemannian

/-- The closed unit interval `[0, 1]`, used as the parameter space for loops. -/
abbrev LoopInterval : Type := Set.Icc (0 : ℝ) 1

namespace LoopInterval

/-- The initial point `0` of the loop interval. -/
def zero : LoopInterval :=
  ⟨0, by constructor <;> norm_num⟩

/-- The terminal point `1` of the loop interval. -/
def one : LoopInterval :=
  ⟨1, by constructor <;> norm_num⟩

@[simp] theorem zero_val : ((zero : LoopInterval) : ℝ) = 0 := rfl

@[simp] theorem one_val : ((one : LoopInterval) : ℝ) = 1 := rfl

end LoopInterval

/-- The **based loop space** at `base`: continuous maps
`γ : [0, 1] → X` satisfying `γ(0) = base` and `γ(1) = base`. -/
structure BasedLoop (X : Type*) [TopologicalSpace X] (base : X) where
  /-- The underlying map from the unit interval. -/
  toFun : LoopInterval → X
  /-- The loop is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The loop starts at the basepoint. -/
  map_zero : toFun LoopInterval.zero = base
  /-- The loop ends at the basepoint. -/
  map_one : toFun LoopInterval.one = base

/-- Synonym emphasizing the type as a space of based loops. -/
abbrev LoopSpace (X : Type*) [TopologicalSpace X] (base : X) : Type _ :=
  BasedLoop X base

namespace BasedLoop

variable {X : Type*} [TopologicalSpace X] {base : X}

instance : CoeFun (BasedLoop X base) (fun _ => LoopInterval → X) :=
  ⟨BasedLoop.toFun⟩

@[simp] theorem apply_zero (γ : BasedLoop X base) :
    γ LoopInterval.zero = base :=
  γ.map_zero

@[simp] theorem apply_one (γ : BasedLoop X base) :
    γ LoopInterval.one = base :=
  γ.map_one

/-- The constant based loop at `base`. -/
def const (base : X) : BasedLoop X base where
  toFun := fun _ => base
  continuous_toFun := continuous_const
  map_zero := rfl
  map_one := rfl

instance instNonempty (base : X) : Nonempty (BasedLoop X base) :=
  ⟨const base⟩

end BasedLoop

/-- The **free loop space** of `X`: continuous maps `γ : [0, 1] → X`
whose endpoints agree. No basepoint is fixed. -/
structure FreeLoop (X : Type*) [TopologicalSpace X] where
  /-- The underlying map from the unit interval. -/
  toFun : LoopInterval → X
  /-- The loop is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The endpoints agree. -/
  isLoop : toFun LoopInterval.zero = toFun LoopInterval.one

/-- Synonym emphasizing the type as a space of free loops. -/
abbrev FreeLoopSpace (X : Type*) [TopologicalSpace X] : Type _ :=
  FreeLoop X

namespace FreeLoop

variable {X : Type*} [TopologicalSpace X]

instance : CoeFun (FreeLoop X) (fun _ => LoopInterval → X) :=
  ⟨FreeLoop.toFun⟩

@[simp] theorem apply_zero_eq_apply_one (γ : FreeLoop X) :
    γ LoopInterval.zero = γ LoopInterval.one :=
  γ.isLoop

/-- The constant free loop at a point. -/
def const (x : X) : FreeLoop X where
  toFun := fun _ => x
  continuous_toFun := continuous_const
  isLoop := rfl

noncomputable instance instNonempty [h : Nonempty X] : Nonempty (FreeLoop X) :=
  ⟨const (Classical.choice h)⟩

end FreeLoop

end Riemannian
