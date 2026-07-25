import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real

set_option autoImplicit false
set_option linter.style.longLine false

open scoped Topology









namespace DifferentialGeometry.Integral.Connection




inductive TimeEndpoint where
  | negInf
  | finite (t : Real)
  | posInf

namespace TimeEndpoint



def lowerLt (a : TimeEndpoint) (t : Real) : Prop :=
  match a with
  | negInf => True
  | finite s => s < t
  | posInf => False



def lowerLe (a : TimeEndpoint) (t : Real) : Prop :=
  match a with
  | negInf => True
  | finite s => s <= t
  | posInf => False



def upperLt (t : Real) (b : TimeEndpoint) : Prop :=
  match b with
  | negInf => False
  | finite s => t < s
  | posInf => True



def upperLe (t : Real) (b : TimeEndpoint) : Prop :=
  match b with
  | negInf => False
  | finite s => t <= s
  | posInf => True



def lowerMem (closed : Bool) (a : TimeEndpoint) (t : Real) : Prop :=
  match closed, a with
  | _, negInf => True
  | true, finite s => s <= t
  | false, finite s => s < t
  | _, posInf => False



def upperMem (closed : Bool) (t : Real) (b : TimeEndpoint) : Prop :=
  match closed, b with
  | _, negInf => False
  | true, finite s => t <= s
  | false, finite s => t < s
  | _, posInf => True

theorem lowerLt_to_mem (closed : Bool) {a : TimeEndpoint} {t : Real}
    (h : lowerLt a t) :
  lowerMem closed a t := by
  cases closed
  · cases a with
    | negInf => simp [lowerMem]
    | finite s => exact h
    | posInf => simp [lowerLt] at h
  · cases a with
    | negInf => simp [lowerMem]
    | finite s =>
        exact le_of_lt h
    | posInf => simp [lowerLt] at h

theorem upperLt_to_mem (closed : Bool) {b : TimeEndpoint} {t : Real}
    (h : upperLt t b) :
  upperMem closed t b := by
  cases closed
  · cases b with
    | negInf => simp [upperLt] at h
    | finite s => exact h
    | posInf => simp [upperMem]
  · cases b with
    | negInf => simp [upperLt] at h
    | finite s =>
        exact le_of_lt h
    | posInf => simp [upperMem]

end TimeEndpoint



structure RealTimeInterval where
  carrier : Set Real
  regular : Set Real
  initial : Real
  initial_mem : initial ∈ carrier
  regular_subset : regular ⊆ carrier
  regular_isOpen : IsOpen regular
  regular_mem_nhds : ∀ {t : Real}, t ∈ regular -> carrier ∈ 𝓝 t

namespace RealTimeInterval

private theorem endpointCarrier_mem_nhds
    (a b : TimeEndpoint) (lowerClosed upperClosed : Bool) {t : Real}
    (ht : TimeEndpoint.lowerLt a t ∧ TimeEndpoint.upperLt t b) :
    {s : Real |
      TimeEndpoint.lowerMem lowerClosed a s ∧
        TimeEndpoint.upperMem upperClosed s b} ∈ 𝓝 t := by
  have hstrict :
      {s : Real | TimeEndpoint.lowerLt a s ∧ TimeEndpoint.upperLt s b} ∈ 𝓝 t := by
    cases a with
    | negInf =>
        cases b with
        | negInf =>
            simp [TimeEndpoint.upperLt] at ht
        | finite b =>
            simpa [TimeEndpoint.lowerLt, TimeEndpoint.upperLt] using Iio_mem_nhds ht.2
        | posInf =>
            simp [TimeEndpoint.lowerLt, TimeEndpoint.upperLt]
    | finite a =>
        cases b with
        | negInf =>
            simp [TimeEndpoint.upperLt] at ht
        | finite b =>
            simpa [TimeEndpoint.lowerLt, TimeEndpoint.upperLt] using Ioo_mem_nhds ht.1 ht.2
        | posInf =>
            simpa [TimeEndpoint.lowerLt, TimeEndpoint.upperLt] using Ioi_mem_nhds ht.1
    | posInf =>
        simp [TimeEndpoint.lowerLt] at ht
  exact
    Filter.mem_of_superset hstrict (by
      intro s hs
      exact
        ⟨TimeEndpoint.lowerLt_to_mem lowerClosed hs.1,
          TimeEndpoint.upperLt_to_mem upperClosed hs.2⟩)


abbrev FlowTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.carrier}


abbrev RegularTime (D : RealTimeInterval) : Type := {t : Real // t ∈ D.regular}


def initialTime (D : RealTimeInterval) : D.FlowTime :=
  ⟨D.initial, D.initial_mem⟩


def regularToFlow {D : RealTimeInterval} (t : D.RegularTime) : D.FlowTime :=
  ⟨t.1, D.regular_subset t.2⟩

@[simp] theorem initialTime_val (D : RealTimeInterval) :
    (D.initialTime : Real) = D.initial := by
  rfl

@[simp] theorem regularToFlow_val {D : RealTimeInterval} (t : D.RegularTime) :
    (D.regularToFlow t : Real) = (t : Real) := by
  rfl





def timeShift (D : RealTimeInterval) (τ : Real) : RealTimeInterval where
  carrier := {s : Real | s + τ ∈ D.carrier}
  regular := {s : Real | s + τ ∈ D.regular}
  initial := D.initial - τ
  initial_mem := by
    simpa [sub_add_cancel] using D.initial_mem
  regular_subset := by
    intro s hs
    exact D.regular_subset hs
  regular_isOpen := by
    exact D.regular_isOpen.preimage (continuous_id.add continuous_const)
  regular_mem_nhds := by
    intro s hs
    simpa [Set.preimage] using
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
        (D.regular_mem_nhds hs)

@[simp] theorem timeShift_carrier (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).carrier = {s : Real | s + τ ∈ D.carrier} := by
  rfl

@[simp] theorem timeShift_regular (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).regular = {s : Real | s + τ ∈ D.regular} := by
  rfl

@[simp] theorem timeShift_initial (D : RealTimeInterval) (τ : Real) :
    (D.timeShift τ).initial = D.initial - τ := by
  rfl

@[simp] theorem timeShift_initial_self (D : RealTimeInterval) :
    (D.timeShift D.initial).initial = 0 := by
  simp [timeShift]

@[simp] theorem timeShift_initialTime_val (D : RealTimeInterval) (τ : Real) :
    ((D.timeShift τ).initialTime : Real) = D.initial - τ := by
  rfl

@[simp] theorem timeShift_initialTime_self_val (D : RealTimeInterval) :
    ((D.timeShift D.initial).initialTime : Real) = 0 := by
  simp [timeShift]






def ofEndpoints
    (a b : TimeEndpoint) (lowerClosed upperClosed : Bool)
    (initial : Real)
    (hinit :
      TimeEndpoint.lowerMem lowerClosed a initial ∧
        TimeEndpoint.upperMem upperClosed initial b) : RealTimeInterval where
  carrier := {t : Real |
    TimeEndpoint.lowerMem lowerClosed a t ∧
      TimeEndpoint.upperMem upperClosed t b}
  regular := {t : Real | TimeEndpoint.lowerLt a t ∧ TimeEndpoint.upperLt t b}
  initial := initial
  initial_mem := hinit
  regular_subset := by
    intro t ht
    exact
      ⟨TimeEndpoint.lowerLt_to_mem lowerClosed ht.1,
        TimeEndpoint.upperLt_to_mem upperClosed ht.2⟩
  regular_isOpen := by
    have h1 : IsOpen {t : Real | TimeEndpoint.lowerLt a t} := by
      cases a with
      | negInf => simp [TimeEndpoint.lowerLt]
      | finite s => simpa [TimeEndpoint.lowerLt] using isOpen_Ioi
      | posInf => simp [TimeEndpoint.lowerLt]
    have h2 : IsOpen {t : Real | TimeEndpoint.upperLt t b} := by
      cases b with
      | negInf => simp [TimeEndpoint.upperLt]
      | finite s => simpa [TimeEndpoint.upperLt] using isOpen_Iio
      | posInf => simp [TimeEndpoint.upperLt]
    exact h1.inter h2
  regular_mem_nhds := by
    intro t ht
    exact endpointCarrier_mem_nhds a b lowerClosed upperClosed ht


def closed (a b : Real) (hab : a ≤ b) : RealTimeInterval where
  carrier := Set.Icc a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Icc_mem_nhds ht.1 ht.2


def closedOpen (a b : Real) (hab : a < b) : RealTimeInterval where
  carrier := Set.Ico a b
  regular := Set.Ioo a b
  initial := a
  initial_mem := ⟨le_rfl, hab⟩
  regular_subset := by
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ico_mem_nhds ht.1 ht.2



theorem timeShift_closedOpen_carrier
    {a b : Real} (hab : a < b) :
    ((closedOpen a b hab).timeShift a).carrier = Set.Ico 0 (b - a) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩



theorem timeShift_closedOpen_regular
    {a b : Real} (hab : a < b) :
    ((closedOpen a b hab).timeShift a).regular = Set.Ioo 0 (b - a) := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · intro hs
    rcases hs with ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩


def openInterval (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioo a b) : RealTimeInterval where
  carrier := Set.Ioo a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ioo_mem_nhds ht.1 ht.2


def openClosed (a b t₀ : Real) (ht₀ : t₀ ∈ Set.Ioc a b) : RealTimeInterval where
  carrier := Set.Ioc a b
  regular := Set.Ioo a b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩
  regular_isOpen := isOpen_Ioo
  regular_mem_nhds := by
    intro t ht
    exact Ioc_mem_nhds ht.1 ht.2


def closedInfinite (a : Real) : RealTimeInterval where
  carrier := Set.Ici a
  regular := Set.Ioi a
  initial := a
  initial_mem := by
    exact Set.mem_Ici.mpr le_rfl
  regular_subset := by
    intro t ht
    exact Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht))
  regular_isOpen := isOpen_Ioi
  regular_mem_nhds := by
    intro t ht
    exact Ici_mem_nhds (Set.mem_Ioi.mp ht)


def openInfinite (a t₀ : Real) (ht₀ : a < t₀) : RealTimeInterval where
  carrier := Set.Ioi a
  regular := Set.Ioi a
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Ioi
  regular_mem_nhds := by
    intro t ht
    exact Ioi_mem_nhds ht


def infiniteClosed (b t₀ : Real) (ht₀ : t₀ ≤ b) : RealTimeInterval where
  carrier := Set.Iic b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp ht))
  regular_isOpen := isOpen_Iio
  regular_mem_nhds := by
    intro t ht
    exact Iic_mem_nhds (Set.mem_Iio.mp ht)


def infiniteOpen (b t₀ : Real) (ht₀ : t₀ < b) : RealTimeInterval where
  carrier := Set.Iio b
  regular := Set.Iio b
  initial := t₀
  initial_mem := ht₀
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_Iio
  regular_mem_nhds := by
    intro t ht
    exact Iio_mem_nhds ht


def univ (t₀ : Real) : RealTimeInterval where
  carrier := Set.univ
  regular := Set.univ
  initial := t₀
  initial_mem := trivial
  regular_subset := by
    intro t ht
    exact ht
  regular_isOpen := isOpen_univ
  regular_mem_nhds := by
    intro t ht
    simp

end RealTimeInterval

end DifferentialGeometry.Integral.Connection
