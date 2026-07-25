import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic


namespace DifferentialGeometry

structure TimeDerivativeData (R : Type*) (A : Type*) (Time : Type*)
    [CommRing R] [CommRing A] [Algebra R A] where
  dt : Derivation R A A
  lift : (Time -> R) -> A
  eval : A -> Time -> R
  lift_algebraMap : forall c : R, lift (fun _ => c) = algebraMap R A c
  eval_add : forall (a b : A) (t : Time), eval (a + b) t = eval a t + eval b t
  eval_mul : forall (a b : A) (t : Time), eval (a * b) t = eval a t * eval b t
  eval_algebraMap : forall (c : R) (t : Time), eval (algebraMap R A c) t = c

class TimeRegularFam {R : Type*} {A : Type*} {Time : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    (td : TimeDerivativeData R A Time) where
  isSmoothFam : (Time -> R) -> Prop
  eval_lift : forall (f : Time -> R), isSmoothFam f -> forall t : Time,
    td.eval (td.lift f) t = f t
  lift_add : forall (f g : Time -> R), isSmoothFam f -> isSmoothFam g ->
    td.lift (f + g) = td.lift f + td.lift g
  lift_mul : forall (f g : Time -> R), isSmoothFam f -> isSmoothFam g ->
    td.lift (f * g) = td.lift f * td.lift g
  isSmoothFam_const : forall c : R, isSmoothFam (fun _ => c)
  isSmoothFam_add : forall (f g : Time -> R), isSmoothFam f -> isSmoothFam g ->
    isSmoothFam (f + g)
  isSmoothFam_mul : forall (f g : Time -> R), isSmoothFam f -> isSmoothFam g ->
    isSmoothFam (f * g)
  isSmoothFam_neg : forall (f : Time -> R), isSmoothFam f -> isSmoothFam (-f)

namespace TimeDerivativeData

variable {R A Time : Type*} [CommRing R] [CommRing A] [Algebra R A]

abbrev isSmoothFam (td : TimeDerivativeData R A Time) [TimeRegularFam td] :
    (Time -> R) -> Prop :=
  TimeRegularFam.isSmoothFam (td := td)

theorem eval_lift (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f : Time -> R) (hf : td.isSmoothFam f) (t : Time) :
    td.eval (td.lift f) t = f t :=
  TimeRegularFam.eval_lift f hf t

theorem lift_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.lift (f + g) = td.lift f + td.lift g :=
  TimeRegularFam.lift_add f g hf hg

theorem lift_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.lift (f * g) = td.lift f * td.lift g :=
  TimeRegularFam.lift_mul f g hf hg

theorem isSmoothFam_const (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (c : R) : td.isSmoothFam (fun _ => c) :=
  TimeRegularFam.isSmoothFam_const (td := td) c

theorem isSmoothFam_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f + g) :=
  TimeRegularFam.isSmoothFam_add f g hf hg

theorem isSmoothFam_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f * g) :=
  TimeRegularFam.isSmoothFam_mul f g hf hg

theorem isSmoothFam_neg (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f : Time -> R) (hf : td.isSmoothFam f) :
    td.isSmoothFam (-f) :=
  TimeRegularFam.isSmoothFam_neg f hf

theorem isSmoothFam_sub (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.isSmoothFam (f - g) := by
  have h : f - g = f + (-g) := by
    ext t
    simp [sub_eq_add_neg]
  rw [h]
  exact td.isSmoothFam_add f (-g) hf (td.isSmoothFam_neg g hg)

theorem isSmoothFam_sum (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι : Type*} (s : Finset ι) (f : ι -> Time -> R)
    (h : forall i, i ∈ s -> td.isSmoothFam (f i)) :
    td.isSmoothFam (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty =>
      simpa using td.isSmoothFam_const (0 : R)
  | cons a s' ha ih =>
      rw [Finset.sum_cons]
      exact td.isSmoothFam_add _ _
        (h a (Finset.mem_cons_self a s'))
        (ih (fun i hi => h i (Finset.mem_cons.mpr (Or.inr hi))))

theorem isSmoothFam_const_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (c : R) (f : Time -> R) (hf : td.isSmoothFam f) :
    td.isSmoothFam (fun s => c * f s) := by
  have h : (fun s => c * f s) = (fun _ => c) * f := by
    ext s
    rfl
  rw [h]
  exact td.isSmoothFam_mul _ _ (td.isSmoothFam_const c) hf

def dt_apply (td : TimeDerivativeData R A Time) (f : Time -> R) (t : Time) : R :=
  td.eval (td.dt (td.lift f)) t

@[simp] theorem eval_zero (td : TimeDerivativeData R A Time) (t : Time) :
    td.eval (0 : A) t = 0 := by
  simpa using td.eval_algebraMap (0 : R) t

theorem dt_apply_add (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f + g) t = td.dt_apply f t + td.dt_apply g t := by
  simp [dt_apply, td.lift_add f g hf hg, map_add, td.eval_add]

theorem dt_apply_const (td : TimeDerivativeData R A Time)
    (c : R) (t : Time) :
    td.dt_apply (fun _ => c) t = 0 := by
  simp [dt_apply, td.lift_algebraMap c, Derivation.map_algebraMap]

theorem dt_apply_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f * g) t = f t * td.dt_apply g t + g t * td.dt_apply f t := by
  simp only [dt_apply, td.lift_mul f g hf hg]
  rw [td.dt.leibniz (td.lift f) (td.lift g)]
  simp only [td.eval_add, td.eval_mul, smul_eq_mul, td.eval_lift f hf,
    td.eval_lift g hg]

theorem dt_apply_const_mul (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (c : R) (f : Time -> R) (t : Time) (hf : td.isSmoothFam f) :
    td.dt_apply (fun s => c * f s) t = c * td.dt_apply f t := by
  have h : (fun s => c * f s) = (fun _ => c) * f := by
    ext s
    rfl
  rw [h, td.dt_apply_mul _ _ _ (td.isSmoothFam_const c) hf]
  rw [td.dt_apply_const]
  ring

theorem dt_apply_neg (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f : Time -> R) (t : Time) (hf : td.isSmoothFam f) :
    td.dt_apply (-f) t = -td.dt_apply f t := by
  have h := td.dt_apply_add f (-f) t hf (td.isSmoothFam_neg f hf)
  have h0 : td.dt_apply (0 : Time -> R) t = 0 := by
    change td.dt_apply (fun _ => (0 : R)) t = 0
    exact td.dt_apply_const 0 t
  simp only [add_neg_cancel] at h
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem dt_apply_sub (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (f g : Time -> R) (t : Time)
    (hf : td.isSmoothFam f) (hg : td.isSmoothFam g) :
    td.dt_apply (f - g) t = td.dt_apply f t - td.dt_apply g t := by
  have h : f - g = f + (-g) := by
    ext s
    simp [sub_eq_add_neg]
  rw [h, td.dt_apply_add _ _ _ hf (td.isSmoothFam_neg g hg),
    td.dt_apply_neg _ _ hg]
  ring

theorem dt_apply_sum (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    {ι : Type*} (s : Finset ι) (f : ι -> Time -> R) (t : Time)
    (hfs : forall i, i ∈ s -> td.isSmoothFam (f i)) :
    td.dt_apply (∑ i ∈ s, f i) t = ∑ i ∈ s, td.dt_apply (f i) t := by
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.sum_empty]
      change td.dt_apply (fun _ => (0 : R)) t = 0
      exact td.dt_apply_const 0 t
  | cons a s' ha ih =>
      have h_tail_smooth : td.isSmoothFam (∑ i ∈ s', f i) :=
        td.isSmoothFam_sum s' f (fun i hi => hfs i (Finset.mem_cons.mpr (Or.inr hi)))
      rw [Finset.sum_cons,
        td.dt_apply_add _ _ _ (hfs a (Finset.mem_cons_self a s')) h_tail_smooth,
        ih (fun i hi => hfs i (Finset.mem_cons.mpr (Or.inr hi))),
        Finset.sum_cons]

end TimeDerivativeData

end DifferentialGeometry
