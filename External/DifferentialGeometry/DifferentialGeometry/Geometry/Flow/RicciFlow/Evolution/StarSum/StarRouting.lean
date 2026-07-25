import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.StarSum2

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unnecessarySeqFocus false



















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}









def tfPos (k : ℕ) (q : Fin (4 + (k + 1))) :
    Fin (((4 + (k + 1)) + (4 + 0)) + 2 * 0) → Fin ((4 + (k + 1)) + 2 * (2 + 0)) := fun a =>
  if a.val = 0 then ⟨0, by omega⟩
  else if a.val = q.val then ⟨2, by omega⟩
  else if h : a.val ≤ k + 4 then ⟨4 + a.val, by omega⟩
  else if a.val = k + 5 then ⟨1, by omega⟩
  else if a.val = k + 6 then ⟨4, by omega⟩
  else if a.val = k + 7 then ⟨4 + q.val, by have := q.isLt; omega⟩
  else ⟨3, by omega⟩


def sigmaCurvPos (k : ℕ) (q : Fin (4 + (k + 1))) (hq : q.val ≠ 0) :
    Fin (((4 + (k + 1)) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  Equiv.ofBijective (tfPos k q) (by
    have hqlt := q.isLt
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, by simp only [Fintype.card_fin]⟩
    apply Fin.ext
    simp only [tfPos] at hab
    split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega)



theorem sigmaCurvPos_cast_val (k : ℕ) (q : Fin (4 + (k + 1))) (hq : q.val ≠ 0)
    (p : Fin (4 + (k + 1))) :
    ((sigmaCurvPos k q hq) (Fin.castAdd (4 + 0) p)).val
      = if p.val = 0 then 0 else if p.val = q.val then 2 else 4 + p.val := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaCurvPos, Equiv.ofBijective_apply, tfPos, Fin.val_castAdd]
  split_ifs <;> first | rfl | omega



theorem sigmaCurvPos_nat_val (k : ℕ) (q : Fin (4 + (k + 1))) (hq : q.val ≠ 0)
    (p : Fin (4 + 0)) :
    ((sigmaCurvPos k q hq) (Fin.natAdd (4 + (k + 1)) p)).val
      = if p.val = 0 then 1 else if p.val = 1 then 4 else if p.val = 2 then 4 + q.val else 3 := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaCurvPos, Equiv.ofBijective_apply, tfPos, Fin.val_natAdd]
  split_ifs <;> first | rfl | omega



omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem wRoute_val {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x)) (k : ℕ) (i j : Idx)
    (m : Fin (4 + (k + 1)) → Idx) (idx : Fin (((4 + (k + 1)) + 2) + 2)) :
    metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p))) idx
      = if idx.val = 0 then basis i else if idx.val = 1 then basis i
        else if idx.val = 2 then basis j else if idx.val = 3 then basis j
        else basis (m ⟨idx.val - 4, by have := idx.isLt; omega⟩) := by
  rw [metricTraceInput_apply]
  by_cases h0 : idx.val = 0
  · rw [dif_pos h0, if_pos h0]
  · rw [dif_neg h0, if_neg h0]
    by_cases h1 : idx.val = 1
    · rw [dif_pos h1, if_pos h1]
    · rw [dif_neg h1, if_neg h1, metricTraceInput_apply]
      by_cases h2 : idx.val - 2 = 0
      · rw [dif_pos (by simpa using h2), if_pos (by omega)]
      · rw [dif_neg (by simpa using h2), if_neg (by omega)]
        by_cases h3 : idx.val - 2 = 1
        · rw [dif_pos (by simpa using h3), if_pos (by omega)]
        · rw [dif_neg (by simpa using h3), if_neg (by omega)]
          congr 2




set_option maxHeartbeats 1000000 in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem curvactStarPos
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    (q : Fin (4 + (k + 1))) (hq : q.val ≠ 0) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (m : Fin (4 + (k + 1)) → Idx) :
    starBaseField (I := I) S t (k + 1) (k + 1) 0 0 (sigmaCurvPos k q hq) x (fun p => basis (m p))
      = ∑ j : Idx, ∑ i : Idx,
          nablaKRm04Field (I := I) S t (k + 1) x
              (Function.update (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i) (fun l : Fin (4 + k) => basis (m l.succ))) q (basis j))
            * nablaKRm04Field (I := I) S t 0 x
              (vec4 (I := I) (basis i) (basis (m 0))
                (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i) (fun l : Fin (4 + k) => basis (m l.succ)) q) (basis j)) := by
  rw [starBaseProd_eq (I := I) S t (k + 1) (k + 1) 0 basis horth (sigmaCurvPos k q hq) m]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hqlt := q.isLt
  have hL : (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p)))
        ((sigmaCurvPos k q hq) (Fin.castAdd (4 + 0) p)))
      = Function.update (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i) (fun l : Fin (4 + k) => basis (m l.succ))) q (basis j) := by
    funext p
    have hplt := p.isLt
    have hcons : ∀ r : Fin (4 + (k + 1)), r ≠ 0 →
        (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
          (fun l : Fin (4 + k) => basis (m l.succ))) r = basis (m r) := by
      intro r hr
      conv_lhs => rw [← Fin.succ_pred r hr]
      rw [Fin.cons_succ, Fin.succ_pred]
    rw [wRoute_val basis k i j m, Function.update_apply]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaCurvPos k q hq) (Fin.castAdd (4 + 0) p)).val = 0 := by
        rw [sigmaCurvPos_cast_val]; split_ifs <;> omega
      rw [if_pos hcv, if_neg (Fin.ne_of_val_ne (by omega)),
        Fin.ext (a := p) (b := 0) h0, Fin.cons_zero]
    · rcases eq_or_ne p.val q.val with hq2 | hq2
      · have hcv : ((sigmaCurvPos k q hq) (Fin.castAdd (4 + 0) p)).val = 2 := by
          rw [sigmaCurvPos_cast_val]; split_ifs <;> omega
        rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_pos hcv, if_pos (Fin.ext hq2)]
      · have hcv : ((sigmaCurvPos k q hq) (Fin.castAdd (4 + 0) p)).val = 4 + p.val := by
          rw [sigmaCurvPos_cast_val]; split_ifs <;> omega
        rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (Fin.ne_of_val_ne (by omega)), hcons p (Fin.ne_of_val_ne h0)]
        congr 2
        simp only [hcv, Nat.add_sub_cancel_left, Fin.eta]
  have hR : (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p)))
        ((sigmaCurvPos k q hq) (Fin.natAdd (4 + (k + 1)) p)))
      = vec4 (I := I) (basis i) (basis (m 0))
          (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i) (fun l : Fin (4 + k) => basis (m l.succ)) q) (basis j) := by
    funext p
    have hplt := p.isLt
    rw [wRoute_val basis k i j m, vec4]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaCurvPos k q hq) (Fin.natAdd (4 + (k + 1)) p)).val = 1 := by
        rw [sigmaCurvPos_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_pos hcv, if_pos (Fin.ext h0)]
    · rcases eq_or_ne p.val 1 with h1 | h1
      · have hcv : ((sigmaCurvPos k q hq) (Fin.natAdd (4 + (k + 1)) p)).val = 4 := by
          rw [sigmaCurvPos_nat_val]; split_ifs <;> omega
        rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (Fin.ne_of_val_ne h0), if_pos (Fin.ext h1)]
        congr 2
        simp only [hcv]; rfl
      · rcases eq_or_ne p.val 2 with h2 | h2
        · have hcv : ((sigmaCurvPos k q hq) (Fin.natAdd (4 + (k + 1)) p)).val = 4 + q.val := by
            rw [sigmaCurvPos_nat_val]; split_ifs <;> omega
          have hcons : (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
              (fun l : Fin (4 + k) => basis (m l.succ))) q = basis (m q) := by
            conv_lhs => rw [← Fin.succ_pred q (Fin.ne_of_val_ne hq)]
            rw [Fin.cons_succ, Fin.succ_pred]
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
            if_pos (Fin.ext h2), hcons]
          congr 2
          simp only [hcv, Nat.add_sub_cancel_left, Fin.eta]
        · have hcv : ((sigmaCurvPos k q hq) (Fin.natAdd (4 + (k + 1)) p)).val = 3 := by
            rw [sigmaCurvPos_nat_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_pos hcv,
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
            if_neg (Fin.ne_of_val_ne h2)]
  rw [hL, hR]







def tf0 (k : ℕ) :
    Fin (((4 + (k + 1)) + (4 + 0)) + 2 * 0) → Fin ((4 + (k + 1)) + 2 * (2 + 0)) := fun a =>
  if a.val = 0 then ⟨2, by omega⟩
  else if h : a.val ≤ k + 4 then ⟨4 + a.val, by omega⟩
  else if a.val = k + 5 then ⟨0, by omega⟩
  else if a.val = k + 6 then ⟨4, by omega⟩
  else if a.val = k + 7 then ⟨1, by omega⟩
  else ⟨3, by omega⟩


def sigmaCurv0 (k : ℕ) :
    Fin (((4 + (k + 1)) + (4 + 0)) + 2 * 0) ≃ Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  Equiv.ofBijective (tf0 k) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, by simp only [Fintype.card_fin]⟩
    apply Fin.ext
    simp only [tf0] at hab
    split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega)


theorem sigmaCurv0_cast_val (k : ℕ) (p : Fin (4 + (k + 1))) :
    ((sigmaCurv0 k) (Fin.castAdd (4 + 0) p)).val
      = if p.val = 0 then 2 else 4 + p.val := by
  have hplt := p.isLt
  simp only [sigmaCurv0, Equiv.ofBijective_apply, tf0, Fin.val_castAdd]
  split_ifs <;> first | rfl | omega


theorem sigmaCurv0_nat_val (k : ℕ) (p : Fin (4 + 0)) :
    ((sigmaCurv0 k) (Fin.natAdd (4 + (k + 1)) p)).val
      = if p.val = 0 then 0 else if p.val = 1 then 4 else if p.val = 2 then 1 else 3 := by
  have hplt := p.isLt
  simp only [sigmaCurv0, Equiv.ofBijective_apply, tf0, Fin.val_natAdd]
  split_ifs <;> first | rfl | omega

set_option maxHeartbeats 1000000 in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem curvactStar0
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (m : Fin (4 + (k + 1)) → Idx) :
    starBaseField (I := I) S t (k + 1) (k + 1) 0 0 (sigmaCurv0 k) x (fun p => basis (m p))
      = ∑ j : Idx, ∑ i : Idx,
          nablaKRm04Field (I := I) S t (k + 1) x
              (Function.update (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
                (fun l : Fin (4 + k) => basis (m l.succ))) 0 (basis j))
            * nablaKRm04Field (I := I) S t 0 x
              (vec4 (I := I) (basis i) (basis (m 0)) (basis i) (basis j)) := by
  rw [starBaseProd_eq (I := I) S t (k + 1) (k + 1) 0 basis horth (sigmaCurv0 k) m]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hL : (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p)))
        ((sigmaCurv0 k) (Fin.castAdd (4 + 0) p)))
      = Function.update (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
          (fun l : Fin (4 + k) => basis (m l.succ))) 0 (basis j) := by
    funext p
    have hplt := p.isLt
    have hcons : ∀ r : Fin (4 + (k + 1)), r ≠ 0 →
        (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
          (fun l : Fin (4 + k) => basis (m l.succ))) r = basis (m r) := by
      intro r hr
      conv_lhs => rw [← Fin.succ_pred r hr]
      rw [Fin.cons_succ, Fin.succ_pred]
    rw [wRoute_val basis k i j m, Function.update_apply]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaCurv0 k) (Fin.castAdd (4 + 0) p)).val = 2 := by
        rw [sigmaCurv0_cast_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos hcv,
        if_pos (Fin.ext h0)]
    · have hcv : ((sigmaCurv0 k) (Fin.castAdd (4 + 0) p)).val = 4 + p.val := by
        rw [sigmaCurv0_cast_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (Fin.ne_of_val_ne h0), hcons p (Fin.ne_of_val_ne h0)]
      congr 2
      simp only [hcv, Nat.add_sub_cancel_left, Fin.eta]
  have hR : (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis j) (basis j) (fun p => basis (m p)))
        ((sigmaCurv0 k) (Fin.natAdd (4 + (k + 1)) p)))
      = vec4 (I := I) (basis i) (basis (m 0)) (basis i) (basis j) := by
    funext p
    have hplt := p.isLt
    rw [wRoute_val basis k i j m, vec4]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaCurv0 k) (Fin.natAdd (4 + (k + 1)) p)).val = 0 := by
        rw [sigmaCurv0_nat_val]; split_ifs <;> omega
      rw [if_pos hcv, if_pos (Fin.ext h0)]
    · rcases eq_or_ne p.val 1 with h1 | h1
      · have hcv : ((sigmaCurv0 k) (Fin.natAdd (4 + (k + 1)) p)).val = 4 := by
          rw [sigmaCurv0_nat_val]; split_ifs <;> omega
        rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (Fin.ne_of_val_ne h0), if_pos (Fin.ext h1)]
        congr 2
        simp only [hcv]; rfl
      · rcases eq_or_ne p.val 2 with h2 | h2
        · have hcv : ((sigmaCurv0 k) (Fin.natAdd (4 + (k + 1)) p)).val = 1 := by
            rw [sigmaCurv0_nat_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_pos hcv,
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1), if_pos (Fin.ext h2)]
        · have hcv : ((sigmaCurv0 k) (Fin.natAdd (4 + (k + 1)) p)).val = 3 := by
            rw [sigmaCurv0_nat_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_pos hcv,
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
            if_neg (Fin.ne_of_val_ne h2)]
  rw [hL, hR]



def tfDiffA (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) →
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  fun a =>
    if a.val = 0 then
      ⟨0, by omega⟩
    else if a.val = 1 then
      ⟨1, by omega⟩
    else if a.val = 2 then
      ⟨4, by omega⟩
    else if a.val = 3 then
      ⟨5 + q.val, by omega⟩
    else if a.val = 4 then
      ⟨2, by omega⟩
    else if a.val = 5 + q.val then
      ⟨3, by omega⟩
    else
      ⟨a.val, by omega⟩


def sigmaDiffA (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) ≃
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  Equiv.ofBijective (tfDiffA k q) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, by simp only [Fintype.card_fin]; omega⟩
    apply Fin.ext
    simp only [tfDiffA] at hab
    split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega)

@[simp]
theorem sigmaDiffA_cast_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + 1)) :
    ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val =
      if p.val = 0 then 0
      else if p.val = 1 then 1
      else if p.val = 2 then 4
      else if p.val = 3 then 5 + q.val
      else 2 := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaDiffA, Equiv.ofBijective_apply, tfDiffA, Fin.val_castAdd]
  split_ifs <;> first | rfl | omega

@[simp]
theorem sigmaDiffA_nat_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + k)) :
    ((sigmaDiffA k q) (Fin.natAdd (4 + 1) p)).val =
      if p.val = q.val then 3 else 5 + p.val := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaDiffA, Equiv.ofBijective_apply, tfDiffA, Fin.val_natAdd]
  split_ifs <;> first | rfl | omega

set_option maxHeartbeats 1000000 in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem slotdiffStarA
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (m : Fin (4 + (k + 1)) → Idx) :
    starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaDiffA k q) x
        (fun p => basis (m p)) =
      ∑ e : Idx, ∑ i : Idx,
        nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) (basis i) (basis i) (basis (m 0)) (basis (m q.succ)) (basis e)) *
        nablaKRm04Field (I := I) S t k x
          (Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e)) := by
  rw [starBaseProd_eq (I := I) S t (k + 1) 1 k basis horth (sigmaDiffA k q) m]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => ?_
  have hL :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)))
        = vec5 (I := I) (basis i) (basis i) (basis (m 0)) (basis (m q.succ)) (basis e) := by
    funext p
    rw [wRoute_val basis k i e m, vec5]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val = 0 := by
        rw [sigmaDiffA_cast_val]; split_ifs <;> omega
      rw [if_pos hcv, if_pos (Fin.ext h0)]
    · rcases eq_or_ne p.val 1 with h1 | h1
      · have hcv : ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val = 1 := by
          rw [sigmaDiffA_cast_val]; split_ifs <;> omega
        rw [if_neg (by rw [hcv]; omega), if_pos hcv,
          if_neg (Fin.ne_of_val_ne h0), if_pos (Fin.ext h1)]
      · rcases eq_or_ne p.val 2 with h2 | h2
        · have hcv : ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val = 4 := by
            rw [sigmaDiffA_cast_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1), if_pos (Fin.ext h2)]
          congr 2
          have hidx :
              ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val - 4 =
                (0 : Fin (4 + (k + 1))).val := by
            rw [hcv]
            norm_num
          exact Fin.ext hidx
        · rcases eq_or_ne p.val 3 with h3 | h3
          · have hcv : ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val = 5 + q.val := by
              rw [sigmaDiffA_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
              if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_pos (Fin.ext h3)]
            congr 2
            have hidx :
                ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val - 4 = q.succ.val := by
              rw [hcv, Fin.val_succ]
              omega
            exact Fin.ext hidx
          · have hcv : ((sigmaDiffA k q) (Fin.castAdd (4 + k) p)).val = 2 := by
              rw [sigmaDiffA_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos hcv,
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_neg (Fin.ne_of_val_ne h3)]
  have hR :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaDiffA k q) (Fin.natAdd (4 + 1) p)))
        = Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e) := by
    funext p
    rw [wRoute_val basis k i e m, Function.update_apply]
    rcases eq_or_ne p.val q.val with hp | hp
    · have hpq : p = q := Fin.ext hp
      have hcv : ((sigmaDiffA k q) (Fin.natAdd 5 p)).val = 3 := by
        rw [sigmaDiffA_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_pos hcv, if_pos hpq]
    · have hpq : p ≠ q := by
        intro h
        exact hp (by simp [h])
      have hcv : ((sigmaDiffA k q) (Fin.natAdd 5 p)).val = 5 + p.val := by
        rw [sigmaDiffA_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_neg hpq]
      congr 2
      have hidx :
          ((sigmaDiffA k q) (Fin.natAdd (4 + 1) p)).val - 4 = p.succ.val := by
        change ((sigmaDiffA k q) (Fin.natAdd 5 p)).val - 4 = p.succ.val
        rw [hcv, Fin.val_succ]
        omega
      exact Fin.ext hidx
  rw [hL, hR]



def tfDiffB (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 0) + (4 + (k + 1))) + 2 * 0) →
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  fun a =>
    if a.val = 0 then
      ⟨0, by omega⟩
    else if a.val = 1 then
      ⟨4, by omega⟩
    else if a.val = 2 then
      ⟨5 + q.val, by omega⟩
    else if a.val = 3 then
      ⟨2, by omega⟩
    else if a.val = 4 then
      ⟨1, by omega⟩
    else if a.val = 5 + q.val then
      ⟨3, by omega⟩
    else
      ⟨a.val, by omega⟩


def sigmaDiffB (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 0) + (4 + (k + 1))) + 2 * 0) ≃
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  Equiv.ofBijective (tfDiffB k q) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, by simp only [Fintype.card_fin]; omega⟩
    apply Fin.ext
    simp only [tfDiffB] at hab
    split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega)

@[simp]
theorem sigmaDiffB_cast_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + 0)) :
    ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)).val =
      if p.val = 0 then 0
      else if p.val = 1 then 4
      else if p.val = 2 then 5 + q.val
      else 2 := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaDiffB, Equiv.ofBijective_apply, tfDiffB, Fin.val_castAdd]
  split_ifs <;> first | rfl | omega

@[simp]
theorem sigmaDiffB_nat_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + (k + 1))) :
    ((sigmaDiffB k q) (Fin.natAdd (4 + 0) p)).val =
      if p.val = 0 then 1
      else if p.val = q.val + 1 then 3
      else 4 + p.val := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaDiffB, Equiv.ofBijective_apply, tfDiffB, Fin.val_natAdd]
  split_ifs <;> first | rfl | omega

set_option maxHeartbeats 1000000 in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem slotdiffStarB
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (m : Fin (4 + (k + 1)) → Idx) :
    starBaseField (I := I) S t (k + 1) 0 (k + 1) 0 (sigmaDiffB k q) x
        (fun p => basis (m p)) =
      ∑ e : Idx, ∑ i : Idx,
        nablaKRm04Field (I := I) S t 0 x
          (vec4 (I := I) (basis i) (basis (m 0)) (basis (m q.succ)) (basis e)) *
        nablaKRm04Field (I := I) S t (k + 1) x
          (Fin.cons (basis i)
            (Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e))) := by
  rw [starBaseProd_eq (I := I) S t (k + 1) 0 (k + 1) basis horth (sigmaDiffB k q) m]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => ?_
  have hL :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)))
        = vec4 (I := I) (basis i) (basis (m 0)) (basis (m q.succ)) (basis e) := by
    funext p
    rw [wRoute_val basis k i e m, vec4]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)).val = 0 := by
        rw [sigmaDiffB_cast_val]; split_ifs <;> omega
      rw [if_pos hcv, if_pos (Fin.ext h0)]
    · rcases eq_or_ne p.val 1 with h1 | h1
      · have hcv : ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)).val = 4 := by
          rw [sigmaDiffB_cast_val]; split_ifs <;> omega
        rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (Fin.ne_of_val_ne h0), if_pos (Fin.ext h1)]
        congr 2
        have hidx :
            ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)).val - 4 =
              (0 : Fin (4 + (k + 1))).val := by
          rw [hcv]
          norm_num
        exact Fin.ext hidx
      · rcases eq_or_ne p.val 2 with h2 | h2
        · have hcv : ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)).val = 5 + q.val := by
            rw [sigmaDiffB_cast_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1), if_pos (Fin.ext h2)]
          congr 2
          have hidx :
              ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)).val - 4 = q.succ.val := by
            rw [hcv, Fin.val_succ]
            omega
          exact Fin.ext hidx
        · have hcv : ((sigmaDiffB k q) (Fin.castAdd (4 + (k + 1)) p)).val = 2 := by
            rw [sigmaDiffB_cast_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos hcv,
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
            if_neg (Fin.ne_of_val_ne h2)]
  have hR :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaDiffB k q) (Fin.natAdd (4 + 0) p)))
        = Fin.cons (basis i)
            (Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e)) := by
    funext p
    rw [wRoute_val basis k i e m]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hp0 : p = 0 := Fin.ext h0
      have hcv : ((sigmaDiffB k q) (Fin.natAdd 4 p)).val = 1 := by
        rw [sigmaDiffB_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_pos hcv, hp0]
      simp
    · rcases eq_or_ne p.val (q.val + 1) with hq | hq
      · have hpq : p = q.succ := by
          ext
          simpa [Fin.val_succ] using hq
        have hcv : ((sigmaDiffB k q) (Fin.natAdd 4 p)).val = 3 := by
          rw [sigmaDiffB_nat_val]; split_ifs <;> omega
        rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (by rw [hcv]; omega), if_pos hcv, hpq]
        simp
      · have hp0 : p ≠ 0 := by
          intro hp
          exact h0 (by simp [hp])
        have hpred : p.pred hp0 ≠ q := by
          intro h
          apply hq
          calc
            p.val = (p.pred hp0).succ.val := by rw [Fin.succ_pred]
            _ = q.val + 1 := by simp [h, Fin.val_succ]
        have hcv : ((sigmaDiffB k q) (Fin.natAdd 4 p)).val = 4 + p.val := by
          rw [sigmaDiffB_nat_val]; split_ifs <;> omega
        have hrhs :
            (@Fin.cons (4 + k) (fun _ => TangentSpace I x) (basis i)
                (Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e))) p =
              basis (m p) := by
          conv_lhs => rw [← Fin.succ_pred p hp0]
          rw [Fin.cons_succ, Function.update_apply, if_neg hpred, Fin.succ_pred]
        rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
          if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), hrhs]
        congr 2
        have hidx :
            ((sigmaDiffB k q) (Fin.natAdd (4 + 0) p)).val - 4 = p.val := by
          change ((sigmaDiffB k q) (Fin.natAdd 4 p)).val - 4 = p.val
          rw [hcv]
          omega
        exact Fin.ext hidx
  rw [hL, hR]












def tfRic1 (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) →
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  fun a =>
    if a.val = 0 then ⟨4, by omega⟩
    else if a.val = 1 then ⟨0, by omega⟩
    else if a.val = 2 then ⟨5 + q.val, by omega⟩
    else if a.val = 3 then ⟨2, by omega⟩
    else if a.val = 4 then ⟨1, by omega⟩
    else if a.val = 5 + q.val then ⟨3, by omega⟩
    else ⟨a.val, by omega⟩


def sigmaRic1 (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) ≃
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  Equiv.ofBijective (tfRic1 k q) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, by simp only [Fintype.card_fin]; omega⟩
    apply Fin.ext
    simp only [tfRic1] at hab
    split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega)

@[simp]
theorem sigmaRic1_cast_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + 1)) :
    ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val =
      if p.val = 0 then 4
      else if p.val = 1 then 0
      else if p.val = 2 then 5 + q.val
      else if p.val = 3 then 2
      else 1 := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaRic1, Equiv.ofBijective_apply, tfRic1, Fin.val_castAdd]
  split_ifs <;> first | rfl | omega

@[simp]
theorem sigmaRic1_nat_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + k)) :
    ((sigmaRic1 k q) (Fin.natAdd (4 + 1) p)).val =
      if p.val = q.val then 3 else 5 + p.val := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaRic1, Equiv.ofBijective_apply, tfRic1, Fin.val_natAdd]
  split_ifs <;> first | rfl | omega

set_option maxHeartbeats 1000000 in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem slotRic1
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (m : Fin (4 + (k + 1)) → Idx) :
    starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic1 k q) x
        (fun p => basis (m p)) =
      ∑ e : Idx, ∑ i : Idx,
        nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) (basis (m 0)) (basis i) (basis (m q.succ)) (basis e) (basis i)) *
        nablaKRm04Field (I := I) S t k x
          (Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e)) := by
  rw [starBaseProd_eq (I := I) S t (k + 1) 1 k basis horth (sigmaRic1 k q) m]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => ?_
  have hL :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)))
        = vec5 (I := I) (basis (m 0)) (basis i) (basis (m q.succ)) (basis e) (basis i) := by
    funext p
    rw [wRoute_val basis k i e m, vec5]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val = 4 := by
        rw [sigmaRic1_cast_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos (Fin.ext h0)]
      congr 2
      have hidx :
          ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val - 4 =
            (0 : Fin (4 + (k + 1))).val := by
        rw [hcv]; norm_num
      exact Fin.ext hidx
    · rcases eq_or_ne p.val 1 with h1 | h1
      · have hcv : ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val = 0 := by
          rw [sigmaRic1_cast_val]; split_ifs <;> omega
        rw [if_pos hcv, if_neg (Fin.ne_of_val_ne h0), if_pos (Fin.ext h1)]
      · rcases eq_or_ne p.val 2 with h2 | h2
        · have hcv : ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val = 5 + q.val := by
            rw [sigmaRic1_cast_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1), if_pos (Fin.ext h2)]
          congr 2
          have hidx :
              ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val - 4 = q.succ.val := by
            rw [hcv, Fin.val_succ]; omega
          exact Fin.ext hidx
        · rcases eq_or_ne p.val 3 with h3 | h3
          · have hcv : ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val = 2 := by
              rw [sigmaRic1_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos hcv,
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_pos (Fin.ext h3)]
          · have hcv : ((sigmaRic1 k q) (Fin.castAdd (4 + k) p)).val = 1 := by
              rw [sigmaRic1_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_pos hcv,
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_neg (Fin.ne_of_val_ne h3)]
  have hR :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaRic1 k q) (Fin.natAdd (4 + 1) p)))
        = Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e) := by
    funext p
    rw [wRoute_val basis k i e m, Function.update_apply]
    rcases eq_or_ne p.val q.val with hp | hp
    · have hpq : p = q := Fin.ext hp
      have hcv : ((sigmaRic1 k q) (Fin.natAdd 5 p)).val = 3 := by
        rw [sigmaRic1_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_pos hcv, if_pos hpq]
    · have hpq : p ≠ q := by
        intro h
        exact hp (by simp [h])
      have hcv : ((sigmaRic1 k q) (Fin.natAdd 5 p)).val = 5 + p.val := by
        rw [sigmaRic1_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_neg hpq]
      congr 2
      have hidx :
          ((sigmaRic1 k q) (Fin.natAdd (4 + 1) p)).val - 4 = p.succ.val := by
        change ((sigmaRic1 k q) (Fin.natAdd 5 p)).val - 4 = p.succ.val
        rw [hcv, Fin.val_succ]; omega
      exact Fin.ext hidx
  rw [hL, hR]


def tfRic2 (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) →
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  fun a =>
    if a.val = 0 then ⟨5 + q.val, by omega⟩
    else if a.val = 1 then ⟨0, by omega⟩
    else if a.val = 2 then ⟨4, by omega⟩
    else if a.val = 3 then ⟨2, by omega⟩
    else if a.val = 4 then ⟨1, by omega⟩
    else if a.val = 5 + q.val then ⟨3, by omega⟩
    else ⟨a.val, by omega⟩


def sigmaRic2 (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) ≃
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  Equiv.ofBijective (tfRic2 k q) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, by simp only [Fintype.card_fin]; omega⟩
    apply Fin.ext
    simp only [tfRic2] at hab
    split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega)

@[simp]
theorem sigmaRic2_cast_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + 1)) :
    ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val =
      if p.val = 0 then 5 + q.val
      else if p.val = 1 then 0
      else if p.val = 2 then 4
      else if p.val = 3 then 2
      else 1 := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaRic2, Equiv.ofBijective_apply, tfRic2, Fin.val_castAdd]
  split_ifs <;> first | rfl | omega

@[simp]
theorem sigmaRic2_nat_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + k)) :
    ((sigmaRic2 k q) (Fin.natAdd (4 + 1) p)).val =
      if p.val = q.val then 3 else 5 + p.val := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaRic2, Equiv.ofBijective_apply, tfRic2, Fin.val_natAdd]
  split_ifs <;> first | rfl | omega

set_option maxHeartbeats 1000000 in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem slotRic2
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (m : Fin (4 + (k + 1)) → Idx) :
    starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic2 k q) x
        (fun p => basis (m p)) =
      ∑ e : Idx, ∑ i : Idx,
        nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) (basis (m q.succ)) (basis i) (basis (m 0)) (basis e) (basis i)) *
        nablaKRm04Field (I := I) S t k x
          (Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e)) := by
  rw [starBaseProd_eq (I := I) S t (k + 1) 1 k basis horth (sigmaRic2 k q) m]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => ?_
  have hL :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)))
        = vec5 (I := I) (basis (m q.succ)) (basis i) (basis (m 0)) (basis e) (basis i) := by
    funext p
    rw [wRoute_val basis k i e m, vec5]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val = 5 + q.val := by
        rw [sigmaRic2_cast_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos (Fin.ext h0)]
      congr 2
      have hidx :
          ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val - 4 = q.succ.val := by
        rw [hcv, Fin.val_succ]; omega
      exact Fin.ext hidx
    · rcases eq_or_ne p.val 1 with h1 | h1
      · have hcv : ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val = 0 := by
          rw [sigmaRic2_cast_val]; split_ifs <;> omega
        rw [if_pos hcv, if_neg (Fin.ne_of_val_ne h0), if_pos (Fin.ext h1)]
      · rcases eq_or_ne p.val 2 with h2 | h2
        · have hcv : ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val = 4 := by
            rw [sigmaRic2_cast_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1), if_pos (Fin.ext h2)]
          congr 2
          have hidx :
              ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val - 4 =
                (0 : Fin (4 + (k + 1))).val := by
            rw [hcv]; norm_num
          exact Fin.ext hidx
        · rcases eq_or_ne p.val 3 with h3 | h3
          · have hcv : ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val = 2 := by
              rw [sigmaRic2_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos hcv,
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_pos (Fin.ext h3)]
          · have hcv : ((sigmaRic2 k q) (Fin.castAdd (4 + k) p)).val = 1 := by
              rw [sigmaRic2_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_pos hcv,
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_neg (Fin.ne_of_val_ne h3)]
  have hR :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaRic2 k q) (Fin.natAdd (4 + 1) p)))
        = Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e) := by
    funext p
    rw [wRoute_val basis k i e m, Function.update_apply]
    rcases eq_or_ne p.val q.val with hp | hp
    · have hpq : p = q := Fin.ext hp
      have hcv : ((sigmaRic2 k q) (Fin.natAdd 5 p)).val = 3 := by
        rw [sigmaRic2_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_pos hcv, if_pos hpq]
    · have hpq : p ≠ q := by
        intro h
        exact hp (by simp [h])
      have hcv : ((sigmaRic2 k q) (Fin.natAdd 5 p)).val = 5 + p.val := by
        rw [sigmaRic2_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_neg hpq]
      congr 2
      have hidx :
          ((sigmaRic2 k q) (Fin.natAdd (4 + 1) p)).val - 4 = p.succ.val := by
        change ((sigmaRic2 k q) (Fin.natAdd 5 p)).val - 4 = p.succ.val
        rw [hcv, Fin.val_succ]; omega
      exact Fin.ext hidx
  rw [hL, hR]


def tfRic3 (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) →
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  fun a =>
    if a.val = 0 then ⟨2, by omega⟩
    else if a.val = 1 then ⟨0, by omega⟩
    else if a.val = 2 then ⟨4, by omega⟩
    else if a.val = 3 then ⟨5 + q.val, by omega⟩
    else if a.val = 4 then ⟨1, by omega⟩
    else if a.val = 5 + q.val then ⟨3, by omega⟩
    else ⟨a.val, by omega⟩


def sigmaRic3 (k : ℕ) (q : Fin (4 + k)) :
    Fin (((4 + 1) + (4 + k)) + 2 * 0) ≃
      Fin ((4 + (k + 1)) + 2 * (2 + 0)) :=
  Equiv.ofBijective (tfRic3 k q) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, by simp only [Fintype.card_fin]; omega⟩
    apply Fin.ext
    simp only [tfRic3] at hab
    split_ifs at hab <;> (try simp only [Fin.mk.injEq] at hab) <;> omega)

@[simp]
theorem sigmaRic3_cast_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + 1)) :
    ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val =
      if p.val = 0 then 2
      else if p.val = 1 then 0
      else if p.val = 2 then 4
      else if p.val = 3 then 5 + q.val
      else 1 := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaRic3, Equiv.ofBijective_apply, tfRic3, Fin.val_castAdd]
  split_ifs <;> first | rfl | omega

@[simp]
theorem sigmaRic3_nat_val (k : ℕ) (q : Fin (4 + k)) (p : Fin (4 + k)) :
    ((sigmaRic3 k q) (Fin.natAdd (4 + 1) p)).val =
      if p.val = q.val then 3 else 5 + p.val := by
  have hplt := p.isLt
  have hqlt := q.isLt
  simp only [sigmaRic3, Equiv.ofBijective_apply, tfRic3, Fin.val_natAdd]
  split_ifs <;> first | rfl | omega

set_option maxHeartbeats 1000000 in

omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem slotRic3
    [Module.Finite ℝ E]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) (q : Fin (4 + k))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx, (S.family.metric t).inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (m : Fin (4 + (k + 1)) → Idx) :
    starBaseField (I := I) S t (k + 1) 1 k 0 (sigmaRic3 k q) x
        (fun p => basis (m p)) =
      ∑ e : Idx, ∑ i : Idx,
        nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) (basis e) (basis i) (basis (m 0)) (basis (m q.succ)) (basis i)) *
        nablaKRm04Field (I := I) S t k x
          (Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e)) := by
  rw [starBaseProd_eq (I := I) S t (k + 1) 1 k basis horth (sigmaRic3 k q) m]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => ?_
  have hL :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)))
        = vec5 (I := I) (basis e) (basis i) (basis (m 0)) (basis (m q.succ)) (basis i) := by
    funext p
    rw [wRoute_val basis k i e m, vec5]
    rcases eq_or_ne p.val 0 with h0 | h0
    · have hcv : ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val = 2 := by
        rw [sigmaRic3_cast_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_pos hcv,
        if_pos (Fin.ext h0)]
    · rcases eq_or_ne p.val 1 with h1 | h1
      · have hcv : ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val = 0 := by
          rw [sigmaRic3_cast_val]; split_ifs <;> omega
        rw [if_pos hcv, if_neg (Fin.ne_of_val_ne h0), if_pos (Fin.ext h1)]
      · rcases eq_or_ne p.val 2 with h2 | h2
        · have hcv : ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val = 4 := by
            rw [sigmaRic3_cast_val]; split_ifs <;> omega
          rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
            if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1), if_pos (Fin.ext h2)]
          congr 2
          have hidx :
              ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val - 4 =
                (0 : Fin (4 + (k + 1))).val := by
            rw [hcv]; norm_num
          exact Fin.ext hidx
        · rcases eq_or_ne p.val 3 with h3 | h3
          · have hcv : ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val = 5 + q.val := by
              rw [sigmaRic3_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
              if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_pos (Fin.ext h3)]
            congr 2
            have hidx :
                ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val - 4 = q.succ.val := by
              rw [hcv, Fin.val_succ]; omega
            exact Fin.ext hidx
          · have hcv : ((sigmaRic3 k q) (Fin.castAdd (4 + k) p)).val = 1 := by
              rw [sigmaRic3_cast_val]; split_ifs <;> omega
            rw [if_neg (by rw [hcv]; omega), if_pos hcv,
              if_neg (Fin.ne_of_val_ne h0), if_neg (Fin.ne_of_val_ne h1),
              if_neg (Fin.ne_of_val_ne h2), if_neg (Fin.ne_of_val_ne h3)]
  have hR :
      (fun p => metricTraceInput (I := I) (basis i) (basis i)
        (metricTraceInput (I := I) (basis e) (basis e) (fun p => basis (m p)))
        ((sigmaRic3 k q) (Fin.natAdd (4 + 1) p)))
        = Function.update (fun p : Fin (4 + k) => basis (m p.succ)) q (basis e) := by
    funext p
    rw [wRoute_val basis k i e m, Function.update_apply]
    rcases eq_or_ne p.val q.val with hp | hp
    · have hpq : p = q := Fin.ext hp
      have hcv : ((sigmaRic3 k q) (Fin.natAdd 5 p)).val = 3 := by
        rw [sigmaRic3_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_pos hcv, if_pos hpq]
    · have hpq : p ≠ q := by
        intro h
        exact hp (by simp [h])
      have hcv : ((sigmaRic3 k q) (Fin.natAdd 5 p)).val = 5 + p.val := by
        rw [sigmaRic3_nat_val]; split_ifs <;> omega
      rw [if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega),
        if_neg (by rw [hcv]; omega), if_neg (by rw [hcv]; omega), if_neg hpq]
      congr 2
      have hidx :
          ((sigmaRic3 k q) (Fin.natAdd (4 + 1) p)).val - 4 = p.succ.val := by
        change ((sigmaRic3 k q) (Fin.natAdd 5 p)).val - 4 = p.succ.val
        rw [hcv, Fin.val_succ]; omega
      exact Fin.ext hidx
  rw [hL, hR]

end DifferentialGeometry.PDE.RicciFlow
