import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutator

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false




























































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]



private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace Real (Tensor0SModel s Real E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s Real E) := inferInstance











def nabla3SlotFields
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 6 → (x : M) → TangentSpace I x :=
  Fin.cons (frame d₁) (Fin.cons (frame d₂) (fun q : Fin 4 => frame (m q)))




omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nabla3SlotFields_swap
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3SlotFields (I := I) frame d₂ d₁ m =
      fun q : Fin 6 => nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 q) := by
  funext q
  refine Fin.cases ?_ (fun q => ?_) q
  · change nabla3SlotFields (I := I) frame d₂ d₁ m 0 =
      nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 0)
    rw [Equiv.swap_apply_left]; rfl
  · refine Fin.cases ?_ (fun q => ?_) q
    · change nabla3SlotFields (I := I) frame d₂ d₁ m 1 =
        nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 1)
      rw [Equiv.swap_apply_right]; rfl
    · have hne0 : Fin.succ (Fin.succ q) ≠ (0 : Fin 6) := Fin.succ_ne_zero _
      have hne1 : Fin.succ (Fin.succ q) ≠ (1 : Fin 6) := by
        rw [show (1 : Fin 6) = Fin.succ 0 from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      change nabla3SlotFields (I := I) frame d₂ d₁ m (Fin.succ (Fin.succ q)) =
        nabla3SlotFields (I := I) frame d₁ d₂ m (Equiv.swap (0 : Fin 6) 1 (Fin.succ (Fin.succ q)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]; rfl



omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nabla3FrameTuple_eq_cons_slotFields
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (a d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3FrameTuple (I := I) frame x a d₁ d₂ m =
      Fin.cons (frame a x)
        (fun q : Fin 6 => nabla3SlotFields (I := I) frame d₁ d₂ m q x) := by
  funext q
  refine Fin.cases ?_ (fun q => ?_) q
  · rfl
  ·
    simp only [nabla3FrameTuple, nabla3InnerSlots, metricTraceInput, nabla3SlotFields,
      Fin.cons_succ]
    refine Fin.cases ?_ (fun q => ?_) q
    · rfl
    · refine Fin.cases ?_ (fun q => ?_) q
      · rfl
      · rfl



omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nabla3InnerSlots_eq_tail_slotFields
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3InnerSlots (I := I) frame x d₂ m =
      fun q : Fin 5 =>
        (Fin.tail (fun r : Fin 6 => nabla3SlotFields (I := I) frame d₁ d₂ m r x)) q := by
  funext q
  simp only [nabla3InnerSlots, nabla3SlotFields, Fin.tail]
  refine Fin.cases ?_ (fun q => ?_) q
  · rfl
  · rfl














omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla3Rm04Field_eval_expand
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a d₁ d₂ m) =
      extDerivFun (I := I)
          (fun p : M =>
            nabla2Rm04Field (I := I) S t p
              (fun q : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m q p))
          x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
        ∑ q : Fin 6,
          nabla2Rm04Field (I := I) S t x₀
            (Function.update
              (fun r : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m r x₀) q
              ((S.family.connection t
                  (nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m q) x₀)
                (coordinateFrameAt (I := I) x₀ a x₀))) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set V : Fin 6 → (x : M) → TangentSpace I x :=
    nabla3SlotFields (I := I) frame d₁ d₂ m with hV_def

  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x₀ (frame a x₀)

  have hV_at : ∀ q : Fin 6,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
    intro q

    have hbase : ∀ i : CoordinateIdx (𝕜 := Real) E,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun y : M => (⟨y, frame i y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ :=
      fun i =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) i

    refine Fin.cases ?_ (fun q => ?_) q
    · simpa [hV_def, nabla3SlotFields] using hbase d₁
    · refine Fin.cases ?_ (fun q => ?_) q
      · simpa [hV_def, nabla3SlotFields] using hbase d₂
      · simpa [hV_def, nabla3SlotFields] using hbase (m q)

  have heval :=
    (nabla3Rm04Field_realizes (I := I) S t).eval_C1_slots X V x₀ hV_at

  rw [nabla3FrameTuple_eq_cons_slotFields (I := I) frame x₀ a d₁ d₂ m]
  rw [hX] at heval
  exact heval











omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem nabla3SlotFields_eq_metricTraceInput
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    (fun q : Fin 6 => nabla3SlotFields (I := I) frame b c m q x) =
      metricTraceInput (I := I) (frame b x) (frame c x)
        (frameTuple (I := I) frame x m) := by
  funext q
  simp only [nabla3SlotFields, metricTraceInput]
  refine Fin.cases ?_ (fun q => ?_) q
  · rfl
  · refine Fin.cases ?_ (fun q => ?_) q
    · rfl
    · rfl





omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla2Rm04Field_antisym_eq_curvatureAction_field
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    (fun p : M =>
        nabla2Rm04Field (I := I) S (t : Real) p
            (fun q : Fin 6 =>
              nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) b c m q p) -
          nabla2Rm04Field (I := I) S (t : Real) p
            (fun q : Fin 6 =>
              nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) c b m q p)) =
      fun p : M =>
        curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
          (S.base.rm04 (t : Real) p)
          (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
          (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m) := by
  funext p
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def

  have hR := rm04_ricciIdentityAt (I := I) S hS t p
    (frame b p) (frame c p) (frameTuple (I := I) frame p m)
  rw [nabla3SlotFields_eq_metricTraceInput (I := I) frame p b c m,
    nabla3SlotFields_eq_metricTraceInput (I := I) frame p c b m]
  exact hR








omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem fin6_eq_metricTraceInput {x : M} (W : Fin 6 → TangentSpace I x) :
    W =
      metricTraceInput (I := I) (W 0) (W 1)
        (fun q : Fin 4 => W (Fin.succ (Fin.succ q))) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem fin6_comp_swap_eq_metricTraceInput {x : M} (W : Fin 6 → TangentSpace I x) :
    W ∘ Equiv.swap (0 : Fin 6) 1 =
      metricTraceInput (I := I) (W 1) (W 0)
        (fun q : Fin 4 => W (Fin.succ (Fin.succ q))) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change W (Equiv.swap (0 : Fin 6) 1 0) = _
    rw [Equiv.swap_apply_left]; rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · change W (Equiv.swap (0 : Fin 6) 1 1) = _
      rw [Equiv.swap_apply_right]; rfl
    ·
      have hne0 : Fin.succ (Fin.succ j) ≠ (0 : Fin 6) := Fin.succ_ne_zero _
      have hne1 : Fin.succ (Fin.succ j) ≠ (1 : Fin 6) := by
        rw [show (1 : Fin 6) = Fin.succ 0 from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      change W (Equiv.swap (0 : Fin 6) 1 (Fin.succ (Fin.succ j))) = _
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]; rfl





omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla2Rm04Field_slot01_antisym
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) (W : Fin 6 → TangentSpace I x₀) :
    nabla2Rm04Field (I := I) S (t : Real) x₀ W -
        nabla2Rm04Field (I := I) S (t : Real) x₀ (W ∘ Equiv.swap (0 : Fin 6) 1) =
      curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
        (W 0) (W 1) (fun q : Fin 4 => W (Fin.succ (Fin.succ q))) := by
  have hR := rm04_ricciIdentityAt (I := I) S hS t x₀
    (W 0) (W 1) (fun q : Fin 4 => W (Fin.succ (Fin.succ q)))
  rw [← fin6_eq_metricTraceInput (I := I) W,
    ← fin6_comp_swap_eq_metricTraceInput (I := I) W] at hR
  exact hR










omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla2Rm04Field_slotFields_mdifferentiableAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M =>
        nabla2Rm04Field (I := I) S t p
          (fun q : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) d₁ d₂ m q p))
      x₀ := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def
  set V : Fin 6 → (x : M) → TangentSpace I x :=
    nabla3SlotFields (I := I) frame d₁ d₂ m with hV_def

  have hV_at : ∀ q : Fin 6,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
    intro q
    have hbase : ∀ i : CoordinateIdx (𝕜 := Real) E,
        ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame i y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ :=
      fun i =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) i
    refine Fin.cases ?_ (fun q => ?_) q
    · simpa [hV_def, nabla3SlotFields] using hbase d₁
    · refine Fin.cases ?_ (fun q => ?_) q
      · simpa [hV_def, nabla3SlotFields] using hbase d₂
      · simpa [hV_def, nabla3SlotFields] using hbase (m q)

  exact tensor0SField_eval_C1_slots_mdiffAt
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (nabla2Rm04Field (I := I) S t) V x₀ hV_at














omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem correction_sum_swap_reindex {x₀ : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 6 x₀)
    (S : Fin 6 → TangentSpace I x₀) (D : Fin 6 → TangentSpace I x₀) :
    (∑ q : Fin 6,
        α (Function.update (fun r : Fin 6 => S (Equiv.swap (0 : Fin 6) 1 r)) q
          (D (Equiv.swap (0 : Fin 6) 1 q)))) =
      ∑ q : Fin 6,
        α (Function.update S q (D q) ∘ Equiv.swap (0 : Fin 6) 1) := by
  classical
  set σ : Equiv.Perm (Fin 6) := Equiv.swap (0 : Fin 6) 1 with hσ

  rw [← Equiv.sum_comp σ
        (fun q : Fin 6 =>
          α (Function.update (fun r : Fin 6 => S (σ r)) q (D (σ q))))]
  refine Finset.sum_congr rfl fun q _ => ?_

  have hσσ : σ (σ q) = q := by rw [hσ]; exact Equiv.swap_apply_self _ _ q
  rw [hσσ]

  congr 1
  have hinj : Function.Injective σ := σ.injective
  have hupd :
      Function.update S (σ (σ q)) (D q) ∘ σ =
        Function.update (S ∘ σ) (σ q) (D q) :=
    Function.update_comp_eq_of_injective S hinj (σ q) (D q)
  rw [hσσ] at hupd
  exact hupd.symm













def nabla3CorrectedSlots
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E)
    (q : Fin 6) : Fin 6 → TangentSpace I x₀ :=
  Function.update
    (fun r : Fin 6 => nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) b c m r x₀) q
    ((S.family.connection t
        (nabla3SlotFields (I := I) (coordinateFrameAt (I := I) x₀) b c m q) x₀)
      (coordinateFrameAt (I := I) x₀ a x₀))















omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_T1_eq_covDeriv_curvatureAction
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) =
      extDerivFun (I := I)
          (fun p : M =>
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (S.base.rm04 (t : Real) p)
              (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
              (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m))
          x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
        ∑ q : Fin 6,
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 0)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 1)
            (fun r : Fin 4 =>
              nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q (Fin.succ (Fin.succ r))) := by
  classical
  set frame := coordinateFrameAt (I := I) x₀ with hframe_def

  set Sbc : Fin 6 → TangentSpace I x₀ :=
    fun r : Fin 6 => nabla3SlotFields (I := I) frame b c m r x₀ with hSbc_def

  rw [nabla3Rm04Field_eval_expand (I := I) S (t : Real) x₀ a b c m,
    nabla3Rm04Field_eval_expand (I := I) S (t : Real) x₀ a c b m]

  rw [show
    ∀ Ebc Ecb Cbc Ccb : Real, (Ebc - Cbc) - (Ecb - Ccb) = (Ebc - Ecb) - (Cbc - Ccb)
    from fun _ _ _ _ => by ring]
  congr 1
  ·
    rw [← extDerivFun_sub_at (I := I) (frame a x₀)
      (nabla2Rm04Field_slotFields_mdifferentiableAt (I := I) S (t : Real) x₀ b c m)
      (nabla2Rm04Field_slotFields_mdifferentiableAt (I := I) S (t : Real) x₀ c b m)]

    rw [nabla2Rm04Field_antisym_eq_curvatureAction_field (I := I) S hS t x₀ b c m]
  ·



    have hStep1 :
        (∑ q : Fin 6,
            nabla2Rm04Field (I := I) S (t : Real) x₀
              (Function.update
                (fun r : Fin 6 => nabla3SlotFields (I := I) frame c b m r x₀) q
                ((S.family.connection (t : Real)
                    (nabla3SlotFields (I := I) frame c b m q) x₀) (frame a x₀)))) =
          ∑ q : Fin 6,
            nabla2Rm04Field (I := I) S (t : Real) x₀
              (Function.update (fun r : Fin 6 => Sbc (Equiv.swap (0 : Fin 6) 1 r)) q
                ((S.family.connection (t : Real)
                    (nabla3SlotFields (I := I) frame b c m (Equiv.swap (0 : Fin 6) 1 q)) x₀)
                  (frame a x₀))) := by
      simp only [nabla3SlotFields_swap (I := I) frame b c m, hSbc_def]

    rw [hStep1, correction_sum_swap_reindex (I := I)
      (nabla2Rm04Field (I := I) S (t : Real) x₀) Sbc
      (fun q : Fin 6 =>
        (S.family.connection (t : Real)
          (nabla3SlotFields (I := I) frame b c m q) x₀) (frame a x₀))]

    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_

    have hW := nabla2Rm04Field_slot01_antisym (I := I) S hS t x₀
      (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q)
    simp only [nabla3CorrectedSlots, hframe_def, hSbc_def] at hW ⊢
    exact hW
































omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapCommReactionTerm_eq_covDeriv_curvatureAction_add_curvatureAction
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m =
      (extDerivFun (I := I)
            (fun p : M =>
              curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
                (S.base.rm04 (t : Real) p)
                (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
                (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m))
            x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
          ∑ q : Fin 6,
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
              (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 0)
              (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 1)
              (fun r : Fin 4 =>
                nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q (Fin.succ (Fin.succ r)))) +
        curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
          (nablaRm04Field (I := I) S (t : Real) x₀)
          (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
          (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) := by
  rw [nablaLapCommReactionTerm]
  rw [nablaLapComm_T1_eq_covDeriv_curvatureAction (I := I) S hS t x₀ a b c m]

















































































































































end DifferentialGeometry.PDE.RicciFlow
