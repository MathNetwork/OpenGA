import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Lemma45Engine

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false







































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]










omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem claim1_LC {u : Set M} (hu : IsOpen u)
    (gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hframeS : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y d i j) u)
    (C0 K : Real) (m : ℕ) :
    ∃ C, 0 ≤ C ∧
      ∀ (g : SmoothRiemannianMetric I M),
        (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun y => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
            frame hframe y d i j) u) →
        (∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun y => frameComp0S (I := I) (metricTensorField (I := I) g) frame y k) u) →
      ∀ (Ginv : M → (Fin (1 + 1) → Idx) → Real),
        (∀ x ∈ u, ∀ c e : Idx,
          (∑ l : Idx, frameComp0S (I := I) (metricTensorField (I := I) g) frame x
              (Fin.snoc (fun _ : Fin 1 => l) c) *
            Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0) →
        (∀ x ∈ u, compL2 (Ginv x) ≤ C0) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m →
          compL2 (iterCovComp (I := I) frame
            (fun z => christoffelSymbolInFrame
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
              frame hframe z)
            (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j x) ≤ K) →
        ∀ x ∈ u,
      compL2 (iterCovCompU (I := I) frame
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe z)
        (chrDiffField
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
            frame hframe z)
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z)) m x) ≤
        C * (1 + compL2 (iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z)
          (frameComp0S (I := I) (metricTensorField (I := I) g) frame) (m + 1) x)) := by
  classical
  obtain ⟨C, hC0, hCb⟩ := claim1 hu frame
    (fun z => christoffelSymbolInFrame
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
      frame hframe z) hframeS hchrH
    (1 / 2) (1 / 2) (-(1 / 2))
    (Equiv.refl (Fin 3)) (Equiv.swap (0 : Fin 3) 1) ((finRotate 3).symm)
    C0 K m
  refine ⟨C, hC0, ?_⟩
  intro g hchrG hgsm Ginv hinv hGinv hK
  have hDsm : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => chrDiffField
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
          frame hframe z)
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe z) y k) u :=
    fun k => (hchrG _ _ _).sub (hchrH _ _ _)
  exact hCb (frameComp0S (I := I) (metricTensorField (I := I) g) frame) hgsm Ginv
    (chrDiffField
      (fun z => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
        frame hframe z)
      (fun z => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe z)) hDsm hinv
    (fun y hy => hkoszul_of_leviCivita hu g gRef frame hframe y hy)
    hGinv hK






omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem contMDiffOn_finsetSum' {ι : Type*} {u : Set M} (t : Finset ι)
    (f : ι → M → Real) (hf : ∀ i ∈ t, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f i y) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ t, f i y) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (contMDiffOn_const : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun _ => (0 : Real)) u)
  | insert a t ha ih =>
    rw [show (fun y => ∑ i ∈ insert a t, f i y) = fun y => f a y + ∑ i ∈ t, f i y from by
      funext y; rw [Finset.sum_insert ha]]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

omit [DecidableEq Idx] in
private theorem compL2_finsetSum_le {ι : Type*} {r : ℕ} (t : Finset ι)
    (f : ι → (Fin r → Idx) → Real) :
    compL2 (fun n : Fin r → Idx => ∑ i ∈ t, f i n) ≤ ∑ i ∈ t, compL2 (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : compL2 (fun _ : Fin r → Idx => (0 : Real)) = 0 := by
      simp [compL2, compL2Sq]
    exact le_of_eq h0
  | insert b t hb ih =>
    have hrw : (fun n : Fin r → Idx => ∑ i ∈ insert b t, f i n) =
        fun n => f b n + ∑ i ∈ t, f i n := by
      funext n; rw [Finset.sum_insert hb]
    rw [hrw, Finset.sum_insert hb]
    exact le_trans (compL2_add_le _ _) (by linarith [ih])








omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem mixed_oneStep_rev {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrG chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (X : M → (Fin r → Idx) → Real)
    (hX : ∀ k : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => X y k) u)
    (B : ℕ → Real) (hB : ∀ i : ℕ, 0 ≤ B i) (eps : Real) (heps0 : 0 ≤ eps)
    (k : ℕ)
    (hDbound : ∀ c : ℕ, c ≤ k → ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c * eps)
    {x : M} (hx : x ∈ u) :
    compL2 (iterCovComp (I := I) frame chrH X (k + 1) x) ≤
      compL2 (iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
        eps * oneStepConst B k r *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH X j x) := by
  classical
  set D : M → Idx → Idx → Idx → Real := fun z d b p => chrG z d b p - chrH z d b p with hDdef
  have hDsm : ∀ d b p : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => D y d b p) u :=
    fun d b p => (hchrG d b p).sub (hchrH d b p)

  have hsplit : (fun y => iterCovComp (I := I) frame chrG X 1 y) =
      fun z (n : Fin (r + 1) → Idx) =>
        iterCovComp (I := I) frame chrH X 1 z n -
          ∑ s : Fin r, chrCorrField D X s z n := by
    funext z n
    exact iterCov_one_chr_change frame chrG chrH X z n
  have hHstep_sm : ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chrH X 1 y m) u :=
    fun m => iterCovComp_contMDiffOn hu frame chrH X hframe hchrH hX 1 m
  have hcorr_sm : ∀ s : Fin r, ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrCorrField D X s y m) u :=
    fun s m => contMDiffOn_chrCorrField D hDsm X hX s m
  have hcorrSum_sm : ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ s : Fin r, chrCorrField D X s y m) u :=
    fun m => contMDiffOn_finsetSum' Finset.univ _ (fun s _ => hcorr_sm s m)

  have htri : compL2 (iterCovComp (I := I) frame chrH
      (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) ≤
      compL2 (iterCovComp (I := I) frame chrH
        (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
      ∑ s : Fin r, compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) := by
    have harr' : iterCovComp (I := I) frame chrH
        (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x =
        fun n => iterCovComp (I := I) frame chrH
            (fun y => iterCovComp (I := I) frame chrG X 1 y) k x n +
          ∑ s : Fin r, iterCovComp (I := I) frame chrH (chrCorrField D X s) k x n := by
      funext n
      show iterCovComp (I := I) frame chrH
          (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x n =
        iterCovComp (I := I) frame chrH
            (fun y => iterCovComp (I := I) frame chrG X 1 y) k x n +
          ∑ s : Fin r, iterCovComp (I := I) frame chrH (chrCorrField D X s) k x n

      have h : iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x n =
          iterCovComp (I := I) frame chrH
            (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x n -
          ∑ s : Fin r, iterCovComp (I := I) frame chrH (chrCorrField D X s) k x n := by
        rw [hsplit,
          iterCovComp_sub hu frame chrH
            (fun z m => iterCovComp (I := I) frame chrH X 1 z m)
            (fun z m => ∑ s : Fin r, chrCorrField D X s z m)
            hframe hchrH hHstep_sm hcorrSum_sm k x hx n,
          iterCovComp_finsetSum hu frame chrH hframe hchrH Finset.univ
            (fun s => chrCorrField D X s) (fun s _ m => hcorr_sm s m) k x hx n]
      linarith
    rw [harr']
    refine le_trans (compL2_add_le _ _) ?_
    have hsum := compL2_finsetSum_le (Finset.univ : Finset (Fin r))
      (fun s => iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)
    linarith

  have hshift : compL2 (iterCovComp (I := I) frame chrH X (k + 1) x) =
      compL2 (iterCovComp (I := I) frame chrH
        (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) :=
    compL2_iterCovComp_shift frame chrH X k x

  have hXsum0 : (0 : Real) ≤ ∑ j ∈ Finset.range (k + 1),
      compL2 (iterCovComp (I := I) frame chrH X j x) :=
    Finset.sum_nonneg fun j _ => compL2_nonneg _
  have hcorrBound : (∑ s : Fin r,
      compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)) ≤
      eps * oneStepConst B k r *
        ∑ j ∈ Finset.range (k + 1),
          compL2 (iterCovComp (I := I) frame chrH X j x) := by
    cases r with
    | zero =>
      rw [show (∑ s : Fin 0,
          compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)) = 0 from
        Finset.sum_of_isEmpty _]
      have h0 : oneStepConst B k 0 = 0 := by
        rw [oneStepConst]
        norm_num
      rw [h0, mul_zero, zero_mul]
    | succ r' =>

      have hslot : ∀ s : Fin (r' + 1),
          compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) ≤
            eps * (∑ c ∈ Finset.range (k + 1), (k.choose c : Real) * B c) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
        intro s
        refine le_trans (compL2_iterCov_chrCorr_le hu frame chrH hframe hchrH D hDsm X hX
          s k hx) ?_
        have hterm : ∀ c ∈ Finset.range (k + 1),
            (k.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chrH
                (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
              compL2 (iterCovComp (I := I) frame chrH X (k - c) x) ≤
            (k.choose c : Real) * (B c * eps) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
          intro c hc
          have hc' := Finset.mem_range.mp hc
          have hDc : compL2 (iterCovCompU (I := I) frame chrH
              (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) ≤ B c * eps :=
            hDbound c (by omega) x hx
          have hXc : compL2 (iterCovComp (I := I) frame chrH X (k - c) x) ≤
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) :=
            Finset.single_le_sum
              (f := fun j => compL2 (iterCovComp (I := I) frame chrH X j x))
              (fun j _ => compL2_nonneg _) (Finset.mem_range.mpr (by omega))
          calc (k.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chrH
                  (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
                compL2 (iterCovComp (I := I) frame chrH X (k - c) x)
              ≤ (k.choose c : Real) * (B c * eps) *
                  compL2 (iterCovComp (I := I) frame chrH X (k - c) x) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDc (Nat.cast_nonneg _)) (compL2_nonneg _)
            _ ≤ (k.choose c : Real) * (B c * eps) *
                  ∑ j ∈ Finset.range (k + 1),
                    compL2 (iterCovComp (I := I) frame chrH X j x) :=
                mul_le_mul_of_nonneg_left hXc
                  (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hB c) heps0))
        refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      calc (∑ s : Fin (r' + 1),
            compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x))
          ≤ ∑ _s : Fin (r' + 1),
              eps * (∑ c ∈ Finset.range (k + 1), (k.choose c : Real) * B c) *
                ∑ j ∈ Finset.range (k + 1),
                  compL2 (iterCovComp (I := I) frame chrH X j x) :=
            Finset.sum_le_sum fun s _ => hslot s
        _ = eps * oneStepConst B k (r' + 1) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, oneStepConst]
            push_cast
            ring
  calc compL2 (iterCovComp (I := I) frame chrH X (k + 1) x)
      = compL2 (iterCovComp (I := I) frame chrH
          (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) := hshift
    _ ≤ compL2 (iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
        ∑ s : Fin r, compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) :=
        htri
    _ ≤ compL2 (iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
        eps * oneStepConst B k r *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH X j x) := by
        linarith [hcorrBound]








omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem mixed_oneStep_top {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrG chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (X : M → (Fin r → Idx) → Real)
    (hX : ∀ k : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => X y k) u)
    (B : ℕ → Real) (hB : ∀ i : ℕ, 0 ≤ B i)
    (k : ℕ)
    (hDbound : ∀ c : ℕ, c < k → ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c)
    {x : M} (hx : x ∈ u) :
    compL2 (iterCovComp (I := I) frame chrH X (k + 1) x) ≤
      compL2 (iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
      (r : Real) * compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) k x) *
        compL2 (X x) +
      oneStepConst B k r *
        ∑ j ∈ Finset.range (k + 1),
          compL2 (iterCovComp (I := I) frame chrH X j x) := by
  classical
  set D : M → Idx → Idx → Idx → Real := fun z d b p => chrG z d b p - chrH z d b p with hDdef
  have hDsm : ∀ d b p : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => D y d b p) u :=
    fun d b p => (hchrG d b p).sub (hchrH d b p)
  have hsplit : (fun y => iterCovComp (I := I) frame chrG X 1 y) =
      fun z (n : Fin (r + 1) → Idx) =>
        iterCovComp (I := I) frame chrH X 1 z n -
          ∑ s : Fin r, chrCorrField D X s z n := by
    funext z n
    exact iterCov_one_chr_change frame chrG chrH X z n
  have hHstep_sm : ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chrH X 1 y m) u :=
    fun m => iterCovComp_contMDiffOn hu frame chrH X hframe hchrH hX 1 m
  have hcorr_sm : ∀ s : Fin r, ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrCorrField D X s y m) u :=
    fun s m => contMDiffOn_chrCorrField D hDsm X hX s m
  have hcorrSum_sm : ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ s : Fin r, chrCorrField D X s y m) u :=
    fun m => contMDiffOn_finsetSum' Finset.univ _ (fun s _ => hcorr_sm s m)

  have htri : compL2 (iterCovComp (I := I) frame chrH
      (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) ≤
      compL2 (iterCovComp (I := I) frame chrH
        (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
      ∑ s : Fin r, compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) := by
    have harr' : iterCovComp (I := I) frame chrH
        (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x =
        fun n => iterCovComp (I := I) frame chrH
            (fun y => iterCovComp (I := I) frame chrG X 1 y) k x n +
          ∑ s : Fin r, iterCovComp (I := I) frame chrH (chrCorrField D X s) k x n := by
      funext n
      show iterCovComp (I := I) frame chrH
          (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x n =
        iterCovComp (I := I) frame chrH
            (fun y => iterCovComp (I := I) frame chrG X 1 y) k x n +
          ∑ s : Fin r, iterCovComp (I := I) frame chrH (chrCorrField D X s) k x n
      have h : iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x n =
          iterCovComp (I := I) frame chrH
            (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x n -
          ∑ s : Fin r, iterCovComp (I := I) frame chrH (chrCorrField D X s) k x n := by
        rw [hsplit,
          iterCovComp_sub hu frame chrH
            (fun z m => iterCovComp (I := I) frame chrH X 1 z m)
            (fun z m => ∑ s : Fin r, chrCorrField D X s z m)
            hframe hchrH hHstep_sm hcorrSum_sm k x hx n,
          iterCovComp_finsetSum hu frame chrH hframe hchrH Finset.univ
            (fun s => chrCorrField D X s) (fun s _ m => hcorr_sm s m) k x hx n]
      linarith
    rw [harr']
    refine le_trans (compL2_add_le _ _) ?_
    have hsum := compL2_finsetSum_le (Finset.univ : Finset (Fin r))
      (fun s => iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)
    linarith
  have hshift : compL2 (iterCovComp (I := I) frame chrH X (k + 1) x) =
      compL2 (iterCovComp (I := I) frame chrH
        (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) :=
    compL2_iterCovComp_shift frame chrH X k x

  have hXsum0 : (0 : Real) ≤ ∑ j ∈ Finset.range (k + 1),
      compL2 (iterCovComp (I := I) frame chrH X j x) :=
    Finset.sum_nonneg fun j _ => compL2_nonneg _
  have hcorrBound : (∑ s : Fin r,
      compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)) ≤
      (r : Real) * compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) k x) *
        compL2 (X x) +
      oneStepConst B k r *
        ∑ j ∈ Finset.range (k + 1),
          compL2 (iterCovComp (I := I) frame chrH X j x) := by
    cases r with
    | zero =>
      rw [show (∑ s : Fin 0,
          compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)) = 0 from
        Finset.sum_of_isEmpty _]
      have h0 : oneStepConst B k 0 = 0 := by
        rw [oneStepConst]
        norm_num
      rw [h0, Nat.cast_zero]
      norm_num
    | succ r' =>

      have htopEq : (k.choose k : Real) *
          compL2 (iterCovCompU (I := I) frame chrH
            (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) k x) *
          compL2 (iterCovComp (I := I) frame chrH X (k - k) x) =
          compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) k x) *
            compL2 (X x) := by
        rw [Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul]
        rfl

      have hslot : ∀ s : Fin (r' + 1),
          compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) ≤
            compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) k x) *
              compL2 (X x) +
            (∑ c ∈ Finset.range (k + 1), (k.choose c : Real) * B c) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
        intro s
        refine le_trans (compL2_iterCov_chrCorr_le hu frame chrH hframe hchrH D hDsm X hX
          s k hx) ?_
        rw [Finset.sum_range_succ, htopEq]

        have hblock : (∑ c ∈ Finset.range k, (k.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chrH
                (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
              compL2 (iterCovComp (I := I) frame chrH X (k - c) x)) ≤
            (∑ c ∈ Finset.range (k + 1), (k.choose c : Real) * B c) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
          have hterm : ∀ c ∈ Finset.range k,
              (k.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chrH
                  (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
                compL2 (iterCovComp (I := I) frame chrH X (k - c) x) ≤
              (k.choose c : Real) * B c *
                ∑ j ∈ Finset.range (k + 1),
                  compL2 (iterCovComp (I := I) frame chrH X j x) := by
            intro c hc
            have hc' := Finset.mem_range.mp hc
            have hDc : compL2 (iterCovCompU (I := I) frame chrH
                (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) ≤ B c :=
              hDbound c (by omega) x hx
            have hXc : compL2 (iterCovComp (I := I) frame chrH X (k - c) x) ≤
                ∑ j ∈ Finset.range (k + 1),
                  compL2 (iterCovComp (I := I) frame chrH X j x) :=
              Finset.single_le_sum
                (f := fun j => compL2 (iterCovComp (I := I) frame chrH X j x))
                (fun j _ => compL2_nonneg _) (Finset.mem_range.mpr (by omega))
            calc (k.choose c : Real) *
                  compL2 (iterCovCompU (I := I) frame chrH
                    (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
                  compL2 (iterCovComp (I := I) frame chrH X (k - c) x)
                ≤ (k.choose c : Real) * B c *
                    compL2 (iterCovComp (I := I) frame chrH X (k - c) x) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hDc (Nat.cast_nonneg _)) (compL2_nonneg _)
              _ ≤ (k.choose c : Real) * B c *
                    ∑ j ∈ Finset.range (k + 1),
                      compL2 (iterCovComp (I := I) frame chrH X j x) :=
                  mul_le_mul_of_nonneg_left hXc
                    (mul_nonneg (Nat.cast_nonneg _) (hB c))
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ hXsum0
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (Nat.le_succ k))
            (fun c _ _ => mul_nonneg (Nat.cast_nonneg _) (hB c))
        linarith

      have hsumslot := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (Fin (r' + 1)))) =>
        hslot s
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsumslot
      refine le_trans hsumslot (le_of_eq ?_)
      rw [oneStepConst]
      push_cast
      ring
  calc compL2 (iterCovComp (I := I) frame chrH X (k + 1) x)
      = compL2 (iterCovComp (I := I) frame chrH
          (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) := hshift
    _ ≤ compL2 (iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
        ∑ s : Fin r, compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) :=
        htri
    _ ≤ compL2 (iterCovComp (I := I) frame chrH
          (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) +
        (r : Real) * compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) k x) *
          compL2 (X x) +
        oneStepConst B k r *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH X j x) := by
        linarith [hcorrBound]








private theorem claim2DoubleAux (L : ℕ) (A : ℕ → Real) (hA : ∀ n : ℕ, 0 ≤ A n)
    (K : Real) (hK0 : 0 ≤ K) :
    ∀ k : ℕ, ∃ Ck : Real, 0 ≤ Ck ∧
      ∀ W : ℕ → ℕ → Real, (∀ i' k', 0 ≤ W i' k') →
        (∀ i', i' ≤ L → W i' 0 ≤ K) →
        (∀ i' k', i' + k' + 1 ≤ L →
          W i' (k' + 1) ≤ W (i' + 1) k' + A k' * ∑ j ∈ Finset.range (k' + 1), W i' j) →
        ∀ i', i' + k ≤ L → W i' k ≤ Ck := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      exact ⟨K, hK0, fun W hW0 hBase hOne i' hi' => hBase i' (by omega)⟩
    | succ k' =>

      have hCj : ∀ j : ℕ, ∃ Cj : Real, 0 ≤ Cj ∧ (j < k' + 1 →
          ∀ W : ℕ → ℕ → Real, (∀ i' k'', 0 ≤ W i' k'') →
            (∀ i', i' ≤ L → W i' 0 ≤ K) →
            (∀ i' k'', i' + k'' + 1 ≤ L →
              W i' (k'' + 1) ≤ W (i' + 1) k'' +
                A k'' * ∑ j' ∈ Finset.range (k'' + 1), W i' j') →
            ∀ i', i' + j ≤ L → W i' j ≤ Cj) := by
        intro j
        by_cases hj : j < k' + 1
        · obtain ⟨C, hC0, hCb⟩ := ih j hj
          exact ⟨C, hC0, fun _ => hCb⟩
        · exact ⟨0, le_rfl, fun h => absurd h hj⟩
      choose Cj hCj0 hCjB using hCj
      have hsum0 : (0 : Real) ≤ ∑ j ∈ Finset.range (k' + 1), Cj j :=
        Finset.sum_nonneg fun j _ => hCj0 j
      refine ⟨Cj k' + A k' * ∑ j ∈ Finset.range (k' + 1), Cj j,
        add_nonneg (hCj0 k') (mul_nonneg (hA k') hsum0), ?_⟩
      intro W hW0 hBase hOne i' hik
      have h1 : W i' (k' + 1) ≤ W (i' + 1) k' +
          A k' * ∑ j ∈ Finset.range (k' + 1), W i' j :=
        hOne i' k' (by omega)
      have h2 : W (i' + 1) k' ≤ Cj k' :=
        hCjB k' (by omega) W hW0 hBase hOne (i' + 1) (by omega)
      have h3 : (∑ j ∈ Finset.range (k' + 1), W i' j) ≤
          ∑ j ∈ Finset.range (k' + 1), Cj j := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        exact hCjB j (by omega) W hW0 hBase hOne i' (by omega)
      have h4 : A k' * (∑ j ∈ Finset.range (k' + 1), W i' j) ≤
          A k' * ∑ j ∈ Finset.range (k' + 1), Cj j :=
        mul_le_mul_of_nonneg_left h3 (hA k')
      linarith








theorem claim2Double (L : ℕ) (A : ℕ → Real) (hA : ∀ n : ℕ, 0 ≤ A n)
    (K : Real) (hK0 : 0 ≤ K) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ W : ℕ → ℕ → Real, (∀ i k, 0 ≤ W i k) →
        (∀ i, i ≤ L → W i 0 ≤ K) →
        (∀ i k, i + k + 1 ≤ L →
          W i (k + 1) ≤ W (i + 1) k + A k * ∑ j ∈ Finset.range (k + 1), W i j) →
        ∀ i k, i + k ≤ L → W i k ≤ C := by
  choose Ck hCk0 hCkB using claim2DoubleAux L A hA K hK0
  refine ⟨∑ k ∈ Finset.range (L + 1), Ck k,
    Finset.sum_nonneg fun k _ => hCk0 k, ?_⟩
  intro W hW0 hBase hOne i k hik
  have h1 : W i k ≤ Ck k := hCkB k W hW0 hBase hOne i hik
  have h2 : Ck k ≤ ∑ k' ∈ Finset.range (L + 1), Ck k' :=
    Finset.single_le_sum (f := fun k' => Ck k') (fun k' _ => hCk0 k')
      (Finset.mem_range.mpr (by omega))
  linarith











omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem claim2_component {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (B : ℕ → Real) (hB : ∀ n : ℕ, 0 ≤ B n)
    (L : ℕ) (K : Real) (hK0 : 0 ≤ K) :
    ∃ C, 0 ≤ C ∧
      ∀ (chrG : M → Idx → Idx → Idx → Real),
        (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u) →
      ∀ (T : M → (Fin r₀ → Idx) → Real),
        (∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u) →
        (∀ c : ℕ, c < L → ∀ z ∈ u,
          compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c) →
        (∀ z ∈ u, ∀ s : ℕ, s ≤ L →
          compL2 (iterCovComp (I := I) frame chrG T s z) ≤ K) →
        ∀ x ∈ u, ∀ b a : ℕ, a + b ≤ L →
          compL2 (iterCovComp (I := I) frame chrH
            (iterCovComp (I := I) frame chrG T b) a x) ≤ C := by
  classical
  obtain ⟨C, hC0, hCb⟩ := claim2Double L (fun k => oneStepConst B k (r₀ + L))
    (fun k => oneStepConst_nonneg hB k (r₀ + L)) K hK0
  refine ⟨C, hC0, ?_⟩
  intro chrG hchrG T hT hDbound hShi x hx b a hab
  have hX_sm : ∀ i : ℕ, ∀ kk : Fin (r₀ + i) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chrG T i y kk) u :=
    fun i => iterCovComp_contMDiffOn hu frame chrG T hframe hchrG hT i

  have hbase : ∀ i : ℕ, i ≤ L →
      compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T i) 0 x) ≤ K :=
    fun i hi => hShi x hx i hi

  have hone : ∀ i k : ℕ, i + k + 1 ≤ L →
      compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T i) (k + 1) x) ≤
      compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T (i + 1)) k x) +
      oneStepConst B k (r₀ + L) *
        ∑ j ∈ Finset.range (k + 1),
          compL2 (iterCovComp (I := I) frame chrH
            (iterCovComp (I := I) frame chrG T i) j x) := by
    intro i k hik
    have hrev : compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T i) (k + 1) x) ≤
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T (i + 1)) k x) +
        1 * oneStepConst B k (r₀ + i) *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH
              (iterCovComp (I := I) frame chrG T i) j x) :=
      mixed_oneStep_rev hu frame chrG chrH hframe hchrG hchrH
        (iterCovComp (I := I) frame chrG T i) (hX_sm i) B hB 1 zero_le_one k
        (fun c hck z hz => by rw [mul_one]; exact hDbound c (by omega) z hz) hx
    have hS0 : (0 : Real) ≤ ∑ a' ∈ Finset.range (k + 1), (k.choose a' : Real) * B a' :=
      Finset.sum_nonneg fun a' _ => mul_nonneg (Nat.cast_nonneg _) (hB a')
    have hmono : oneStepConst B k (r₀ + i) ≤ oneStepConst B k (r₀ + L) := by
      have hcast : ((r₀ + i : ℕ) : Real) ≤ ((r₀ + L : ℕ) : Real) := by
        exact_mod_cast Nat.add_le_add_left (show i ≤ L by omega) r₀
      calc oneStepConst B k (r₀ + i)
          = ((r₀ + i : ℕ) : Real) *
              ∑ a' ∈ Finset.range (k + 1), (k.choose a' : Real) * B a' := rfl
        _ ≤ ((r₀ + L : ℕ) : Real) *
              ∑ a' ∈ Finset.range (k + 1), (k.choose a' : Real) * B a' :=
            mul_le_mul_of_nonneg_right hcast hS0
        _ = oneStepConst B k (r₀ + L) := rfl
    have hSig0 : (0 : Real) ≤ ∑ j ∈ Finset.range (k + 1),
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T i) j x) :=
      Finset.sum_nonneg fun j _ => compL2_nonneg _
    have hconst : 1 * oneStepConst B k (r₀ + i) *
        (∑ j ∈ Finset.range (k + 1),
          compL2 (iterCovComp (I := I) frame chrH
            (iterCovComp (I := I) frame chrG T i) j x)) ≤
        oneStepConst B k (r₀ + L) *
        ∑ j ∈ Finset.range (k + 1),
          compL2 (iterCovComp (I := I) frame chrH
            (iterCovComp (I := I) frame chrG T i) j x) := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hmono hSig0
    linarith
  exact hCb
    (fun i k => compL2 (iterCovComp (I := I) frame chrH
      (iterCovComp (I := I) frame chrG T i) k x))
    (fun i k => compL2_nonneg _) hbase hone b a (by omega)




private theorem chain_le (V Q : ℕ → Real) (N : ℕ)
    (hstep : ∀ i, i < N → V i ≤ V (i + 1) + Q i) :
    V 0 ≤ V N + ∑ i ∈ Finset.range N, Q i := by
  induction N with
  | zero => simp
  | succ n ih =>
    have h1 : V 0 ≤ V n + ∑ i ∈ Finset.range n, Q i :=
      ih fun i hi => hstep i (by omega)
    have h2 : V n ≤ V (n + 1) + Q n := hstep n (by omega)
    rw [Finset.sum_range_succ]
    linarith












omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem mixed_descent {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (B : ℕ → Real) (hB : ∀ n : ℕ, 0 ≤ B n)
    (N : ℕ) (hN : 1 ≤ N)
    (C₂ : Real) (hC₂0 : 0 ≤ C₂)
    (K : Real) (hK0 : 0 ≤ K) :
    ∃ C, 0 ≤ C ∧
      ∀ (chrG : M → Idx → Idx → Idx → Real),
        (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u) →
      ∀ (T : M → (Fin r₀ → Idx) → Real),
        (∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u) →
        (∀ c : ℕ, c + 1 < N → ∀ z ∈ u,
          compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c) →
        (∀ z ∈ u, ∀ b a : ℕ, a + b ≤ N - 1 →
          compL2 (iterCovComp (I := I) frame chrH
            (iterCovComp (I := I) frame chrG T b) a z) ≤ C₂) →
        (∀ z ∈ u, compL2 (iterCovComp (I := I) frame chrG T N z) ≤ K) →
        ∀ x ∈ u,
          compL2 (iterCovComp (I := I) frame chrH T N x) ≤
            C * (1 + compL2 (iterCovCompU (I := I) frame chrH
              (chrDiffField chrG chrH) (N - 1) x)) := by
  classical
  have hBmax0 : (0 : Real) ≤ ∑ c ∈ Finset.range N, B c :=
    Finset.sum_nonneg fun c _ => hB c
  have hOS0 : (0 : Real) ≤ ∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N) :=
    Finset.sum_nonneg fun k _ => oneStepConst_nonneg hB k _
  have h1B : (0 : Real) ≤ 1 + ∑ c ∈ Finset.range N, B c := by linarith
  refine ⟨K + (N : Real) * (((r₀ + N : ℕ) : Real) * (1 + ∑ c ∈ Finset.range N, B c) * C₂ +
      (∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N)) * ((N : Real) * C₂)),
    add_nonneg hK0 (mul_nonneg (Nat.cast_nonneg N)
      (add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) h1B) hC₂0)
        (mul_nonneg hOS0 (mul_nonneg (Nat.cast_nonneg N) hC₂0)))), ?_⟩
  intro chrG hchrG T hT hDlow hmix hShiN x hx
  have hX_sm : ∀ i : ℕ, ∀ kk : Fin (r₀ + i) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chrG T i y kk) u :=
    fun i => iterCovComp_contMDiffOn hu frame chrG T hframe hchrG hT i
  have hd0 : (0 : Real) ≤ compL2 (iterCovCompU (I := I) frame chrH
      (chrDiffField chrG chrH) (N - 1) x) := compL2_nonneg _

  have hstep : ∀ i, i < N →
      compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T i) (N - i) x) ≤
      compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T (i + 1)) (N - (i + 1)) x) +
      (((r₀ + N : ℕ) : Real) *
          (compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) +
            ∑ c ∈ Finset.range N, B c) * C₂ +
        (∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N)) * ((N : Real) * C₂)) := by
    intro i hi
    have e1 : N - i = (N - i - 1) + 1 := by omega
    have e2 : N - (i + 1) = N - i - 1 := by omega
    rw [e1, e2]

    have htop : compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T i) ((N - i - 1) + 1) x) ≤
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T (i + 1)) (N - i - 1) x) +
        ((r₀ + i : ℕ) : Real) *
          compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - i - 1) x) *
          compL2 (iterCovComp (I := I) frame chrG T i x) +
        oneStepConst B (N - i - 1) (r₀ + i) *
          ∑ j ∈ Finset.range ((N - i - 1) + 1),
            compL2 (iterCovComp (I := I) frame chrH
              (iterCovComp (I := I) frame chrG T i) j x) :=
      mixed_oneStep_top hu frame chrG chrH hframe hchrG hchrH
        (iterCovComp (I := I) frame chrG T i) (hX_sm i) B hB (N - i - 1)
        (fun c hc z hz => hDlow c (by omega) z hz) hx

    have hDfac : compL2 (iterCovCompU (I := I) frame chrH
        (chrDiffField chrG chrH) (N - i - 1) x) ≤
        compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) +
          ∑ c ∈ Finset.range N, B c := by
      by_cases hi0 : i = 0
      · subst hi0
        have he : compL2 (iterCovCompU (I := I) frame chrH
            (chrDiffField chrG chrH) (N - 0 - 1) x) =
            compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) := rfl
        rw [he]
        linarith
      · have hDle := hDlow (N - i - 1) (by omega) x hx
        have hBle : B (N - i - 1) ≤ ∑ c ∈ Finset.range N, B c :=
          Finset.single_le_sum (f := fun c => B c) (fun c _ => hB c)
            (Finset.mem_range.mpr (by omega))
        linarith

    have hXi : compL2 (iterCovComp (I := I) frame chrG T i x) ≤ C₂ :=
      hmix x hx i 0 (by omega)
    have hcast : ((r₀ + i : ℕ) : Real) ≤ ((r₀ + N : ℕ) : Real) := by
      exact_mod_cast Nat.add_le_add_left (le_of_lt hi) r₀
    have hmid : ((r₀ + i : ℕ) : Real) *
        compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - i - 1) x) *
        compL2 (iterCovComp (I := I) frame chrG T i x) ≤
        ((r₀ + N : ℕ) : Real) *
          (compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) +
            ∑ c ∈ Finset.range N, B c) * C₂ := by
      have h12 : ((r₀ + i : ℕ) : Real) *
          compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - i - 1) x) ≤
          ((r₀ + N : ℕ) : Real) *
            (compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) +
              ∑ c ∈ Finset.range N, B c) :=
        mul_le_mul hcast hDfac (compL2_nonneg _) (Nat.cast_nonneg _)
      exact mul_le_mul h12 hXi (compL2_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (by linarith))
    have hSum : (∑ j ∈ Finset.range ((N - i - 1) + 1),
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T i) j x)) ≤ (N : Real) * C₂ := by
      have hb : ∀ j ∈ Finset.range ((N - i - 1) + 1),
          compL2 (iterCovComp (I := I) frame chrH
            (iterCovComp (I := I) frame chrG T i) j x) ≤ C₂ :=
        fun j hj => hmix x hx i j (by have := Finset.mem_range.mp hj; omega)
      have h1 := Finset.sum_le_card_nsmul _ _ _ hb
      rw [Finset.card_range, nsmul_eq_mul] at h1
      have h2 : ((N - i - 1 + 1 : ℕ) : Real) * C₂ ≤ (N : Real) * C₂ :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast (show N - i - 1 + 1 ≤ N by omega)) hC₂0
      linarith
    have hOSi : oneStepConst B (N - i - 1) (r₀ + i) ≤
        ∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N) := by
      have hS0' : (0 : Real) ≤ ∑ a ∈ Finset.range ((N - i - 1) + 1),
          ((N - i - 1).choose a : Real) * B a :=
        Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg _) (hB a)
      have hrank : oneStepConst B (N - i - 1) (r₀ + i) ≤
          oneStepConst B (N - i - 1) (r₀ + N) := by
        calc oneStepConst B (N - i - 1) (r₀ + i)
            = ((r₀ + i : ℕ) : Real) * ∑ a ∈ Finset.range ((N - i - 1) + 1),
                ((N - i - 1).choose a : Real) * B a := rfl
          _ ≤ ((r₀ + N : ℕ) : Real) * ∑ a ∈ Finset.range ((N - i - 1) + 1),
                ((N - i - 1).choose a : Real) * B a :=
              mul_le_mul_of_nonneg_right hcast hS0'
          _ = oneStepConst B (N - i - 1) (r₀ + N) := rfl
      have hmem : oneStepConst B (N - i - 1) (r₀ + N) ≤
          ∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N) :=
        Finset.single_le_sum (f := fun k => oneStepConst B k (r₀ + N))
          (fun k _ => oneStepConst_nonneg hB k _) (Finset.mem_range.mpr (by omega))
      linarith
    have hlast : oneStepConst B (N - i - 1) (r₀ + i) *
        (∑ j ∈ Finset.range ((N - i - 1) + 1),
          compL2 (iterCovComp (I := I) frame chrH
            (iterCovComp (I := I) frame chrG T i) j x)) ≤
        (∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N)) * ((N : Real) * C₂) :=
      mul_le_mul hOSi hSum (Finset.sum_nonneg fun j _ => compL2_nonneg _) hOS0
    linarith

  have hchain : compL2 (iterCovComp (I := I) frame chrH
      (iterCovComp (I := I) frame chrG T 0) (N - 0) x) ≤
      compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T N) (N - N) x) +
      ∑ _i ∈ Finset.range N,
        (((r₀ + N : ℕ) : Real) *
            (compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) +
              ∑ c ∈ Finset.range N, B c) * C₂ +
          (∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N)) * ((N : Real) * C₂)) :=
    chain_le
      (fun i => compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T i) (N - i) x))
      (fun _ => ((r₀ + N : ℕ) : Real) *
          (compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) +
            ∑ c ∈ Finset.range N, B c) * C₂ +
        (∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N)) * ((N : Real) * C₂))
      N hstep
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hchain

  have hVN : compL2 (iterCovComp (I := I) frame chrH
      (iterCovComp (I := I) frame chrG T N) (N - N) x) ≤ K := by
    rw [Nat.sub_self]
    exact hShiN x hx

  have hhead : compL2 (iterCovComp (I := I) frame chrH T N x) ≤
      compL2 (iterCovComp (I := I) frame chrH
        (iterCovComp (I := I) frame chrG T N) (N - N) x) +
      (N : Real) * (((r₀ + N : ℕ) : Real) *
          (compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) +
            ∑ c ∈ Finset.range N, B c) * C₂ +
        (∑ k ∈ Finset.range N, oneStepConst B k (r₀ + N)) * ((N : Real) * C₂)) := hchain
  nlinarith [hhead, hVN, hd0, hK0, hC₂0, hBmax0, hOS0,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg (r₀ + N))) hC₂0,
    mul_nonneg hK0 hd0,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (Nat.cast_nonneg (r₀ + N))) hBmax0) hC₂0) hd0,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (Nat.cast_nonneg N)) hOS0) hC₂0) hd0]


















omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem aN_component {r₀ rg : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (N : ℕ) (hN : 1 ≤ N)
    (B : ℕ → Real) (hB0 : ∀ n : ℕ, 0 ≤ B n)
    (Ctop : Real) (hCtop0 : 0 ≤ Ctop)
    (KShi : Real) (hKShi0 : 0 ≤ KShi) :
    ∃ Cpp Cppp : Real, 0 ≤ Cpp ∧ 0 ≤ Cppp ∧
      ∀ (chrG : M → Idx → Idx → Idx → Real),
        (∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u) →
      ∀ (T : M → (Fin r₀ → Idx) → Real),
        (∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u) →
        (∀ c : ℕ, c < N - 1 → ∀ z ∈ u,
          compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c) →
      ∀ (gComp : M → (Fin rg → Idx) → Real),
        (∀ x ∈ u,
          compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) ≤
            Ctop * (1 + compL2 (iterCovComp (I := I) frame chrH gComp N x))) →
        (∀ z ∈ u, ∀ s : ℕ, s ≤ N →
          compL2 (iterCovComp (I := I) frame chrG T s z) ≤ KShi) →
        ∀ x ∈ u,
          compL2 (iterCovComp (I := I) frame chrH T N x) ≤
            Cpp * compL2 (iterCovComp (I := I) frame chrH gComp N x) + Cppp := by
  classical

  obtain ⟨C₂, hC₂0, hmixU⟩ := claim2_component (r₀ := r₀) hu frame chrH hframe hchrH
    B hB0 (N - 1) KShi hKShi0

  obtain ⟨Cdesc, hCdesc0, hdescU⟩ := mixed_descent (r₀ := r₀) hu frame chrH hframe hchrH
    B hB0 N hN C₂ hC₂0 KShi hKShi0
  refine ⟨Cdesc * Ctop, Cdesc * (1 + Ctop), mul_nonneg hCdesc0 hCtop0,
    mul_nonneg hCdesc0 (by linarith), ?_⟩
  intro chrG hchrG T hT hDlow gComp hDtop hShi x hx
  have hmix := hmixU chrG hchrG T hT (fun c hc z hz => hDlow c hc z hz)
    (fun z hz s hs => hShi z hz s (by omega))
  have hdesc := hdescU chrG hchrG T hT (fun c hc z hz => hDlow c (by omega) z hz)
    (fun z hz b a hab => hmix z hz b a hab)
    (fun z hz => hShi z hz N le_rfl)
  have hd := hdesc x hx
  have ht := hDtop x hx
  have hkey : Cdesc *
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) (N - 1) x) ≤
      Cdesc * (Ctop * (1 + compL2 (iterCovComp (I := I) frame chrH gComp N x))) :=
    mul_le_mul_of_nonneg_left ht hCdesc0
  nlinarith [hd, hkey]

end DifferentialGeometry.PDE.RicciFlow
