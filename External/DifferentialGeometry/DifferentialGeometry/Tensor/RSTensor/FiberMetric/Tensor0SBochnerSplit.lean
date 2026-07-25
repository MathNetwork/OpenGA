import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Geometry.Operator.RoughLaplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

























































namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]










section Coord

variable {Idx : Type*} [Fintype Idx]



def freezeFirst2Comp {s : Nat}
    (H2 : (Fin (s + 2) -> Idx) -> Real) (i j : Idx) :
    (Fin s -> Idx) -> Real :=
  fun J0 => H2 (Fin.cons i (Fin.cons j J0))



def freezeFirst1Comp {s : Nat}
    (H1 : (Fin (s + 1) -> Idx) -> Real) (i : Idx) :
    (Fin s -> Idx) -> Real :=
  fun J0 => H1 (Fin.cons i J0)





def traceFirst2Comp {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (H2 : (Fin (s + 2) -> Idx) -> Real) :
    (Fin s -> Idx) -> Real :=
  fun J0 => ∑ i : Idx, ∑ j : Idx, gInv i j * H2 (Fin.cons i (Fin.cons j J0))



theorem sum_fin_cons {s : Nat} {A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) -> Idx) -> A) :
    (∑ K : Fin (s + 1) -> Idx, F K) =
      ∑ i : Idx, ∑ K' : Fin s -> Idx, F (Fin.cons i K') := by
  classical
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).symm
      F (fun p : Idx × (Fin s -> Idx) => F (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro K
    congr 1
    exact (Fin.cons_self_tail K).symm




theorem sum_comm_blocks {s : Nat} {A : Type*} [AddCommMonoid A]
    (F : Idx -> Idx -> (Fin s -> Idx) -> (Fin s -> Idx) -> A) :
    (∑ i : Idx, ∑ j : Idx, ∑ p : Fin s -> Idx, ∑ q : Fin s -> Idx, F i j p q) =
      ∑ p : Fin s -> Idx, ∑ q : Fin s -> Idx, ∑ i : Idx, ∑ j : Idx, F i j p q := by
  classical
  rw [show
      (∑ i : Idx, ∑ j : Idx, ∑ p : Fin s -> Idx, ∑ q : Fin s -> Idx, F i j p q) =
        ∑ ij : Idx × Idx, ∑ pq : (Fin s -> Idx) × (Fin s -> Idx),
          F ij.1 ij.2 pq.1 pq.2 from by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Fintype.sum_prod_type]




theorem sum_fin_cons2 {s : Nat} {A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) -> Idx) -> (Fin (s + 1) -> Idx) -> A) :
    (∑ K : Fin (s + 1) -> Idx, ∑ L : Fin (s + 1) -> Idx, F K L) =
      ∑ i : Idx, ∑ K' : Fin s -> Idx, ∑ j : Idx, ∑ L' : Fin s -> Idx,
        F (Fin.cons i K') (Fin.cons j L') := by
  rw [sum_fin_cons (fun K : Fin (s + 1) -> Idx =>
    ∑ L : Fin (s + 1) -> Idx, F K L)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun K' _ => ?_
  rw [sum_fin_cons (fun L : Fin (s + 1) -> Idx => F (Fin.cons i K') L)]









theorem sum_trace_coordContract_rough {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (H2 : (Fin (s + 2) -> Idx) -> Real)
    (cT : (Fin s -> Idx) -> Real) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordContract (s := s) gInv (freezeFirst2Comp H2 i j) cT) =
      coordContract (s := s) gInv (traceFirst2Comp gInv H2) cT := by
  classical
  unfold coordContract traceFirst2Comp freezeFirst2Comp

  trans (∑ i : Idx, ∑ j : Idx, ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
      gInv i j *
        ((∏ a : Fin s, gInv (I0 a) (J0 a)) *
            H2 (Fin.cons i (Fin.cons j I0)) * cT J0))
  ·
    simp_rw [Finset.mul_sum]
  ·
    rw [sum_comm_blocks (fun i j I0 J0 =>
      gInv i j *
        ((∏ a : Fin s, gInv (I0 a) (J0 a)) *
            H2 (Fin.cons i (Fin.cons j I0)) * cT J0))]
    refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring










theorem sum_trace_coordContract_nabla {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (H1 : (Fin (s + 1) -> Idx) -> Real) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordContract (s := s) gInv
            (freezeFirst1Comp H1 i) (freezeFirst1Comp H1 j)) =
      coordContract (s := s + 1) gInv H1 H1 := by
  classical


  symm
  unfold coordContract freezeFirst1Comp
  rw [sum_fin_cons2 (fun K L : Fin (s + 1) -> Idx =>
    (∏ a : Fin (s + 1), gInv (K a) (L a)) * H1 K * H1 L)]

  simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun L' _ => ?_
  ring

end Coord








section Intrinsic

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

open DifferentialGeometry.Integral.Connection



omit [Fintype Idx] [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_comp {s : Nat} {x : M}
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i : Idx) (J0 : Fin s -> Idx) :
    tensor0SComponent (I := I)
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
        (fun k => basis k) J0 =
      freezeFirst1Comp (s := s)
        (fun K0 => tensor0SComponent (I := I) nablaT (fun k => basis k) K0) i J0 := by
  unfold tensor0SComponent freezeFirst1Comp
  rw [tensor0S_curry_apply_cons (I := I) s nablaT (basis i) (fun a => basis (J0 a))]
  congr 1
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · rfl




omit [Fintype Idx] [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] in
private theorem freezeFirstTwoArgs0S_comp {s : Nat} {x : M}
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j : Idx) (J0 : Fin s -> Idx) :
    tensor0SComponent (I := I)
        (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j))
        (fun k => basis k) J0 =
      freezeFirst2Comp (s := s)
        (fun K0 => tensor0SComponent (I := I) nabla2T (fun k => basis k) K0)
        i j J0 := by
  unfold tensor0SComponent freezeFirst2Comp
  rw [freezeFirstTwoArgs0S_apply (I := I) nabla2T (basis i) (basis j)
    (fun a => basis (J0 a))]
  congr 1
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun c => ?_) b
    · rfl
    · rfl



omit [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] in
private theorem metricTrace0S2TensorInBasis_comp {s : Nat} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (J0 : Fin s -> Idx) :
    tensor0SComponent (I := I)
        (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T)
        (fun k => basis k) J0 =
      traceFirst2Comp (s := s) gInv
        (fun K0 => tensor0SComponent (I := I) nabla2T (fun k => basis k) K0) J0 := by
  unfold tensor0SComponent traceFirst2Comp
  rw [metricTrace0S2TensorInBasis_apply (I := I) basis gInv nabla2T
    (fun k => basis (J0 k))]
  unfold metricTrace0S2InBasis
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  beta_reduce
  congr 1
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun c => ?_) b
    · rfl
    · rfl










def TensorNormHessianProductInBasis {s : Nat} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (normSecond : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 x) : Prop :=
  ∀ i j : Idx,
    normSecond (vec2 (I := I) (basis i) (basis j)) =
      (2 : Real) *
        (coordInner0S (I := I) (x := x) s gInv
            (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j)) T basis +
          coordInner0S (I := I) (x := x) s gInv
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis j))
            basis)
















omit [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] in
theorem tensorNormBochnerSplit_coord {s : Nat} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (normSecond : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 x)
    (hprod : TensorNormHessianProductInBasis (I := I) basis gInv T nablaT nabla2T
      normSecond) :
    metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
      2 * coordInner0S (I := I) (x := x) s gInv
            (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T basis +
        2 * coordInner0S (I := I) (x := x) (s + 1) gInv nablaT nablaT basis := by
  classical

  set cT : (Fin s -> Idx) -> Real :=
    fun J0 => tensor0SComponent (I := I) T (fun k => basis k) J0 with hcT
  set cH1 : (Fin (s + 1) -> Idx) -> Real :=
    fun J0 => tensor0SComponent (I := I) nablaT (fun k => basis k) J0 with hcH1
  set cH2 : (Fin (s + 2) -> Idx) -> Real :=
    fun J0 => tensor0SComponent (I := I) nabla2T (fun k => basis k) J0 with hcH2

  have hexpand :
      metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
        ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            ((2 : Real) *
              (coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT +
                coordContract (s := s) gInv
                  (freezeFirst1Comp cH1 i)
                  (freezeFirst1Comp cH1 j))) := by
    unfold metricTrace0S2InBasis
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1

    have hinput :
        normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
          normSecond (vec2 (I := I) (basis i) (basis j)) := by
      congr 1
      funext a
      fin_cases a
      · simp [metricTraceInput, vec2,
          DifferentialGeometry.Integral.Connection.vec2]
      · rfl
    rw [hinput, hprod i j]

    have hRough :
        coordInner0S (I := I) (x := x) s gInv
            (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j)) T basis =
          coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT := by
      rw [← coordContract_eq_coordInner0S (I := I) gInv
        (freezeFirstTwoArgs0S (I := I) nabla2T (basis i) (basis j)) T basis]
      refine congrArg (fun f => coordContract (s := s) gInv f cT) ?_
      funext K0
      rw [freezeFirstTwoArgs0S_comp (I := I) nabla2T basis i j K0]
    have hNab :
        coordInner0S (I := I) (x := x) s gInv
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
            (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis j))
            basis =
          coordContract (s := s) gInv
            (freezeFirst1Comp cH1 i) (freezeFirst1Comp cH1 j) := by
      rw [← coordContract_eq_coordInner0S (I := I) gInv
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis i))
        (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x nablaT (basis j)) basis]
      refine congrArg₂ (fun f g => coordContract (s := s) gInv f g) ?_ ?_
      · funext K0; rw [tensor0S_curry_comp (I := I) nablaT basis i K0]
      · funext K0; rw [tensor0S_curry_comp (I := I) nablaT basis j K0]
    rw [hRough, hNab]

  rw [hexpand]
  have hsplit :
      (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            ((2 : Real) *
              (coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT +
                coordContract (s := s) gInv
                  (freezeFirst1Comp cH1 i)
                  (freezeFirst1Comp cH1 j)))) =
        2 *
            (∑ i : Idx, ∑ j : Idx,
              gInv i j *
                coordContract (s := s) gInv (freezeFirst2Comp cH2 i j) cT) +
          2 *
            (∑ i : Idx, ∑ j : Idx,
              gInv i j *
                coordContract (s := s) gInv
                  (freezeFirst1Comp cH1 i)
                  (freezeFirst1Comp cH1 j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]

  rw [sum_trace_coordContract_rough gInv cH2 cT]
  rw [sum_trace_coordContract_nabla gInv cH1]


  have hRL :
      coordContract (s := s) gInv (traceFirst2Comp gInv cH2) cT =
        coordInner0S (I := I) (x := x) s gInv
          (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T basis := by
    rw [← coordContract_eq_coordInner0S (I := I) gInv
      (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T basis]
    refine congrArg (fun f => coordContract (s := s) gInv f cT) ?_
    funext J0
    rw [metricTrace0S2TensorInBasis_comp (I := I) basis gInv nabla2T J0]

  have hNN :
      coordContract (s := s + 1) gInv cH1 cH1 =
        coordInner0S (I := I) (x := x) (s + 1) gInv nablaT nablaT basis := by
    rw [hcH1]
    exact coordContract_eq_coordInner0S (I := I) gInv nablaT nablaT basis
  rw [hRL, hNN]























theorem tensorNormBochnerSplit {s : Nat} {x : M}
    (g : SmoothMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (normSecond : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 x)
    (hprod : TensorNormHessianProductInBasis (I := I) basis gInv T nablaT nabla2T
      normSecond) :
    metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
      2 * inner0S (I := I) g x s
            (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T +
        2 * normSq0S (I := I) g x (s + 1) nablaT := by
  rw [tensorNormBochnerSplit_coord (I := I) basis gInv T nablaT nabla2T normSecond
    hprod]
  rw [← inner0S_eq_coord (I := I) g x s basis gInv hinv
      (metricTrace0S2TensorInBasis (I := I) basis gInv nabla2T) T,
    ← normSq0S_eq_coord (I := I) g x (s + 1) basis gInv hinv nablaT]

end Intrinsic

end

end Tensor0SBundle
