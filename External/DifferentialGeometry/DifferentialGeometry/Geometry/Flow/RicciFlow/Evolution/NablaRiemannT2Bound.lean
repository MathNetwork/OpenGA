import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRaisingBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannOrthoFrame
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeat

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
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]






section AbstractBound

variable {n : ℕ}




omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem tensor04_vec4_sum_last
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (A B C : TangentSpace I x)
    (coef : Fin n → Real) (vecs : Fin n → TangentSpace I x) :
    Rm04 (vec4 (I := I) A B C (∑ e : Fin n, coef e • vecs e)) =
      ∑ e : Fin n, coef e * Rm04 (vec4 (I := I) A B C (vecs e)) := by
  classical

  have hupd : ∀ Z : TangentSpace I x,
      vec4 (I := I) A B C Z =
        Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 Z := by
    intro Z
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [hupd]

  rw [show Rm04 (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Fin n, coef e • vecs e)) =
      Rm04.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (∑ e : Fin n, coef e • vecs e)) from rfl]
  rw [Rm04.toMultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show Rm04.toMultilinearMap (Function.update
        (vec4 (I := I) A B C (0 : TangentSpace I x)) 3 (coef e • vecs e)) =
      Rm04 (Function.update (vec4 (I := I) A B C (0 : TangentSpace I x)) 3
        (coef e • vecs e)) from rfl]
  rw [Rm04.map_update_smul, ← hupd]
  simp [smul_eq_mul]




omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem cotangentSharp_orthoBasis_expand
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    cotangentSharp_gen (I := I) g x β =
      ∑ e : Fin n, (β (fun _ : Fin 1 => basis e)) • basis e := by
  classical

  set gInv : Fin n → Fin n → Real := fun i j => if i = j then 1 else 0 with hgInv
  have hdiag : ∀ i : Fin n, gInv i i = 1 := by intro i; simp [hgInv]
  have hoff : ∀ i k : Fin n, i ≠ k → gInv i k = 0 := by
    intro i k hk; simp [hgInv, hk]
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv := by
    intro i j
    refine ⟨?_, ?_⟩
    ·
      rw [Finset.sum_eq_single i]
      · rw [hdiag i, one_mul]; exact horth i j
      · intro k _ hk; rw [hoff i k (fun h => hk h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    ·
      rw [Finset.sum_eq_single j]
      · rw [hdiag j, mul_one]; exact horth i j
      · intro k _ hk; rw [hoff k j hk, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
  rw [cotangentSharp_eq_sum_inv_gen (I := I) g x basis gInv hinv β]
  refine Finset.sum_congr rfl fun i _ => ?_

  congr 1
  rw [Finset.sum_eq_single i]
  · rw [hdiag i, one_mul, cotangentToDual_apply_gen]
  · intro j _ hj; rw [hoff i j (fun h => hj h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h










omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curvatureAction0SAt_orthoBasis_eq_sum
    (g : SmoothRiemannianMetric I M) {x : M} {s : ℕ}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (a c : Fin n) (sidx : Fin s → Fin n) :
    curvatureAction0SAt (I := I) Rm13 alpha (basis a) (basis c)
        (fun p => basis (sidx p)) =
      -∑ q : Fin s, ∑ e : Fin n,
        alpha (fun p => basis (Function.update sidx q e p)) *
          Rm04 (vec4 (I := I) (basis a) (basis c) (basis (sidx q)) (basis e)) := by
  classical
  rw [curvatureAction0SAt]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_

  rw [rm13_apply_eq_rm04_raise (I := I) g (Rm13 x) Rm04 hLower
    (oneFormAtSlot0S (I := I) alpha (fun p => basis (sidx p)) q) (basis a) (basis c)
    (basis (sidx q))]

  rw [cotangentSharp_orthoBasis_expand (I := I) g basis horth
    (oneFormAtSlot0S (I := I) alpha (fun p => basis (sidx p)) q)]
  rw [tensor04_vec4_sum_last (I := I) Rm04 (basis a) (basis c) (basis (sidx q))]
  refine Finset.sum_congr rfl fun e _ => ?_

  congr 1
  rw [oneFormAtSlot0S_apply]

  congr 1
  funext p
  by_cases hp : p = q
  · subst hp; simp [Function.update]
  · simp [Function.update, hp]

















omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem abs_curvatureAction0SAt_orthoBasis_le
    (g : SmoothRiemannianMetric I M) {x : M} {s : ℕ}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x))
    (horth : ∀ i j : Fin n,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (a c : Fin n) (sidx : Fin s → Fin n) :
    |curvatureAction0SAt (I := I) Rm13 alpha (basis a) (basis c)
        (fun p => basis (sidx p))| ≤
      (s : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
            Rm04 (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin s → Fin n =>
            alpha (fun p => basis (idx p))))) := by
  classical
  set R : Fin n → Fin n → Fin n → Fin n → Real :=
    fun i j k l => Rm04 (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)) with hR
  set A : (Fin s → Fin n) → Real :=
    fun idx => alpha (fun p => basis (idx p)) with hA
  set NR : Real := Real.sqrt (compNormSq4 R) with hNR
  set NA : Real := Real.sqrt (compNormSqMulti A) with hNA
  have hNRnn : 0 ≤ NR := Real.sqrt_nonneg _
  have hNAnn : 0 ≤ NA := Real.sqrt_nonneg _

  rw [curvatureAction0SAt_orthoBasis_eq_sum (I := I) g Rm13 Rm04 hLower basis horth
    alpha a c sidx]
  rw [abs_neg]

  have hStep :
      |∑ q : Fin s, ∑ e : Fin n, A (Function.update sidx q e) * R a c (sidx q) e| ≤
        ∑ q : Fin s, ∑ e : Fin n, NR * NA := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun q _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun e _ => ?_
    rw [abs_mul]
    have hAbnd : |A (Function.update sidx q e)| ≤ NA := by
      rw [hNA]; exact abs_le_sqrt_compNormSqMulti A (Function.update sidx q e)
    have hRbnd : |R a c (sidx q) e| ≤ NR := by
      rw [hNR]; exact abs_le_sqrt_compNormSq4 R a c (sidx q) e
    calc
      |A (Function.update sidx q e)| * |R a c (sidx q) e|
          ≤ NA * NR := mul_le_mul hAbnd hRbnd (abs_nonneg _) hNAnn
      _ = NR * NA := by ring
  refine le_trans hStep ?_

  have hconst :
      (∑ q : Fin s, ∑ e : Fin n, NR * NA) =
        (s : Real) * (Fintype.card (Fin n) : Real) * (NR * NA) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    ring
  rw [hconst]

end AbstractBound









section OrthoBasisFrame






omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem exists_orthoBasisFrameAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x)
      (basis : Module.Basis (Fin n) Real (TangentSpace I x₀)),
      (∀ i : Fin n, frame i x₀ = basis i) ∧
      (∀ i j : Fin n,
        (S.family.metric t).inner x₀ (basis i) (basis j) =
          if i = j then (1 : Real) else 0) := by
  classical
  set g := S.family.metric t with hg_def
  let cd : InnerProductSpace.Core Real (TangentSpace I x₀) := g.toRiemannianMetric.toCore x₀
  have hc : ContinuousAt (fun v : TangentSpace I x₀ => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x₀
  have hbnd : Bornology.IsVonNBounded Real {v : TangentSpace I x₀ |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x₀
  letI nag : NormedAddCommGroup (TangentSpace I x₀) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace Real (TangentSpace I x₀) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank Real (TangentSpace I x₀) with hn_def
  set e : OrthonormalBasis (Fin n) Real (TangentSpace I x₀) :=
    stdOrthonormalBasis Real (TangentSpace I x₀) with he_def
  have hinner_eq : ∀ u v : TangentSpace I x₀, (inner Real u v : Real) = g.inner x₀ u v :=
    fun u v => rfl
  refine ⟨n, fun i _x => e i, e.toBasis, ?_, ?_⟩
  · intro i; rw [OrthonormalBasis.coe_toBasis]
  · intro i j
    have horth : Orthonormal Real (fun i : Fin n => e i) := e.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := Real) (E := TangentSpace I x₀)).mp horth i j

    change (g.inner x₀) (e i) (e j) = if i = j then (1 : Real) else 0
    rw [← hinner_eq (e i) (e j)]
    simpa using hite

end OrthoBasisFrame







section SolutionBound

variable {n : ℕ}











omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem abs_nablaLapComm_T2_orthoBasis_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.family.metric t).inner x₀ (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (a b c : Fin n) (m : Fin 4 → Fin n) :
    |curvatureAction0SAt (I := I) (S.base.rm13 t) (nablaRm04Field (I := I) S t x₀)
        (frame a x₀) (frame c x₀)
        (nabla3InnerSlotsF (I := I) frame x₀ b m)| ≤
      (5 : Real) * (Fintype.card (Fin n) : Real) *
        (Real.sqrt (compNormSq4 (fun i j k l : Fin n =>
            S.base.rm04 t x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l)))) *
          Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S t x₀ (fun p => basis (idx p))))) := by
  classical

  set sidx : Fin 5 → Fin n := Fin.cons b m with hsidx

  have hslots :
      nabla3InnerSlotsF (I := I) frame x₀ b m =
        (fun p => basis (sidx p)) := by
    funext p
    refine Fin.cases ?_ ?_ p
    · simp [nabla3InnerSlotsF, hframe b, hsidx]
    · intro q
      simp [nabla3InnerSlotsF, frameTuple, hframe (m q), hsidx]
  rw [hframe a, hframe c, hslots]

  have hmain :=
    abs_curvatureAction0SAt_orthoBasis_le (I := I) (S.family.metric t)
      (S.base.rm13 t) (S.base.rm04 t x₀)
      (solution_rm04LowersRm13At (I := I) S t x₀)
      basis horth (nablaRm04Field (I := I) S t x₀) a c sidx

  simpa using hmain



private theorem sum_pi_fin_succ {Idx : Type*} [Fintype Idx] {k : ℕ}
    (f : (Fin (k + 1) → Idx) → Real) :
    (∑ idx : Fin (k + 1) → Idx, f idx) =
      ∑ a : Idx, ∑ rest : Fin k → Idx, f (Fin.cons a rest) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Idx)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl




theorem compNormSqMulti_eq_compNormSq5
    {Idx : Type*} [Fintype Idx] (A : (Fin 5 → Idx) → Real) :
    compNormSqMulti A =
      compNormSq5 (fun m a b c d : Idx => A ![m, a, b, c, d]) := by
  classical
  unfold compNormSqMulti compNormSq5
  rw [sum_pi_fin_succ (fun idx => (A idx) ^ 2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons m idx)) ^ 2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons m (Fin.cons a idx))) ^ 2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons m (Fin.cons a (Fin.cons b idx)))) ^ 2)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_pi_fin_succ (fun idx => (A (Fin.cons m (Fin.cons a (Fin.cons b (Fin.cons c idx))))) ^ 2)]
  refine Finset.sum_congr rfl fun d _ => ?_

  rw [Finset.sum_eq_single (default : Fin 0 → Idx)]
  ·
    have htuple :
        (Fin.cons m (Fin.cons a (Fin.cons b (Fin.cons c
          (Fin.cons d (default : Fin 0 → Idx))))) : Fin 5 → Idx) =
          ![m, a, b, c, d] := by
      funext p
      fin_cases p <;> rfl
    rw [htuple]
  · intro y _ hy
    exact absurd (Subsingleton.elim y default) hy
  · intro h; exact absurd (Finset.mem_univ _) h















omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem abs_nablaLapComm_T2_orthoFrame_le
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric t).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) ∧
      InverseMetricOrthonormalAt (M := M) (Idx := Fin n)
        (deltaInvMetric (M := M)) t x₀ ∧
      ∀ (a b c : Fin n) (m : Fin 4 → Fin n),
        |curvatureAction0SAt (I := I) (S.base.rm13 t) (nablaRm04Field (I := I) S t x₀)
            (frame a x₀) (frame c x₀)
            (nabla3InnerSlotsF (I := I) frame x₀ b m)| ≤
          (5 : Real) * (Fintype.card (Fin n) : Real) *
            (Real.sqrt (rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
                (deltaInvMetric (M := M)) frame t x₀) *
              Real.sqrt (compNormSqMulti (fun idx : Fin 5 → Fin n =>
                nablaRm04Field (I := I) S t x₀ (fun p => frame (idx p) x₀)))) := by
  classical
  obtain ⟨n, frame, basis, hframe, horth⟩ := exists_orthoBasisFrameAt (I := I) S t x₀
  refine ⟨n, frame, ?_, deltaInvMetric_orthonormal (M := M) t x₀, ?_⟩
  ·
    intro i j; rw [hframe i, hframe j]; exact horth i j
  · intro a b c m

    have hbnd :=
      abs_nablaLapComm_T2_orthoBasis_le (I := I) S t x₀ frame basis hframe horth a b c m

    have hRm :
        compNormSq4 (fun i j k l : Fin n =>
            S.base.rm04 t x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) =
          rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
            (deltaInvMetric (M := M)) frame t x₀ := by
      rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) (fun s => S.base.rm04 s)
        (deltaInvMetric (M := M)) frame t x₀ (deltaInvMetric_orthonormal (M := M) t x₀)]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [DifferentialGeometry.Integral.Connection.rm04Comp]
      rw [hframe i, hframe j, hframe k, hframe l]

    have hNab :
        compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S t x₀ (fun p => basis (idx p))) =
          compNormSqMulti (fun idx : Fin 5 → Fin n =>
            nablaRm04Field (I := I) S t x₀ (fun p => frame (idx p) x₀)) := by
      have hpt : ∀ idx : Fin 5 → Fin n,
          nablaRm04Field (I := I) S t x₀ (fun p => basis (idx p)) =
            nablaRm04Field (I := I) S t x₀ (fun p => frame (idx p) x₀) := by
        intro idx
        congr 1
        funext p; rw [hframe (idx p)]
      unfold compNormSqMulti
      refine Finset.sum_congr rfl fun idx _ => ?_
      dsimp only
      rw [hpt idx]
    rw [hRm, hNab] at hbnd
    exact hbnd

end SolutionBound

end DifferentialGeometry.PDE.RicciFlow
