import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannReactionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatSolution

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








section FrameInvariance

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]






omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricInverseInBasis_identity_of_orthonormal
    (g : SmoothMetric_gen I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  classical
  intro i j
  refine ⟨?_, ?_⟩
  ·
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]; exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hk h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  ·
    rw [Finset.sum_eq_single j]
    · rw [identityInvMetric_apply_self, mul_one]; exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h













omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem compNormSqMulti_orthoBasis_eq_normSq0S
    [FiniteDimensional Real E]
    (g : SmoothMetric_gen I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    compNormSqMulti (fun idx : Fin s → Idx => A (fun p => basis (idx p))) =
      normSq0S (I := I) g x s A := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth) A]
  unfold compNormSqMulti
  refine Finset.sum_congr rfl fun idx _ => ?_

  rfl

end FrameInvariance










section ProducerNorms

variable {n : ℕ}





omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem rm04NormSqInFrame_orthoBasis_eq_normSq0S
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
        (deltaInvMetric (M := M)) frame (t : Real) x₀ =
      normSq0S (I := I) (S.base.metric (t : Real)) x₀ 4 (S.base.rm04 (t : Real) x₀) := by
  classical

  rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) (fun s => S.base.rm04 s)
    (deltaInvMetric (M := M)) frame (t : Real) x₀
    (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]


  rw [← compNormSqMulti_orthoBasis_eq_normSq0S (I := I) (S.base.metric (t : Real))
    basis horth (S.base.rm04 (t : Real) x₀)]
  rw [compNormSqMulti_eq_compNormSq4_basis (I := I) (S.base.rm04 (t : Real) x₀) basis]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [DifferentialGeometry.Integral.Connection.rm04Comp]
  rw [hframe i, hframe j, hframe k, hframe l]





omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04NormSqInFrame_orthoBasis_eq_normSq0S
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (frame : Fin n → (x : M) → TangentSpace I x)
    (basis : Module.Basis (Fin n) Real (TangentSpace I x₀))
    (hframe : ∀ i : Fin n, frame i x₀ = basis i)
    (horth : ∀ i j : Fin n,
      (S.base.metric (t : Real)).inner x₀ (basis i) (basis j) =
        if i = j then (1 : Real) else 0) :
    nablaRm04NormSqInFrame (M := M)
        (fun s y i j k l p =>
          nablaRm04Field (I := I) S s y (vec5 (I := I)
            (frame i y) (frame j y) (frame k y) (frame l y) (frame p y)))
        (deltaInvMetric (M := M)) (t : Real) x₀ =
      normSq0S (I := I) (S.base.metric (t : Real)) x₀ 5
        (nablaRm04Field (I := I) S (t : Real) x₀) := by
  classical

  rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) _
    (deltaInvMetric (M := M)) (t : Real) x₀
    (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]

  rw [← compNormSqMulti_orthoBasis_eq_normSq0S (I := I) (S.base.metric (t : Real))
    basis horth (nablaRm04Field (I := I) S (t : Real) x₀)]
  rw [compNormSqMulti_eq_compNormSq5
    (fun idx : Fin 5 → Fin n =>
      nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))]
  refine Finset.sum_congr rfl fun mi _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  have htup : (fun p : Fin 5 => basis ((![mi, a, b, c, d] : Fin 5 → Fin n) p)) =
      vec5 (I := I) (frame mi x₀) (frame a x₀) (frame b x₀) (frame c x₀) (frame d x₀) := by
    funext p; fin_cases p <;> simp [vec5, hframe]
  rw [htup]

end ProducerNorms




























omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] in
theorem abs_spatialCommNablaRm_intrinsic_le
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M) :
    ∃ (n : ℕ) (frame : Fin n → (x : M) → TangentSpace I x),
      (∀ i j : Fin n,
        (S.family.metric (t : Real)).inner x₀ (frame i x₀) (frame j x₀) =
          if i = j then (1 : Real) else 0) ∧
      InverseMetricOrthonormalAt (M := M) (Idx := Fin n)
        (deltaInvMetric (M := M)) (t : Real) x₀ ∧
      ∀ (c : Fin n) (m : Fin 4 → Fin n),
        |roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame
            (deltaInvMetric (M := M) (Idx := Fin n) (t : Real) x₀) c m| ≤
          (13 : Real) * (Fintype.card (Fin n) : Real) ^ 2 *
            (Real.sqrt (normSq0S (I := I) (S.base.metric (t : Real)) x₀ 4
                (S.base.rm04 (t : Real) x₀)) *
              Real.sqrt (normSq0S (I := I) (S.base.metric (t : Real)) x₀ 5
                (nablaRm04Field (I := I) S (t : Real) x₀))) := by
  classical


  obtain ⟨n, frame, hortho, hinv, hbnd⟩ :=
    abs_spatialCommNablaRm_orthoFrame_le (I := I) S hS t x₀


  obtain ⟨n', frame', basis, hframe', horth'⟩ :=
    exists_orthoBasisFrameAt (I := I) S (t : Real) x₀



  refine ⟨n', frame', ?_, deltaInvMetric_orthonormal (M := M) (t : Real) x₀, ?_⟩
  · intro i j; rw [hframe' i, hframe' j]; exact horth' i j
  intro c m

  have hbnd' :
      |roughLapNablaRmCompF (I := I) S (t : Real) x₀ frame'
            (deltaInvMetric (M := M) (Idx := Fin n') (t : Real) x₀) c m -
          nablaRoughLapRmCompF (I := I) S (t : Real) x₀ frame'
            (deltaInvMetric (M := M) (Idx := Fin n') (t : Real) x₀) c m| ≤
        (13 : Real) * (Fintype.card (Fin n') : Real) ^ 2 *
          (Real.sqrt (rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
              (deltaInvMetric (M := M)) frame' (t : Real) x₀) *
            Real.sqrt (nablaRm04NormSqInFrame (M := M)
              (fun s y i j k l p =>
                nablaRm04Field (I := I) S s y (vec5 (I := I)
                  (frame' i y) (frame' j y) (frame' k y) (frame' l y) (frame' p y)))
              (deltaInvMetric (M := M)) (t : Real) x₀)) := by

    rw [nablaLapCommF_orthonormalTrace (I := I) S hS t x₀ frame'
      (deltaInvMetric (M := M) (Idx := Fin n') (t : Real) x₀) (fun i j => rfl) c m]
    have hreact := abs_nablaLapCommReactionTerm_diag_orthoBasis_le (I := I) S hS t x₀
      frame' basis hframe' horth' c m
    have hRm :
        compNormSq4 (fun i j k l : Fin n' =>
            S.base.rm04 (t : Real) x₀ (vec4 (I := I) (basis i) (basis j) (basis k) (basis l))) =
          rm04NormSqInFrame (I := I) (fun s => S.base.rm04 s)
            (deltaInvMetric (M := M)) frame' (t : Real) x₀ := by
      rw [rm04NormSqInFrame_eq_compNormSq4 (I := I) (fun s => S.base.rm04 s)
        (deltaInvMetric (M := M)) frame' (t : Real) x₀
        (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [DifferentialGeometry.Integral.Connection.rm04Comp]
      rw [hframe' i, hframe' j, hframe' k, hframe' l]
    have hNab :
        compNormSqMulti (fun idx : Fin 5 → Fin n' =>
            nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p))) =
          nablaRm04NormSqInFrame (M := M)
            (fun s y i j k l p =>
              nablaRm04Field (I := I) S s y (vec5 (I := I)
                (frame' i y) (frame' j y) (frame' k y) (frame' l y) (frame' p y)))
            (deltaInvMetric (M := M)) (t : Real) x₀ := by
      rw [nablaRm04NormSqInFrame_eq_compNormSq5 (M := M) _
        (deltaInvMetric (M := M)) (t : Real) x₀
        (deltaInvMetric_orthonormal (M := M) (t : Real) x₀)]
      rw [compNormSqMulti_eq_compNormSq5
        (fun idx : Fin 5 → Fin n' =>
          nablaRm04Field (I := I) S (t : Real) x₀ (fun p => basis (idx p)))]
      refine Finset.sum_congr rfl fun mi _ => ?_
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c' _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      dsimp only
      have htup : (fun p : Fin 5 => basis ((![mi, a, b, c', d] : Fin 5 → Fin n') p)) =
          vec5 (I := I) (frame' mi x₀) (frame' a x₀) (frame' b x₀) (frame' c' x₀) (frame' d x₀) := by
        funext p; fin_cases p <;> simp [vec5, hframe']
      rw [htup]
    rw [hRm, hNab] at hreact
    exact hreact

  rw [rm04NormSqInFrame_orthoBasis_eq_normSq0S (I := I) S t x₀ frame' basis hframe' horth',
    nablaRm04NormSqInFrame_orthoBasis_eq_normSq0S (I := I) S t x₀ frame' basis hframe' horth']
    at hbnd'
  exact hbnd'












































end DifferentialGeometry.PDE.RicciFlow
