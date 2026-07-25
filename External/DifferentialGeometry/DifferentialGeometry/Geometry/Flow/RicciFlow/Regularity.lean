import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]






omit [SigmaCompactSpace M] in
theorem scalarSmoothOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (S.scalar t) := by
  simpa [SolutionOn.scalar, SolutionFamily.scalar] using
    metricScalar_smooth (I := I) (M := M) (S.family.metric t)



omit [SigmaCompactSpace M] in
theorem scalarContOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ContinuousOn (fun q : Real × M => S.scalar q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)) := by
  exact hS.scalarCont



omit [SigmaCompactSpace M] in
theorem scalarTimeOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {K : Set Real} {t : Real} (ht : t ∈ K) (hK : K ⊆ D.carrier)
    (x : M) :
    DifferentiableWithinAt Real (fun s : Real => S.scalar s x) K t := by
  exact hS.scalarTime ht hK x


omit [SigmaCompactSpace M] in
theorem scalarRegOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    CanonicalScalarRegularOn (I := I) (M := M) S := by
  classical
  refine
    { scalar_continuousOn := ?_
      scalar_time_within := ?_
      scalar_space := ?_
      scalar_grad := ?_
      scalar_mul_grad := ?_
      scalar_sq_space := ?_
      scalar_sq_grad := ?_
      scalar_sq_div_space := ?_
      scalar_sq_div_grad := ?_
      scalar_grad_sub_const := ?_
      scalar_grad_const_mul_sub_const := ?_ }
  · exact scalarContOfSol (I := I) S hS
  · intro K t ht hK x
    exact scalarTimeOfSol (I := I) S hS ht hK x
  · intro t ht x
    exact ((scalarSmoothOfSol (I := I) S t).contMDiffAt).mdifferentiableAt
      (by simp)
  · intro t ht x
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I) (S.family.metric t)
      (scalarSmoothOfSol (I := I) S t) x
  · intro t ht x
    have hsmooth := scalarSmoothOfSol (I := I) S t
    have hspace : ∀ y : M,
        MDifferentiableAt I 𝓘(Real, Real) (S.scalar t) y := by
      intro y
      exact hsmooth.contMDiffAt.mdifferentiableAt (by simp)
    have hgrad : ∀ y : M,
        MDiffAt (T% fun z : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric t) (S.scalar t) z) y := by
      intro y
      exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I) (S.family.metric t) hsmooth y
    exact DifferentialGeometry.Integral.Connection.scalar_mul_grad_mdiffAt (I := I) (S.family.metric t)
      hspace hgrad
  · intro t ht x
    have hsmooth := scalarSmoothOfSol (I := I) S t
    have hsq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => S.scalar t y ^ 2) := by
      have hmul : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M => S.scalar t y * S.scalar t y) :=
        hsmooth.mul hsmooth
      simpa [pow_two] using hmul
    exact hsq.contMDiffAt.mdifferentiableAt (by simp)
  · intro t ht x
    have hsmooth := scalarSmoothOfSol (I := I) S t
    have hsq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => S.scalar t y ^ 2) := by
      have hmul : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M => S.scalar t y * S.scalar t y) :=
        hsmooth.mul hsmooth
      simpa [pow_two] using hmul
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I) (S.family.metric t) hsq x
  · intro t ht x
    have hsmooth := scalarSmoothOfSol (I := I) S t
    have hsq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => S.scalar t y ^ 2) := by
      have hmul : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M => S.scalar t y * S.scalar t y) :=
        hsmooth.mul hsmooth
      simpa [pow_two] using hmul
    have hsqDiv : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => S.scalar t y ^ 2 / 3) := by
      simpa [div_eq_mul_inv] using hsq.mul contMDiff_const
    exact hsqDiv.contMDiffAt.mdifferentiableAt (by simp)
  · intro t ht x
    have hsmooth := scalarSmoothOfSol (I := I) S t
    have hsq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => S.scalar t y ^ 2) := by
      have hmul : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M => S.scalar t y * S.scalar t y) :=
        hsmooth.mul hsmooth
      simpa [pow_two] using hmul
    have hsqDiv : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => S.scalar t y ^ 2 / 3) := by
      simpa [div_eq_mul_inv] using hsq.mul contMDiff_const
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I) (S.family.metric t) hsqDiv x
  · intro t ht c x
    have hsmooth := scalarSmoothOfSol (I := I) S t
    have hshift : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun z : M => S.scalar t z - c) :=
      hsmooth.sub contMDiff_const
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I) (S.family.metric t) hshift x
  · intro t ht a c x
    have hsmooth := scalarSmoothOfSol (I := I) S t
    have hshift : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun z : M => S.scalar t z - c) :=
      hsmooth.sub contMDiff_const
    have hscaled : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun z : M => a * (S.scalar t z - c)) :=
      contMDiff_const.mul hshift
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I) (S.family.metric t) hscaled x







omit [SigmaCompactSpace M] in
theorem scalarSTContOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ScalarSTContOn (I := I) (M := M) S := by
  exact CanonicalScalarRegularOn.toScalarSTCont (I := I) (M := M)
    (scalarRegOfSol (I := I) S hS)



omit [SigmaCompactSpace M] in
theorem ricciRegOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    CanonicalRicciRegularOn (I := I) (M := M) S := by
  exact
    { ricci_cont := hS.ricciCont
      rm04_cont := hS.rm04Cont
      ricci_norm_space := hS.ricciNormSpace
      ricci_norm_grad := hS.ricciNormGrad }


theorem scalarEvolOfSol
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ∀ (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real),
      (∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        G.metric (t : Real) = S.family.metric (t : Real)) ->
      (∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        G.connection (t : Real) = S.family.connection (t : Real)) ->
      ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
        HasDerivWithinAt
          (fun s : Real => S.scalar s x)
          (DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G (t : Real)
              (S.scalar (t : Real)) x +
            2 * normSq0S (I := I) (S.family.metric (t : Real)) x 2
              (S.ricci (t : Real) x))
          D.carrier
          (t : Real) := by
  exact scalarEvolution_of_isSolution (I := I) S hS



theorem invEvolOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) :
    InverseMetricEvolutionEquationInFrame
      (I := I) S (coordInv (I := I) S x0)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0) := by
  exact coordInvEvol (I := I) S hS x0


theorem ricciEvolOfSol
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x0 : M) (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) s x0 i j)
      (ricciEvolutionRHSInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x0)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
        (coordRoughRic (I := I) S x0 (coordNab2Ric (I := I) S x0))
        (t : Real) x0 i j)
      D.carrier
      (t : Real) := by
  exact coordRicciEvol (I := I) S hS x0 t i j



theorem invSymmOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (x0 : M) :
    ∀ t i j,
      coordInv (I := I) S x0 t x0 i j =
        coordInv (I := I) S x0 t x0 j i := by
  intro t i j
  simpa [coordInv] using
    DifferentialGeometry.Tensor.Coordinates.gInvChart_symm (I := I) (S.family.metric t) x0
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x0) i j


theorem ricciSymmOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (x0 : M) :
    ∀ t i j,
      ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x0 i j =
        ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x0 j i := by
  intro t i j
  have hinv := coordInvReal (I := I) S x0 t
  have hsym :=
    DifferentialGeometry.Integral.Connection.metricRicciSymm (I := I) (M := M) (S.family.metric t)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x0)
      (fun a b => coordInv (I := I) S x0 t x0 a b) hinv i j
  simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt] using hsym








theorem coordNab2_can
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x0 : M)
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 4)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 3 (S.family.connection t) nablaA nabla2A)
    (hnabla : ∀ y a i j,
      nablaA y
          (DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 a y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 i y)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 j y)) =
        nablaRicComp (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t y a i j) :
    ∀ d a i j,
      nabla2A x0
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 d x0)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 a x0)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 i x0)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0 j x0)) =
        coordNab2Ric (I := I) S x0 t x0 d a i j := by
  classical
  intro d a i j
  let Idx := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0
  let hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x0
  have hx0 : x0 ∈ DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0 :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x0
  let V : Fin 3 -> (x : M) -> TangentSpace I x :=
    fun q y => if q = 0 then frame a y else if q = 1 then frame i y else frame j y
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x0 (frame d x0)).choose
  have hX : X x0 = frame d x0 := by
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x0 (frame d x0)).choose_spec
  have hframeAt (r : Idx) :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x0 := by
    have htop :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, frame r y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x0 := by
      simpa [frame] using
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_isLocalFrame (I := I) x0).contMDiffAt
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x0)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x0) r
    exact htop.of_le (by simp)
  have hV_at : ∀ q : Fin 3,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x0 := by
    intro q
    fin_cases q
    · simpa [V] using hframeAt a
    · simpa [V] using hframeAt i
    · simpa [V] using hframeAt j
  have hslots3 : ∀ y,
      (fun q : Fin 3 => V q y) =
        DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a y) (frame i y) (frame j y) := by
    intro y
    funext q
    fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
  have hslots4 :
      Fin.cons (X x0) (fun q : Fin 3 => V q x0) =
        DifferentialGeometry.Integral.Connection.vec4 (I := I) (frame d x0) (frame a x0) (frame i x0)
          (frame j x0) := by
    rw [hX, hslots3 x0]
    funext q
    fin_cases q <;> rfl
  have hfun :
      (fun y : M => nablaA y (fun q : Fin 3 => V q y)) =
        fun y : M =>
          nablaRicComp (I := I) S (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            t y a i j := by
    funext y
    rw [hslots3 y]
    simpa [frame] using hnabla y a i j
  have heval :=
    TotalNabla0SRealizes.eval_C1_slots (I := I) h2 X V x0 hV_at
  rw [hslots4, hfun, hX] at heval
  let Γ : Idx -> Idx -> Idx -> Real :=
    fun u v p =>
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (S.family.connection t) frame hframe x0 u v p
  let N : Idx -> Idx -> Idx -> Real :=
    fun u v w =>
      nablaRicComp (I := I) S (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
        t x0 u v w
  have hterm0 :
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
            ((S.family.connection t) (V 0) x0 (frame d x0))) =
        ∑ p : Idx, Γ d a p * N p i j := by
    have hV0 : V 0 = frame a := by
      funext y
      simp [V]
    have hcov :
        (S.family.connection t) (V 0) x0 (frame d x0) =
          ∑ p : Idx, Γ d a p • frame p x0 := by
      rw [hV0]
      simpa [Γ] using
        DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel
          (𝕜 := Real) (I := I) (cov := S.family.connection t)
          (frame := frame) (hframe := hframe) hx0 d a
    have hsum := (nablaA x0).toMultilinearMap.map_update_sum
      (Finset.univ : Finset Idx) (0 : Fin 3)
      (fun p : Idx => Γ d a p • frame p x0)
      (fun b : Fin 3 => V b x0)
    calc
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
            ((S.family.connection t) (V 0) x0 (frame d x0))) =
        nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
            (∑ p : Idx, Γ d a p • frame p x0)) := by
          rw [hcov]
      _ = ∑ p : Idx,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3)
                (Γ d a p • frame p x0)) := by
          exact hsum
      _ = ∑ p : Idx, Γ d a p * N p i j := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [(nablaA x0).map_update_smul]
          have hslot :
              Function.update (fun b : Fin 3 => V b x0) (0 : Fin 3) (frame p x0) =
                DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame p x0) (frame i x0) (frame j x0) := by
            funext q
            fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
          rw [hslot]
          rw [hnabla x0 p i j]
          simp [N, smul_eq_mul]
  have hterm1 :
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
            ((S.family.connection t) (V 1) x0 (frame d x0))) =
        ∑ p : Idx, Γ d i p * N a p j := by
    have hV1 : V 1 = frame i := by
      funext y
      simp [V]
    have hcov :
        (S.family.connection t) (V 1) x0 (frame d x0) =
          ∑ p : Idx, Γ d i p • frame p x0 := by
      rw [hV1]
      simpa [Γ] using
        DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel
          (𝕜 := Real) (I := I) (cov := S.family.connection t)
          (frame := frame) (hframe := hframe) hx0 d i
    have hsum := (nablaA x0).toMultilinearMap.map_update_sum
      (Finset.univ : Finset Idx) (1 : Fin 3)
      (fun p : Idx => Γ d i p • frame p x0)
      (fun b : Fin 3 => V b x0)
    calc
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
            ((S.family.connection t) (V 1) x0 (frame d x0))) =
        nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
            (∑ p : Idx, Γ d i p • frame p x0)) := by
          rw [hcov]
      _ = ∑ p : Idx,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3)
                (Γ d i p • frame p x0)) := by
          exact hsum
      _ = ∑ p : Idx, Γ d i p * N a p j := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [(nablaA x0).map_update_smul]
          have hslot :
              Function.update (fun b : Fin 3 => V b x0) (1 : Fin 3) (frame p x0) =
                DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x0) (frame p x0) (frame j x0) := by
            funext q
            fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
          rw [hslot]
          rw [hnabla x0 a p j]
          simp [N, smul_eq_mul]
  have hterm2 :
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
            ((S.family.connection t) (V 2) x0 (frame d x0))) =
        ∑ p : Idx, Γ d j p * N a i p := by
    have hV2 : V 2 = frame j := by
      funext y
      simp [V]
    have hcov :
        (S.family.connection t) (V 2) x0 (frame d x0) =
          ∑ p : Idx, Γ d j p • frame p x0 := by
      rw [hV2]
      simpa [Γ] using
        DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel
          (𝕜 := Real) (I := I) (cov := S.family.connection t)
          (frame := frame) (hframe := hframe) hx0 d j
    have hsum := (nablaA x0).toMultilinearMap.map_update_sum
      (Finset.univ : Finset Idx) (2 : Fin 3)
      (fun p : Idx => Γ d j p • frame p x0)
      (fun b : Fin 3 => V b x0)
    calc
      nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
            ((S.family.connection t) (V 2) x0 (frame d x0))) =
        nablaA x0
          (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
            (∑ p : Idx, Γ d j p • frame p x0)) := by
          rw [hcov]
      _ = ∑ p : Idx,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3)
                (Γ d j p • frame p x0)) := by
          exact hsum
      _ = ∑ p : Idx, Γ d j p * N a i p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [(nablaA x0).map_update_smul]
          have hslot :
              Function.update (fun b : Fin 3 => V b x0) (2 : Fin 3) (frame p x0) =
                DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x0) (frame i x0) (frame p x0) := by
            funext q
            fin_cases q <;> simp [V, DifferentialGeometry.Integral.Connection.vec3, DifferentialGeometry.Integral.Connection.vec3]
          rw [hslot]
          rw [hnabla x0 a i p]
          simp [N, smul_eq_mul]
  have hcorr :
      (∑ q : Fin 3,
          nablaA x0
            (Function.update (fun b : Fin 3 => V b x0) q
            ((S.family.connection t) (V q) x0 (frame d x0)))) =
        (∑ p : Idx, Γ d a p * N p i j) +
          (∑ p : Idx, Γ d i p * N a p j) +
            (∑ p : Idx, Γ d j p * N a i p) := by
    rw [Fin.sum_univ_three]
    rw [hterm0, hterm1, hterm2]
  calc
    nabla2A x0
        (DifferentialGeometry.Integral.Connection.vec4 (I := I) (frame d x0) (frame a x0) (frame i x0)
          (frame j x0)) =
        extDerivFun (I := I)
          (fun y : M =>
            nablaRicComp (I := I) S (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
              t y a i j) x0 (frame d x0) -
          (∑ q : Fin 3,
            nablaA x0
              (Function.update (fun b : Fin 3 => V b x0) q
                ((S.family.connection t) (V q) x0 (frame d x0)))) := heval
    _ = coordNab2Ric (I := I) S x0 t x0 d a i j := by
          rw [coordNab2Ric]
          dsimp [frame, Γ, N]
          rw [hcorr]
          ring



theorem coordRough_can
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M)
    (nabla2A :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 4)
    (hnab2 : ∀ a b i j,
      nabla2A x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) =
        coordNab2Ric (I := I) S x t x a b i j)
    (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
    DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) (S.family.metric t) (nabla2A x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) =
      coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j := by
  classical
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun a b => coordInv (I := I) S x t x a b
  have htrace :=
    DifferentialGeometry.Integral.Connection.metricTraceFirstTwo0SAt_eq_sum_basis
      (I := I) (S.family.metric t) basis gInv
      (coordInvReal (I := I) S x t) (nabla2A x)
      (DifferentialGeometry.Integral.Connection.vec2 (I := I)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x))
  calc
    DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) (S.family.metric t) (nabla2A x)
        (DifferentialGeometry.Integral.Connection.vec2 (I := I)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) =
        DifferentialGeometry.Integral.Connection.metricTraceFirstTwo0SAt (I := I) (S.family.metric t)
          (nabla2A x)
          (DifferentialGeometry.Integral.Connection.vec2 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) := by
          rw [DifferentialGeometry.Integral.Connection.roughLap0STensor_apply]
    _ =
        DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis (I := I) basis gInv (nabla2A x)
          (DifferentialGeometry.Integral.Connection.vec2 (I := I)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) := htrace
    _ = coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x i j := by
          unfold DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis coordRoughRic basis gInv
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b _ => ?_
          have hinput :
              DifferentialGeometry.Integral.Connection.metricTraceInput (I := I)
                  ((DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x) a)
                  ((DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x) b)
                  (DifferentialGeometry.Integral.Connection.vec2 (I := I)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
                    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x)) =
                DifferentialGeometry.Integral.Connection.vec4 (I := I)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x)
                  (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x j x) := by
            rw [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply,
              DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
            funext q
            fin_cases q <;> rfl
          rw [hinput, hnab2 a b i j]



theorem ricciLapOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S) :
    ∀ t x,
      ricciNormLap (I := I) S t x =
        2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x))
              (coordInv (I := I) S x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x +
          2 * ricciGradSq (I := I) S t x := by
  classical
  intro t x
  let Idx := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real := flowG (I := I) S
  let basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x) :=
    fun x => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    fun i x => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x i x
  let gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx :=
    fun t x i j => coordInv (I := I) S x t x i j
  have hcov : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.base.connection t) (∞ : WithTop ℕ∞) := by
    intro t
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let derivs : (t : Real) ->
      CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) (S.base.connection t) (S.ricci t) :=
    fun t =>
      CanonicalSpatialDerivs0S.of_smooth_connection
        (E := E) (H := H) (I := I) (M := M)
        (S.base.connection t) (hcov t) (S.ricci t)
  let A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    fun t => S.ricci t
  let nablaA : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3 :=
    fun t => (derivs t).nablaA
  let nabla2A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4 :=
    fun t => (derivs t).nabla2A
  let roughA : Real -> (x : M) -> DifferentialGeometry.Integral.Connection.Tensor02At (I := I) x :=
    fun t x => DifferentialGeometry.Integral.Connection.roughLap0STensor (I := I) (S.base.metric t) (nabla2A t x)
  let f : Real -> M -> Real :=
    fun t y => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (S.base.metric t) y (A t y)
  have hf : ∀ t : Real,
      ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (f t) := by
    intro t
    simpa [f, A] using
      DifferentialGeometry.Integral.Connection.norm02_smooth (I := I) (M := M) (S.base.metric t) (S.ricci t)
  let du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 :=
    fun t => DifferentialGeometry.Integral.Connection.duSec (I := I) (f t) (hf t)
  let normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y :=
    fun t y => DifferentialGeometry.Integral.Connection.hessianSec (I := I) (S.base.connection t) (hcov t)
      (f t) (hf t) y
  let X : (x : M) -> Idx ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun x i =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis x i)).choose
  have hframe : ∀ x i, basis x i = frame i x := by
    intro x i
    exact DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply (I := I) x i
  have hinv : ∀ t x,
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) (G.metric t) x
        (basis x) (gInv t x) := by
    intro t x
    simpa [G, basis, gInv, flowG] using coordInvReal (I := I) S x t
  have hfields : ∀ x, DifferentialGeometry.Integral.Connection.SmoothBasisFieldsAt (I := I) (basis x) (X x) := by
    intro x i
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis x i)).choose_spec
  have hlapTrace : ∀ t x,
      ricciNormLap (I := I) S t x =
        DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0 := by
    intro t x
    have hlap :=
      DifferentialGeometry.Integral.Connection.scalarLap_smooth (I := I) (x := x) (S.base.connection t) (hcov t)
        (S.base.metric t) (G.metricCompatible t) (f t) (hf t)
    have hbasis :=
      DifferentialGeometry.Integral.Connection.ScalarLaplacianRealizesTraceAt.toInBasis
        (I := I) (S.base.connection t) (S.base.metric t) (basis x)
        (gInv t x) (hinv t x) (f t) (normSecond t x) hlap
    simpa [ricciNormLap, flowG, G, DifferentialGeometry.Integral.Connection.laplacianAt, ricciNorm, f, A,
      DifferentialGeometry.Integral.Connection.normSq02, DifferentialGeometry.Integral.Connection.inner02, Tensor0SBundle.normSq0S,
      normSecond] using hbasis
  have hA : ∀ t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (G.connection t) (A t) (nablaA t) := by
    intro t
    simpa [G, flowG, A, nablaA, derivs] using (derivs t).first
  have h2 : ∀ t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 3 (G.connection t) (nablaA t) (nabla2A t) := by
    intro t
    simpa [G, flowG, nablaA, nabla2A, derivs] using (derivs t).second
  have hdu : ∀ t,
      DifferentialGeometry.Integral.Connection.DuFieldRealizes (I := I) (f t) (du t) := by
    intro t
    simpa [du] using DifferentialGeometry.Integral.Connection.duSec_realizes (I := I) (f t) (hf t)
  have hHess : ∀ t x,
      DifferentialGeometry.Integral.Connection.HessianRealizesNablaDuAt (I := I) (G.connection t) (du t)
        (normSecond t) x := by
    intro t x
    simpa [G, flowG, du, normSecond] using
      DifferentialGeometry.Integral.Connection.hessianSec_realizesAt (I := I) (S.base.connection t) (hcov t)
        (f t) (hf t) x
  have hrough : ∀ t x,
      DifferentialGeometry.Integral.Connection.RoughLap0SRealizesMetricTraceInBasis (I := I)
        (basis x) (gInv t x) (s := 2) (roughA t x) (nabla2A t x) := by
    intro t x tail
    exact
      DifferentialGeometry.Integral.Connection.rough_lap_0s_apply_basis (I := I) (S.base.metric t)
        (basis x) (gInv t x) (nabla2A t x) (roughA t x)
        (DifferentialGeometry.Integral.Connection.roughLap0STensor_realizes (I := I) (S.base.metric t)
          (nabla2A t x))
        (by simpa [G, flowG] using hinv t x) tail
  have hAComp : ∀ t x i j,
      A t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        ricciTwoTensorField (I := I) S t x (frame i x) (frame j x) := by
    intro t x i j
    simp [A, ricciTwoTensorField]
  have hnablaComp : ∀ t x a i j,
      nablaA t x (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRicComp (I := I) S frame t x a i j := by
    intro t x a i j
    simp [nablaA, derivs, nablaRicComp, frame,
      CanonicalSpatialDerivs0S.of_smooth_connection]
  let roughLapRic : Real -> M -> Idx -> Idx -> Real :=
    fun t x => coordRoughRic (I := I) S x (coordNab2Ric (I := I) S x) t x
  have hroughComp : ∀ t x i j,
      roughA t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j := by
    intro t x i j
    have hnablaFixed : ∀ y a b c,
        nablaA t y
            (DifferentialGeometry.Integral.Connection.vec3 (I := I)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x a y)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x b y)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x c y)) =
          nablaRicComp (I := I) S
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t y a b c := by
      intro y a b c
      simp [nablaA, derivs, nablaRicComp,
        CanonicalSpatialDerivs0S.of_smooth_connection]
    have hnab2 :=
      coordNab2_can (I := I) S t x (nablaA t) (nabla2A t)
        (by simpa [G, flowG] using h2 t)
        hnablaFixed
    simpa [roughA, roughLapRic, frame] using
      coordRough_can (I := I) S t x (nabla2A t) hnab2 i j
  have h_lap :
      DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
        (I := I) (M := M) (Time := Real) (ricciNormLap (I := I) S)
        roughLapRic (ricciTwoTensorField (I := I) S) gInv frame
        (nablaRicComp (I := I) S frame) := by
    exact
      DifferentialGeometry.Integral.Connection.ricci_lap_mc (I := I) (M := M) (Time := Real) G
        (ricciNormLap (I := I) S) roughLapRic (ricciTwoTensorField (I := I) S)
        gInv frame (nablaRicComp (I := I) S frame) basis X A roughA
        nablaA nabla2A du normSecond hframe hinv hfields hlapTrace hA h2 hdu
        hHess hrough hAComp hroughComp hnablaComp
  have hcomp :=
    ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
      (I := I) S gInv frame roughLapRic (ricciNormLap (I := I) S)
      (nablaRicComp (I := I) S frame) h_lap
  have hnabla :=
    nablaRicciNorm_can (I := I) S gInv frame (basis x) (hinv t x)
      (hframe x)
  have hval := hcomp t x
  rw [hnabla] at hval
  simpa [roughLapRic, gInv, frame] using hval







theorem smoothOfSol
    [I.Boundaryless]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    IsSmoothSolutionOn (I := I) (M := M) S := by
  exact
    { isSolution := hS
      scalarSTCont := scalarSTContOfSol (I := I) S hS
      scalarRegular := scalarRegOfSol (I := I) S hS
      ricciRegular := ricciRegOfSol (I := I) S hS
      scalarEvolution := scalarEvolOfSol (I := I) S hS
      invEvol := invEvolOfSol (I := I) S hS
      ricciEvol := ricciEvolOfSol (I := I) S hS
      invSymm := invSymmOfSol (I := I) S hS
      ricciSymm := ricciSymmOfSol (I := I) S hS
      ricciLap := ricciLapOfSol (I := I) S hS }

end DifferentialGeometry.PDE.RicciFlow
