import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci

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




structure TFLapReg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) : Prop where
  ricci_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (ricciNorm (I := I) S t) y
  ricci_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric t)
          (ricciNorm (I := I) S t) y) x
  scalar_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar t) y
  scalar_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric t) (S.scalar t) y) x
  scalar_sq_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => S.scalar t z ^ 2) y
  scalar_sq_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2) y) x
  scalar_sq_div_space :
    ∀ t : Real, t ∈ D.carrier -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => S.scalar t z ^ 2 / 3) y
  scalar_sq_div_grad :
    ∀ t : Real, t ∈ D.carrier -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (S.family.metric t)
          (fun z : M => S.scalar t z ^ 2 / 3) y) x







theorem tfLapReg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    TFLapReg (I := I) S := by
  exact
    { ricci_space := hS.ricciRegular.ricci_norm_space
      ricci_grad := hS.ricciRegular.ricci_norm_grad
      scalar_space := hS.scalarRegular.scalar_space
      scalar_grad := hS.scalarRegular.scalar_grad
      scalar_sq_space := hS.scalarRegular.scalar_sq_space
      scalar_sq_grad := hS.scalarRegular.scalar_sq_grad
      scalar_sq_div_space := hS.scalarRegular.scalar_sq_div_space
      scalar_sq_div_grad := hS.scalarRegular.scalar_sq_div_grad }



theorem tfLapCore
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    ∀ t, t ∈ D.carrier -> ∀ x,
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x =
        ricciNormLap (I := I) S t x -
          (2 * S.scalar t x *
              DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x +
            2 * (S.family.metric t).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)) / 3 := by
  intro t ht x
  let G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real :=
    flowG (I := I) S
  have hreg := tfLapReg (I := I) S hS
  have hsq :
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (fun y : M => S.scalar t y ^ 2) x =
        2 * S.scalar t x * DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
            (S.scalar t) x +
          2 * (G.metric t).inner x
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (S.scalar t) x)
            (DifferentialGeometry.Integral.Connection.gradientAt (I := I) G t (S.scalar t) x) :=
    DifferentialGeometry.Integral.Connection.laplacianAt_sq_of_scalarRegular (I := I) G t
      (hreg.scalar_space t ht) (hreg.scalar_grad t ht)
  have hdivFun :
      (fun y : M => S.scalar t y ^ 2 / 3) =
        ((1 / 3 : Real) • fun y : M => S.scalar t y ^ 2) := by
    funext y
    simp [Pi.smul_apply]
    ring
  have hdiv :
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (fun y : M => S.scalar t y ^ 2 / 3) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (fun y : M => S.scalar t y ^ 2) x / 3 := by
    rw [hdivFun]
    rw [DifferentialGeometry.Integral.Connection.laplacianAt_smul (I := I) G t (1 / 3 : Real)
      (hreg.scalar_sq_space t ht) (hreg.scalar_sq_grad t ht x)]
    ring
  have hsub :
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x =
          DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (ricciNorm (I := I) S t) x -
          DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
            (fun y : M => S.scalar t y ^ 2 / 3) x :=
    DifferentialGeometry.Integral.Connection.laplacianAt_sub (I := I) G t
      (hreg.ricci_space t ht) (hreg.scalar_sq_div_space t ht)
      (hreg.ricci_grad t ht x) (hreg.scalar_sq_div_grad t ht x)
  calc
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x =
        DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
          (fun y : M =>
            ricciNorm (I := I) S t y - S.scalar t y ^ 2 / 3) x := rfl
    _ = DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (ricciNorm (I := I) S t) x -
          DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t
            (fun y : M => S.scalar t y ^ 2 / 3) x := hsub
    _ = ricciNormLap (I := I) S t x -
          (2 * S.scalar t x *
              DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x +
            2 * (S.family.metric t).inner x
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
              (DifferentialGeometry.Integral.Connection.gradientAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)) / 3 := by
          rw [hdiv, hsq]
          simp [G, ricciNormLap, flowG]







structure RicciHeatData
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) where
  roughLapInner : Real -> M -> Real
  timeDeriv :
    RicciNormTimeDerivativeComponentsOn
      (D := D) (ricciNorm (I := I) S) roughLapInner (ricciReact (I := I) S)
  laplacian :
    RicciNormLaplacianComponentsOn
      (ricciNormLap (I := I) S) roughLapInner (ricciGradSq (I := I) S)



theorem ricciHeat_of_data
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (h : RicciHeatData (I := I) S) :
    RicciNormHeatEquationOn
      (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
      (ricciGradSq (I := I) S) (ricciReact (I := I) S) := by
  exact
    ricciNormHeatEquationOn_of_components
      (D := D)
      (ricciNorm (I := I) S)
      (ricciNormLap (I := I) S)
      h.roughLapInner
      (ricciGradSq (I := I) S)
      (ricciReact (I := I) S)
      h.timeDeriv
      h.laplacian


omit [FiniteDimensional ℝ E] in
@[simp]
theorem ricciPair04_apply {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (v : Fin 4 -> TangentSpace I x) :
    ricciPair04 (I := I) Ric v =
      Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v 0) (v 2)) *
        Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (v 1) (v 3)) := by
  unfold ricciPair04
  have hdom :
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (1 : Fin 4) (2 : Fin 4))
        (Bundle.continuousMultilinearMap.product_fun
          (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
          (s := 2) (q := 2) (x := x) Ric Ric)) v =
        (Bundle.continuousMultilinearMap.product_fun
          (𝕜 := Real) (B := M) (F := E) (E := TangentSpace I)
          (s := 2) (q := 2) (x := x) Ric Ric)
          (fun i => v ((Equiv.swap (1 : Fin 4) (2 : Fin 4)) i)) := by
    with_unfolding_all rfl
  refine hdom.trans ?_
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hswap0 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 0 = 0 := by decide
  have hswap1 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 1 = 2 := by decide
  have hswap2 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 2 = 1 := by decide
  have hswap3 : (Equiv.swap (1 : Fin 4) (2 : Fin 4)) 3 = 3 := by decide
  congr 2 <;> funext a <;> fin_cases a <;>
    simp [hswap0, hswap1, hswap2, hswap3, DifferentialGeometry.Integral.Connection.vec2,
      DifferentialGeometry.Integral.Connection.vec2]

private def slot4ikjl {Idx : Type*} (i j k l : Idx) : Fin 4 -> Idx :=
  fun a => if a = 0 then i else if a = 1 then k else if a = 2 then j else l

private def fin4ikjl {Idx : Type*} :
    (Fin 4 -> Idx) ≃ (((Idx × Idx) × Idx) × Idx) where
  toFun u := (((u 0, u 2), u 1), u 3)
  invFun p := slot4ikjl p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv u := by
    funext a
    fin_cases a <;> simp [slot4ikjl]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slot4ikjl]

private theorem sumFin4Slot {Idx α : Type*} [Fintype Idx] [AddCommMonoid α]
    (F : (Fin 4 -> Idx) -> α) :
    (∑ u : Fin 4 -> Idx, F u) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F (slot4ikjl i j k l) := by
  rw [Fintype.sum_equiv (fin4ikjl (Idx := Idx)) F
    (fun p : (((Idx × Idx) × Idx) × Idx) =>
      F (slot4ikjl p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro u
    congr 1
    exact ((fin4ikjl (Idx := Idx)).left_inv u).symm

private theorem sumPairProd {Idx : Type*} [Fintype Idx]
    (A B : Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ c : Idx, A a c) *
        (∑ b : Idx, ∑ d : Idx, B b d) =
      ∑ a : Idx, ∑ c : Idx, ∑ b : Idx, ∑ d : Idx, A a c * B b d := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

omit [FiniteDimensional ℝ E] in
private theorem pairSum_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i j k l : Idx) :
    (∑ u : Fin 4 -> Idx,
      (∏ q : Fin 4, gInv (slot4ikjl i j k l q) (u q)) *
        ricciPair04 (I := I) Ric (fun q : Fin 4 => basis (u q))) =
      (∑ a : Idx, ∑ c : Idx,
        gInv i a * gInv j c *
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis c))) *
      (∑ b : Idx, ∑ d : Idx,
        gInv k b * gInv l d *
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis b) (basis d))) := by
  classical
  rw [sumFin4Slot]
  trans
      ∑ a : Idx, ∑ c : Idx, ∑ b : Idx, ∑ d : Idx,
        (gInv i a * gInv j c *
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis c))) *
        (gInv k b * gInv l d *
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis b) (basis d)))
  · refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [slot4ikjl, ricciPair04_apply, Fin.prod_univ_four]
    ring_nf
  · exact (sumPairProd
      (fun a c : Idx =>
        gInv i a * gInv j c *
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis c)))
      (fun b d : Idx =>
        gInv k b * gInv l d *
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis b) (basis d)))).symm

omit [FiniteDimensional ℝ E] in
private theorem coordPair4_eq
    {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx -> Idx -> Real)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 4 gInv Rm04
        (ricciPair04 (I := I) Ric) basis =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (∑ a : Idx, ∑ c : Idx,
            gInv i a * gInv j c *
              Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis c))) *
          (∑ b : Idx, ∑ d : Idx,
            gInv k b * gInv l d *
              Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis b) (basis d))) := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sumFin4Slot]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  calc
    (∑ u : Fin 4 -> Idx,
        ((∏ q : Fin 4, gInv (slot4ikjl i j k l q) (u q)) *
            Rm04 (fun q : Fin 4 => basis (slot4ikjl i j k l q))) *
          ricciPair04 (I := I) Ric (fun q : Fin 4 => basis (u q)))
        =
        Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (∑ u : Fin 4 -> Idx,
            (∏ q : Fin 4, gInv (slot4ikjl i j k l q) (u q)) *
              ricciPair04 (I := I) Ric (fun q : Fin 4 => basis (u q))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          have hRm :
              (fun q : Fin 4 => basis (slot4ikjl i j k l q)) =
                DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis i) (basis k) (basis j) (basis l) := by
            funext q
            fin_cases q <;> simp [slot4ikjl, DifferentialGeometry.Integral.Connection.vec4,
              DifferentialGeometry.Integral.Connection.vec4]
          rw [hRm]
          ring
    _ =
        Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          ((∑ a : Idx, ∑ c : Idx,
              gInv i a * gInv j c *
                Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis c))) *
            (∑ b : Idx, ∑ d : Idx,
              gInv k b * gInv l d *
                Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis b) (basis d)))) := by
          rw [pairSum_eq (I := I) gInv Ric basis i j k l]
    _ =
        Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis i) (basis k) (basis j) (basis l)) *
          (∑ a : Idx, ∑ c : Idx,
            gInv i a * gInv j c *
              Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis a) (basis c))) *
          (∑ b : Idx, ∑ d : Idx,
            gInv k b * gInv l d *
              Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis b) (basis d))) := by
          ring



private def ricciDataOfFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) (ricciNormLap (I := I) S)
      roughLapRic (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hnorm : forall t x,
      ricciNormSqInFrame (I := I) S gInv frame t x =
        ricciNorm (I := I) S t x)
    (hnabla : forall t x,
      nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
        ricciGradSq (I := I) S t x)
    (hreact : forall t x,
      ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
        ricciReact (I := I) S t x) :
    RicciHeatData (I := I) S := by
  refine
    { roughLapInner :=
        roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame
      timeDeriv := ?_
      laplacian := ?_ }
  · have hdt :=
      ricciNormTimeDerivativeComponentsOn_of_ricciEvolution_canonical
        (I := I) S Rm04 gInv frame roughLapRic
        h_inv h_ricci hInvSym hRicSym
    intro t x
    change
      HasDerivWithinAt
        (fun s : Real => ricciNorm (I := I) S s x)
        (2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame
            (t : Real) x +
          4 * ricciReact (I := I) S (t : Real) x)
        D.carrier
        (t : Real)
    have hframeDeriv :=
      (hdt t x).congr_deriv (by
        rw [hreact (t : Real) x])
    refine hframeDeriv.congr_of_eventuallyEq ?_ ?_
    filter_upwards with s
    exact (hnorm s x).symm
    exact (hnorm (t : Real) x).symm
  · have hlap :=
      ricciNormLaplacianComponentsOn_of_normSq_laplacian_expansion
        (I := I) S gInv frame roughLapRic (ricciNormLap (I := I) S)
        nablaRic h_lap
    intro t x
    change
      ricciNormLap (I := I) S t x =
        2 * roughLapRicciInnerInFrame (I := I) S roughLapRic gInv frame t x +
          2 * ricciGradSq (I := I) S t x
    exact (hlap t x).trans (by
      rw [hnabla t x])




theorem coordReact
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (x0 : M) (t : Real) :
    ricciNormCurvatureReactionInFrame
      (I := I) S S.base.rm04 (coordInv (I := I) S x0)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x0 =
      ricciReact (I := I) S t x0 := by
  classical
  rw [ricciNormCurvatureReactionInFrame_apply, ricciReact]
  congr 1
  rw [inner0S_eq_coord
    (I := I) (S.base.metric t) x0 4
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x0)
    (fun i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      coordInv (I := I) S x0 t x0 i j)
    (coordInvReal (I := I) S x0 t)]
  rw [coordPair4_eq]
  unfold curvRicciRicciInFrame raisedRicciCompInFrame
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame ricciTwoTensorField DifferentialGeometry.Integral.Connection.rm04Comp
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]







def ricciDataAtCoord
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (nabla2Ric : forall _x0, Real -> M ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (hInvEvol : forall x0,
      InverseMetricEvolutionEquationInFrame
        (I := I) S (coordInv (I := I) S x0)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet (I := I) x0))
    (hRicciEvol : forall x0,
      ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
        (i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E),
        HasDerivWithinAt
          (fun s : Real =>
            ricciCompInFrame (I := I) S
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) s x0 i j)
          (ricciEvolutionRHSInFrame
            (I := I) S S.base.rm04 (coordInv (I := I) S x0)
            (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0)
            (coordRoughRic (I := I) S x0 (nabla2Ric x0))
            (t : Real) x0 i j)
          D.carrier
          (t : Real))
    (hInvSymm : forall x0 t i j,
      coordInv (I := I) S x0 t x0 i j =
        coordInv (I := I) S x0 t x0 j i)
    (hRicciSymm : forall x0 t i j,
      ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x0 i j =
        ricciCompInFrame (I := I) S
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x0) t x0 j i)
    (hLap : forall t x,
      ricciNormLap (I := I) S t x =
        2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (nabla2Ric x))
              (coordInv (I := I) S x)
              (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x +
          2 * ricciGradSq (I := I) S t x) :
    RicciHeatData (I := I) S := by
  refine
    { roughLapInner := fun t x =>
        roughLapRicciInnerInFrame
          (I := I) S (coordRoughRic (I := I) S x (nabla2Ric x))
          (coordInv (I := I) S x)
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x) t x
      timeDeriv := ?_
      laplacian := ?_ }
  · intro t x
    let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
    have hbase :=
      ricciNormSqDerivAt
        (I := I) S S.base.rm04 (coordInv (I := I) S x) frame
        (coordRoughRic (I := I) S x (nabla2Ric x))
        (hInvEvol x) t x (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x)
        (hRicciEvol x t)
    have hsimplify :=
      ricciDerivSimpAt
        (I := I) S S.base.rm04 (coordInv (I := I) S x) frame
        (coordRoughRic (I := I) S x (nabla2Ric x)) t x
        (fun i j => hInvSymm x (t : Real) i j)
        (fun i j => hRicciSymm x (t : Real) i j)
    have hframe0 :=
      hbase.congr_deriv hsimplify
    have hnorm : forall s : Real,
        ricciNormSqInFrame (I := I) S (coordInv (I := I) S x) frame s x =
          ricciNorm (I := I) S s x := by
      intro s
      have hbasis :
          forall i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x i = frame i x := by
        intro i
        simp [frame, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply]
      simpa [ricciNorm] using
        ricciNormSq_basis (I := I) S (coordInv (I := I) S x) frame
          (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
          (coordInvReal (I := I) S x s) hbasis
    change
      HasDerivWithinAt
        (fun s : Real => ricciNorm (I := I) S s x)
        (2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (nabla2Ric x))
              (coordInv (I := I) S x)
              frame (t : Real) x +
          4 * ricciReact (I := I) S (t : Real) x)
        D.carrier (t : Real)
    have hframeDeriv :=
      hframe0.congr_deriv (by
        rw [coordReact (I := I) S x (t : Real)])
    refine hframeDeriv.congr_of_eventuallyEq ?_ ?_
    filter_upwards with s
    exact (hnorm s).symm
    exact (hnorm (t : Real)).symm
  · intro t x
    let frame := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x
    change
      ricciNormLap (I := I) S t x =
        2 *
            roughLapRicciInnerInFrame
              (I := I) S (coordRoughRic (I := I) S x (nabla2Ric x))
              (coordInv (I := I) S x)
              frame t x +
          2 * ricciGradSq (I := I) S t x
    exact hLap t x





def ricciHeatDataSmooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    RicciHeatData (I := I) S := by
  exact
    ricciDataAtCoord (I := I) S (coordNab2Ric (I := I) S)
      (fun x0 => hS.invEvol x0)
      (fun x0 => hS.ricciEvol x0)
      (fun x0 => hS.invSymm x0)
      (fun x0 => hS.ricciSymm x0)
      hS.ricciLap





theorem ricciHeatSmooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S) :
    RicciNormHeatEquationOn
      (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
      (ricciGradSq (I := I) S) (ricciReact (I := I) S) := by
  exact ricciHeat_of_data (I := I) S (ricciHeatDataSmooth (I := I) S _hS)

end DifferentialGeometry.PDE.RicciFlow
