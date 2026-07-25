import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.PotentialEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat
import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Volume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Regularity
import DifferentialGeometry.Geometry.Operator.NormGradSqTime

set_option autoImplicit false









namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Evolution.Volume
open scoped Manifold ContDiff BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section Normed

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E



theorem revGram_smooth
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) (T : Real) {U : Set Real}
    (hU : Set.MapsTo (fun r : Real => T - r) U D.regular)
    (x₀ : M) (i j : Fin (Module.finrank Real E)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        chartGramMatrix (I := I)
          ((reverseFamily (I := I) (M := M) (flowG (I := I) S) T).metric p.1)
          x₀ p.2 i j)
      (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  let e := trivializationAt E (TangentSpace I) x₀
  change ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
    (fun p : Real × M =>
      chartGramMatrix (I := I)
        ((reverseFamily (I := I) (M := M) (flowG (I := I) S) T).metric p.1)
        x₀ p.2 i j) (U ×ˢ e.baseSet)
  have hframe :
      IsLocalFrameOn I E ∞ (e.localFrame (chartModelBasis E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I ∞ (chartModelBasis E)
  have hrev : ContMDiff (𝓘(Real, Real).prod I) (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (T - p.1, p.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hmap : Set.MapsTo (fun p : Real × M => (T - p.1, p.2))
      (U ×ˢ e.baseSet) (D.regular ×ˢ e.baseSet) := by
    intro p hp
    exact ⟨hU hp.1, hp.2⟩
  have hcomp : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      ((fun q : Real × M =>
        (S.family.metric q.1).inner q.2
          (e.localFrame (chartModelBasis E) i q.2)
          (e.localFrame (chartModelBasis E) j q.2)) ∘
        fun p : Real × M => (T - p.1, p.2)) (U ×ˢ e.baseSet) :=
    (hS.smoothMetric.frameCompSmooth
      (e.localFrame (chartModelBasis E)) hframe i j).comp hrev.contMDiffOn hmap
  refine hcomp.congr ?_
  intro p hp
  have hx : p.2 ∈ e.baseSet := hp.2
  simp only [Function.comp_apply, chartGramMatrix_apply]
  rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx,
    e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
  rfl

end Normed

section InnerProduct

variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E


theorem revTrace_eq
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S) (T s : Real)
    (hs : T - s ∈ D.regular) (x : M) :
    traceTimeDerivMetricAt (I := I)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T) s x =
        (2 : Real) * S.scalar (T - s) x := by
  classical
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  let Ric : RicciTensorField (I := I) (M := M) Real := fun r y X Y =>
    -S.ricciAt (T - r) y (vec2 (I := I) X Y)
  let scalar : Real → M → Real := fun r y => -S.scalar (T - r) y
  have hsub : HasDerivAt (fun r : Real => T - r) (-1) s := by
    simpa using
      (hasDerivAt_const (x := s) (c := T)).sub (hasDerivAt_id (x := s))
  have hEq : MetricVariationEquationDerivAt (I := I) G Ric s := by
    intro y X Y
    have hcomp := (metricDerivAt (I := I) S hS ⟨T - s, hs⟩ y X Y).comp s hsub
    simpa [G, Ric, reverseFamily, flowG] using hcomp
  have hScalar : ScalarRealizesRicciTraceInFrame (I := I)
      (scalar s) (Ric s)
      (volumeTraceInvMetricComponents (I := I) (M := M) (G.metric s))
      (volumeTraceFrame (I := I) (M := M)) := by
    intro y
    have hy : y ∈ (trivializationAt E (TangentSpace I) y).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) y
    have hinv : MetricInverseInBasis_gen (I := I) (G.metric s) y
        (chartBasisFamily (I := I) y hy)
        (fun i j => chartInvGramMatrix (I := I) (G.metric s) y y i j) := by
      exact chartInvGram_inverse (I := I) (G.metric s) y hy
    have htrace := metricTracePair0SAt_eq_sum_basis
      (I := I) (G.metric s) (chartBasisFamily (I := I) y hy)
      (fun i j => chartInvGramMatrix (I := I) (G.metric s) y y i j)
      hinv (S.ricciAt (T - s) y)
    change -S.scalar (T - s) y =
      ∑ i : Fin (Module.finrank Real E),
        ∑ j : Fin (Module.finrank Real E),
          ((chartGramMatrix (I := I) (G.metric s) y y)⁻¹) i j *
            (-S.ricciAt (T - s) y
              (vec2 (I := I) (chartBasisVecFiber (I := I) y i y)
                (chartBasisVecFiber (I := I) y j y)))
    rw [S.scalar_eq_metricTrace]
    change -metricTracePair0SAt (I := I) (G.metric s)
      (S.ricciAt (T - s) y) = _
    rw [htrace]
    simp only [chartBasisFamily_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [chartInvGramMatrix]
    ring
  have htrace :=
    traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv
      (I := I) (M := M) G Ric scalar hEq hScalar x
  change traceTimeDerivMetricAt (I := I) G s x = _
  rw [htrace]
  dsimp only [scalar]
  ring

end InnerProduct

section Normed

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E



theorem revScalar_time
    [I.Boundaryless]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T s : Real) (hs : T - s ∈ D.regular) (x : M) :
    HasDerivAt
      (fun r : Real => S.scalar (T - r) x)
      (-(laplacianAt (I := I)
            (reverseFamily (I := I) (M := M) (flowG (I := I) S) T) s
            (S.scalar (T - s)) x +
          2 * normSq0S (I := I)
            ((reverseFamily (I := I) (M := M)
              (flowG (I := I) S) T).metric s)
            x 2 (S.ricci (T - s) x))) s := by
  let G := flowG (I := I) S
  have hbase :=
    (scalarEvolOfSol (I := I) S hS G
      (fun _ => rfl) (fun _ => rfl) ⟨T - s, hs⟩ x).hasDerivAt
      (D.regular_mem_nhds hs)
  have hsub : HasDerivAt (fun r : Real => T - r) (-1) s := by
    simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, id_eq, zero_add] using
      (hasDerivAt_const (x := s) (c := T)).sub (hasDerivAt_id (x := s))
  have hcomp := hbase.comp s hsub
  have hderiv :
      (laplacianAt (I := I) G (T - s) (S.scalar (T - s)) x +
          2 * normSq0S (I := I) (S.family.metric (T - s)) x 2
            (S.ricci (T - s) x)) * (-1) =
        -(laplacianAt (I := I)
              (reverseFamily (I := I) (M := M) G T) s
              (S.scalar (T - s)) x +
            2 * normSq0S (I := I)
              ((reverseFamily (I := I) (M := M) G T).metric s)
              x 2 (S.ricci (T - s) x)) := by
    simp only [laplacianAt, reverseFamily, G, flowG, SolutionOn.family]
    ring
  simpa only [Function.comp_apply, G] using hcomp.congr_deriv hderiv




theorem revGradSq_time
    [I.Boundaryless]
    {D Dr : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (V u : Real -> M -> Real) (n : Nat)
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn Dr
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) T) V u)
    (hpos : ∀ t : Real, t ∈ Dr.regular ∩ Set.Ioi (0 : Real) ->
      ∀ y : M, 0 < u t y)
    {s : Real} (hs : s ∈ Dr.regular) (hspos : 0 < s)
    (hTs : T - s ∈ D.regular) (x : M) :
    HasDerivAt
      (fun r : Real =>
        ((reverseFamily (I := I) (M := M)
          (flowG (I := I) S) T).metric r).inner x
          (gradientFun (I := I)
            ((reverseFamily (I := I) (M := M)
              (flowG (I := I) S) T).metric r)
            (perelmanPotential n r (u r)) x)
          (gradientFun (I := I)
            ((reverseFamily (I := I) (M := M)
              (flowG (I := I) S) T).metric r)
            (perelmanPotential n r (u r)) x))
      ((-2 : Real) * S.ricciAt (T - s) x
          (vec2
            (gradientFun (I := I)
              ((reverseFamily (I := I) (M := M)
                (flowG (I := I) S) T).metric s)
              (perelmanPotential n s (u s)) x)
            (gradientFun (I := I)
              ((reverseFamily (I := I) (M := M)
                (flowG (I := I) S) T).metric s)
              (perelmanPotential n s (u s)) x)) +
        2 * ((reverseFamily (I := I) (M := M)
          (flowG (I := I) S) T).metric s).inner x
          (gradientFun (I := I)
            ((reverseFamily (I := I) (M := M)
              (flowG (I := I) S) T).metric s)
            (fun y : M =>
              laplacianAt (I := I)
                  (reverseFamily (I := I) (M := M)
                    (flowG (I := I) S) T) s
                  (perelmanPotential n s (u s)) y -
                ((reverseFamily (I := I) (M := M)
                  (flowG (I := I) S) T).metric s).inner y
                  (gradientFun (I := I)
                    ((reverseFamily (I := I) (M := M)
                      (flowG (I := I) S) T).metric s)
                    (perelmanPotential n s (u s)) y)
                  (gradientFun (I := I)
                    ((reverseFamily (I := I) (M := M)
                      (flowG (I := I) S) T).metric s)
                    (perelmanPotential n s (u s)) y) -
                V s y - (n : Real) / (2 * s)) x)
          (gradientFun (I := I)
            ((reverseFamily (I := I) (M := M)
              (flowG (I := I) S) T).metric s)
            (perelmanPotential n s (u s)) x)) s := by
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) T
  let f : Real -> M -> Real := fun r => perelmanPotential n r (u r)
  let ft : M -> Real := fun y =>
    laplacianAt (I := I) G s (f s) y -
      (G.metric s).inner y
        (gradientFun (I := I) (G.metric s) (f s) y)
        (gradientFun (I := I) (G.metric s) (f s) y) -
      V s y - (n : Real) / (2 * s)
  let Q : Tensor0SSpace 2 I x := -S.ricciAt (T - s) x
  have hsub : HasDerivAt (fun r : Real => T - r) (-1) s := by
    simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, id_eq, zero_add] using
      (hasDerivAt_const (x := s) (c := T)).sub (hasDerivAt_id (x := s))
  have hg (X Y : TangentSpace I x) :
      HasDerivAt
        (fun r : Real => (G.metric r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) s := by
    have hcomp :=
      (metricDerivAt (I := I) S hS ⟨T - s, hTs⟩ x X Y).comp s hsub
    have hderiv :
        ((-2 : Real) * S.ricciAt (T - s) x (vec2 X Y)) * (-1) =
          (-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y) := by
      dsimp only [Q]
      rw [show (fun a : Fin 2 => if a = 0 then X else Y) = vec2 X Y by rfl]
      rw [Tensor0SSpace.neg_apply]
      ring
    simpa only [Function.comp_apply, G, reverseFamily, flowG] using
      hcomp.congr_deriv hderiv
  have hdf (X : TangentSpace I x) :
      HasDerivAt
        (fun r : Real => extDerivFun (I := I) (f r) x X)
        (extDerivFun (I := I) ft x X) s := by
    simpa only [G, f, ft] using
      potential_df_time (I := I) Dr G V u n hu hpos hs hspos x X
  have hmain := normGradSq_time (I := I) G.metric f ft Q hg hdf
  have hderiv :
      2 * Q (fun a : Fin 2 =>
          if a = 0 then gradientFun (I := I) (G.metric s) (f s) x
          else gradientFun (I := I) (G.metric s) (f s) x) +
          2 * (G.metric s).inner x
            (gradientFun (I := I) (G.metric s) ft x)
            (gradientFun (I := I) (G.metric s) (f s) x) =
        (-2 : Real) * S.ricciAt (T - s) x
          (vec2
            (gradientFun (I := I) (G.metric s) (f s) x)
            (gradientFun (I := I) (G.metric s) (f s) x)) +
          2 * (G.metric s).inner x
            (gradientFun (I := I) (G.metric s) ft x)
            (gradientFun (I := I) (G.metric s) (f s) x) := by
    dsimp only [Q]
    rw [show
      (fun a : Fin 2 =>
        if a = 0 then gradientFun (I := I) (G.metric s) (f s) x
        else gradientFun (I := I) (G.metric s) (f s) x) =
      vec2
        (gradientFun (I := I) (G.metric s) (f s) x)
        (gradientFun (I := I) (G.metric s) (f s) x) by rfl]
    rw [Tensor0SSpace.neg_apply]
    ring
  simpa only [G, f, ft] using hmain.congr_deriv hderiv

end Normed

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
