import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.CovOrderTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiProducer

set_option autoImplicit false









noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]




theorem covTailBoundSol
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (order : Nat)
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hbound : exists K : Real, forall t : Real, forall x : M,
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= K)
    (hEquiv : exists Lambda : Real, 1 <= Lambda ∧
      exists t1 : Real, t1 ∈ Set.Ico alpha omega ∧
        forall s : Real, s ∈ Set.Ico t1 omega ->
          forall x : M, forall v : TangentSpace I x,
            Lambda⁻¹ * (S.base.metric alpha).inner x v v <=
                (S.base.metric s).inner x v v ∧
              (S.base.metric s).inner x v v <=
                Lambda * (S.base.metric alpha).inner x v v) :
    exists C : Real, 1 <= C ∧ exists t2 : Real, t2 ∈ Set.Ico alpha omega ∧
      forall s : Real, s ∈ Set.Ico t2 omega ->
        forall a : Nat, a <= order ->
          MetricCovDerivOrderBoundOn (I := I) Set.univ a
            (S.base.metric s) (S.base.metric alpha) C := by
  classical
  obtain ⟨Lambda, hLambda, t1, ht1, hEquivTail⟩ := hEquiv
  obtain ⟨tShi, hAlphaShi, hShiOmega⟩ := exists_between hAlphaOmega
  obtain ⟨KShi, hKShi0, hShi⟩ :=
    movingShiBoundN (I := I) tShi ⟨hAlphaShi, hShiOmega⟩ order hdim hS hbound
  have hMaxOmega : max t1 tShi < omega := max_lt ht1.2 hShiOmega
  obtain ⟨t2, hMaxT2, hT2Omega⟩ := exists_between hMaxOmega
  have ht1t2 : t1 <= t2 :=
    (le_max_left t1 tShi).trans hMaxT2.le
  have htShit2 : tShi <= t2 :=
    (le_max_right t1 tShi).trans hMaxT2.le
  have hAlphaT2 : alpha < t2 := hAlphaShi.trans_le htShit2
  let D := RealTimeInterval.closedOpen alpha omega hAlphaOmega
  let gSeq : Nat -> Real -> SmoothRiemannianMetric I M :=
    fun _ t => S.base.metric t
  let gRef : SmoothRiemannianMetric I M := S.base.metric alpha
  have hequivWindow : forall psi : Real, psi ∈ Set.Ico t2 omega ->
      MetricUniformEquivalentOnWindow (I := I) Set.univ t2 psi
        gRef gSeq (fun _ => Lambda) := by
    intro psi hPsi i t ht
    refine ⟨hLambda, ?_⟩
    intro x _hx v
    exact hEquivTail t
      ⟨ht1t2.trans ht.1, lt_of_le_of_lt ht.2 hPsi.2⟩ x v
  have hShiWindow : forall psi : Real, psi ∈ Set.Ico t2 omega ->
      MovingShiBoundOn (I := I) Set.univ t2 psi gSeq order KShi := by
    intro psi hPsi q hq i t ht x hx
    exact hShi psi ⟨htShit2.trans hPsi.1, hPsi.2⟩ q hq i t
      ⟨htShit2.trans ht.1, ht.2⟩ x hx
  have hDreg : forall {t : Real}, t ∈ D.regular -> D.regular ∈ nhds t :=
    fun {_t} ht => D.regular_isOpen.mem_nhds ht
  have hevWindow : forall psi : Real, psi ∈ Set.Ico t2 omega ->
      forall q : Nat, 1 <= q -> q <= order ->
        forall i : Nat, forall x : M, x ∈ Set.univ ->
          forall s : Real, s ∈ Set.Icc t2 psi ->
            forall v : Fin (q + 2) -> TangentSpace I x,
              HasDerivAt
                (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef q x v)
                (((-2 : Real) • nablaRicReal (I := I) gSeq gRef q i s x) v) s := by
    intro psi hPsi q _hq1 _hqOrder
    exact hevComp_of_solutions (I := I) (K := Set.univ) (β := t2) (ψ := psi)
      (N := q) (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl)
      (fun _ t ht => by
        change t ∈ Set.Ioo alpha omega
        exact ⟨lt_of_lt_of_le hAlphaT2 ht.1, lt_of_le_of_lt ht.2 hPsi.2⟩)
      (fun _ p hp V x0 => solnTowerSwap_reg (I := I) gRef S hS q hDreg p hp V x0)
  obtain ⟨initC, hinitC0, hinit⟩ :=
    exists_initC (I := I) (S.base.metric t2) gRef
  have htime : forall t : Real, t ∈ Set.Ico t2 omega ->
      |t - t2| <= omega - t2 := by
    intro t ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hpos := covOrder_Ico_tail (I := I)
    (K := Set.univ) (U := Set.univ) (t0 := t2) (omega := omega)
    (gSeq := gSeq) (gRef := gRef)
    isCompact_univ isOpen_univ (subset_refl Set.univ) order
    Lambda hLambda KShi hKShi0 initC hinitC0 (omega - t2)
    (fun _ => Lambda) hequivWindow (fun _ _ => le_rfl) hShiWindow hevWindow
    (fun q _ _ _i x _hx => hinit q x) htime
  have hPosExists : forall a : Nat, exists Ca : Real,
      1 <= a -> a <= order -> forall s : Real, s ∈ Set.Ico t2 omega ->
        MetricCovDerivOrderBoundOn (I := I) Set.univ a
          (S.base.metric s) gRef Ca := by
    intro a
    by_cases ha : 1 <= a ∧ a <= order
    · obtain ⟨Ca, hCa⟩ := hpos a ha.1 ha.2
      exact ⟨Ca, fun _ _ s hs => hCa 0 s hs⟩
    · exact ⟨0, fun ha1 haOrder => False.elim (ha ⟨ha1, haOrder⟩)⟩
  choose Ca hCa using hPosExists
  let levels : Finset Nat := Finset.range (order + 1)
  have hLevels : levels.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [levels, Finset.mem_range]
    omega
  let Cpos : Real := levels.sup' hLevels Ca
  have hCaCpos : forall a : Nat, a <= order -> Ca a <= Cpos := by
    intro a ha
    apply Finset.le_sup'
    simp only [levels, Finset.mem_range]
    omega
  let C0 : Real := Lambda * Real.sqrt (Module.finrank Real E : Real)
  have hC0 : forall s : Real, s ∈ Set.Ico t2 omega ->
      MetricCovDerivOrderBoundOn (I := I) Set.univ 0
        (S.base.metric s) gRef C0 := by
    intro s hs
    apply covOrder_zero_le (I := I)
    refine ⟨hLambda, ?_⟩
    intro x _hx v
    exact hEquivTail s ⟨ht1t2.trans hs.1, hs.2⟩ x v
  let C : Real := max 1 (max C0 Cpos)
  refine ⟨C, le_max_left _ _, t2, ⟨hAlphaT2.le, hT2Omega⟩, ?_⟩
  intro s hs a haOrder
  by_cases ha0 : a = 0
  · subst a
    intro x hx
    exact (hC0 s hs x hx).trans
      ((le_max_left C0 Cpos).trans (le_max_right 1 (max C0 Cpos)))
  · have ha1 : 1 <= a := Nat.one_le_iff_ne_zero.mpr ha0
    intro x hx
    exact (hCa a ha1 haOrder s hs x hx).trans
      ((hCaCpos a haOrder).trans
        ((le_max_right C0 Cpos).trans (le_max_right 1 (max C0 Cpos))))

end DifferentialGeometry.PDE.RicciFlow
