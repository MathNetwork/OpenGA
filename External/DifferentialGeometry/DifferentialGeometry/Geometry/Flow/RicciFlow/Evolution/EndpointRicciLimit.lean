import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.CovTailProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowGInf
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciFromJets
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated












noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
    [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [BoundarylessManifold I M]




theorem ricci_tendsto_left
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
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
                Lambda * (S.base.metric alpha).inner x v v)
    (gInf : SmoothRiemannianMetric I M)
    (hleft : forall x0 x : M,
      forall i j : Fin (Module.finrank Real E),
        Tendsto
          (fun s : Real => Integral.Measure.chartGramMatrix (I := I)
            (S.base.metric s) x0 x i j)
          (nhdsWithin omega (Set.Iio omega))
          (nhds (Integral.Measure.chartGramMatrix (I := I) gInf x0 x i j)))
    (x : M) (v w : TangentSpace I x) :
    Tendsto (fun s : Real => ricciTensor (I := I) (S.base.metric s) x v w)
      (nhdsWithin omega (Set.Iio omega))
      (nhds (ricciTensor (I := I) gInf x v w)) := by
  classical
  obtain ⟨Lambda, hLambda, t1, ht1, hEquivTail⟩ := hEquiv
  obtain ⟨beta, ht1beta, hBetaOmega⟩ := exists_between ht1.2
  rw [tendsto_iff_seq_tendsto]
  intro tSeq htSeq
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let qSeq : Nat -> Real := fun n => tSeq (ns n)
  have hqSeq : Tendsto qSeq atTop (nhdsWithin omega (Set.Iio omega)) := by
    simpa [qSeq, Function.comp_apply] using htSeq.comp hns
  have htail : ∀ᶠ n in atTop, qSeq n ∈ Set.Ioo beta omega :=
    hqSeq.eventually (Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hBetaOmega))
      self_mem_nhdsWithin)
  obtain ⟨n0, hn0⟩ := htail.exists_forall_of_atTop
  let qShift : Nat -> Real := fun n => qSeq (n + n0)
  have hShiftMem (n : Nat) : qShift n ∈ Set.Ioo beta omega := by
    exact hn0 (n + n0) (by omega)
  have hqShift : Tendsto qShift atTop (nhdsWithin omega (Set.Iio omega)) := by
    simpa [qShift, qSeq, Function.comp_apply] using
      hqSeq.comp (tendsto_add_atTop_nat n0)
  let gRef : SmoothRiemannianMetric I M := S.base.metric alpha
  let gSeq : Nat -> SmoothRiemannianMetric I M :=
    fun n => S.base.metric (qShift n)
  have hbdd : forall q : Nat, forall K : Set M, IsCompact K -> exists C : Real,
      forall k : Nat, forall z, z ∈ K ->
        metricCovDerivNorm (I := I) q (gSeq k) gRef z <= C := by
    intro q K hK
    obtain ⟨Cq, _hCq, tq, htq, hq⟩ :=
      covTailBoundSol (I := I) q hdim hS hbound
        ⟨Lambda, hLambda, t1, ht1, hEquivTail⟩
    have hqNhds : Tendsto qShift atTop (nhds omega) :=
      hqShift.mono_right nhdsWithin_le_nhds
    obtain ⟨k0, hk0⟩ :=
      ((tendsto_order.1 hqNhds).1 tq htq.2).exists_forall_of_atTop
    apply cov_bdd_of_eventual (I := I) hK q gSeq gRef
    refine ⟨k0, Cq, ?_⟩
    intro k hk z hz
    exact hq (qShift k) ⟨(hk0 k hk).le, (hShiftMem k).2⟩ q (le_refl q) z
      (Set.mem_univ z)
  have hlowSeq : forall k : Nat, forall y : M, forall xi : TangentSpace I y,
      Lambda⁻¹ * gRef.inner y xi xi <= (gSeq k).inner y xi xi := by
    intro k y xi
    exact (hEquivTail (qShift k)
      ⟨le_of_lt (lt_trans ht1beta (hShiftMem k).1), (hShiftMem k).2⟩ y xi).1
  have hLambdaInv : 0 < Lambda⁻¹ :=
    inv_pos.mpr (lt_of_lt_of_le zero_lt_one hLambda)
  obtain ⟨phi, hPhi, gLim, hInner, hDerivConv⟩ :=
    metricPreconvFull (I := I) ⟨x⟩
      Set.univ isCompact_univ 2 gRef gSeq hbdd
      ⟨Lambda⁻¹, hLambdaInv, hlowSeq⟩
  have hInnerEq : forall y : M, gLim.inner y = gInf.inner y := by
    intro y
    have hy : y ∈ (trivializationAt E (TangentSpace I) y).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) y
    let b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I y) :=
      Integral.Measure.chartBasisFamily (I := I) y hy
    have hb : forall i j : Fin (Module.finrank Real E),
        gLim.inner y (b i) (b j) = gInf.inner y (b i) (b j) := by
      intro i j
      have hEvalCont : Continuous
          (fun eta : TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real =>
            eta (b i) (b j)) :=
        ((ContinuousLinearMap.apply Real Real (b j)).comp
          (ContinuousLinearMap.apply Real (TangentSpace I y →L[Real] Real)
            (b i))).continuous
      have hLimSeq : Tendsto
          (fun k => (gSeq (phi k)).inner y (b i) (b j)) atTop
          (nhds (gLim.inner y (b i) (b j))) :=
        (hEvalCont.tendsto (gLim.inner y)).comp (hInner y)
      have hEndSeq : Tendsto
          (fun k => (gSeq (phi k)).inner y (b i) (b j)) atTop
          (nhds (gInf.inner y (b i) (b j))) := by
        simpa [gSeq, qShift, qSeq, b, Integral.Measure.chartBasisFamily_apply,
          Integral.Measure.chartGramMatrix_apply, Function.comp_apply] using
          (hleft y y i j).comp (hqShift.comp hPhi.tendsto_atTop)
      exact tendsto_nhds_unique hLimSeq hEndSeq
    have hcoe : (gLim.inner y).toLinearMap = (gInf.inner y).toLinearMap := by
      apply Module.Basis.ext b
      intro i
      have hrow : ((gLim.inner y) (b i)).toLinearMap =
          ((gInf.inner y) (b i)).toLinearMap := by
        apply Module.Basis.ext b
        intro j
        exact hb i j
      ext z
      exact LinearMap.congr_fun hrow z
    ext z u
    have hz := LinearMap.congr_fun hcoe z
    exact congrArg (fun eta => eta u) hz
  have hMetricEq : gLim = gInf := by
    have hinner : gLim.inner = gInf.inner := by
      funext y
      exact hInnerEq y
    cases gLim with
    | mk gi gsymm gpos gvon gcont =>
      cases gInf with
      | mk gi' gsymm' gpos' gvon' gcont' =>
        cases hinner
        rfl
  subst gLim
  have hlowInf : forall xi : TangentSpace I x,
      Lambda⁻¹ * gRef.inner x xi xi <= gInf.inner x xi xi := by
    intro xi
    have hEvalCont : Continuous
        (fun eta : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
          eta xi xi) :=
      ((ContinuousLinearMap.apply Real Real xi).comp
        (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) xi)).continuous
    have hLim : Tendsto (fun k => (gSeq (phi k)).inner x xi xi) atTop
        (nhds (gInf.inner x xi xi)) :=
      (hEvalCont.tendsto (gInf.inner x)).comp (hInner x)
    exact ge_of_tendsto hLim
      (Filter.Eventually.of_forall fun k => hlowSeq (phi k) x xi)
  have hxBdd : forall a : Nat, exists C : Real, forall k : Nat,
      metricCovDerivNorm (I := I) a (gSeq k) gRef x <= C := by
    intro a
    obtain ⟨C, hC⟩ := hbdd a {x} isCompact_singleton
    exact ⟨C, fun k => hC k x (Set.mem_singleton x)⟩
  choose C hC using hxBdd
  let B : Real := ∑ a ∈ Finset.range 3,
    (max 0 (C a) + metricCovDerivNorm (I := I) a gInf gRef x)
  have hB : 0 <= B := by
    apply Finset.sum_nonneg
    intro a ha
    exact add_nonneg (le_max_left 0 (C a)) (Real.sqrt_nonneg _)
  have hbddSeq : forall k : Nat, forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a (gSeq (phi k)) gRef x <= B := by
    intro k a ha
    have haMem : a ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    have hterm : max 0 (C a) + metricCovDerivNorm (I := I) a gInf gRef x <= B :=
      by
        simpa only [B] using
          (Finset.single_le_sum
            (f := fun b => max 0 (C b) +
              metricCovDerivNorm (I := I) b gInf gRef x)
            (fun b _ => add_nonneg (le_max_left 0 (C b)) (Real.sqrt_nonneg _)) haMem)
    calc
      metricCovDerivNorm (I := I) a (gSeq (phi k)) gRef x <= C a := hC a (phi k)
      _ <= max 0 (C a) := le_max_right 0 (C a)
      _ <= max 0 (C a) + metricCovDerivNorm (I := I) a gInf gRef x :=
        le_add_of_nonneg_right (Real.sqrt_nonneg _)
      _ <= B := hterm
  have hbddInf : forall a : Nat, a <= 2 ->
      metricCovDerivNorm (I := I) a gInf gRef x <= B := by
    intro a ha
    have haMem : a ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    have hterm : max 0 (C a) + metricCovDerivNorm (I := I) a gInf gRef x <= B :=
      by
        simpa only [B] using
          (Finset.single_le_sum
            (f := fun b => max 0 (C b) +
              metricCovDerivNorm (I := I) b gInf gRef x)
            (fun b _ => add_nonneg (le_max_left 0 (C b)) (Real.sqrt_nonneg _)) haMem)
    exact (le_add_of_nonneg_left (le_max_left 0 (C a))).trans hterm
  have hRicEps := ricciConv_of_dnConv (I := I) gRef x
    (fun k _ => gSeq (phi k)) (fun _ => gInf)
    0 0 Lambda⁻¹ B hLambdaInv hB
    (fun k _ _ xi => hlowSeq (phi k) x xi)
    (fun _ _ xi => hlowInf xi)
    (fun k _ _ a ha => hbddSeq k a ha)
    (fun _ _ a ha => hbddInf a ha)
    (fun eps heps => by
      obtain ⟨k0, hk0⟩ := hDerivConv eps heps
      exact ⟨k0, fun k hk _ _ a ha => hk0 k hk a ha x (Set.mem_univ x)⟩)
    v w
  have hRicLim : Tendsto
      (fun k => ricciTensor (I := I) (gSeq (phi k)) x v w) atTop
      (nhds (ricciTensor (I := I) gInf x v w)) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨k0, hk0⟩ := hRicEps eps heps
    refine ⟨k0, fun k hk => ?_⟩
    simpa [Real.dist_eq] using hk0 k hk 0 ⟨le_rfl, le_rfl⟩
  refine ⟨fun k => phi k + n0, ?_⟩
  simpa [gSeq, qShift, qSeq, Function.comp_apply] using hRicLim

end DifferentialGeometry.PDE.RicciFlow
