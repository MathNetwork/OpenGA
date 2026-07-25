import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.CovTailProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowGInf
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import Mathlib.Topology.Order.IsLUB











noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Filter
open scoped Manifold ContDiff Topology
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




theorem exists_endMetric
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hbound : exists K : Real, forall t : Real, forall x : M,
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= K)
    (hEquiv : exists Lambda : Real, 1 <= Lambda /\
      exists t1 : Real, t1 ∈ Set.Ico alpha omega /\
        forall s : Real, s ∈ Set.Ico t1 omega ->
          forall x : M, forall v : TangentSpace I x,
            Lambda⁻¹ * (S.base.metric alpha).inner x v v <=
                (S.base.metric s).inner x v v /\
              (S.base.metric s).inner x v v <=
                Lambda * (S.base.metric alpha).inner x v v) :
    exists gInf : SmoothRiemannianMetric I M,
      forall x0 x : M, forall i j : Fin (Module.finrank Real E),
        Tendsto (fun s : Real =>
          Integral.Measure.chartGramMatrix (I := I) (S.base.metric s) x0 x i j)
          (nhdsWithin omega (Set.Iio omega))
          (nhds (Integral.Measure.chartGramMatrix (I := I) gInf x0 x i j)) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hM =>
      letI : IsEmpty M := hM
      refine ⟨S.base.metric alpha, ?_⟩
      intro x0
      exact isEmptyElim x0
  | inr hM =>
      letI : Nonempty M := hM
      obtain ⟨Lambda, hLambda, t1, ht1, hEquivTail⟩ := hEquiv
      obtain ⟨beta, ht1beta, hBetaOmega⟩ := exists_between ht1.2
      have hBeta : beta ∈ Set.Ioo alpha omega :=
        ⟨lt_of_le_of_lt ht1.1 ht1beta, hBetaOmega⟩
      obtain ⟨KShi, hKShi, hShi⟩ :=
        movingShiBoundN (I := I) beta hBeta 0 hdim hS hbound
      obtain ⟨tSeq, hSeqMono, hSeqMem, hSeqLim⟩ :=
        exists_seq_strictMono_tendsto' hBetaOmega
      let gRef : SmoothRiemannianMetric I M := S.base.metric alpha
      let gSeq : Nat -> SmoothRiemannianMetric I M :=
        fun n => S.base.metric (tSeq n)
      have hbdd : forall q : Nat, forall K : Set M, IsCompact K -> exists C : Real,
          forall k : Nat, forall z, z ∈ K ->
            metricCovDerivNorm (I := I) q (gSeq k) gRef z <= C := by
        intro q K hK
        obtain ⟨Cq, _hCq, tq, htq, hq⟩ :=
          covTailBoundSol (I := I) q hdim hS hbound
            ⟨Lambda, hLambda, t1, ht1, hEquivTail⟩
        obtain ⟨k0, hk0⟩ :=
          ((tendsto_order.1 hSeqLim).1 tq htq.2).exists_forall_of_atTop
        apply cov_bdd_of_eventual (I := I) hK q gSeq gRef
        refine ⟨k0, Cq, ?_⟩
        intro k hk z hz
        exact hq (tSeq k) ⟨(hk0 k hk).le, (hSeqMem k).2⟩ q (le_refl q) z
          (Set.mem_univ z)
      have hlow : exists c : Real, 0 < c /\
          forall k : Nat, forall x : M, forall v : TangentSpace I x,
            c * gRef.inner x v v <= (gSeq k).inner x v v := by
        refine ⟨Lambda⁻¹, ?_, ?_⟩
        · exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hLambda)
        · intro k x v
          exact (hEquivTail (tSeq k)
            ⟨le_of_lt (lt_trans ht1beta (hSeqMem k).1), (hSeqMem k).2⟩ x v).1
      obtain ⟨phi, hPhi, gInf, hInner, _hDerivConv⟩ :=
        metricPreconvFull (I := I) hM Set.univ isCompact_univ 2 gRef gSeq hbdd hlow
      refine ⟨gInf, ?_⟩
      intro x0 x i j
      let v : TangentSpace I x :=
        Integral.Measure.chartBasisVecFiber (I := I) x0 i x
      let w : TangentSpace I x :=
        Integral.Measure.chartBasisVecFiber (I := I) x0 j x
      have hRicAbs : forall s : Real, s ∈ Set.Ioo beta omega ->
          |ricciTensor (I := I) (S.base.metric s) x v w| <=
            KShi * (Real.sqrt (Lambda * gRef.inner x v v) *
              Real.sqrt (Lambda * gRef.inner x w w)) := by
        intro s hs
        obtain ⟨basis, hON⟩ :=
          exists_gOrthonormalBasis (I := I) (S.base.metric s) x
        have hNorm :
            Real.sqrt (normSq0S (I := I) (S.base.metric s) x 2
              (ricCovTower (I := I) (S.base.metric s) (S.base.metric s) 0 x)) <=
                KShi := by
          exact hShi s ⟨hs.1.le, hs.2⟩ 0 (le_refl 0) 0 s
            ⟨hs.1.le, le_refl s⟩ x (Set.mem_univ x)
        have hCS := abs_apply_le_sqrt_normSq0S (I := I)
          (S.base.metric s) x 2 basis hON
          (ricCovTower (I := I) (S.base.metric s) (S.base.metric s) 0 x)
          (vec2 (I := I) v w)
        have hRicVal :
            (ricCovTower (I := I) (S.base.metric s) (S.base.metric s) 0 x)
                (vec2 (I := I) v w) =
              ricciTensor (I := I) (S.base.metric s) x v w := by
          simpa [ricCovTower] using
            (ricciSection_eq_ricciTensor (I := I) (S.base.metric s) x v w)
        have hv := (hEquivTail s
          ⟨le_of_lt (lt_trans ht1beta hs.1), hs.2⟩ x v).2
        have hw := (hEquivTail s
          ⟨le_of_lt (lt_trans ht1beta hs.1), hs.2⟩ x w).2
        have hProd :
            Real.sqrt ((S.base.metric s).inner x v v) *
                Real.sqrt ((S.base.metric s).inner x w w) <=
              Real.sqrt (Lambda * gRef.inner x v v) *
                Real.sqrt (Lambda * gRef.inner x w w) := by
          exact mul_le_mul (Real.sqrt_le_sqrt hv) (Real.sqrt_le_sqrt hw)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        calc
          |ricciTensor (I := I) (S.base.metric s) x v w| <=
              Real.sqrt (normSq0S (I := I) (S.base.metric s) x 2
                (ricCovTower (I := I) (S.base.metric s) (S.base.metric s) 0 x)) *
                (Real.sqrt ((S.base.metric s).inner x v v) *
                  Real.sqrt ((S.base.metric s).inner x w w)) := by
                    simpa [hRicVal, Fin.prod_univ_two, vec2] using hCS
          _ <= KShi * (Real.sqrt ((S.base.metric s).inner x v v) *
                Real.sqrt ((S.base.metric s).inner x w w)) :=
              mul_le_mul_of_nonneg_right hNorm
                (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          _ <= KShi * (Real.sqrt (Lambda * gRef.inner x v v) *
                Real.sqrt (Lambda * gRef.inner x w w)) :=
              mul_le_mul_of_nonneg_left hProd hKShi
      have hDeriv : forall s : Real, s ∈ Set.Ioo beta omega ->
          HasDerivAt (fun u : Real =>
            Integral.Measure.chartGramMatrix (I := I) (S.base.metric u) x0 x i j)
            (deriv (fun u : Real =>
              Integral.Measure.chartGramMatrix (I := I) (S.base.metric u) x0 x i j) s) s := by
        intro s hs
        have hsReg : s ∈ Set.Ioo alpha omega :=
          ⟨lt_trans hBeta.1 hs.1, hs.2⟩
        have h := metricDerivAt (I := I) S hS ⟨s, hsReg⟩ x v w
        simpa [Integral.Measure.chartGramMatrix_apply, v, w, SolutionOn.family] using
          h.differentiableAt.hasDerivAt
      have hDerivBound : forall s : Real, s ∈ Set.Ioo beta omega ->
          |deriv (fun u : Real =>
            Integral.Measure.chartGramMatrix (I := I) (S.base.metric u) x0 x i j) s| <=
              2 * (KShi * (Real.sqrt (Lambda * gRef.inner x v v) *
                Real.sqrt (Lambda * gRef.inner x w w))) := by
        intro s hs
        have hsReg : s ∈ Set.Ioo alpha omega :=
          ⟨lt_trans hBeta.1 hs.1, hs.2⟩
        have h := metricDerivAt (I := I) S hS ⟨s, hsReg⟩ x v w
        have hVal : S.base.ricciAt s x (vec2 (I := I) v w) =
            ricciTensor (I := I) (S.base.metric s) x v w :=
          metricRicciAt_apply_eq_ricciTensor (I := I) (S.base.metric s) x v w
        have hDerivEq :
            deriv (fun u : Real =>
              Integral.Measure.chartGramMatrix (I := I) (S.base.metric u) x0 x i j) s =
                (-2 : Real) * ricciTensor (I := I) (S.base.metric s) x v w := by
          simpa [Integral.Measure.chartGramMatrix_apply, v, w, SolutionOn.family, hVal] using
            h.deriv
        calc
          |deriv (fun u : Real =>
              Integral.Measure.chartGramMatrix (I := I) (S.base.metric u) x0 x i j) s| =
              2 * |ricciTensor (I := I) (S.base.metric s) x v w| := by
                rw [hDerivEq, abs_mul]
                norm_num
          _ <= 2 * (KShi * (Real.sqrt (Lambda * gRef.inner x v v) *
                Real.sqrt (Lambda * gRef.inner x w w))) :=
              mul_le_mul_of_nonneg_left (hRicAbs s hs) (by norm_num)
      obtain ⟨L, hLimit⟩ :=
        chartGramMatrix_tendsto_nhdsLT_of_bounded_deriv (I := I)
          S.base.metric hBetaOmega x0 x i j hDeriv hDerivBound
      have hSeqLeft : Tendsto tSeq atTop (nhdsWithin omega (Set.Iio omega)) :=
        tendsto_nhdsWithin_mono_right
          (Set.range_subset_iff.2 (fun n => (hSeqMem n).2))
          (tendsto_nhdsWithin_range.2 hSeqLim)
      have hLimitSeq : Tendsto (fun n : Nat =>
          Integral.Measure.chartGramMatrix (I := I)
            (S.base.metric (tSeq (phi n))) x0 x i j) atTop (nhds L) := by
        simpa using hLimit.comp (hSeqLeft.comp hPhi.tendsto_atTop)
      have hEvalCont : Continuous
          (fun eta : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real =>
            eta v w) :=
        ((ContinuousLinearMap.apply Real Real w).comp
          (ContinuousLinearMap.apply Real (TangentSpace I x →L[Real] Real) v)).continuous
      have hMetricSeq : Tendsto (fun n : Nat =>
          Integral.Measure.chartGramMatrix (I := I)
            (S.base.metric (tSeq (phi n))) x0 x i j) atTop
          (nhds (Integral.Measure.chartGramMatrix (I := I) gInf x0 x i j)) := by
        simpa [gSeq, gRef, Integral.Measure.chartGramMatrix_apply, v, w] using
          (hEvalCont.tendsto (gInf.inner x)).comp (hInner x)
      have hEq : L = Integral.Measure.chartGramMatrix (I := I) gInf x0 x i j :=
        tendsto_nhds_unique hLimitSeq hMetricSeq
      rwa [hEq] at hLimit

end DifferentialGeometry.PDE.RicciFlow
