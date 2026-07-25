import DifferentialGeometry.Analysis.Calculus.TimeJetMatch
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.RankZeroRealization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarLapDiffCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarPotential
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ScalarPathReconstruct
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SeriesContinuous
import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinStrong
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjugateHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.HeatPotential
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.WeylEigenvalueCountingBound









noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.Evolution.Volume
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in

private theorem rev_gram_smooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
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
  simp only [Function.comp_apply, chartGramMatrix_apply, reverse_metric]
  rw [e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx,
    e.localFrame_apply_of_mem_baseSet (chartModelBasis E) hx]
  rfl

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in

private theorem rev_trace_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
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
    have hy : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
      exact mem_baseSet_trivializationAt E (TangentSpace I) y
    let b := chartBasisFamily (I := I) y hy
    have hinv : MetricInverseInBasis_gen (I := I) (G.metric s) y b
        (fun i j => chartInvGramMatrix (I := I) (G.metric s) y y i j) := by
      simpa only [b] using
        chartInvGram_inverse (I := I) (G.metric s) y hy
    have htrace := metricTracePair0SAt_eq_sum_basis
      (I := I) (G.metric s) b
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
    simp only [b, chartBasisFamily_apply]
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

omit [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] in
theorem heatpot_mass_deriv
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {tau : Real} (htau : 0 ≤ tau) {u : Real → M → Real}
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau htau)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun r x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
      u)
    {s : Real} (hs : s ∈ Set.Ioo (0 : Real) tau)
    (hTs : (T : Real) - s ∈ D.regular) :
    HasDerivAt
      (fun r : Real =>
        ∫ x, u r x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) r))
      0 s := by
  classical
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)
  let U : Set Real := Set.Ioo (0 : Real) tau ∩
    (fun r : Real => (T : Real) - r) ⁻¹' D.regular
  have hsub_cont : Continuous (fun r : Real => (T : Real) - r) :=
    continuous_const.sub continuous_id
  have hUopen : IsOpen U :=
    isOpen_Ioo.inter (D.regular_isOpen.preimage hsub_cont)
  have hsU : s ∈ U := ⟨hs, hTs⟩
  have hUmap : Set.MapsTo (fun r : Real => (T : Real) - r) U D.regular := by
    intro r hr
    exact hr.2
  have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    simpa only [G] using
      rev_gram_smooth (I := I) (M := M) hS (T : Real) hUmap x₀ i j
  have hu_joint : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => u p.1 p.2) (U ×ˢ Set.univ) :=
    hu.jointSmooth.mono (Set.prod_mono Set.inter_subset_left Set.Subset.rfl)
  have hvariation :
      HasDerivAt
        (fun r : Real => ∫ x, u r x ∂(volumeMeasureFamily (I := I) (M := M) G r))
        (∫ x, (deriv (fun r : Real => u r x) s +
              (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G s x * u s x)
            ∂(volumeMeasureFamily (I := I) (M := M) G s)) s := by
    simpa [volumeMeasureFamily, traceTimeDerivMetricAt] using
      (first_var_joint (I := I) (M := M) hUopen hsU hgram hu_joint)
  have hu_smooth : ContMDiff I 𝓘(Real, Real) ∞ (u s) :=
    hu.sliceSmooth s ⟨hs.1.le, hs.2.le⟩
  have hgreen :=
    integral_smul_laplacian_sub_eq_zero_family
      (I := I) (M := M) (fun r : Real => G.metric r)
      (f := fun _ : M => (1 : Real)) (h := u s)
      contMDiff_const hu_smooth s
  have hlap :
      ∫ x, Δ_g (I := I) (G.metric s) hu_smooth x
        ∂(volumeMeasureFamily (I := I) (M := M) G s) = 0 := by
    simpa only [one_mul, Δ_g_const, mul_zero, sub_zero] using hgreen
  have hmass :
      ∫ x, (deriv (fun r : Real => u r x) s +
            (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G s x * u s x)
          ∂(volumeMeasureFamily (I := I) (M := M) G s) = 0 := by
    calc
      _ = ∫ x, Δ_g (I := I) (G.metric s) hu_smooth x
            ∂(volumeMeasureFamily (I := I) (M := M) G s) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [(hu.equation s hs x).deriv]
          rw [rev_trace_eq (I := I) (M := M) hS (T : Real) s hTs x]
          rw [laplacianAt_eq_delta (I := I) (M := M) G s hu_smooth (by rfl) x]
          simp only [conjCoeff_apply]
          ring
      _ = 0 := hlap
  change HasDerivAt
    (fun r : Real => ∫ x, u r x ∂(volumeMeasureFamily (I := I) (M := M) G r)) 0 s
  exact hvariation.congr_deriv hmass

omit [BoundarylessManifold I M] in

omit [NeZero (Module.finrank ℝ E)] in
theorem heatpot_mass_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    {tau : Real} (htau : 0 < tau) {u : Real → M → Real}
    (hu : DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
      (RealTimeInterval.closed 0 tau htau.le)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      (fun r x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
      u) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ tau ∧
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (RealTimeInterval.closed 0 tau' htau'.le)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
        (fun r x =>
          (conjCoeff (I := I) (M := M) S ((T : Real) - r) : M → Real) x)
        u ∧
      ∀ s ∈ Set.Icc (0 : Real) tau',
        (∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) s)) =
        ∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)) 0) := by
  classical
  let W : Set Real := (fun r : Real => (T : Real) - r) ⁻¹' D.regular
  have hsub_cont : Continuous (fun r : Real => (T : Real) - r) :=
    continuous_const.sub continuous_id
  have hWopen : IsOpen W := D.regular_isOpen.preimage hsub_cont
  have h0W : (0 : Real) ∈ W := by
    change (T : Real) - 0 ∈ D.regular
    simpa only [sub_zero] using T.2
  obtain ⟨l, w, h0lw, hlw⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWopen.mem_nhds h0W)
  let tau' : Real := min tau (w / 2)
  have htau' : 0 < tau' := by
    simpa only [tau'] using lt_min htau (half_pos h0lw.2)
  have htau'_tau : tau' ≤ tau := min_le_left _ _
  have hmap : Set.MapsTo (fun r : Real => (T : Real) - r)
      (Set.Icc (0 : Real) tau') D.regular := by
    intro r hr
    apply hlw
    refine ⟨h0lw.1.trans_le hr.1, ?_⟩
    exact lt_of_le_of_lt (hr.2.trans (min_le_right tau (w / 2)))
      (half_lt_self h0lw.2)
  have hu' := hu.mono
    (D' := RealTimeInterval.closed 0 tau' htau'.le)
    (Set.Icc_subset_Icc le_rfl htau'_tau)
    (Set.Ioo_subset_Ioo le_rfl htau'_tau)
  let G := reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real)
  let mass : Real → Real := fun s =>
    ∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M) G s)
  have hmass_cont : ContinuousOn mass (Set.Icc (0 : Real) tau') := by
    have hgram (x₀ : M) (i j : Fin (Module.finrank Real E)) :
        ContinuousOn
          (fun p : Real × M => chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
          (Set.Icc (0 : Real) tau' ×ˢ
            (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      exact (rev_gram_smooth (I := I) (M := M) hS (T : Real) hmap x₀ i j).continuousOn
    simpa only [mass, volumeMeasureFamily, metricFamilyForMeasure] using
      (integral_family_cont (I := I) (M := M) isCompact_Icc hgram hu'.jointCont)
  have hderiv (r : Real) (hr : r ∈ Set.Ioo (0 : Real) tau') :
      HasDerivAt mass 0 r := by
    have hTr : (T : Real) - r ∈ D.regular := hmap ⟨hr.1.le, hr.2.le⟩
    simpa only [mass, G] using
      heatpot_mass_deriv (I := I) (M := M) S hS T htau'.le hu' hr hTr
  have hdiff : DifferentiableOn Real mass (Set.Ioo (0 : Real) tau') := by
    intro r hr
    exact (hderiv r hr).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv mass) 0 (Set.Ioo (0 : Real) tau') := by
    intro r hr
    exact (hderiv r hr).deriv
  let mid : Real := tau' / 2
  have hmid : mid ∈ Set.Ioo (0 : Real) tau' := by
    exact ⟨half_pos htau', half_lt_self htau'⟩
  have hinner : Set.EqOn mass (fun _ : Real => mass mid)
      (Set.Ioo (0 : Real) tau') := by
    intro r hr
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hdiff hzero hr hmid
  have hclosed : Set.EqOn mass (fun _ : Real => mass mid)
      (Set.Icc (0 : Real) tau') := by
    apply hinner.of_subset_closure hmass_cont continuousOn_const
      Set.Ioo_subset_Icc_self
    rw [closure_Ioo htau'.ne]
  refine ⟨tau', htau', htau'_tau, hu', ?_⟩
  intro s hs
  change mass s = mass 0
  exact (hclosed hs).trans (hclosed ⟨le_rfl, htau'.le⟩).symm



@[simp] theorem galLimExt_coeff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (m : Nat) {t : Real} (ht : t ∈ Icc (0 : Real) tau)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    (galLimExt hτ hlim m t).coeff i = ulim t i := by
  rw [galLimExt_mem hτ hlim m ht]
  rfl




theorem galLim_jet_mass
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ ⦃a b : Real⦄, 0 < a → a ≤ b → b < tau' →
        (∀ i, ContDiffOn Real ∞ (fun t => ulim t i) (Icc a b)) ∧
        ∀ (j m : Nat),
          ∃ B : TensorEigenIdx (I := I) (M := M)
              (S.family.metric (T : Real)) 0 0 → Real,
            Summable B ∧
            ∀ i, ∀ t ∈ Icc a b,
              tensorSobolevWeight (I := I) (M := M) i (m : Real) *
                (iteratedDeriv j (fun s => ulim s i) t) ^ 2 ≤ B i := by
  classical
  obtain ⟨tau', htau', htau'_tau, hsmooth⟩ :=
    galLimExt_smooth (I := I) (M := M) hS hτ hlim
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M) q 0 0
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) q 0 0)
  obtain ⟨p, _hp, hpsum⟩ := htail
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro a b ha hab hb
  have hKsub : Icc a b ⊆ Ioo (0 : Real) tau' := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hcoeff_smooth (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ContDiffOn Real ∞ (fun t => ulim t i) (Icc a b) := by
    let L := tensorHsCoeffL (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0)
      (a := ((0 : Nat) : Real)) i
    have hcomp : ContDiffOn Real ∞
        (fun t => L (galLimExt hτ.le hlim 0 t))
        (Ioo (0 : Real) tau') := by
      simpa only [Function.comp_apply] using
        L.contDiff.comp_contDiffOn (hsmooth 0)
    have hcoeff_open : ContDiffOn Real ∞
        (fun t => ulim t i) (Ioo (0 : Real) tau') := by
      refine hcomp.congr ?_
      intro t ht
      simpa only [L, q, tensorHsCoeffL_apply] using
        (galLimExt_coeff hτ.le hlim 0
          ⟨ht.1.le, ht.2.le.trans htau'_tau⟩ i).symm
    exact hcoeff_open.mono hKsub
  refine ⟨hcoeff_smooth, ?_⟩
  intro j m
  obtain ⟨k : Nat, hk⟩ := exists_nat_gt p
  have hmp : (m : Real) + p ≤ ((m + k : Nat) : Real) := by
    rw [Nat.cast_add]
    nlinarith
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0) hmp
  let U : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => J (galLimExt hτ.le hlim (m + k) t)
  have hU : ContDiffOn Real ∞ U (Ioo (0 : Real) tau') := by
    simpa only [U, Function.comp_apply] using
      J.contDiff.comp_contDiffOn (hsmooth (m + k))
  let W : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => iteratedDeriv j U t
  have hWopen : ContinuousOn W (Ioo (0 : Real) tau') := by
    have hF : ContinuousOn (iteratedFDeriv Real j U)
        (Ioo (0 : Real) tau') :=
      ContinuousOn.continuousOn_iteratedFDeriv hU isOpen_Ioo
        (by exact_mod_cast le_top)
    have hE :=
      (ContinuousMultilinearMap.piFieldEquiv Real (Fin j)
        (tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p))).symm.continuous
        |>.comp_continuousOn hF
    simpa only [W, iteratedDeriv_eq_equiv_comp, Function.comp_apply] using hE
  have hW : ContinuousOn W (Icc a b) := hWopen.mono hKsub
  let jet : TensorEigenIdx (I := I) (M := M) q 0 0 → Real → Real :=
    fun i t => iteratedDeriv j (fun s => ulim s i) t
  have hjet (i : TensorEigenIdx (I := I) (M := M) q 0 0)
      (t : Real) (ht : t ∈ Icc a b) :
      (W t).coeff i = jet i t := by
    have htO : t ∈ Ioo (0 : Real) tau' := hKsub ht
    let L := tensorHsCoeffL (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (a := (m : Real) + p) i
    have hEq : Set.EqOn (fun z => L (U z)) (fun z => ulim z i)
        (Ioo (0 : Real) tau') := by
      intro z hz
      simpa only [L, U, J, q, tensorHsCoeffL_apply,
        tensorHsInclusion_coeff_apply] using
        galLimExt_coeff hτ.le hlim (m + k)
          ⟨hz.1.le, hz.2.le.trans htau'_tau⟩ i
    have hUt : ContDiffWithinAt Real j U (Ioo (0 : Real) tau') t :=
      (hU t htO).of_le (by exact_mod_cast le_top)
    have hcomm := DifferentialGeometry.Analysis.iteratedDerivWithin_clm_comp
      L hUt (uniqueDiffOn_Ioo (0 : Real) tau') htO
    calc
      (W t).coeff i = L (iteratedDeriv j U t) := by
        simp only [W, L, tensorHsCoeffL_apply]
      _ = L (iteratedDerivWithin j U (Ioo (0 : Real) tau') t) :=
        congrArg L
          (iteratedDerivWithin_of_isOpen (f := U) isOpen_Ioo htO).symm
      _ = iteratedDerivWithin j (fun z => L (U z))
          (Ioo (0 : Real) tau') t := hcomm.symm
      _ = iteratedDerivWithin j (fun z => ulim z i)
          (Ioo (0 : Real) tau') t :=
        iteratedDerivWithin_congr hEq htO
      _ = iteratedDeriv j (fun z => ulim z i) t :=
        iteratedDerivWithin_of_isOpen isOpen_Ioo htO
      _ = jet i t := rfl
  have hneg : Summable (fun i : TensorEigenIdx (I := I) (M := M) q 0 0 =>
      tensorSobolevWeight (I := I) (M := M) i
        (-(((m : Real) + p) - (m : Real)))) := by
    simpa only [tensorSobolevWeight, sub_self, add_sub_cancel_left,
      neg_inj] using hpsum
  obtain ⟨B, hB, hB_le⟩ :=
    mass_le_of_compact (I := I) (M := M) q hneg isCompact_Icc W hW jet
      (fun t ht i => hjet i t ht)
  refine ⟨B, hB, ?_⟩
  intro i t ht
  simpa only [jet] using hB_le i t ht




theorem galLim_mass0
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∀ m : Nat,
      ∃ B : TensorEigenIdx (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 → Real,
        Summable B ∧
        ∀ i, ∀ t ∈ Icc (0 : Real) tau,
          tensorSobolevWeight (I := I) (M := M) i (m : Real) *
            (ulim t i) ^ 2 ≤ B i := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M) q 0 0
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) q 0 0)
  obtain ⟨p, _hp, hpsum⟩ := htail
  intro m
  obtain ⟨k : Nat, hk⟩ := exists_nat_gt p
  have hmp : (m : Real) + p ≤ ((m + k : Nat) : Real) := by
    rw [Nat.cast_add]
    nlinarith
  let J := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0) hmp
  let W : Real → tensorHs (I := I) (M := M) q 0 0 ((m : Real) + p) :=
    fun t => J (galLimExt hτ.le hlim (m + k) t)
  have hW : Continuous W := by
    simpa only [W, Function.comp_apply] using
      J.continuous.comp (galLimExt_cont hτ.le hlim (m + k))
  have hcoeff : ∀ t ∈ Icc (0 : Real) tau, ∀ i,
      (W t).coeff i = ulim t i := by
    intro t ht i
    simpa only [W, J, q, tensorHsInclusion_coeff_apply] using
      galLimExt_coeff hτ.le hlim (m + k) ht i
  have hneg : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) q 0 0 =>
        tensorSobolevWeight (I := I) (M := M) i
          (-(((m : Real) + p) - (m : Real)))) := by
    simpa only [tensorSobolevWeight, sub_self, add_sub_cancel_left,
      neg_inj] using hpsum
  exact mass_le_of_compact (I := I) (M := M) q hneg isCompact_Icc
    W hW.continuousOn (fun i t => ulim t i) hcoeff



private theorem galLim_slice_cc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 ≤ tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    {t : Real} (ht : t ∈ Icc (0 : Real) tau) :
    ∃ U : SmoothCcTensor (S.family.metric (T : Real)) 0 0,
      (∀ m : Nat,
        ccTensorToHs (I := I) (M := M)
            (S.family.metric (T : Real)) 0 (m : Real) U =
          galLimExt hτ hlim m t) ∧
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i s => ulim s i) t =
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection := by
  classical
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M)
    (S.family.metric (T : Real)) 0 0
  have h0 : 0 ≤ ((0 : Nat) : Real) := by positivity
  let u : TensorL2 0 0 (S.family.metric (T : Real)) :=
    tensorHsToL2 (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0)
      hc h0 (galLimExt hτ hlim 0 t)
  have htail : EigenvalueTailSummable (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M)
        (S.family.metric (T : Real)) 0 0)
  have hmem : ∀ σ : Real, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 σ,
        tensorHsToL2 (I := I) (M := M)
            (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            hc hσ v = u := by
    intro σ hσ
    obtain ⟨m, hm⟩ := exists_nat_ge σ
    let J := tensorHsInclusion (I := I) (M := M)
      (g := S.family.metric (T : Real)) (r := 0) (s := 0) hm
    refine ⟨J (galLimExt hτ hlim m t), ?_⟩
    let b :=
      _root_.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) hc
    apply b.repr.injective
    ext i
    change tensorL2Coeff (I := I) (M := M) hc
        (tensorHsToL2 (I := I) (M := M)
          (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            hc hσ (J (galLimExt hτ hlim m t))) i =
      tensorL2Coeff (I := I) (M := M) hc u i
    rw [tensorHsToL2_tensorL2Coeff, tensorHsInclusion_coeff_apply,
      galLimExt_coeff hτ hlim m ht,
      show tensorL2Coeff (I := I) (M := M) hc u i = ulim t i by
        dsimp only [u]
        rw [tensorHsToL2_tensorL2Coeff]
        exact galLimExt_coeff hτ hlim 0 ht i]
  have hgate : SpectralSmoothRealizesAsSmooth (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 :=
    spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable
      (I := I) (M := M) (S.family.metric (T : Real)) 0 0 htail
  obtain ⟨U, hU⟩ := hgate u hmem
  have hrealize (m : Nat) :
      ccTensorToHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 (m : Real) U =
        galLimExt hτ hlim m t := by
    apply tensorHs.ext
    funext i
    rw [ccTensorToHs_coeff, SmoothCcTensor.toL2_apply, hU]
    dsimp only [u]
    rw [tensorHsToL2_tensorL2Coeff]
    calc
      (galLimExt hτ hlim 0 t).coeff i = ulim t i :=
        galLimExt_coeff hτ hlim 0 ht i
      _ = (galLimExt hτ hlim m t).coeff i :=
        (galLimExt_coeff hτ hlim m ht i).symm
  refine ⟨U, ?_, ?_⟩
  · intro m
    exact hrealize m
  · calc
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i s => ulim s i) t =
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i _ => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 U) i) 0 := by
            funext x
            unfold scalarSpecSum
            apply tsum_congr
            intro i
            have hcoeff : tensorL2Coeff (I := I) (M := M) hc
                (SmoothCcTensor.toL2 U) i = ulim t i := by
              rw [SmoothCcTensor.toL2_apply, hU]
              dsimp only [u]
              rw [tensorHsToL2_tensorL2Coeff]
              exact galLimExt_coeff hτ hlim 0 ht i
            simp only [hcoeff]
      _ = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection := by
        simpa only [hc] using scalarSpec_cc (I := I) (M := M)
          (S.family.metric (T : Real)) U



theorem galLim_initial
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i t => ulim t i) 0 =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection := by
  calc
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i t => ulim t i) 0 =
      scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
        (fun i _ => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0)
          (SmoothCcTensor.toL2 u0) i) 0 := by
      funext x
      unfold scalarSpecSum
      apply tsum_congr
      intro i
      change ulim 0 i * _ =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0)
          (SmoothCcTensor.toL2 u0) i * _
      rw [hlim.lim_init i]
    _ = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection :=
      scalarSpec_cc (I := I) (M := M) (S.family.metric (T : Real)) u0



theorem galLim_joint_cont
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ContinuousOn
      (fun q : Real × M =>
        scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
          (fun i t => ulim t i) q.1 q.2)
      (Icc (0 : Real) tau ×ˢ (Set.univ : Set M)) := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M) q 0 0
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) q 0 0)
  have hc : ∀ i : TensorEigenIdx (I := I) (M := M) q 0 0,
      ContDiffOn Real (0 : Nat) (fun t => ulim t i) Set.univ := by
    intro i
    exact contDiffOn_zero.mpr (hlim.lim_cont i).continuousOn
  have hmass : ∀ j : Nat, j ≤ 0 → ∀ m : Nat,
      ∃ B : TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
        Summable B ∧
        ∀ i t, t ∈ Icc (0 : Real) tau →
          tensorSobolevWeight (I := I) (M := M) i (m : Real) *
            (iteratedDeriv j (fun s => ulim s i) t) ^ 2 ≤ B i := by
    intro j hj m
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    obtain ⟨B, hB, hB_le⟩ :=
      galLim_mass0 (I := I) (M := M) hτ hlim m
    refine ⟨B, hB, ?_⟩
    intro i t ht
    simpa only [iteratedDeriv_zero] using hB_le i t ht
  exact (scalar_path_recon (I := I) (M := M) q htail hτ 0
    (fun i t => ulim t i) isOpen_univ (Set.subset_univ _) hc hmass).continuousOn




theorem galLim_joint_smooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ ⦃a b : Real⦄, 0 < a → a < b → b < tau' → ∀ N : Nat,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) (N : Nat)
          (fun q : Real × M =>
            scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
              (fun i t => ulim t i) q.1 q.2)
          (Icc a b ×ˢ (Set.univ : Set M)) := by
  classical
  obtain ⟨tau', htau', htau'_tau, hjet⟩ :=
    galLim_jet_mass (I := I) (M := M) hS hτ hlim
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M) q 0 0
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) q 0 0)
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro a b ha hab hb N
  let a₀ : Real := a / 2
  let b₀ : Real := (b + tau') / 2
  have ha₀ : 0 < a₀ := by
    dsimp only [a₀]
    linarith
  have hab₀ : a₀ ≤ b₀ := by
    dsimp only [a₀, b₀]
    linarith
  have hb₀ : b₀ < tau' := by
    dsimp only [b₀]
    linarith
  obtain ⟨hcoeff, hmass⟩ := hjet ha₀ hab₀ hb₀
  have hinner : Icc a b ⊆ Ioo a₀ b₀ := by
    intro t ht
    constructor <;> dsimp only [a₀, b₀] <;> linarith [ht.1, ht.2]
  refine scalar_path_recon (I := I) (M := M) q htail hab N
    (fun i t => ulim t i) isOpen_Ioo hinner ?_ ?_
  · intro i
    exact ((hcoeff i).mono Ioo_subset_Icc_self).of_le
      (by exact_mod_cast le_top)
  · intro j _hj m
    obtain ⟨B, hB, hB_le⟩ := hmass j m
    refine ⟨B, hB, ?_⟩
    intro i t ht
    exact hB_le i t (Ioo_subset_Icc_self (hinner ht))



theorem galLim_joint_top
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun q : Real × M =>
          scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i t => ulim t i) q.1 q.2)
        (Ioo (0 : Real) tau' ×ˢ (Set.univ : Set M)) := by
  obtain ⟨tau', htau', htau'_tau, hfin⟩ :=
    galLim_joint_smooth (I := I) (M := M) hS hτ hlim
  refine ⟨tau', htau', htau'_tau, ?_⟩
  rw [contMDiffOn_infty]
  intro N p hp
  let a : Real := p.1 / 2
  let b : Real := (p.1 + tau') / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith [hp.1.1]
  have hab : a < b := by
    dsimp only [a, b]
    linarith [hp.1.2]
  have hb : b < tau' := by
    dsimp only [b]
    linarith [hp.1.2]
  have hat : a < p.1 := by
    dsimp only [a]
    linarith [hp.1.1]
  have htb : p.1 < b := by
    dsimp only [b]
    linarith [hp.1.2]
  have hpab : p ∈ Icc a b ×ˢ (Set.univ : Set M) :=
    ⟨⟨hat.le, htb.le⟩, Set.mem_univ _⟩
  have hnhds : Icc a b ×ˢ (Set.univ : Set M) ∈ 𝓝 p :=
    prod_mem_nhds (Icc_mem_nhds hat htb) univ_mem
  exact ((hfin ha hab hb N) p hpab).contMDiffAt hnhds |>.contMDiffWithinAt



theorem galLim_slice_pos
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ t ∈ Ioo (0 : Real) tau',
        ContMDiff I 𝓘(Real) ∞
          (scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i s => ulim s i) t) := by
  obtain ⟨tau', htau', htau'_tau, htop⟩ :=
    galLim_joint_top (I := I) (M := M) hS hτ hlim
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro t ht
  have harg : ContMDiffOn I (𝓘(Real, Real).prod I) ∞
      (fun x : M => (t, x)) Set.univ :=
    (contMDiffOn_const (c := t)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun x : M => (t, x)) Set.univ
      (Ioo (0 : Real) tau' ×ˢ (Set.univ : Set M)) := by
    intro x _hx
    exact ⟨ht, Set.mem_univ x⟩
  exact contMDiffOn_univ.mp (htop.comp harg hmaps)



theorem galLim_pde
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, 0 < tau' ∧ tau' ≤ tau ∧
      ∀ t ∈ Ioo (0 : Real) tau', ∀ x : M,
        HasDerivAt
          (fun s =>
            scalarSpecSum (I := I) (M := M)
              (S.family.metric (T : Real))
              (fun i r => ulim r i) s x)
          (laplacianAt (I := I) (flowG (I := I) S) ((T : Real) - t)
              (scalarSpecSum (I := I) (M := M)
                (S.family.metric (T : Real))
                (fun i r => ulim r i) t) x +
            (conjCoeff (I := I) (M := M) S ((T : Real) - t) : M → Real) x *
              scalarSpecSum (I := I) (M := M)
                (S.family.metric (T : Real))
                (fun i r => ulim r i) t x) t := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0
  have htail : EigenvalueTailSummable (I := I) (M := M) q 0 0 :=
    eigenvalueTailSummable_of_countingBound (I := I) (M := M) q 0 0
      (weyl_eigenvalue_counting_bound_of_closed (I := I) (M := M) q 0 0)
  obtain ⟨tauJ, htauJ, htauJ_tau, hjet⟩ :=
    galLim_jet_mass (I := I) (M := M) hS hτ hlim
  obtain ⟨tauD, htauD, _htauD_one, _hreg, hcore⟩ :=
    lapDiffHs_core (I := I) (M := M) S.family hS.smoothMetric T
  obtain ⟨tauV, htauV, _htauV_tau, hlift⟩ :=
    galLimVel_lift (I := I) (M := M) hS hτ hlim
  obtain ⟨w, _hwcont, hw0, hwcan⟩ := hlift 0
  let tau' : Real := min tauJ (min tauD tauV)
  have htau' : 0 < tau' := by
    dsimp only [tau']
    exact lt_min htauJ (lt_min htauD htauV)
  have htau'_J : tau' ≤ tauJ := by
    dsimp only [tau']
    exact min_le_left _ _
  have htau'_D : tau' ≤ tauD := by
    dsimp only [tau']
    exact (min_le_right _ _).trans (min_le_left _ _)
  have htau'_V : tau' ≤ tauV := by
    dsimp only [tau']
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨tau', htau', htau'_J.trans htauJ_tau, ?_⟩
  intro t ht x
  have htJ : t < tauJ := ht.2.trans_le htau'_J
  have htDlt : t < tauD := ht.2.trans_le htau'_D
  have htVlt : t < tauV := ht.2.trans_le htau'_V
  have htTauOpen : t ∈ Ioo (0 : Real) tau :=
    ⟨ht.1, htJ.trans_le htauJ_tau⟩
  have htTau : t ∈ Icc (0 : Real) tau :=
    ⟨htTauOpen.1.le, htTauOpen.2.le⟩
  have htD : t ∈ Icc (0 : Real) tauD := ⟨ht.1.le, htDlt.le⟩
  have htV : t ∈ Icc (0 : Real) tauV := ⟨ht.1.le, htVlt.le⟩
  obtain ⟨U, hUall, hscalar⟩ :=
    galLim_slice_cc (I := I) (M := M) hτ.le hlim htTau
  let f : M → Real :=
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := by
    exact TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) U.toSection
  have hscalar' :
      scalarSpecSum (I := I) (M := M) q
          (fun i s => ulim s i) t = f := by
    simpa only [q, f] using hscalar
  let h : SmoothRiemannianMetric I M := S.family.metric ((T : Real) - t)
  let zeta : C^∞⟮I, M; Real⟯ :=
    conjCoeff (I := I) (M := M) S ((T : Real) - t)
  let W : SmoothCcTensor q 0 0 :=
    rawTensorConnLapSmooth (I := I) q 0 0 U +
      scalarLapDiffCc (I := I) q h U +
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
          (I := I) (M := M) q 0 0 zeta U
  let U3 : tensorHs (I := I) (M := M) q 0 0
      (((1 : Nat) : Real) + 2) :=
    ccTensorToHs (I := I) (M := M) q 0 (((1 : Nat) : Real) + 2) U
  let U1 : tensorHs (I := I) (M := M) q 0 0 ((1 : Nat) : Real) :=
    ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) U
  let Ubar : tensorHs (I := I) (M := M) q 0 0
      (((1 : Nat) : Real) + 2) :=
    tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((1 + 2 : Nat) : Real) = ((1 : Nat) : Real) + 2)
      (galLimExt hτ.le hlim (1 + 2) t)
  let U1bar : tensorHs (I := I) (M := M) q 0 0 ((1 : Nat) : Real) :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((1 : Nat) : Real) ≤ ((1 : Nat) : Real) + 2) Ubar
  have hUbar : Ubar = U3 := by
    apply tensorHs.ext
    funext i
    simp only [Ubar, tensorHs.castEquiv_coeff]
    have hi := congrArg
      (fun v : tensorHs (I := I) (M := M) q 0 0
          (((1 + 2 : Nat) : Real)) => v.coeff i)
      (hUall (1 + 2))
    simpa only [U3, q, ccTensorToHs_coeff] using hi.symm
  have hU1bar : U1bar = U1 := by
    apply tensorHs.ext
    funext i
    simp only [U1bar, tensorHsInclusion_coeff_apply]
    rw [hUbar]
    simp only [U3, U1, ccTensorToHs_coeff]
  have hlapCore :
      tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) U3 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (rawTensorConnLapSmooth (I := I) q 0 0 U) := by
    simpa only [U3] using
      scalarLapHs_core (I := I) (M := M) q ((1 : Nat) : Real) U
  have hdiffCore :
      lapDiffHs (I := I) (M := M) q h 1 U3 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (scalarLapDiffCc (I := I) q h U) := by
    simpa only [q, h, U3] using hcore (1 : Nat) t htD U
  have hpotCore :
      scalarPotHs (I := I) (M := M) q zeta 1 U1 =
        ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
            (I := I) (M := M) q 0 0 zeta U) := by
    simpa only [U1] using
      scalarPotHs_core (I := I) (M := M) q zeta 1 U
  have hvelExpand :
      galLimVelHs hτ.le hlim 1 t =
        tensorScaleLaplacian (I := I) (M := M)
            (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) Ubar +
          lapDiffHs (I := I) (M := M) q h 1 Ubar +
          scalarPotHs (I := I) (M := M) q zeta 1 U1bar := by
    rfl
  have hW1 :
      ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) W =
        galLimVelHs hτ.le hlim 1 t := by
    calc
      _ = ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (rawTensorConnLapSmooth (I := I) q 0 0 U) +
            ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (scalarLapDiffCc (I := I) q h U) +
            ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
                (I := I) (M := M) q 0 0 zeta U) := by
              simp only [W, ccTensorToHs_add]
      _ = tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0) ((1 : Nat) : Real) U3 +
            lapDiffHs (I := I) (M := M) q h 1 U3 +
            scalarPotHs (I := I) (M := M) q zeta 1 U1 := by
              rw [← hlapCore, ← hdiffCore, ← hpotCore]
      _ = _ := by
        rw [← hUbar, ← hU1bar]
        exact hvelExpand.symm
  let J10 := tensorHsInclusion (I := I) (M := M)
    (g := q) (r := 0) (s := 0)
    (by norm_num : ((0 : Nat) : Real) ≤ ((1 : Nat) : Real))
  have hcan :
      J10 (ccTensorToHs (I := I) (M := M) q 0 ((1 : Nat) : Real) W) =
        galLimVelCan hτ.le hlim 0 t := by
    have hz := congrArg J10 hW1
    simpa only [J10, galLimVelCan, q] using hz
  let tt : Icc (0 : Real) tauV := ⟨t, htV⟩
  have hWcoeff (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 W) i =
        (galLimVel hτ.le hlim t).coeff i := by
    have h1 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 ((0 : Nat) : Real) =>
        z.coeff i) hcan
    have h2 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 ((0 : Nat) : Real) =>
        z.coeff i) (hwcan tt)
    have h3 := congrArg
      (fun z : tensorHs (I := I) (M := M) q 0 0 (0 : Real) =>
        z.coeff i) (hw0 tt)
    calc
      _ = (ccTensorToHs (I := I) (M := M) q 0
          ((1 : Nat) : Real) W).coeff i := by
        simpa only [hc] using
          (ccTensorToHs_coeff (I := I) (M := M) q 0
            ((1 : Nat) : Real) W i).symm
      _ = (galLimVelCan hτ.le hlim 0 t).coeff i := by
        simpa only [J10, tensorHsInclusion_coeff_apply] using h1
      _ = (w tt).coeff i := by
        simpa only [tt] using h2.symm
      _ = (galLimVel hτ.le hlim t).coeff i := by
        simpa only [tt, tensorHsInclusion_coeff_apply] using h3
  let a : Real := t / 2
  let b : Real := (t + tauJ) / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith [ht.1]
  have hab : a < b := by
    dsimp only [a, b]
    linarith [htJ]
  have hb : b < tauJ := by
    dsimp only [b]
    linarith [htJ]
  obtain ⟨_hcoeff, hmass⟩ := hjet ha hab.le hb
  have hIcc : Icc a b ⊆ Ioo (0 : Real) tau := by
    intro s hs
    constructor
    · exact ha.trans_le hs.1
    · exact hs.2.trans_lt (hb.trans_le htauJ_tau)
  have htIcc : t ∈ Icc a b := by
    constructor <;> dsimp only [a, b] <;> linarith [ht.1, htJ]
  have hat : a < t := by
    dsimp only [a]
    linarith [ht.1]
  have htb : t < b := by
    dsimp only [b]
    linarith [htJ]
  have hmass1 : ∀ j : Nat, j ≤ 1 → ∀ m : Nat,
      ∃ B : TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
        Summable B ∧
        ∀ i s, s ∈ Icc a b →
          tensorSobolevWeight (I := I) (M := M) i (m : Real) *
            (iteratedDeriv j (fun r => ulim r i) s) ^ 2 ≤ B i := by
    intro j _hj m
    simpa only [q] using hmass j m
  have hderiv :
      HasDerivAt
        (fun s => scalarSpecSum (I := I) (M := M) q
          (fun i r => ulim r i) s x)
        (scalarSpecSum (I := I) (M := M) q
          (fun i s => deriv (fun r => ulim r i) s) t x) t := by
    exact (scalarSpec_d1 (I := I) (M := M) q htail hab
      (fun i r => ulim r i) isOpen_Ioo hIcc
      (fun i => galLim_mode_c1 hτ hlim i) hmass1 x htIcc).hasDerivAt
        (Icc_mem_nhds hat htb)
  have hderivSeries :
      scalarSpecSum (I := I) (M := M) q
          (fun i s => deriv (fun r => ulim r i) s) t x =
        scalarSpecSum (I := I) (M := M) q
          (fun i _ => (galLimVel hτ.le hlim t).coeff i) t x := by
    unfold scalarSpecSum
    apply tsum_congr
    intro i
    change deriv (fun r => ulim r i) t * _ =
      (galLimVel hτ.le hlim t).coeff i * _
    rw [(galLim_mode_deriv hτ hlim htTauOpen i).deriv]
  have hseriesW :
      scalarSpecSum (I := I) (M := M) q
          (fun i _ => (galLimVel hτ.le hlim t).coeff i) t x =
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x := by
    calc
      _ = scalarSpecSum (I := I) (M := M) q
          (fun i _ => tensorL2Coeff (I := I) (M := M) hc
            (SmoothCcTensor.toL2 W) i) 0 x := by
              unfold scalarSpecSum
              apply tsum_congr
              intro i
              change (galLimVel hτ.le hlim t).coeff i * _ =
                tensorL2Coeff (I := I) (M := M) hc
                  (SmoothCcTensor.toL2 W) i * _
              rw [hWcoeff i]
      _ = _ := congrFun (scalarSpec_cc (I := I) (M := M) q W) x
  have htime :
      HasDerivAt
        (fun s => scalarSpecSum (I := I) (M := M) q
          (fun i r => ulim r i) s x)
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x) t :=
    hderiv.congr_deriv (hderivSeries.trans hseriesW)
  have hWscalar :
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) W.toSection x =
        Δ_g (I := I) h hf x + (zeta : M → Real) x * f x := by
    simp only [W, SmoothCcTensor.toSection_add, TensorRSField.scalar0_add,
      Pi.add_apply, rawLap_cc_scalar (I := I) (M := M) q U x,
      scalarLapDiff_eq (I := I) (M := M) q h U x,
      DifferentialGeometry.Integral.Connection.scalar0_smul_cc
        (I := I) (M := M) q zeta U x, f]
    ring
  have hlap :
      laplacianAt (I := I) (flowG (I := I) S) ((T : Real) - t) f x =
        Δ_g (I := I) h hf x := by
    simpa only [h] using
      (laplacianAt_eq_delta (I := I) (M := M)
        (flowG (I := I) S) ((T : Real) - t) hf (by rfl) x)
  refine htime.congr_deriv ?_
  rw [hscalar']
  rw [hlap]
  simpa only [zeta] using hWscalar



theorem heatpot_of_gallim
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hS : IsSolutionOn (I := I) S) (hτ : 0 < tau)
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ tau ∧
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (RealTimeInterval.closed 0 tau' htau'.le)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
        (fun s x =>
          (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
        (fun s x =>
          scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
            (fun i r => ulim r i) s x) := by
  obtain ⟨tauP, htauP, htauP_tau, hpde⟩ :=
    galLim_pde (I := I) (M := M) hS hτ hlim
  obtain ⟨tauS, htauS, _htauS_tau, hsmooth⟩ :=
    galLim_joint_top (I := I) (M := M) hS hτ hlim
  obtain ⟨tauL, htauL, _htauL_tau, hslice⟩ :=
    galLim_slice_pos (I := I) (M := M) hS hτ hlim
  have hcont := galLim_joint_cont (I := I) (M := M) hτ hlim
  let rho : Real := min tauP (min tauS tauL)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min htauP (lt_min htauS htauL)
  have hrhoP : rho ≤ tauP := by
    dsimp only [rho]
    exact min_le_left _ _
  have hrhoS : rho ≤ tauS := by
    dsimp only [rho]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrhoL : rho ≤ tauL := by
    dsimp only [rho]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let tau' : Real := rho / 2
  have htau' : 0 < tau' := by
    dsimp only [tau']
    positivity
  have htau'P : tau' < tauP := by
    dsimp only [tau']
    exact (half_lt_self hrho).trans_le hrhoP
  have htau'S : tau' < tauS := by
    dsimp only [tau']
    exact (half_lt_self hrho).trans_le hrhoS
  have htau'L : tau' < tauL := by
    dsimp only [tau']
    exact (half_lt_self hrho).trans_le hrhoL
  have htau'_tau : tau' ≤ tau :=
    (htau'P.trans_le htauP_tau).le
  refine ⟨tau', htau', htau'_tau, ?_⟩
  refine
    { jointSmooth := ?_
      jointCont := ?_
      sliceSmooth := ?_
      equation := ?_ }
  · exact hsmooth.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨⟨hs.1, hs.2.trans htau'S⟩, hx⟩)
  · exact hcont.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨⟨hs.1, hs.2.trans htau'_tau⟩, hx⟩)
  · intro s hs
    change s ∈ Icc (0 : Real) tau' at hs
    by_cases hs0 : s = 0
    · subst s
      rw [galLim_initial (I := I) (M := M) hlim]
      exact TensorRSField.scalar0_smooth
        (n := (∞ : WithTop ℕ∞)) u0.toSection
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      exact hslice s ⟨hspos, hs.2.trans_lt htau'L⟩
  · intro s hs x
    change s ∈ Ioo (0 : Real) tau' at hs
    have hsP : s ∈ Ioo (0 : Real) tauP :=
      ⟨hs.1, hs.2.trans htau'P⟩
    simpa only [reverseFamily] using hpde s hsP x




theorem heatpot_exists
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
          (fun s x =>
            (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
          u ∧
        u 0 = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection := by
  obtain ⟨tau, htau, htau_one, hsubseq⟩ :=
    scalar_gal_subseq (I := I) (M := M) S hS T
  obtain ⟨V, phi, ulim, hlim⟩ := hsubseq u0
  obtain ⟨tau', htau', htau'_tau, hpot⟩ :=
    heatpot_of_gallim (I := I) (M := M) hS htau hlim
  let u : Real → M → Real := fun s x =>
    scalarSpecSum (I := I) (M := M) (S.family.metric (T : Real))
      (fun i r => ulim r i) s x
  refine ⟨tau', htau', htau'_tau.trans htau_one, u, ?_, ?_⟩
  · simpa only [u] using hpot
  · simpa only [u] using galLim_initial (I := I) (M := M) hlim




theorem conj_heat_exists
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        IsConjHeatOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (flowG (I := I) S) S.scalar u (T : Real) ∧
        u (T : Real) =
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection := by
  obtain ⟨tau', htau', htau'_one, v, hv, hv0⟩ :=
    heatpot_exists (I := I) (M := M) S hS T u0
  have hv' :
      DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
        (RealTimeInterval.closed 0 tau' htau'.le)
        (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
        (fun s x => -S.scalar ((T : Real) - s) x) v := by
    simpa only [conjCoeff_apply] using hv
  let u : Real → M → Real := reverseHeat (T : Real) v
  refine ⟨tau', htau', htau'_one, u, ?_, ?_⟩
  · simpa only [u] using
      conj_heat_of_pot (I := I) (M := M)
        (RealTimeInterval.closed 0 tau' htau'.le)
        (flowG (I := I) S) S.scalar v (T : Real) hv'
  · change v ((T : Real) - (T : Real)) =
      TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection
    simpa only [sub_self] using hv0



theorem gallim_nonneg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0)
    (hinit : ∀ x : M,
      0 ≤ TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection x) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
          (fun s x =>
            (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
          u ∧
        u 0 = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection ∧
        ∀ s ∈ Set.Icc (0 : Real) tau', ∀ x : M, 0 ≤ u s x := by
  obtain ⟨tauH, htauH, htauH_one, u, hu, hu0⟩ :=
    heatpot_exists (I := I) (M := M) S hS T u0
  obtain ⟨tauC, htauC, _htauC_one, C, _hCnonneg, hC⟩ :=
    conjCoeff_bound (I := I) (M := M) S hS T
  let tau' : Real := min tauH tauC
  have htau' : 0 < tau' := by
    simpa only [tau'] using lt_min htauH htauC
  have htau'_H : tau' ≤ tauH := min_le_left _ _
  have htau'_C : tau' ≤ tauC := min_le_right _ _
  have htau'_one : tau' ≤ 1 := htau'_H.trans htauH_one
  have hcarrier :
      (RealTimeInterval.closed 0 tau' htau'.le).carrier ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).carrier := by
    change Set.Icc (0 : Real) tau' ⊆ Set.Icc (0 : Real) tauH
    exact Set.Icc_subset_Icc le_rfl htau'_H
  have hregular :
      (RealTimeInterval.closed 0 tau' htau'.le).regular ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).regular := by
    change Set.Ioo (0 : Real) tau' ⊆ Set.Ioo (0 : Real) tauH
    intro s hs
    exact ⟨hs.1, hs.2.trans_le htau'_H⟩
  have hu' := hu.mono hcarrier hregular
  have hV : ∀ s : Real, s ∈ Set.Icc (0 : Real) tau' → ∀ x : M,
      (conjCoeff (I := I) (M := M) S
        ((T : Real) - s) : M → Real) x ≤ C := by
    intro s hs x
    exact (le_abs_self _).trans
      (hC s ⟨hs.1, hs.2.trans htau'_C⟩ x)
  have huinit : ∀ x : M, 0 ≤ u 0 x := by
    intro x
    rw [hu0]
    exact hinit x
  have hnonneg :=
    DifferentialGeometry.Analysis.Parabolic.heat_pot_nonneg
      (I := I) (M := M)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      htau'.le
      (fun s x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
      u hu' C hV huinit
  exact ⟨tau', htau', htau'_one, u, hu', hu0, hnonneg⟩



theorem gallim_pos
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime)
    (u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0)
    (hinit : ∀ x : M,
      0 < TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection x) :
    ∃ tau' : Real, ∃ htau' : 0 < tau', tau' ≤ 1 ∧
      ∃ u : Real → M → Real,
        DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
          (RealTimeInterval.closed 0 tau' htau'.le)
          (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
          (fun s x =>
            (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
          u ∧
        u 0 = TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) u0.toSection ∧
        ∀ s ∈ Set.Icc (0 : Real) tau', ∀ x : M, 0 < u s x := by
  obtain ⟨tauH, htauH, htauH_one, u, hu, hu0⟩ :=
    heatpot_exists (I := I) (M := M) S hS T u0
  obtain ⟨tauC, htauC, _htauC_one, C, _hCnonneg, hC⟩ :=
    conjCoeff_bound (I := I) (M := M) S hS T
  let tau' : Real := min tauH tauC
  have htau' : 0 < tau' := by
    simpa only [tau'] using lt_min htauH htauC
  have htau'_H : tau' ≤ tauH := min_le_left _ _
  have htau'_C : tau' ≤ tauC := min_le_right _ _
  have htau'_one : tau' ≤ 1 := htau'_H.trans htauH_one
  have hcarrier :
      (RealTimeInterval.closed 0 tau' htau'.le).carrier ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).carrier := by
    change Set.Icc (0 : Real) tau' ⊆ Set.Icc (0 : Real) tauH
    exact Set.Icc_subset_Icc le_rfl htau'_H
  have hregular :
      (RealTimeInterval.closed 0 tau' htau'.le).regular ⊆
        (RealTimeInterval.closed 0 tauH htauH.le).regular := by
    change Set.Ioo (0 : Real) tau' ⊆ Set.Ioo (0 : Real) tauH
    intro s hs
    exact ⟨hs.1, hs.2.trans_le htau'_H⟩
  have hu' := hu.mono hcarrier hregular
  have hV : ∀ s : Real, s ∈ Set.Icc (0 : Real) tau' → ∀ x : M,
      |(conjCoeff (I := I) (M := M) S
        ((T : Real) - s) : M → Real) x| ≤ C := by
    intro s hs x
    exact hC s ⟨hs.1, hs.2.trans htau'_C⟩ x
  have huinit : ∀ x : M, 0 < u 0 x := by
    intro x
    rw [hu0]
    exact hinit x
  have hpos :=
    DifferentialGeometry.Analysis.Parabolic.heat_pot_pos
      (I := I) (M := M)
      (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
      htau'.le
      (fun s x =>
        (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
      u hu' C hV huinit
  exact ⟨tau', htau', htau'_one, u, hu', hu0, hpos⟩


theorem gallim_unit_pos
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    IsEmpty M ∨
      ∃ tau : Real, ∃ htau : 0 < tau, tau ≤ 1 ∧
        ∃ u : Real → M → Real,
          DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
            (RealTimeInterval.closed 0 tau htau.le)
            (reverseFamily (I := I) (M := M) (flowG (I := I) S) (T : Real))
            (fun s x =>
              (conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x)
            u ∧
          (∀ s ∈ Set.Icc (0 : Real) tau, ∀ x : M, 0 < u s x) ∧
          ∀ s ∈ Set.Icc (0 : Real) tau,
            (∫ x, u s x ∂(volumeMeasureFamily (I := I) (M := M)
              (reverseFamily (I := I) (M := M)
                (flowG (I := I) S) (T : Real)) s)) = 1 := by
  rcases unit_init_or_empty (I := I) (M := M)
      (S.family.metric (T : Real)) with hM | ⟨u0, hinit, hunit⟩
  · exact Or.inl hM
  · right
    obtain ⟨tau, htau, htau_one, u, hu, hu0, hpos⟩ :=
      gallim_pos (I := I) (M := M) S hS T u0 hinit
    obtain ⟨tau', htau', htau'_tau, hu', hmass⟩ :=
      heatpot_mass_eq (I := I) (M := M) S hS T htau hu
    refine ⟨tau', htau', htau'_tau.trans htau_one, u, hu', ?_, ?_⟩
    · intro s hs x
      exact hpos s ⟨hs.1, hs.2.trans htau'_tau⟩ x
    · have hmass0 :
          (∫ x, u 0 x ∂(volumeMeasureFamily (I := I) (M := M)
            (reverseFamily (I := I) (M := M)
              (flowG (I := I) S) (T : Real)) 0)) = 1 := by
        rw [hu0]
        simpa only [volumeMeasureFamily, metricFamilyForMeasure,
          riemannianMeasureFamily, reverseFamily, flowG, sub_zero] using hunit
      intro s hs
      exact (hmass s hs).trans hmass0

end DifferentialGeometry.PDE.RicciFlow.Entropy
