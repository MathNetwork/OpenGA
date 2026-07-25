import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTrace
import DifferentialGeometry.Analysis.Spectral.Intrinsic.GalerkinCompactness
import DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinEnergy

set_option autoImplicit false










noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

open Classical in



structure IsConjGalSubseq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (tau : Real) (u0 : SmoothCcTensor
      (S.family.metric (T : Real)) 0 0)
    (V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real)
    (phi : Nat → Nat)
    (ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real) : Prop where
  cont : ∀ N i, i ∈ eigenFinset (I := I) (M := M)
    (S.family.metric (T : Real)) 0 0 N →
    ContinuousOn (fun t => V N t i) (Icc (0 : Real) tau)
  deriv : ∀ N t, t ∈ Ico (0 : Real) tau →
    ∀ i, i ∈ eigenFinset (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 N →
      HasDerivWithinAt (fun r => V N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V N t i +
          (scalarGalPert (I := I) (M := M) S T t
            (scalarGalVec (I := I) (M := M)
              (S.family.metric (T : Real))
              (eigenFinset (I := I) (M := M)
                (S.family.metric (T : Real)) 0 0 N) (V N t) 2)).coeff i)
        (Ici t) t
  init : ∀ N i, i ∈ eigenFinset (I := I) (M := M)
    (S.family.metric (T : Real)) 0 0 N →
    V N 0 i = tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        (S.family.metric (T : Real)) 0 0) (SmoothCcTensor.toL2 u0) i
  support : ∀ N t i, i ∉ eigenFinset (I := I) (M := M)
    (S.family.metric (T : Real)) 0 0 N → V N t i = 0
  pert_cont : ContinuousOn
    (fun t => scalarGalPert (I := I) (M := M) S T t)
    (Icc (0 : Real) tau)
  energy : ∀ k : Nat, ∃ Bound : Real, ∀ N t,
    t ∈ Icc (0 : Real) tau →
      galerkinEnergy (I := I) (M := M)
        (eigenFinset (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 N) (V N) (k : Real) t ≤ Bound
  mono : StrictMono phi
  lim_cont : ∀ i, Continuous (fun t => ulim t i)
  conv : ∀ i, TendstoUniformlyOn (fun n t => V (phi n) t i)
    (fun t => ulim t i) atTop (Icc (0 : Real) tau)
  lim_init : ∀ i, ulim 0 i = tensorL2Coeff (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) (SmoothCcTensor.toL2 u0) i
  lim_mass : ∀ k : Nat, ∃ Bound : Real, ∀ t ∈ Icc (0 : Real) tau,
    Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (k : Real) *
      (ulim t i) ^ 2) ∧
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (k : Real) *
        (ulim t i) ^ 2 ≤ Bound

private theorem galPert_norm_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (t : Real) (C1 : NNReal)
    (hLap : ‖lapDiffA20 (I := I) (M := M) S.family T t‖ ≤ 1)
    (hPot : ‖conjA1 (I := I) (M := M) S T t‖ ≤ (C1 : Real))
    (v : tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 2) :
    ‖scalarGalPert (I := I) (M := M) S T t v‖ ≤
      (1 + (C1 : Real) *
        ‖tensorHsInclusion (I := I) (M := M)
          (g := S.family.metric (T : Real)) (r := 0) (s := 0)
          (show (1 : Real) ≤ 2 by norm_num)‖) * ‖v‖ := by
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let Inc : tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 1 :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (show (1 : Real) ≤ 2 by norm_num)
  let Lap : tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 0 :=
    lapDiffA20 (I := I) (M := M) S.family T t
  let Pot : tensorHs (I := I) (M := M) q 0 0 1 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 0 :=
    conjA1 (I := I) (M := M) S T t
  calc
    ‖scalarGalPert (I := I) (M := M) S T t v‖ =
        ‖Lap v + Pot (Inc v)‖ := by
      simp only [scalarGalPert, Lap, Pot, Inc, q,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
    _ ≤ ‖Lap v‖ + ‖Pot (Inc v)‖ := norm_add_le _ _
    _ ≤ ‖Lap‖ * ‖v‖ + ‖Pot‖ * ‖Inc v‖ :=
      add_le_add (Lap.le_opNorm v) (Pot.le_opNorm (Inc v))
    _ ≤ ‖Lap‖ * ‖v‖ + ‖Pot‖ * (‖Inc‖ * ‖v‖) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Inc.le_opNorm v) (norm_nonneg Pot))
    _ ≤ 1 * ‖v‖ + (C1 : Real) * (‖Inc‖ * ‖v‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hLap (norm_nonneg v))
        (mul_le_mul_of_nonneg_right hPot
          (mul_nonneg (norm_nonneg Inc) (norm_nonneg v)))
    _ = (1 + (C1 : Real) * ‖tensorHsInclusion (I := I) (M := M)
          (g := S.family.metric (T : Real)) (r := 0) (s := 0)
          (show (1 : Real) ≤ 2 by norm_num)‖) * ‖v‖ := by
      dsimp only [Inc, q]
      ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem gal_lim_mass
    (q : SmoothRiemannianMetric I M) {tau : Real}
    (Fs : Nat → Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (phi : Nat → Nat)
    (V : Nat → Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
    (ulim : Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
    (hFs_phi : Tendsto (fun n => Fs (phi n)) atTop atTop)
    (hconv : ∀ i, TendstoUniformlyOn
      (fun n t => V (phi n) t i) (fun t => ulim t i)
      atTop (Icc (0 : Real) tau))
    (henergy : ∀ k : Nat, ∃ Bound : Real, ∀ N t,
      t ∈ Icc (0 : Real) tau →
        galerkinEnergy (I := I) (M := M) (Fs N) (V N) (k : Real) t ≤ Bound) :
    ∀ k : Nat, ∃ Bound : Real, ∀ t ∈ Icc (0 : Real) tau,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i (k : Real) *
        (ulim t i) ^ 2) ∧
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (k : Real) *
        (ulim t i) ^ 2 ≤ Bound := by
  intro k
  obtain ⟨Bound, hBound⟩ := henergy k
  refine ⟨Bound, ?_⟩
  intro t ht
  apply fatou_sq_mass (fun n => Fs (phi n)) hFs_phi
    (fun i => tensorSobolevWeight (I := I) (M := M) i (k : Real))
    (fun i => tensorSobolevWeight_nonneg (I := I) (M := M) i (k : Real))
    (fun n i => V (phi n) t i) (ulim t)
    (fun i => (hconv i).tendsto_at ht) Bound
  intro n
  simpa only [galerkinEnergy] using hBound (phi n) t ht

open Classical in
private theorem gal_lim_init
    {Idx : Type*} {tau : Real}
    (Fs : Nat → Finset Idx) (phi : Nat → Nat)
    (V : Nat → Real → Idx → Real) (ulim : Real → Idx → Real)
    (a : Idx → Real) (htau0 : (0 : Real) ∈ Icc (0 : Real) tau)
    (hFs_phi : Tendsto (fun n => Fs (phi n)) atTop atTop)
    (hconv : ∀ i, TendstoUniformlyOn
      (fun n t => V (phi n) t i) (fun t => ulim t i)
      atTop (Icc (0 : Real) tau))
    (hinit : ∀ N i, i ∈ Fs N → V N 0 i = a i) :
    ∀ i, ulim 0 i = a i := by
  intro i
  have hlim := (hconv i).tendsto_at htau0
  have hev : ∀ᶠ n in atTop, i ∈ Fs (phi n) := by
    have hsingle : ∀ᶠ n in atTop, ({i} : Finset Idx) ⊆ Fs (phi n) :=
      hFs_phi.eventually_ge_atTop {i}
    filter_upwards [hsingle] with n hn
    exact hn (Finset.mem_singleton_self i)
  have hinit_lim : Tendsto (fun n => V (phi n) 0 i) atTop (𝓝 (a i)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hev] with n hn
    exact hinit (phi n) i hn
  exact tendsto_nhds_unique hlim hinit_lim

open Classical in
private theorem supp_right_lip
    {Idx : Type*} {tau : Real}
    (F : Nat → Finset Idx) (u du : Nat → Real → Idx → Real)
    (L : Idx → NNReal)
    (hcont : ∀ N i, i ∈ F N →
      ContinuousOn (fun t => u N t i) (Icc (0 : Real) tau))
    (hderiv : ∀ N t, t ∈ Ico (0 : Real) tau → ∀ i, i ∈ F N →
      HasDerivWithinAt (fun r => u N r i) (du N t i) (Ici t) t)
    (hsupp : ∀ N t i, i ∉ F N → u N t i = 0)
    (hdu : ∀ N t, t ∈ Ico (0 : Real) tau → ∀ i, i ∈ F N →
      ‖du N t i‖ ≤ (L i : Real)) :
    ∀ N i, LipschitzOnWith (L i) (fun t => u N t i)
      (Icc (0 : Real) tau) := by
  intro N i
  have hc : ContinuousOn (fun t => u N t i) (Icc (0 : Real) tau) := by
    by_cases hi : i ∈ F N
    · exact hcont N i hi
    · have hz : (fun t : Real => u N t i) = fun _ => 0 := by
        funext t
        exact hsupp N t i hi
      rw [hz]
      exact continuousOn_const
  let f' : Real → Real := fun t => if i ∈ F N then du N t i else 0
  apply right_lipschitz (f' := f') hc
  · intro t ht
    by_cases hi : i ∈ F N
    · simpa only [f', if_pos hi] using hderiv N t ht i hi
    · have hz : (fun r : Real => u N r i) = fun _ => 0 := by
        funext r
        exact hsupp N r i hi
      rw [hz]
      simpa only [f', if_neg hi] using
        (hasDerivWithinAt_const t (Ici t) (0 : Real))
  · intro t ht
    by_cases hi : i ∈ F N
    · simpa only [f', if_pos hi] using hdu N t ht i hi
    · simpa only [f', if_neg hi, norm_zero] using (L i).property

set_option maxHeartbeats 800000 in



theorem scalar_gal_subseq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    let q := S.family.metric (T : Real)
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∀ u0 : SmoothCcTensor q 0 0,
        ∃ V : Nat → Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
        ∃ phi : Nat → Nat,
        ∃ ulim : Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
          IsConjGalSubseq (I := I) (M := M) S T tau u0 V phi ulim := by
  classical
  dsimp only
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have hgal := scalar_gal_bound (I := I) (M := M) S hS T
  dsimp only at hgal
  obtain ⟨tauE, htauE, htauE_one, hsolve⟩ := hgal
  obtain ⟨tau2, htau2, _htau2_one, hcont2, _hmeas2, hbound2,
      _hboundAE2⟩ :=
    lapDiffA20_short (I := I) (M := M) S.family hS.smoothMetric T
      (epsilon := (1 : Real)) zero_lt_one
  obtain ⟨tau1, htau1, _htau1_one, C1, hcont1, _hmeas1, hbound1,
      _hboundAE1⟩ := conjA1_short (I := I) (M := M) S hS T
  let tau : Real := min tauE (min tau2 tau1)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min htauE (lt_min htau2 htau1)
  have htauE' : tau ≤ tauE := min_le_left _ _
  have htau2' : tau ≤ tau2 :=
    (min_le_right tauE (min tau2 tau1)).trans (min_le_left tau2 tau1)
  have htau1' : tau ≤ tau1 :=
    (min_le_right tauE (min tau2 tau1)).trans (min_le_right tau2 tau1)
  have htau_one : tau ≤ 1 := htauE'.trans htauE_one
  have hIccE : Icc (0 : Real) tau ⊆ Icc (0 : Real) tauE :=
    fun _ ht => ⟨ht.1, ht.2.trans htauE'⟩
  have hIcoE : Ico (0 : Real) tau ⊆ Ico (0 : Real) tauE :=
    fun _ ht => ⟨ht.1, ht.2.trans_le htauE'⟩
  have hIcc2 : Icc (0 : Real) tau ⊆ Icc (0 : Real) tau2 :=
    fun _ ht => ⟨ht.1, ht.2.trans htau2'⟩
  have hIcc1 : Icc (0 : Real) tau ⊆ Icc (0 : Real) tau1 :=
    fun _ ht => ⟨ht.1, ht.2.trans htau1'⟩
  refine ⟨tau, htau, htau_one, ?_⟩
  intro u0
  let Fs : Nat → Finset (TensorEigenIdx (I := I) (M := M) q 0 0) :=
    eigenFinset (I := I) (M := M) q 0 0
  obtain ⟨V, hcontE, hderivE, hinit, hsupp, henergyE⟩ := hsolve u0 Fs
  have hcont : ∀ N i, i ∈ Fs N →
      ContinuousOn (fun t => V N t i) (Icc (0 : Real) tau) := by
    intro N i hi
    exact (hcontE N i hi).mono hIccE
  have hderiv : ∀ N t, t ∈ Ico (0 : Real) tau → ∀ i, i ∈ Fs N →
      HasDerivWithinAt (fun r => V N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V N t i +
          (scalarGalPert (I := I) (M := M) S T t
            (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i)
        (Ici t) t := by
    intro N t ht i hi
    exact hderivE N t (hIcoE ht) i hi
  have henergy : ∀ k : Nat, ∃ Bound : Real, ∀ N t,
      t ∈ Icc (0 : Real) tau →
        galerkinEnergy (I := I) (M := M) (Fs N) (V N) (k : Real) t ≤ Bound := by
    intro k
    obtain ⟨Bound, hBound⟩ := henergyE k
    exact ⟨Bound, fun N t ht => hBound N t (hIccE ht)⟩
  have hpert_cont : ContinuousOn
      (fun t => scalarGalPert (I := I) (M := M) S T t)
      (Icc (0 : Real) tau) := by
    let Inc : tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
        tensorHs (I := I) (M := M) q 0 0 1 :=
      tensorHsInclusion (I := I) (M := M)
        (g := q) (r := 0) (s := 0) (show (1 : Real) ≤ 2 by norm_num)
    have hPot := (hcont1.mono hIcc1).clm_comp
      (continuousOn_const : ContinuousOn (fun _ : Real => Inc) (Icc 0 tau))
    simpa only [scalarGalPert, q, Inc] using (hcont2.mono hIcc2).add hPot
  obtain ⟨B0, hB0⟩ := henergy 0
  obtain ⟨B2, hB2⟩ := henergy 2
  have htau0 : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, htau.le⟩
  have hB0_nonneg : 0 ≤ B0 :=
    (galerkinEnergy_nonneg (I := I) (M := M) (Fs 0) (V 0) 0 0).trans
      (by simpa only [Nat.cast_zero] using hB0 0 0 htau0)
  have hcoord_sq (N : Nat) (t : Real) (ht : t ∈ Icc (0 : Real) tau)
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      (V N t i) ^ 2 ≤ B0 := by
    by_cases hi : i ∈ Fs N
    · have hterm :
          tensorSobolevWeight (I := I) (M := M) i 0 * (V N t i) ^ 2 ≤
            galerkinEnergy (I := I) (M := M) (Fs N) (V N) 0 t := by
        rw [galerkinEnergy]
        exact Finset.single_le_sum (fun j _ =>
          mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) j 0)
            (sq_nonneg _)) hi
      calc
        (V N t i) ^ 2 =
            tensorSobolevWeight (I := I) (M := M) i 0 * (V N t i) ^ 2 := by
              rw [tensorSobolevWeight_zero, one_mul]
        _ ≤ galerkinEnergy (I := I) (M := M) (Fs N) (V N) 0 t := hterm
        _ ≤ B0 := by simpa only [Nat.cast_zero] using hB0 N t ht
    · rw [hsupp N t i hi]
      simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hB0_nonneg
  have hcoord (N : Nat) (t : Real) (ht : t ∈ Icc (0 : Real) tau)
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      |V N t i| ≤ Real.sqrt B0 := by
    calc
      |V N t i| = Real.sqrt ((V N t i) ^ 2) :=
        (Real.sqrt_sq_eq_abs (V N t i)).symm
      _ ≤ Real.sqrt B0 := Real.sqrt_le_sqrt (hcoord_sq N t ht i)
  let Inc : tensorHs (I := I) (M := M) q 0 0 2 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 1 :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (show (1 : Real) ≤ 2 by norm_num)
  let Kpert : Real := 1 + (C1 : Real) * ‖Inc‖
  have hKpert : 0 ≤ Kpert := by
    dsimp only [Kpert]
    positivity
  have hvec_norm (N : Nat) (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
      ‖scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2‖ ≤
        Real.sqrt B2 := by
    have hsq :
        ‖scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2‖ ^ 2 ≤ B2 := by
      rw [galVec_norm_sq (I := I) (M := M)]
      simpa only [galerkinEnergy] using hB2 N t ht
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt
  have hpert_apply (t : Real) (ht : t ∈ Icc (0 : Real) tau)
      (v : tensorHs (I := I) (M := M) q 0 0 2) :
      ‖scalarGalPert (I := I) (M := M) S T t v‖ ≤ Kpert * ‖v‖ := by
    simpa only [Kpert, Inc, q] using
      galPert_norm_le (I := I) (M := M) S T t C1
        (hbound2 t (hIcc2 ht)) (hbound1 t (hIcc1 ht)) v
  have hforce (N : Nat) (t : Real) (ht : t ∈ Icc (0 : Real) tau)
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      |(scalarGalPert (I := I) (M := M) S T t
        (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i| ≤
          Kpert * Real.sqrt B2 := by
    let v := scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2
    have hcoeff := abs_coeff_le_norm (I := I) (M := M) i
      (scalarGalPert (I := I) (M := M) S T t v)
    have hcoeff' :
        |(scalarGalPert (I := I) (M := M) S T t v).coeff i| ≤
          ‖scalarGalPert (I := I) (M := M) S T t v‖ := by
      simpa only [tensorSobolevWeight_zero, Real.sqrt_one, inv_one, one_mul]
        using hcoeff
    exact hcoeff'.trans ((hpert_apply t ht v).trans
      (mul_le_mul_of_nonneg_left (hvec_norm N t ht) hKpert))
  let rhs : Nat → Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real :=
    fun N t i =>
      -(TensorEigenIdx.lambda (I := I) (M := M) i) * V N t i +
        (scalarGalPert (I := I) (M := M) S T t
          (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i
  let L : TensorEigenIdx (I := I) (M := M) q 0 0 → NNReal := fun i =>
    ⟨TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
      Kpert * Real.sqrt B2, by
        exact add_nonneg
          (mul_nonneg (tensor_lambda_nonneg (I := I) (M := M) i)
            (Real.sqrt_nonneg B0))
          (mul_nonneg hKpert (Real.sqrt_nonneg B2))⟩
  have hrhs_bound (N : Nat) (t : Real) (ht : t ∈ Ico (0 : Real) tau)
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) (hi : i ∈ Fs N) :
      ‖rhs N t i‖ ≤ (L i : Real) := by
    have ht' : t ∈ Icc (0 : Real) tau := Set.Ico_subset_Icc_self ht
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) i :=
      tensor_lambda_nonneg (I := I) (M := M) i
    calc
      ‖rhs N t i‖ =
          |-(TensorEigenIdx.lambda (I := I) (M := M) i) * V N t i +
            (scalarGalPert (I := I) (M := M) S T t
              (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i| := by
                simp only [Real.norm_eq_abs, rhs]
      _ ≤ |-(TensorEigenIdx.lambda (I := I) (M := M) i) * V N t i| +
            |(scalarGalPert (I := I) (M := M) S T t
              (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i| :=
          abs_add_le _ _
      _ = TensorEigenIdx.lambda (I := I) (M := M) i * |V N t i| +
            |(scalarGalPert (I := I) (M := M) S T t
              (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hlam]
      _ ≤ TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
            Kpert * Real.sqrt B2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hcoord N t ht' i) hlam)
            (hforce N t ht' i)
      _ = (L i : Real) := rfl
  have hlip := supp_right_lip (tau := tau) Fs V rhs L hcont
    (by
      intro N t ht i hi
      simpa only [rhs] using hderiv N t ht i hi)
    hsupp hrhs_bound
  have hC : ∀ _ : TensorEigenIdx (I := I) (M := M) q 0 0,
      0 ≤ Real.sqrt B0 := fun _ => Real.sqrt_nonneg B0
  let Kq := tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0
  letI : Countable (TensorEigenIdx (I := I) (M := M) q 0 0) :=
    DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx
      (I := I) (M := M) (g := q) (r := 0) (s := 0) Kq
  obtain ⟨phi, hphi, ulim, hulim_cont, hconv⟩ :=
    galerkin_subseq (hτ := htau.le) V (fun _ => Real.sqrt B0) hC L
      (fun N t ht i => hcoord N t ht i) hlip
  have hFs : Tendsto Fs atTop atTop := by
    simpa only [Fs] using eigenFinset_tendsto (I := I) (M := M) q 0 0
  have hFs_phi : Tendsto (fun n => Fs (phi n)) atTop atTop :=
    hFs.comp hphi.tendsto_atTop
  have hlim_init := gal_lim_init (tau := tau) Fs phi V ulim
    (fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
      (SmoothCcTensor.toL2 u0) i)
    htau0 hFs_phi hconv hinit
  have hlim_mass := gal_lim_mass (I := I) (M := M) (tau := tau)
    q Fs phi V ulim hFs_phi hconv henergy
  refine ⟨V, phi, ulim, {
    cont := by simpa only [Fs] using hcont
    deriv := by simpa only [Fs, q] using hderiv
    init := by simpa only [Fs, q] using hinit
    support := by simpa only [Fs, q] using hsupp
    pert_cont := hpert_cont
    energy := by simpa only [Fs, q] using henergy
    mono := hphi
    lim_cont := hulim_cont
    conv := hconv
    lim_init := by simpa only [q] using hlim_init
    lim_mass := by simpa only [q] using hlim_mass
  }⟩



noncomputable def galLimHs
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (m : Nat) (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
    tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) where
  coeff := ulim t
  weighted_summable := ((hlim.lim_mass m).choose_spec t ht).1


noncomputable def galLimPath
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (m : Nat) :
    Icc (0 : Real) tau → tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) :=
  fun t => galLimHs hlim m t t.2



theorem galLimPath_cont
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim) (m : Nat) :
    Continuous (galLimPath hlim m) := by
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have hm : (m : Real) < ((m + 1 : Nat) : Real) := by
    exact_mod_cast Nat.lt_succ_self m
  let W : Icc (0 : Real) tau →
      tensorHs (I := I) (M := M) q 0 0 ((m + 1 : Nat) : Real) :=
    galLimPath hlim (m + 1)
  obtain ⟨B, hB⟩ := hlim.lim_mass (m + 1)
  have hW_bound (t : Icc (0 : Real) tau) : ‖W t‖ ≤ Real.sqrt B := by
    have hsq : ‖W t‖ ^ 2 ≤ B := by
      rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
      simpa only [W, galLimPath, galLimHs, q] using (hB t t.2).2
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt
  have hcoeff (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      Continuous (fun t => (W t).coeff i) := by
    simpa only [W, galLimPath, galLimHs, q] using
      (hlim.lim_cont i).comp continuous_subtype_val
  have hcont := cont_of_coeff (I := I) (M := M) hm W
    (Real.sqrt_nonneg B) hW_bound hcoeff
  have heq : (fun t =>
      tensorHsInclusion (I := I) (M := M) (g := q) (r := 0) (s := 0)
        hm.le (W t)) = galLimPath hlim m := by
    funext t
    apply tensorHs.ext
    funext i
    simp only [W, galLimPath, galLimHs, q, tensorHsInclusion_coeff_apply]
  rw [heq] at hcont
  exact hcont



theorem galLim_tendsto
    {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    {T : D.RegularTime} {tau : Real}
    {u0 : SmoothCcTensor (S.family.metric (T : Real)) 0 0}
    {V : Nat → Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    {phi : Nat → Nat}
    {ulim : Real → TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 → Real}
    (hlim : IsConjGalSubseq (I := I) (M := M)
      S T tau u0 V phi ulim)
    (m : Nat) (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
    Tendsto
      (fun n =>
        scalarGalVec (I := I) (M := M)
          (S.family.metric (T : Real))
          (eigenFinset (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0 (phi n))
          (V (phi n) t) (m : Real))
      atTop (𝓝 (galLimHs hlim m t ht)) := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  have hm : (m : Real) < ((m + 1 : Nat) : Real) := by
    exact_mod_cast Nat.lt_succ_self m
  set u : Nat → tensorHs (I := I) (M := M) q 0 0
      ((m + 1 : Nat) : Real) := fun n =>
    scalarGalVec (I := I) (M := M) q
      (eigenFinset (I := I) (M := M) q 0 0 (phi n))
      (V (phi n) t) ((m + 1 : Nat) : Real) with hu_def
  set W : tensorHs (I := I) (M := M) q 0 0
      ((m + 1 : Nat) : Real) := galLimHs hlim (m + 1) t ht with hW_def
  set d : Nat → tensorHs (I := I) (M := M) q 0 0
      ((m + 1 : Nat) : Real) := fun n => u n - W with hd_def
  have hW_coeff (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      W.coeff i = ulim t i := by
    rw [hW_def]
    rfl
  obtain ⟨Bu, hBu⟩ := hlim.energy (m + 1)
  obtain ⟨BW, hBW⟩ := hlim.lim_mass (m + 1)
  have hu_sq (n : Nat) : ‖u n‖ ^ 2 ≤ Bu := by
    rw [hu_def, galVec_norm_sq (I := I) (M := M)]
    simpa only [q, galerkinEnergy] using hBu (phi n) t ht
  have hW_sq : ‖W‖ ^ 2 ≤ BW := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)]
    simpa only [hW_coeff] using (hBW t ht).2
  have hu_norm (n : Nat) : ‖u n‖ ≤ Real.sqrt Bu := by
    calc
      ‖u n‖ = Real.sqrt (‖u n‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt Bu := Real.sqrt_le_sqrt (hu_sq n)
  have hW_norm : ‖W‖ ≤ Real.sqrt BW := by
    calc
      ‖W‖ = Real.sqrt (‖W‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt BW := Real.sqrt_le_sqrt hW_sq
  have hF : Tendsto
      (fun n => eigenFinset (I := I) (M := M) q 0 0 (phi n))
      atTop atTop :=
    (eigenFinset_tendsto (I := I) (M := M) q 0 0).comp
      hlim.mono.tendsto_atTop
  have hmem (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ∀ᶠ n in atTop,
        i ∈ eigenFinset (I := I) (M := M) q 0 0 (phi n) := by
    have hs : ∀ᶠ n in atTop,
        ({i} : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) ⊆
          eigenFinset (I := I) (M := M) q 0 0 (phi n) :=
      hF.eventually_ge_atTop {i}
    filter_upwards [hs] with n hn
    exact hn (Finset.mem_singleton_self i)
  have hu_coeff (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      Tendsto (fun n => (u n).coeff i) atTop (𝓝 (ulim t i)) := by
    refine ((hlim.conv i).tendsto_at ht).congr' ?_
    filter_upwards [hmem i] with n hn
    rw [hu_def, scalarGalVec_coeff, if_pos hn]
  have hsub_coeff
      (a b : tensorHs (I := I) (M := M) q 0 0 ((m + 1 : Nat) : Real))
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      (a - b).coeff i = a.coeff i - b.coeff i := by
    simp only [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
  have hd_coeff (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      Tendsto (fun n => (d n).coeff i) atTop (𝓝 0) := by
    have hc := (hu_coeff i).sub_const (W.coeff i)
    rw [hW_coeff i, sub_self] at hc
    refine hc.congr (fun n => ?_)
    rw [hd_def, hsub_coeff (u n) W i, hW_coeff i]
  let C : Real := Real.sqrt Bu + Real.sqrt BW
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hd_bound (n : Nat) : ‖d n‖ ≤ C := by
    calc
      ‖d n‖ = ‖u n - W‖ := by rw [hd_def]
      _ ≤ ‖u n‖ + ‖W‖ := norm_sub_le _ _
      _ ≤ Real.sqrt Bu + Real.sqrt BW := add_le_add (hu_norm n) hW_norm
      _ = C := rfl
  have hdown := tendsto_of_coeff
    (I := I) (M := M) (g := q) (r := 0) (s := 0)
    (σ' := (m : Real)) (σ'' := ((m + 1 : Nat) : Real))
    hm d hC hd_bound hd_coeff
  have hinc_u (n : Nat) :
      tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0) hm.le (u n) =
        scalarGalVec (I := I) (M := M) q
          (eigenFinset (I := I) (M := M) q 0 0 (phi n))
          (V (phi n) t) (m : Real) := by
    simpa only [hu_def] using
      scalarGalVec_inc (I := I) (M := M) q
        (eigenFinset (I := I) (M := M) q 0 0 (phi n))
        (V (phi n) t) hm.le
  have hinc_W :
      tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0) hm.le W =
        galLimHs hlim m t ht := by
    apply tensorHs.ext
    funext i
    rw [tensorHsInclusion_coeff_apply, hW_coeff i]
    rfl
  have hinc_d (n : Nat) :
      tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0) hm.le (d n) =
        scalarGalVec (I := I) (M := M) q
            (eigenFinset (I := I) (M := M) q 0 0 (phi n))
            (V (phi n) t) (m : Real) -
          galLimHs hlim m t ht := by
    rw [hd_def, map_sub, hinc_u n, hinc_W]
  have hnorm : Tendsto
      (fun n =>
        ‖scalarGalVec (I := I) (M := M) q
            (eigenFinset (I := I) (M := M) q 0 0 (phi n))
            (V (phi n) t) (m : Real) - galLimHs hlim m t ht‖)
      atTop (𝓝 0) := by
    refine hdown.congr (fun n => ?_)
    rw [hinc_d n]
  have hsub := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  exact tendsto_sub_nhds_zero_iff.mp hsub

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
