import DifferentialGeometry.Analysis.ODE.ChartLocalPicardIntegral
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.RankZeroRealization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautCompat
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautTime
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarPotentialTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkinLimit
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Integral.DominatedConvergence











noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators Interval

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.ODE
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


noncomputable def galLimExt
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim) (m : Nat) :
    Real → tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) :=
  Set.IccExtend hτ (galLimPath hlim m)


@[simp] theorem galLimExt_mem
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim) (m : Nat)
    {t : Real} (ht : t ∈ Icc (0 : Real) tau) :
    galLimExt hτ hlim m t = galLimHs hlim m t ht := by
  rw [galLimExt, Set.IccExtend_of_mem hτ _ ht]
  rfl



theorem galLimExt_inc
    {D : RealTimeInterval}
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
    {n m : Nat} (hnm : n ≤ m) {t : Real}
    (ht : t ∈ Icc (0 : Real) tau) :
    tensorHsInclusion (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0)
        (by exact_mod_cast hnm : (n : Real) ≤ (m : Real))
        (galLimExt hτ hlim m t) =
      galLimExt hτ hlim n t := by
  rw [galLimExt_mem hτ hlim m ht, galLimExt_mem hτ hlim n ht]
  apply tensorHs.ext
  funext i
  simp only [tensorHsInclusion_coeff_apply, galLimHs]


theorem galLimExt_cont
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim) (m : Nat) :
    Continuous (galLimExt hτ hlim m) := by
  exact Continuous.Icc_extend' (galLimPath_cont hlim m)


noncomputable def galLimVel
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim) (t : Real) :
    tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 0 :=
  scalarScaleLap (I := I) (M := M) (S.family.metric (T : Real))
      (galLimExt hτ hlim 2 t) +
    scalarGalPert (I := I) (M := M) S T t (galLimExt hτ hlim 2 t)



noncomputable def galLimVelHs
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim) (m : Nat) (t : Real) :
    tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) :=
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let U : tensorHs (I := I) (M := M) q 0 0 ((m : Real) + 2) :=
    tensorHs.castEquiv (I := I) (M := M)
      (g := q) (r := 0) (s := 0)
      (by norm_num : ((m + 2 : Nat) : Real) = (m : Real) + 2)
      (galLimExt hτ hlim (m + 2) t)
  let Um : tensorHs (I := I) (M := M) q 0 0 (m : Real) :=
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (by norm_num) U
  tensorScaleLaplacian (I := I) (M := M)
      (g := q) (r := 0) (s := 0) (m : Real) U +
    lapDiffHs (I := I) (M := M) q
      (S.family.metric ((T : Real) - t)) m U +
    scalarPotHs (I := I) (M := M) q
      (conjCoeff (I := I) (M := M) S ((T : Real) - t)) m Um



noncomputable def galLimVelCan
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim) (m : Nat) (t : Real) :
    tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) :=
  tensorHsInclusion (I := I) (M := M)
    (g := S.family.metric (T : Real)) (r := 0) (s := 0)
    (by exact_mod_cast Nat.le_succ m :
      (m : Real) ≤ ((m + 1 : Nat) : Real))
    (galLimVelHs hτ hlim (m + 1) t)



theorem galLimVel_cont
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim) :
    ContinuousOn (galLimVel hτ hlim) (Icc (0 : Real) tau) := by
  have hU : ContinuousOn (galLimExt hτ hlim 2) (Icc (0 : Real) tau) :=
    (galLimExt_cont hτ hlim 2).continuousOn
  exact
    ((scalarScaleLap (I := I) (M := M)
        (S.family.metric (T : Real))).continuous.comp_continuousOn hU).add
      (hlim.pert_cont.clm_apply hU)



theorem galLimVel_lift
    {D : RealTimeInterval}
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
      ∀ m : Nat, ∃ w : Icc (0 : Real) tau' →
          tensorHs (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0 (m : Real),
        Continuous w ∧
          (∀ t, tensorHsInclusion (I := I) (M := M)
              (g := S.family.metric (T : Real)) (r := 0) (s := 0)
              (by positivity : (0 : Real) ≤ (m : Real)) (w t) =
            galLimVel hτ.le hlim (t : Real)) ∧
          ∀ t, w t = galLimVelCan hτ.le hlim m (t : Real) := by
  classical
  obtain ⟨tauN, htauN, _, hregN, hnorm⟩ :=
    lapDiffHs_norm (I := I) (M := M) S.family hS.smoothMetric T
  obtain ⟨tauI, htauI, _, _, hinc⟩ :=
    lapDiffHs_inc (I := I) (M := M) S.family hS.smoothMetric T
  obtain ⟨tauE, htauE, hEq⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (lapDiffHs_eq_A20 (I := I) (M := M)
        S.family hS.smoothMetric T)
  let tau' : Real := min tau (min tauN (min tauI tauE))
  have htau' : 0 < tau' := by
    dsimp only [tau']
    exact lt_min hτ (lt_min htauN (lt_min htauI htauE))
  have htau'_tau : tau' ≤ tau := by
    dsimp only [tau']
    exact min_le_left _ _
  have htau'_N : tau' ≤ tauN := by
    dsimp only [tau']
    exact (min_le_right _ _).trans (min_le_left _ _)
  have htau'_I : tau' ≤ tauI := by
    dsimp only [tau']
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have htau'_E : tau' ≤ tauE := by
    dsimp only [tau']
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hsubTau : Icc (0 : Real) tau' ⊆ Icc (0 : Real) tau :=
    Icc_subset_Icc le_rfl htau'_tau
  have hsubN : Icc (0 : Real) tau' ⊆ Icc (0 : Real) tauN :=
    Icc_subset_Icc le_rfl htau'_N
  have hsubI : Icc (0 : Real) tau' ⊆ Icc (0 : Real) tauI :=
    Icc_subset_Icc le_rfl htau'_I
  have hsubE : Icc (0 : Real) tau' ⊆ Icc (0 : Real) tauE :=
    Icc_subset_Icc le_rfl htau'_E
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let K : Set Real := Icc (0 : Real) tau'
  let R : Set Real := {s : Real | (T : Real) - s ∈ D.regular}
  let zeta : Real → C^∞⟮I, M; Real⟯ := fun s =>
    conjCoeff (I := I) (M := M) S ((T : Real) - s)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc
  have hKR : K ⊆ R := by
    intro s hs
    simpa only [K, R] using hregN s (hsubN hs)
  have hzeta : ContMDiffOn (I.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ R) := by
    simpa only [zeta, R, conjCoeffRev] using
      conjCoeff_rev (I := I) S hS T
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro m
  obtain ⟨B, hB⟩ := hlim.lim_mass (m + 1 + 2)
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := hnorm (m + 1)
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    scalarPotHs_unif (I := I) (M := M) q zeta
      (K := K) (S := R) hK hKR hzeta (m + 1)
  have hfac : 0 ≤ 1 + C₂ + C₁ := by positivity
  let C : Real := (1 + C₂ + C₁) * Real.sqrt B
  have hC_nn : 0 ≤ C := by
    exact mul_nonneg hfac (Real.sqrt_nonneg B)
  let W : Icc (0 : Real) tau' →
      tensorHs (I := I) (M := M) q 0 0 ((m + 1 : Nat) : Real) :=
    fun t => galLimVelHs hτ.le hlim (m + 1) t
  have hW_bound (t : Icc (0 : Real) tau') : ‖W t‖ ≤ C := by
    have htTau : (t : Real) ∈ Icc (0 : Real) tau := hsubTau t.2
    have htN : (t : Real) ∈ Icc (0 : Real) tauN := hsubN t.2
    let U : tensorHs (I := I) (M := M) q 0 0
        (((m + 1 : Nat) : Real) + 2) :=
      tensorHs.castEquiv (I := I) (M := M)
        (g := q) (r := 0) (s := 0)
        (by norm_num : ((m + 1 + 2 : Nat) : Real) =
          ((m + 1 : Nat) : Real) + 2)
        (galLimExt hτ.le hlim (m + 1 + 2) t)
    have hincU : ((m + 1 : Nat) : Real) ≤
        ((m + 1 : Nat) : Real) + 2 := by norm_num
    let Um : tensorHs (I := I) (M := M) q 0 0
        ((m + 1 : Nat) : Real) :=
      tensorHsInclusion (I := I) (M := M)
        (g := q) (r := 0) (s := 0) hincU U
    have hExtSq : ‖galLimExt hτ.le hlim (m + 1 + 2) t‖ ^ 2 ≤ B := by
      rw [galLimExt_mem hτ.le hlim (m + 1 + 2) htTau,
        tensorHs.norm_sq_eq_tsum]
      simpa only [galLimHs] using (hB t htTau).2
    have hUnorm : ‖U‖ = ‖galLimExt hτ.le hlim (m + 1 + 2) t‖ := by
      dsimp only [U]
      exact (tensorHs.castEquiv (I := I) (M := M)
        (g := q) (r := 0) (s := 0)
        (by norm_num : ((m + 1 + 2 : Nat) : Real) =
          ((m + 1 : Nat) : Real) + 2)).norm_map _
    have hUSq : ‖U‖ ^ 2 ≤ B := by
      rw [hUnorm]
      exact hExtSq
    have hU : ‖U‖ ≤ Real.sqrt B := by
      have hsqrt := Real.sqrt_le_sqrt hUSq
      rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt
    have hUm : ‖Um‖ ≤ ‖U‖ := by
      dsimp only [Um]
      exact tensorHsInclusion_norm_le (I := I) (M := M) hincU U
    have hLap :
        ‖tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U‖ ≤ ‖U‖ := by
      simpa only [tensorScaleLaplacian_apply] using
        norm_scaleLaplacianFun_le (I := I) (M := M) U
    have hDiff :
        ‖lapDiffHs (I := I) (M := M) q
          (S.family.metric ((T : Real) - t)) (m + 1) U‖ ≤ C₂ * ‖U‖ := by
      calc
        _ ≤ ‖lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1)‖ * ‖U‖ :=
          (lapDiffHs (I := I) (M := M) q
            (S.family.metric ((T : Real) - t)) (m + 1)).le_opNorm U
        _ ≤ C₂ * ‖U‖ :=
          mul_le_mul_of_nonneg_right (hC₂ t htN) (norm_nonneg U)
    have hPot :
        ‖scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ ≤
          C₁ * ‖Um‖ := by
      calc
        _ ≤ ‖scalarPotHs (I := I) (M := M) q
              (zeta t) (m + 1)‖ * ‖Um‖ :=
          (scalarPotHs (I := I) (M := M) q
            (zeta t) (m + 1)).le_opNorm Um
        _ ≤ C₁ * ‖Um‖ :=
          mul_le_mul_of_nonneg_right
            (hC₁ t (by simpa only [K] using t.2)) (norm_nonneg Um)
    change ‖
      tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U +
        lapDiffHs (I := I) (M := M) q
          (S.family.metric ((T : Real) - t)) (m + 1) U +
        scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ ≤ C
    calc
      _ ≤ ‖tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U +
            lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U‖ +
          ‖scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ :=
        norm_add_le _ _
      _ ≤ (‖tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U‖ +
            ‖lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U‖) +
          ‖scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (‖U‖ + C₂ * ‖U‖) + C₁ * ‖Um‖ :=
        add_le_add (add_le_add hLap hDiff) hPot
      _ ≤ (‖U‖ + C₂ * ‖U‖) + C₁ * ‖U‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hUm hC₁_nn)
      _ = (1 + C₂ + C₁) * ‖U‖ := by ring
      _ ≤ (1 + C₂ + C₁) * Real.sqrt B :=
        mul_le_mul_of_nonneg_left hU hfac
      _ = C := rfl
  have hW0 (t : Icc (0 : Real) tau') :
      tensorHsInclusion (I := I) (M := M)
          (g := q) (r := 0) (s := 0)
          (by positivity : (0 : Real) ≤ ((m + 1 : Nat) : Real)) (W t) =
        galLimVel hτ.le hlim (t : Real) := by
    have htTau : (t : Real) ∈ Icc (0 : Real) tau := hsubTau t.2
    have hk : (1 : Real) ≤ ((m + 1 : Nat) : Real) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have h0k : (0 : Real) ≤ ((m + 1 : Nat) : Real) :=
      zero_le_one.trans hk
    have hk2 : ((m + 1 : Nat) : Real) ≤
        ((m + 1 : Nat) : Real) + 2 := by norm_num
    have h2k2 : (2 : Real) ≤ ((m + 1 : Nat) : Real) + 2 := by
      linarith
    have h12 : (1 : Real) ≤ 2 := by norm_num
    have h02k : ((0 : Nat) : Real) + 2 ≤
        ((m + 1 : Nat) : Real) + 2 := by
      simpa only [Nat.cast_zero, zero_add] using h2k2
    have h20 : (2 : Real) = ((0 : Nat) : Real) + 2 := by norm_num
    have hzero : ((0 : Nat) : Real) = 0 := by norm_num
    let U₂ : tensorHs (I := I) (M := M) q 0 0 2 :=
      galLimExt hτ.le hlim 2 t
    let U : tensorHs (I := I) (M := M) q 0 0
        (((m + 1 : Nat) : Real) + 2) :=
      tensorHs.castEquiv (I := I) (M := M)
        (g := q) (r := 0) (s := 0)
        (by norm_num : ((m + 1 + 2 : Nat) : Real) =
          ((m + 1 : Nat) : Real) + 2)
        (galLimExt hτ.le hlim (m + 1 + 2) t)
    let Um : tensorHs (I := I) (M := M) q 0 0
        ((m + 1 : Nat) : Real) :=
      tensorHsInclusion (I := I) (M := M)
        (g := q) (r := 0) (s := 0) hk2 U
    have hU2 :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h2k2 U = U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i)
        (galLimExt_inc hτ.le hlim
          (show 2 ≤ m + 1 + 2 by omega) htTau)
      simpa only [U, U₂, tensorHsInclusion_coeff_apply,
        tensorHs.castEquiv_coeff] using hi
    have hUm1 :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hk Um =
          tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h12 U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i) hU2
      simpa only [Um, tensorHsInclusion_coeff_apply] using hi
    have hLap :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (tensorScaleLaplacian (I := I) (M := M)
              (g := q) (r := 0) (s := 0)
              ((m + 1 : Nat) : Real) U) =
          scalarScaleLap (I := I) (M := M) q U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i) hU2
      simp only [tensorHsInclusion_coeff_apply] at hi
      simp only [tensorHsInclusion_coeff_apply,
        tensorScaleLaplacian_coeff, scalarScaleLap_coeff]
      rw [hi]
    have hU0 :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h02k U =
          tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h20 U₂ := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0 (2 : Real) =>
          v.coeff i) hU2
      simpa only [tensorHsInclusion_coeff_apply,
        tensorHs.castEquiv_coeff] using hi
    have hinc0 := hinc (n := 0) (m := m + 1) (Nat.zero_le _)
      (t : Real) (hsubI t.2)
    have happ := congrArg (fun L => L U) hinc0
    simp only [ContinuousLinearMap.comp_apply] at happ
    have hleft :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U) =
          tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hzero
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) 0
              (tensorHsInclusion (I := I) (M := M)
                (g := q) (r := 0) (s := 0) h02k U)) := by
      apply tensorHs.ext
      funext i
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M) q 0 0
          ((0 : Nat) : Real) => v.coeff i) happ
      simpa only [tensorHsInclusion_coeff_apply,
        tensorHs.castEquiv_coeff] using hi
    have hDiff :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) (m + 1) U) =
          lapDiffA20 (I := I) (M := M) S.family T t U₂ := by
      calc
        _ = tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hzero
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) 0
              (tensorHsInclusion (I := I) (M := M)
                (g := q) (r := 0) (s := 0) h02k U)) := hleft
        _ = tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0) hzero
            (lapDiffHs (I := I) (M := M) q
              (S.family.metric ((T : Real) - t)) 0
              (tensorHs.castEquiv (I := I) (M := M)
                (g := q) (r := 0) (s := 0) h20 U₂)) := by rw [hU0]
        _ = lapDiffA20 (I := I) (M := M) S.family T t U₂ :=
          hEq (hsubE t.2) U₂
    have hPot :
        tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0) h0k
            (scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um) =
          scalarPotH0 (I := I) (M := M) q (zeta t)
            (tensorHsInclusion (I := I) (M := M)
              (g := q) (r := 0) (s := 0) h12 U₂) := by
      calc
        _ = scalarPotH0 (I := I) (M := M) q (zeta t)
            (tensorHsInclusion (I := I) (M := M)
              (g := q) (r := 0) (s := 0) hk Um) :=
          scalarPotHs_inc (I := I) (M := M) q (zeta t)
            (m + 1) hk Um
        _ = _ := by rw [hUm1]
    change tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) h0k
      (tensorScaleLaplacian (I := I) (M := M)
          (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) U +
        lapDiffHs (I := I) (M := M) q
          (S.family.metric ((T : Real) - t)) (m + 1) U +
        scalarPotHs (I := I) (M := M) q (zeta t) (m + 1) Um) =
      galLimVel hτ.le hlim t
    rw [map_add, map_add, hLap, hDiff, hPot]
    simp only [galLimVel, scalarGalPert, conjA1, zeta, q,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
    rw [add_assoc]
  have hm : (m : Real) < ((m + 1 : Nat) : Real) := by
    exact_mod_cast Nat.lt_succ_self m
  have hvelCoeffOn
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ContinuousOn
        (fun s : Real => (galLimVel hτ.le hlim s).coeff i)
        (Icc (0 : Real) tau') := by
    exact (coeffCLM (I := I) (M := M) (g := q) (r := 0) (s := 0)
      (σ := 0) i).continuous.comp_continuousOn
        ((galLimVel_cont hτ.le hlim).mono hsubTau)
  have hvelCoeff
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      Continuous (fun t : Icc (0 : Real) tau' =>
        (galLimVel hτ.le hlim (t : Real)).coeff i) :=
    (hvelCoeffOn i).restrict
  have hcoeff
      (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
      Continuous (fun t : Icc (0 : Real) tau' => (W t).coeff i) := by
    refine (hvelCoeff i).congr ?_
    intro t
    have hi := congrArg
      (fun v : tensorHs (I := I) (M := M) q 0 0 0 => v.coeff i)
      (hW0 t)
    simpa only [tensorHsInclusion_coeff_apply] using hi.symm
  have hdown := cont_of_coeff (I := I) (M := M) hm W hC_nn hW_bound hcoeff
  let w : Icc (0 : Real) tau' →
      tensorHs (I := I) (M := M) q 0 0 (m : Real) := fun t =>
    tensorHsInclusion (I := I) (M := M)
      (g := q) (r := 0) (s := 0) hm.le (W t)
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [w] using hdown
  · intro t
    apply tensorHs.ext
    funext i
    have hi := congrArg
      (fun v : tensorHs (I := I) (M := M) q 0 0 0 => v.coeff i)
      (hW0 t)
    simpa only [w, tensorHsInclusion_coeff_apply] using hi
  · intro t
    simp only [w, W, galLimVelCan, q]


theorem galLimVel_coeff
    {D : RealTimeInterval}
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
    (t : Real) (ht : t ∈ Icc (0 : Real) tau)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    (galLimVel hτ hlim t).coeff i =
      -TensorEigenIdx.lambda (I := I) (M := M) i * ulim t i +
        (scalarGalPert (I := I) (M := M) S T t
          (galLimHs hlim 2 t ht)).coeff i := by
  simp only [galLimVel, tensorHs.add_coeff, scalarScaleLap_coeff,
    galLimExt_mem hτ hlim 2 ht, galLimHs]

set_option maxHeartbeats 800000 in


theorem galLim_mode_ftc
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim)
    (t : Real) (ht : t ∈ Icc (0 : Real) tau)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    ulim t i =
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0)
          (SmoothCcTensor.toL2 u0) i +
        ∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i := by
  classical
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let Fs : Nat → Finset (TensorEigenIdx (I := I) (M := M) q 0 0) :=
    fun N => eigenFinset (I := I) (M := M) q 0 0 N
  let U : Nat → Real → tensorHs (I := I) (M := M) q 0 0 2 :=
    fun N r => scalarGalVec (I := I) (M := M) q (Fs N) (V N r) 2
  let R : Nat → Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real :=
    fun N r j =>
      -TensorEigenIdx.lambda (I := I) (M := M) j * V N r j +
        (scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j
  obtain ⟨B0, hB0⟩ := hlim.energy 0
  obtain ⟨B2, hB2⟩ := hlim.energy 2
  have h0mem : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, hτ.le⟩
  have hB0_nonneg : 0 ≤ B0 :=
    (galerkinEnergy_nonneg (I := I) (M := M) (Fs 0) (V 0) 0 0).trans
      (by simpa only [Fs, q, Nat.cast_zero] using hB0 0 0 h0mem)
  have hcoord_sq (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      (V N r j) ^ 2 ≤ B0 := by
    by_cases hj : j ∈ Fs N
    · have hterm :
          tensorSobolevWeight (I := I) (M := M) j 0 * (V N r j) ^ 2 ≤
            galerkinEnergy (I := I) (M := M) (Fs N) (V N) 0 r := by
        rw [galerkinEnergy]
        exact Finset.single_le_sum (fun k _ =>
          mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) k 0)
            (sq_nonneg _)) hj
      calc
        (V N r j) ^ 2 =
            tensorSobolevWeight (I := I) (M := M) j 0 * (V N r j) ^ 2 := by
              rw [tensorSobolevWeight_zero, one_mul]
        _ ≤ galerkinEnergy (I := I) (M := M) (Fs N) (V N) 0 r := hterm
        _ ≤ B0 := by simpa only [Fs, q, Nat.cast_zero] using hB0 N r hr
    · rw [hlim.support N r j (by simpa only [Fs, q] using hj)]
      simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hB0_nonneg
  have hcoord (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      |V N r j| ≤ Real.sqrt B0 := by
    calc
      |V N r j| = Real.sqrt ((V N r j) ^ 2) :=
        (Real.sqrt_sq_eq_abs (V N r j)).symm
      _ ≤ Real.sqrt B0 := Real.sqrt_le_sqrt (hcoord_sq N r hr j)
  have hvec_norm (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau) :
      ‖U N r‖ ≤ Real.sqrt B2 := by
    have hsq : ‖U N r‖ ^ 2 ≤ B2 := by
      rw [show ‖U N r‖ ^ 2 =
          ∑ j ∈ Fs N,
            tensorSobolevWeight (I := I) (M := M) j 2 * (V N r j) ^ 2 by
        exact galVec_norm_sq (I := I) (M := M) q (Fs N) (V N r) 2]
      simpa only [Fs, U, q, galerkinEnergy] using hB2 N r hr
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt
  obtain ⟨Kpert, hKpert⟩ := banach_steinhaus
    (g := fun r : Icc (0 : Real) tau =>
      scalarGalPert (I := I) (M := M) S T r.1) (fun w => by
      have hwcont : ContinuousOn
          (fun r => scalarGalPert (I := I) (M := M) S T r w)
          (Icc (0 : Real) tau) :=
        hlim.pert_cont.clm_apply continuousOn_const
      obtain ⟨rmax, _hrmax, hmax⟩ :=
        isCompact_Icc.exists_isMaxOn (s := Icc (0 : Real) tau) ⟨0, h0mem⟩
          hwcont.norm
      exact ⟨‖scalarGalPert (I := I) (M := M) S T rmax w‖,
        fun r => hmax r.2⟩)
  have hKpert_nonneg : 0 ≤ Kpert :=
    (norm_nonneg (scalarGalPert (I := I) (M := M) S T (0 : Real))).trans
      (hKpert ⟨0, h0mem⟩)
  have hpert_norm (r : Real) (hr : r ∈ Icc (0 : Real) tau) :
      ‖scalarGalPert (I := I) (M := M) S T r‖ ≤ Kpert := by
    exact hKpert ⟨r, hr⟩
  have hforce (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| ≤
        Kpert * Real.sqrt B2 := by
    have hcoeff := abs_coeff_le_norm (I := I) (M := M) j
      (scalarGalPert (I := I) (M := M) S T r (U N r))
    have hcoeff' :
        |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| ≤
          ‖scalarGalPert (I := I) (M := M) S T r (U N r)‖ := by
      simpa only [tensorSobolevWeight_zero, Real.sqrt_one, inv_one, one_mul]
        using hcoeff
    calc
      |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j|
          ≤ ‖scalarGalPert (I := I) (M := M) S T r (U N r)‖ := hcoeff'
      _ ≤ ‖scalarGalPert (I := I) (M := M) S T r‖ * ‖U N r‖ :=
        (scalarGalPert (I := I) (M := M) S T r).le_opNorm (U N r)
      _ ≤ Kpert * Real.sqrt B2 :=
        mul_le_mul (hpert_norm r hr) (hvec_norm N r hr)
          (norm_nonneg _) hKpert_nonneg
  have hRcont (N : Nat)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ContinuousOn (fun r => R N r j) (Icc (0 : Real) tau) := by
    have hVcont : ContinuousOn (fun r => V N r j) (Icc (0 : Real) tau) := by
      by_cases hj : j ∈ Fs N
      · exact hlim.cont N j (by simpa only [Fs, q] using hj)
      · have hz : (fun r : Real => V N r j) = fun _ => 0 := by
          funext r
          exact hlim.support N r j (by simpa only [Fs, q] using hj)
        rw [hz]
        exact continuousOn_const
    have hUcont : ContinuousOn (U N) (Icc (0 : Real) tau) := by
      simpa only [U, Fs, q] using
        (scalarGalVec_cont (I := I) (M := M) q (Fs N) (V N)
          (fun k hk => hlim.cont N k (by simpa only [Fs, q] using hk)))
    have hPcont : ContinuousOn
        (fun r => scalarGalPert (I := I) (M := M) S T r (U N r))
        (Icc (0 : Real) tau) := hlim.pert_cont.clm_apply hUcont
    have hPc : ContinuousOn
        (fun r => (scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j)
        (Icc (0 : Real) tau) :=
      (coeffCLM (I := I) (M := M) (g := q) (r := 0) (s := 0)
        (σ := (0 : Real)) j).continuous.comp_continuousOn hPcont
    have hdiag : ContinuousOn
        (fun r => -TensorEigenIdx.lambda (I := I) (M := M) j * V N r j)
        (Icc (0 : Real) tau) := continuousOn_const.mul hVcont
    simpa only [R] using hdiag.add hPc
  have hRbound (N : Nat) (r : Real) (hr : r ∈ Icc (0 : Real) tau)
      (j : TensorEigenIdx (I := I) (M := M) q 0 0) :
      ‖R N r j‖ ≤
        TensorEigenIdx.lambda (I := I) (M := M) j * Real.sqrt B0 +
          Kpert * Real.sqrt B2 := by
    have hlam : 0 ≤ TensorEigenIdx.lambda (I := I) (M := M) j :=
      tensor_lambda_nonneg (I := I) (M := M) j
    calc
      ‖R N r j‖ =
          |-TensorEigenIdx.lambda (I := I) (M := M) j * V N r j +
            (scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| := by
              simp only [Real.norm_eq_abs, R]
      _ ≤ |-TensorEigenIdx.lambda (I := I) (M := M) j * V N r j| +
            |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| :=
          abs_add_le _ _
      _ = TensorEigenIdx.lambda (I := I) (M := M) j * |V N r j| +
            |(scalarGalPert (I := I) (M := M) S T r (U N r)).coeff j| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hlam]
      _ ≤ TensorEigenIdx.lambda (I := I) (M := M) j * Real.sqrt B0 +
            Kpert * Real.sqrt B2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hcoord N r hr j) hlam)
            (hforce N r hr j)
  have hsub : Ι (0 : Real) t ⊆ Icc (0 : Real) tau := by
    intro r hr
    rw [uIoc_of_le ht.1] at hr
    exact ⟨hr.1.le, hr.2.trans ht.2⟩
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun r => R (phi n) r i)
        (volume.restrict (Ι (0 : Real) t)) := by
    filter_upwards with n
    exact ((hRcont (phi n) i).mono hsub).aestronglyMeasurable measurableSet_uIoc
  have hbound : ∀ᶠ n in atTop, ∀ᵐ r ∂volume, r ∈ Ι (0 : Real) t →
      ‖R (phi n) r i‖ ≤
        TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
          Kpert * Real.sqrt B2 := by
    filter_upwards with n
    filter_upwards with r
    intro hr
    exact hRbound (phi n) r (hsub hr) i
  have hbound_int : IntervalIntegrable
      (fun _ : Real =>
        TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
          Kpert * Real.sqrt B2) volume 0 t :=
    continuousOn_const.intervalIntegrable
  have hpoint : ∀ᵐ r ∂volume, r ∈ Ι (0 : Real) t →
      Tendsto (fun n => R (phi n) r i) atTop
        (𝓝 ((galLimVel hτ.le hlim r).coeff i)) := by
    filter_upwards with r
    intro hr
    have hrIcc : r ∈ Icc (0 : Real) tau := hsub hr
    have hVlim : Tendsto (fun n => V (phi n) r i) atTop (𝓝 (ulim r i)) :=
      (hlim.conv i).tendsto_at hrIcc
    have hUlim : Tendsto (fun n => U (phi n) r) atTop
        (𝓝 (galLimHs hlim 2 r hrIcc)) := by
      simpa only [U, Fs, q] using galLim_tendsto hlim 2 r hrIcc
    have hPlim : Tendsto
        (fun n => scalarGalPert (I := I) (M := M) S T r (U (phi n) r)) atTop
        (𝓝 (scalarGalPert (I := I) (M := M) S T r
          (galLimHs hlim 2 r hrIcc))) :=
      ((scalarGalPert (I := I) (M := M) S T r).continuous.tendsto _).comp hUlim
    have hPclim : Tendsto
        (fun n => (scalarGalPert (I := I) (M := M) S T r
          (U (phi n) r)).coeff i) atTop
        (𝓝 ((scalarGalPert (I := I) (M := M) S T r
          (galLimHs hlim 2 r hrIcc)).coeff i)) :=
      ((coeffCLM (I := I) (M := M) (g := q) (r := 0) (s := 0)
        (σ := (0 : Real)) i).continuous.tendsto _).comp hPlim
    have hdiag : Tendsto
        (fun n => -TensorEigenIdx.lambda (I := I) (M := M) i * V (phi n) r i)
        atTop (𝓝 (-TensorEigenIdx.lambda (I := I) (M := M) i * ulim r i)) :=
      tendsto_const_nhds.mul hVlim
    have hsum := hdiag.add hPclim
    simpa only [R, galLimVel_coeff hτ.le hlim r hrIcc] using hsum
  have hInt : Tendsto (fun n => ∫ r in (0 : Real)..t, R (phi n) r i) atTop
      (𝓝 (∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ : Real =>
        TensorEigenIdx.lambda (I := I) (M := M) i * Real.sqrt B0 +
          Kpert * Real.sqrt B2)
      hmeas hbound hbound_int hpoint
  have hFs : Tendsto (fun n => Fs (phi n)) atTop atTop := by
    have hbase : Tendsto Fs atTop atTop := by
      simpa only [Fs] using eigenFinset_tendsto (I := I) (M := M) q 0 0
    exact hbase.comp hlim.mono.tendsto_atTop
  have hi : ∀ᶠ n in atTop, i ∈ Fs (phi n) := by
    have hsingle : ∀ᶠ n in atTop,
        ({i} : Finset (TensorEigenIdx (I := I) (M := M) q 0 0)) ⊆ Fs (phi n) :=
      hFs.eventually_ge_atTop {i}
    filter_upwards [hsingle] with n hn
    exact hn (Finset.mem_singleton_self i)
  have hfinite : ∀ᶠ n in atTop,
      V (phi n) t i =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
            (SmoothCcTensor.toL2 u0) i +
          ∫ r in (0 : Real)..t, R (phi n) r i := by
    filter_upwards [hi] with n hin
    have hftc := ode_right_ftc
      (hlim.cont (phi n) i (by simpa only [Fs, q] using hin))
      (fun r hr => by
        simpa only [R, U, Fs, q] using
          hlim.deriv (phi n) r hr i (by simpa only [Fs, q] using hin))
      (hRcont (phi n) i) t ht
    rw [hlim.init (phi n) i (by simpa only [Fs, q] using hin)] at hftc
    simpa only [q] using hftc
  have hleft : Tendsto (fun n => V (phi n) t i) atTop (𝓝 (ulim t i)) :=
    (hlim.conv i).tendsto_at ht
  have hright : Tendsto
      (fun n =>
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
            (SmoothCcTensor.toL2 u0) i +
          ∫ r in (0 : Real)..t, R (phi n) r i) atTop
      (𝓝 (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
          (SmoothCcTensor.toL2 u0) i +
        ∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i)) :=
    tendsto_const_nhds.add hInt
  have hright' : Tendsto (fun n => V (phi n) t i) atTop
      (𝓝 (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
          (SmoothCcTensor.toL2 u0) i +
        ∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i)) :=
    hright.congr' (by
      filter_upwards [hfinite] with n hn
      exact hn.symm)
  simpa only [q] using tendsto_nhds_unique hleft hright'



theorem galLim_mode_deriv
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim)
    {t : Real} (ht : t ∈ Ioo (0 : Real) tau)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    HasDerivAt (fun r : Real => ulim r i)
      ((galLimVel hτ.le hlim t).coeff i) t := by
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let c : Real := tensorL2Coeff (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
    (SmoothCcTensor.toL2 u0) i
  let f : Real → Real := fun r => (galLimVel hτ.le hlim r).coeff i
  have hfIcc : ContinuousOn f (Icc (0 : Real) tau) := by
    exact (coeffCLM (I := I) (M := M) (g := q) (r := 0) (s := 0)
      (σ := (0 : Real)) i).continuous.comp_continuousOn
        (galLimVel_cont hτ.le hlim)
  have hfIoo : ContinuousOn f (Ioo (0 : Real) tau) :=
    hfIcc.mono Ioo_subset_Icc_self
  have hfAt : ContinuousAt f t :=
    hfIoo.continuousAt (isOpen_Ioo.mem_nhds ht)
  have hsub : Icc (0 : Real) t ⊆ Icc (0 : Real) tau :=
    Icc_subset_Icc le_rfl ht.2.le
  have hfInt : IntervalIntegrable f volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1.le (hfIcc.mono hsub)
  have hfMeas : StronglyMeasurableAtFilter f (nhds t) volume :=
    hfIoo.stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hprim : HasDerivAt (fun r : Real => ∫ s in (0 : Real)..r, f s) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right hfInt hfMeas hfAt
  have hsum : HasDerivAt
      (fun r : Real => c + ∫ s in (0 : Real)..r, f s) (f t) t :=
    hprim.const_add c
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  simpa only [c, f, q] using galLim_mode_ftc hτ hlim r hr i


theorem galLim_mode_c1
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim)
    (i : TensorEigenIdx (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0) :
    ContDiffOn Real 1 (fun t : Real ↦ ulim t i) (Ioo (0 : Real) tau) := by
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (galLim_mode_deriv hτ hlim ht i).differentiableAt.differentiableWithinAt
  · simp only [WithTop.zero_ne_top, false_implies]
  · rw [contDiffOn_zero]
    have hvel : ContinuousOn
        (fun t : Real ↦ (galLimVel hτ.le hlim t).coeff i)
        (Ioo (0 : Real) tau) := by
      exact ((coeffCLM (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0)
        (σ := (0 : Real)) i).continuous.comp_continuousOn
          (galLimVel_cont hτ.le hlim)).mono Ioo_subset_Icc_self
    exact hvel.congr fun t ht ↦ (galLim_mode_deriv hτ hlim ht i).deriv



theorem galLim_ftc
    {D : RealTimeInterval}
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
      S T tau u0 V phi ulim)
    (t : Real) (ht : t ∈ Icc (0 : Real) tau) :
    tensorHsInclusion (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0)
        (show (0 : Real) ≤ 2 by norm_num) (galLimExt hτ.le hlim 2 t) =
      ccTensorToHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 u0 +
        ∫ r in (0 : Real)..t, galLimVel hτ.le hlim r := by
  apply tensorHs.ext
  funext i
  have h0mem : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, hτ.le⟩
  have hInt : IntervalIntegrable (galLimVel hτ.le hlim) volume 0 t :=
    ((galLimVel_cont hτ.le hlim).mono
      (uIcc_subset_Icc h0mem ht)).intervalIntegrable
  have hmap := ContinuousLinearMap.intervalIntegral_comp_comm
    (coeffCLM (I := I) (M := M) (g := S.family.metric (T : Real))
      (r := 0) (s := 0) (σ := (0 : Real)) i) hInt
  change (∫ r in (0 : Real)..t, (galLimVel hτ.le hlim r).coeff i) =
    (∫ r in (0 : Real)..t, galLimVel hτ.le hlim r).coeff i at hmap
  simp only [tensorHsInclusion_coeff_apply,
    galLimExt_mem hτ.le hlim 2 ht, galLimHs,
    tensorHs.add_coeff, ccTensorToHs_coeff]
  rw [galLim_mode_ftc hτ hlim t ht i, hmap]



theorem galLimExt_deriv
    {D : RealTimeInterval}
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
      ∀ m : Nat, ∃ w : Real →
          tensorHs (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0 (m : Real),
        Continuous w ∧
          (∀ t ∈ Icc (0 : Real) tau',
            tensorHsInclusion (I := I) (M := M)
                (g := S.family.metric (T : Real)) (r := 0) (s := 0)
                (by positivity : (0 : Real) ≤ (m : Real)) (w t) =
              galLimVel hτ.le hlim t) ∧
          (∀ t ∈ Icc (0 : Real) tau',
            w t = galLimVelCan hτ.le hlim m t) ∧
          ∀ t ∈ Ioo (0 : Real) tau',
            HasDerivAt (galLimExt hτ.le hlim m) (w t) t := by
  classical
  obtain ⟨tau', htau', htau'_tau, hlift⟩ :=
    galLimVel_lift (I := I) (M := M) hS hτ hlim
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro m
  obtain ⟨w₀, hw₀, hw₀_eq, hw₀_can⟩ := hlift m
  let w : Real → tensorHs (I := I) (M := M)
      (S.family.metric (T : Real)) 0 0 (m : Real) :=
    Set.IccExtend htau'.le w₀
  have hw : Continuous w := by
    simpa only [w] using Continuous.Icc_extend' hw₀
  have hw_mem (t : Real) (ht : t ∈ Icc (0 : Real) tau') :
      w t = w₀ ⟨t, ht⟩ := by
    simpa only [w] using Set.IccExtend_of_mem htau'.le w₀ ht
  have hw_eq (t : Real) (ht : t ∈ Icc (0 : Real) tau') :
      tensorHsInclusion (I := I) (M := M)
          (g := S.family.metric (T : Real)) (r := 0) (s := 0)
          (by positivity : (0 : Real) ≤ (m : Real)) (w t) =
        galLimVel hτ.le hlim t := by
    rw [hw_mem t ht]
    exact hw₀_eq ⟨t, ht⟩
  have hw_can (t : Real) (ht : t ∈ Icc (0 : Real) tau') :
      w t = galLimVelCan hτ.le hlim m t := by
    rw [hw_mem t ht]
    exact hw₀_can ⟨t, ht⟩
  refine ⟨w, hw, hw_eq, hw_can, ?_⟩
  have h0Small : (0 : Real) ∈ Icc (0 : Real) tau' :=
    ⟨le_rfl, htau'.le⟩
  have h0Tau : (0 : Real) ∈ Icc (0 : Real) tau :=
    ⟨le_rfl, hτ.le⟩
  have hsubTau : Icc (0 : Real) tau' ⊆ Icc (0 : Real) tau :=
    Icc_subset_Icc le_rfl htau'_tau
  have hftc (r : Real) (hr : r ∈ Icc (0 : Real) tau') :
      galLimExt hτ.le hlim m r =
        galLimExt hτ.le hlim m 0 + ∫ s in (0 : Real)..r, w s := by
    apply tensorHs.ext
    funext i
    have hrTau : r ∈ Icc (0 : Real) tau := hsubTau hr
    have hInt : IntervalIntegrable w volume 0 r :=
      hw.intervalIntegrable _ _
    have hmap := ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0)
        (σ := (m : Real)) i) hInt
    change (∫ s in (0 : Real)..r, (w s).coeff i) =
      (∫ s in (0 : Real)..r, w s).coeff i at hmap
    have hIntEq :
        (∫ s in (0 : Real)..r, (w s).coeff i) =
          ∫ s in (0 : Real)..r, (galLimVel hτ.le hlim s).coeff i := by
      refine intervalIntegral.integral_congr (fun s hs ↦ ?_)
      have hsSmall : s ∈ Icc (0 : Real) tau' :=
        (uIcc_subset_Icc h0Small hr) hs
      have hi := congrArg
        (fun v : tensorHs (I := I) (M := M)
          (S.family.metric (T : Real)) 0 0 0 => v.coeff i)
        (hw_eq s hsSmall)
      simpa only [tensorHsInclusion_coeff_apply] using hi
    simp only [galLimExt_mem hτ.le hlim m hrTau,
      galLimExt_mem hτ.le hlim m h0Tau, galLimHs,
      tensorHs.add_coeff]
    rw [galLim_mode_ftc hτ hlim r hrTau i, hlim.lim_init i,
      ← hmap, hIntEq]
  intro t ht
  have hwIoo : ContinuousOn w (Ioo (0 : Real) tau') := hw.continuousOn
  have hwAt : ContinuousAt w t := hw.continuousAt
  have hwInt : IntervalIntegrable w volume 0 t :=
    hw.intervalIntegrable _ _
  have hwMeas : StronglyMeasurableAtFilter w (nhds t) volume :=
    hwIoo.stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hprim : HasDerivAt
      (fun r : Real => ∫ s in (0 : Real)..r, w s) (w t) t :=
    intervalIntegral.integral_hasDerivAt_right hwInt hwMeas hwAt
  have hsum : HasDerivAt
      (fun r : Real => galLimExt hτ.le hlim m 0 +
        ∫ s in (0 : Real)..r, w s) (w t) t :=
    hprim.const_add (galLimExt hτ.le hlim m 0)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  exact hftc r hr



theorem galLimExt_ode
    {D : RealTimeInterval}
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
      ∀ m : Nat, ∀ t ∈ Ioo (0 : Real) tau',
        HasDerivAt (galLimExt hτ.le hlim m)
          (galLimVelCan hτ.le hlim m t) t := by
  obtain ⟨tau', htau', htau'_tau, hd⟩ :=
    galLimExt_deriv (I := I) (M := M) hS hτ hlim
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro m t ht
  obtain ⟨w, _hw, _hw0, hwCan, hwDeriv⟩ := hd m
  have h := hwDeriv t ht
  rw [hwCan t ⟨ht.1.le, ht.2.le⟩] at h
  exact h



theorem galLimExt_smooth
    {D : RealTimeInterval}
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
      ∀ m : Nat, ContDiffOn Real ∞
        (galLimExt hτ.le hlim m) (Ioo (0 : Real) tau') := by
  classical
  obtain ⟨tauO, htauO, htauO_tau, hode⟩ :=
    galLimExt_ode (I := I) (M := M) hS hτ hlim
  obtain ⟨tauA, htauA, _htauA_one, hregA, hLap⟩ :=
    lapDiffHs_dyn_fin (I := I) (M := M) S.family hS.smoothMetric T
  let tau' : Real := min tauO tauA
  have htau' : 0 < tau' := by
    simpa only [tau'] using lt_min htauO htauA
  have htau'_O : tau' ≤ tauO := by
    exact min_le_left _ _
  have htau'_A : tau' ≤ tauA := by
    exact min_le_right _ _
  have htau'_tau : tau' ≤ tau := htau'_O.trans htauO_tau
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let zeta : Real → C^∞⟮I, M; Real⟯ := fun s =>
    conjCoeff (I := I) (M := M) S ((T : Real) - s)
  have hback : Ioo (0 : Real) tau' ⊆
      {s : Real | (T : Real) - s ∈ D.regular} := by
    intro s hs
    exact hregA s ⟨hs.1.le, hs.2.le.trans htau'_A⟩
  have hzeta : ContMDiffOn (I.prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun p : M × Real => (zeta p.2 : M → Real) p.1)
      ((Set.univ : Set M) ×ˢ Ioo (0 : Real) tau') := by
    simpa only [zeta, conjCoeffRev] using
      (conjCoeff_rev (I := I) S hS T).mono
        (Set.prod_mono (Set.Subset.rfl) hback)
  have hfin : ∀ k : Nat, ∀ m : Nat, ContDiffOn Real k
      (galLimExt hτ.le hlim m) (Ioo (0 : Real) tau') := by
    intro k
    induction k with
    | zero =>
        intro m
        apply contDiffOn_zero.mpr
        exact (galLimExt_cont hτ.le hlim m).continuousOn
    | succ k ih =>
        have hvel (m : Nat) : ContDiffOn Real k
            (galLimVelCan hτ.le hlim m) (Ioo (0 : Real) tau') := by
          let e := tensorHs.castEquiv (I := I) (M := M)
            (g := q) (r := 0) (s := 0)
            (by norm_num : (((m + 1) + 2 : Nat) : Real) =
              ((m + 1 : Nat) : Real) + 2)
          let U : Real → tensorHs (I := I) (M := M) q 0 0
              (((m + 1 : Nat) : Real) + 2) := fun t =>
            e (galLimExt hτ.le hlim ((m + 1) + 2) t)
          have hU : ContDiffOn Real k U (Ioo (0 : Real) tau') := by
            simpa only [U, Function.comp_apply] using
              e.contDiff.comp_contDiffOn (ih ((m + 1) + 2))
          let Jm := tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0)
            (by norm_num : ((m + 1 : Nat) : Real) ≤
              ((m + 1 : Nat) : Real) + 2)
          let Um : Real → tensorHs (I := I) (M := M) q 0 0
              ((m + 1 : Nat) : Real) := fun t => Jm (U t)
          have hUm : ContDiffOn Real k Um (Ioo (0 : Real) tau') := by
            simpa only [Um, Function.comp_apply] using
              Jm.contDiff.comp_contDiffOn hU
          have hfixed : ContDiffOn Real k
              (fun t => tensorScaleLaplacian (I := I) (M := M)
                (g := q) (r := 0) (s := 0) ((m + 1 : Nat) : Real) (U t))
              (Ioo (0 : Real) tau') := by
            simpa only [Function.comp_apply] using
              (tensorScaleLaplacian (I := I) (M := M)
                (g := q) (r := 0) (s := 0)
                ((m + 1 : Nat) : Real)).contDiff.comp_contDiffOn hU
          have hdiff : ContDiffOn Real k
              (fun t => lapDiffHs (I := I) (M := M) q
                (S.family.metric ((T : Real) - t)) (m + 1) (U t))
              (Ioo (0 : Real) tau') := by
            simpa only [q] using
              hLap tau' htau' htau'_A (m + 1) k U hU
          have hpot : ContDiffOn Real k
              (fun t => scalarPotHs (I := I) (M := M) q
                (zeta t) (m + 1) (Um t))
              (Ioo (0 : Real) tau') :=
            scalarPot_dyn_fin (I := I) (M := M) q zeta isOpen_Ioo hzeta
              (m + 1) k Um hUm
          have hvhs : ContDiffOn Real k
              (galLimVelHs hτ.le hlim (m + 1)) (Ioo (0 : Real) tau') := by
            simpa only [galLimVelHs, q, e, U, Jm, Um, zeta] using
              (hfixed.add hdiff).add hpot
          let Jvel := tensorHsInclusion (I := I) (M := M)
            (g := q) (r := 0) (s := 0)
            (by exact_mod_cast Nat.le_succ m :
              (m : Real) ≤ ((m + 1 : Nat) : Real))
          have hcan : ContDiffOn Real k
              (fun t => Jvel (galLimVelHs hτ.le hlim (m + 1) t))
              (Ioo (0 : Real) tau') := by
            simpa only [Function.comp_apply] using
              Jvel.contDiff.comp_contDiffOn hvhs
          simpa only [galLimVelCan, q, Jvel] using hcan
        intro m
        have hdiff : DifferentiableOn Real (galLimExt hτ.le hlim m)
            (Ioo (0 : Real) tau') := by
          intro t ht
          exact (hode m t ⟨ht.1, ht.2.trans_le htau'_O⟩).differentiableAt
            |>.differentiableWithinAt
        have hderiv_cd : ContDiffOn Real k
            (deriv (galLimExt hτ.le hlim m)) (Ioo (0 : Real) tau') := by
          refine (hvel m).congr ?_
          intro t ht
          exact (hode m t ⟨ht.1, ht.2.trans_le htau'_O⟩).deriv
        simp only [Nat.cast_add, Nat.cast_one]
        rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
        refine ⟨hdiff, ?_, hderiv_cd⟩
        intro hk
        norm_num at hk
  refine ⟨tau', htau', htau'_tau, ?_⟩
  intro m
  rw [contDiffOn_infty]
  intro k
  exact hfin k m



theorem scalar_gal_limit
    {D : RealTimeInterval}
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
    ∃ u : MaxRegSolutionSpace (I := I) (M := M)
        (g := S.family.metric (T : Real)) (r := 0) (s := 0) 0 tau,
      timeH1.trace0 _ tau u =
          ccTensorToHs (I := I) (M := M)
            (S.family.metric (T : Real)) 0 0 u0 ∧
      (∀ t : Icc (0 : Real) tau,
        u.toFun t =
          tensorHsInclusion (I := I) (M := M)
            (g := S.family.metric (T : Real)) (r := 0) (s := 0)
            (show (0 : Real) ≤ 2 by norm_num)
            (galLimExt hτ.le hlim 2 t)) ∧
      timeH1.timeDeriv _ tau u =
        ofContinuousOn (galLimVel_cont hτ.le hlim) := by
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  let v : timeL2
      (tensorHs (I := I) (M := M) q 0 0 0) tau :=
    ofContinuousOn (galLimVel_cont hτ.le hlim)
  let init : tensorHs (I := I) (M := M) q 0 0 0 :=
    ccTensorToHs (I := I) (M := M) q 0 0 u0
  let u : MaxRegSolutionSpace (I := I) (M := M)
      (g := q) (r := 0) (s := 0) 0 tau :=
    timeH1.mk init v
  refine ⟨u, ?_, ?_, ?_⟩
  · simp only [u, init, q, timeH1.trace0_mk]
  · intro t
    have h0mem : (0 : Real) ∈ Icc (0 : Real) tau := ⟨le_rfl, hτ.le⟩
    have hrep :
        (v : Real → tensorHs (I := I) (M := M) q 0 0 0) =ᵐ[timeMeasure tau]
          galLimVel hτ.le hlim := by
      simpa only [v, q] using
        (coeFn_ofContinuousOn (galLimVel_cont hτ.le hlim))
    have hrepVol : ∀ᵐ s ∂volume, s ∈ Icc (0 : Real) tau →
        v s = galLimVel hτ.le hlim s :=
      (ae_restrict_iff' measurableSet_Icc).1 hrep
    have hintEq :
        (∫ s in (0 : Real)..(t : Real), v s) =
          ∫ s in (0 : Real)..(t : Real), galLimVel hτ.le hlim s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hrepVol] with s hs hsI
      exact hs ((Set.uIoc_subset_uIcc).trans
        (uIcc_subset_Icc h0mem t.2) hsI)
    simp only [u, timeH1.toFun_apply, timeH1.init_mk,
      timeH1.deriv_mk]
    rw [hintEq]
    simpa only [init, q] using (galLim_ftc hτ hlim t t.2).symm
  · simp only [u, v, q, timeH1.timeDeriv_mk]

end DifferentialGeometry.PDE.RicciFlow.Entropy
