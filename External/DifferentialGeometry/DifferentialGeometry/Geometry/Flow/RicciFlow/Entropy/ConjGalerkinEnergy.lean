import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.GalerkinParabolicEnergy
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjCriticalTame
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.ConjGalerkin

set_option autoImplicit false
set_option maxHeartbeats 6400000









noncomputable section

open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [BoundarylessManifold I M] in


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem galVec_norm_sq
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c : TensorEigenIdx (I := I) (M := M) q 0 0 → Real) (sigma : Real) :
    ‖scalarGalVec (I := I) (M := M) q F c sigma‖ ^ 2 =
      ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i sigma * (c i) ^ 2 := by
  classical
  rw [tensorHs.norm_sq_eq_tsum]
  rw [tsum_eq_sum (s := F) (fun i hi => by
    rw [scalarGalVec_coeff, if_neg hi]
    ring)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [scalarGalVec_coeff, if_pos hi]

omit [BoundarylessManifold I M] in
open scoped Classical in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem gal_crit_nf
    (q : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) q 0 0))
    (c f R : TensorEigenIdx (I := I) (M := M) q 0 0 → Real)
    (k : Nat) (C : Real)
    (hforce : ∀ i, f i = R i)
    (hcrit :
      2 * ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (k : Real) *
            ((scalarGalVec (I := I) (M := M) q F c 0).coeff i * R i) ≤
        ((23 : Real) / 12) *
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i ((k + 1 : Nat) : Real) *
                ((scalarGalVec (I := I) (M := M) q F c 0).coeff i) ^ 2) +
          C * ∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (k : Real) *
              ((scalarGalVec (I := I) (M := M) q F c 0).coeff i) ^ 2) :
      2 * ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (k : Real) * (c i * f i) ≤
        ((23 : Real) / 12) *
            (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i ((k : Real) + 1) * (c i) ^ 2) +
          C * ∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i (k : Real) * (c i) ^ 2 := by
  have hleft :
      (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (k : Real) *
            ((scalarGalVec (I := I) (M := M) q F c 0).coeff i * R i)) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (k : Real) * (c i * f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [scalarGalVec_coeff, if_pos hi, hforce i]
  have hhigh :
      (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i ((k + 1 : Nat) : Real) *
            ((scalarGalVec (I := I) (M := M) q F c 0).coeff i) ^ 2) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i ((k : Real) + 1) * (c i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_add, Nat.cast_one, scalarGalVec_coeff, if_pos hi]
  have hlow :
      (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (k : Real) *
            ((scalarGalVec (I := I) (M := M) q F c 0).coeff i) ^ 2) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (k : Real) * (c i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [scalarGalVec_coeff, if_pos hi]
  rw [hleft, hhigh, hlow] at hcrit
  exact hcrit

open scoped Classical in



theorem scalar_gal_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    let q := S.family.metric (T : Real)
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∀ (u0 : SmoothCcTensor q 0 0)
        (Fs : Nat → Finset (TensorEigenIdx (I := I) (M := M) q 0 0)),
        ∃ V : Nat → Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real,
          (∀ N i, i ∈ Fs N →
            ContinuousOn (fun t => V N t i) (Set.Icc (0 : Real) tau)) ∧
          (∀ N t, t ∈ Set.Ico (0 : Real) tau → ∀ i, i ∈ Fs N →
            HasDerivWithinAt (fun r => V N r i)
              (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V N t i +
                (scalarGalPert (I := I) (M := M) S T t
                  (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i)
              (Set.Ici t) t) ∧
          (∀ N i, i ∈ Fs N →
            V N 0 i =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator
                  (I := I) (M := M) q 0 0)
                (SmoothCcTensor.toL2 u0) i) ∧
          (∀ N t i, i ∉ Fs N → V N t i = 0) ∧
          ∀ k : Nat, ∃ Bound : Real, ∀ N t,
            t ∈ Set.Icc (0 : Real) tau →
              galerkinEnergy (I := I) (M := M) (Fs N) (V N)
                (k : Real) t ≤ Bound := by
  classical
  dsimp only
  let q : SmoothRiemannianMetric I M := S.family.metric (T : Real)
  obtain ⟨G, hG⟩ :=
    scalar_gal_exists (I := I) (M := M) S hS T
  let tauG : Real := G.tau
  have htauG : 0 < tauG := by
    simpa only [tauG] using hG.pos
  have htauG_one : tauG ≤ 1 := by
    simpa only [tauG] using hG.le_one
  obtain ⟨tauC, htauC, _htauC_one, Cmid, hCmid, hcrit⟩ :=
    scalar_crit_tame (I := I) (M := M) S hS T
  have hcore := scalarGalPert_fin (I := I) (M := M) S hS T
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hcore
  let tau : Real := min (min tauG tauC) (delta / 2)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min (lt_min htauG htauC) (half_pos hdelta)
  have htau_tauG : tau ≤ tauG :=
    (min_le_left (min tauG tauC) (delta / 2)).trans (min_le_left tauG tauC)
  have htau_tauC : tau ≤ tauC :=
    (min_le_left (min tauG tauC) (delta / 2)).trans (min_le_right tauG tauC)
  have htau_one : tau ≤ 1 := htau_tauG.trans htauG_one
  have htau_delta : tau < delta :=
    (min_le_right (min tauG tauC) (delta / 2)).trans_lt (half_lt_self hdelta)
  have hIccG : Set.Icc (0 : Real) tau ⊆ Set.Icc (0 : Real) tauG := by
    intro t ht
    exact ⟨ht.1, ht.2.trans htau_tauG⟩
  have hIccC : Set.Icc (0 : Real) tau ⊆ Set.Icc (0 : Real) tauC := by
    intro t ht
    exact ⟨ht.1, ht.2.trans htau_tauC⟩
  have hIcoG : Set.Ico (0 : Real) tau ⊆ Set.Ico (0 : Real) tauG := by
    intro t ht
    exact ⟨ht.1, ht.2.trans_le htau_tauG⟩
  have htball (t : Real) (ht : t ∈ Set.Icc (0 : Real) tau) :
      t ∈ Metric.ball (0 : Real) delta := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt htau_delta
  refine ⟨tau, htau, htau_one, ?_⟩
  intro u0 Fs
  let uInit : tensorHs (I := I) (M := M) q 0 0 0 :=
    ccTensorToHs (I := I) (M := M) q 0 0 u0
  choose V hV using fun N => hG.exists_sol uInit (Fs N)
  let Fseq : Nat → Real → TensorEigenIdx (I := I) (M := M) q 0 0 → Real :=
    fun N t i =>
      (scalarGalPert (I := I) (M := M) S T t
        (scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 2)).coeff i
  have hcont : ∀ N i, i ∈ Fs N →
      ContinuousOn (fun t => V N t i) (Set.Icc (0 : Real) tau) := by
    intro N i hi
    exact ((hV N).cont i hi).mono hIccG
  have hderiv : ∀ N t, t ∈ Set.Ico (0 : Real) tau → ∀ i, i ∈ Fs N →
      HasDerivWithinAt (fun r => V N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * V N t i + Fseq N t i)
        (Set.Ici t) t := by
    intro N t ht i hi
    simpa only [Fseq, scalarGalRhs] using (hV N).deriv t (hIcoG ht) i hi
  have hinit : ∀ N i, i ∈ Fs N →
      V N 0 i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
          (SmoothCcTensor.toL2 u0) i := by
    intro N i hi
    simpa only [uInit, ccTensorToHs_coeff] using (hV N).init i hi
  have hsupp : ∀ N t i, i ∉ Fs N → V N t i = 0 := by
    intro N t i hi
    exact (hV N).support t i hi
  have hclosure : ∀ (N k : Nat), ∀ t ∈ Set.Ico (0 : Real) tau,
      2 * ∑ i ∈ Fs N,
          tensorSobolevWeight (I := I) (M := M) i (k : Real) *
            (V N t i * Fseq N t i) ≤
        ((23 : Real) / 12) *
            galerkinEnergy (I := I) (M := M) (Fs N) (V N) ((k : Real) + 1) t +
          Cmid k * galerkinEnergy (I := I) (M := M) (Fs N) (V N) (k : Real) t := by
    intro N k t ht
    let v : tensorHs (I := I) (M := M) q 0 0 0 :=
      scalarGalVec (I := I) (M := M) q (Fs N) (V N t) 0
    let hv : (Function.support v.coeff).Finite :=
      scalarGalVec_finite (I := I) (M := M) q (Fs N) (V N t) 0
    have hsub : hv.toFinset ⊆ Fs N := by
      intro i hi
      exact scalarGalVec_supp (I := I) (M := M) q (Fs N) (V N t) 0
        (hv.mem_toFinset.mp hi)
    have hcrit' := hcrit k t (hIccC (Set.Ico_subset_Icc_self ht))
      (Fs N) v hv hsub
    let R : TensorEigenIdx (I := I) (M := M) q 0 0 → Real := fun i =>
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
            (SmoothCcTensor.toL2
              (scalarLapDiffCc (I := I) q
                  (S.family.metric ((T : Real) - t))
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
                    (I := I) (M := M) v hv) +
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul
                  (I := I) (M := M) q 0 0
                  (conjCoeff (I := I) (M := M) S ((T : Real) - t))
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
                    (I := I) (M := M) v hv))) i
    have hforce (i : TensorEigenIdx (I := I) (M := M) q 0 0) :
        Fseq N t i = R i := by
      simpa only [R, Fseq, v, hv] using
        (hball (htball t (Set.Ico_subset_Icc_self ht))) (Fs N) (V N t) i
    have hcritR :
        2 * ∑ i ∈ Fs N,
            tensorSobolevWeight (I := I) (M := M) i (k : Real) *
              (v.coeff i * R i) ≤
          ((23 : Real) / 12) *
              (∑ i ∈ Fs N,
                tensorSobolevWeight (I := I) (M := M) i ((k + 1 : Nat) : Real) *
                  (v.coeff i) ^ 2) +
            Cmid k * ∑ i ∈ Fs N,
              tensorSobolevWeight (I := I) (M := M) i (k : Real) *
                (v.coeff i) ^ 2 := by
      simpa only [R, q] using hcrit'
    have hnf := gal_crit_nf (I := I) (M := M) q (Fs N)
      (V N t) (Fseq N t) R k (Cmid k) hforce (by
        simpa only [v] using hcritR)
    simpa only [galerkinEnergy] using hnf
  have hinitEnergy : ∀ (N k : Nat),
      galerkinEnergy (I := I) (M := M) (Fs N) (V N) (k : Real) 0 ≤
        ‖ccTensorToHs (I := I) (M := M) q 0 (k : Real) u0‖ ^ 2 := by
    intro N k
    rw [galerkinEnergy]
    calc
      ∑ i ∈ Fs N, tensorSobolevWeight (I := I) (M := M) i (k : Real) *
            (V N 0 i) ^ 2 =
          ∑ i ∈ Fs N,
            tensorSobolevWeight (I := I) (M := M) i (k : Real) *
              (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
                (SmoothCcTensor.toL2 u0) i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hinit N i hi]
      _ ≤ ‖ccTensorToHs (I := I) (M := M) q 0 (k : Real) u0‖ ^ 2 :=
        cc_partial_le_norm (I := I) (M := M) q 0 (k : Real) u0 (Fs N)
  have hbounds := galerkin_energy_uniform_bound_perScale
    (I := I) (M := M) (g := q) (r := 0) (s₀ := 0)
    (U := V) (Fseq := Fseq) (sseq := Fs) (T := tau) (σ₀ := 0)
    (Cδ := (23 : Real) / 12) (Cmid := Cmid) (seed := fun _ => 0)
    (B0 := fun k =>
      ‖ccTensorToHs (I := I) (M := M) q 0 (k : Real) u0‖ ^ 2)
    (by norm_num) hCmid hcont hderiv (by
      intro N k t ht
      simpa only [zero_add, zero_mul, add_zero] using hclosure N k t ht)
    (by
      intro N k
      simpa only [zero_add] using hinitEnergy N k)
  refine ⟨V, hcont, ?_, hinit, hsupp, ?_⟩
  · intro N t ht i hi
    simpa only [Fseq] using hderiv N t ht i hi
  · simpa only [zero_add] using hbounds

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
