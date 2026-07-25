import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge


noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Topology Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def bareChartJetContent (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : SmoothCcTensor g r s) (α : M) (N : ℕ) (y : EuclN) : ℝ :=
  ∑ q' : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)),
    ∑ m ∈ Finset.range (N + 1),
      ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g r s X α q'.1 q'.2) y‖

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bareChartJetContent_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : SmoothCcTensor g r s) (α : M) (N : ℕ) (y : EuclN) :
    0 ≤ bareChartJetContent (I := I) (M := M) g r s X α N y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma iteratedFDeriv_rawPullR_le_bareChartJetContent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {m N : ℕ} (hm : m ≤ N) (y : EuclN) :
    ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g r s X α Idx Jdx) y‖ ≤
      bareChartJetContent (I := I) (M := M) g r s X α N y := by
  classical
  set f : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun q' => ∑ m' ∈ Finset.range (N + 1),
      ‖iteratedFDeriv ℝ m' (tensorComponentEuclideanChart (I := I) (M := M) g r s X α q'.1 q'.2) y‖ with hf_def
  have hmem : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have h_inner : ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g r s X α Idx Jdx) y‖ ≤
      f ⟨Idx, Jdx⟩ := by
    rw [hf_def]
    exact Finset.single_le_sum (f := fun m' =>
      ‖iteratedFDeriv ℝ m' (tensorComponentEuclideanChart (I := I) (M := M) g r s X α Idx Jdx) y‖)
      (fun m' _ => norm_nonneg _) hmem
  refine h_inner.trans ?_
  have hbig : f ⟨Idx, Jdx⟩ ≤ ∑ q', f q' :=
    Finset.single_le_sum (f := f) (fun q' _ => Finset.sum_nonneg fun m' _ => norm_nonneg _)
      (Finset.mem_univ _)
  refine hbig.trans (le_of_eq ?_)
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma bareChartJetContent_mono (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : SmoothCcTensor g r s) (α : M) {N N' : ℕ} (hN : N ≤ N') (y : EuclN) :
    bareChartJetContent (I := I) (M := M) g r s X α N y ≤
      bareChartJetContent (I := I) (M := M) g r s X α N' y := by
  classical
  have hsub : Finset.range (N + 1) ⊆ Finset.range (N' + 1) :=
    Finset.range_mono (by omega)
  simp only [bareChartJetContent]
  refine Finset.sum_le_sum (fun q' _ => ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => norm_nonneg _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma iteratedFDeriv_euclidPartial_norm_le
    {u : EuclN → ℝ} {O : Set EuclN} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    (m : Fin (Module.finrank ℝ E)) (l : ℕ) {y : EuclN} (hy : y ∈ O) :
    ‖iteratedFDeriv ℝ l (fun z => euclidPartial (E := E) m u z) y‖ ≤
      ‖iteratedFDeriv ℝ (l + 1) u y‖ := by
  classical
  have h_cdAt : ContDiffAt ℝ ∞ u y := hu.contDiffAt (hO.mem_nhds hy)
  have h_ev : (fun z => euclidPartial (E := E) m u z) =ᶠ[nhds y]
      (fun z => fderiv ℝ u z (EuclideanSpace.single m 1)) := by
    filter_upwards with z
    rw [euclidPartial_def]
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_ev l).self_of_nhds]
  have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun z => fderiv ℝ u z) y := by
    have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
    have h := h_cdAt.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
    simpa using h
  have h_clm := norm_iteratedFDeriv_clm_apply_const
    (𝕜 := ℝ) (f := fun z => fderiv ℝ u z) (c := EuclideanSpace.single m 1)
    (x := y) (n := l) h_fderiv_cdAt (by exact_mod_cast le_top)
  have h_single_norm : ‖(EuclideanSpace.single m (1 : ℝ))‖ = 1 := by
    rw [PiLp.norm_single]; simp
  have h_fderiv_iter : ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ u z) y‖ =
      ‖iteratedFDeriv ℝ (l + 1) u y‖ := norm_iteratedFDeriv_fderiv
  calc ‖iteratedFDeriv ℝ l
          (fun z => (fderiv ℝ u z) (EuclideanSpace.single m 1)) y‖
      ≤ ‖(EuclideanSpace.single m (1 : ℝ))‖ *
          ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ u z) y‖ := h_clm
    _ = ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ u z) y‖ := by
        rw [h_single_norm, one_mul]
    _ = ‖iteratedFDeriv ℝ (l + 1) u y‖ := h_fderiv_iter

omit [BoundarylessManifold I M] in
lemma iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : SmoothCcTensor g r s) (p l : ℕ), l + p ≤ P →
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin (s + p) → Fin (Module.finrank ℝ E)),
          ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
            ‖iteratedFDeriv ℝ l
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad (I := I) g r s p X) α Idx Jdx) y‖ ≤
              C * bareChartJetContent (I := I) (M := M) g r s X α (l + p) y := by
  classical
  obtain ⟨Γ, hΓ_nn, hΓ⟩ :=
    exists_christoffel_bound_valence_range (I := I) (M := M) g r s α P P
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n); exact_mod_cast this
  set Npair : ℝ := (n : ℝ) ^ (r + (s + P)) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity

  set Cstep : ℝ := 1 + Npair * (2 : ℝ) ^ P * Γ with hCstep_def
  have hCstep_nn : 0 ≤ Cstep := by rw [hCstep_def]; positivity
  set Cp : ℕ → ℝ := fun p => Cstep ^ p with hCp_def
  have hCp_nn : ∀ p, 0 ≤ Cp p := fun p => by rw [hCp_def]; positivity
  refine ⟨(Finset.range (P + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos P)⟩ Cp,
    le_trans (hCp_nn 0) (Finset.le_sup' Cp (Finset.mem_range.mpr (Nat.succ_pos P))), ?_⟩
  intro X

  have hmain : ∀ p l : ℕ, l + p ≤ P →
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin (s + p) → Fin (Module.finrank ℝ E)),
        ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ l
              (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                (iteratedCovGrad (I := I) g r s p X) α Idx Jdx) y‖ ≤
            Cp p * bareChartJetContent (I := I) (M := M) g r s X α (l + p) y := by
    intro p
    induction p with
    | zero =>
        intro l _hlP Idx Jdx y _hy
        simp only [hCp_def, pow_zero, one_mul]

        have hLHS :
            ‖iteratedFDeriv ℝ l
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + 0)
                  (iteratedCovGrad (I := I) g r s 0 X) α Idx Jdx) y‖ =
              ‖iteratedFDeriv ℝ l
                (tensorComponentEuclideanChart (I := I) (M := M) g r s X α Idx Jdx) y‖ := by
          congr 1
        rw [hLHS]
        exact iteratedFDeriv_rawPullR_le_bareChartJetContent (I := I) (M := M)
          g r s X α Idx Jdx (by omega) y
    | succ p ih =>
        intro l hlP Idx Jdx y hy
        have hy_mem : y ∈ chartTargetEuclid (I := I) (M := M) α :=
          chartImagePOUTsupport_subset_target (I := I) (M := M) α hy
        set Z : SmoothCcTensor g r (s + p) :=
          iteratedCovGrad (I := I) g r s p X with hZ_def

        set m0 : Fin (Module.finrank ℝ E) := Jdx 0 with hm0_def
        set Jtail : Fin (s + p) → Fin (Module.finrank ℝ E) :=
          Matrix.vecTail Jdx with hJtail_def

        have hsplit : tensorComponentEuclideanChart (I := I) (M := M) g r (s + (p + 1))
              (iteratedCovGrad (I := I) g r s (p + 1) X) α Idx Jdx =ᶠ[nhds y]
            (fun z => euclidPartial (E := E) m0
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) z +
              covDerivLowerOrderTerm (I := I) (M := M) g r (s + p) Z α m0 Idx Jtail z) := by
          have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
            chartTargetEuclid_isOpen (I := I) (M := M) α
          filter_upwards [h_open.mem_nhds hy_mem] with z hz
          have hJcons : (Matrix.vecCons m0 Jtail :
              Fin (s + p + 1) → Fin (Module.finrank ℝ E)) = Jdx := by
            funext i
            refine Fin.cases ?_ (fun i => ?_) i
            · simp [hm0_def]
            · simp [hJtail_def, Matrix.vecTail]
          have hstep := fderiv_rawPullR_single_eq (I := I) (M := M) g r (s + p) Z α m0 Idx
            Jtail hz
          rw [euclidPartial_def]
          have hcovGrad_eq :
              tensorComponentEuclideanChart (I := I) (M := M) g r (s + (p + 1))
                  (iteratedCovGrad (I := I) g r s (p + 1) X) α Idx Jdx z =
                tensorComponentEuclideanChart (I := I) (M := M) g r ((s + p) + 1)
                  (covGrad (I := I) (M := M) g r (s + p) Z) α Idx
                  (Matrix.vecCons m0 Jtail) z := by
            rw [hZ_def] at *
            congr 1
            · exact hJcons.symm
          rw [hcovGrad_eq, hstep]
          ring
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hsplit l).self_of_nhds]

        have hA_cdAt : ContDiffAt ℝ ∞
            (fun z => euclidPartial (E := E) m0
              (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) z) y := by
          have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
            chartTargetEuclid_isOpen (I := I) (M := M) α
          have hraw_cdAt : ContDiffAt ℝ ∞
              (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) y :=
            rawPullR_contDiffAt (I := I) (M := M) g r (s + p) Z α Idx Jtail hy_mem
          have hev : (fun z => euclidPartial (E := E) m0
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) z) =ᶠ[nhds y]
              (fun z => fderiv ℝ (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) z
                (EuclideanSpace.single m0 1)) := by
            filter_upwards with z; rw [euclidPartial_def]
          refine ContDiffAt.congr_of_eventuallyEq ?_ hev
          have h_fderiv_cdAt : ContDiffAt ℝ (∞ : WithTop ℕ∞)
              (fun z => fderiv ℝ (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) z) y := by
            have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
              rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl]
            have h := hraw_cdAt.fderiv_right (m := (∞ : WithTop ℕ∞)) hle
            simpa using h
          exact (ContinuousLinearMap.apply ℝ ℝ
            (EuclideanSpace.single m0 (1 : ℝ))).contDiff.contDiffAt.comp y h_fderiv_cdAt
        have hB_cdAt : ContDiffAt ℝ ∞
            (fun z => covDerivLowerOrderTerm (I := I) (M := M) g r (s + p) Z α m0 Idx Jtail z)
            y := by
          have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
            chartTargetEuclid_isOpen (I := I) (M := M) α
          have h_cdOn := covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M)
            g r (s + p) Z α m0 Idx Jtail
            (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
              (I := I) (M := M) g r (s + p) Z α Idx' Jdx')
          exact h_cdOn.contDiffAt (h_open.mem_nhds hy_mem)
        have hjle : (l : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
        rw [fun_iteratedFDeriv_add_apply (hA_cdAt.of_le hjle) (hB_cdAt.of_le hjle)]
        refine le_trans (norm_add_le _ _) ?_

        set RHS : ℝ := bareChartJetContent (I := I) (M := M) g r s X α (l + (p + 1)) y
          with hRHS_def
        have hRHS_nn : 0 ≤ RHS := bareChartJetContent_nonneg (I := I) (M := M) g r s X α _ y

        have hA : ‖iteratedFDeriv ℝ l
              (fun z => euclidPartial (E := E) m0
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) z) y‖ ≤
            Cp p * RHS := by
          have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
            chartTargetEuclid_isOpen (I := I) (M := M) α
          have heuclid := iteratedFDeriv_euclidPartial_norm_le (E := E)
            (u := tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail)
            (O := chartTargetEuclid (I := I) (M := M) α) h_open
            (rawPullR_contDiffOn (I := I) (M := M) g r (s + p) Z α Idx Jtail) m0 l hy_mem
          refine heuclid.trans ?_
          have hih := ih (l + 1) (by omega) Idx Jtail y hy
          rw [hZ_def] at hih
          refine hih.trans ?_
          have hwin : bareChartJetContent (I := I) (M := M) g r s X α ((l + 1) + p) y ≤ RHS := by
            rw [hRHS_def]
            exact bareChartJetContent_mono (I := I) (M := M) g r s X α (by omega) y
          exact mul_le_mul_of_nonneg_left hwin (hCp_nn p)

        have hB : ‖iteratedFDeriv ℝ l
              (fun z => covDerivLowerOrderTerm (I := I) (M := M)
                g r (s + p) Z α m0 Idx Jtail z) y‖ ≤
            (Npair * (2 : ℝ) ^ P * Γ * Cp p) * RHS := by
          have hleib := lowerOrderTerm_iteratedFDeriv_norm_leR (I := I) (M := M)
            g r (s + p) Z α m0 Idx Jtail l hy_mem
          refine hleib.trans ?_
          have hp_le_P : p ≤ P := by omega

          have h_per : ∀ q'' : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin (s + p) → Fin (Module.finrank ℝ E)),
              (∑ l' ∈ Finset.range (l + 1),
                (l.choose l' : ℝ) *
                  ‖iteratedFDeriv ℝ l'
                    (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m0 Idx
                      q''.1 Jtail q''.2) y‖ *
                  ‖iteratedFDeriv ℝ (l - l')
                    (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α q''.1 q''.2) y‖) ≤
                ((2 : ℝ) ^ P) * (Γ * (Cp p * RHS)) := by
            intro q''
            have h1 : (∑ l' ∈ Finset.range (l + 1),
                (l.choose l' : ℝ) *
                  ‖iteratedFDeriv ℝ l'
                    (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m0 Idx
                      q''.1 Jtail q''.2) y‖ *
                  ‖iteratedFDeriv ℝ (l - l')
                    (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α q''.1 q''.2) y‖) ≤
                ∑ l' ∈ Finset.range (l + 1), (l.choose l' : ℝ) * (Γ * (Cp p * RHS)) := by
              refine Finset.sum_le_sum (fun l' hl' => ?_)
              have hl'l : l' ≤ l := by have := Finset.mem_range.mp hl'; omega
              have hl'P : l' ≤ P := le_trans hl'l (by omega)
              have hΓ_bd : ‖iteratedFDeriv ℝ l'
                  (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m0 Idx
                    q''.1 Jtail q''.2) y‖ ≤ Γ :=
                hΓ p hp_le_P m0 Idx Jtail q'' l' hl'P y hy
              have hraw_bd : ‖iteratedFDeriv ℝ (l - l')
                  (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α q''.1 q''.2) y‖ ≤
                  Cp p * RHS := by
                have hih := ih (l - l') (by omega) q''.1 q''.2 y hy
                rw [hZ_def] at hih ⊢
                refine hih.trans ?_
                have hwin : bareChartJetContent (I := I) (M := M) g r s X α ((l - l') + p) y ≤
                    RHS := by
                  rw [hRHS_def]
                  exact bareChartJetContent_mono (I := I) (M := M) g r s X α (by omega) y
                exact mul_le_mul_of_nonneg_left hwin (hCp_nn p)
              have h_choose_nn : 0 ≤ (l.choose l' : ℝ) := by positivity
              have hraw_nn : 0 ≤ ‖iteratedFDeriv ℝ (l - l')
                  (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α q''.1 q''.2) y‖ := norm_nonneg _
              calc (l.choose l' : ℝ) *
                    ‖iteratedFDeriv ℝ l'
                      (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m0 Idx
                        q''.1 Jtail q''.2) y‖ *
                    ‖iteratedFDeriv ℝ (l - l')
                      (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α q''.1 q''.2) y‖
                  ≤ (l.choose l' : ℝ) * Γ * (Cp p * RHS) := by
                    have ha : (l.choose l' : ℝ) *
                        ‖iteratedFDeriv ℝ l'
                          (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m0 Idx
                            q''.1 Jtail q''.2) y‖ ≤ (l.choose l' : ℝ) * Γ :=
                      mul_le_mul_of_nonneg_left hΓ_bd h_choose_nn
                    have hb : (l.choose l' : ℝ) * Γ ≥ 0 := by positivity
                    calc (l.choose l' : ℝ) *
                          ‖iteratedFDeriv ℝ l'
                            (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m0 Idx
                              q''.1 Jtail q''.2) y‖ *
                          ‖iteratedFDeriv ℝ (l - l')
                            (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α q''.1 q''.2) y‖
                        ≤ ((l.choose l' : ℝ) * Γ) * (Cp p * RHS) :=
                          mul_le_mul ha hraw_bd hraw_nn hb
                      _ = (l.choose l' : ℝ) * Γ * (Cp p * RHS) := by ring
                _ = (l.choose l' : ℝ) * (Γ * (Cp p * RHS)) := by ring
            have h2 : (∑ l' ∈ Finset.range (l + 1), (l.choose l' : ℝ)) = (2 : ℝ) ^ l := by
              rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
            refine h1.trans ?_
            rw [← Finset.sum_mul, h2]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_right₀ (by norm_num) (by omega)

          calc (∑ q'' : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin (s + p) → Fin (Module.finrank ℝ E)),
                ∑ l' ∈ Finset.range (l + 1),
                  (l.choose l' : ℝ) *
                    ‖iteratedFDeriv ℝ l'
                      (covDerivLowerOrderCoeff (I := I) (M := M) g r (s + p) α m0 Idx
                        q''.1 Jtail q''.2) y‖ *
                    ‖iteratedFDeriv ℝ (l - l')
                      (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α q''.1 q''.2) y‖)
              ≤ ∑ _q'' : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin (s + p) → Fin (Module.finrank ℝ E)),
                  ((2 : ℝ) ^ P) * (Γ * (Cp p * RHS)) :=
                Finset.sum_le_sum (fun q'' _ => h_per q'')
            _ = (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin (s + p) → Fin (Module.finrank ℝ E))) : ℝ) *
                  (((2 : ℝ) ^ P) * (Γ * (Cp p * RHS))) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            _ ≤ Npair * (((2 : ℝ) ^ P) * (Γ * (Cp p * RHS))) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                have hcard : Fintype.card ((Fin r → Fin n) × (Fin (s + p) → Fin n)) =
                    n ^ (r + (s + p)) := by
                  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
                  rw [← pow_add]
                rw [hNpair_def]
                calc ((Fintype.card ((Fin r → Fin n) × (Fin (s + p) → Fin n)) : ℕ) : ℝ)
                    = ((n ^ (r + (s + p)) : ℕ) : ℝ) := by rw [hcard]
                  _ ≤ (n : ℝ) ^ (r + (s + P)) := by
                      push_cast
                      exact pow_le_pow_right₀ hn1 (by omega)
            _ = (Npair * (2 : ℝ) ^ P * Γ * Cp p) * RHS := by ring

        have hCp_succ : Cp (p + 1) = Cp p + Npair * (2 : ℝ) ^ P * Γ * Cp p := by
          simp only [hCp_def]; rw [pow_succ, hCstep_def]; ring
        calc ‖iteratedFDeriv ℝ l
                (fun z => euclidPartial (E := E) m0
                  (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p) Z α Idx Jtail) z) y‖ +
              ‖iteratedFDeriv ℝ l
                (fun z => covDerivLowerOrderTerm (I := I) (M := M)
                  g r (s + p) Z α m0 Idx Jtail z) y‖
            ≤ Cp p * RHS + (Npair * (2 : ℝ) ^ P * Γ * Cp p) * RHS := add_le_add hA hB
          _ = Cp (p + 1) * RHS := by rw [hCp_succ]; ring

  intro p l hlP Idx Jdx y hy
  refine (hmain p l hlP Idx Jdx y hy).trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (bareChartJetContent_nonneg (I := I) (M := M) g r s X α _ y)
  exact Finset.le_sup' Cp (Finset.mem_range.mpr (by omega))

omit [BoundarylessManifold I M] in
lemma iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X : SmoothCcTensor g r s) (α : M) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p l : ℕ), l + p ≤ P →
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin (s + p) → Fin (Module.finrank ℝ E)),
          ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
            ‖iteratedFDeriv ℝ l
                (tensorComponentEuclideanChart (I := I) (M := M) g r (s + p)
                  (iteratedCovGrad (I := I) g r s p X) α Idx Jdx) y‖ ≤
              C * bareChartJetContent (I := I) (M := M) g r s X α (l + p) y := by
  obtain ⟨C, hC_nn, hC⟩ :=
    iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent_uniform
      (I := I) (M := M) g r s α P
  exact ⟨C, hC_nn, fun p l hlP Idx Jdx y hy => hC X p l hlP Idx Jdx y hy⟩

omit [BoundarylessManifold I M] in
theorem bareJet_le_fiber
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : SmoothCcTensor g r s) {y : EuclN},
        y ∈ chartPouKernel (I := I) (M := M) α →
        bareChartJetContent (I := I) (M := M) g r s D α N y ≤
          C * ∑ i ∈ Finset.range (N + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r (s + i)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((iteratedCovGrad (I := I) g r s i D).toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) := by
  classical

  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum (I := I) (M := M) g r s α N N (le_refl N)

  have h_fib : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ (D : SmoothCcTensor g r s) {z : EuclN},
        z ∈ chartPouKernel (I := I) (M := M) α →
        tensorComponentAbsSum (I := I) (M := M) g r (s + i)
          (iteratedCovGrad (I := I) g r s i D) α z ≤
          Ci * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r (s + i)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
            ((iteratedCovGrad (I := I) g r s i D).toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))) := by
    intro i
    obtain ⟨Ci, hCi_nn, hCi⟩ :=
      exists_zeroContentR_le_fiberNorm_on_pouKernel (I := I) (M := M) g r (s + i) α
    refine ⟨Ci, hCi_nn, fun D {z} hz => ?_⟩
    refine (hCi (iteratedCovGrad (I := I) g r s i D) hz).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCi_nn
    letI : Bundle.RiemannianBundle (fun w : M => TensorRSSpace r (s + i) I w) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r (s + i)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r (s + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g r s i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))]
    exact norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r (s + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g r s i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
  choose Cfib hCfib_nn hCfib using h_fib
  set Cfibmax : ℝ := (Finset.range (N + 1)).sup' (by simp) Cfib with hCfibmax_def
  have hCfibmax_nn : 0 ≤ Cfibmax :=
    le_trans (hCfib_nn 0) (Finset.le_sup' Cfib (by simp))
  set Npair : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
    (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity
  refine ⟨Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax)), by positivity, ?_⟩
  intro D y hyK
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  set Fib : ℕ → ℝ := fun i =>
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r (s + i) b
      ((iteratedCovGrad (I := I) g r s i D).toSection b)) with hFib_def
  have hFib_nn : ∀ i, 0 ≤ Fib i := fun i => Real.sqrt_nonneg _
  set FibSum : ℝ := ∑ i ∈ Finset.range (N + 1), Fib i with hFibSum_def
  have hFibSum_nn : 0 ≤ FibSum := Finset.sum_nonneg fun i _ => hFib_nn i

  have hyK' : y ∈ chartImagePOUTsupport (I := I) (M := M) α := hyK

  have h_zc : ∀ i ∈ Finset.range (N + 1),
      tensorComponentAbsSum (I := I) (M := M) g r (s + i)
        (iteratedCovGrad (I := I) g r s i D) α y ≤ Cfibmax * Fib i := by
    intro i hi
    have hiN : i < N + 1 := Finset.mem_range.mp hi
    have hzc := hCfib i D hyK
    refine hzc.trans ?_
    rw [hFib_def, hb_def]
    exact mul_le_mul_of_nonneg_right
      (Finset.le_sup' Cfib (Finset.mem_range.mpr hiN)) (Real.sqrt_nonneg _)

  have h_each : ∀ q' : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      (∑ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g r s D α q'.1 q'.2) y‖) ≤
      (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum := by
    intro q'
    have h_per : ∀ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g r s D α q'.1 q'.2) y‖ ≤
          Cpeel * (Cfibmax * FibSum) := by
      intro m hm
      have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hpeel := hCpeel D m hmN 0 (by omega) q'.1 q'.2 y hyK'
      have h0eq : (iteratedCovGrad (I := I) g r s 0 D) = D :=
        DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero (I := I) g r s D
      rw [h0eq] at hpeel
      have hreindex : (∑ i ∈ Finset.range (m + 1),
            tensorComponentAbsSum (I := I) (M := M) g r (s + (0 + i))
              (iteratedCovGrad (I := I) g r s (0 + i) D) α y) =
          ∑ i ∈ Finset.range (m + 1),
            tensorComponentAbsSum (I := I) (M := M) g r (s + i)
              (iteratedCovGrad (I := I) g r s i D) α y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1 <;> rw [Nat.zero_add]
      rw [hreindex] at hpeel
      refine hpeel.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCpeel_nn

      calc (∑ i ∈ Finset.range (m + 1),
            tensorComponentAbsSum (I := I) (M := M) g r (s + i)
              (iteratedCovGrad (I := I) g r s i D) α y)
          ≤ ∑ i ∈ Finset.range (m + 1), Cfibmax * Fib i :=
            Finset.sum_le_sum (fun i hi => h_zc i
              (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi)
                (Nat.succ_le_succ hmN))))
        _ = Cfibmax * ∑ i ∈ Finset.range (m + 1), Fib i := by rw [Finset.mul_sum]
        _ ≤ Cfibmax * FibSum := by
            refine mul_le_mul_of_nonneg_left ?_ hCfibmax_nn
            rw [hFibSum_def]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (by omega)) (fun i _ _ => hFib_nn i)
    refine (Finset.sum_le_sum h_per).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

  calc bareChartJetContent (I := I) (M := M) g r s D α N y
      = ∑ q' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ m ∈ Finset.range (N + 1),
            ‖iteratedFDeriv ℝ m (tensorComponentEuclideanChart (I := I) (M := M) g r s D α q'.1 q'.2) y‖ := rfl
    _ ≤ ∑ _q' : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum :=
        Finset.sum_le_sum (fun q' _ => h_each q')
    _ = Npair * ((Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpair_def]
    _ = (Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax))) * FibSum := by ring

omit [BoundarylessManifold I M] in
lemma bareChartJetContent_le_sqrt_fiberNormSq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (D : SmoothCcTensor g r s) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {y : EuclN}, y ∈ chartPouKernel (I := I) (M := M) α →
        bareChartJetContent (I := I) (M := M) g r s D α N y ≤
          C * ∑ i ∈ Finset.range (N + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r (s + i)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((iteratedCovGrad (I := I) g r s i D).toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) := by
  obtain ⟨C, hC, h⟩ := bareJet_le_fiber (I := I) (M := M) g r s α N
  exact ⟨C, hC, h D⟩

end DifferentialGeometry.PDE.RicciFlow
