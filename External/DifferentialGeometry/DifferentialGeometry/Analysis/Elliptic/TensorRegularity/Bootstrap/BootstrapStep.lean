import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.InteriorRegularity.NirenbergH2
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Iteration
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density


noncomputable section

open Bundle Manifold Set Filter MeasureTheory Topology Function
open scoped Manifold Topology ContDiff BigOperators Matrix InnerProductSpace
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open DifferentialGeometry.Analysis.Sobolev.NirenbergIteration
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section ChartPerturbedSource

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem tensorComponent_perturbedSource_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (perturbedSource (d := Module.finrank ℝ E)
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target)
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
        l) := by
  classical
  have hu_cd : ContDiff ℝ ∞
      (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
    tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp
  have hf_cd : ContDiff ℝ ∞
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp
  set B := tensorPrincipalForm (I := I) (M := M) g α hK hK_target with hB_def
  set u := tensorComponentEuclid (I := I) (M := M) g r s T α P₀ with hu_def
  set f := tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀
    with hf_def
  unfold perturbedSource
  have h_dlf : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclN =>
      (fderiv ℝ f x) (EuclideanSpace.single l 1)) := by
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
      hf_cd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l (1 : ℝ))).contDiff.comp h_fderiv_smooth
  have h_dlc : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclN =>
      (fderiv ℝ B.c x) (EuclideanSpace.single l 1)) := by
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ B.c) :=
      B.smooth_c.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l (1 : ℝ))).contDiff.comp h_fderiv_smooth
  have h_dlc_u : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclN =>
      (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x) :=
    h_dlc.mul hu_cd
  refine (h_dlf.sub h_dlc_u).add ?_
  refine ContDiff.sum ?_
  intro i _
  refine ContDiff.sum ?_
  intro j _
  have h_dla : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ (fun z : EuclN => B.a z i j) y) (EuclideanSpace.single l 1)) := by
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fderiv ℝ (fun z : EuclN => B.a z i j)) :=
      (B.contDiff_a i j).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l (1 : ℝ))).contDiff.comp h_fderiv_smooth
  have h_diu : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
      hu_cd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single i (1 : ℝ))).contDiff.comp h_fderiv_smooth
  have h_prod : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ (fun z : EuclN => B.a z i j) y) (EuclideanSpace.single l 1) *
        (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    h_dla.mul h_diu
  have h_fderiv_prod : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun y : EuclN =>
      (fderiv ℝ (fun z : EuclN => B.a z i j) y) (EuclideanSpace.single l 1) *
        (fderiv ℝ u y) (EuclideanSpace.single i 1))) :=
    h_prod.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single j (1 : ℝ))).contDiff.comp h_fderiv_prod

theorem tensorComponent_partial_isSmoothWeakSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T F : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hF_supp : tsupport F.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    (hweak : ∀ v : SmoothCcTensor g r s,
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun)
    (l : Fin (Module.finrank ℝ E)) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
      (fun y : EuclN =>
        (fderiv ℝ (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y)
          (EuclideanSpace.single l 1))
      (perturbedSource (d := Module.finrank ℝ E)
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target)
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀)
        l) := by
  classical
  have h_base :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).IsSmoothWeakSolution
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀)
        (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponent_isSmoothWeakSolution (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp hT_K hweak
  have hf_cd : ContDiff ℝ (⊤ : ℕ∞)
      (tensorComponentWeakRHS (I := I) (M := M) g r s T F α hK hK_target P₀) :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp
  exact partial_smooth_weak_solution (d := Module.finrank ℝ E)
    (Ω := (Set.univ : Set EuclN)) isOpen_univ
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target)
    h_base hf_cd l

end ChartPerturbedSource

section GenericAdapter

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem memW1p_of_smooth_compactSupport_anyOpen
    {Ω : Set EE} (hΩ_open : IsOpen Ω)
    {ψ : EE → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ) {p : ℝ≥0∞} :
    DeGiorgi.MemW1p p ψ Ω := by
  classical
  refine ⟨(hψ_smooth.continuous.memLp_of_hasCompactSupport
    (μ := (volume : Measure EE)) hψ_cpt).restrict _, ?_⟩
  intro i
  refine ⟨fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1), ?_, ?_⟩
  · have h_cont : Continuous
        (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
      (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have h_cpt : HasCompactSupport
        (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
      hψ_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    exact (h_cont.memLp_of_hasCompactSupport
      (μ := (volume : Measure EE)) h_cpt).restrict _
  · exact DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ_open
      (hψ_smooth.of_le (by norm_cast))

omit [NeZero d] in
theorem memWkp_of_smooth_compactSupport_anyOpen
    {Ω : Set EE} (hΩ_open : IsOpen Ω)
    {ψ : EE → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ) {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ) :
    MemWkp (d := d) k p ψ Ω := by
  classical
  induction k generalizing ψ with
  | zero =>
      rw [MemWkp_zero]
      exact (hψ_smooth.continuous.memLp_of_hasCompactSupport
        (μ := (volume : Measure EE)) hψ_cpt).restrict _
  | succ k ih =>
      rw [MemWkp_succ]
      have hψ_W1p : DeGiorgi.MemW1p p ψ Ω :=
        memW1p_of_smooth_compactSupport_anyOpen (d := d) hΩ_open hψ_smooth hψ_cpt
      refine ⟨hψ_W1p, ?_⟩
      intro i
      have h_ae := chosenWeakPartial_smooth_ae_eq (d := d) hp hΩ_open hψ_smooth
        hψ_W1p i
      have h_classical_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        (hψ_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_classical_cpt : HasCompactSupport
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        hψ_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      have h_ih_classical := ih h_classical_smooth h_classical_cpt
      exact (MemWkp_congr_ae (d := d) hp hΩ_open h_ae).mpr h_ih_classical

omit [NeZero d] in
private theorem iterWeakPartial_smooth_ae_eq_iterClassical_anyOpen
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set EE} (hΩ_open : IsOpen Ω) :
    ∀ (j : ℕ) (β : Fin j → Fin d) {ψ : EE → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      iterWeakPartial (d := d) p j β ψ Ω
        =ᵐ[volume.restrict Ω] iterClassicalPartial (d := d) j β ψ := by
  intro j
  induction j with
  | zero =>
      intro β ψ _ _
      rw [iterWeakPartial_zero, iterClassicalPartial_zero]
  | succ j ih =>
      intro β ψ hψ_smooth hψ_cpt
      rw [iterWeakPartial_succ, iterClassicalPartial_succ]
      have hψ_W1p : DeGiorgi.MemW1p p ψ Ω :=
        memW1p_of_smooth_compactSupport_anyOpen (d := d) hΩ_open hψ_smooth hψ_cpt
      have h_ae := chosenWeakPartial_smooth_ae_eq (d := d) hp hΩ_open hψ_smooth
        hψ_W1p (β 0)
      have h_classical_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) :=
        (hψ_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_classical_cpt : HasCompactSupport
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) :=
        hψ_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (β 0) 1)
      have h_ih := ih (fun i : Fin j => β i.succ) h_classical_smooth h_classical_cpt
      have h_iter_congr := iterWeakPartial_ae_congr (d := d) hp hΩ_open j
        (fun i : Fin j => β i.succ) h_ae
      exact h_iter_congr.trans h_ih

omit [NeZero d] in

lemma hasCompactSupport_sq {h : EE → ℝ} (hh : HasCompactSupport h) :
    HasCompactSupport (fun x => h x ^ 2) := by
  have h_eq : (fun x => h x ^ 2) = h * h := by funext x; rw [Pi.mul_apply, sq]
  rw [h_eq]
  exact hh.mul_right

private lemma le_rpow_half_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

lemma rpow_half_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

omit [NeZero d] in

private lemma eLpNorm_two_sq_eq_ofReal_integral_sq
    {Ω : Set EE} {h : EE → ℝ}
    (hh_l2 : MemLp h 2 (volume.restrict Ω)) :
    (eLpNorm h 2 (volume.restrict Ω)) ^ 2 =
      ENNReal.ofReal (∫ x in Ω, h x ^ 2 ∂(volume : Measure EE)) := by
  classical
  have h_sq_lintegral :
      (eLpNorm h 2 (volume.restrict Ω)) ^ 2 =
        ∫⁻ x, (‖h x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume.restrict Ω) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
    rw [h2]
    have h_inner_eq : ∫⁻ x, (‖h x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(volume.restrict Ω) =
        ∫⁻ x, (‖h x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume.restrict Ω) := by
      refine lintegral_congr_ae ?_
      filter_upwards with x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [h_sq_lintegral]
  have h_pt : ∀ x : EE, (‖h x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (h x ^ 2) := by
    intro x
    rw [← Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [show h x ^ 2 = h x * h x from by ring, enorm_mul]
    rw [show (‖h x‖ₑ : ℝ≥0∞) ^ 2 = ‖h x‖ₑ * ‖h x‖ₑ from by ring]
  rw [lintegral_congr (fun x => h_pt x)]
  have h_sq_int : Integrable (fun x => h x ^ 2) (volume.restrict Ω) := by
    have := hh_l2.integrable_sq
    simpa [pow_two] using this
  have h_sq_nn : 0 ≤ᵐ[volume.restrict Ω] fun x => h x ^ 2 :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  exact (ofReal_integral_eq_lintegral_ofReal h_sq_int h_sq_nn).symm

theorem smooth_cc_h2_loc_memWkp_two
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE))
    {Ω'' : Set EE} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u f : EE → ℝ}, B.IsSmoothWeakSolution u f →
        HasCompactSupport u → ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      MemWkp (d := d) 2 2 u Ω'' ∧
        iteratedWeakSobolevNorm (d := d) 2 2 u Ω'' ≤
          ENNReal.ofReal
            (C * Real.sqrt
              ((∫ x, ∑ j : Fin d,
                  ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
                  ∂(volume : Measure EE)) +
                (∫ x, (u x) ^ 2 ∂(volume : Measure EE)) +
                (∫ x, (f x) ^ 2 ∂(volume : Measure EE)))) := by
  classical
  have h_room :
      Metric.cthickening 2 (closure Ω'') ⊆ (Set.univ : Set EE) :=
    fun y _ => Set.mem_univ y
  have h_closure_in :
      closure Ω'' ⊆ (Set.univ : Set EE) := fun y _ => Set.mem_univ y
  obtain ⟨C_engine, hC_engine_nn, h_engine⟩ :=
    loc_smooth_solution (d := d) B hΩ'' hΩ''_compact_closure
      h_closure_in h_room
  set C₀ : ℝ :=
    ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) * C_engine + 1
    with hC₀_def
  have hC₀_nn : 0 ≤ C₀ := by
    rw [hC₀_def]
    have : 0 ≤ ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ))
        * C_engine :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        hC_engine_nn
    linarith
  have h_one_le_C₀ : (1 : ℝ) ≤ C₀ := by
    rw [hC₀_def]
    have : 0 ≤ ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ))
        * C_engine :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        hC_engine_nn
    linarith
  have hC_engine_le_C₀ : C_engine ≤ C₀ := by
    rw [hC₀_def]
    have h_card_pos : (1 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) := by
      have := Fintype.card_pos (α := Fin d)
      exact_mod_cast this
    have h_le : C_engine ≤
        ((Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ)) * C_engine := by
      have h_one_le : (1 : ℝ) ≤
          (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) := by
        nlinarith [h_card_pos]
      nlinarith [h_one_le, hC_engine_nn]
    linarith
  set Nterms : ℕ := ∑ j ∈ Finset.range 3, (d ^ j : ℕ) with hN_def
  have hNterms_real_nn : (0 : ℝ) ≤ (Nterms : ℝ) := Nat.cast_nonneg _
  refine ⟨(Nterms : ℝ) * Real.sqrt C₀, by positivity, ?_⟩
  intro u f h_weak hu_cpt hf_cd hf_cpt
  have hu_cd : ContDiff ℝ (⊤ : ℕ∞) u := h_weak.1
  have hu_partial_smooth : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EE => (fderiv ℝ u y) (EuclideanSpace.single j 1)) := by
    intro j
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
      hu_cd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single j (1 : ℝ))).contDiff.comp h_fderiv_smooth
  have hu_partial_cpt : ∀ j : Fin d, HasCompactSupport
      (fun y : EE => (fderiv ℝ u y) (EuclideanSpace.single j 1)) := by
    intro j
    exact hu_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  set D : ℝ :=
    (∫ x, ∑ j : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
      ∂(volume : Measure EE)) +
    (∫ x, (u x) ^ 2 ∂(volume : Measure EE)) +
    (∫ x, (f x) ^ 2 ∂(volume : Measure EE)) with hD_def
  have hD_nn : 0 ≤ D := by
    have h1 : 0 ≤ ∫ x, ∑ j : Fin d,
        ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2 ∂(volume : Measure EE) :=
      integral_nonneg (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have h2 : 0 ≤ ∫ x, (u x) ^ 2 ∂(volume : Measure EE) :=
      integral_nonneg (fun x => sq_nonneg _)
    have h3 : 0 ≤ ∫ x, (f x) ^ 2 ∂(volume : Measure EE) :=
      integral_nonneg (fun x => sq_nonneg _)
    rw [hD_def]; positivity
  have hΩ''_meas : MeasurableSet Ω'' := hΩ''.measurableSet
  have h_memWkp : MemWkp (d := d) 2 2 u Ω'' :=
    memWkp_of_smooth_compactSupport_anyOpen (d := d) hΩ'' hu_cd hu_cpt
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) 2
  refine ⟨h_memWkp, ?_⟩
  have hf_l2_loc : ∀ {Ω' : Set EE}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω') := by
    intro Ω' _
    exact (hf_cd.continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure EE)) (p := 2) hf_cpt).restrict _
  have h_engine_inst := h_engine h_weak hf_l2_loc
  have h_engine_bound : ∀ i k : Fin d,
      ∫ x in Ω'',
          ((fderiv ℝ (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1)) x)
            (EuclideanSpace.single k 1)) ^ 2 ∂(volume : Measure EE) ≤
        C_engine * D := by
    intro i k
    obtain ⟨g_ik, hg_memLp, hg_weak, Ω', _hΩ'_open, _hΩ''_in_Ω', _hΩ'_in,
      _hΩ'_compact, hC_bound⟩ := h_engine_inst i k
    have h_classical_weak :
        DeGiorgi.HasWeakPartialDeriv (d := d) k
          (fun y : EE => (fderiv ℝ
            (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
            (EuclideanSpace.single k 1))
          (fun y : EE => (fderiv ℝ u y) (EuclideanSpace.single i 1)) Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ''
        ((hu_partial_smooth i).of_le (by norm_cast))
    have hg_loc : LocallyIntegrable g_ik (volume.restrict Ω'') :=
      hg_memLp.locallyIntegrable (by norm_num)
    have h_classical_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : EE => (fderiv ℝ
          (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
          (EuclideanSpace.single k 1)) := by
      have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fderiv ℝ (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1))) :=
        (hu_partial_smooth i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      exact (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single k (1 : ℝ))).contDiff.comp h_fderiv_smooth
    have h_classical_loc : LocallyIntegrable
        (fun y : EE => (fderiv ℝ
          (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
          (EuclideanSpace.single k 1)) (volume.restrict Ω'') :=
      h_classical_smooth.continuous.locallyIntegrable.mono_measure
        Measure.restrict_le_self
    have h_ae : g_ik =ᵐ[volume.restrict Ω'']
        (fun y : EE => (fderiv ℝ
          (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y)
          (EuclideanSpace.single k 1)) :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ'' hg_weak h_classical_weak
        hg_loc h_classical_loc
    have h_sq_ae : (fun x => g_ik x ^ 2) =ᵐ[volume.restrict Ω'']
        (fun x => ((fderiv ℝ
          (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1)) x)
          (EuclideanSpace.single k 1)) ^ 2) := by
      filter_upwards [h_ae] with x hx
      rw [hx]
    have h_int_eq :
        ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EE) =
          ∫ x in Ω'',
            ((fderiv ℝ
              (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single i 1)) x)
              (EuclideanSpace.single k 1)) ^ 2 ∂(volume : Measure EE) :=
      integral_congr_ae h_sq_ae
    have h_data_le :
        (∫ x in Ω',
            ∑ j : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure EE)) +
          (∫ x in Ω', (u x) ^ 2 ∂(volume : Measure EE)) +
          (∫ x in Ω', (f x) ^ 2 ∂(volume : Measure EE)) ≤ D := by
      have h_grad_int : Integrable
          (fun x => ∑ j : Fin d,
            ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2)
          (volume : Measure EE) := by
        refine integrable_finset_sum Finset.univ (fun j _ => ?_)
        have h_cont : Continuous
            (fun x => ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2) :=
          ((hu_partial_smooth j).continuous).pow 2
        have h_cpt : HasCompactSupport
            (fun x => ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2) :=
          hasCompactSupport_sq (d := d) (hu_partial_cpt j)
        exact h_cont.integrable_of_hasCompactSupport h_cpt
      have h_u_int : Integrable (fun x => (u x) ^ 2) (volume : Measure EE) :=
        (hu_cd.continuous.pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (d := d) hu_cpt)
      have h_f_int : Integrable (fun x => (f x) ^ 2) (volume : Measure EE) :=
        (hf_cd.continuous.pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (d := d) hf_cpt)
      have h_grad_le :
          ∫ x in Ω', ∑ j : Fin d,
              ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) ≤
          ∫ x, ∑ j : Fin d,
              ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) :=
        setIntegral_le_integral h_grad_int
          (Filter.Eventually.of_forall
            (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      have h_u_le :
          ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure EE) ≤
          ∫ x, (u x) ^ 2 ∂(volume : Measure EE) :=
        setIntegral_le_integral h_u_int
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      have h_f_le :
          ∫ x in Ω', (f x) ^ 2 ∂(volume : Measure EE) ≤
          ∫ x, (f x) ^ 2 ∂(volume : Measure EE) :=
        setIntegral_le_integral h_f_int
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      rw [hD_def]
      exact add_le_add (add_le_add h_grad_le h_u_le) h_f_le
    have hC_bound' :
        ∫ x in Ω'', g_ik x ^ 2 ∂(volume : Measure EE) ≤ C_engine * D := by
      refine hC_bound.trans ?_
      exact mul_le_mul_of_nonneg_left h_data_le hC_engine_nn
    rw [← h_int_eq]
    exact hC_bound'
  have h_iter_classical_bound : ∀ (j : ℕ), j ≤ 2 → ∀ β : Fin j → Fin d,
      ∫ x in Ω'', (iterClassicalPartial (d := d) j β u x) ^ 2
        ∂(volume : Measure EE) ≤ C₀ * D := by
    intro j hj β
    have h_iter_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (iterClassicalPartial (d := d) j β u) :=
      contDiff_iterClassicalPartial (d := d) j β hu_cd
    have h_iter_cpt : HasCompactSupport (iterClassicalPartial (d := d) j β u) :=
      hasCompactSupport_iterClassicalPartial (d := d) j β hu_cpt
    interval_cases j
    · have h_eq : iterClassicalPartial (d := d) 0 β u = u := by
        simp [iterClassicalPartial_zero]
      rw [h_eq]
      have h_u_int : Integrable (fun x => (u x) ^ 2) (volume : Measure EE) :=
        (hu_cd.continuous.pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (d := d) hu_cpt)
      have h_le : ∫ x in Ω'', (u x) ^ 2 ∂(volume : Measure EE) ≤
          ∫ x, (u x) ^ 2 ∂(volume : Measure EE) :=
        setIntegral_le_integral h_u_int
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      have h_le_D : ∫ x, (u x) ^ 2 ∂(volume : Measure EE) ≤ D := by
        have h1 : 0 ≤ ∫ x, ∑ j : Fin d,
            ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) :=
          integral_nonneg (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _))
        have h3 : 0 ≤ ∫ x, (f x) ^ 2 ∂(volume : Measure EE) :=
          integral_nonneg (fun x => sq_nonneg _)
        rw [hD_def]; linarith
      calc ∫ x in Ω'', (u x) ^ 2 ∂(volume : Measure EE)
          ≤ ∫ x, (u x) ^ 2 ∂(volume : Measure EE) := h_le
        _ ≤ D := h_le_D
        _ = 1 * D := (one_mul D).symm
        _ ≤ C₀ * D := mul_le_mul_of_nonneg_right h_one_le_C₀ hD_nn
    · have h_eq : iterClassicalPartial (d := d) 1 β u =
          (fun x => (fderiv ℝ u x) (EuclideanSpace.single (β 0) 1)) := by
        rw [iterClassicalPartial_succ]
        simp [iterClassicalPartial_zero]
      rw [h_eq]
      have h_ptwise : ∀ x : EE,
          ((fderiv ℝ u x) (EuclideanSpace.single (β 0) 1)) ^ 2 ≤
          ∑ j : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2 :=
        fun x => Finset.single_le_sum
          (f := fun j => ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ (β 0))
      have h_grad_int : Integrable
          (fun x => ∑ j : Fin d,
            ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2)
          (volume : Measure EE) := by
        refine integrable_finset_sum Finset.univ (fun j _ => ?_)
        exact (((hu_partial_smooth j).continuous).pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (d := d) (hu_partial_cpt j))
      have h_partial_sq_int : Integrable
          (fun x => ((fderiv ℝ u x) (EuclideanSpace.single (β 0) 1)) ^ 2)
          (volume : Measure EE) :=
        (((hu_partial_smooth (β 0)).continuous).pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (d := d) (hu_partial_cpt (β 0)))
      have h_step1 :
          ∫ x in Ω'', ((fderiv ℝ u x) (EuclideanSpace.single (β 0) 1)) ^ 2
            ∂(volume : Measure EE) ≤
          ∫ x in Ω'', ∑ j : Fin d,
              ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) := by
        refine setIntegral_mono_on h_partial_sq_int.restrict h_grad_int.restrict
          hΩ''_meas ?_
        intro x _
        exact h_ptwise x
      have h_step2 :
          ∫ x in Ω'', ∑ j : Fin d,
              ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) ≤
          ∫ x, ∑ j : Fin d,
              ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) :=
        setIntegral_le_integral h_grad_int
          (Filter.Eventually.of_forall
            (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      have h_le_D : ∫ x, ∑ j : Fin d,
          ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure EE) ≤ D := by
        have h2 : 0 ≤ ∫ x, (u x) ^ 2 ∂(volume : Measure EE) :=
          integral_nonneg (fun x => sq_nonneg _)
        have h3 : 0 ≤ ∫ x, (f x) ^ 2 ∂(volume : Measure EE) :=
          integral_nonneg (fun x => sq_nonneg _)
        rw [hD_def]; linarith
      calc ∫ x in Ω'', ((fderiv ℝ u x) (EuclideanSpace.single (β 0) 1)) ^ 2
              ∂(volume : Measure EE)
          ≤ ∫ x in Ω'', ∑ j : Fin d,
              ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) := h_step1
        _ ≤ ∫ x, ∑ j : Fin d,
              ((fderiv ℝ u x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE) := h_step2
        _ ≤ D := h_le_D
        _ = 1 * D := (one_mul D).symm
        _ ≤ C₀ * D := mul_le_mul_of_nonneg_right h_one_le_C₀ hD_nn
    · have h_eq : iterClassicalPartial (d := d) 2 β u =
          (fun x => (fderiv ℝ
            (fun z : EE => (fderiv ℝ u z) (EuclideanSpace.single (β 0) 1)) x)
            (EuclideanSpace.single (β 1) 1)) := by
        rw [iterClassicalPartial_succ, iterClassicalPartial_succ]
        simp [iterClassicalPartial_zero]
      rw [h_eq]
      have h_engine_term := h_engine_bound (β 0) (β 1)
      have h_pair_le :
          C_engine * D ≤ C₀ * D :=
        mul_le_mul_of_nonneg_right hC_engine_le_C₀ hD_nn
      exact h_engine_term.trans h_pair_le
  have hΩ''_open := hΩ''
  have h_iterWeak_ae : ∀ (j : ℕ) (β : Fin j → Fin d),
      iterWeakPartial (d := d) 2 j β u Ω''
        =ᵐ[volume.restrict Ω''] iterClassicalPartial (d := d) j β u :=
    fun j β => iterWeakPartial_smooth_ae_eq_iterClassical_anyOpen (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open j β hu_cd hu_cpt
  have h_term_bound : ∀ (j : ℕ), j ∈ Finset.range 3 → ∀ β : Fin j → Fin d,
      eLpNorm (iterWeakPartial (d := d) 2 j β u Ω'') 2 (volume.restrict Ω'') ≤
        ENNReal.ofReal (Real.sqrt (C₀ * D)) := by
    intro j hj β
    have hj_le : j ≤ 2 := by rw [Finset.mem_range] at hj; omega
    have h_ae := h_iterWeak_ae j β
    rw [eLpNorm_congr_ae h_ae]
    have h_iter_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (iterClassicalPartial (d := d) j β u) :=
      contDiff_iterClassicalPartial (d := d) j β hu_cd
    have h_iter_cpt : HasCompactSupport (iterClassicalPartial (d := d) j β u) :=
      hasCompactSupport_iterClassicalPartial (d := d) j β hu_cpt
    have h_iter_l2 : MemLp (iterClassicalPartial (d := d) j β u) 2
        (volume.restrict Ω'') :=
      (h_iter_smooth.continuous.memLp_of_hasCompactSupport
        (μ := (volume : Measure EE)) (p := 2) h_iter_cpt).restrict _
    have h_sq_eq := eLpNorm_two_sq_eq_ofReal_integral_sq (d := d)
      (Ω := Ω'') (h := iterClassicalPartial (d := d) j β u) h_iter_l2
    have h_int_le := h_iter_classical_bound j hj_le β
    have h_sq_le : (eLpNorm (iterClassicalPartial (d := d) j β u) 2
        (volume.restrict Ω'')) ^ 2 ≤ ENNReal.ofReal (C₀ * D) := by
      rw [h_sq_eq]
      exact ENNReal.ofReal_le_ofReal h_int_le
    have h_le_rpow := le_rpow_half_of_sq_le h_sq_le
    rwa [rpow_half_ofReal_eq_ofReal_sqrt (by positivity)] at h_le_rpow
  have h_wkp_le :
      iteratedWeakSobolevNorm (d := d) 2 2 u Ω'' ≤
        ∑ j ∈ Finset.range 3, ∑ _β : Fin j → Fin d,
          ENNReal.ofReal (Real.sqrt (C₀ * D)) := by
    rw [wkpNorm_eq_sum]
    refine Finset.sum_le_sum ?_
    intro j hj
    refine Finset.sum_le_sum ?_
    intro β _
    exact h_term_bound j hj β
  have h_const_sum :
      ∑ j ∈ Finset.range 3, ∑ _β : Fin j → Fin d,
        ENNReal.ofReal (Real.sqrt (C₀ * D)) =
      (Nterms : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (C₀ * D)) := by
    rw [hN_def, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
  refine h_wkp_le.trans ?_
  rw [h_const_sum, ← ENNReal.ofReal_natCast Nterms,
    ← ENNReal.ofReal_mul hNterms_real_nn]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.sqrt_mul hC₀_nn]
  exact le_of_eq (by ring)

end GenericAdapter

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
