import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciDrift
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Connection.ChartBridge.HessFrobenius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.Geometry

set_option autoImplicit false










namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [IsManifold I 1 M] in
private theorem weighted_int [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {f q : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (hq : Continuous q) :
    Integrable q
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) f) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity f x)) μ :=
    (ENNReal.continuous_ofReal.comp
      (expNegPotentialDensity_contMDiff (I := I) hf).continuous).aemeasurable
  have hfinite :
      ∀ᵐ x ∂μ, ENNReal.ofReal (expNegPotentialDensity f x) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [expNegPotentialWeightedMeasure]
  apply (integrable_withDensity_iff_integrable_smul₀' hmeas hfinite).2
  have hbase : Integrable
      (fun x : M => expNegPotentialDensity f x * q x) μ := by
    exact ((expNegPotentialDensity_contMDiff (I := I) hf).continuous.mul hq)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simpa only [expNegPotentialDensity,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul] using hbase

private theorem int7_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f0 f1 f2 f3 f4 f5 f6 : X -> Real}
    (h0I : Integrable f0 μ) (h1I : Integrable f1 μ)
    (h2I : Integrable f2 μ) (h3I : Integrable f3 μ)
    (h4I : Integrable f4 μ) (h5I : Integrable f5 μ)
    (h6I : Integrable f6 μ)
    (h0 : (∫ x, f0 x ∂μ) = 0) (h1 : (∫ x, f1 x ∂μ) = 0)
    (h2 : (∫ x, f2 x ∂μ) = 0) (h3 : (∫ x, f3 x ∂μ) = 0)
    (h4 : (∫ x, f4 x ∂μ) = 0) (h5 : (∫ x, f5 x ∂μ) = 0)
    (h6 : (∫ x, f6 x ∂μ) = 0)
    (c0 c1 c2 c3 c4 c5 c6 : Real) :
    (∫ x,
        ((((((c0 * f0 x + c1 * f1 x) + c2 * f2 x) + c3 * f3 x) +
          c4 * f4 x) + c5 * f5 x) + c6 * f6 x)
      ∂μ) = 0 := by
  let g0 : X -> Real := fun x => c0 * f0 x
  let g1 : X -> Real := fun x => c1 * f1 x
  let g2 : X -> Real := fun x => c2 * f2 x
  let g3 : X -> Real := fun x => c3 * f3 x
  let g4 : X -> Real := fun x => c4 * f4 x
  let g5 : X -> Real := fun x => c5 * f5 x
  let g6 : X -> Real := fun x => c6 * f6 x
  have hc0I : Integrable g0 μ := by simpa only [g0] using h0I.const_mul c0
  have hc1I : Integrable g1 μ := by simpa only [g1] using h1I.const_mul c1
  have hc2I : Integrable g2 μ := by simpa only [g2] using h2I.const_mul c2
  have hc3I : Integrable g3 μ := by simpa only [g3] using h3I.const_mul c3
  have hc4I : Integrable g4 μ := by simpa only [g4] using h4I.const_mul c4
  have hc5I : Integrable g5 μ := by simpa only [g5] using h5I.const_mul c5
  have hc6I : Integrable g6 μ := by simpa only [g6] using h6I.const_mul c6
  have hg0 : (∫ x, g0 x ∂μ) = 0 := by
    dsimp only [g0]
    rw [integral_const_mul, h0]
    ring
  have hg1 : (∫ x, g1 x ∂μ) = 0 := by
    dsimp only [g1]
    rw [integral_const_mul, h1]
    ring
  have hg2 : (∫ x, g2 x ∂μ) = 0 := by
    dsimp only [g2]
    rw [integral_const_mul, h2]
    ring
  have hg3 : (∫ x, g3 x ∂μ) = 0 := by
    dsimp only [g3]
    rw [integral_const_mul, h3]
    ring
  have hg4 : (∫ x, g4 x ∂μ) = 0 := by
    dsimp only [g4]
    rw [integral_const_mul, h4]
    ring
  have hg5 : (∫ x, g5 x ∂μ) = 0 := by
    dsimp only [g5]
    rw [integral_const_mul, h5]
    ring
  have hg6 : (∫ x, g6 x ∂μ) = 0 := by
    dsimp only [g6]
    rw [integral_const_mul, h6]
    ring
  have hadd0 (u v : X -> Real) (huI : Integrable u μ) (hvI : Integrable v μ)
      (hu : (∫ x, u x ∂μ) = 0) (hv : (∫ x, v x ∂μ) = 0) :
      (∫ x, (u + v) x ∂μ) = 0 := by
    calc
      (∫ x, (u + v) x ∂μ) = (∫ x, u x ∂μ) + ∫ x, v x ∂μ := by
        simpa only [Pi.add_apply] using integral_add huI hvI
      _ = 0 := by rw [hu, hv]; ring
  have hg01 : (∫ x, (g0 + g1) x ∂μ) = 0 := hadd0 g0 g1 hc0I hc1I hg0 hg1
  have hg012 : (∫ x, ((g0 + g1) + g2) x ∂μ) = 0 :=
    hadd0 (g0 + g1) g2 (hc0I.add hc1I) hc2I hg01 hg2
  have hg0123 : (∫ x, (((g0 + g1) + g2) + g3) x ∂μ) = 0 :=
    hadd0 ((g0 + g1) + g2) g3 ((hc0I.add hc1I).add hc2I) hc3I hg012 hg3
  have hg01234 : (∫ x, ((((g0 + g1) + g2) + g3) + g4) x ∂μ) = 0 :=
    hadd0 (((g0 + g1) + g2) + g3) g4
      (((hc0I.add hc1I).add hc2I).add hc3I) hc4I hg0123 hg4
  have hg012345 : (∫ x, (((((g0 + g1) + g2) + g3) + g4) + g5) x ∂μ) = 0 :=
    hadd0 ((((g0 + g1) + g2) + g3) + g4) g5
      ((((hc0I.add hc1I).add hc2I).add hc3I).add hc4I) hc5I hg01234 hg5
  have hall : (∫ x, ((((((g0 + g1) + g2) + g3) + g4) + g5) + g6) x ∂μ) = 0 :=
    hadd0 (((((g0 + g1) + g2) + g3) + g4) + g5) g6
      (((((hc0I.add hc1I).add hc2I).add hc3I).add hc4I).add hc5I) hc6I
      hg012345 hg6
  simpa only [g0, g1, g2, g3, g4, g5, g6, Pi.add_apply] using hall

omit [SigmaCompactSpace M] [T2Space M] in
private theorem norm_sq_shift
    (g : SmoothRiemannianMetric I M) {x : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x)
    (a r l : Real)
    (hA : metricTracePair0SAt (I := I) g A = r)
    (hB : metricTracePair0SAt (I := I) g B = l) :
    normSq0S (I := I) g x 2
        (A + B - a • metricTensor0S (I := I) g x) =
      normSq0S (I := I) g x 2 A +
        normSq0S (I := I) g x 2 B +
        2 * inner02 (I := I) g x A B -
        2 * a * (r + l) + a ^ 2 * (Module.finrank Real E : Real) := by
  classical
  let D := tensor0SMetricData (I := I) g x 2
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  have hmetric :
      normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) =
        (Module.finrank Real E : Real) := by
    simpa using normSq0S_metricTensor0S_eq_card (I := I) g basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv
  have hBA : inner0S (I := I) g x 2 B A = inner02 (I := I) g x A B := by
    rw [inner0S_symm (I := I) g x B A]
    rfl
  have hAg :
      inner0S (I := I) g x 2 A (metricTensor0S (I := I) g x) = r := by
    rw [inner0S_symm (I := I) g x A (metricTensor0S (I := I) g x)]
    exact hA
  have hBg :
      inner0S (I := I) g x 2 B (metricTensor0S (I := I) g x) = l := by
    rw [inner0S_symm (I := I) g x B (metricTensor0S (I := I) g x)]
    exact hB
  rw [normSq0S_eq_inner]
  change D.inner
      (A + B - a • metricTensor0S (I := I) g x)
      (A + B - a • metricTensor0S (I := I) g x) = _
  unfold MetricFiberData.inner
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  change
    inner0S (I := I) g x 2 A A + inner0S (I := I) g x 2 B A -
          a * inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) A +
        (inner0S (I := I) g x 2 A B + inner0S (I := I) g x 2 B B -
          a * inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) B) -
      a *
        (inner0S (I := I) g x 2 A (metricTensor0S (I := I) g x) +
          inner0S (I := I) g x 2 B (metricTensor0S (I := I) g x) -
          a * inner0S (I := I) g x 2
            (metricTensor0S (I := I) g x) (metricTensor0S (I := I) g x)) = _
  rw [hBA, hAg, hBg]
  rw [show inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) A = r from hA]
  rw [show inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) B = l from hB]
  rw [show inner0S (I := I) g x 2 A B = inner02 (I := I) g x A B from rfl]
  rw [← normSq0S_eq_inner, ← normSq0S_eq_inner, ← normSq0S_eq_inner, hmetric]
  ring



theorem weighted_hess_split [I.Boundaryless] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ∫ x,
        (inner02 (I := I) g x (metricRicciAt (I := I) (M := M) g x)
              (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                (metricCov_smooth (I := I) (M := M) g) f hf x) -
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (grad_g (I := I) g hf x)
              (grad_g (I := I) g hf x)) -
          (1 / 2 : Real) * metricScalarAt (I := I) (M := M) g x *
            (Δ_g (I := I) g hf x -
              g.inner x (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x)))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) f) = 0 := by
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity f x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (ENNReal.continuous_ofReal.comp
      (expNegPotentialDensity_contMDiff (I := I) hf).continuous).aemeasurable
  exact weightedDivZero_of_connTrace (I := I) g hf
    (ricDriftVec (I := I) g hf) hmeas
    (fun x => ricDriftDiv (I := I) g hf x)
    (fun x => ricDriftAct (I := I) g hf x)
    (fun x => by ring)



theorem weighted_bochner [I.Boundaryless] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ∫ x,
        (normSq0S (I := I) g x 2
              (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                (metricCov_smooth (I := I) (M := M) g) f hf x) +
          metricRicciAt (I := I) (M := M) g x
            (vec2 (I := I) (grad_g (I := I) g hf x)
              (grad_g (I := I) g hf x)) -
          (Δ_g (I := I) g hf x -
              g.inner x (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x)) ^ 2 -
          (1 / 2 : Real) *
            g.inner x (grad_g (I := I) g hf x)
              (grad_g (I := I) g hf x) *
            (Δ_g (I := I) g hf x -
              g.inner x (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x)))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) f) = 0 := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => by
      have htang : Module.finrank Real (TangentSpace I x) = 0 := hdim
      letI : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.mp htang
      have hgrad : grad_g (I := I) g hf x = 0 := Subsingleton.elim _ _
      let basis := Module.finBasis Real (TangentSpace I x)
      let gInv : Fin (Module.finrank Real (TangentSpace I x)) ->
          Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun _ _ => 0
      have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
        intro i _
        have hi : i.val < 0 := by simpa only [htang] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      have hunivT :
          (Finset.univ : Finset (Fin (Module.finrank Real (TangentSpace I x)))) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i _
        have hi : i.val < 0 := by simpa only [htang] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      have hHessNorm :
          normSq0S (I := I) g x 2
              (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                (metricCov_smooth (I := I) (M := M) g) f hf x) = 0 := by
        rw [normSq0S_two_eq_coord (I := I) g x basis gInv hinv]
        rw [hunivT]
        simp
      have hunivE :
          (Finset.univ : Finset (Fin (Module.finrank Real E))) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i _
        have hi : i.val < 0 := by simpa only [hdim] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      have hLap : Δ_g (I := I) g hf x = 0 := by
        rw [Δ_g_def, divergence_g_def, localDivergence_def, hunivE]
        simp
      have hRic :
          metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0 := by
        exact (metricRicciAt (I := I) (M := M) g x).map_coord_zero
          (i := 0) (by simp [vec2])
      have hinner :
          g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        rw [(g.inner x).map_zero, ContinuousLinearMap.zero_apply]
      change
        normSq0S (I := I) g x 2
              (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                (metricCov_smooth (I := I) (M := M) g) f hf x) +
            metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x)) -
            (Δ_g (I := I) g hf x -
                g.inner x (grad_g (I := I) g hf x)
                  (grad_g (I := I) g hf x)) ^ 2 -
            (1 / 2 : Real) *
              g.inner x (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x) *
              (Δ_g (I := I) g hf x -
                g.inner x (grad_g (I := I) g hf x)
                  (grad_g (I := I) g hf x)) = 0
      rw [hgrad, hHessNorm, hLap, hRic, hinner]
      ring
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    let q : M -> Real := fun x =>
      g.inner x (grad_g (I := I) g hf x) (grad_g (I := I) g hf x)
    have hq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) q := by
      simpa only [q, grad_g_apply] using
        (normGradSqFun_contMDiff (I := I) g hf)
    let L : M -> Real := Δ_g (I := I) g hf
    have hL : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) L := by
      simpa only [L] using Δ_g_contMDiff (I := I) g hf
    let z : M -> Real := fun x => L x - q x
    have hz : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) z := by
      exact hL.sub hq
    let cross : M -> Real := fun x =>
      g.inner x (grad_g (I := I) g hL x) (grad_g (I := I) g hf x)
    have hcross : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) cross := by
      simpa only [cross] using
        (contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
          (grad_g (I := I) g hL) (grad_g (I := I) g hf))
    let A0 : M -> Real := fun x =>
      (1 / 2 : Real) * (Δ_g (I := I) g hq x + q x * z x)
    let A1 : M -> Real := fun x => Δ_g (I := I) g hL x - cross x
    let A2 : M -> Real := fun x => Δ_g (I := I) g hL x + L x * z x
    have hA0 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) A0 := by
      exact contMDiff_const.mul
        ((Δ_g_contMDiff (I := I) g hq).add (hq.mul hz))
    have hA1 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) A1 := by
      exact (Δ_g_contMDiff (I := I) g hL).sub hcross
    have hA2 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) A2 := by
      exact (Δ_g_contMDiff (I := I) g hL).add (hL.mul hz)
    let μw := expNegPotentialWeightedMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) f
    have hmeas :
        AEMeasurable
          (fun x : M => ENNReal.ofReal (expNegPotentialDensity f x))
          (riemannianVolumeMeasure (I := I) (M := M) g) :=
      (ENNReal.continuous_ofReal.comp
        (expNegPotentialDensity_contMDiff (I := I) hf).continuous).aemeasurable
    have hDqI : Integrable (fun x : M => Δ_g (I := I) g hq x) μw :=
      weighted_int (I := I) g hf (Δ_g_contMDiff (I := I) g hq).continuous
    have hqzI : Integrable (fun x : M => q x * z x) μw :=
      weighted_int (I := I) g hf (hq.mul hz).continuous
    have hDLI : Integrable (fun x : M => Δ_g (I := I) g hL x) μw :=
      weighted_int (I := I) g hf (Δ_g_contMDiff (I := I) g hL).continuous
    have hLzI : Integrable (fun x : M => L x * z x) μw :=
      weighted_int (I := I) g hf (hL.mul hz).continuous
    have hA0I : Integrable A0 μw := weighted_int (I := I) g hf hA0.continuous
    have hA1I : Integrable A1 μw := weighted_int (I := I) g hf hA1.continuous
    have hA2I : Integrable A2 μw := weighted_int (I := I) g hf hA2.continuous
    have hqGreen := weightedGreen (I := I) g hf hq hmeas
    have hqRight :
        (∫ x, q x * (-Δ_g (I := I) g hf x + q x) ∂μw) =
          -(∫ x, q x * z x ∂μw) := by
      calc
        (∫ x, q x * (-Δ_g (I := I) g hf x + q x) ∂μw) =
            ∫ x, -(q x * z x) ∂μw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp only [z, L]
            ring
        _ = -(∫ x, q x * z x ∂μw) := by rw [integral_neg]
    have hA0zero : (∫ x, A0 x ∂μw) = 0 := by
      have hraw :
          (∫ x, Δ_g (I := I) g hq x + q x * z x ∂μw) = 0 := by
        rw [integral_add hDqI hqzI, hqGreen, hqRight]
        ring
      dsimp only [A0]
      rw [integral_const_mul, hraw]
      ring
    have hA1zero : (∫ x, A1 x ∂μw) = 0 := by
      simpa only [A1, cross, L, μw] using
        (weighted_grad_zero (I := I) g hf hL)
    have hLGreen := weightedGreen (I := I) g hf hL hmeas
    have hLRight :
        (∫ x, L x * (-Δ_g (I := I) g hf x + q x) ∂μw) =
          -(∫ x, L x * z x ∂μw) := by
      calc
        (∫ x, L x * (-Δ_g (I := I) g hf x + q x) ∂μw) =
            ∫ x, -(L x * z x) ∂μw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp only [z, L]
            ring
        _ = -(∫ x, L x * z x ∂μw) := by rw [integral_neg]
    have hA2zero : (∫ x, A2 x ∂μw) = 0 := by
      dsimp only [A2]
      rw [integral_add hDLI hLzI, hLGreen, hLRight]
      ring
    have hpoint : ∀ x : M,
        normSq0S (I := I) g x 2
              (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                (metricCov_smooth (I := I) (M := M) g) f hf x) +
            metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x)) -
            (Δ_g (I := I) g hf x - q x) ^ 2 -
            (1 / 2 : Real) * q x * (Δ_g (I := I) g hf x - q x) =
          A0 x + A1 x - A2 x := by
      intro x
      have hHess :
          normSq0S (I := I) g x 2
              (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                (metricCov_smooth (I := I) (M := M) g) f hf x) =
            chartHessFrobeniusSq (I := I) g f x := by
        simpa only [leviHessSec, metricCov] using
          (hessSec_normSq (I := I) g hf x)
      have hRic :
          metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x)) =
            ricciTensor (I := I) g x
              (gradFun (I := I) g f x) (gradFun (I := I) g f x) := by
        simpa only [grad_g_apply] using
          (metricRicciAt_apply_eq_ricciTensor (I := I) g x
            (grad_g (I := I) g hf x) (grad_g (I := I) g hf x))
      have hsymm :
          g.inner x (gradFun (I := I) g f x)
              (gradFun (I := I) g L x) = cross x := by
        dsimp only [cross]
        rw [grad_g_apply, grad_g_apply]
        exact g.symm x _ _
      have hB := bochner_pointwise_concrete_metric_unconditional (I := I) g hf x
      rw [← hHess, ← hRic, hsymm] at hB
      have hB' :
          Δ_g (I := I) g hq x =
            2 * normSq0S (I := I) g x 2
                (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                  (metricCov_smooth (I := I) (M := M) g) f hf x) +
              2 * metricRicciAt (I := I) (M := M) g x
                (vec2 (I := I) (grad_g (I := I) g hf x)
                  (grad_g (I := I) g hf x)) +
              2 * cross x := by
        simpa only [q, L, normGradSqFun, grad_g_apply] using hB
      have hHR :
          normSq0S (I := I) g x 2
                (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                  (metricCov_smooth (I := I) (M := M) g) f hf x) +
              metricRicciAt (I := I) (M := M) g x
                (vec2 (I := I) (grad_g (I := I) g hf x)
                  (grad_g (I := I) g hf x)) =
            (1 / 2 : Real) * Δ_g (I := I) g hq x - cross x := by
        linarith [hB']
      rw [hHR]
      dsimp only [A0, A1, A2, z, L]
      ring
    calc
      (∫ x,
          (normSq0S (I := I) g x 2
                (hessianSec (I := I) (metricCov (I := I) (M := M) g)
                  (metricCov_smooth (I := I) (M := M) g) f hf x) +
            metricRicciAt (I := I) (M := M) g x
              (vec2 (I := I) (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x)) -
            (Δ_g (I := I) g hf x -
                g.inner x (grad_g (I := I) g hf x)
                  (grad_g (I := I) g hf x)) ^ 2 -
            (1 / 2 : Real) *
              g.inner x (grad_g (I := I) g hf x)
                (grad_g (I := I) g hf x) *
              (Δ_g (I := I) g hf x -
                g.inner x (grad_g (I := I) g hf x)
                  (grad_g (I := I) g hf x))) ∂μw) =
          ∫ x, A0 x + A1 x - A2 x ∂μw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simpa only [q] using hpoint x
      _ = ∫ x, ((A0 + A1) - A2) x ∂μw := by rfl
      _ = (∫ x, (A0 + A1) x ∂μw) - (∫ x, A2 x ∂μw) := by
        exact integral_sub (hA0I.add hA1I) hA2I
      _ = (∫ x, A0 x ∂μw) + (∫ x, A1 x ∂μw) - (∫ x, A2 x ∂μw) := by
        have hadd :
            (∫ x, (A0 + A1) x ∂μw) =
              (∫ x, A0 x ∂μw) + (∫ x, A1 x ∂μw) :=
          integral_add hA0I hA1I
        exact congrArg (fun r : Real => r - ∫ x, A2 x ∂μw) hadd
      _ = 0 := by rw [hA0zero, hA1zero, hA2zero]; ring



theorem weighted_w_square [I.Boundaryless] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {f : M -> Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    {s : Real} (hs : 0 < s) :
    let n := Module.finrank Real E
    let R : M -> Real := metricScalarAt (I := I) (M := M) g
    let q : M -> Real := fun x =>
      g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x)
    let L : M -> Real := Δ_g (I := I) g hf
    let z : M -> Real := fun x => L x - q x
    let ft : M -> Real := fun x => z x + R x - (n : Real) / (2 * s)
    let Rt : M -> Real := fun x =>
      -(Δ_g (I := I) g (metricScalar_smooth (I := I) (M := M) g) x +
        2 * normSq0S (I := I) g x 2 (metricRicciAt (I := I) (M := M) g x))
    let qt : M -> Real := fun x =>
      (-2 : Real) * metricRicciAt (I := I) (M := M) g x
          (vec2 (I := I) (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)) +
        2 * g.inner x (gradientFun (I := I) g ft x)
          (gradientFun (I := I) g f x)
    (∫ x,
        (R x + q x + s * (Rt x + qt x) + ft x +
          (s * (R x + q x) + f x - (n : Real)) *
            (-((n : Real) / (2 * s)) - ft x + R x))
      ∂(expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) f)) =
      -2 * s *
        ∫ x,
          normSq0S (I := I) g x 2
            (metricRicciAt (I := I) (M := M) g x +
              hessianSec (I := I) (metricCov (I := I) (M := M) g)
                (metricCov_smooth (I := I) (M := M) g) f hf x -
              (1 / (2 * s)) • metricTensor0S (I := I) g x)
        ∂(expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) f) := by
  classical
  dsimp only
  let n := Module.finrank Real E
  let R : M -> Real := metricScalarAt (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let Hess := hessianSec (I := I) (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) f hf
  let q : M -> Real := fun x =>
    g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x)
  let L : M -> Real := Δ_g (I := I) g hf
  let z : M -> Real := fun x => L x - q x
  let ft : M -> Real := fun x => z x + R x - (n : Real) / (2 * s)
  let Rt : M -> Real := fun x =>
    -(Δ_g (I := I) g (metricScalar_smooth (I := I) (M := M) g) x +
      2 * normSq0S (I := I) g x 2 (Ric x))
  let qt : M -> Real := fun x =>
    (-2 : Real) * Ric x
        (vec2 (I := I) (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x)) +
      2 * g.inner x (gradientFun (I := I) g ft x)
        (gradientFun (I := I) g f x)
  let μw := expNegPotentialWeightedMeasure
    (riemannianVolumeMeasure (I := I) (M := M) g) f
  have hR : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) R := by
    simpa only [R] using metricScalar_smooth (I := I) (M := M) g
  by_cases hdim : Module.finrank Real E = 0
  · have hLap0 (a : M -> Real)
        (ha : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) a) (x : M) :
        Δ_g (I := I) g ha x = 0 := by
      have hunivE :
          (Finset.univ : Finset (Fin (Module.finrank Real E))) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i _
        have hi : i.val < 0 := by simpa only [hdim] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      rw [Δ_g_def, divergence_g_def, localDivergence_def, hunivE]
      simp
    have hNorm0 (x : M)
        (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x) :
        normSq0S (I := I) g x 2 A = 0 := by
      have htang : Module.finrank Real (TangentSpace I x) = 0 := hdim
      let basis := Module.finBasis Real (TangentSpace I x)
      let gInv : Fin (Module.finrank Real (TangentSpace I x)) ->
          Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun _ _ => 0
      have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
        intro i _
        have hi : i.val < 0 := by simpa only [htang] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      have hunivT :
          (Finset.univ : Finset (Fin (Module.finrank Real (TangentSpace I x)))) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i _
        have hi : i.val < 0 := by simpa only [htang] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      rw [normSq0S_two_eq_coord (I := I) g x basis gInv hinv, hunivT]
      simp
    have hR0 (x : M) : R x = 0 := by
      have htang : Module.finrank Real (TangentSpace I x) = 0 := hdim
      let basis := Module.finBasis Real (TangentSpace I x)
      let gInv : Fin (Module.finrank Real (TangentSpace I x)) ->
          Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun _ _ => 0
      have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
        intro i _
        have hi : i.val < 0 := by simpa only [htang] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      have hunivT :
          (Finset.univ : Finset (Fin (Module.finrank Real (TangentSpace I x)))) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i _
        have hi : i.val < 0 := by simpa only [htang] using i.isLt
        exact (Nat.not_lt_zero _ hi).elim
      dsimp only [R]
      rw [metricScalarAt_def,
        metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv,
        hunivT]
      simp
    have hq0 (x : M) : q x = 0 := by
      have htang : Module.finrank Real (TangentSpace I x) = 0 := hdim
      letI : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.mp htang
      have hgrad : gradientFun (I := I) g f x = 0 := Subsingleton.elim _ _
      dsimp only [q]
      rw [hgrad, (g.inner x).map_zero, ContinuousLinearMap.zero_apply]
    have hft0 (x : M) : ft x = 0 := by
      dsimp only [ft, z]
      have hL0 : L x = 0 := by simpa only [L] using hLap0 f hf x
      rw [hL0, hq0 x, hR0 x]
      simp [n, hdim]
    have hRt0 (x : M) : Rt x = 0 := by
      dsimp only [Rt]
      rw [hLap0 R hR x, hNorm0 x (Ric x)]
      ring
    have hqt0 (x : M) : qt x = 0 := by
      have htang : Module.finrank Real (TangentSpace I x) = 0 := hdim
      letI : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.mp htang
      have hgrad : gradientFun (I := I) g f x = 0 := Subsingleton.elim _ _
      have hgradft : gradientFun (I := I) g ft x = 0 := Subsingleton.elim _ _
      have hRic : Ric x (vec2 (I := I) (0 : TangentSpace I x) 0) = 0 := by
        exact (Ric x).map_coord_zero (i := 0) (by simp [vec2])
      have hinner :
          g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        rw [(g.inner x).map_zero, ContinuousLinearMap.zero_apply]
      dsimp only [qt]
      rw [hgrad, hgradft, hRic, hinner]
      ring
    let Sq0 : M -> Real := fun x =>
      normSq0S (I := I) g x 2
        (Ric x + Hess x - (1 / (2 * s)) • metricTensor0S (I := I) g x)
    have hSq0 (x : M) : Sq0 x = 0 := by
      exact hNorm0 x _
    have hraw0 (x : M) :
        R x + q x + s * (Rt x + qt x) + ft x +
            (s * (R x + q x) + f x - (n : Real)) *
              (-((n : Real) / (2 * s)) - ft x + R x) = 0 := by
      rw [hR0 x, hq0 x, hRt0 x, hqt0 x, hft0 x]
      simp [n, hdim]
    have hleft :
        (∫ x,
          (R x + q x + s * (Rt x + qt x) + ft x +
            (s * (R x + q x) + f x - (n : Real)) *
              (-((n : Real) / (2 * s)) - ft x + R x)) ∂μw) = 0 := by
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall hraw0
    have hright : (∫ x, Sq0 x ∂μw) = 0 := by
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall hSq0
    change
      (∫ x,
        (R x + q x + s * (Rt x + qt x) + ft x +
          (s * (R x + q x) + f x - (n : Real)) *
            (-((n : Real) / (2 * s)) - ft x + R x)) ∂μw) =
        -2 * s * ∫ x, Sq0 x ∂μw
    rw [hleft, hright]
    ring
  letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
  have hq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) q := by
    simpa only [q, grad_g_apply] using normGradSqFun_contMDiff (I := I) g hf
  have hL : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) L := by
    simpa only [L] using Δ_g_contMDiff (I := I) g hf
  have hz : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) z := by
    exact hL.sub hq
  have hft : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) ft := by
    exact (hz.add hR).sub contMDiff_const
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (expNegPotentialDensity f x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (ENNReal.continuous_ofReal.comp
      (expNegPotentialDensity_contMDiff (I := I) hf).continuous).aemeasurable
  have hZG (a : M -> Real)
      (ha : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) a) :
      (∫ x,
          (Δ_g (I := I) g ha x -
            g.inner x (grad_g (I := I) g ha x) (grad_g (I := I) g hf x))
        ∂μw) = 0 := by
    simpa only [μw] using weighted_grad_zero (I := I) g hf ha
  have hWG (a : M -> Real)
      (ha : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) a) :
      (∫ x, (Δ_g (I := I) g ha x + a x * z x) ∂μw) = 0 := by
    have hDaI : Integrable (fun x : M => Δ_g (I := I) g ha x) μw := by
      simpa only [μw] using weighted_int (I := I) g hf
        (Δ_g_contMDiff (I := I) g ha).continuous
    have hazI : Integrable (fun x : M => a x * z x) μw := by
      simpa only [μw] using weighted_int (I := I) g hf (ha.mul hz).continuous
    have hgreen :
        (∫ x, Δ_g (I := I) g ha x ∂μw) =
          ∫ x, a x * (-L x + q x) ∂μw := by
      simpa only [μw, L, q, grad_g_apply] using
        weightedGreen (I := I) g hf ha hmeas
    calc
      (∫ x, (Δ_g (I := I) g ha x + a x * z x) ∂μw) =
          (∫ x, Δ_g (I := I) g ha x ∂μw) +
            ∫ x, a x * z x ∂μw := integral_add hDaI hazI
      _ = (∫ x, a x * (-L x + q x) ∂μw) +
            ∫ x, a x * z x ∂μw := by rw [hgreen]
      _ = (∫ x, -(a x * z x) ∂μw) +
            ∫ x, a x * z x ∂μw := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp only [z]
            ring
      _ = -(∫ x, a x * z x ∂μw) +
            ∫ x, a x * z x ∂μw := by rw [integral_neg]
      _ = 0 := by ring
  let RicGrad : M -> Real := fun x =>
    Ric x (vec2 (I := I) (gradientFun (I := I) g f x)
      (gradientFun (I := I) g f x))
  let C : M -> Real := fun x => inner02 (I := I) g x (Ric x) (Hess x)
  let HB : M -> Real := fun x =>
    normSq0S (I := I) g x 2 (Hess x) + RicGrad x - z x ^ 2 -
      (1 / 2 : Real) * q x * z x
  let HS : M -> Real := fun x =>
    C x - RicGrad x - (1 / 2 : Real) * R x * z x
  let Zft : M -> Real := fun x =>
    Δ_g (I := I) g hft x -
      g.inner x (grad_g (I := I) g hft x) (grad_g (I := I) g hf x)
  let Wft : M -> Real := fun x => Δ_g (I := I) g hft x + ft x * z x
  let WR : M -> Real := fun x => Δ_g (I := I) g hR x + R x * z x
  let Wf : M -> Real := fun x => Δ_g (I := I) g hf x + f x * z x
  let Zf : M -> Real := fun x =>
    Δ_g (I := I) g hf x -
      g.inner x (grad_g (I := I) g hf x) (grad_g (I := I) g hf x)
  let Sq : M -> Real := fun x =>
    normSq0S (I := I) g x 2
      (Ric x + Hess x - (1 / (2 * s)) • metricTensor0S (I := I) g x)
  let Corr : M -> Real := fun x =>
    ((((((2 * s) * HB x + (4 * s) * HS x) + (-2 * s) * Zft x) +
      (2 * s) * Wft x) + (-s) * WR x) + (-1) * Wf x) +
      (2 * (n : Real)) * Zf x
  have hRicGrad : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) RicGrad := by
    have hact := tangentSectionAction_contMDiff (I := I)
      (ricDriftVec (I := I) g hf) hf
    have hRq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x : M => (1 / 2 : Real) * R x * q x) :=
      (contMDiff_const.mul hR).mul hq
    refine (hact.add hRq).congr ?_
    intro x
    simp only [Pi.add_apply]
    rw [ricDriftAct (I := I) g hf x]
    simp only [RicGrad, Ric, R, q, metricRicci_apply, grad_g_apply,
      gradient_eq_gradFun]
    ring
  have hHB : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) HB := by
    have hHessNorm := normSq02_smooth (I := I) g Hess
    have hhalfqz : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x : M => (1 / 2 : Real) * q x * z x) :=
      (contMDiff_const.mul hq).mul hz
    simpa only [HB] using
      (((hHessNorm.add hRicGrad).sub (hz.pow 2)).sub hhalfqz)
  have hHS : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) HS := by
    have hd := divergence_g_contMDiff (I := I) g (ricDriftVec (I := I) g hf)
    have ha := tangentSectionAction_contMDiff (I := I)
      (ricDriftVec (I := I) g hf) hf
    refine (hd.sub ha).congr ?_
    intro x
    rw [ricDriftDiv (I := I) g hf x, ricDriftAct (I := I) g hf x]
    simp only [HS, C, RicGrad, Ric, Hess, R, L, q, z,
      metricRicci_apply, grad_g_apply, gradient_eq_gradFun]
    ring
  have hZGsm (a : M -> Real)
      (ha : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) a) :
      ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => Δ_g (I := I) g ha x -
          g.inner x (grad_g (I := I) g ha x) (grad_g (I := I) g hf x)) :=
    (Δ_g_contMDiff (I := I) g ha).sub
      (contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
        (grad_g (I := I) g ha) (grad_g (I := I) g hf))
  have hWGsm (a : M -> Real)
      (ha : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) a) :
      ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => Δ_g (I := I) g ha x + a x * z x) :=
    (Δ_g_contMDiff (I := I) g ha).add (ha.mul hz)
  have hZft : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) Zft := by
    simpa only [Zft] using hZGsm ft hft
  have hWft : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) Wft := by
    simpa only [Wft] using hWGsm ft hft
  have hWR : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) WR := by
    simpa only [WR] using hWGsm R hR
  have hWf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) Wf := by
    simpa only [Wf] using hWGsm f hf
  have hZf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) Zf := by
    simpa only [Zf] using hZGsm f hf
  have hmetric (x : M) :
      metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
    ext v
    rw [metricTensorField_apply, metricTensor0S_apply]
  let K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    Ric + Hess - (1 / (2 * s)) • metricTensorField (I := I) g
  have hSq : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) Sq := by
    have hK := normSq02_smooth (I := I) g K
    refine hK.congr ?_
    intro x
    change
      normSq0S (I := I) g x 2
          (Ric x + Hess x - (1 / (2 * s)) • metricTensor0S (I := I) g x) =
        normSq0S (I := I) g x 2
          (Ric x + Hess x - (1 / (2 * s)) • metricTensorField (I := I) g x)
    rw [hmetric x]
  have hmc : IsMetricCompatible_gen (I := I)
      (metricCov (I := I) (M := M) g) g := by
    simpa only [metricCov] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hHtrace (x : M) :
      metricTracePair0SAt (I := I) g (Hess x) = L x := by
    have htrace :=
      (scalarLap_smooth (I := I) (M := M)
        (metricCov (I := I) (M := M) g)
        (metricCov_smooth (I := I) (M := M) g)
        g hmc (x := x) f hf).eq_trace
    calc
      metricTracePair0SAt (I := I) g (Hess x) =
          laplacian (I := I) (metricCov (I := I) (M := M) g) g f x := by
        simpa only [Hess, scalarLapTraceAt_eq_pair] using htrace.symm
      _ = Δ_g (I := I) g hf x := by
        simpa only [metricCov, LeviCivita] using
          (laplacian_levi_eq (I := I) g hf x)
      _ = L x := rfl
  have hRtrace (x : M) :
      metricTracePair0SAt (I := I) g (Ric x) = R x := by
    simpa only [Ric, R, metricRicci_apply] using
      (metricScalarAt_def (I := I) (M := M) g x).symm
  have hsq (x : M) :=
    norm_sq_shift (I := I) g (Ric x) (Hess x)
      (1 / (2 * s)) (R x) (L x) (hRtrace x) (hHtrace x)
  have hHBzero : (∫ x, HB x ∂μw) = 0 := by
    simpa only [HB, RicGrad, Ric, Hess, q, L, z, μw,
      metricRicci_apply, grad_g_apply] using weighted_bochner (I := I) g hf
  have hHSzero : (∫ x, HS x ∂μw) = 0 := by
    simpa only [HS, C, RicGrad, Ric, Hess, R, q, L, z, μw,
      metricRicci_apply, grad_g_apply] using weighted_hess_split (I := I) g hf
  have hZftzero : (∫ x, Zft x ∂μw) = 0 := by
    simpa only [Zft] using hZG ft hft
  have hWftzero : (∫ x, Wft x ∂μw) = 0 := by
    simpa only [Wft] using hWG ft hft
  have hWRzero : (∫ x, WR x ∂μw) = 0 := by
    simpa only [WR] using hWG R hR
  have hWfzero : (∫ x, Wf x ∂μw) = 0 := by
    simpa only [Wf] using hWG f hf
  have hZfzero : (∫ x, Zf x ∂μw) = 0 := by
    simpa only [Zf] using hZG f hf
  have hHBI : Integrable HB μw := by
    simpa only [μw] using weighted_int (I := I) g hf hHB.continuous
  have hHSI : Integrable HS μw := by
    simpa only [μw] using weighted_int (I := I) g hf hHS.continuous
  have hZftI : Integrable Zft μw := by
    simpa only [μw] using weighted_int (I := I) g hf hZft.continuous
  have hWftI : Integrable Wft μw := by
    simpa only [μw] using weighted_int (I := I) g hf hWft.continuous
  have hWRI : Integrable WR μw := by
    simpa only [μw] using weighted_int (I := I) g hf hWR.continuous
  have hWfI : Integrable Wf μw := by
    simpa only [μw] using weighted_int (I := I) g hf hWf.continuous
  have hZfI : Integrable Zf μw := by
    simpa only [μw] using weighted_int (I := I) g hf hZf.continuous
  have hSqI : Integrable Sq μw := by
    simpa only [μw] using weighted_int (I := I) g hf hSq.continuous
  have hCorr : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) Corr := by
    have h0 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => (2 * s) * HB x) := contMDiff_const.mul hHB
    have h1 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => (4 * s) * HS x) := contMDiff_const.mul hHS
    have h2 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => (-2 * s) * Zft x) := contMDiff_const.mul hZft
    have h3 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => (2 * s) * Wft x) := contMDiff_const.mul hWft
    have h4 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => (-s) * WR x) := contMDiff_const.mul hWR
    have h5 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => (-1) * Wf x) := contMDiff_const.mul hWf
    have h6 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun x => (2 * (n : Real)) * Zf x) := contMDiff_const.mul hZf
    simpa only [Corr] using (((((h0.add h1).add h2).add h3).add h4).add h5).add h6
  have hCorrI : Integrable Corr μw := by
    simpa only [μw] using weighted_int (I := I) g hf hCorr.continuous
  have hCorrzero : (∫ x, Corr x ∂μw) = 0 := by
    simpa only [Corr] using int7_zero (μ := μw)
      hHBI hHSI hZftI hWftI hWRI hWfI hZfI
      hHBzero hHSzero hZftzero hWftzero hWRzero hWfzero hZfzero
      (2 * s) (4 * s) (-2 * s) (2 * s) (-s) (-1) (2 * (n : Real))
  have hpoint (x : M) :
      R x + q x + s * (Rt x + qt x) + ft x +
          (s * (R x + q x) + f x - (n : Real)) *
            (-((n : Real) / (2 * s)) - ft x + R x) =
        (-2 * s) * Sq x + Corr x := by
    dsimp only [Sq, Corr, HB, HS, C, RicGrad, Zft, Wft, WR, Wf, Zf,
      Rt, qt]
    rw [hsq x]
    dsimp only [R, L, n]
    simp only [grad_g_apply, gradient_eq_gradFun]
    rw [show ft x = z x + R x - (n : Real) / (2 * s) from rfl]
    dsimp only [z, L, q, R, n]
    simp only [gradient_eq_gradFun]
    field_simp [ne_of_gt hs]
    ring
  change
    (∫ x,
        (R x + q x + s * (Rt x + qt x) + ft x +
          (s * (R x + q x) + f x - (n : Real)) *
            (-((n : Real) / (2 * s)) - ft x + R x)) ∂μw) =
      -2 * s * ∫ x, Sq x ∂μw
  calc
    (∫ x,
        (R x + q x + s * (Rt x + qt x) + ft x +
          (s * (R x + q x) + f x - (n : Real)) *
            (-((n : Real) / (2 * s)) - ft x + R x)) ∂μw) =
        ∫ x, ((-2 * s) * Sq x + Corr x) ∂μw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (∫ x, (-2 * s) * Sq x ∂μw) + ∫ x, Corr x ∂μw := by
      exact integral_add (hSqI.const_mul (-2 * s)) hCorrI
    _ = (-2 * s) * (∫ x, Sq x ∂μw) + 0 := by
      rw [integral_const_mul, hCorrzero]
    _ = -2 * s * ∫ x, Sq x ∂μw := by ring

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
