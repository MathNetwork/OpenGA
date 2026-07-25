import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RicciDiffAffine
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciContinuityInMetricTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAllPt

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000



































noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open Tensor0SBundle TensorLieDeriv
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]



section JetExpansion

variable (gRef : SmoothRiemannianMetric I M) (x : M)




private def sRep
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) : E → Real :=
  writtenInExtChartAt I 𝓘(Real, Real) x
    (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => W a w))



omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma sRep_diffAt
    [Module.Finite ℝ E]
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {z : E} (hz : z ∈ (extChartAt I x).target) :
    DifferentiableAt Real (sRep gRef x A0 p W) z := by
  have h := chartRep_towerScalar_contDiffOn (I := I) gRef A0 p W x
  have h1 : DifferentiableOn Real (sRep gRef x A0 p W) (extChartAt I x).target :=
    h.differentiableOn (by simp)
  exact h1.differentiableAt ((isOpen_extChartAt_target (I := I) x).mem_nhds hz)



omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma sRep_fderiv_germ
    [Module.Finite ℝ E]
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (v : E)
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hσ : ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σ z = tangentConstInChart (𝕜 := Real) (I := I) x v z) :
    (fun z : E => fderiv Real (sRep gRef x A0 p W) z v)
      =ᶠ[𝓝 (extChartAt I x x)]
      writtenInExtChartAt I 𝓘(Real, Real) x (towerStep (I := I) gRef A0 p W σ) :=
  fderiv_chartRep_eq_towerStep (I := I) gRef A0 p W x v σ hσ
    (Set.singleton_subset_iff.mpr (mem_chart_source H x)) rfl



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma sRep_pd_val
    [Module.Finite ℝ E]
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (m : Fin (Module.finrank Real E))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hσ : ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σ z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) m) z) :
    partialDeriv (E := E) m (sRep gRef x A0 p W) (extChartAt I x x)
      = towerStep (I := I) gRef A0 p W σ x := by
  have hval := (sRep_fderiv_germ gRef x A0 p W ((chartModelBasis E) m) σ hσ).eq_of_nhds
  have hx : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  calc partialDeriv (E := E) m (sRep gRef x A0 p W) (extChartAt I x x)
      = fderiv Real (sRep gRef x A0 p W) (extChartAt I x x) ((chartModelBasis E) m) := rfl
    _ = writtenInExtChartAt I 𝓘(Real, Real) x (towerStep (I := I) gRef A0 p W σ)
        (extChartAt I x x) := hval
    _ = towerStep (I := I) gRef A0 p W σ x := by
        rw [writtenInExtChartAt_real_apply, hx]




omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma towerStep_rep_split
    [Module.Finite ℝ E]
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    writtenInExtChartAt I 𝓘(Real, Real) x (towerStep (I := I) gRef A0 p W σ)
      = fun z : E =>
        sRep gRef x A0 (p + 1) (Fin.cons σ W) z
          + ∑ a : Fin (p + 2),
              sRep gRef x A0 p
                (Function.update W a
                  (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                      (I := I) gRef) σ (W a))) z := by
  funext z
  simp only [sRep, writtenInExtChartAt_real_apply, towerStep]
  set q : M := (extChartAt I x).symm z with hq
  congr 1
  · congr 1
    funext b
    refine Fin.cases ?_ (fun c => ?_) b <;> simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    funext b
    by_cases h : b = a
    · subst h; simp [covSection_apply]
    · simp [Function.update_of_ne h]



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma sRep_pd2_val
    [Module.Finite ℝ E]
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (m mm : Fin (Module.finrank Real E))
    (σm σmm : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hσm : ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σm z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) m) z)
    (hσmm : ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σmm z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) mm) z) :
    partialDeriv (E := E) mm
        (partialDeriv (E := E) m (sRep gRef x A0 0 W)) (extChartAt I x x)
      = towerStep (I := I) gRef A0 1 (Fin.cons σm W) σmm x
        + ∑ a : Fin 2,
            towerStep (I := I) gRef A0 0
              (Function.update W a
                (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                    (I := I) gRef) σm (W a))) σmm x := by
  have hαtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)

  have hgerm := sRep_fderiv_germ gRef x A0 0 W ((chartModelBasis E) m) σm hσm
  have hinner : partialDeriv (E := E) m (sRep gRef x A0 0 W)
      = fun z : E => fderiv Real (sRep gRef x A0 0 W) z ((chartModelBasis E) m) := rfl
  have hfd : fderiv Real (partialDeriv (E := E) m (sRep gRef x A0 0 W))
        (extChartAt I x x)
      = fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x
          (towerStep (I := I) gRef A0 0 W σm)) (extChartAt I x x) := by
    rw [hinner]
    exact hgerm.fderiv_eq

  set corr : Fin 2 → (E → Real) := fun a =>
    sRep gRef x A0 0
      (Function.update W a
        (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
            (I := I) gRef) σm (W a))) with hcorr
  have hsplit := towerStep_rep_split gRef x A0 0 W σm
  have hd1 : DifferentiableAt Real (sRep gRef x A0 1 (Fin.cons σm W))
      (extChartAt I x x) := sRep_diffAt gRef x A0 1 (Fin.cons σm W) hαtgt
  have hdc : ∀ a : Fin 2, DifferentiableAt Real (corr a) (extChartAt I x x) :=
    fun a => sRep_diffAt gRef x A0 0 _ hαtgt
  have hsum : fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x
        (towerStep (I := I) gRef A0 0 W σm)) (extChartAt I x x) ((chartModelBasis E) mm)
      = fderiv Real (sRep gRef x A0 1 (Fin.cons σm W)) (extChartAt I x x)
          ((chartModelBasis E) mm)
        + ∑ a : Fin 2, fderiv Real (corr a) (extChartAt I x x)
            ((chartModelBasis E) mm) := by
    have hcsum : HasFDerivAt (fun z : E => ∑ a : Fin 2, corr a z)
        (∑ a : Fin 2, fderiv Real (corr a) (extChartAt I x x)) (extChartAt I x x) := by
      simpa [Finset.sum_apply] using
        HasFDerivAt.sum (fun (a : Fin 2) (_ : a ∈ Finset.univ) => (hdc a).hasFDerivAt)
    have htot : HasFDerivAt (writtenInExtChartAt I 𝓘(Real, Real) x
        (towerStep (I := I) gRef A0 0 W σm))
        (fderiv Real (sRep gRef x A0 1 (Fin.cons σm W)) (extChartAt I x x)
          + ∑ a : Fin 2, fderiv Real (corr a) (extChartAt I x x)) (extChartAt I x x) := by
      rw [hsplit]
      exact hd1.hasFDerivAt.add hcsum
    rw [htot.fderiv]
    simp [ContinuousLinearMap.add_apply]
  calc partialDeriv (E := E) mm
        (partialDeriv (E := E) m (sRep gRef x A0 0 W)) (extChartAt I x x)
      = fderiv Real (partialDeriv (E := E) m (sRep gRef x A0 0 W))
          (extChartAt I x x) ((chartModelBasis E) mm) := rfl
    _ = fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x
          (towerStep (I := I) gRef A0 0 W σm)) (extChartAt I x x)
          ((chartModelBasis E) mm) := by rw [hfd]
    _ = fderiv Real (sRep gRef x A0 1 (Fin.cons σm W)) (extChartAt I x x)
            ((chartModelBasis E) mm)
          + ∑ a : Fin 2, fderiv Real (corr a) (extChartAt I x x)
              ((chartModelBasis E) mm) := hsum
    _ = towerStep (I := I) gRef A0 1 (Fin.cons σm W) σmm x
          + ∑ a : Fin 2,
              towerStep (I := I) gRef A0 0
                (Function.update W a
                  (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                      (I := I) gRef) σm (W a))) σmm x := by
        rw [show fderiv Real (sRep gRef x A0 1 (Fin.cons σm W)) (extChartAt I x x)
              ((chartModelBasis E) mm)
            = partialDeriv (E := E) mm (sRep gRef x A0 1 (Fin.cons σm W))
                (extChartAt I x x) from rfl]
        rw [sRep_pd_val gRef x A0 1 (Fin.cons σm W) mm σmm hσmm]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [show fderiv Real (corr a) (extChartAt I x x) ((chartModelBasis E) mm)
            = partialDeriv (E := E) mm (corr a) (extChartAt I x x) from rfl]
        exact sRep_pd_val gRef x A0 0 _ mm σmm hσmm




omit [Module.Finite ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma eval_le
    [Module.Finite ℝ E]
    (s : ℕ) (slots : Fin s → TangentSpace I x) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ T : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) s x,
        |T slots| ≤ C * Real.sqrt (normSq0S (I := I) gRef x s T) := by
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  refine ⟨∏ a : Fin s, Real.sqrt (gRef.inner x (slots a) (slots a)),
    Finset.prod_nonneg (fun a _ => Real.sqrt_nonneg _), fun T => ?_⟩
  have h := abs_apply_le_sqrt_normSq0S (I := I) (g := gRef)
    (x := x) (s := s) basis hON T slots
  calc |T slots|
      ≤ Real.sqrt (normSq0S (I := I) gRef x s T)
          * ∏ a : Fin s, Real.sqrt (gRef.inner x (slots a) (slots a)) := h
    _ = (∏ a : Fin s, Real.sqrt (gRef.inner x (slots a) (slots a)))
          * Real.sqrt (normSq0S (I := I) gRef x s T) := by
        rw [mul_comm]




omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma towVal_le
    [Module.Finite ℝ E]
    (p : ℕ)
    (W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ A0 A0' : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 p W σ x - towerStep (I := I) gRef A0' p W σ x| ≤
          C * (Real.sqrt (normSq0S (I := I) gRef x (p + 1 + 2)
                (covDerivOfField (I := I) gRef A0 (p + 1) x
                  - covDerivOfField (I := I) gRef A0' (p + 1) x))
              + Real.sqrt (normSq0S (I := I) gRef x (p + 2)
                (covDerivOfField (I := I) gRef A0 p x
                  - covDerivOfField (I := I) gRef A0' p x))) := by
  classical
  obtain ⟨C1, hC1nn, hC1⟩ := eval_le gRef x (p + 1 + 2)
    (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x))
  have hCa : ∀ a : Fin (p + 2), ∃ C : Real, 0 ≤ C ∧
      ∀ T : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (p + 2) x,
        |T (Function.update (fun b : Fin (p + 2) => W b x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => W a r) x) (σ x)))| ≤
          C * Real.sqrt (normSq0S (I := I) gRef x (p + 2) T) :=
    fun a => eval_le gRef x (p + 2) _
  choose Ca hCann hCa using hCa
  refine ⟨C1 + ∑ a : Fin (p + 2), Ca a,
    add_nonneg hC1nn (Finset.sum_nonneg fun a _ => hCann a), fun A0 A0' => ?_⟩
  set d1 : Real := Real.sqrt (normSq0S (I := I) gRef x (p + 1 + 2)
    (covDerivOfField (I := I) gRef A0 (p + 1) x
      - covDerivOfField (I := I) gRef A0' (p + 1) x)) with hd1def
  set d0 : Real := Real.sqrt (normSq0S (I := I) gRef x (p + 2)
    (covDerivOfField (I := I) gRef A0 p x
      - covDerivOfField (I := I) gRef A0' p x)) with hd0def
  have hd1nn : 0 ≤ d1 := Real.sqrt_nonneg _
  have hd0nn : 0 ≤ d0 := Real.sqrt_nonneg _
  have hdiff : towerStep (I := I) gRef A0 p W σ x - towerStep (I := I) gRef A0' p W σ x
      = (covDerivOfField (I := I) gRef A0 (p + 1) x
            - covDerivOfField (I := I) gRef A0' (p + 1) x)
          (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x))
        + ∑ a : Fin (p + 2),
            (covDerivOfField (I := I) gRef A0 p x
                - covDerivOfField (I := I) gRef A0' p x)
              (Function.update (fun b : Fin (p + 2) => W b x) a
                (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun r : M => W a r) x) (σ x))) := by
    have htop :
        (covDerivOfField (I := I) gRef A0 (p + 1) x
            - covDerivOfField (I := I) gRef A0' (p + 1) x)
          (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x)) =
        covDerivOfField (I := I) gRef A0 (p + 1) x
            (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x))
          - covDerivOfField (I := I) gRef A0' (p + 1) x
            (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x)) := rfl
    have hslot (a : Fin (p + 2)) :
        (covDerivOfField (I := I) gRef A0 p x
            - covDerivOfField (I := I) gRef A0' p x)
          (Function.update (fun b : Fin (p + 2) => W b x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => W a r) x) (σ x))) =
        covDerivOfField (I := I) gRef A0 p x
            (Function.update (fun b : Fin (p + 2) => W b x) a
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                (fun r : M => W a r) x) (σ x)))
          - covDerivOfField (I := I) gRef A0' p x
            (Function.update (fun b : Fin (p + 2) => W b x) a
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                (fun r : M => W a r) x) (σ x))) := rfl
    rw [htop]
    simp_rw [hslot]
    unfold towerStep
    rw [Finset.sum_sub_distrib]
    abel
  rw [hdiff]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(covDerivOfField (I := I) gRef A0 (p + 1) x
        - covDerivOfField (I := I) gRef A0' (p + 1) x)
      (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x))| ≤ C1 * d1 := hC1 _
  have h2 : |∑ a : Fin (p + 2),
        (covDerivOfField (I := I) gRef A0 p x
            - covDerivOfField (I := I) gRef A0' p x)
          (Function.update (fun b : Fin (p + 2) => W b x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => W a r) x) (σ x)))| ≤
      (∑ a : Fin (p + 2), Ca a) * d0 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun a _ => hCa a _
  calc _ ≤ C1 * d1 + (∑ a : Fin (p + 2), Ca a) * d0 := add_le_add h1 h2
    _ ≤ (C1 + ∑ a : Fin (p + 2), Ca a) * (d1 + d0) := by
        have hs : 0 ≤ ∑ a : Fin (p + 2), Ca a := Finset.sum_nonneg fun a _ => hCann a
        nlinarith



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma towVal_le'
    [Module.Finite ℝ E]
    (p : ℕ)
    (W : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 p W σ x| ≤
          C * (Real.sqrt (normSq0S (I := I) gRef x (p + 1 + 2)
                (covDerivOfField (I := I) gRef A0 (p + 1) x))
              + Real.sqrt (normSq0S (I := I) gRef x (p + 2)
                (covDerivOfField (I := I) gRef A0 p x))) := by
  classical
  obtain ⟨C1, hC1nn, hC1⟩ := eval_le gRef x (p + 1 + 2)
    (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x))
  have hCa : ∀ a : Fin (p + 2), ∃ C : Real, 0 ≤ C ∧
      ∀ T : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (p + 2) x,
        |T (Function.update (fun b : Fin (p + 2) => W b x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => W a r) x) (σ x)))| ≤
          C * Real.sqrt (normSq0S (I := I) gRef x (p + 2) T) :=
    fun a => eval_le gRef x (p + 2) _
  choose Ca hCann hCa using hCa
  refine ⟨C1 + ∑ a : Fin (p + 2), Ca a,
    add_nonneg hC1nn (Finset.sum_nonneg fun a _ => hCann a), fun A0 => ?_⟩
  set d1 : Real := Real.sqrt (normSq0S (I := I) gRef x (p + 1 + 2)
    (covDerivOfField (I := I) gRef A0 (p + 1) x)) with hd1def
  set d0 : Real := Real.sqrt (normSq0S (I := I) gRef x (p + 2)
    (covDerivOfField (I := I) gRef A0 p x)) with hd0def
  have hd1nn : 0 ≤ d1 := Real.sqrt_nonneg _
  have hd0nn : 0 ≤ d0 := Real.sqrt_nonneg _
  rw [towerStep]
  refine (abs_add_le _ _).trans ?_
  have h1 : |(covDerivOfField (I := I) gRef A0 (p + 1) x)
      (Fin.cons (σ x) (fun a : Fin (p + 2) => W a x))| ≤ C1 * d1 := hC1 _
  have h2 : |∑ a : Fin (p + 2),
        (covDerivOfField (I := I) gRef A0 p x)
          (Function.update (fun b : Fin (p + 2) => W b x) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => W a r) x) (σ x)))| ≤
      (∑ a : Fin (p + 2), Ca a) * d0 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun a _ => hCa a _
  calc _ ≤ C1 * d1 + (∑ a : Fin (p + 2), Ca a) * d0 := add_le_add h1 h2
    _ ≤ (C1 + ∑ a : Fin (p + 2), Ca a) * (d1 + d0) := by
        have hs : 0 ≤ ∑ a : Fin (p + 2), Ca a := Finset.sum_nonneg fun a _ => hCann a
        nlinarith




omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma gram_germ
    [Module.Finite ℝ E]
    (u : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank Real E))
    (σi σj : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hσi : ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σi z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) z)
    (hσj : ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σj z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) j) z) :
    chartGramOnE (I := I) u x i j
      =ᶠ[𝓝 (extChartAt I x x)]
      sRep gRef x (Tensor0SBundle.metricTensorField (I := I) u) 0 ![σi, σj] := by
  have hαtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)
  have hx : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have htend : Filter.Tendsto (extChartAt I x).symm
      (𝓝 (extChartAt I x x)) (𝓝 x) := by
    have h := (continuousAt_extChartAt_symm'' (I := I) (x := x) hαtgt).tendsto
    rwa [hx] at h
  have hσi0 : ∀ᶠ q in 𝓝 x,
      σi q = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) q := by
    simpa [nhdsSet_singleton] using hσi
  have hσj0 : ∀ᶠ q in 𝓝 x,
      σj q = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) j) q := by
    simpa [nhdsSet_singleton] using hσj
  filter_upwards [htend.eventually hσi0, htend.eventually hσj0] with z hzi hzj
  simp only [sRep, writtenInExtChartAt_real_apply]
  set q : M := (extChartAt I x).symm z with hq
  have hval : (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) u) 0) q
        (fun a => (![σi, σj] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)) a q)
      = u.inner q (σi q) (σj q) := by
    have h0 : (covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) u) 0) q
          (fun a => (![σi, σj] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _)) a q)
        = (Tensor0SBundle.metricTensorField (I := I) u) q
            (fun a => (![σi, σj] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M → Type _)) a q) := rfl
    rw [h0, Tensor0SBundle.metricTensorField_apply]
    simp
  rw [hval, hzi, hzj, chartGramOnE]
  rw [chartGramMatrix_apply]
  congr 1


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma gram0_le
    [Module.Finite ℝ E]
    :
    ∃ C : Real, 0 ≤ C ∧ ∀ (u u' : SmoothRiemannianMetric I M)
      (i j : Fin (Module.finrank Real E)),
      |chartGramMatrix (I := I) u x x i j - chartGramMatrix (I := I) u' x x i j| ≤
        C * metricDerivNorm (I := I) 0 u u' gRef x := by
  classical
  have hC : ∀ t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
      ∃ C : Real, 0 ≤ C ∧
        ∀ T : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) 2 x,
          |T ![chartBasisVecFiber (I := I) x t.1 x, chartBasisVecFiber (I := I) x t.2 x]| ≤
            C * Real.sqrt (normSq0S (I := I) gRef x 2 T) :=
    fun t => eval_le gRef x 2 _
  choose Cf hCf0 hCf using hC
  refine ⟨∑ t, Cf t, Finset.sum_nonneg fun t _ => hCf0 t, fun u u' i j => ?_⟩
  have hentry : chartGramMatrix (I := I) u x x i j - chartGramMatrix (I := I) u' x x i j
      = (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
          ![chartBasisVecFiber (I := I) x i x, chartBasisVecFiber (I := I) x j x] := by
    rw [chartGramMatrix_apply, chartGramMatrix_apply]
    have hu := Tensor0SBundle.metricTensorField_apply (I := I) u x
      (fun a => (![chartBasisVecFiber (I := I) x i x,
        chartBasisVecFiber (I := I) x j x] : Fin 2 → TangentSpace I x) a)
    have hu' := Tensor0SBundle.metricTensorField_apply (I := I) u' x
      (fun a => (![chartBasisVecFiber (I := I) x i x,
        chartBasisVecFiber (I := I) x j x] : Fin 2 → TangentSpace I x) a)
    simp only [metricDiffCovDerivAt]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hu'
    change u.inner x _ _ - u'.inner x _ _
      = (metricCovDeriv (I := I) u gRef 0 x) _ - (metricCovDeriv (I := I) u' gRef 0 x) _
    rw [show (metricCovDeriv (I := I) u gRef 0 x) = Tensor0SBundle.metricTensorField (I := I) u x from rfl,
      show (metricCovDeriv (I := I) u' gRef 0 x) = Tensor0SBundle.metricTensorField (I := I) u' x from rfl,
      hu, hu']
  rw [hentry]
  have h := hCf (i, j) (metricDiffCovDerivAt (I := I) 0 u u' gRef x)
  refine h.trans ?_
  have hle : Cf (i, j) ≤ ∑ t, Cf t :=
    Finset.single_le_sum (fun t _ => hCf0 t) (Finset.mem_univ (i, j))
  have hnn : 0 ≤ Real.sqrt (normSq0S (I := I) gRef x 2
      (metricDiffCovDerivAt (I := I) 0 u u' gRef x)) := Real.sqrt_nonneg _
  calc Cf (i, j) * Real.sqrt (normSq0S (I := I) gRef x 2
          (metricDiffCovDerivAt (I := I) 0 u u' gRef x))
      ≤ (∑ t, Cf t) * Real.sqrt (normSq0S (I := I) gRef x 2
          (metricDiffCovDerivAt (I := I) 0 u u' gRef x)) :=
        mul_le_mul_of_nonneg_right hle hnn
    _ = (∑ t, Cf t) * metricDerivNorm (I := I) 0 u u' gRef x := rfl


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma gram_pd_eq
    [Module.Finite ℝ E]
    (σs : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hσs : ∀ i, ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σs i z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) z)
    (u : SmoothRiemannianMetric I M) (m i j : Fin (Module.finrank Real E)) :
    partialDeriv (E := E) m (chartGramOnE (I := I) u x i j) (extChartAt I x x)
      = towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
          ![σs i, σs j] (σs m) x := by
  have hg := gram_germ gRef x u i j (σs i) (σs j) (hσs i) (hσs j)
  have h1 : partialDeriv (E := E) m (chartGramOnE (I := I) u x i j) (extChartAt I x x)
      = partialDeriv (E := E) m
          (sRep gRef x (Tensor0SBundle.metricTensorField (I := I) u) 0 ![σs i, σs j])
          (extChartAt I x x) := by
    change fderiv Real _ (extChartAt I x x) ((chartModelBasis E) m)
      = fderiv Real _ (extChartAt I x x) ((chartModelBasis E) m)
    rw [hg.fderiv_eq]
  rw [h1, sRep_pd_val gRef x _ 0 ![σs i, σs j] m (σs m) (hσs m)]



omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma gram_pd2_eq
    [Module.Finite ℝ E]
    (σs : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hσs : ∀ i, ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σs i z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) z)
    (u : SmoothRiemannianMetric I M) (mm m i j : Fin (Module.finrank Real E)) :
    partialDeriv (E := E) mm
        (partialDeriv (E := E) m (chartGramOnE (I := I) u x i j)) (extChartAt I x x)
      = towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 1
          (Fin.cons (σs m) ![σs i, σs j]) (σs mm) x
        + ∑ a : Fin 2,
            towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
              (Function.update ![σs i, σs j] a
                (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                    (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x := by
  have hg := gram_germ gRef x u i j (σs i) (σs j) (hσs i) (hσs j)
  have hpd : partialDeriv (E := E) m (chartGramOnE (I := I) u x i j)
      =ᶠ[𝓝 (extChartAt I x x)]
      partialDeriv (E := E) m
        (sRep gRef x (Tensor0SBundle.metricTensorField (I := I) u) 0 ![σs i, σs j]) := by
    have h' : ∀ᶠ z in 𝓝 (extChartAt I x x),
        chartGramOnE (I := I) u x i j
          =ᶠ[𝓝 z] sRep gRef x (Tensor0SBundle.metricTensorField (I := I) u) 0
            ![σs i, σs j] := hg.eventuallyEq_nhds
    filter_upwards [h'] with z hz
    change fderiv Real _ z ((chartModelBasis E) m) = fderiv Real _ z ((chartModelBasis E) m)
    rw [hz.fderiv_eq]
  have h1 : partialDeriv (E := E) mm
      (partialDeriv (E := E) m (chartGramOnE (I := I) u x i j)) (extChartAt I x x)
      = partialDeriv (E := E) mm
          (partialDeriv (E := E) m
            (sRep gRef x (Tensor0SBundle.metricTensorField (I := I) u) 0 ![σs i, σs j]))
          (extChartAt I x x) := by
    change fderiv Real _ (extChartAt I x x) ((chartModelBasis E) mm)
      = fderiv Real _ (extChartAt I x x) ((chartModelBasis E) mm)
    rw [hpd.fderiv_eq]
  rw [h1]
  exact sRep_pd2_val gRef x _ ![σs i, σs j] m mm (σs m) (σs mm) (hσs m) (hσs mm)


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma gram1_le
    [Module.Finite ℝ E]
    (σs : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hσs : ∀ i, ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σs i z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) z) :
    ∃ C : Real, 0 ≤ C ∧ ∀ (u u' : SmoothRiemannianMetric I M)
      (m i j : Fin (Module.finrank Real E)),
      |partialDeriv (E := E) m (chartGramOnE (I := I) u x i j) (extChartAt I x x)
        - partialDeriv (E := E) m (chartGramOnE (I := I) u' x i j) (extChartAt I x x)| ≤
      C * (metricDerivNorm (I := I) 1 u u' gRef x
            + metricDerivNorm (I := I) 0 u u' gRef x) := by
  classical
  have hC : ∀ t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E)
      × Fin (Module.finrank Real E), ∃ C : Real, 0 ≤ C ∧
      ∀ A0 A0' : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 0 ![σs t.2.1, σs t.2.2] (σs t.1) x
          - towerStep (I := I) gRef A0' 0 ![σs t.2.1, σs t.2.2] (σs t.1) x| ≤
        C * (Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
              (covDerivOfField (I := I) gRef A0 (0 + 1) x
                - covDerivOfField (I := I) gRef A0' (0 + 1) x))
            + Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
              (covDerivOfField (I := I) gRef A0 0 x
                - covDerivOfField (I := I) gRef A0' 0 x))) :=
    fun t => towVal_le gRef x 0 ![σs t.2.1, σs t.2.2] (σs t.1)
  choose Cf hCf0 hCf using hC
  refine ⟨∑ t, Cf t, Finset.sum_nonneg fun t _ => hCf0 t, fun u u' m i j => ?_⟩
  rw [gram_pd_eq gRef x σs hσs u m i j, gram_pd_eq gRef x σs hσs u' m i j]
  have h := hCf (m, i, j) (Tensor0SBundle.metricTensorField (I := I) u)
    (Tensor0SBundle.metricTensorField (I := I) u')
  have hd1 : Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
      (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) (0 + 1) x
        - covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') (0 + 1) x))
      = metricDerivNorm (I := I) 1 u u' gRef x := rfl
  have hd0 : Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
      (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0 x
        - covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 0 x))
      = metricDerivNorm (I := I) 0 u u' gRef x := rfl
  rw [hd1, hd0] at h
  refine h.trans ?_
  have hle : Cf (m, i, j) ≤ ∑ t, Cf t :=
    Finset.single_le_sum (fun t _ => hCf0 t) (Finset.mem_univ (m, i, j))
  have hnn : 0 ≤ metricDerivNorm (I := I) 1 u u' gRef x
      + metricDerivNorm (I := I) 0 u u' gRef x :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hle hnn


omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private lemma gram2_le
    [Module.Finite ℝ E]
    (σs : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hσs : ∀ i, ∀ᶠ z in 𝓝ˢ ({x} : Set M),
      σs i z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) z) :
    ∃ C : Real, 0 ≤ C ∧ ∀ (u u' : SmoothRiemannianMetric I M)
      (mm m i j : Fin (Module.finrank Real E)),
      |partialDeriv (E := E) mm
          (partialDeriv (E := E) m (chartGramOnE (I := I) u x i j)) (extChartAt I x x)
        - partialDeriv (E := E) mm
            (partialDeriv (E := E) m (chartGramOnE (I := I) u' x i j)) (extChartAt I x x)| ≤
      C * (metricDerivNorm (I := I) 2 u u' gRef x
            + metricDerivNorm (I := I) 1 u u' gRef x
            + metricDerivNorm (I := I) 0 u u' gRef x) := by
  classical

  have hC1 : ∀ t : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E))
      × Fin (Module.finrank Real E) × Fin (Module.finrank Real E), ∃ C : Real, 0 ≤ C ∧
      ∀ A0 A0' : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 1 (Fin.cons (σs t.1.2) ![σs t.2.1, σs t.2.2]) (σs t.1.1) x
          - towerStep (I := I) gRef A0' 1 (Fin.cons (σs t.1.2) ![σs t.2.1, σs t.2.2]) (σs t.1.1) x| ≤
        C * (Real.sqrt (normSq0S (I := I) gRef x (1 + 1 + 2)
              (covDerivOfField (I := I) gRef A0 (1 + 1) x
                - covDerivOfField (I := I) gRef A0' (1 + 1) x))
            + Real.sqrt (normSq0S (I := I) gRef x (1 + 2)
              (covDerivOfField (I := I) gRef A0 1 x
                - covDerivOfField (I := I) gRef A0' 1 x))) :=
    fun t => towVal_le gRef x 1 (Fin.cons (σs t.1.2) ![σs t.2.1, σs t.2.2]) (σs t.1.1)

  have hC0 : ∀ t : ((Fin (Module.finrank Real E) × Fin (Module.finrank Real E))
      × Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) × Fin 2,
      ∃ C : Real, 0 ≤ C ∧
      ∀ A0 A0' : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 0
            (Function.update ![σs t.1.2.1, σs t.1.2.2] t.2
              (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                  (I := I) gRef) (σs t.1.1.2) (![σs t.1.2.1, σs t.1.2.2] t.2))) (σs t.1.1.1) x
          - towerStep (I := I) gRef A0' 0
              (Function.update ![σs t.1.2.1, σs t.1.2.2] t.2
                (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                    (I := I) gRef) (σs t.1.1.2) (![σs t.1.2.1, σs t.1.2.2] t.2))) (σs t.1.1.1) x| ≤
        C * (Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
              (covDerivOfField (I := I) gRef A0 (0 + 1) x
                - covDerivOfField (I := I) gRef A0' (0 + 1) x))
            + Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
              (covDerivOfField (I := I) gRef A0 0 x
                - covDerivOfField (I := I) gRef A0' 0 x))) :=
    fun t => towVal_le gRef x 0 _ (σs t.1.1.1)
  choose C1 hC10 hC1f using hC1
  choose C0 hC00 hC0f using hC0
  refine ⟨(∑ t, C1 t) + ∑ t, C0 t,
    add_nonneg (Finset.sum_nonneg fun t _ => hC10 t) (Finset.sum_nonneg fun t _ => hC00 t),
    fun u u' mm m i j => ?_⟩
  set dN2 : Real := metricDerivNorm (I := I) 2 u u' gRef x with hdN2
  set dN1 : Real := metricDerivNorm (I := I) 1 u u' gRef x with hdN1
  set dN0 : Real := metricDerivNorm (I := I) 0 u u' gRef x with hdN0
  have hdN2nn : 0 ≤ dN2 := Real.sqrt_nonneg _
  have hdN1nn : 0 ≤ dN1 := Real.sqrt_nonneg _
  have hdN0nn : 0 ≤ dN0 := Real.sqrt_nonneg _
  rw [gram_pd2_eq gRef x σs hσs u mm m i j, gram_pd2_eq gRef x σs hσs u' mm m i j]
  set T1 : Real := towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 1
    (Fin.cons (σs m) ![σs i, σs j]) (σs mm) x with hT1
  set T1' : Real := towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 1
    (Fin.cons (σs m) ![σs i, σs j]) (σs mm) x with hT1'
  have hsplit : T1 + (∑ a : Fin 2,
        towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
          (Function.update ![σs i, σs j] a
            (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x)
      - (T1' + ∑ a : Fin 2,
          towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 0
            (Function.update ![σs i, σs j] a
              (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                  (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x)
      = (T1 - T1') + ∑ a : Fin 2,
          (towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
              (Function.update ![σs i, σs j] a
                (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                    (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x
            - towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 0
                (Function.update ![σs i, σs j] a
                  (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                      (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 := hC1f ((mm, m), i, j) (Tensor0SBundle.metricTensorField (I := I) u)
    (Tensor0SBundle.metricTensorField (I := I) u')
  have hd2 : Real.sqrt (normSq0S (I := I) gRef x (1 + 1 + 2)
      (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) (1 + 1) x
        - covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') (1 + 1) x))
      = dN2 := rfl
  have hd1 : Real.sqrt (normSq0S (I := I) gRef x (1 + 2)
      (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 1 x
        - covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 1 x))
      = dN1 := rfl
  rw [hd2, hd1] at h1
  have h1' : |T1 - T1'| ≤ C1 ((mm, m), i, j) * (dN2 + dN1) := h1
  have h0 : ∀ a : Fin 2,
      |towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
          (Function.update ![σs i, σs j] a
            (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x
        - towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 0
            (Function.update ![σs i, σs j] a
              (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                  (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x| ≤
      C0 (((mm, m), i, j), a) * (dN1 + dN0) := by
    intro a
    have h := hC0f (((mm, m), i, j), a) (Tensor0SBundle.metricTensorField (I := I) u)
      (Tensor0SBundle.metricTensorField (I := I) u')
    have hda : Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
        (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) (0 + 1) x
          - covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') (0 + 1) x))
        = dN1 := rfl
    have hdb : Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
        (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0 x
          - covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 0 x))
        = dN0 := rfl
    rwa [hda, hdb] at h
  have hsum0 : |∑ a : Fin 2,
      (towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
          (Function.update ![σs i, σs j] a
            (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x
        - towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u') 0
            (Function.update ![σs i, σs j] a
              (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                  (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x)| ≤
      (∑ a : Fin 2, C0 (((mm, m), i, j), a)) * (dN1 + dN0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun a _ => h0 a
  have hC1le : C1 ((mm, m), i, j) ≤ ∑ t, C1 t :=
    Finset.single_le_sum (fun t _ => hC10 t) (Finset.mem_univ _)
  have hC0le : ∑ a : Fin 2, C0 (((mm, m), i, j), a) ≤ ∑ t, C0 t := by
    calc ∑ a : Fin 2, C0 (((mm, m), i, j), a)
        = ∑ t ∈ Finset.univ.image (fun a : Fin 2 => (((mm, m), i, j), a)), C0 t := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          simpa using hab
      _ ≤ ∑ t, C0 t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun t _ _ => hC00 t)
  calc |T1 - T1'| + |∑ a : Fin 2, _| ≤
      C1 ((mm, m), i, j) * (dN2 + dN1)
        + (∑ a : Fin 2, C0 (((mm, m), i, j), a)) * (dN1 + dN0) := add_le_add h1' hsum0
    _ ≤ (∑ t, C1 t) * (dN2 + dN1 + dN0) + (∑ t, C0 t) * (dN2 + dN1 + dN0) := by
        have hs1 : 0 ≤ ∑ t, C1 t := Finset.sum_nonneg fun t _ => hC10 t
        have hs0 : 0 ≤ ∑ t, C0 t := Finset.sum_nonneg fun t _ => hC00 t
        have hb1 : C1 ((mm, m), i, j) * (dN2 + dN1) ≤ (∑ t, C1 t) * (dN2 + dN1 + dN0) := by
          have := hC10 ((mm, m), i, j)
          nlinarith
        have hb0 : (∑ a : Fin 2, C0 (((mm, m), i, j), a)) * (dN1 + dN0)
            ≤ (∑ t, C0 t) * (dN2 + dN1 + dN0) := by
          have hnn : 0 ≤ ∑ a : Fin 2, C0 (((mm, m), i, j), a) :=
            Finset.sum_nonneg fun a _ => hC00 _
          nlinarith
        linarith
    _ = ((∑ t, C1 t) + ∑ t, C0 t) * (dN2 + dN1 + dN0) := by ring

end JetExpansion

section JetEndpoints

variable (gRef : SmoothRiemannianMetric I M) (x : M)



omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [CompleteSpace E] [I.Boundaryless] [IsManifold I 2 M] in
private lemma exists_slotSections
    [Module.Finite ℝ E]
    :
    ∃ σs : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _),
      ∀ i, ∀ᶠ z in 𝓝ˢ ({x} : Set M),
        σs i z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) z := by
  classical
  have hσex : ∀ i : Fin (Module.finrank Real E),
      ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ∀ᶠ z in 𝓝ˢ ({x} : Set M),
          σ z = tangentConstInChart (𝕜 := Real) (I := I) x ((chartModelBasis E) i) z :=
    fun i => exists_section_eqOn_compact (I := I) x ((chartModelBasis E) i)
      isCompact_singleton (Set.singleton_subset_iff.mpr (mem_chart_source H x))
  choose σs hσs using hσex
  exact ⟨σs, hσs⟩






omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
theorem jet2Diff_le_dNorm
    [Module.Finite ℝ E]
    :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      chartMetricJet2DiffSup (I := I) (M := M) u u' x (extChartAt I x x) ≤
        C * ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x := by
  classical
  obtain ⟨σs, hσs⟩ := exists_slotSections (I := I) x
  obtain ⟨C0, hC00, hC0⟩ := gram0_le gRef x
  obtain ⟨C1, hC10, hC1⟩ := gram1_le gRef x σs hσs
  obtain ⟨C2, hC20, hC2⟩ := gram2_le gRef x σs hσs
  set n2 : Real := (Fintype.card (Fin (Module.finrank Real E)
    × Fin (Module.finrank Real E)) : Real) with hn2
  set n3 : Real := (Fintype.card (Fin (Module.finrank Real E)
    × Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) : Real) with hn3
  set n4 : Real := (Fintype.card (Fin (Module.finrank Real E)
    × Fin (Module.finrank Real E) × Fin (Module.finrank Real E)
    × Fin (Module.finrank Real E)) : Real) with hn4
  have hn2nn : 0 ≤ n2 := Nat.cast_nonneg _
  have hn3nn : 0 ≤ n3 := Nat.cast_nonneg _
  have hn4nn : 0 ≤ n4 := Nat.cast_nonneg _
  refine ⟨n2 * C0 + n3 * C1 + n4 * C2 + 1, by positivity, fun u u' => ?_⟩
  set S : Real := ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x with hS
  have hSexp : S = metricDerivNorm (I := I) 0 u u' gRef x
      + metricDerivNorm (I := I) 1 u u' gRef x
      + metricDerivNorm (I := I) 2 u u' gRef x := by
    rw [hS, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hd0nn : 0 ≤ metricDerivNorm (I := I) 0 u u' gRef x := Real.sqrt_nonneg _
  have hd1nn : 0 ≤ metricDerivNorm (I := I) 1 u u' gRef x := Real.sqrt_nonneg _
  have hd2nn : 0 ≤ metricDerivNorm (I := I) 2 u u' gRef x := Real.sqrt_nonneg _
  have hSnn : 0 ≤ S := by rw [hSexp]; linarith
  have hS0 : metricDerivNorm (I := I) 0 u u' gRef x ≤ S := by rw [hSexp]; linarith
  have hS01 : metricDerivNorm (I := I) 1 u u' gRef x
      + metricDerivNorm (I := I) 0 u u' gRef x ≤ S := by rw [hSexp]; linarith
  have hS012 : metricDerivNorm (I := I) 2 u u' gRef x
      + metricDerivNorm (I := I) 1 u u' gRef x
      + metricDerivNorm (I := I) 0 u u' gRef x ≤ S := by rw [hSexp]; linarith
  have hψ : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hA : chartGramDiffSup (I := I) (M := M) u u' x
      ((extChartAt I x).symm (extChartAt I x x)) ≤ n2 * C0 * S := by
    rw [hψ]
    unfold chartGramDiffSup matrixEntryL1
    calc ∑ pq : Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
          |(chartGramMatrix (I := I) u x x - chartGramMatrix (I := I) u' x x) pq.1 pq.2|
        ≤ ∑ _pq : Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
            C0 * S := by
          refine Finset.sum_le_sum fun pq _ => ?_
          rw [Matrix.sub_apply]
          refine (hC0 u u' pq.1 pq.2).trans ?_
          exact mul_le_mul_of_nonneg_left hS0 hC00
      _ = n2 * (C0 * S) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = n2 * C0 * S := by ring
  have hB : chartGramPartialDiffSup (I := I) (M := M) u u' x (extChartAt I x x)
      ≤ n3 * C1 * S := by
    unfold chartGramPartialDiffSup gramPartialDiffEntry
    calc ∑ p : Fin (Module.finrank Real E) × Fin (Module.finrank Real E)
          × Fin (Module.finrank Real E),
          |partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u x p.1 p.2.2)
              (extChartAt I x x)
            - partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u' x p.1 p.2.2)
              (extChartAt I x x)|
        ≤ ∑ _p : Fin (Module.finrank Real E) × Fin (Module.finrank Real E)
            × Fin (Module.finrank Real E), C1 * S := by
          refine Finset.sum_le_sum fun p _ => ?_
          refine (hC1 u u' p.2.1 p.1 p.2.2).trans ?_
          exact mul_le_mul_of_nonneg_left hS01 hC10
      _ = n3 * (C1 * S) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = n3 * C1 * S := by ring
  have hCc : chartGramPartial2DiffSup (I := I) (M := M) u u' x (extChartAt I x x)
      ≤ n4 * C2 * S := by
    unfold chartGramPartial2DiffSup gramPartial2DiffEntry
    calc ∑ p : Fin (Module.finrank Real E) × Fin (Module.finrank Real E)
          × Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
          |partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u x p.2.2.1 p.2.2.2))
              (extChartAt I x x)
            - partialDeriv (E := E) p.1
                (partialDeriv (E := E) p.2.1 (chartGramOnE (I := I) u' x p.2.2.1 p.2.2.2))
                (extChartAt I x x)|
        ≤ ∑ _p : Fin (Module.finrank Real E) × Fin (Module.finrank Real E)
            × Fin (Module.finrank Real E) × Fin (Module.finrank Real E), C2 * S := by
          refine Finset.sum_le_sum fun p _ => ?_
          refine (hC2 u u' p.1 p.2.1 p.2.2.1 p.2.2.2).trans ?_
          exact mul_le_mul_of_nonneg_left hS012 hC20
      _ = n4 * (C2 * S) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = n4 * C2 * S := by ring
  unfold chartMetricJet2DiffSup chartMetricJet1DiffSup
  calc chartGramDiffSup (I := I) (M := M) u u' x
        ((extChartAt I x).symm (extChartAt I x x))
      + chartGramPartialDiffSup (I := I) (M := M) u u' x (extChartAt I x x)
      + chartGramPartial2DiffSup (I := I) (M := M) u u' x (extChartAt I x x)
      ≤ n2 * C0 * S + n3 * C1 * S + n4 * C2 * S := by
        exact add_le_add (add_le_add hA hB) hCc
    _ ≤ (n2 * C0 + n3 * C1 + n4 * C2 + 1) * S := by nlinarith





omit [Module.Finite ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [IsManifold I 2 M] in
theorem gramJet_le_covNorm
    [Module.Finite ℝ E]
    :
    ∃ C : Real, 0 < C ∧ ∀ u : SmoothRiemannianMetric I M,
      (∀ m i j : Fin (Module.finrank Real E),
        |partialDeriv (E := E) m (chartGramOnE (I := I) u x i j) (extChartAt I x x)| ≤
          C * ∑ a ∈ Finset.range 3, metricCovDerivNorm (I := I) a u gRef x)
      ∧ (∀ mm m i j : Fin (Module.finrank Real E),
        |partialDeriv (E := E) mm
            (partialDeriv (E := E) m (chartGramOnE (I := I) u x i j))
            (extChartAt I x x)| ≤
          C * ∑ a ∈ Finset.range 3, metricCovDerivNorm (I := I) a u gRef x) := by
  classical
  obtain ⟨σs, hσs⟩ := exists_slotSections (I := I) x

  have hK1 : ∀ t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E)
      × Fin (Module.finrank Real E), ∃ C : Real, 0 ≤ C ∧
      ∀ A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 0 ![σs t.2.1, σs t.2.2] (σs t.1) x| ≤
        C * (Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
              (covDerivOfField (I := I) gRef A0 (0 + 1) x))
            + Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
              (covDerivOfField (I := I) gRef A0 0 x))) :=
    fun t => towVal_le' gRef x 0 ![σs t.2.1, σs t.2.2] (σs t.1)

  have hK2 : ∀ t : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E))
      × Fin (Module.finrank Real E) × Fin (Module.finrank Real E), ∃ C : Real, 0 ≤ C ∧
      ∀ A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 1 (Fin.cons (σs t.1.2) ![σs t.2.1, σs t.2.2]) (σs t.1.1) x| ≤
        C * (Real.sqrt (normSq0S (I := I) gRef x (1 + 1 + 2)
              (covDerivOfField (I := I) gRef A0 (1 + 1) x))
            + Real.sqrt (normSq0S (I := I) gRef x (1 + 2)
              (covDerivOfField (I := I) gRef A0 1 x))) :=
    fun t => towVal_le' gRef x 1 (Fin.cons (σs t.1.2) ![σs t.2.1, σs t.2.2]) (σs t.1.1)

  have hK0 : ∀ t : ((Fin (Module.finrank Real E) × Fin (Module.finrank Real E))
      × Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) × Fin 2,
      ∃ C : Real, 0 ≤ C ∧
      ∀ A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
        |towerStep (I := I) gRef A0 0
            (Function.update ![σs t.1.2.1, σs t.1.2.2] t.2
              (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                  (I := I) gRef) (σs t.1.1.2) (![σs t.1.2.1, σs t.1.2.2] t.2))) (σs t.1.1.1) x| ≤
        C * (Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
              (covDerivOfField (I := I) gRef A0 (0 + 1) x))
            + Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
              (covDerivOfField (I := I) gRef A0 0 x))) :=
    fun t => towVal_le' gRef x 0 _ (σs t.1.1.1)
  choose K1 hK10 hK1f using hK1
  choose K2 hK20 hK2f using hK2
  choose K0 hK00 hK0f using hK0
  refine ⟨(∑ t, K1 t) + ((∑ t, K2 t) + ∑ t, K0 t) + 1, by
    have h1 : 0 ≤ ∑ t, K1 t := Finset.sum_nonneg fun t _ => hK10 t
    have h2 : 0 ≤ ∑ t, K2 t := Finset.sum_nonneg fun t _ => hK20 t
    have h0 : 0 ≤ ∑ t, K0 t := Finset.sum_nonneg fun t _ => hK00 t
    linarith, fun u => ?_⟩
  set cS : Real := ∑ a ∈ Finset.range 3, metricCovDerivNorm (I := I) a u gRef x with hcS
  have hcSexp : cS = metricCovDerivNorm (I := I) 0 u gRef x
      + metricCovDerivNorm (I := I) 1 u gRef x
      + metricCovDerivNorm (I := I) 2 u gRef x := by
    rw [hcS, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hc0nn : 0 ≤ metricCovDerivNorm (I := I) 0 u gRef x := Real.sqrt_nonneg _
  have hc1nn : 0 ≤ metricCovDerivNorm (I := I) 1 u gRef x := Real.sqrt_nonneg _
  have hc2nn : 0 ≤ metricCovDerivNorm (I := I) 2 u gRef x := Real.sqrt_nonneg _
  have hcSnn : 0 ≤ cS := by rw [hcSexp]; linarith
  have hK1sum : 0 ≤ ∑ t, K1 t := Finset.sum_nonneg fun t _ => hK10 t
  have hK2sum : 0 ≤ ∑ t, K2 t := Finset.sum_nonneg fun t _ => hK20 t
  have hK0sum : 0 ≤ ∑ t, K0 t := Finset.sum_nonneg fun t _ => hK00 t
  constructor
  · intro m i j
    rw [gram_pd_eq gRef x σs hσs u m i j]
    have h := hK1f (m, i, j) (Tensor0SBundle.metricTensorField (I := I) u)
    have hda : Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
        (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) (0 + 1) x))
        = metricCovDerivNorm (I := I) 1 u gRef x := rfl
    have hdb : Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
        (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0 x))
        = metricCovDerivNorm (I := I) 0 u gRef x := rfl
    rw [hda, hdb] at h
    refine h.trans ?_
    have hle : K1 (m, i, j) ≤ (∑ t, K1 t) + ((∑ t, K2 t) + ∑ t, K0 t) + 1 := by
      have := Finset.single_le_sum (fun t _ => hK10 t) (Finset.mem_univ (m, i, j))
      linarith
    have hcle : metricCovDerivNorm (I := I) 1 u gRef x
        + metricCovDerivNorm (I := I) 0 u gRef x ≤ cS := by rw [hcSexp]; linarith
    have hbnn : 0 ≤ metricCovDerivNorm (I := I) 1 u gRef x
        + metricCovDerivNorm (I := I) 0 u gRef x := by linarith
    have hBnn : 0 ≤ (∑ t, K1 t) + ((∑ t, K2 t) + ∑ t, K0 t) + 1 := by linarith
    exact mul_le_mul hle hcle hbnn hBnn
  · intro mm m i j
    rw [gram_pd2_eq gRef x σs hσs u mm m i j]
    refine (abs_add_le _ _).trans ?_
    have h2 := hK2f ((mm, m), i, j) (Tensor0SBundle.metricTensorField (I := I) u)
    have hda2 : Real.sqrt (normSq0S (I := I) gRef x (1 + 1 + 2)
        (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) (1 + 1) x))
        = metricCovDerivNorm (I := I) 2 u gRef x := rfl
    have hdb2 : Real.sqrt (normSq0S (I := I) gRef x (1 + 2)
        (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 1 x))
        = metricCovDerivNorm (I := I) 1 u gRef x := rfl
    rw [hda2, hdb2] at h2
    have h0 : |∑ a : Fin 2,
        towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
          (Function.update ![σs i, σs j] a
            (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x| ≤
        (∑ a : Fin 2, K0 (((mm, m), i, j), a))
          * (metricCovDerivNorm (I := I) 1 u gRef x
              + metricCovDerivNorm (I := I) 0 u gRef x) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun a _ => ?_
      have h := hK0f (((mm, m), i, j), a) (Tensor0SBundle.metricTensorField (I := I) u)
      have hda : Real.sqrt (normSq0S (I := I) gRef x (0 + 1 + 2)
          (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) (0 + 1) x))
          = metricCovDerivNorm (I := I) 1 u gRef x := rfl
      have hdb : Real.sqrt (normSq0S (I := I) gRef x (0 + 2)
          (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0 x))
          = metricCovDerivNorm (I := I) 0 u gRef x := rfl
      rwa [hda, hdb] at h
    have hK2le : K2 ((mm, m), i, j) ≤ ∑ t, K2 t :=
      Finset.single_le_sum (fun t _ => hK20 t) (Finset.mem_univ _)
    have hK0le : ∑ a : Fin 2, K0 (((mm, m), i, j), a) ≤ ∑ t, K0 t := by
      calc ∑ a : Fin 2, K0 (((mm, m), i, j), a)
          = ∑ t ∈ Finset.univ.image (fun a : Fin 2 => (((mm, m), i, j), a)), K0 t := by
            rw [Finset.sum_image]
            intro a _ b _ hab
            simpa using hab
        _ ≤ ∑ t, K0 t :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun t _ _ => hK00 t)
    have hK0ann : 0 ≤ ∑ a : Fin 2, K0 (((mm, m), i, j), a) :=
      Finset.sum_nonneg fun a _ => hK00 _
    calc |towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 1
            (Fin.cons (σs m) ![σs i, σs j]) (σs mm) x|
          + |∑ a : Fin 2,
              towerStep (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) u) 0
                (Function.update ![σs i, σs j] a
                  (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                      (I := I) gRef) (σs m) (![σs i, σs j] a))) (σs mm) x|
        ≤ K2 ((mm, m), i, j) * (metricCovDerivNorm (I := I) 2 u gRef x
              + metricCovDerivNorm (I := I) 1 u gRef x)
            + (∑ a : Fin 2, K0 (((mm, m), i, j), a))
              * (metricCovDerivNorm (I := I) 1 u gRef x
                  + metricCovDerivNorm (I := I) 0 u gRef x) := add_le_add h2 h0
      _ ≤ ((∑ t, K1 t) + ((∑ t, K2 t) + ∑ t, K0 t) + 1) * cS := by
          have h1 := hK20 ((mm, m), i, j)
          rw [hcSexp]
          nlinarith

end JetEndpoints



section InvGram

open Matrix

variable (gRef : SmoothRiemannianMetric I M) (x : M)


omit [Module.Finite ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma gram_quad_low
    [Module.Finite ℝ E]
    :
    ∃ c0 : Real, 0 < c0 ∧ ∀ ξ : Fin (Module.finrank Real E) → Real,
      c0 * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ (chartGramMatrix (I := I) gRef x x) *ᵥ ξ := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  set f : (Fin (Module.finrank Real E) → Real) → Real :=
    fun ξ => ξ ⬝ᵥ (chartGramMatrix (I := I) gRef x x) *ᵥ ξ with hf
  have hfeq : ∀ ξ : Fin (Module.finrank Real E) → Real, f ξ =
      gRef.inner x (∑ i, ξ i • chartBasisVecFiber (I := I) x i x)
        (∑ j, ξ j • chartBasisVecFiber (I := I) x j x) := by
    intro ξ
    have h := chartGramMatrix_dotProduct_mulVec (I := I) gRef x x ξ
    have hstar : star ξ = ξ := funext fun i => by simp
    rw [hstar] at h
    exact h
  have hfpos : ∀ ξ : Fin (Module.finrank Real E) → Real, ξ ≠ 0 → 0 < f ξ := by
    intro ξ hξ
    rw [hfeq]
    set w := ∑ i, ξ i • chartBasisVecFiber (I := I) x i x with hw
    have hwnz : w ≠ 0 := by
      intro hw0
      have hli := chartBasisFamily_linearIndependent (I := I) x hxbase
      rw [Fintype.linearIndependent_iff] at hli
      exact hξ (funext (hli ξ hw0))
    exact gRef.pos x w hwnz
  have hfcont : Continuous f := by
    have hfe : f = fun ξ : Fin (Module.finrank Real E) → Real =>
        ∑ i, ξ i * ∑ j, chartGramMatrix (I := I) gRef x x i j * ξ j := by
      funext ξ
      simp [hf, dotProduct, Matrix.mulVec]
    rw [hfe]
    exact continuous_finset_sum _ fun i _ =>
      (continuous_apply i).mul (continuous_finset_sum _ fun j _ =>
        continuous_const.mul (continuous_apply j))
  have hg0cont : Continuous fun ξ : Fin (Module.finrank Real E) → Real => ξ ⬝ᵥ ξ := by
    have hge : (fun ξ : Fin (Module.finrank Real E) → Real => ξ ⬝ᵥ ξ)
        = fun ξ => ∑ i, ξ i * ξ i := by
      funext ξ; simp [dotProduct]
    rw [hge]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i)
  set S : Set (Fin (Module.finrank Real E) → Real) := {ξ | ξ ⬝ᵥ ξ = 1} with hSdef
  have hSclosed : IsClosed S := by
    have : S = (fun ξ : Fin (Module.finrank Real E) → Real => ξ ⬝ᵥ ξ) ⁻¹' {1} := rfl
    rw [this]
    exact IsClosed.preimage hg0cont isClosed_singleton
  have hSsub : S ⊆ Metric.closedBall 0 1 := by
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hsum : ξ i * ξ i ≤ 1 := by
      have h1 : ξ i * ξ i ≤ ∑ j, ξ j * ξ j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (ξ j)) (Finset.mem_univ i)
      have h2 : (∑ j, ξ j * ξ j) = 1 := hξ
      linarith
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (ξ i), sq_abs (ξ i), abs_mul_abs_self (ξ i)]
  have hScpt : IsCompact S :=
    (isCompact_closedBall (0 : Fin (Module.finrank Real E) → Real) 1).of_isClosed_subset
      hSclosed hSsub
  have hSne : S.Nonempty := by
    refine ⟨Pi.single (0 : Fin (Module.finrank Real E)) 1, ?_⟩
    change (Pi.single (0 : Fin (Module.finrank Real E)) (1 : Real))
      ⬝ᵥ (Pi.single (0 : Fin (Module.finrank Real E)) (1 : Real)) = 1
    simp [dotProduct, Pi.single_apply]
  obtain ⟨ξ0, hξ0S, hmin⟩ := hScpt.exists_isMinOn hSne hfcont.continuousOn
  have hξ0ne : ξ0 ≠ 0 := by
    intro h0
    have : (0 : Fin (Module.finrank Real E) → Real) ⬝ᵥ 0 = 1 := by
      rw [← h0]; exact hξ0S
    simp at this
  refine ⟨f ξ0, hfpos ξ0 hξ0ne, fun ξ => ?_⟩
  by_cases hz : ξ = 0
  · subst hz
    simp [hf]
  · have hnn : 0 ≤ ξ ⬝ᵥ ξ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hpos : 0 < ξ ⬝ᵥ ξ := by
      rcases eq_or_lt_of_le hnn with h0 | h
      · exfalso
        have hall := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_self_nonneg (ξ i))).mp h0.symm
        exact hz (funext fun i => mul_self_eq_zero.mp (hall i (Finset.mem_univ i)))
      · exact h
    set r : Real := Real.sqrt (ξ ⬝ᵥ ξ) with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = ξ ⬝ᵥ ξ := Real.sq_sqrt hnn
    have hξ'S : (r⁻¹ • ξ) ∈ S := by
      change (r⁻¹ • ξ) ⬝ᵥ (r⁻¹ • ξ) = 1
      rw [smul_dotProduct, dotProduct_smul]
      rw [smul_eq_mul, smul_eq_mul, ← mul_assoc]
      rw [show r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ by rw [sq]; rw [mul_inv]]
      rw [hr2]
      field_simp
    have hle : f ξ0 ≤ f (r⁻¹ • ξ) := hmin hξ'S
    have hfξ' : f (r⁻¹ • ξ) = (r ^ 2)⁻¹ * f ξ := by
      change (r⁻¹ • ξ) ⬝ᵥ (chartGramMatrix (I := I) gRef x x) *ᵥ (r⁻¹ • ξ)
        = (r ^ 2)⁻¹ * (ξ ⬝ᵥ (chartGramMatrix (I := I) gRef x x) *ᵥ ξ)
      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      rw [smul_eq_mul, smul_eq_mul, ← mul_assoc]
      rw [show r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ by rw [sq]; rw [mul_inv]]
    rw [hfξ'] at hle
    have hr2pos : 0 < r ^ 2 := by positivity
    calc f ξ0 * (ξ ⬝ᵥ ξ) ≤ ((r ^ 2)⁻¹ * f ξ) * (ξ ⬝ᵥ ξ) :=
          mul_le_mul_of_nonneg_right hle hnn
      _ = f ξ := by
          rw [← hr2]
          field_simp




omit [Module.Finite ℝ E] in
omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] in
theorem invGram_le_of_low
    [Module.Finite ℝ E]
    (lam : Real) (hlam : 0 < lam) :
    ∃ Mb : Real, 0 ≤ Mb ∧ ∀ u : SmoothRiemannianMetric I M,
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u.inner x ξ ξ) →
      ∀ k l : Fin (Module.finrank Real E),
        |chartInvGramMatrix (I := I) u x x k l| ≤ Mb := by
  classical
  obtain ⟨c0, hc0, hquad⟩ := gram_quad_low gRef x
  have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hμ : 0 < lam * c0 := by positivity
  refine ⟨(lam * c0)⁻¹, (inv_nonneg).mpr hμ.le, fun u hlow k l => ?_⟩
  have hdet : IsUnit (chartGramMatrix (I := I) u x x).det :=
    (chartGramMatrix_det_pos (I := I) u x hxbase).ne'.isUnit

  have hulow : ∀ ξ : Fin (Module.finrank Real E) → Real,
      lam * c0 * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ (chartGramMatrix (I := I) u x x) *ᵥ ξ := by
    intro ξ
    have hu := chartGramMatrix_dotProduct_mulVec (I := I) u x x ξ
    have hg := chartGramMatrix_dotProduct_mulVec (I := I) gRef x x ξ
    have hstar : star ξ = ξ := funext fun i => by simp
    rw [hstar] at hu hg
    calc lam * c0 * (ξ ⬝ᵥ ξ) = lam * (c0 * (ξ ⬝ᵥ ξ)) := by ring
      _ ≤ lam * (ξ ⬝ᵥ (chartGramMatrix (I := I) gRef x x) *ᵥ ξ) :=
          mul_le_mul_of_nonneg_left (hquad ξ) hlam.le
      _ = lam * gRef.inner x (∑ i, ξ i • chartBasisVecFiber (I := I) x i x)
            (∑ j, ξ j • chartBasisVecFiber (I := I) x j x) := by rw [hg]
      _ ≤ u.inner x (∑ i, ξ i • chartBasisVecFiber (I := I) x i x)
            (∑ j, ξ j • chartBasisVecFiber (I := I) x j x) := hlow _
      _ = ξ ⬝ᵥ (chartGramMatrix (I := I) u x x) *ᵥ ξ := hu.symm

  set η : Fin (Module.finrank Real E) → Real :=
    (chartGramMatrix (I := I) u x x)⁻¹ *ᵥ Pi.single l 1 with hη
  have hGη : (chartGramMatrix (I := I) u x x) *ᵥ η = Pi.single l 1 := by
    rw [hη, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hquadη : η ⬝ᵥ (chartGramMatrix (I := I) u x x) *ᵥ η = η l := by
    rw [hGη]
    simp [dotProduct, Pi.single_apply]
  have hηnn : 0 ≤ η ⬝ᵥ η := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  set N : Real := Real.sqrt (η ⬝ᵥ η) with hN
  have hN2 : N ^ 2 = η ⬝ᵥ η := Real.sq_sqrt hηnn
  have hNnn : 0 ≤ N := Real.sqrt_nonneg _
  have habs : ∀ p, |η p| ≤ N := by
    intro p
    rw [hN]
    refine Real.abs_le_sqrt ?_
    calc η p ^ 2 = η p * η p := sq (η p)
      _ ≤ ∑ i, η i * η i :=
          Finset.single_le_sum (fun i _ => mul_self_nonneg (η i)) (Finset.mem_univ p)
      _ = η ⬝ᵥ η := rfl
  have hkey : lam * c0 * N ^ 2 ≤ N := by
    have h1 := hulow η
    rw [hquadη] at h1
    calc lam * c0 * N ^ 2 = lam * c0 * (η ⬝ᵥ η) := by rw [hN2]
      _ ≤ η l := h1
      _ ≤ |η l| := le_abs_self _
      _ ≤ N := habs l
  have hNle : N ≤ (lam * c0)⁻¹ := by
    rcases eq_or_lt_of_le hNnn with h0 | hNpos
    · rw [← h0]
      positivity
    · have hmulN : (lam * c0) * N ≤ 1 := by
        have h2 : (lam * c0) * N * N ≤ 1 * N := by
          calc (lam * c0) * N * N = lam * c0 * N ^ 2 := by ring
            _ ≤ N := hkey
            _ = 1 * N := (one_mul N).symm
        exact le_of_mul_le_mul_right h2 hNpos
      calc N = (lam * c0)⁻¹ * ((lam * c0) * N) := by field_simp
        _ ≤ (lam * c0)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hmulN ((inv_nonneg).mpr hμ.le)
        _ = (lam * c0)⁻¹ := mul_one _
  have hentry : chartInvGramMatrix (I := I) u x x k l = η k := by
    rw [hη]
    show chartInvGramMatrix (I := I) u x x k l
      = ((chartGramMatrix (I := I) u x x)⁻¹ *ᵥ Pi.single l 1) k
    rw [chartInvGramMatrix]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hentry]
  exact (habs k).trans hNle

end InvGram



section RicciAssembly

variable (gRef : SmoothRiemannianMetric I M) (x : M)


private lemma abs_add_sub_le (A B C : Real) : |A + B - C| ≤ |A| + |B| + |C| := by
  calc |A + B - C| = |A + B + (-C)| := by ring_nf
    _ ≤ |A + B| + |(-C)| := abs_add_le _ _
    _ ≤ (|A| + |B|) + |(-C)| := by gcongr; exact abs_add_le _ _
    _ = |A| + |B| + |C| := by rw [abs_neg]





omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
theorem chartRicci_sub_le
    [Module.Finite ℝ E]
    (lam B : Real) (hlam : 0 < lam) (hB : 0 ≤ B) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u.inner x ξ ξ) →
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u'.inner x ξ ξ) →
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u gRef x ≤ B) →
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u' gRef x ≤ B) →
      ∀ i k : Fin (Module.finrank Real E),
        |chartRicciTensor (I := I) u x i k (extChartAt I x x)
          - chartRicciTensor (I := I) u' x i k (extChartAt I x x)| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) u u' x (extChartAt I x x) := by
  classical
  obtain ⟨CJ, hCJ0, hCJ⟩ := gramJet_le_covNorm gRef x
  obtain ⟨Mb, hMb0, hMb⟩ := invGram_le_of_low gRef x lam hlam
  have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hαtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)
  have hyInt : extChartAt I x x ∈ interior (extChartAt I x).target := by
    rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
    exact hαtgt
  have hψ : (extChartAt I x).symm (extChartAt I x x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)

  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnR0 : 0 ≤ nR := Nat.cast_nonneg _
  set Q : Real := CJ * (3 * B) with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  set P : Real := 3 * Q with hPdef
  have hP0 : 0 ≤ P := by positivity
  set Cinv : Real := nR ^ 2 * Mb ^ 2 with hCinvdef
  have hCinv0 : 0 ≤ Cinv := by positivity
  set D : Real := nR ^ 2 * (Mb ^ 2 * Q) with hDdef
  have hD0 : 0 ≤ D := by positivity
  set R : Real := 3 * Q with hRdef
  have hR0 : 0 ≤ R := by positivity
  set Mg : Real := (1 / 2) * nR * (Mb * P) with hMgdef
  have hMg0 : 0 ≤ Mg := by positivity
  set Cd : Real := nR ^ 2 * (2 * Cinv * Mb * Q + Mb ^ 2) with hCddef
  have hCd0 : 0 ≤ Cd := by positivity
  set Clip : Real := (1 / 2) * nR * (Cinv * P + 3 * Mb) with hClipdef
  have hClip0 : 0 ≤ Clip := by positivity
  set Cdiff : Real := (1 / 2) * nR * (Cd * P + 3 * D + Cinv * R + 3 * Mb) with hCdiffdef
  have hCdiff0 : 0 ≤ Cdiff := by positivity
  refine ⟨2 * nR * Cdiff + 4 * nR ^ 2 * Clip * Mg + 1, by positivity,
    fun u u' hlowu hlowu' hcovu hcovu' i k => ?_⟩

  have hcS : ∀ (w : SmoothRiemannianMetric I M),
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a w gRef x ≤ B) →
      (∑ a ∈ Finset.range 3, metricCovDerivNorm (I := I) a w gRef x) ≤ 3 * B := by
    intro w hw
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 := hw 0 (by norm_num)
    have h1 := hw 1 (by norm_num)
    have h2 := hw 2 (by norm_num)
    linarith

  have hQu : ∀ m a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) m (chartGramOnE (I := I) u x a b) (extChartAt I x x)| ≤ Q := by
    intro m a b
    refine ((hCJ u).1 m a b).trans ?_
    rw [hQdef]
    exact mul_le_mul_of_nonneg_left (hcS u hcovu) hCJ0.le
  have hQu' : ∀ m a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) m (chartGramOnE (I := I) u' x a b) (extChartAt I x x)| ≤ Q := by
    intro m a b
    refine ((hCJ u').1 m a b).trans ?_
    rw [hQdef]
    exact mul_le_mul_of_nonneg_left (hcS u' hcovu') hCJ0.le
  have hQQu : ∀ mm m a b : Fin (Module.finrank Real E),
      |partialDeriv (E := E) mm
        (partialDeriv (E := E) m (chartGramOnE (I := I) u x a b)) (extChartAt I x x)| ≤ Q := by
    intro mm m a b
    refine ((hCJ u).2 mm m a b).trans ?_
    rw [hQdef]
    exact mul_le_mul_of_nonneg_left (hcS u hcovu) hCJ0.le

  have hMbα : ∀ (w : SmoothRiemannianMetric I M),
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ w.inner x ξ ξ) →
      ∀ k' l : Fin (Module.finrank Real E),
        |chartInvGramOnE (I := I) w x k' l (extChartAt I x x)| ≤ Mb := by
    intro w hloww k' l
    rw [chartInvGramOnE_def, hψ]
    exact hMb w hloww k' l
  have hMbu := hMbα u hlowu
  have hMbu' := hMbα u' hlowu'

  have hCinvα : ∀ k' l : Fin (Module.finrank Real E),
      |chartInvGramOnE (I := I) u x k' l (extChartAt I x x)
        - chartInvGramOnE (I := I) u' x k' l (extChartAt I x x)| ≤
      Cinv * chartGramDiffSup (I := I) (M := M) u u' x
        ((extChartAt I x).symm (extChartAt I x x)) := by
    intro k' l
    rw [chartInvGramOnE_def, chartInvGramOnE_def, hψ]
    have h := chartInvGramMatrix_entry_sub_abs_le_gramDiffSup (I := I) (M := M) u u' x
      hxbase (fun p q => hMb u hlowu p q) (fun p q => hMb u' hlowu' p q) k' l
    rw [hCinvdef, hnR]
    exact h

  have hPu : ∀ i' j l : Fin (Module.finrank Real E),
      |gramBracket (I := I) u x i' j l (extChartAt I x x)| ≤ P := by
    intro i' j l
    have h := abs_add_sub_le
      (partialDeriv (E := E) i' (chartGramOnE (I := I) u x l j) (extChartAt I x x))
      (partialDeriv (E := E) j (chartGramOnE (I := I) u x l i') (extChartAt I x x))
      (partialDeriv (E := E) l (chartGramOnE (I := I) u x i' j) (extChartAt I x x))
    have hg : gramBracket (I := I) u x i' j l (extChartAt I x x)
        = partialDeriv (E := E) i' (chartGramOnE (I := I) u x l j) (extChartAt I x x)
          + partialDeriv (E := E) j (chartGramOnE (I := I) u x l i') (extChartAt I x x)
          - partialDeriv (E := E) l (chartGramOnE (I := I) u x i' j) (extChartAt I x x) := rfl
    rw [hg]
    refine h.trans ?_
    have h1 := hQu i' l j
    have h2 := hQu j l i'
    have h3 := hQu l i' j
    rw [hPdef]
    linarith

  have hRu : ∀ m i' j l : Fin (Module.finrank Real E),
      |gramBracketDeriv (I := I) u x m i' j l (extChartAt I x x)| ≤ R := by
    intro m i' j l
    have h := abs_add_sub_le
      (partialDeriv (E := E) m
        (partialDeriv (E := E) i' (chartGramOnE (I := I) u x l j)) (extChartAt I x x))
      (partialDeriv (E := E) m
        (partialDeriv (E := E) j (chartGramOnE (I := I) u x l i')) (extChartAt I x x))
      (partialDeriv (E := E) m
        (partialDeriv (E := E) l (chartGramOnE (I := I) u x i' j)) (extChartAt I x x))
    have hg : gramBracketDeriv (I := I) u x m i' j l (extChartAt I x x)
        = partialDeriv (E := E) m
            (partialDeriv (E := E) i' (chartGramOnE (I := I) u x l j)) (extChartAt I x x)
          + partialDeriv (E := E) m
              (partialDeriv (E := E) j (chartGramOnE (I := I) u x l i')) (extChartAt I x x)
          - partialDeriv (E := E) m
              (partialDeriv (E := E) l (chartGramOnE (I := I) u x i' j)) (extChartAt I x x) := rfl
    rw [hg]
    refine h.trans ?_
    have h1 := hQQu m i' l j
    have h2 := hQQu m j l i'
    have h3 := hQQu m l i' j
    rw [hRdef]
    linarith

  have hDu' : ∀ m k' l : Fin (Module.finrank Real E),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) u' x k' l) (extChartAt I x x)| ≤ D := by
    intro m k' l
    rw [partialDeriv_chartInvGramOnE_eq (I := I) u' x (extChartAt I x x) m k' l hyInt]
    rw [abs_neg]
    calc |∑ a : Fin (Module.finrank Real E), ∑ b : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) u' x k' a (extChartAt I x x) *
            chartInvGramOnE (I := I) u' x b l (extChartAt I x x) *
            partialDeriv (E := E) m (chartGramOnE (I := I) u' x a b) (extChartAt I x x)|
        ≤ ∑ a : Fin (Module.finrank Real E), |∑ b : Fin (Module.finrank Real E),
            chartInvGramOnE (I := I) u' x k' a (extChartAt I x x) *
              chartInvGramOnE (I := I) u' x b l (extChartAt I x x) *
              partialDeriv (E := E) m (chartGramOnE (I := I) u' x a b) (extChartAt I x x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin (Module.finrank Real E), nR * (Mb * Mb * Q) := by
          refine Finset.sum_le_sum fun a _ => ?_
          calc |∑ b : Fin (Module.finrank Real E),
                chartInvGramOnE (I := I) u' x k' a (extChartAt I x x) *
                  chartInvGramOnE (I := I) u' x b l (extChartAt I x x) *
                  partialDeriv (E := E) m (chartGramOnE (I := I) u' x a b) (extChartAt I x x)|
              ≤ ∑ b : Fin (Module.finrank Real E),
                  |chartInvGramOnE (I := I) u' x k' a (extChartAt I x x) *
                    chartInvGramOnE (I := I) u' x b l (extChartAt I x x) *
                    partialDeriv (E := E) m (chartGramOnE (I := I) u' x a b) (extChartAt I x x)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _b : Fin (Module.finrank Real E), Mb * Mb * Q := by
                refine Finset.sum_le_sum fun b _ => ?_
                rw [abs_mul, abs_mul]
                have hb1 := hMbu' k' a
                have hb2 := hMbu' b l
                have hb3 := hQu' m a b
                have habs1 : 0 ≤ |chartInvGramOnE (I := I) u' x k' a (extChartAt I x x)| :=
                  abs_nonneg _
                have habs2 : 0 ≤ |chartInvGramOnE (I := I) u' x b l (extChartAt I x x)| :=
                  abs_nonneg _
                have habs3 : 0 ≤ |partialDeriv (E := E) m
                    (chartGramOnE (I := I) u' x a b) (extChartAt I x x)| := abs_nonneg _
                exact mul_le_mul (mul_le_mul hb1 hb2 habs2 hMb0) hb3 habs3
                  (by positivity)
            _ = nR * (Mb * Mb * Q) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnR]
      _ = nR * (nR * (Mb * Mb * Q)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnR]
      _ = D := by rw [hDdef]; ring

  have hMgb : ∀ (w : SmoothRiemannianMetric I M),
      (∀ k' l : Fin (Module.finrank Real E),
        |chartInvGramOnE (I := I) w x k' l (extChartAt I x x)| ≤ Mb) →
      (∀ i' j l : Fin (Module.finrank Real E),
        |gramBracket (I := I) w x i' j l (extChartAt I x x)| ≤ P) →
      ∀ i' j k' : Fin (Module.finrank Real E),
        |chartChristoffel (I := I) w x i' j k' (extChartAt I x x)| ≤ Mg := by
    intro w hMbw hPw i' j k'
    rw [chartChristoffel_eq_sum_invGramOnE_bracket]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
    rw [hMgdef]
    rw [show (1 / 2 : Real) * nR * (Mb * P) = (1 / 2) * (nR * (Mb * P)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc |∑ l : Fin (Module.finrank Real E),
          chartInvGramOnE (I := I) w x k' l (extChartAt I x x) *
            gramBracket (I := I) w x i' j l (extChartAt I x x)|
        ≤ ∑ l : Fin (Module.finrank Real E),
            |chartInvGramOnE (I := I) w x k' l (extChartAt I x x) *
              gramBracket (I := I) w x i' j l (extChartAt I x x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin (Module.finrank Real E), Mb * P := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hMbw k' l) (hPw i' j l) (abs_nonneg _) hMb0
      _ = nR * (Mb * P) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnR]

  have hPu' : ∀ i' j l : Fin (Module.finrank Real E),
      |gramBracket (I := I) u' x i' j l (extChartAt I x x)| ≤ P := by
    intro i' j l
    have h := abs_add_sub_le
      (partialDeriv (E := E) i' (chartGramOnE (I := I) u' x l j) (extChartAt I x x))
      (partialDeriv (E := E) j (chartGramOnE (I := I) u' x l i') (extChartAt I x x))
      (partialDeriv (E := E) l (chartGramOnE (I := I) u' x i' j) (extChartAt I x x))
    have hg : gramBracket (I := I) u' x i' j l (extChartAt I x x)
        = partialDeriv (E := E) i' (chartGramOnE (I := I) u' x l j) (extChartAt I x x)
          + partialDeriv (E := E) j (chartGramOnE (I := I) u' x l i') (extChartAt I x x)
          - partialDeriv (E := E) l (chartGramOnE (I := I) u' x i' j) (extChartAt I x x) := rfl
    rw [hg]
    refine h.trans ?_
    have h1 := hQu' i' l j
    have h2 := hQu' j l i'
    have h3 := hQu' l i' j
    rw [hPdef]
    linarith
  have hMgu := hMgb u hMbu hPu
  have hMgu' := hMgb u' hMbu' hPu'

  have hCdα : ∀ (m k' l : Fin (Module.finrank Real E)),
      |partialDeriv (E := E) m (chartInvGramOnE (I := I) u x k' l) (extChartAt I x x)
        - partialDeriv (E := E) m (chartInvGramOnE (I := I) u' x k' l) (extChartAt I x x)| ≤
      Cd * chartMetricJet1DiffSup (I := I) (M := M) u u' x (extChartAt I x x) := by
    intro m k' l
    have h := partialDeriv_chartInvGramOnE_sub_abs_le (I := I) (M := M) u u' x hyInt
      hMb0 hQ0 hCinv0 hMbu hMbu' (fun m' a b => hQu m' a b) hCinvα m k' l
    rw [hCddef, hnR]
    exact h

  have hClipα : ∀ i' j k' : Fin (Module.finrank Real E),
      |chartChristoffel (I := I) u x i' j k' (extChartAt I x x)
        - chartChristoffel (I := I) u' x i' j k' (extChartAt I x x)| ≤
      Clip * chartMetricJet1DiffSup (I := I) (M := M) u u' x (extChartAt I x x) := by
    intro i' j k'
    have h := chartChristoffel_sub_abs_le (I := I) (M := M) u u' x
      hP0 hMb0 hMbu' hPu hCinvα hCinv0 i' j k'
    rw [hClipdef, hnR]
    exact h

  have hCdiffα : ∀ m i' j k' : Fin (Module.finrank Real E),
      |partialDeriv (E := E) m (chartChristoffel (I := I) u x i' j k') (extChartAt I x x)
        - partialDeriv (E := E) m (chartChristoffel (I := I) u' x i' j k') (extChartAt I x x)| ≤
      Cdiff * chartMetricJet2DiffSup (I := I) (M := M) u u' x (extChartAt I x x) := by
    intro m i' j k'
    have h := partialDeriv_chartChristoffel_sub_abs_le (I := I) (M := M) u u' x hyInt
      hCd0 hCinv0 hMb0 hP0 hD0 hR0 m i' j k'
      (fun k'' l => hCdα m k'' l) hMbu' hPu (fun k'' l => hDu' m k'' l)
      (fun i'' j' l => hRu m i'' j' l) hCinvα
    rw [hCdiffdef, hnR]
    exact h

  set jet2 : Real := chartMetricJet2DiffSup (I := I) (M := M) u u' x (extChartAt I x x)
    with hjet2def
  have hjet2nn : 0 ≤ jet2 := chartMetricJet2DiffSup_nonneg _ _ _ _
  have hjet1le : chartMetricJet1DiffSup (I := I) (M := M) u u' x (extChartAt I x x) ≤ jet2 :=
    chartMetricJet1DiffSup_le_jet2 (I := I) (M := M) u u' x (extChartAt I x x)
  have h2nd := chartRicciSecondOrderTerm_sub_abs_le (I := I) (M := M) u u' x
    hCdiffα i k
  have h1st := chartRicciFirstOrderTerm_sub_abs_le (I := I) (M := M) u u' x
    hClip0 hMg0 hClipα hMgu hMgu' i k
  have hsplit : chartRicciTensor (I := I) u x i k (extChartAt I x x)
      - chartRicciTensor (I := I) u' x i k (extChartAt I x x)
      = (chartRicciSecondOrderTerm (I := I) u x i k (extChartAt I x x)
          - chartRicciSecondOrderTerm (I := I) u' x i k (extChartAt I x x))
        + (chartRicciFirstOrderTerm (I := I) u x i k (extChartAt I x x)
            - chartRicciFirstOrderTerm (I := I) u' x i k (extChartAt I x x)) := by
    rw [chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) u x i k (extChartAt I x x),
      chartRicciTensor_eq_secondOrder_add_firstOrder (I := I) u' x i k (extChartAt I x x)]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1st' : |chartRicciFirstOrderTerm (I := I) u x i k (extChartAt I x x)
      - chartRicciFirstOrderTerm (I := I) u' x i k (extChartAt I x x)| ≤
      4 * nR ^ 2 * Clip * Mg * jet2 := by
    refine h1st.trans ?_
    rw [hnR]
    exact mul_le_mul_of_nonneg_left hjet1le (by positivity)
  have h2nd' : |chartRicciSecondOrderTerm (I := I) u x i k (extChartAt I x x)
      - chartRicciSecondOrderTerm (I := I) u' x i k (extChartAt I x x)| ≤
      2 * nR * Cdiff * jet2 := by
    refine h2nd.trans ?_
    rw [hnR]
  calc |chartRicciSecondOrderTerm (I := I) u x i k (extChartAt I x x)
        - chartRicciSecondOrderTerm (I := I) u' x i k (extChartAt I x x)|
      + |chartRicciFirstOrderTerm (I := I) u x i k (extChartAt I x x)
          - chartRicciFirstOrderTerm (I := I) u' x i k (extChartAt I x x)|
      ≤ 2 * nR * Cdiff * jet2 + 4 * nR ^ 2 * Clip * Mg * jet2 := add_le_add h2nd' h1st'
    _ ≤ (2 * nR * Cdiff + 4 * nR ^ 2 * Clip * Mg + 1) * jet2 := by nlinarith

end RicciAssembly



section Endpoints

variable (gRef : SmoothRiemannianMetric I M) (x : M)






omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
theorem ricciSub_le_dNorm
    [Module.Finite ℝ E]
    (lam B : Real) (hlam : 0 < lam) (hB : 0 ≤ B)
    (v w : TangentSpace I x) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u.inner x ξ ξ) →
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u'.inner x ξ ξ) →
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u gRef x ≤ B) →
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u' gRef x ≤ B) →
      |ricciTensor (I := I) u x v w - ricciTensor (I := I) u' x v w| ≤
        C * ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x := by
  classical
  obtain ⟨CR, hCR0, hCR⟩ := chartRicci_sub_le gRef x lam B hlam hB
  obtain ⟨CJ2, hCJ20, hCJ2⟩ := jet2Diff_le_dNorm gRef x
  set crep : Real := ∑ i : Fin (Module.finrank Real E),
    ∑ k : Fin (Module.finrank Real E),
      |((chartModelBasis E).repr v) k| * |((chartModelBasis E).repr w) i| with hcrep
  have hcrep0 : 0 ≤ crep :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨crep * (CR * CJ2) + 1, by positivity, fun u u' h1 h2 h3 h4 => ?_⟩
  set S : Real := ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x with hSd
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _
  have hjet : chartMetricJet2DiffSup (I := I) (M := M) u u' x (extChartAt I x x)
      ≤ CJ2 * S := hCJ2 u u'
  have hentry : ∀ i k : Fin (Module.finrank Real E),
      |chartRicciTensor (I := I) u x i k (extChartAt I x x)
        - chartRicciTensor (I := I) u' x i k (extChartAt I x x)| ≤ CR * (CJ2 * S) := by
    intro i k
    refine (hCR u u' h1 h2 h3 h4 i k).trans ?_
    exact mul_le_mul_of_nonneg_left hjet hCR0.le
  have hbru := ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I) u x
    (chartRiemannBasisIdentity_holds (I := I) u x) v w
  have hbru' := ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I) u' x
    (chartRiemannBasisIdentity_holds (I := I) u' x) v w
  rw [hbru, hbru']
  have hdiff : (∑ i : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          chartRicciTensor (I := I) u x i k (extChartAt I x x))
      - (∑ i : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
          ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
            chartRicciTensor (I := I) u' x i k (extChartAt I x x))
      = ∑ i : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
          ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
            (chartRicciTensor (I := I) u x i k (extChartAt I x x)
              - chartRicciTensor (I := I) u' x i k (extChartAt I x x)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hdiff]
  calc |∑ i : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          (chartRicciTensor (I := I) u x i k (extChartAt I x x)
            - chartRicciTensor (I := I) u' x i k (extChartAt I x x))|
      ≤ ∑ i : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
          |((chartModelBasis E).repr v) k| * |((chartModelBasis E).repr w) i|
            * (CR * (CJ2 * S)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_mul]
        refine mul_le_mul_of_nonneg_left (hentry i k) ?_
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = crep * (CR * (CJ2 * S)) := by
        rw [hcrep, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
    _ ≤ (crep * (CR * CJ2) + 1) * S := by nlinarith






omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
theorem ricciConv_of_dnConv
    [Module.Finite ℝ E]
    (gSeq : ℕ → Real → SmoothRiemannianMetric I M)
    (gInf : Real → SmoothRiemannianMetric I M)
    (β ψ lam B : Real) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hlowSeq : ∀ k : ℕ, ∀ t ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ ≤ (gSeq k t).inner x ξ ξ)
    (hlowInf : ∀ t ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ ≤ (gInf t).inner x ξ ξ)
    (hbddSeq : ∀ k : ℕ, ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gSeq k t) gRef x ≤ B)
    (hbddInf : ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gInf t) gRef x ≤ B)
    (hconv : ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ 2 →
        metricDerivNorm (I := I) a (gSeq k t) (gInf t) gRef x < ε)
    (v w : TangentSpace I x) :
    ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t ∈ Set.Icc β ψ,
      |ricciTensor (I := I) (gSeq k t) x v w - ricciTensor (I := I) (gInf t) x v w| < ε := by
  obtain ⟨C, hC0, hC⟩ := ricciSub_le_dNorm gRef x lam B hlam hB v w
  intro ε hε
  have hε' : 0 < ε / (3 * C + 1) := by positivity
  obtain ⟨k0, hk0⟩ := hconv (ε / (3 * C + 1)) hε'
  refine ⟨k0, fun k hk t ht => ?_⟩
  have hb := hC (gSeq k t) (gInf t) (hlowSeq k t ht) (hlowInf t ht)
    (hbddSeq k t ht) (hbddInf t ht)
  have hS : ∑ a ∈ Finset.range 3,
      metricDerivNorm (I := I) a (gSeq k t) (gInf t) gRef x
      < 3 * (ε / (3 * C + 1)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 := hk0 k hk t ht 0 (by norm_num)
    have h1 := hk0 k hk t ht 1 (by norm_num)
    have h2 := hk0 k hk t ht 2 (by norm_num)
    linarith
  have hlt : C * (∑ a ∈ Finset.range 3,
      metricDerivNorm (I := I) a (gSeq k t) (gInf t) gRef x)
      < C * (3 * (ε / (3 * C + 1))) := by
    exact mul_lt_mul_of_pos_left hS hC0
  have hfin : C * (3 * (ε / (3 * C + 1))) < ε := by
    have h2 : (3 * C + 1) * (ε / (3 * C + 1)) = ε := by
      field_simp
    nlinarith
  exact lt_of_le_of_lt hb (lt_trans hlt hfin)

end Endpoints










section ScalarEndpoints

variable (gRef : SmoothRiemannianMetric I M) (x : M)





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] in
private lemma invGram_sub_le
    [Module.Finite ℝ E]
    (lam : Real) (hlam : 0 < lam) :
    ∃ C : Real, 0 ≤ C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u.inner x ξ ξ) →
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u'.inner x ξ ξ) →
      ∀ i j : Fin (Module.finrank Real E),
        |chartInvGramMatrix (I := I) u x x i j - chartInvGramMatrix (I := I) u' x x i j|
          ≤ C * metricDerivNorm (I := I) 0 u u' gRef x := by
  classical
  obtain ⟨Mb, hMb0, hMb⟩ := invGram_le_of_low gRef x lam hlam
  obtain ⟨C0, hC00, hC0⟩ := gram0_le gRef x
  refine ⟨(Module.finrank Real E : Real) ^ 2 * (Mb * Mb * C0),
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hMb0 hMb0) hC00),
    fun u u' hlow hlow' i j => ?_⟩
  have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hdN0 : 0 ≤ metricDerivNorm (I := I) 0 u u' gRef x := Real.sqrt_nonneg _
  have hdetu : IsUnit (chartGramMatrix (I := I) u x x).det :=
    (chartGramMatrix_det_pos (I := I) u x hxbase).ne'.isUnit
  have hdetu' : IsUnit (chartGramMatrix (I := I) u' x x).det :=
    (chartGramMatrix_det_pos (I := I) u' x hxbase).ne'.isUnit
  have hunit : IsUnit (chartGramMatrix (I := I) u x x)
      ↔ IsUnit (chartGramMatrix (I := I) u' x x) :=
    iff_of_true ((Matrix.isUnit_iff_isUnit_det _).mpr hdetu)
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdetu')
  have hkey : chartInvGramMatrix (I := I) u x x - chartInvGramMatrix (I := I) u' x x
      = chartInvGramMatrix (I := I) u x x
          * (chartGramMatrix (I := I) u' x x - chartGramMatrix (I := I) u x x)
          * chartInvGramMatrix (I := I) u' x x := by
    simp only [chartInvGramMatrix]
    exact Matrix.inv_sub_inv hunit
  have hij : chartInvGramMatrix (I := I) u x x i j - chartInvGramMatrix (I := I) u' x x i j
      = (chartInvGramMatrix (I := I) u x x
          * (chartGramMatrix (I := I) u' x x - chartGramMatrix (I := I) u x x)
          * chartInvGramMatrix (I := I) u' x x) i j := by
    rw [← hkey, Matrix.sub_apply]
  have hΔ : ∀ p q : Fin (Module.finrank Real E),
      |(chartGramMatrix (I := I) u' x x - chartGramMatrix (I := I) u x x) p q|
        ≤ C0 * metricDerivNorm (I := I) 0 u u' gRef x := by
    intro p q
    rw [Matrix.sub_apply, abs_sub_comm]
    exact hC0 u u' p q
  have hterm : ∀ q : Fin (Module.finrank Real E),
      |(chartInvGramMatrix (I := I) u x x
          * (chartGramMatrix (I := I) u' x x - chartGramMatrix (I := I) u x x)) i q
        * chartInvGramMatrix (I := I) u' x x q j|
      ≤ ((Module.finrank Real E : Real)
          * (Mb * (C0 * metricDerivNorm (I := I) 0 u u' gRef x))) * Mb := by
    intro q
    rw [abs_mul]
    refine mul_le_mul ?_ (hMb u' hlow' q j) (abs_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hMb0 (mul_nonneg hC00 hdN0)))
    rw [Matrix.mul_apply]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hp : ∀ p : Fin (Module.finrank Real E),
        |chartInvGramMatrix (I := I) u x x i p
          * (chartGramMatrix (I := I) u' x x - chartGramMatrix (I := I) u x x) p q|
        ≤ Mb * (C0 * metricDerivNorm (I := I) 0 u u' gRef x) := by
      intro p
      rw [abs_mul]
      exact mul_le_mul (hMb u hlow i p) (hΔ p q) (abs_nonneg _) hMb0
    refine le_trans (Finset.sum_le_sum fun p _ => hp p) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hij, Matrix.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun q _ => hterm q) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)






omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
private lemma ricci_abs_le
    [Module.Finite ℝ E]
    (lam B : Real) (hlam : 0 < lam) (hB : 0 ≤ B)
    (v w : TangentSpace I x) :
    ∃ C : Real, 0 ≤ C ∧ ∀ u : SmoothRiemannianMetric I M,
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u.inner x ξ ξ) →
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u gRef x ≤ B) →
      |ricciTensor (I := I) u x v w| ≤ C := by
  classical
  set B0 : Real := max (metricCovDerivNorm (I := I) 0 gRef gRef x)
    (max (metricCovDerivNorm (I := I) 1 gRef gRef x)
      (metricCovDerivNorm (I := I) 2 gRef gRef x)) with hB0
  have hB00 : 0 ≤ B0 := by
    rw [hB0]
    exact le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hlam' : 0 < min lam 1 := lt_min hlam one_pos
  have hB' : 0 ≤ max B B0 := le_trans hB (le_max_left _ _)
  obtain ⟨CA, hCA0, hCA⟩ := ricciSub_le_dNorm gRef x (min lam 1) (max B B0) hlam' hB' v w
  have hCnn : 0 ≤ CA * (3 * (B + B0)) + |ricciTensor (I := I) gRef x v w| :=
    add_nonneg (mul_nonneg hCA0.le (by linarith)) (abs_nonneg _)
  refine ⟨CA * (3 * (B + B0)) + |ricciTensor (I := I) gRef x v w|, hCnn,
    fun u hlow hbdd => ?_⟩
  have hinner : ∀ ξ : TangentSpace I x, 0 ≤ gRef.inner x ξ ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ; simp
    · exact (gRef.pos x ξ hξ).le
  have h1 : ∀ ξ : TangentSpace I x, min lam 1 * gRef.inner x ξ ξ ≤ u.inner x ξ ξ := by
    intro ξ
    calc min lam 1 * gRef.inner x ξ ξ
        ≤ lam * gRef.inner x ξ ξ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (hinner ξ)
      _ ≤ u.inner x ξ ξ := hlow ξ
  have h2 : ∀ ξ : TangentSpace I x, min lam 1 * gRef.inner x ξ ξ ≤ gRef.inner x ξ ξ := by
    intro ξ
    calc min lam 1 * gRef.inner x ξ ξ
        ≤ 1 * gRef.inner x ξ ξ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (hinner ξ)
      _ = gRef.inner x ξ ξ := one_mul _
  have h3 : ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u gRef x ≤ max B B0 :=
    fun a ha => le_trans (hbdd a ha) (le_max_left _ _)
  have h5 : ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a gRef gRef x ≤ B0 := by
    intro a ha
    rw [hB0]
    have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    rcases ha' with rfl | rfl | rfl
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h4 : ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a gRef gRef x ≤ max B B0 :=
    fun a ha => le_trans (h5 a ha) (le_max_right _ _)
  have hsub := hCA u gRef h1 h2 h3 h4
  have hdsum : ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u gRef gRef x
      ≤ 3 * (B + B0) := by
    have hd : ∀ a : ℕ, a ≤ 2 →
        metricDerivNorm (I := I) a u gRef gRef x ≤ B + B0 := by
      intro a ha
      refine le_trans (derivNorm_le_cov_add (I := I) a u gRef gRef x) ?_
      exact add_le_add (hbdd a ha) (h5 a ha)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have hd0 := hd 0 (by norm_num)
    have hd1 := hd 1 (by norm_num)
    have hd2 := hd 2 (by norm_num)
    linarith
  have hR : ricciTensor (I := I) u x v w
      - ricciTensor (I := I) gRef x v w + ricciTensor (I := I) gRef x v w
      = ricciTensor (I := I) u x v w := by ring
  calc |ricciTensor (I := I) u x v w|
      = |ricciTensor (I := I) u x v w - ricciTensor (I := I) gRef x v w
          + ricciTensor (I := I) gRef x v w| := by rw [hR]
    _ ≤ |ricciTensor (I := I) u x v w - ricciTensor (I := I) gRef x v w|
          + |ricciTensor (I := I) gRef x v w| := abs_add_le _ _
    _ ≤ CA * (3 * (B + B0)) + |ricciTensor (I := I) gRef x v w| := by
        have hmul : CA * (∑ a ∈ Finset.range 3,
            metricDerivNorm (I := I) a u gRef gRef x) ≤ CA * (3 * (B + B0)) :=
          mul_le_mul_of_nonneg_left hdsum hCA0.le
        linarith [hsub]







omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
theorem scalarSub_le_dNorm
    [Module.Finite ℝ E]
    (lam B : Real) (hlam : 0 < lam) (hB : 0 ≤ B) :
    ∃ C : Real, 0 < C ∧ ∀ u u' : SmoothRiemannianMetric I M,
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u.inner x ξ ξ) →
      (∀ ξ : TangentSpace I x, lam * gRef.inner x ξ ξ ≤ u'.inner x ξ ξ) →
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u gRef x ≤ B) →
      (∀ a : ℕ, a ≤ 2 → metricCovDerivNorm (I := I) a u' gRef x ≤ B) →
      |metricScalarAt (I := I) u x - metricScalarAt (I := I) u' x| ≤
        C * ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x := by
  classical
  obtain ⟨Minv, hMinv0, hMinv⟩ := invGram_le_of_low gRef x lam hlam
  obtain ⟨Cd, hCd0, hCd⟩ := invGram_sub_le gRef x lam hlam
  choose CR hCR0 hCR using
    fun t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E) =>
      ricciSub_le_dNorm gRef x lam B hlam hB
        (chartBasisVecFiber (I := I) x t.1 x) (chartBasisVecFiber (I := I) x t.2 x)
  choose CA hCA0 hCA using
    fun t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E) =>
      ricci_abs_le gRef x lam B hlam hB
        (chartBasisVecFiber (I := I) x t.1 x) (chartBasisVecFiber (I := I) x t.2 x)
  have hsum0 : 0 ≤ ∑ t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
      (CA t * Cd + Minv * CR t) :=
    Finset.sum_nonneg fun t _ =>
      add_nonneg (mul_nonneg (hCA0 t) hCd0) (mul_nonneg hMinv0 (hCR0 t).le)
  refine ⟨(∑ t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
      (CA t * Cd + Minv * CR t)) + 1, by linarith, fun u u' h1 h2 h3 h4 => ?_⟩
  have hS0 : 0 ≤ ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x :=
    Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _
  have hdN0 : 0 ≤ metricDerivNorm (I := I) 0 u u' gRef x := Real.sqrt_nonneg _
  have hd0S : metricDerivNorm (I := I) 0 u u' gRef x
      ≤ ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x :=
    Finset.single_le_sum
      (f := fun a => metricDerivNorm (I := I) a u u' gRef x)
      (fun a _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by norm_num))
  have hbr : ∀ (g : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank Real E)),
      chartInvGramOnE (I := I) g x i j (extChartAt I x x)
        = chartInvGramMatrix (I := I) g x x i j := by
    intro g i j
    rw [chartInvGramOnE_def, extChartAt_to_inv]
  rw [PDE.RicciFlow.metricScalar_chartTrace_eq (I := I) u x
      (self_mem_chartLeviCivitaGoodSet (I := I) x),
    PDE.RicciFlow.metricScalar_chartTrace_eq (I := I) u' x
      (self_mem_chartLeviCivitaGoodSet (I := I) x)]
  simp only [hbr]
  have hdiff : (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) u x x i j * ricciTensor (I := I) u x
          (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x))
      - (∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          chartInvGramMatrix (I := I) u' x x i j * ricciTensor (I := I) u' x
            (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x))
      = ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
          ((chartInvGramMatrix (I := I) u x x i j - chartInvGramMatrix (I := I) u' x x i j)
              * ricciTensor (I := I) u x
                (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)
            + chartInvGramMatrix (I := I) u' x x i j
              * (ricciTensor (I := I) u x
                  (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)
                - ricciTensor (I := I) u' x
                  (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdiff]
  have hterm : ∀ i j : Fin (Module.finrank Real E),
      |(chartInvGramMatrix (I := I) u x x i j - chartInvGramMatrix (I := I) u' x x i j)
          * ricciTensor (I := I) u x
            (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)
        + chartInvGramMatrix (I := I) u' x x i j
          * (ricciTensor (I := I) u x
              (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)
            - ricciTensor (I := I) u' x
              (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x))|
      ≤ (CA (i, j) * Cd + Minv * CR (i, j))
          * ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x := by
    intro i j
    have e1 : |(chartInvGramMatrix (I := I) u x x i j
          - chartInvGramMatrix (I := I) u' x x i j)
        * ricciTensor (I := I) u x
          (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)|
        ≤ (Cd * metricDerivNorm (I := I) 0 u u' gRef x) * CA (i, j) := by
      rw [abs_mul]
      exact mul_le_mul (hCd u u' h1 h2 i j) (hCA (i, j) u h1 h3) (abs_nonneg _)
        (mul_nonneg hCd0 hdN0)
    have e2 : |chartInvGramMatrix (I := I) u' x x i j
        * (ricciTensor (I := I) u x
            (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x)
          - ricciTensor (I := I) u' x
            (chartBasisVecFiber (I := I) x i x) (chartBasisVecFiber (I := I) x j x))|
        ≤ Minv * (CR (i, j)
            * ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x) := by
      rw [abs_mul]
      exact mul_le_mul (hMinv u' h2 i j) (hCR (i, j) u u' h1 h2 h3 h4)
        (abs_nonneg _) hMinv0
    refine le_trans (abs_add_le _ _) ?_
    have e3 := mul_le_mul_of_nonneg_left hd0S (mul_nonneg (hCA0 (i, j)) hCd0)
    nlinarith [e1, e2, e3]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => hterm i j) ?_
  have hEq : ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
      (CA (i, j) * Cd + Minv * CR (i, j))
        * ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x
      = (∑ t : Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
          (CA t * Cd + Minv * CR t))
        * ∑ a ∈ Finset.range 3, metricDerivNorm (I := I) a u u' gRef x := by
    rw [Finset.sum_mul, Fintype.sum_prod_type]
  rw [hEq]
  exact mul_le_mul_of_nonneg_right (by linarith) hS0






omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] in
theorem scalarConv_of_dnConv
    [Module.Finite ℝ E]
    (gSeq : ℕ → Real → SmoothRiemannianMetric I M)
    (gInf : Real → SmoothRiemannianMetric I M)
    (β ψ lam B : Real) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hlowSeq : ∀ k : ℕ, ∀ t ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ ≤ (gSeq k t).inner x ξ ξ)
    (hlowInf : ∀ t ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * gRef.inner x ξ ξ ≤ (gInf t).inner x ξ ξ)
    (hbddSeq : ∀ k : ℕ, ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gSeq k t) gRef x ≤ B)
    (hbddInf : ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gInf t) gRef x ≤ B)
    (hconv : ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ t ∈ Set.Icc β ψ, ∀ a : ℕ, a ≤ 2 →
        metricDerivNorm (I := I) a (gSeq k t) (gInf t) gRef x < ε) :
    ∀ ε : Real, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ t ∈ Set.Icc β ψ,
      |metricScalarAt (I := I) (gSeq k t) x - metricScalarAt (I := I) (gInf t) x| < ε := by
  obtain ⟨C, hC0, hC⟩ := scalarSub_le_dNorm gRef x lam B hlam hB
  intro ε hε
  have hε' : 0 < ε / (3 * C + 1) := by positivity
  obtain ⟨k0, hk0⟩ := hconv (ε / (3 * C + 1)) hε'
  refine ⟨k0, fun k hk t ht => ?_⟩
  have hb := hC (gSeq k t) (gInf t) (hlowSeq k t ht) (hlowInf t ht)
    (hbddSeq k t ht) (hbddInf t ht)
  have hS : ∑ a ∈ Finset.range 3,
      metricDerivNorm (I := I) a (gSeq k t) (gInf t) gRef x
      < 3 * (ε / (3 * C + 1)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 := hk0 k hk t ht 0 (by norm_num)
    have h1 := hk0 k hk t ht 1 (by norm_num)
    have h2 := hk0 k hk t ht 2 (by norm_num)
    linarith
  have hlt : C * (∑ a ∈ Finset.range 3,
      metricDerivNorm (I := I) a (gSeq k t) (gInf t) gRef x)
      < C * (3 * (ε / (3 * C + 1))) := by
    exact mul_lt_mul_of_pos_left hS hC0
  have hfin : C * (3 * (ε / (3 * C + 1))) < ε := by
    have h2 : (3 * C + 1) * (ε / (3 * C + 1)) = ε := by
      field_simp
    nlinarith
  exact lt_of_le_of_lt hb (lt_trans hlt hfin)

end ScalarEndpoints

end HCGCompactness
end DifferentialGeometry
