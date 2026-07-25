import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTimeDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBoundGoodFrame
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.MetricCovDerivProducer
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Analysis.Calculus.PartialDerivIteratedFDerivOrderBridge
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Geometry.Operator.Hessian
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivContinuity

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false

































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle TensorLieDeriv
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]







omit [CompleteSpace E] in
theorem opNorm_le_sum_coord {n : ℕ}
    (bE : Module.Basis (Fin n) Real E) (L : E →L[Real] Real) :
    ‖L‖ ≤ ∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖ * |L (bE i)| := by
  have hL : L = ∑ i : Fin n, (L (bE i)) • LinearMap.toContinuousLinearMap (bE.coord i) := by
    ext w
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← bE.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  calc ‖L‖
      = ‖∑ i : Fin n, (L (bE i)) • LinearMap.toContinuousLinearMap (bE.coord i)‖ := by rw [← hL]
    _ ≤ ∑ i : Fin n, ‖(L (bE i)) • LinearMap.toContinuousLinearMap (bE.coord i)‖ :=
        norm_sum_le _ _
    _ = ∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖ * |L (bE i)| := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, mul_comm]






omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] in
theorem exists_ON_tangentBasis (gRef : SmoothRiemannianMetric I M) (y : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I y),
      ∀ i j, gRef.inner y (b i) (b j) = if i = j then (1 : Real) else 0 := by
  obtain ⟨basisE, hON⟩ := exists_trivONBasis (I := I) gRef y
  set e := trivializationAt E (TangentSpace I : M → Type _) y with he
  have hy : y ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
  refine ⟨(e.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hy, fun i j => ?_⟩
  rw [IsLocalFrameOn.toBasisAt_coe, IsLocalFrameOn.toBasisAt_coe]
  exact hON i j








omit [CompleteSpace E] [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem exists_section_eqOn_compact
    (x₀ : M) (v : E) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) :
    ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : NormalSpace M := inferInstance
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀ with he
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := Real) (I := I) x₀
  have hKbase : Kc ⊆ e.baseSet := by rw [hbase]; exact hKchart
  have hUopen : IsOpen e.baseSet := e.open_baseSet
  have hKclosed : IsClosed Kc := hKc.isClosed
  obtain ⟨W, hWopen, hKW, hWU⟩ := normal_exists_closure_subset hKclosed hUopen hKbase
  have hKintW : Kc ⊆ interior W := by rw [hWopen.interior_eq]; exact hKW
  obtain ⟨χ, hχ_one, hχ_zero, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := M)
      (n := (⊤ : ℕ∞)) hKclosed hKintW
  have htsupp : tsupport (χ : M → Real) ⊆ e.baseSet := by
    refine subset_trans (closure_mono ?_) hWU
    intro x hx
    by_contra hxW
    exact hx (hχ_zero x hxW)
  have hχ_on : ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (χ : M → Real) e.baseSet :=
    χ.contMDiff.contMDiffOn
  have hconst_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
          (tangentConstInChart (𝕜 := Real) (I := I) x₀ v y)) e.baseSet := by
    simpa [he] using
      tangentConstInChart_contMDiffOn_baseSet (𝕜 := Real) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) x₀ v
  refine ⟨⟨fun y : M => χ y • tangentConstInChart (𝕜 := Real) (I := I) x₀ v y, ?_⟩, ?_⟩
  · exact hχ_on.smul_section_of_tsupport hUopen htsupp hconst_on
  · filter_upwards [hχ_one] with x hx
    simp [hx]




omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem exists_sqrtInner_bound (gRef : SmoothRiemannianMetric I M)
    {Kc : Set M} (hKc : IsCompact Kc)
    (s : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ∃ C : Real, 0 ≤ C ∧ ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (s y) (s y)) ≤ C := by


  have hg : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real) b
        (gRef.inner b)) := gRef.contMDiff
  have hgY : ContMDiff I (I.prod 𝓘(Real, E →L[Real] Real)) ∞
      (fun b : M => TotalSpace.mk' (E →L[Real] Real)
        (E := fun x : M => TangentSpace I x →L[Real] Real) b (gRef.inner b (s b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[Real] Real)
      (b := fun b : M => b)
      (ϕ := fun b => gRef.inner b) (v := fun b => s b) hg s.contMDiff
  have hap : ContMDiff I (I.prod 𝓘(Real, Real)) ∞
      (fun b : M => TotalSpace.mk' Real (E := Bundle.Trivial M Real) b
        (gRef.inner b (s b) (s b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => Real)
      (b := fun b : M => b)
      (ϕ := fun b => gRef.inner b (s b)) (v := fun b => s b) hgY s.contMDiff
  have hpair : ContMDiff I 𝓘(Real, Real) ∞ (fun b : M => gRef.inner b (s b) (s b)) := by
    intro b
    exact (contMDiffAt_section (F := Real) (E := Bundle.Trivial M Real) b).mp (hap b)
  have hcont : Continuous (fun y : M => Real.sqrt (gRef.inner y (s y) (s y))) :=
    Real.continuous_sqrt.comp hpair.continuous
  obtain ⟨C, hC⟩ := hKc.bddAbove_image hcont.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun y hy => le_trans (hC ⟨y, hy, rfl⟩) (le_max_left _ _)⟩



omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem exists_family_bound (gRef : SmoothRiemannianMetric I M)
    {Kc : Set M} (hKc : IsCompact Kc)
    {ι : Type*} [Fintype ι]
    (s : ι → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ∃ D : Real, 0 ≤ D ∧ ∀ i : ι, ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (s i y) (s i y)) ≤ D := by
  classical
  have h : ∀ i : ι, ∃ C : Real, 0 ≤ C ∧ ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (s i y) (s i y)) ≤ C :=
    fun i => exists_sqrtInner_bound (I := I) gRef hKc (s i)
  choose C hC0 hC using h
  refine ⟨∑ i : ι, C i, Finset.sum_nonneg (fun i _ => hC0 i), fun i y hy => ?_⟩
  exact le_trans (hC i y hy)
    (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))









omit [IsManifold I 2 M] in
theorem fderiv_comp_le_tower
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x₀ : M} {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) :
    ∃ CV : Real, 0 ≤ CV ∧ ∀ y ∈ Kc, ∀ Cp Cp1 : Real,
      (∀ z ∈ Kc, Real.sqrt
          (normSq0S (I := I) gRef z (p + 2) (covDerivOfField (I := I) gRef A0 p z)) ≤ Cp) →
      (∀ z ∈ Kc, Real.sqrt
          (normSq0S (I := I) gRef z (p + 3) (covDerivOfField (I := I) gRef A0 (p + 1) z)) ≤ Cp1) →
      ‖fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun z : M => (covDerivOfField (I := I) gRef A0 p) z (fun a => V a z)))
        (extChartAt I x₀ y)‖ ≤ CV * (Cp1 + Cp) := by
  classical
  set n := Module.finrank Real E with hn
  set bE := Module.finBasis Real E with hbE

  have hσex : ∀ i : Fin n, ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _), ∀ᶠ x in 𝓝ˢ Kc,
      σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (bE i) x :=
    fun i => exists_section_eqOn_compact (I := I) x₀ (bE i) hKc hKchart
  choose σ hσ using hσex

  have hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
    ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) gRef isOpen_univ⟩

  let W : Fin n → Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := fun i a =>
    ⟨fun y : M =>
      ((leviCivitaConnectionOfMetric (I := I) gRef) (fun q : M => V a q) y) ((σ i) y),
      by
        simpa [TensorLieDeriv.covariantDeriv_vectorField] using
          TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
            (leviCivitaConnectionOfMetric (I := I) gRef) hcov (σ i) (V a)⟩

  obtain ⟨Dσ, hDσ0, hDσ⟩ := exists_family_bound (I := I) gRef hKc σ
  obtain ⟨DV, hDV0, hDV⟩ := exists_family_bound (I := I) gRef hKc V
  obtain ⟨DW, hDW0, hDW⟩ := exists_family_bound (I := I) gRef hKc
    (fun ia : Fin n × Fin (p + 2) => W ia.1 ia.2)
  set D := max Dσ (max DV DW) with hD
  have hD0 : 0 ≤ D := le_trans hDσ0 (le_max_left _ _)
  have hDσD : Dσ ≤ D := le_max_left _ _
  have hDVD : DV ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
  have hDWD : DW ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)

  have hσbd : ∀ i : Fin n, ∀ y ∈ Kc, Real.sqrt (gRef.inner y (σ i y) (σ i y)) ≤ D :=
    fun i y hy => le_trans (hDσ i y hy) hDσD
  have hVbd : ∀ a : Fin (p + 2), ∀ y ∈ Kc, Real.sqrt (gRef.inner y (V a y) (V a y)) ≤ D :=
    fun a y hy => le_trans (hDV a y hy) hDVD
  have hWbd : ∀ i : Fin n, ∀ a : Fin (p + 2), ∀ y ∈ Kc,
      Real.sqrt (gRef.inner y (W i a y) (W i a y)) ≤ D :=
    fun i a y hy => le_trans (hDW (i, a) y hy) hDWD

  set Ccoord : Real := ∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖
    with hCcoord
  have hCcoord0 : 0 ≤ Ccoord := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  refine ⟨max (Ccoord * D ^ (p + 3)) (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))),
    le_trans (mul_nonneg hCcoord0 (pow_nonneg hD0 _)) (le_max_left _ _), ?_⟩
  intro y hy Cp Cp1 hCp hCp1
  set CV := max (Ccoord * D ^ (p + 3)) (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) with hCV

  set f : M → Real := fun z : M => (covDerivOfField (I := I) gRef A0 p) z (fun a => V a z)
    with hf

  have hCpnn : 0 ≤ Cp := le_trans (Real.sqrt_nonneg _) (hCp y hy)
  have hCp1nn : 0 ≤ Cp1 := le_trans (Real.sqrt_nonneg _) (hCp1 y hy)

  obtain ⟨bON, hbON⟩ := exists_ON_tangentBasis (I := I) gRef y

  have hfmd : MDifferentiableAt I 𝓘(Real, Real) f y :=
    covDerivOfField_eval_mdiffAt (I := I) gRef A0 p V y
  have hychart : y ∈ (chartAt H x₀).source := hKchart hy

  have hdir : ∀ i : Fin n,
      |fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀ y) (bE i)|
        ≤ Cp1 * D ^ (p + 3) + (p + 2 : ℕ) * (Cp * D ^ (p + 2)) := by
    intro i

    have hbridge :
        fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀ y) (bE i)
          = extDerivFun (I := I) f y (σ i y) := by
      rw [← extDerivFun_tangentConstInChart_eq_fderiv (I := I) (f := f)
        (x := x₀) (p := y) hychart hfmd (bE i)]
      rw [(hσ i).self_of_nhdsSet y hy]

    have hdecomp :
        extDerivFun (I := I) f y (σ i y)
          = (covDerivOfField (I := I) gRef A0 (p + 1)) y
              (Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y))
            + ∑ a : Fin (p + 2),
                (covDerivOfField (I := I) gRef A0 p) y
                  (Function.update (fun b : Fin (p + 2) => V b y) a
                    (((leviCivitaConnectionOfMetric (I := I) gRef)
                      (fun q : M => V a q) y) (σ i y))) := by
      have key :
          (covDerivOfField (I := I) gRef A0 (p + 1)) y
              (Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y))
            = extDerivFun (I := I) f y (σ i y)
              - ∑ a : Fin (p + 2),
                  (covDerivOfField (I := I) gRef A0 p) y
                    (Function.update (fun b : Fin (p + 2) => V b y) a
                      (((leviCivitaConnectionOfMetric (I := I) gRef)
                        (fun q : M => V a q) y) (σ i y))) := by
        rw [covDerivOfField_succ, metricCovDerivStep_apply,
          Tensor0SBundle.totalNabla0SFun_apply_section,
          Tensor0SBundle.nabla0SFun_eval_smooth_slots]
      linarith [key]
    rw [hbridge, hdecomp]

    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ ?_
    ·
      have hCS := abs_apply_le_sqrt_normSq0S (I := I) gRef y (p + 3) bON hbON
        (covDerivOfField (I := I) gRef A0 (p + 1) y)
        (Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y))
      refine le_trans hCS ?_
      have hprod :
          (∏ a : Fin (p + 3), Real.sqrt (gRef.inner y
              ((Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y) :
                  Fin (p + 3) → TangentSpace I y) a)
              ((Fin.cons (σ i y) (fun a : Fin (p + 2) => V a y) :
                  Fin (p + 3) → TangentSpace I y) a)))
            ≤ D ^ (p + 3) := by
        refine le_trans (Finset.prod_le_prod (g := fun _ : Fin (p + 3) => D)
          (fun a _ => Real.sqrt_nonneg _) (fun a _ => ?_)) (le_of_eq ?_)
        · refine Fin.cases ?_ ?_ a
          · simpa using hσbd i y hy
          · intro a'
            simpa using hVbd a' y hy
        · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      refine le_trans (mul_le_mul (hCp1 y hy) hprod
        (Finset.prod_nonneg (fun a _ => Real.sqrt_nonneg _)) hCp1nn) ?_
      exact le_of_eq rfl
    ·
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ a : Fin (p + 2),
          |(covDerivOfField (I := I) gRef A0 p) y
              (Function.update (fun b : Fin (p + 2) => V b y) a
                (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun q : M => V a q) y) (σ i y)))|
            ≤ Cp * D ^ (p + 2) := by
        intro a
        have hCS := abs_apply_le_sqrt_normSq0S (I := I) gRef y (p + 2) bON hbON
          (covDerivOfField (I := I) gRef A0 p y)
          (Function.update (fun b : Fin (p + 2) => V b y) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun q : M => V a q) y) (σ i y)))
        refine le_trans hCS ?_
        have hprod :
            (∏ b : Fin (p + 2), Real.sqrt (gRef.inner y
                (Function.update (fun c : Fin (p + 2) => V c y) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun q : M => V a q) y) (σ i y)) b)
                (Function.update (fun c : Fin (p + 2) => V c y) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun q : M => V a q) y) (σ i y)) b)))
              ≤ D ^ (p + 2) := by
          refine le_trans (Finset.prod_le_prod (g := fun _ : Fin (p + 2) => D)
            (fun b _ => Real.sqrt_nonneg _) (fun b _ => ?_)) (le_of_eq ?_)
          · by_cases hba : b = a
            · rw [hba, Function.update_self]
              exact hWbd i a y hy
            · simp only [Function.update_of_ne hba]
              exact hVbd b y hy
          · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        refine le_trans (mul_le_mul (hCp y hy) hprod
          (Finset.prod_nonneg (fun b _ => Real.sqrt_nonneg _)) hCpnn) ?_
        exact le_of_eq rfl
      refine le_trans (Finset.sum_le_sum (fun a _ => hterm a)) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

  set Lz := fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀ y)
    with hLz
  refine le_trans (opNorm_le_sum_coord (E := E) bE Lz) ?_
  have hsum :
      (∑ i : Fin n, ‖LinearMap.toContinuousLinearMap (bE.coord i)‖ * |Lz (bE i)|)
        ≤ Ccoord * (Cp1 * D ^ (p + 3) + (p + 2 : ℕ) * (Cp * D ^ (p + 2))) := by
    rw [hCcoord, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left (hdir i) (norm_nonneg _)
  refine le_trans hsum ?_

  have hb1 : Ccoord * D ^ (p + 3) ≤ CV := le_max_left _ _
  have hb2 : Ccoord * ((p + 2 : ℕ) * D ^ (p + 2)) ≤ CV := le_max_right _ _
  have hexpand :
      Ccoord * (Cp1 * D ^ (p + 3) + (p + 2 : ℕ) * (Cp * D ^ (p + 2)))
        = (Ccoord * D ^ (p + 3)) * Cp1
          + (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) * Cp := by ring
  rw [hexpand]
  have h1 : (Ccoord * D ^ (p + 3)) * Cp1 ≤ CV * Cp1 :=
    mul_le_mul_of_nonneg_right hb1 hCp1nn
  have h2 : (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) * Cp ≤ CV * Cp :=
    mul_le_mul_of_nonneg_right hb2 hCpnn
  calc (Ccoord * D ^ (p + 3)) * Cp1 + (Ccoord * ((p + 2 : ℕ) * D ^ (p + 2))) * Cp
      ≤ CV * Cp1 + CV * Cp := add_le_add h1 h2
    _ = CV * (Cp1 + Cp) := by ring








omit [CompleteSpace E] in
theorem clm_eq_sum_coord {m : ℕ}
    (bE : Module.Basis (Fin m) Real E) (L : E →L[Real] Real) :
    L = ∑ i : Fin m, (L (bE i)) • LinearMap.toContinuousLinearMap (bE.coord i) := by
  ext w
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, smul_eq_mul]
  conv_lhs => rw [← bE.sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul, mul_comm]






omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem extDerivFun_tower_step
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (q : M) :
    extDerivFun (I := I)
        (fun z : M => (covDerivOfField (I := I) gRef A0 p) z (fun a => V a z)) q (X q)
      = (covDerivOfField (I := I) gRef A0 (p + 1)) q
          (Fin.cons (X q) (fun a : Fin (p + 2) => V a q))
        + ∑ a : Fin (p + 2),
            (covDerivOfField (I := I) gRef A0 p) q
              (Function.update (fun b : Fin (p + 2) => V b q) a
                (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun r : M => V a r) q) (X q))) := by
  have key :
      (covDerivOfField (I := I) gRef A0 (p + 1)) q
          (Fin.cons (X q) (fun a : Fin (p + 2) => V a q))
        = extDerivFun (I := I)
            (fun z : M => (covDerivOfField (I := I) gRef A0 p) z (fun a => V a z)) q (X q)
          - ∑ a : Fin (p + 2),
              (covDerivOfField (I := I) gRef A0 p) q
                (Function.update (fun b : Fin (p + 2) => V b q) a
                  (((leviCivitaConnectionOfMetric (I := I) gRef)
                    (fun r : M => V a r) q) (X q))) := by
    rw [covDerivOfField_succ, metricCovDerivStep_apply,
      Tensor0SBundle.totalNabla0SFun_apply_section,
      Tensor0SBundle.nabla0SFun_eval_smooth_slots]
  linarith [key]




omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem contDiffAt_chartRep
    (f : M → Real) (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) :
    ContDiffAt Real (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀ y) := by
  have hsymm : ContMDiffOn 𝓘(Real, E) I (∞ : WithTop ℕ∞)
      (extChartAt I x₀).symm (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
  have hcomp : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target :=
    hf.comp_contMDiffOn hsymm
  have hcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target :=
    contMDiffOn_iff_contDiffOn.mp hcomp
  have hwrite : writtenInExtChartAt I 𝓘(Real, Real) x₀ f
      = f ∘ (extChartAt I x₀).symm := by
    funext z; simp [writtenInExtChartAt]
  rw [hwrite]
  have hysrc : y ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hz : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hysrc
  exact hcd.contDiffAt ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hz)



omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem writtenInExtChartAt_real_apply (x₀ : M) (g : M → Real) (z : E) :
    writtenInExtChartAt I 𝓘(Real, Real) x₀ g z = g ((extChartAt I x₀).symm z) := by
  simp [writtenInExtChartAt]




noncomputable def towerStep (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    M → Real :=
  fun q => (covDerivOfField (I := I) gRef A0 (p + 1)) q
      (Fin.cons (X q) (fun a : Fin (p + 2) => V a q))
    + ∑ a : Fin (p + 2),
        (covDerivOfField (I := I) gRef A0 p) q
          (Function.update (fun b : Fin (p + 2) => V b q) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => V a r) q) (X q)))






omit [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem fderiv_chartRep_eq_towerStep
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) (v : E)
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {Kc : Set M}
    (hσ : ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x)
    (hKchart : Kc ⊆ (chartAt H x₀).source) {y : M} (hy : y ∈ Kc) :
    (fun z : E => fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w))) z v)
      =ᶠ[𝓝 (extChartAt I x₀ y)]
      writtenInExtChartAt I 𝓘(Real, Real) x₀ (towerStep (I := I) gRef A0 p V σ) := by
  set f : M → Real := fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)
    with hf
  have hytarget : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hKchart hy)

  have hsymm_y : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hKchart hy)
  have htend : Filter.Tendsto (extChartAt I x₀).symm
      (𝓝 (extChartAt I x₀ y)) (𝓝 y) := by
    have h := (continuousAt_extChartAt_symm'' (I := I) (x := x₀) hytarget).tendsto
    rwa [hsymm_y] at h
  have hσnhds : ∀ᶠ q in 𝓝 y,
      σ q = tangentConstInChart (𝕜 := Real) (I := I) x₀ v q :=
    hσ.filter_mono (nhds_le_nhdsSet hy)
  have hpull : ∀ᶠ z : E in 𝓝 (extChartAt I x₀ y),
      σ ((extChartAt I x₀).symm z)
        = tangentConstInChart (𝕜 := Real) (I := I) x₀ v ((extChartAt I x₀).symm z) :=
    htend.eventually hσnhds
  filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hytarget, hpull]
    with z hztarget hzσ
  set q : M := (extChartAt I x₀).symm z with hq
  have hqsource : q ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hztarget
  have hqchart : q ∈ (chartAt H x₀).source := by rwa [← extChartAt_source (I := I)]
  have hzq : extChartAt I x₀ q = z := (extChartAt I x₀).right_inv hztarget

  have hbridge := extDerivFun_tangentConstInChart_eq_fderiv (I := I) (f := f)
    (x := x₀) (p := q) hqchart
    (covDerivOfField_eval_mdiffAt (I := I) gRef A0 p V q) v
  rw [hzq] at hbridge

  rw [← hbridge, ← hzσ, writtenInExtChartAt_real_apply, ← hq, hf]
  exact extDerivFun_tower_step (I := I) gRef A0 p V σ q



omit [I.Boundaryless] [IsManifold I 2 M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem covDerivOfField_eval_contMDiff
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : M => (covDerivOfField (I := I) gRef A0 p) q (fun a => V a q)) :=
  fun x => covDerivOfField_eval_smoothAt (I := I) gRef A0
    (fun W => Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
      (I := I) A0 W x) p V



omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem iteratedFDeriv_smul_const_le {rr : ℕ} {g : E → Real} {z₀ : E}
    (c : E →L[Real] Real) (hg : ContDiffAt Real (∞ : WithTop ℕ∞) g z₀) :
    ‖iteratedFDeriv Real rr (fun z : E => g z • c) z₀‖
      ≤ ‖c‖ * ‖iteratedFDeriv Real rr g z₀‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left
    ((ContinuousLinearMap.id Real Real).smulRight c) hg (i := rr)
    (by exact_mod_cast le_top)
  rw [show (fun z : E => g z • c)
      = (⇑((ContinuousLinearMap.id Real Real).smulRight c)) ∘ g from rfl, h]
  refine le_trans
    (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_of_le_one_left (norm_nonneg _) ContinuousLinearMap.norm_id_le








omit [IsManifold I 2 M] in
theorem iteratedFDeriv_comp_le_tower
    (gRef : SmoothRiemannianMetric I M)
    {x₀ : M} {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) (r p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ∃ CV : Real, 0 ≤ CV ∧
      ∀ A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2,
      ∀ y ∈ Kc, ∀ b : ℕ → Real,
      (∀ q : ℕ, ∀ z ∈ Kc, Real.sqrt
          (normSq0S (I := I) gRef z (q + 2) (covDerivOfField (I := I) gRef A0 q z)) ≤ b q) →
      ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)))
        (extChartAt I x₀ y)‖ ≤ CV * ∑ q ∈ Finset.range (p + r + 1), b q := by
  induction r generalizing p V with
  | zero =>
      obtain ⟨D, hD0, hD⟩ := exists_family_bound (I := I) gRef hKc V
      refine ⟨D ^ (p + 2), pow_nonneg hD0 _, ?_⟩
      intro A0 y hy b hb
      have hbnn : ∀ q, 0 ≤ b q := fun q => le_trans (Real.sqrt_nonneg _) (hb q y hy)
      rw [norm_iteratedFDeriv_zero]
      have hsymm : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
        (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact hKchart hy)
      have hFz : writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w))
            (extChartAt I x₀ y)
          = (covDerivOfField (I := I) gRef A0 p) y (fun a => V a y) := by
        rw [writtenInExtChartAt_real_apply, hsymm]
      rw [hFz, Real.norm_eq_abs]
      obtain ⟨bON, hbON⟩ := exists_ON_tangentBasis (I := I) gRef y
      have hCS := abs_apply_le_sqrt_normSq0S (I := I) gRef y (p + 2) bON hbON
        (covDerivOfField (I := I) gRef A0 p y) (fun a => V a y)
      have hprod : (∏ a : Fin (p + 2), Real.sqrt (gRef.inner y (V a y) (V a y)))
          ≤ D ^ (p + 2) := by
        refine le_trans (Finset.prod_le_prod (g := fun _ : Fin (p + 2) => D)
          (fun a _ => Real.sqrt_nonneg _) (fun a _ => hD a y hy)) (le_of_eq ?_)
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc |(covDerivOfField (I := I) gRef A0 p y) (fun a => V a y)|
          ≤ Real.sqrt (normSq0S (I := I) gRef y (p + 2)
              (covDerivOfField (I := I) gRef A0 p y))
            * ∏ a : Fin (p + 2), Real.sqrt (gRef.inner y (V a y) (V a y)) := hCS
        _ ≤ b p * D ^ (p + 2) :=
            mul_le_mul (hb p y hy) hprod
              (Finset.prod_nonneg (fun a _ => Real.sqrt_nonneg _)) (hbnn p)
        _ = D ^ (p + 2) * b p := by ring
        _ ≤ D ^ (p + 2) * ∑ q ∈ Finset.range (p + 0 + 1), b q := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hD0 _)
            exact Finset.single_le_sum (fun q _ => hbnn q)
              (Finset.mem_range.2 (by omega))
  | succ r ih =>
      classical
      set m := Module.finrank Real E with hm
      set bE := Module.finBasis Real E with hbE

      have hσex : ∀ i : Fin m, ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _), ∀ᶠ x in 𝓝ˢ Kc,
          σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (bE i) x :=
        fun i => exists_section_eqOn_compact (I := I) x₀ (bE i) hKc hKchart
      choose σ hσ using hσex
      have hcov : CovariantDerivative.ContMDiffCovariantDerivative
          (leviCivitaConnectionOfMetric (I := I) gRef) (∞ : WithTop ℕ∞) :=
        ⟨leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) gRef isOpen_univ⟩

      let W : Fin m → Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun i a =>
        ⟨fun q : M =>
          ((leviCivitaConnectionOfMetric (I := I) gRef) (fun rr : M => V a rr) q)
            ((σ i) q),
          by
            simpa [TensorLieDeriv.covariantDeriv_vectorField] using
              TensorLieDeriv.covariantDeriv_vectorField_contMDiff (I := I)
                (leviCivitaConnectionOfMetric (I := I) gRef) hcov (σ i) (V a)⟩

      let Vf : Fin m → Fin (p + 3) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun i => Fin.cons (σ i) V
      let Vc : Fin m → Fin (p + 2) → Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _) := fun i a => Function.update V a (W i a)

      have hCf := fun i : Fin m => ih (p + 1) (Vf i)
      choose Cf hCf0 hCfb using hCf
      have hCc := fun (i : Fin m) (a : Fin (p + 2)) => ih p (Vc i a)
      choose Cc hCc0 hCcb using hCc
      set c : Fin m → (E →L[Real] Real) :=
        fun i => LinearMap.toContinuousLinearMap (bE.coord i) with hc
      refine ⟨∑ i : Fin m, ‖c i‖ * (Cf i + ∑ a : Fin (p + 2), Cc i a),
        Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _)
          (add_nonneg (hCf0 i) (Finset.sum_nonneg (fun a _ => hCc0 i a)))), ?_⟩
      intro A0 y hy b hb
      have hbnn : ∀ q : ℕ, 0 ≤ b q := fun q => le_trans (Real.sqrt_nonneg _) (hb q y hy)
      set z : E := extChartAt I x₀ y with hzdef
      set F : E → Real := writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) with hFdef
      set S : Real := ∑ q ∈ Finset.range (p + (r + 1) + 1), b q with hSdef
      have hSnn : 0 ≤ S := Finset.sum_nonneg (fun q _ => hbnn q)

      have hcons : ∀ (i : Fin m) (q : M),
          (Fin.cons ((σ i) q) (fun a : Fin (p + 2) => V a q)
            : Fin (p + 3) → TangentSpace I q) = fun a => Vf i a q := by
        intro i q; funext a
        refine Fin.cases ?_ ?_ a
        · simp [Vf]
        · intro a'; simp [Vf]
      have hupd : ∀ (i : Fin m) (a : Fin (p + 2)) (q : M),
          Function.update (fun bb : Fin (p + 2) => V bb q) a
              (((leviCivitaConnectionOfMetric (I := I) gRef) (fun rr : M => V a rr) q)
                ((σ i) q))
            = fun bb : Fin (p + 2) => Vc i a bb q := by
        intro i a q; funext bb
        by_cases hba : bb = a
        · subst hba; simp [Vc, W]
        · simp [Vc, Function.update_of_ne hba]

      have hsplit : ∀ i : Fin m,
          writtenInExtChartAt I 𝓘(Real, Real) x₀ (towerStep (I := I) gRef A0 p V (σ i))
            = fun z' : E =>
                (writtenInExtChartAt I 𝓘(Real, Real) x₀
                  (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
                    (fun a => Vf i a w))) z'
                + ∑ a : Fin (p + 2),
                  (writtenInExtChartAt I 𝓘(Real, Real) x₀
                    (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
                      (fun bb => Vc i a bb w))) z' := by
        intro i; funext z'
        simp only [writtenInExtChartAt_real_apply, towerStep]
        congr 1
        · rw [hcons i]
        · exact Finset.sum_congr rfl (fun a _ => by rw [hupd i a])

      have hcd_first : ∀ i : Fin m, ContDiffAt Real (∞ : WithTop ℕ∞)
          (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
              (fun a => Vf i a w))) z :=
        fun i => contDiffAt_chartRep _
          (covDerivOfField_eval_contMDiff (I := I) gRef A0 (p + 1) (Vf i))
          x₀ (hKchart hy)
      have hcd_corr : ∀ (i : Fin m) (a : Fin (p + 2)), ContDiffAt Real (∞ : WithTop ℕ∞)
          (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
              (fun bb => (Function.update V a (W i a)) bb w))) z :=
        fun i a => contDiffAt_chartRep _
          (covDerivOfField_eval_contMDiff (I := I) gRef A0 p (Vc i a))
          x₀ (hKchart hy)
      have hcd_corrsum : ∀ i : Fin m, ContDiffAt Real (∞ : WithTop ℕ∞)
          (fun z' : E => ∑ a : Fin (p + 2),
            (writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
                (fun bb => Vc i a bb w))) z') z :=
        fun i => ContDiffAt.sum (fun a _ => hcd_corr i a)
      have hcd_g : ∀ i : Fin m, ContDiffAt Real (∞ : WithTop ℕ∞)
          (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (towerStep (I := I) gRef A0 p V (σ i))) z := by
        intro i; rw [hsplit i]; exact (hcd_first i).add (hcd_corrsum i)

      have hgerm : fderiv Real F =ᶠ[𝓝 z]
          fun z' : E => ∑ i : Fin m,
            (writtenInExtChartAt I 𝓘(Real, Real) x₀
              (towerStep (I := I) gRef A0 p V (σ i))) z' • c i := by
        have hperi : ∀ i : Fin m,
            (fun z' : E => fderiv Real F z' (bE i)) =ᶠ[𝓝 z]
              writtenInExtChartAt I 𝓘(Real, Real) x₀
                (towerStep (I := I) gRef A0 p V (σ i)) :=
          fun i => fderiv_chartRep_eq_towerStep (I := I) gRef A0 p V x₀ (bE i) (σ i)
            (hσ i) hKchart hy
        filter_upwards [Filter.eventually_all.mpr (fun i => hperi i)] with z' hz'
        rw [clm_eq_sum_coord bE (fderiv Real F z')]
        exact Finset.sum_congr rfl (fun i _ => by rw [hz' i])

      have hr : (r : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
      have heqf : p + 1 + r + 1 = p + (r + 1) + 1 := by omega
      have hlec : p + r + 1 ≤ p + (r + 1) + 1 := by omega
      have hrange_f : Finset.range (p + 1 + r + 1) = Finset.range (p + (r + 1) + 1) := by
        rw [heqf]
      have hrange_c : Finset.range (p + r + 1) ⊆ Finset.range (p + (r + 1) + 1) :=
        fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hlec)
      have hSc : ∑ q ∈ Finset.range (p + r + 1), b q ≤ S :=
        Finset.sum_le_sum_of_subset_of_nonneg hrange_c (fun q _ _ => hbnn q)

      have hgi : ∀ i : Fin m,
          ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (towerStep (I := I) gRef A0 p V (σ i))) z‖
            ≤ (Cf i + ∑ a : Fin (p + 2), Cc i a) * S := by
        intro i
        rw [hsplit i,
          fun_iteratedFDeriv_add_apply ((hcd_first i).of_le hr) ((hcd_corrsum i).of_le hr),
          iteratedFDeriv_fun_sum_apply (fun a _ => (hcd_corr i a).of_le hr)]
        refine le_trans (norm_add_le _ _) ?_
        have hfst : ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
              (fun a => Vf i a w))) z‖ ≤ Cf i * S := by
          have := hCfb i A0 y hy b hb
          rwa [hrange_f] at this
        have hcsum : ‖∑ a : Fin (p + 2), iteratedFDeriv Real r
            (writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
                (fun bb => Vc i a bb w))) z‖
            ≤ (∑ a : Fin (p + 2), Cc i a) * S := by
          refine le_trans (norm_sum_le _ _) ?_
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum (fun a _ =>
            le_trans (hCcb i a A0 y hy b hb)
              (mul_le_mul_of_nonneg_left hSc (hCc0 i a)))
        calc ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
                (fun a => Vf i a w))) z‖
            + ‖∑ a : Fin (p + 2), iteratedFDeriv Real r
                (writtenInExtChartAt I 𝓘(Real, Real) x₀
                  (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
                    (fun bb => Vc i a bb w))) z‖
            ≤ Cf i * S + (∑ a : Fin (p + 2), Cc i a) * S := add_le_add hfst hcsum
          _ = (Cf i + ∑ a : Fin (p + 2), Cc i a) * S := by ring

      rw [← norm_iteratedFDeriv_fderiv, (hgerm.iteratedFDeriv Real r).eq_of_nhds,
        iteratedFDeriv_fun_sum_apply
          (f := fun i (z' : E) => (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (towerStep (I := I) gRef A0 p V (σ i))) z' • c i)
          (fun i _ => ((hcd_g i).of_le hr).smul contDiffAt_const)]
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun i _ =>
        iteratedFDeriv_smul_const_le (c i) (hcd_g i))) ?_
      refine le_trans (Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hgi i) (norm_nonneg (c i)))) (le_of_eq ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)







omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem bumpMul_contDiff {χ g : E → Real} {U : Set E} (hU : IsOpen U)
    (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ) (htsupp : tsupport χ ⊆ U)
    (hg : ContDiffOn Real (∞ : WithTop ℕ∞) g U) :
    ContDiff Real (∞ : WithTop ℕ∞) (fun x : E => χ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hχ.contDiffAt).mul (hg.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (htsupp h)
    refine (contDiffAt_const (c := (0 : Real))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx'] with z hz
    have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [hχz]






omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem norm_iteratedFDeriv_bumpMul_le {χ gg : E → Real} (r : ℕ)
    (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ) (hgg : ContDiff Real (∞ : WithTop ℕ∞) gg)
    {Bχ Bg : Real} (hBχ0 : 0 ≤ Bχ) (hBg0 : 0 ≤ Bg)
    (hχbd : ∀ x ∈ tsupport χ, ∀ i : ℕ, i ≤ r → ‖iteratedFDeriv Real i χ x‖ ≤ Bχ)
    (hgbd : ∀ x ∈ tsupport χ, ∀ j : ℕ, j ≤ r → ‖iteratedFDeriv Real j gg x‖ ≤ Bg)
    (x : E) :
    ‖iteratedFDeriv Real r (fun y : E => χ y * gg y) x‖ ≤ 2 ^ r * Bχ * Bg := by
  refine le_trans (norm_iteratedFDeriv_mul_le hχ hgg x (by exact_mod_cast le_top)) ?_
  have hterm : ∀ i ∈ Finset.range (r + 1),
      (r.choose i : Real) * ‖iteratedFDeriv Real i χ x‖
          * ‖iteratedFDeriv Real (r - i) gg x‖
        ≤ (r.choose i : Real) * (Bχ * Bg) := by
    intro i hi
    have hir : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    by_cases hx : x ∈ tsupport χ
    · rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (hχbd x hx i hir) (hgbd x hx (r - i) (Nat.sub_le r i))
        (norm_nonneg _) hBχ0
    · have hχx : iteratedFDeriv Real i χ x = 0 := by
        have heq : χ =ᶠ[nhds x] (fun _ => (0 : Real)) := by
          filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        rw [(heq.iteratedFDeriv Real i).eq_of_nhds]
        simp [iteratedFDeriv_fun_zero]
      rw [hχx]
      simp only [norm_zero, mul_zero, zero_mul]
      positivity
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring




omit [IsManifold I 2 M] in
theorem metricComp_iter_le
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) (r : ℕ)
    (hbdd : ∀ q : ℕ, q ≤ r → ∃ C : Real, ∀ k : ι, ∀ z ∈ Kc,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ∃ Mr : Real, 0 ≤ Mr ∧ ∀ k : ι, ∀ y ∈ Kc,
      ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w)))
        (extChartAt I x₀ y)‖ ≤ Mr := by
  classical
  obtain ⟨CV, hCV0, hCV⟩ :=
    iteratedFDeriv_comp_le_tower (I := I) gRef hKc hKchart r 0 V
  let C : ℕ → Real := fun q =>
    if hq : q ≤ r then Classical.choose (hbdd q hq) else 0
  have hC : ∀ q (hq : q ≤ r), ∀ k : ι, ∀ z ∈ Kc,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C q := by
    intro q hq k z hz
    simpa only [C, dif_pos hq] using (Classical.choose_spec (hbdd q hq)) k z hz
  let B : ℕ → Real := fun q => max (C q) 0
  refine ⟨CV * ∑ q ∈ Finset.range (r + 1), B q,
    mul_nonneg hCV0 (Finset.sum_nonneg (fun q _ => le_max_right _ _)), ?_⟩
  intro k y hy
  let D : ℕ → Real := fun q =>
    Classical.choose (metricCovDerivNorm_bddOn (I := I) hKc q (gSeq k) gRef)
  have hD : ∀ q : ℕ, ∀ z ∈ Kc,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ D q := by
    intro q z hz
    exact (Classical.choose_spec
      (metricCovDerivNorm_bddOn (I := I) hKc q (gSeq k) gRef)) z hz
  let b : ℕ → Real := fun q => if hq : q ≤ r then B q else max (D q) 0
  have hbnd : ∀ q : ℕ, ∀ z ∈ Kc, Real.sqrt
      (normSq0S (I := I) gRef z (q + 2)
        (covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) q z)) ≤ b q := by
    intro q z hz
    have hcompeq : Real.sqrt (normSq0S (I := I) gRef z (q + 2)
        (covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) q z)) =
        metricCovDerivNorm (I := I) q (gSeq k) gRef z := by
      simp only [metricCovDerivNorm, metricCovDeriv_eq_covDerivOfField]
    rw [hcompeq]
    by_cases hq : q ≤ r
    · exact le_trans (hC q hq k z hz) (by simp only [b, dif_pos hq, B]; exact le_max_left _ _)
    · exact le_trans (hD q z hz) (by simp only [b, dif_neg hq]; exact le_max_left _ _)
  have hbound := hCV (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) y hy b hbnd
  have hsum : ∑ q ∈ Finset.range (r + 1), b q =
      ∑ q ∈ Finset.range (r + 1), B q := by
    refine Finset.sum_congr rfl fun q hqmem => ?_
    have hq : q ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hqmem)
    simp only [b, dif_pos hq]
  calc
    ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w)))
        (extChartAt I x₀ y)‖
        ≤ CV * ∑ q ∈ Finset.range (r + 1), b q := by
          simpa only [zero_add] using hbound
    _ = CV * ∑ q ∈ Finset.range (r + 1), B q := by rw [hsum]



omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem chartGram_germ
    (gRef g : SmoothRiemannianMetric I M) (x₀ : M) {Kc : Set M}
    (hKchart : Kc ⊆ (chartAt H x₀).source) {y : M} (hy : y ∈ Kc)
    (i j : Fin (Module.finrank Real E))
    (σi σj : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hσi : ∀ᶠ z in 𝓝ˢ Kc,
      σi z = tangentConstInChart (𝕜 := Real) (I := I) x₀ ((chartModelBasis E) i) z)
    (hσj : ∀ᶠ z in 𝓝ˢ Kc,
      σj z = tangentConstInChart (𝕜 := Real) (I := I) x₀ ((chartModelBasis E) j) z) :
    chartGramOnE (I := I) g x₀ i j =ᶠ[𝓝 (extChartAt I x₀ y)]
      writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) g) 0) w
            (fun a => (![σi, σj] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M → Type _)) a w)) := by
  have hysrc : y ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    exact hKchart hy
  have hytgt : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hysrc
  have hxy : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hysrc
  have htend : Filter.Tendsto (extChartAt I x₀).symm
      (𝓝 (extChartAt I x₀ y)) (𝓝 y) := by
    have h := (continuousAt_extChartAt_symm'' (I := I) (x := x₀) hytgt).tendsto
    rwa [hxy] at h
  have hσi0 : ∀ᶠ q in 𝓝 y,
      σi q = tangentConstInChart (𝕜 := Real) (I := I) x₀ ((chartModelBasis E) i) q :=
    hσi.filter_mono (nhds_le_nhdsSet hy)
  have hσj0 : ∀ᶠ q in 𝓝 y,
      σj q = tangentConstInChart (𝕜 := Real) (I := I) x₀ ((chartModelBasis E) j) q :=
    hσj.filter_mono (nhds_le_nhdsSet hy)
  filter_upwards [htend.eventually hσi0, htend.eventually hσj0] with z hzi hzj
  simp only [writtenInExtChartAt_real_apply]
  set q : M := (extChartAt I x₀).symm z with hq
  have hval : (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) g) 0) q
        (fun a => (![σi, σj] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)) a q) = g.inner q (σi q) (σj q) := by
    have h0 : (covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) g) 0) q
          (fun a => (![σi, σj] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _)) a q) =
        (Tensor0SBundle.metricTensorField (I := I) g) q
          (fun a => (![σi, σj] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _)) a q) := rfl
    rw [h0, Tensor0SBundle.metricTensorField_apply]
    simp
  rw [hval, hzi, hzj, chartGramOnE, chartGramMatrix_apply]
  congr 1




omit [IsManifold I 2 M] in
theorem chartGram_iter_le
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) (r : ℕ)
    (hbdd : ∀ q : ℕ, q ≤ r → ∃ C : Real, ∀ k : ι, ∀ z ∈ Kc,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C) :
    ∃ C : Real, 0 ≤ C ∧ ∀ k : ι, ∀ y ∈ Kc,
      ∀ i j : Fin (Module.finrank Real E),
      ‖iteratedFDeriv Real r (chartGramOnE (I := I) (gSeq k) x₀ i j)
        (extChartAt I x₀ y)‖ ≤ C := by
  classical
  have hσex : ∀ i : Fin (Module.finrank Real E),
      ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ∀ᶠ z in 𝓝ˢ Kc,
          σ z = tangentConstInChart (𝕜 := Real) (I := I) x₀ ((chartModelBasis E) i) z :=
    fun i => exists_section_eqOn_compact (I := I) x₀ ((chartModelBasis E) i) hKc hKchart
  choose σ hσ using hσex
  have hM : ∀ p : Fin (Module.finrank Real E) × Fin (Module.finrank Real E),
      ∃ C : Real, 0 ≤ C ∧ ∀ k : ι, ∀ y ∈ Kc,
        ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => (![σ p.1, σ p.2] : Fin 2 →
                  ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) a w)))
          (extChartAt I x₀ y)‖ ≤ C := fun p =>
    metricComp_iter_le (I := I) gRef gSeq x₀ hKc hKchart r hbdd ![σ p.1, σ p.2]
  choose C hC0 hC using hM
  refine ⟨∑ p, C p, Finset.sum_nonneg (fun p _ => hC0 p), ?_⟩
  intro k y hy i j
  have hgerm := chartGram_germ (I := I) gRef (gSeq k) x₀ hKchart hy i j
    (σ i) (σ j) (hσ i) (hσ j)
  rw [(hgerm.iteratedFDeriv Real r).eq_of_nhds]
  exact le_trans (hC (i, j) k y hy)
    (Finset.single_le_sum (fun p _ => hC0 p) (Finset.mem_univ (i, j)))



omit [IsManifold I 2 M] in
theorem chartGram_of_orders
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) (r : ℕ) (B : Real)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ r →
      MetricCovDerivOrderBoundOn (I := I) Kc q (gSeq k) gRef B) :
    ∃ C : Real, 0 ≤ C ∧ ∀ k : ι, ∀ y ∈ Kc,
      ∀ i j : Fin (Module.finrank Real E),
      ‖iteratedFDeriv Real r (chartGramOnE (I := I) (gSeq k) x₀ i j)
        (extChartAt I x₀ y)‖ ≤ C :=
  chartGram_iter_le (I := I) gRef gSeq x₀ hKc hKchart r
    (fun q hq => ⟨B, fun k z hz => hbdd k q hq z hz⟩)



omit [IsManifold I 2 M] in
theorem chartGram_pou_le
    [CompactSpace M]
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (r : ℕ) (B : Real)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ r →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gRef B) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ y ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j : Fin (Module.finrank Real E),
            ‖iteratedFDeriv Real r (chartGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α y)‖ ≤ C := by
  classical
  have hper : ∀ α : M, ∃ C : Real, 0 ≤ C ∧
      ∀ k : ι, ∀ y ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ i j : Fin (Module.finrank Real E),
          ‖iteratedFDeriv Real r (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α y)‖ ≤ C := by
    intro α
    exact chartGram_of_orders (I := I) gRef gSeq α
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_isCompact
        (I := I) (M := M) α)
      (by
        intro y hy
        have hy_base :=
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
            (I := I) (M := M) α hy
        rwa [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hy_base)
      r B (fun k q hq y _hy => hbdd k q hq y (Set.mem_univ y))
  choose Cα hCα hbound using hper
  let C : Real := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α
  have hC_nonneg : 0 ≤ C := by
    exact Finset.sum_nonneg fun α _ => hCα α
  refine ⟨C, hC_nonneg, ?_⟩
  intro α hα k y hy i j
  have hCα_le : Cα α ≤ C := by
    apply Finset.single_le_sum
    · intro β _
      exact hCα β
    · exact hα
  exact (hbound α k y hy i j).trans hCα_le



omit [IsManifold I 2 M] in
theorem chartGram_pou_bnd
    [CompactSpace M]
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : Real)
    (hbdd : ∀ k : ι,
      MetricCovDerivOrderBoundOn (I := I) Set.univ 0 (gSeq k) gRef B) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ y ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ i j : Fin (Module.finrank Real E),
            |chartGramOnE (I := I) (gSeq k) α i j (extChartAt I α y)| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := chartGram_pou_le (I := I) gRef gSeq 0 B
    (fun k q hq => by
      have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
      simpa only [hq0] using hbdd k)
  refine ⟨C, hC_nn, ?_⟩
  intro α hα k y hy i j
  have h := hC α hα k y hy i j
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h



omit [IsManifold I 2 M] in
theorem chartGram_pou_d1
    [CompactSpace M]
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : Real)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 1 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gRef B) :
    ∃ Q : Real, 0 ≤ Q ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ y ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ m i j : Fin (Module.finrank Real E),
            |partialDeriv (E := E) m (chartGramOnE (I := I) (gSeq k) α i j)
              (extChartAt I α y)| ≤ Q := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := chartGram_pou_le (I := I) gRef gSeq 1 B hbdd
  let C_E : Real := ∑ m : Fin (Module.finrank Real E), ‖(chartModelBasis E) m‖
  have hCE_nn : 0 ≤ C_E := Finset.sum_nonneg fun m _ => norm_nonneg _
  refine ⟨C * C_E, mul_nonneg hC_nn hCE_nn, ?_⟩
  intro α hα k y hy m i j
  have hm_le : ‖(chartModelBasis E) m‖ ≤ C_E :=
    Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ m)
  rw [partial_eq_iter1]
  rw [← Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv Real 1 (chartGramOnE (I := I) (gSeq k) α i j)
        (extChartAt I α y) ![(chartModelBasis E) m]‖
        ≤ ‖iteratedFDeriv Real 1 (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α y)‖ *
          ∏ a : Fin 1, ‖(![(chartModelBasis E) m] : Fin 1 → E) a‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv Real 1 (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α y)‖ * ‖(chartModelBasis E) m‖ := by simp
    _ ≤ C * C_E := mul_le_mul (hC α hα k y hy i j) hm_le
      (norm_nonneg _) hC_nn



omit [IsManifold I 2 M] in
theorem chartGram_pou_d2
    [NeZero (Module.finrank Real E)] [CompactSpace M]
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : Real)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 2 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gRef B) :
    ∃ Q : Real, 0 ≤ Q ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ y ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ c m i j : Fin (Module.finrank Real E),
            |partialDeriv (E := E) c
              (partialDeriv (E := E) m
                (chartGramOnE (I := I) (gSeq k) α i j)) (extChartAt I α y)| ≤ Q := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := chartGram_pou_le (I := I) gRef gSeq 2 B hbdd
  let C_E : Real := ∑ a : Fin (Module.finrank Real E), ‖(chartModelBasis E) a‖
  have hCE_nn : 0 ≤ C_E := Finset.sum_nonneg fun a _ => norm_nonneg _
  refine ⟨C * (C_E * C_E), mul_nonneg hC_nn (mul_nonneg hCE_nn hCE_nn), ?_⟩
  intro α hα k y hy c m i j
  have hy_base : y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hy
  have hy_source : y ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hy_base
  have hz_int : extChartAt I α y ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hy_source)
  have hcont : ContDiffAt Real ∞ (chartGramOnE (I := I) (gSeq k) α i j)
      (extChartAt I α y) :=
    ((chartGramOnE_contDiffOn (I := I) (gSeq k) α i j).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hz_int)
  have hc_le : ‖(chartModelBasis E) c‖ ≤ C_E :=
    Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ c)
  have hm_le : ‖(chartModelBasis E) m‖ ≤ C_E :=
    Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ m)
  rw [partial2_eq_iter2 _ hcont]
  rw [← Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv Real 2 (chartGramOnE (I := I) (gSeq k) α i j)
        (extChartAt I α y) ![(chartModelBasis E) c, (chartModelBasis E) m]‖
        ≤ ‖iteratedFDeriv Real 2 (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α y)‖ *
          ∏ a : Fin 2,
            ‖(![(chartModelBasis E) c, (chartModelBasis E) m] : Fin 2 → E) a‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv Real 2 (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α y)‖ *
          (‖(chartModelBasis E) c‖ * ‖(chartModelBasis E) m‖) := by simp
    _ ≤ C * (C_E * C_E) := mul_le_mul (hC α hα k y hy i j)
      (mul_le_mul hc_le hm_le (norm_nonneg _) hCE_nn) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hC_nn



omit [IsManifold I 2 M] in
theorem chartGram_pou_d3
    [NeZero (Module.finrank Real E)] [CompactSpace M]
    {ι : Type*}
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : Real)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gRef B) :
    ∃ Q : Real, 0 ≤ Q ∧
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ k : ι, ∀ y ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ∀ d c m i j : Fin (Module.finrank Real E),
            |partialDeriv (E := E) d
              (partialDeriv (E := E) c
                (partialDeriv (E := E) m
                  (chartGramOnE (I := I) (gSeq k) α i j))) (extChartAt I α y)| ≤ Q := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := chartGram_pou_le (I := I) gRef gSeq 3 B hbdd
  let C_E : Real := ∑ a : Fin (Module.finrank Real E), ‖(chartModelBasis E) a‖
  have hCE_nn : 0 ≤ C_E := Finset.sum_nonneg fun a _ => norm_nonneg _
  refine ⟨C * (C_E * (C_E * C_E)),
    mul_nonneg hC_nn (mul_nonneg hCE_nn (mul_nonneg hCE_nn hCE_nn)), ?_⟩
  intro α hα k y hy d c m i j
  have hy_base : y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pouTsupport_subset_baseSet
      (I := I) (M := M) α hy
  have hy_source : y ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I),
      ← trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hy_base
  have hz_int : extChartAt I α y ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hy_source)
  have hcont : ContDiffAt Real ∞ (chartGramOnE (I := I) (gSeq k) α i j)
      (extChartAt I α y) :=
    ((chartGramOnE_contDiffOn (I := I) (gSeq k) α i j).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hz_int)
  have hd_le : ‖(chartModelBasis E) d‖ ≤ C_E :=
    Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ d)
  have hc_le : ‖(chartModelBasis E) c‖ ≤ C_E :=
    Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ c)
  have hm_le : ‖(chartModelBasis E) m‖ ≤ C_E :=
    Finset.single_le_sum (fun a _ => norm_nonneg ((chartModelBasis E) a))
      (Finset.mem_univ m)
  rw [partial3_eq_iter3 _ hcont]
  rw [← Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv Real 3 (chartGramOnE (I := I) (gSeq k) α i j)
        (extChartAt I α y)
        ![(chartModelBasis E) d, (chartModelBasis E) c, (chartModelBasis E) m]‖
        ≤ ‖iteratedFDeriv Real 3 (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α y)‖ *
          ∏ a : Fin 3,
            ‖(![(chartModelBasis E) d, (chartModelBasis E) c,
              (chartModelBasis E) m] : Fin 3 → E) a‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv Real 3 (chartGramOnE (I := I) (gSeq k) α i j)
            (extChartAt I α y)‖ *
          (‖(chartModelBasis E) d‖ *
            (‖(chartModelBasis E) c‖ * ‖(chartModelBasis E) m‖)) := by
      simp [Fin.prod_univ_succ]
    _ ≤ C * (C_E * (C_E * C_E)) := by
      have hprod : ‖(chartModelBasis E) d‖ *
          (‖(chartModelBasis E) c‖ * ‖(chartModelBasis E) m‖) ≤
            C_E * (C_E * C_E) :=
        mul_le_mul hd_le
          (mul_le_mul hc_le hm_le (norm_nonneg _) hCE_nn)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCE_nn
      exact mul_le_mul (hC α hα k y hy i j) hprod
        (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hC_nn






omit [IsManifold I 2 M] in
theorem metricComp_iteratedFDeriv_le
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (r : ℕ) :
    ∃ Mr : Real, 0 ≤ Mr ∧ ∀ k : ℕ, ∀ y ∈ Kc,
      ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w)))
        (extChartAt I x₀ y)‖ ≤ Mr :=
  metricComp_iter_le (I := I) gRef gSeq x₀ hKc hKchart r
    (fun q _ => hbdd q Kc hKc) V





omit [IsManifold I 2 M] in
theorem metricComp_iter_refs
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (r : ℕ) :
    ∃ Mr : Real, 0 ≤ Mr ∧ ∀ k : ℕ, ∀ y ∈ Kc,
      ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) (gRef r)
            (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w)))
        (extChartAt I x₀ y)‖ ≤ Mr := by
  classical
  obtain ⟨CV, hCV0, hCV⟩ :=
    iteratedFDeriv_comp_le_tower (I := I) (gRef r) hKc hKchart r 0 V
  let C : ℕ → Real := fun q =>
    if hq : q ≤ r then Classical.choose (hbdd r q hq Kc hKc) else 0
  have hC : ∀ q (hq : q ≤ r), ∀ k : ℕ, ∀ z ∈ Kc,
      metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C q := by
    intro q hq
    dsimp only [C]
    rw [dif_pos hq]
    exact Classical.choose_spec (hbdd r q hq Kc hKc)
  let B : ℕ → Real := fun q => max (C q) 0
  have hB0 : ∀ q, 0 ≤ B q := fun q => le_max_right _ _
  refine ⟨CV * ∑ q ∈ Finset.range (r + 1), B q,
    mul_nonneg hCV0 (Finset.sum_nonneg fun q _ => hB0 q), ?_⟩
  intro k y hy
  choose Cfix hCfix using fun q =>
    metricCovDerivNorm_bddOn (I := I) hKc q (gSeq k) (gRef r)
  let b : ℕ → Real := fun q => if q ≤ r then B q else max (Cfix q) 0
  have hbnd : ∀ q : ℕ, ∀ z ∈ Kc, Real.sqrt
      (normSq0S (I := I) (gRef r) z (q + 2)
        (covDerivOfField (I := I) (gRef r)
          (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) q z)) ≤ b q := by
    intro q z hz
    have hcompeq : Real.sqrt (normSq0S (I := I) (gRef r) z (q + 2)
        (covDerivOfField (I := I) (gRef r)
          (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) q z)) =
        metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z := by
      simp only [metricCovDerivNorm, metricCovDeriv_eq_covDerivOfField]
    rw [hcompeq]
    by_cases hq : q ≤ r
    · rw [show b q = B q by simp [b, hq]]
      exact le_trans (hC q hq k z hz) (le_max_left _ _)
    · rw [show b q = max (Cfix q) 0 by simp [b, hq]]
      exact le_trans (hCfix q z hz) (le_max_left _ _)
  have hbound := hCV (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) y hy b hbnd
  have hsum : ∑ q ∈ Finset.range (r + 1), b q =
      ∑ q ∈ Finset.range (r + 1), B q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqr : q ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    simp [b, hqr]
  calc
    ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) (gRef r)
          (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w)))
      (extChartAt I x₀ y)‖ ≤ CV * ∑ q ∈ Finset.range (0 + r + 1), b q := hbound
    _ = CV * ∑ q ∈ Finset.range (r + 1), B q := by
      rw [show 0 + r + 1 = r + 1 by omega, hsum]







omit [IsManifold I 2 M] in
theorem exists_chart_engineInput
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source) :
    ∃ (Φ : ℕ → E → Real) (χ : E → Real),
      (∀ k, ContDiff Real (∞ : WithTop ℕ∞) (Φ k)) ∧
      (∀ r : ℕ, ∃ M : Real, ∀ k : ℕ, ∀ x : E,
        ‖iteratedFDeriv Real r (Φ k) x‖ ≤ M) ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      (∀ k, Φ k = fun x : E => χ x *
        writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w)) x) := by
  classical
  haveI : NormalSpace E := inferInstance
  haveI : LocallyCompactSpace E := inferInstance
  set tgt := (extChartAt I x₀).target with htgt
  have htgt_open : IsOpen tgt := isOpen_extChartAt_target (I := I) x₀

  set EK₀ : Set E := extChartAt I x₀ '' K₀ with hEK₀
  have hEK₀cpt : IsCompact EK₀ :=
    hK₀.image_of_continuousOn ((continuousOn_extChartAt (I := I) x₀).mono
      (by rw [extChartAt_source]; exact hK₀chart))
  have hEK₀tgt : EK₀ ⊆ tgt := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hK₀chart hy)

  obtain ⟨L, hLcpt, hEK₀L, hLt⟩ := exists_compact_between hEK₀cpt htgt_open hEK₀tgt
  obtain ⟨χM, hχ1, hχ0, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(Real, E)) (M := E)
      (n := (⊤ : ℕ∞)) hEK₀cpt.isClosed hEK₀L
  set χ : E → Real := (χM : E → Real) with hχdef
  have hχcd : ContDiff Real (∞ : WithTop ℕ∞) χ :=
    contMDiff_iff_contDiff.mp (χM.contMDiff.of_le (by exact_mod_cast le_top))
  have hχLsub : tsupport χ ⊆ L :=
    closure_minimal (fun x hx => by by_contra hxL; exact hx (hχ0 x hxL)) hLcpt.isClosed
  have hχcpt : IsCompact (tsupport χ) :=
    hLcpt.of_isClosed_subset (isClosed_tsupport χ) hχLsub
  have hχtsupp : tsupport χ ⊆ tgt := subset_trans hχLsub hLt

  obtain ⟨V₂, hV₂o, htsχV₂, hV₂t⟩ :=
    normal_exists_closure_subset (isClosed_tsupport χ) htgt_open hχtsupp
  obtain ⟨χ1M, hχ1one, hχ1zero, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(Real, E)) (M := E)
      (n := (⊤ : ℕ∞)) (isClosed_tsupport χ) (by rw [hV₂o.interior_eq]; exact htsχV₂)
  set χ1 : E → Real := (χ1M : E → Real) with hχ1def
  have hχ1cd : ContDiff Real (∞ : WithTop ℕ∞) χ1 :=
    contMDiff_iff_contDiff.mp (χ1M.contMDiff.of_le (by exact_mod_cast le_top))
  have hχ1tsupp : tsupport χ1 ⊆ tgt := by
    refine subset_trans (closure_mono ?_) hV₂t
    intro x hx; by_contra hxV; exact hx (hχ1zero x hxV)

  set cr : ℕ → E → Real := fun k =>
    writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w))
    with hcr

  have hcrOn : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (cr k) tgt := by
    intro k z hz
    have : ContDiffAt Real (∞ : WithTop ℕ∞) (cr k) z := by
      have hzsrc : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
        rw [← extChartAt_source (I := I)]; exact (extChartAt I x₀).map_target hz
      have := contDiffAt_chartRep (I := I) _
        (covDerivOfField_eval_contMDiff (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0 V) x₀ hzsrc
      rwa [(extChartAt I x₀).right_inv hz] at this
    exact this.contDiffWithinAt

  refine ⟨fun k => fun x => χ x * cr k x, χ, ?_, ?_, ?_, fun k => rfl⟩
  ·
    exact fun k => bumpMul_contDiff htgt_open hχcd hχtsupp (hcrOn k)
  ·
    intro r
    set Kc : Set M := (extChartAt I x₀).symm '' (tsupport χ) with hKcdef
    have hKccpt : IsCompact Kc :=
      hχcpt.image_of_continuousOn
        ((continuousOn_extChartAt_symm (I := I) x₀).mono hχtsupp)
    have hKcsrc : Kc ⊆ (chartAt H x₀).source := by
      rintro w ⟨z, hz, rfl⟩
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target (hχtsupp hz)

    obtain ⟨Bχ, hBχ0, hBχ⟩ : ∃ Bχ : Real, 0 ≤ Bχ ∧ ∀ x ∈ tsupport χ, ∀ i : ℕ, i ≤ r →
        ‖iteratedFDeriv Real i χ x‖ ≤ Bχ := by
      have hbd : ∀ i : ℕ, ∃ Bi : Real, ∀ x ∈ tsupport χ,
          ‖iteratedFDeriv Real i χ x‖ ≤ Bi := by
        intro i
        obtain ⟨Bi, hBi⟩ := hχcpt.bddAbove_image
          ((hχcd.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).continuousOn
        exact ⟨Bi, fun x hx => hBi ⟨x, hx, rfl⟩⟩
      choose Bi hBi using hbd
      refine ⟨∑ i ∈ Finset.range (r + 1), max (Bi i) 0,
        Finset.sum_nonneg (fun i _ => le_max_right _ _), fun x hx i hir => ?_⟩
      exact le_trans (le_trans (hBi i x hx) (le_max_left _ _))
        (Finset.single_le_sum (fun ii _ => le_max_right _ _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hir)))

    choose Mr hMr0 hMrb using fun j =>
      metricComp_iteratedFDeriv_le (I := I) gRef gSeq hbdd x₀ hKccpt hKcsrc V j
    refine ⟨2 ^ r * Bχ * ∑ j ∈ Finset.range (r + 1), Mr j, fun k x => ?_⟩
    set ggk : E → Real := fun x => χ1 x * cr k x with hggk
    have hggcd : ContDiff Real (∞ : WithTop ℕ∞) ggk :=
      bumpMul_contDiff htgt_open hχ1cd hχ1tsupp (hcrOn k)
    have hΦeq : (fun x : E => χ x * cr k x) = fun x : E => χ x * ggk x := by
      funext z
      by_cases hz : χ z = 0
      · simp [hz]
      · have hzts : z ∈ tsupport χ := subset_tsupport _ hz
        have hχ1z : χ1 z = 1 := hχ1one.self_of_nhdsSet z hzts
        simp [ggk, hχ1z]
    have hgbd : ∀ z ∈ tsupport χ, ∀ j : ℕ, j ≤ r →
        ‖iteratedFDeriv Real j ggk z‖ ≤ ∑ j ∈ Finset.range (r + 1), Mr j := by
      intro z hz j hjr
      have hgerm : ggk =ᶠ[nhds z] cr k := by
        filter_upwards [hχ1one.filter_mono (nhds_le_nhdsSet hz)] with w hw
        simp [ggk, hw]
      rw [(hgerm.iteratedFDeriv Real j).eq_of_nhds]
      have hbnd := hMrb j k ((extChartAt I x₀).symm z) ⟨z, hz, rfl⟩
      rw [(extChartAt I x₀).right_inv (hχtsupp hz)] at hbnd
      exact le_trans hbnd
        (Finset.single_le_sum (fun jj _ => hMr0 jj)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hjr)))
    simp only [hΦeq]
    exact norm_iteratedFDeriv_bumpMul_le (χ := χ) (gg := ggk) r hχcd hggcd
      hBχ0 (Finset.sum_nonneg (fun j _ => hMr0 j)) hBχ hgbd x
  ·
    intro y hy
    exact hχ1.self_of_nhdsSet _ ⟨y, hy, rfl⟩





omit [IsManifold I 2 M] in
theorem exists_chart_cInfConv
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → Real) (χ : E → Real),
      StrictMono φ ∧ ContDiff Real (∞ : WithTop ℕ∞) Φinf ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      MapCInfConvOnCompacts Set.univ
        (fun k => fun x : E => χ x *
          writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ k))) 0) w
                (fun a => V a w)) x) Φinf := by
  obtain ⟨Φ, χ, hΦcd, hΦbd, hχ1, hΦrel⟩ :=
    exists_chart_engineInput (I := I) gRef gSeq hbdd x₀ V hK₀ hK₀chart
  obtain ⟨φ, Φinf, hφ, hΦinf, hconv⟩ :=
    exists_cInf_subseq Φ hΦcd
      (fun r K _ => by obtain ⟨M, hM⟩ := hΦbd r; exact ⟨M, fun k x _ => hM k x⟩)
  refine ⟨φ, Φinf, χ, hφ, hΦinf, hχ1, ?_⟩
  have hseq : (fun k => fun x : E => χ x *
      writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ k))) 0) w
            (fun a => V a w)) x) = fun k => Φ (φ k) := by
    funext k; exact (hΦrel (φ k)).symm
  rw [hseq]; exact hconv

end HCGCompactness
end DifferentialGeometry
