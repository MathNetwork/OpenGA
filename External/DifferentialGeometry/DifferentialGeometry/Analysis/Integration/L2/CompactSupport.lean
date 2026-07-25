import DifferentialGeometry.Geometry.Connection.Realization.Embedding
import DifferentialGeometry.Geometry.Connection.Realization.Connection
import DifferentialGeometry.Analysis.Integration.L2.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.Topology.Algebra.Support
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator


noncomputable section

open Manifold Set Filter Bundle CovariantDerivative
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def compactlySupportedSmoothFunctions
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Submodule ℝ C^∞⟮I, M; ℝ⟯ where
  carrier := { f : C^∞⟮I, M; ℝ⟯ | HasCompactSupport (f : M → ℝ) }
  zero_mem' := by
    change HasCompactSupport ((0 : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    simpa [ContMDiffMap.coe_zero] using
      (HasCompactSupport.zero : HasCompactSupport (0 : M → ℝ))
  add_mem' := by
    intro f f' hf hf'
    change HasCompactSupport ((f + f' : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    simpa [ContMDiffMap.coe_add] using hf.add hf'
  smul_mem' := by
    intro c f hf
    change HasCompactSupport ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    have h : ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (fun _ : M => c) • (f : M → ℝ) := by
      ext x
      simp [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [h]
    exact hf.smul_left

omit [Module.Finite ℝ E] in
@[simp]
lemma mem_compactlySupportedSmoothFunctions
    {f : C^∞⟮I, M; ℝ⟯} :
    f ∈ compactlySupportedSmoothFunctions I M ↔ HasCompactSupport (f : M → ℝ) := Iff.rfl

def compactlySupportedSmoothTangentSections
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Submodule ℝ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  carrier :=
    { X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ |
        HasCompactSupport (fun x : M => (X x : E)) }
  zero_mem' := by
    change HasCompactSupport
      (fun x : M => ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E))
    have h : (fun x : M =>
        ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)) = (fun _ : M => (0 : E)) := by
      funext x
      change ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) = (0 : E)
      rfl
    rw [h]
    exact HasCompactSupport.zero
  add_mem' := by
    intro X Y hX hY
    change HasCompactSupport
      (fun x : M =>
        (((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E))
    have h : (fun x : M =>
        (((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E)) =
        (fun x : M => (X x : E)) + (fun x : M => (Y x : E)) := by
      funext x
      change ((X + Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) =
        ((X x : E) + (Y x : E))
      simp [ContMDiffSection.coe_add, Pi.add_apply]
    rw [h]
    exact hX.add hY
  smul_mem' := by
    intro c X hX
    change HasCompactSupport
      (fun x : M =>
        (((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E))
    have h : (fun x : M =>
        (((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x : E)) =
        (fun _ : M => c) • (fun x : M => (X x : E)) := by
      funext x
      change ((c • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E) =
        c • (X x : E)
      simp [ContMDiffSection.coe_smul, Pi.smul_apply]
    rw [h]
    exact hX.smul_left

omit [Module.Finite ℝ E] in
@[simp]
lemma mem_compactlySupportedSmoothTangentSections
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} :
    X ∈ compactlySupportedSmoothTangentSections I M ↔
      HasCompactSupport (fun x : M => (X x : E)) := Iff.rfl

omit [Module.Finite ℝ E] in
theorem compactlySupportedSmoothFunctions_mul_mem_left
    {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ compactlySupportedSmoothFunctions I M)
    (f' : C^∞⟮I, M; ℝ⟯) :
    f * f' ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have h : ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) * (f' : M → ℝ) := by
    ext x
    simp [ContMDiffMap.coe_mul, Pi.mul_apply]
  rw [h]
  exact hf.mul_right

omit [Module.Finite ℝ E] in
theorem compactlySupportedSmoothFunctions_mul_mem_right
    (f : C^∞⟮I, M; ℝ⟯) {f' : C^∞⟮I, M; ℝ⟯}
    (hf' : f' ∈ compactlySupportedSmoothFunctions I M) :
    f * f' ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have h : ((f * f' : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) * (f' : M → ℝ) := by
    ext x
    simp [ContMDiffMap.coe_mul, Pi.mul_apply]
  rw [h]
  exact hf'.mul_left

omit [Module.Finite ℝ E] in
theorem compactlySupportedSmoothFunctions_mul_mem
    {f f' : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ compactlySupportedSmoothFunctions I M)
    (_hf' : f' ∈ compactlySupportedSmoothFunctions I M) :
    f * f' ∈ compactlySupportedSmoothFunctions I M :=
  compactlySupportedSmoothFunctions_mul_mem_left hf f'

section DirectionalDerivative

variable [T2Space M] [SigmaCompactSpace M]

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
private lemma vectorFieldAction_eq_zero_of_vectorField_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯)
    {x : M} (hx : X x = 0) :
    vectorFieldAction I M X f x = 0 := by
  simp [vectorFieldAction, hx]

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem compactlySupportedSmoothTangentSections_action_mem
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hX : X ∈ compactlySupportedSmoothTangentSections I M)
    (f : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X f ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport
    ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hcoe :
      ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
        vectorFieldAction I M X f := rfl
  rw [hcoe]
  refine HasCompactSupport.mono (f := fun x : M => (X x : E)) hX ?_
  intro x hx
  by_contra hXx
  apply hx
  have : X x = 0 := by
    simpa using hXx
  exact vectorFieldAction_eq_zero_of_vectorField_eq_zero X f this

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem compactlySupportedSmoothFunctions_action_of_smooth_section
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ compactlySupportedSmoothFunctions I M) :
    vectorFieldActionSmooth I M X f ∈ compactlySupportedSmoothFunctions I M := by
  change HasCompactSupport
    ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hcoe :
      ((vectorFieldActionSmooth I M X f : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
        vectorFieldAction I M X f := rfl
  rw [hcoe]
  refine HasCompactSupport.mono' (f := (f : M → ℝ)) hf ?_
  intro x hx
  by_contra hxnot
  apply hx
  have hfEq : (f : M → ℝ) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxnot
  have hmfd : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x = mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x :=
    hfEq.mfderiv_eq
  have : extDerivFun (I := I) (f : M → ℝ) x (X x) = 0 := by
    have hmfd_zero : mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x = 0 := by
      rw [hmfd]
      exact mfderiv_const
    simp [extDerivFun, hmfd_zero]
  simpa [vectorFieldAction] using this

end DirectionalDerivative

section CovariantDerivativeClosure

variable [T2Space M] [SigmaCompactSpace M]

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem compactlySupportedSmoothTangentSections_conn_mem_of_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hX : X ∈ compactlySupportedSmoothTangentSections I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X Y ∈ compactlySupportedSmoothTangentSections I M := by
  change HasCompactSupport
    (fun x : M => ((concreteConn I M cov X Y) x : E))
  refine HasCompactSupport.mono (f := fun x : M => (X x : E)) hX ?_
  intro x hx
  by_contra hXx
  apply hx
  have hXx' : X x = 0 := by simpa using hXx
  change ((concreteConn I M cov X Y) x : E) = 0
  have : (concreteConn I M cov X Y) x = 0 := by
    simp [concreteConn_apply, hXx']
  simpa using this

omit [Module.Finite ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem compactlySupportedSmoothTangentSections_conn_mem_of_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hY : Y ∈ compactlySupportedSmoothTangentSections I M) :
    concreteConn I M cov X Y ∈ compactlySupportedSmoothTangentSections I M := by
  change HasCompactSupport
    (fun x : M => ((concreteConn I M cov X Y) x : E))
  refine HasCompactSupport.mono' (f := fun x : M => (Y x : E)) hY ?_
  intro x hx
  by_contra hxnot
  apply hx
  have hY_eq_E : (fun x : M => (Y x : E)) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxnot
  have hY_eq_dep : (fun x : M => Y x) =ᶠ[𝓝 x]
      (fun x : M => (0 : TangentSpace I x)) := by
    filter_upwards [hY_eq_E] with y hy
    have : (Y y : E) = (0 : E) := by simpa using hy
    exact this
  have hY_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun x : M => (TotalSpace.mk' E x (Y x) : TangentBundle I M)) x :=
    Y.mdifferentiableAt
  have hzero_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun x : M => (TotalSpace.mk' E x
        (0 : (TangentSpace I : M → Type _) x) : TangentBundle I M)) x :=
    mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I)
  have huniv : (Set.univ : Set M) ∈ 𝓝 x := Filter.univ_mem
  have hcov_eq :
      (cov.toFun (fun x : M => Y x)) x =
        (cov.toFun (fun x : M => (0 : (TangentSpace I : M → Type _) x))) x :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hY_diff hzero_diff huniv hY_eq_dep
  have hcov_zero :
      (cov.toFun (fun x : M => (0 : (TangentSpace I : M → Type _) x))) x = 0 := by
    have h0 : cov.toFun (fun x : M => (0 : (TangentSpace I : M → Type _) x)) =
        fun x : M => (0 : TangentSpace I x →L[ℝ] TangentSpace I x) :=
      cov.zero
    exact congrArg (fun φ => φ x) h0
  change ((concreteConn I M cov X Y) x : E) = 0
  have hcov_Y_zero : (cov.toFun (fun x : M => Y x)) x = 0 := hcov_eq.trans hcov_zero
  have : (concreteConn I M cov X Y) x = 0 := by
    change (cov.toFun (fun x : M => Y x)) x (X x) = 0
    rw [hcov_Y_zero]
    simp
  simpa using this

end CovariantDerivativeClosure

section LpDensity

open MeasureTheory
open scoped ENNReal

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure

theorem compactlySupportedSmoothFunctions_memLp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {f : C^∞⟮I, M; ℝ⟯} (hf : f ∈ compactlySupportedSmoothFunctions I M) :
    MeasureTheory.MemLp ((f : M → ℝ)) p
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hcont : Continuous (f : M → ℝ) := f.contMDiff.continuous
  have hsup : HasCompactSupport ((f : M → ℝ)) := hf
  exact hcont.memLp_of_hasCompactSupport (μ := riemannianVolumeMeasure (I := I) (M := M) g) hsup

private lemma exists_contMDiff_uniform_approx_sub_compact_support
    [T2Space M] [SigmaCompactSpace M]
    {φ : M → ℝ} (hφ : Continuous φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C^∞⟮I, M; ℝ⟯,
      (∀ x : M, |(g : M → ℝ) x - φ x| < δ) ∧
        Function.support (g : M → ℝ) ⊆ Function.support φ := by
  have hε_cont : Continuous (fun _ : M => δ) := continuous_const
  have hε_pos : ∀ x : M, 0 < (fun _ : M => δ) x := fun _ => hδ
  obtain ⟨g, g_approx, g_supp⟩ :=
    hφ.exists_contMDiff_approx (F := ℝ) I (⊤ : ℕ∞) hε_cont hε_pos
  refine ⟨g, ?_, g_supp⟩
  intro x
  have := g_approx x
  simpa [Real.dist_eq] using this

private lemma eLpNorm_le_of_bound_and_support_le_measure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    {h : M → ℝ} (_h_meas : AEStronglyMeasurable h
      (riemannianVolumeMeasure (I := I) (M := M) g))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h_bound : ∀ x : M, ‖h x‖ ≤ δ)
    {K : Set M} (hK : IsCompact K)
    (h_supp : ∀ x : M, x ∉ K → h x = 0) :
    eLpNorm h p (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g K) ^ (p.toReal⁻¹) *
        ENNReal.ofReal δ := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have h_eq : h = K.indicator h := by
    ext x
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, h_supp x hx]
  rw [h_eq]
  have hpt : ∀ x : M,
      ‖K.indicator h x‖ ≤ ‖K.indicator (fun _ : M => δ) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · have hnonneg : (0 : ℝ) ≤ δ := hδ
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        show ‖(δ : ℝ)‖ = δ from by rw [Real.norm_eq_abs]; exact abs_of_nonneg hnonneg]
      exact h_bound x
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have h1 : eLpNorm (K.indicator h) p μ ≤
      eLpNorm (K.indicator (fun _ : M => δ)) p μ :=
    eLpNorm_mono hpt
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have h2 : eLpNorm (K.indicator (fun _ : M => δ)) p μ ≤
      ‖(δ : ℝ)‖ₑ * μ K ^ (p.toReal⁻¹) := by
    have := eLpNorm_indicator_const_le (μ := μ) (s := K) (c := δ) p
    simpa [one_div] using this
  have hδ_enorm : ‖(δ : ℝ)‖ₑ = ENNReal.ofReal δ := by
    rw [Real.enorm_eq_ofReal hδ]
  calc
    eLpNorm (K.indicator h) p μ ≤ eLpNorm (K.indicator (fun _ : M => δ)) p μ := h1
    _ ≤ ‖(δ : ℝ)‖ₑ * μ K ^ (p.toReal⁻¹) := h2
    _ = ENNReal.ofReal δ * μ K ^ (p.toReal⁻¹) := by rw [hδ_enorm]
    _ = μ K ^ (p.toReal⁻¹) * ENNReal.ofReal δ := by rw [mul_comm]

private lemma exists_smoothCompactSupport_eLpNorm_sub_le_of_continuous
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {φ : M → ℝ} (hφ_cont : Continuous φ) (hφ_supp : HasCompactSupport φ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : C^∞⟮I, M; ℝ⟯,
      f ∈ compactlySupportedSmoothFunctions I M ∧
        eLpNorm (φ - (f : M → ℝ)) p
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤ ε := by
  classical
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set K : Set M := tsupport φ with hK_def
  have hK_compact : IsCompact K := hφ_supp
  have hμK_lt : μ K < ⊤ := hK_compact.measure_lt_top
  have hμK_ne : μ K ≠ ⊤ := hμK_lt.ne
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp'
  have hμK_pow_ne : μ K ^ (p.toReal⁻¹) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr (le_of_lt hp_toReal_pos)) hμK_ne
  set factor : ℝ≥0∞ := μ K ^ (p.toReal⁻¹) with hfactor_def
  have hfactor_ne_top : factor ≠ ⊤ := hμK_pow_ne
  have hchoice :
      ∃ δ : ℝ, 0 < δ ∧ factor * ENNReal.ofReal δ ≤ ε := by
    by_cases hfactor_zero : factor = 0
    · exact ⟨1, zero_lt_one, by
        rw [hfactor_zero, zero_mul]
        exact zero_le _⟩
    have hfactor_pos : 0 < factor := by
      exact lt_of_le_of_ne (zero_le _) (Ne.symm hfactor_zero)
    by_cases hε_top : ε = ⊤
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [hε_top]; exact le_top
    · have hε_lt : ε < ⊤ := lt_top_iff_ne_top.mpr hε_top
      have hε_toReal_pos : 0 < ε.toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨lt_of_le_of_ne (zero_le _) (Ne.symm hε), hε_lt⟩
      have hfactor_toReal_pos : 0 < factor.toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨hfactor_pos, lt_top_iff_ne_top.mpr hfactor_ne_top⟩
      set δ : ℝ := ε.toReal / (2 * factor.toReal) with hδ_eq
      have hδ_pos : 0 < δ := by positivity
      refine ⟨δ, hδ_pos, ?_⟩
      have hmul :
          factor * ENNReal.ofReal δ =
            ENNReal.ofReal (factor.toReal * δ) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfactor_ne_top]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      rw [hmul]
      have hprod : factor.toReal * δ = ε.toReal / 2 := by
        rw [hδ_eq]
        field_simp
      rw [hprod]
      have h1 : ENNReal.ofReal (ε.toReal / 2) ≤ ENNReal.ofReal ε.toReal := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith
      calc ENNReal.ofReal (ε.toReal / 2)
          ≤ ENNReal.ofReal ε.toReal := h1
        _ = ε := ENNReal.ofReal_toReal hε_top
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hchoice
  obtain ⟨f, hf_approx, hf_supp_le⟩ :=
    exists_contMDiff_uniform_approx_sub_compact_support (I := I) (M := M)
      hφ_cont hδ_pos
  set h : M → ℝ := φ - (f : M → ℝ) with hh_def
  have h_bound : ∀ x : M, ‖h x‖ ≤ δ := by
    intro x
    have := hf_approx x
    rw [Real.norm_eq_abs]
    change |φ x - (f : M → ℝ) x| ≤ δ
    have habs : |(f : M → ℝ) x - φ x| = |φ x - (f : M → ℝ) x| := abs_sub_comm _ _
    linarith [this, habs.symm.le]
  have h_supp : ∀ x : M, x ∉ K → h x = 0 := by
    intro x hx
    have hφx : φ x = 0 := by
      by_contra hne
      exact hx (subset_tsupport φ hne)
    have hfx : (f : M → ℝ) x = 0 := by
      by_contra hne
      have : x ∈ Function.support ((f : M → ℝ)) := hne
      have : x ∈ Function.support φ := hf_supp_le this
      exact this hφx
    simp [h, hφx, hfx]
  have h_meas : AEStronglyMeasurable h μ := by
    apply Continuous.aestronglyMeasurable
    exact hφ_cont.sub f.contMDiff.continuous
  have h_estimate := eLpNorm_le_of_bound_and_support_le_measure (I := I) (M := M) g
    (p := p) (h := h) h_meas (le_of_lt hδ_pos) h_bound hK_compact h_supp
  have hμK_eq : μ K ^ (p.toReal⁻¹) = factor := rfl
  refine ⟨f, ?_, ?_⟩
  · change HasCompactSupport ((f : M → ℝ))
    refine HasCompactSupport.mono' (f := φ) hφ_supp ?_
    intro x hx
    have : x ∈ Function.support φ := hf_supp_le hx
    exact subset_tsupport φ this
  · calc
      eLpNorm h p μ ≤ μ K ^ (p.toReal⁻¹) * ENNReal.ofReal δ := h_estimate
      _ = factor * ENNReal.ofReal δ := by rw [hμK_eq]
      _ ≤ ε := hδ_bound

theorem compactlySupportedSmoothFunctions_denseRange_in_Lp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    ∀ (u : MeasureTheory.Lp ℝ p (riemannianVolumeMeasure (I := I) (M := M) g))
      {ε : ℝ} (_hε : 0 < ε),
    ∃ (f : C^∞⟮I, M; ℝ⟯) (hmem : f ∈ compactlySupportedSmoothFunctions I M),
      ‖u - (compactlySupportedSmoothFunctions_memLp (I := I) (M := M) g hmem).toLp
        (f : M → ℝ)‖ < ε := by
  intro u ε hε
  classical
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  haveI : IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M) g
  haveI : (riemannianVolumeMeasure (I := I) (M := M) g).Regular :=
    riemannianVolumeMeasure_regular (I := I) (M := M) g
  haveI : LocallyCompactSpace M := locallyCompactSpace_of_chartedSpace E H I M
  let μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have hμ_def : μ = riemannianVolumeMeasure (I := I) (M := M) g := rfl
  have hε2_pos : 0 < ε / 2 := by linarith
  have hε4_pos : 0 < ε / 4 := by linarith
  have hε4_enn_ne : ENNReal.ofReal (ε / 4) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hε4_pos
  have hu_mem : MemLp ((u : M → ℝ)) p μ := Lp.memLp u
  obtain ⟨φ, φ_supp, φ_approx, φ_cont, _φ_mem⟩ :=
    hu_mem.exists_hasCompactSupport_eLpNorm_sub_le (μ := μ) hp' hε4_enn_ne
  obtain ⟨f, hf_mem, f_approx⟩ :=
    exists_smoothCompactSupport_eLpNorm_sub_le_of_continuous
      (I := I) (M := M) g hp hp' φ_cont φ_supp hε4_enn_ne
  refine ⟨f, hf_mem, ?_⟩
  set fLp := (compactlySupportedSmoothFunctions_memLp (I := I) (M := M) g hf_mem).toLp
      ((f : M → ℝ))
  have h_fLp_eq : (fLp : M → ℝ) =ᵐ[μ] ((f : M → ℝ)) :=
    MemLp.coeFn_toLp _
  have h_sub_coe : ((u - fLp : Lp ℝ p μ) : M → ℝ) =ᵐ[μ]
      (u : M → ℝ) - (fLp : M → ℝ) := Lp.coeFn_sub u fLp
  have h_sub_eq_ae : ((u - fLp : Lp ℝ p μ) : M → ℝ) =ᵐ[μ]
      (u : M → ℝ) - (f : M → ℝ) := by
    filter_upwards [h_sub_coe, h_fLp_eq] with x hsub hf
    rw [hsub]; simp [hf]
  have heLp_eq : eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ =
      eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ :=
    eLpNorm_congr_ae h_sub_eq_ae
  have h_u_minus_φ_aem : AEStronglyMeasurable ((u : M → ℝ) - φ) μ :=
    hu_mem.1.sub φ_cont.aestronglyMeasurable
  have h_φ_minus_f_aem : AEStronglyMeasurable (φ - (f : M → ℝ)) μ :=
    φ_cont.aestronglyMeasurable.sub f.contMDiff.continuous.aestronglyMeasurable
  have htri_raw := eLpNorm_add_le (p := p) (μ := μ)
    h_u_minus_φ_aem h_φ_minus_f_aem hp
  have h_sum_eq : ((u : M → ℝ) - φ) + (φ - (f : M → ℝ)) =
      (u : M → ℝ) - (f : M → ℝ) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htri : eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ ≤
      eLpNorm ((u : M → ℝ) - φ) p μ + eLpNorm (φ - (f : M → ℝ)) p μ := by
    rw [← h_sum_eq]; exact htri_raw
  have hsum_bound : eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ ≤
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
    htri.trans (add_le_add φ_approx f_approx)
  have h_ofReal_add : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) =
      ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add (le_of_lt hε4_pos) (le_of_lt hε4_pos)]
    ring_nf
  have hsum_bound' : eLpNorm ((u : M → ℝ) - (f : M → ℝ)) p μ ≤
      ENNReal.ofReal (ε / 2) := hsum_bound.trans_eq h_ofReal_add
  have h_fLp_bound : eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ ≤
      ENNReal.ofReal (ε / 2) := by
    rw [heLp_eq]; exact hsum_bound'
  have hnorm_def : ‖u - fLp‖ = (eLpNorm (⇑(u - fLp)) p μ).toReal := Lp.norm_def _
  have h_ofReal_ne_top : ENNReal.ofReal (ε / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_toReal_bound : (eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ).toReal ≤ ε / 2 := by
    have := ENNReal.toReal_mono h_ofReal_ne_top h_fLp_bound
    calc (eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal := this
      _ = ε / 2 := ENNReal.toReal_ofReal (le_of_lt hε2_pos)
  calc ‖u - fLp‖ = (eLpNorm ((u - fLp : Lp ℝ p μ) : M → ℝ) p μ).toReal := hnorm_def
    _ ≤ ε / 2 := h_toReal_bound
    _ < ε := by linarith

theorem compactlySupportedSmoothFunctions_dense_image_in_Lp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (hp' : p ≠ ⊤) :
    Dense (Set.range
      (fun f : compactlySupportedSmoothFunctions I M =>
        ((compactlySupportedSmoothFunctions_memLp (I := I) (M := M) (p := p) g f.2).toLp
          ((f : C^∞⟮I, M; ℝ⟯) : M → ℝ) :
            MeasureTheory.Lp ℝ p (riemannianVolumeMeasure (I := I) (M := M) g)))) := by
  rw [Metric.dense_iff]
  intro u r hr
  obtain ⟨f, hf_mem, hbound⟩ :=
    compactlySupportedSmoothFunctions_denseRange_in_Lp (I := I) (M := M)
      g hp.out hp' u hr
  refine ⟨
    (compactlySupportedSmoothFunctions_memLp (I := I) (M := M) (p := p) g hf_mem).toLp
      ((f : C^∞⟮I, M; ℝ⟯) : M → ℝ),
    ?_, ?_⟩
  · rw [Metric.mem_ball, dist_comm]
    have hdist : dist u ((compactlySupportedSmoothFunctions_memLp
        (I := I) (M := M) (p := p) g hf_mem).toLp
      ((f : C^∞⟮I, M; ℝ⟯) : M → ℝ)) = ‖u - _‖ := dist_eq_norm u _
    rw [hdist]; exact hbound
  · exact ⟨⟨f, hf_mem⟩, rfl⟩

end LpDensity

end L2
end Integral
end DifferentialGeometry

end
