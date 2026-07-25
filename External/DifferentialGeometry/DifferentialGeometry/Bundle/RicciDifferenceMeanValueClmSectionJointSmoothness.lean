import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

lemma contMDiffAt_clm_of_pointwise_jointSource
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {n : WithTop ℕ∞}
    {A : X → (F₁ →L[ℝ] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IX 𝓘(ℝ, F₂) n (fun q => A q v) x) :
    ContMDiffAt IX 𝓘(ℝ, F₁ →L[ℝ] F₂) n A x := by
  haveI : FiniteDimensional ℝ (F₁ →L[ℝ] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis ℝ F₁
  let evalBasis : (F₁ →L[ℝ] F₂) →L[ℝ] (Fin (Module.finrank ℝ F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  haveI : FiniteDimensional ℝ (Fin (Module.finrank ℝ F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let gCLM : (Fin (Module.finrank ℝ F₁) → F₂) →L[ℝ] (F₁ →L[ℝ] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ y, gCLM (evalBasis y) = y := fun y => congr($(hgLM) y)
  have hEA : ContMDiffAt IX 𝓘(ℝ, Fin _ → F₂) n (evalBasis ∘ A) x :=
    contMDiffAt_pi_space.mpr fun i => h (bF₁ i)
  have hcompose : A = gCLM ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [hcompose]
  exact gCLM.contDiff.contMDiff.contMDiffAt.comp _ hEA

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem contMDiff_clm_section_of_pointwise_joint_manifold_time
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
    [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
    [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
    [ContMDiffVectorBundle ∞ F₁ V₁ I]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [ContMDiffVectorBundle ∞ F₂ V₂ I]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    (φ : ∀ p : M × ℝ, V₁ p.1 →L[ℝ] V₂ p.1)
    (h : ∀ (Y : Cₛ^∞⟮I; F₁, V₁⟯),
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
        (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y p.1)))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (F₁ →L[ℝ] F₂)
        (E := fun x : M => V₁ x →L[ℝ] V₂ x) p.1 (φ p)) := by
  intro p₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  apply contMDiffAt_clm_of_pointwise_jointSource (IX := I.prod 𝓘(ℝ, ℝ)) (X := M × ℝ)
  intro v
  let e₁ := trivializationAt F₁ V₁ x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ F₁
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ V₁ x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hφY : ∀ i, ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y i p.1))) := fun i => h (Y i)
  have hφY_fiber : ∀ i, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => (e₂ ⟨p.1, φ p (Y i p.1)⟩).2) p₀ := fun i => by
    have hi := (Bundle.contMDiffAt_totalSpace (F := F₂) (E := V₂)).mp ((hφY i) p₀)
    exact hi.2
  have hsum : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => ∑ i, b.repr v i • (e₂ ⟨p.1, φ p (Y i p.1)⟩).2) p₀ := by
    apply ContMDiffAt.sum
    intro i _
    exact (contMDiffAt_const (c := (b.repr v i : ℝ))).smul (hφY_fiber i)
  refine hsum.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ p : M × ℝ in 𝓝 p₀, p.1 ∈ e₁.baseSet :=
    continuousAt_fst (e₁.open_baseSet.mem_nhds he₁)
  have h_base₂ : ∀ᶠ p : M × ℝ in 𝓝 p₀, p.1 ∈ e₂.baseSet :=
    continuousAt_fst (e₂.open_baseSet.mem_nhds he₂)
  have h_frame : ∀ᶠ p : M × ℝ in 𝓝 p₀, ∀ i, (Y i) p.1 = e₁.localFrame b i p.1 := by
    have hYnhd : ∀ᶠ x in 𝓝 x₀, ∀ i, (Y i) x = e₁.localFrame b i x := hY
    exact continuousAt_fst hYnhd
  filter_upwards [h_base₁, h_base₂, h_frame] with p hx₁ hx₂ hYp
  have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have h_inCoord : (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ p.1 x₀ p.1 (φ p)) v =
      e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 v)) := rfl
  rw [h_inCoord]
  have h₁ : e₁.symmL ℝ p.1 v = ∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i) := by
    conv_lhs => rw [hv_decomp]
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₂ : (φ p) (∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i)) =
      ∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i)) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₃ : e₂.continuousLinearMapAt ℝ p.1 (∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i))) =
      ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 (b i))) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  rw [h₁, h₂, h₃]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  have h_lf : e₁.symmL ℝ p.1 (b i) = (Y i) p.1 := by
    rw [hYp i]
    rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  rw [h_lf]
  rw [Trivialization.continuousLinearMapAt_apply]
  exact congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e₂) hx₂) _

lemma contMDiffWithinAt_clm_of_pointwise_jointSource
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {n : WithTop ℕ∞}
    {A : X → (F₁ →L[ℝ] F₂)} {sX : Set X} {x : X}
    (h : ∀ v, ContMDiffWithinAt IX 𝓘(ℝ, F₂) n (fun q => A q v) sX x) :
    ContMDiffWithinAt IX 𝓘(ℝ, F₁ →L[ℝ] F₂) n A sX x := by
  haveI : FiniteDimensional ℝ (F₁ →L[ℝ] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis ℝ F₁
  let evalBasis : (F₁ →L[ℝ] F₂) →L[ℝ] (Fin (Module.finrank ℝ F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  haveI : FiniteDimensional ℝ (Fin (Module.finrank ℝ F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let gCLM : (Fin (Module.finrank ℝ F₁) → F₂) →L[ℝ] (F₁ →L[ℝ] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ y, gCLM (evalBasis y) = y := fun y => congr($(hgLM) y)
  have hEA : ContMDiffWithinAt IX 𝓘(ℝ, Fin _ → F₂) n (evalBasis ∘ A) sX x :=
    contMDiffWithinAt_pi_space.mpr fun i => h (bF₁ i)
  have hcompose : A = gCLM ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [hcompose]
  exact gCLM.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt _ hEA

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem contMDiffOn_clm_section_of_pointwise_joint_manifold_time
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
    [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, TopologicalSpace (V₁ x)]
    [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
    [ContMDiffVectorBundle ∞ F₁ V₁ I]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [ContMDiffVectorBundle ∞ F₂ V₂ I]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    (φ : ∀ p : M × ℝ, V₁ p.1 →L[ℝ] V₂ p.1) {S : Set ℝ}
    (h : ∀ (Y : Cₛ^∞⟮I; F₁, V₁⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
        (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y p.1)))
        ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (F₁ →L[ℝ] F₂)
        (E := fun x : M => V₁ x →L[ℝ] V₂ x) p.1 (φ p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  apply contMDiffWithinAt_clm_of_pointwise_jointSource (IX := I.prod 𝓘(ℝ, ℝ)) (X := M × ℝ)
  intro v
  let e₁ := trivializationAt F₁ V₁ x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ F₁
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ V₁ x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hφY : ∀ i, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, F₂)) ∞
      (fun p : M × ℝ => TotalSpace.mk' F₂ (E := V₂) p.1 (φ p (Y i p.1)))
      ((Set.univ : Set M) ×ˢ S) := fun i => h (Y i)
  have hφY_fiber : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => (e₂ ⟨p.1, φ p (Y i p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := fun i => by
    have hi := (Bundle.contMDiffWithinAt_totalSpace (F := F₂) (E := V₂)).mp ((hφY i) p₀ hp₀)
    exact hi.2
  have hsum : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F₂) ∞
      (fun p : M × ℝ => ∑ i, b.repr v i • (e₂ ⟨p.1, φ p (Y i p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    apply ContMDiffWithinAt.sum
    intro i _
    exact (contMDiffWithinAt_const (c := (b.repr v i : ℝ))).smul (hφY_fiber i)
  refine hsum.congr_of_eventuallyEq ?_ ?_
  · have h_base₁ : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e₁.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e₁.open_baseSet.mem_nhds he₁)
    have h_base₂ : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e₂.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e₂.open_baseSet.mem_nhds he₂)
    have h_frame : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        ∀ i, (Y i) p.1 = e₁.localFrame b i p.1 := by
      have hYnhd : ∀ᶠ x in 𝓝 x₀, ∀ i, (Y i) x = e₁.localFrame b i x := hY
      exact (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀)) hYnhd
    filter_upwards [h_base₁, h_base₂, h_frame] with p hx₁ hx₂ hYp
    have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    have h_inCoord : (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ p.1 x₀ p.1 (φ p)) v =
        e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 v)) := rfl
    rw [h_inCoord]
    have h₁ : e₁.symmL ℝ p.1 v = ∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i) := by
      conv_lhs => rw [hv_decomp]
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₂ : (φ p) (∑ i, (b.repr v) i • e₁.symmL ℝ p.1 (b i)) =
        ∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i)) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₃ : e₂.continuousLinearMapAt ℝ p.1 (∑ i, (b.repr v) i • (φ p) (e₁.symmL ℝ p.1 (b i))) =
        ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ p.1 ((φ p) (e₁.symmL ℝ p.1 (b i))) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    rw [h₁, h₂, h₃]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    have h_lf : e₁.symmL ℝ p.1 (b i) = (Y i) p.1 := by
      rw [hYp i]
      rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    rw [h_lf]
    rw [Trivialization.continuousLinearMapAt_apply]
    exact congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e₂) hx₂) _
  · have hx₁ : x₀ ∈ e₁.baseSet := he₁
    have hx₂ : x₀ ∈ e₂.baseSet := he₂
    have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    have h_inCoord : (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ p₀.1 x₀ p₀.1 (φ p₀)) v =
        e₂.continuousLinearMapAt ℝ p₀.1 ((φ p₀) (e₁.symmL ℝ p₀.1 v)) := rfl
    rw [h_inCoord]
    have h₁ : e₁.symmL ℝ p₀.1 v = ∑ i, (b.repr v) i • e₁.symmL ℝ p₀.1 (b i) := by
      conv_lhs => rw [hv_decomp]
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₂ : (φ p₀) (∑ i, (b.repr v) i • e₁.symmL ℝ p₀.1 (b i)) =
        ∑ i, (b.repr v) i • (φ p₀) (e₁.symmL ℝ p₀.1 (b i)) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    have h₃ : e₂.continuousLinearMapAt ℝ p₀.1 (∑ i, (b.repr v) i • (φ p₀) (e₁.symmL ℝ p₀.1 (b i))) =
        ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ p₀.1 ((φ p₀) (e₁.symmL ℝ p₀.1 (b i))) := by
      rw [map_sum]; congr 1; ext i; rw [map_smul]
    rw [h₁, h₂, h₃]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    have hYnhd : ∀ᶠ x in 𝓝 x₀, ∀ i, (Y i) x = e₁.localFrame b i x := hY
    have hY0 : ∀ i, (Y i) x₀ = e₁.localFrame b i x₀ := hYnhd.self_of_nhds
    have h_lf : e₁.symmL ℝ p₀.1 (b i) = (Y i) p₀.1 := by
      rw [← hx₀, hY0 i]
      rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    rw [h_lf]
    rw [Trivialization.continuousLinearMapAt_apply]
    exact congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e₂) hx₂) _

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
