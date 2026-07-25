import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvBridge

set_option autoImplicit false
set_option linter.style.longLine false





















noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv
open Filter Topology
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]






omit [CompleteSpace E] in
theorem exists_cInf_subseq_finiteFamily
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    {ι : Type*} (s : Finset ι) (Φ : ι → ℕ → E → F)
    (hΦ : ∀ p ∈ s, ∀ k, ContDiff Real (⊤ : ℕ∞) (Φ p k))
    (hbdd : ∀ p ∈ s, ∀ r : ℕ, ∀ K : Set E, IsCompact K →
        ∃ Mr : Real, ∀ k, ∀ x ∈ K, ‖iteratedFDeriv Real r (Φ p k) x‖ ≤ Mr) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ p ∈ s,
      ∃ Φinf : E → F, MapCInfConvOnCompacts (Set.univ : Set E) (fun k => Φ p (φ k)) Φinf := by
  classical
  revert hΦ hbdd
  induction s using Finset.induction with
  | empty =>
    intro _ _
    exact ⟨id, strictMono_id, fun p hp => by simp at hp⟩
  | @insert a s ha IH =>
    intro hΦ hbdd
    obtain ⟨φ, hφ, hconv⟩ := IH (fun p hp => hΦ p (Finset.mem_insert_of_mem hp))
      (fun p hp => hbdd p (Finset.mem_insert_of_mem hp))
    obtain ⟨ψ, Φa, hψ, -, hΦaconv⟩ :=
      exists_cInf_subseq (fun k => Φ a (φ k))
        (fun k => hΦ a (Finset.mem_insert_self a s) (φ k))
        (fun r K hK => by
          obtain ⟨Mr, hMr⟩ := hbdd a (Finset.mem_insert_self a s) r K hK
          exact ⟨Mr, fun k x hx => hMr (φ k) x hx⟩)
    refine ⟨φ ∘ ψ, hφ.comp hψ, fun p hp => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hps
    · exact ⟨Φa, hΦaconv⟩
    · obtain ⟨Φinf, hΦinf⟩ := hconv p hps
      exact ⟨Φinf, hΦinf.comp_subseq hψ⟩








theorem exists_framePairs_diag
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (φ : ℕ → ℕ) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ (i j : Fin (Module.finrank Real E)), ∃ Φinf : E → Real,
        MapCInfConvOnCompacts (Set.univ : Set E)
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) Φinf := by
  classical
  set Vfam : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) →
      Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun p => Function.update (fun _ : Fin 2 => frame p.1) 1 (frame p.2) with hVfam
  have hbdd' : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q ((gSeq ∘ φ) k) gRef z ≤ C := by
    intro q K hK; obtain ⟨C, hC⟩ := hbdd q K hK; exact ⟨C, fun k z hz => hC (φ k) z hz⟩
  obtain ⟨χ, hχcd, htsupp, hχ1, hfam⟩ :=
    exists_chart_engineInput_family (I := I) gRef (gSeq ∘ φ) hbdd' x₀ Vfam hK₀ hK₀chart
  set Φ : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) → ℕ → E → Real :=
    fun p k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) ((gSeq ∘ φ) k)) 0) w
          (fun a => Vfam p a w)) z with hΦ
  obtain ⟨ψ, hψ, hconv⟩ :=
    exists_cInf_subseq_finiteFamily (Finset.univ : Finset (Fin (Module.finrank Real E) ×
        Fin (Module.finrank Real E))) Φ
      (fun p _ k => (hfam p).1 k)
      (fun p _ r K _ => by
        obtain ⟨Mr, hMr⟩ := (hfam p).2 r
        exact ⟨Mr, fun k x _ => hMr k x⟩)
  refine ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, fun i j => ?_⟩
  obtain ⟨Φinf, hΦinf⟩ := hconv (i, j) (Finset.mem_univ _)
  exact ⟨Φinf, hΦinf⟩


theorem exists_pairs_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (φ : ℕ → ℕ) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ (i j : Fin (Module.finrank Real E)), ∃ Φinf : E → Real,
        MapCInfConvOnCompacts (Set.univ : Set E)
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) Φinf := by
  classical
  set Vfam : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) →
      Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun p => Function.update (fun _ : Fin 2 => frame p.1) 1 (frame p.2) with hVfam
  have hbdd' : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K,
        metricCovDerivNorm (I := I) q ((gSeq ∘ φ) k) (gRef r) z ≤ C := by
    intro r q hqr K hK
    obtain ⟨C, hC⟩ := hbdd r q hqr K hK
    exact ⟨C, fun k z hz => hC (φ k) z hz⟩
  obtain ⟨χ, hχcd, htsupp, hχ1, hfam⟩ :=
    engine_input_refs (I := I) gBase gRef (gSeq ∘ φ) hbdd' x₀ Vfam hK₀ hK₀chart
  set Φ : (Fin (Module.finrank Real E) × Fin (Module.finrank Real E)) → ℕ → E → Real :=
    fun p k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gBase
        (Tensor0SBundle.metricTensorField (I := I) ((gSeq ∘ φ) k)) 0) w
          (fun a => Vfam p a w)) z with hΦ
  obtain ⟨ψ, hψ, hconv⟩ :=
    exists_cInf_subseq_finiteFamily (Finset.univ : Finset (Fin (Module.finrank Real E) ×
        Fin (Module.finrank Real E))) Φ
      (fun p _ k => (hfam p).1 k)
      (fun p _ r K _ => by
        obtain ⟨Mr, hMr⟩ := (hfam p).2 r
        exact ⟨Mr, fun k x _ => hMr k x⟩)
  refine ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, fun i j => ?_⟩
  obtain ⟨Φinf, hΦinf⟩ := hconv (i, j) (Finset.mem_univ _)
  exact ⟨Φinf, hΦinf⟩






theorem framePairs_pinned
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x))) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ (i j : Fin (Module.finrank Real E)),
        MapCInfConvOnCompacts (Set.univ : Set E)
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) := by
  classical
  obtain ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, hpairs0⟩ :=
    exists_framePairs_diag (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart frame φ
  refine ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, fun i j => ?_⟩
  obtain ⟨Φinf, hΦinf⟩ := hpairs0 i j

  have hinner : ∀ (g : SmoothRiemannianMetric I M) (w : M),
      (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)
        = g.inner w (frame i w) (frame j w) := by
    intro g w
    show (Tensor0SBundle.metricTensorField (I := I) g) w
        (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)
      = g.inner w (frame i w) (frame j w)
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [Function.update_of_ne, Function.update_self]
  have hval : ∀ (g : SmoothRiemannianMetric I M) (z : E),
      χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) g) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z
        = χ z * g.inner ((extChartAt I x₀).symm z)
            (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z)) := by
    intro g z
    rw [writtenInExtChartAt_real_apply, hinner g ((extChartAt I x₀).symm z)]
  have hpin : Φinf = (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) := by
    funext z
    have hseq := tendsto_of_cInf hΦinf (Set.mem_univ z)
    have hlim : Filter.Tendsto
        (fun k => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
        Filter.atTop (nhds (χ z * (gInf.inner ((extChartAt I x₀).symm z)
          (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z))))) := by
      have hcont : Continuous
          (fun η : TangentSpace I ((extChartAt I x₀).symm z) →L[Real]
              TangentSpace I ((extChartAt I x₀).symm z) →L[Real] Real =>
            η (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z))) :=
        ((ContinuousLinearMap.apply Real Real
            (frame j ((extChartAt I x₀).symm z))).comp
          (ContinuousLinearMap.apply Real (TangentSpace I ((extChartAt I x₀).symm z) →L[Real] Real)
            (frame i ((extChartAt I x₀).symm z)))).continuous
      have hbase := ((hcont.tendsto _).comp
        ((hconv ((extChartAt I x₀).symm z)).comp hψ.tendsto_atTop)).const_mul (χ z)
      refine hbase.congr (fun k => ?_)
      rw [hval (gSeq (φ (ψ k))) z]
      simp only [Function.comp_apply]
    rw [hval gInf z]
    exact tendsto_nhds_unique hseq hlim
  rw [hpin] at hΦinf
  exact hΦinf


theorem pairs_pinned_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x))) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real),
      StrictMono ψ ∧ ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ (i j : Fin (Module.finrank Real E)),
        MapCInfConvOnCompacts (Set.univ : Set E)
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
                (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) := by
  classical
  obtain ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, hpairs0⟩ :=
    exists_pairs_refs (I := I) gBase gRef gSeq hbdd x₀ hK₀ hK₀chart frame φ
  refine ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, fun i j => ?_⟩
  obtain ⟨Φinf, hΦinf⟩ := hpairs0 i j
  have hinner : ∀ (g : SmoothRiemannianMetric I M) (w : M),
      (covDerivOfField (I := I) gBase (Tensor0SBundle.metricTensorField (I := I) g) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)
        = g.inner w (frame i w) (frame j w) := by
    intro g w
    show (Tensor0SBundle.metricTensorField (I := I) g) w
        (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)
      = g.inner w (frame i w) (frame j w)
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [Function.update_of_ne, Function.update_self]
  have hval : ∀ (g : SmoothRiemannianMetric I M) (z : E),
      χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gBase
            (Tensor0SBundle.metricTensorField (I := I) g) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z
        = χ z * g.inner ((extChartAt I x₀).symm z)
            (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z)) := by
    intro g z
    rw [writtenInExtChartAt_real_apply, hinner g ((extChartAt I x₀).symm z)]
  have hpin : Φinf = (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gBase
        (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) := by
    funext z
    have hseq := tendsto_of_cInf hΦinf (Set.mem_univ z)
    have hlim : Filter.Tendsto
        (fun k => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gBase
            (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
        Filter.atTop (nhds (χ z * (gInf.inner ((extChartAt I x₀).symm z)
          (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z))))) := by
      have hcont : Continuous
          (fun η : TangentSpace I ((extChartAt I x₀).symm z) →L[Real]
              TangentSpace I ((extChartAt I x₀).symm z) →L[Real] Real =>
            η (frame i ((extChartAt I x₀).symm z)) (frame j ((extChartAt I x₀).symm z))) :=
        ((ContinuousLinearMap.apply Real Real
            (frame j ((extChartAt I x₀).symm z))).comp
          (ContinuousLinearMap.apply Real (TangentSpace I ((extChartAt I x₀).symm z) →L[Real] Real)
            (frame i ((extChartAt I x₀).symm z)))).continuous
      have hbase := ((hcont.tendsto _).comp
        ((hconv ((extChartAt I x₀).symm z)).comp hψ.tendsto_atTop)).const_mul (χ z)
      refine hbase.congr (fun k => ?_)
      rw [hval (gSeq (φ (ψ k))) z]
      simp only [Function.comp_apply]
    rw [hval gInf z]
    exact tendsto_nhds_unique hseq hlim
  rw [hpin] at hΦinf
  exact hΦinf






theorem exists_tower_conv
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x))) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real) (U : Set E),
      StrictMono ψ ∧ IsOpen U ∧
      (extChartAt I x₀ '' interior K₀ ⊆ U) ∧ Set.EqOn χ 1 U ∧
      ∀ (a : ℕ) (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) a) w
                (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) gInf) a) w
                (fun a => V a w)) z) := by
  classical
  obtain ⟨frame, vbasis, hframeσ, hspan⟩ := exists_frameData (I := I) x₀ hK₀ hK₀chart
  obtain ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, hpairs⟩ :=
    framePairs_pinned (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart frame φ gInf hconv

  set U : Set E := (extChartAt I x₀).target ∩
    (extChartAt I x₀).symm ⁻¹' interior K₀ with hUdef
  have hUopen : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := I) x₀) isOpen_interior
  have hUtarget : U ⊆ (extChartAt I x₀).target := fun z hz => hz.1
  have hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ K₀ := fun z hz => interior_subset hz.2
  have hχU : Set.EqOn χ 1 U := by
    intro z hz
    have hzK₀ : (extChartAt I x₀).symm z ∈ K₀ := hUKc z hz
    have := hχ1 ((extChartAt I x₀).symm z) hzK₀
    rwa [(extChartAt I x₀).right_inv hz.1] at this
  have hImg : extChartAt I x₀ '' interior K₀ ⊆ U := by
    rintro z ⟨y, hy, rfl⟩
    have hysrc : y ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]; exact hK₀chart (interior_subset hy)
    exact ⟨(extChartAt I x₀).map_source hysrc, by
      rw [Set.mem_preimage, (extChartAt I x₀).left_inv hysrc]; exact hy⟩
  refine ⟨ψ, χ, U, hψ, hUopen, hImg, hχU, fun a V => ?_⟩

  have hpairsU : ∀ (i j : Fin (Module.finrank Real E)),
      MapCInfConvOnCompacts U
        (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
        (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) :=
    fun i j K hK hKU p => (hpairs i j) K hK (Set.subset_univ K) p
  exact bumpTowerCarrier_all (I := I) gRef
    (fun k => Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k))))
    (Tensor0SBundle.metricTensorField (I := I) gInf) x₀ hχcd htsupp hUopen hχU hUtarget
    hK₀chart hUKc Finset.univ frame vbasis hframeσ hspan
    (fun V => hbase_of_framePairs (I := I) gRef
      (fun k => Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k))))
      (Tensor0SBundle.metricTensorField (I := I) gInf) x₀ hχcd htsupp hUopen hχU hUtarget
      hUKc Finset.univ frame hspan hpairsU V) a V


theorem exists_tower_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M) {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source)
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x))) :
    ∃ (ψ : ℕ → ℕ) (χ : E → Real) (U : Set E),
      StrictMono ψ ∧ IsOpen U ∧
      (extChartAt I x₀ '' interior K₀ ⊆ U) ∧ Set.EqOn χ 1 U ∧
      ∀ (a : ℕ) (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) a) w
                (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) gInf) a) w
                (fun a => V a w)) z) := by
  classical
  obtain ⟨frame, vbasis, hframeσ, hspan⟩ := exists_frameData (I := I) x₀ hK₀ hK₀chart
  obtain ⟨ψ, χ, hψ, hχcd, htsupp, hχ1, hpairs⟩ :=
    pairs_pinned_refs (I := I) gBase gRef gSeq hbdd
      x₀ hK₀ hK₀chart frame φ gInf hconv
  set U : Set E := (extChartAt I x₀).target ∩
    (extChartAt I x₀).symm ⁻¹' interior K₀ with hUdef
  have hUopen : IsOpen U :=
    (continuousOn_extChartAt_symm (I := I) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := I) x₀) isOpen_interior
  have hUtarget : U ⊆ (extChartAt I x₀).target := fun z hz => hz.1
  have hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ K₀ :=
    fun z hz => interior_subset hz.2
  have hχU : Set.EqOn χ 1 U := by
    intro z hz
    have hzK₀ : (extChartAt I x₀).symm z ∈ K₀ := hUKc z hz
    have := hχ1 ((extChartAt I x₀).symm z) hzK₀
    rwa [(extChartAt I x₀).right_inv hz.1] at this
  have hImg : extChartAt I x₀ '' interior K₀ ⊆ U := by
    rintro z ⟨y, hy, rfl⟩
    have hysrc : y ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]
      exact hK₀chart (interior_subset hy)
    exact ⟨(extChartAt I x₀).map_source hysrc, by
      rw [Set.mem_preimage, (extChartAt I x₀).left_inv hysrc]
      exact hy⟩
  refine ⟨ψ, χ, U, hψ, hUopen, hImg, hχU, fun a V => ?_⟩
  have hpairsU : ∀ (i j : Fin (Module.finrank Real E)),
      MapCInfConvOnCompacts U
        (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gBase
            (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
        (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gBase
            (Tensor0SBundle.metricTensorField (I := I) gInf) 0) w
              (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z) :=
    fun i j K hK hKU p => (hpairs i j) K hK (Set.subset_univ K) p
  exact bumpTowerCarrier_all (I := I) gBase
    (fun k => Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k))))
    (Tensor0SBundle.metricTensorField (I := I) gInf) x₀ hχcd htsupp hUopen hχU hUtarget
    hK₀chart hUKc Finset.univ frame vbasis hframeσ hspan
    (fun V => hbase_of_framePairs (I := I) gBase
      (fun k => Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k))))
      (Tensor0SBundle.metricTensorField (I := I) gInf) x₀ hχcd htsupp hUopen hχU hUtarget
      hUKc Finset.univ frame hspan hpairsU V) a V










theorem componentConv_covDeriv_of_chartCInf
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
      (nhds (gInf.inner x)))
    (a : ℕ) (x : M)
    (b : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (I0 : Fin (a + 2) → Fin (Module.finrank Real E)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (fun m => Tensor0SBundle.component0S (I := I) b
          (metricCovDeriv (I := I) (gSeq (φ (ψ m))) gRef a x) I0) Filter.atTop
        (nhds (Tensor0SBundle.component0S (I := I) b
          (metricCovDeriv (I := I) gInf gRef a x) I0)) := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K₀, hK₀cpt, hxint, hK₀src⟩ :=
    exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)
  obtain ⟨ψ, χ, U, hψ, hUopen, hImg, hχU, htower⟩ :=
    exists_tower_conv (I := I) gRef gSeq hbdd x hK₀cpt hK₀src φ gInf hconv
  refine ⟨ψ, hψ, ?_⟩
  have hxU : extChartAt I x x ∈ U := hImg ⟨x, hxint, rfl⟩
  set V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun q => (ContMDiffSection.exists_eq_at_gen (I := I) (n := (⊤ : ℕ∞)) x (b (I0 q))).choose
    with hVdef
  have hVval : ∀ q, V q x = b (I0 q) := fun q =>
    (ContMDiffSection.exists_eq_at_gen (I := I) (n := (⊤ : ℕ∞)) x (b (I0 q))).choose_spec
  have hcar : ∀ (g : SmoothRiemannianMetric I M),
      χ (extChartAt I x x) * writtenInExtChartAt I 𝓘(Real, Real) x
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) g) a) w (fun q => V q w)) (extChartAt I x x)
        = Tensor0SBundle.component0S (I := I) b (metricCovDeriv (I := I) g gRef a x) I0 := by
    intro g
    rw [hχU hxU, Pi.one_apply, one_mul, writtenInExtChartAt_real_apply,
      (extChartAt I x).left_inv (mem_extChartAt_source x)]
    simp only [hVval]
    rfl
  have htend := tendsto_of_cInf (htower a V) hxU
  rw [hcar gInf] at htend
  exact htend.congr (fun k => hcar (gSeq (φ (ψ k))))






omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [IsManifold I 2 M] in
theorem tangentConst_basis_expand (x₀ : M)
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (i : Fin (Module.finrank Real E)) (p : M) :
    tangentConstInChart (𝕜 := Real) (I := I) x₀ (basisE i) p
      = ∑ j : Fin (Module.finrank Real E),
          (Module.finBasis Real E).repr (basisE i) j •
            tangentConstInChart (𝕜 := Real) (I := I) x₀ (Module.finBasis Real E j) p := by
  simp only [tangentConstInChart_apply]
  conv_lhs => rw [← (Module.finBasis Real E).sum_repr (basisE i)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]





omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
theorem bz_eq_tangentConst (x : M)
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (i : Fin (Module.finrank Real E)) {z : M}
    (hz : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet) :
    (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
        I 1 basisE).toBasisAt hz) i
      = tangentConstInChart (𝕜 := Real) (I := I) x (basisE i) z := by
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he
  rw [IsLocalFrameOn.toBasisAt_coe, e.localFrame_apply_of_mem_baseSet basisE hz]
  simp [Bundle.Trivialization.basisAt, tangentConstInChart_apply, he]







omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem componentBz_eq_covDeriv
    (gRef : SmoothRiemannianMetric I M) (x : M)
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {Kc : Set M}
    (hframeσ : ∀ i, ∀ᶠ y in 𝓝ˢ Kc, frame i y
       = tangentConstInChart (𝕜 := Real) (I := I) x (Module.finBasis Real E i) y)
    (a : ℕ) (I0 : Fin (a + 2) → Fin (Module.finrank Real E))
    (g : SmoothRiemannianMetric I M)
    {z : M} (hzbase : z ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet)
    (hzKc : z ∈ Kc) :
    Tensor0SBundle.component0S (I := I)
        (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
            I 1 basisE).toBasisAt hzbase)
        (metricCovDeriv (I := I) g gRef a z) I0
      = (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) a) z
          (fun q => (∑ j : Fin (Module.finrank Real E),
            (Module.finBasis Real E).repr (basisE (I0 q)) j • frame j) z) := by
  rw [Tensor0SBundle.component0S_apply]
  show (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) a) z
      (fun q => (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
          I 1 basisE).toBasisAt hzbase) (I0 q))
    = (covDerivOfField (I := I) gRef (Tensor0SBundle.metricTensorField (I := I) g) a) z
      (fun q => (∑ j : Fin (Module.finrank Real E),
        (Module.finBasis Real E).repr (basisE (I0 q)) j • frame j) z)
  congr 1
  funext q
  rw [bz_eq_tangentConst, tangentConst_basis_expand, ContMDiffSection.finset_sum_apply_gen]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [(hframeσ j).self_of_nhdsSet z hzKc]

private def TowerExtractor
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M) : Prop :=
  ∀ (x₀ : M) (K₀ : Set M), IsCompact K₀ → K₀ ⊆ (chartAt H x₀).source →
    ∀ (φ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M),
      (∀ x : M, Filter.Tendsto (fun m => (gSeq (φ m)).inner x) Filter.atTop
        (nhds (gInf.inner x))) →
      ∃ (ψ : ℕ → ℕ) (χ : E → Real) (U : Set E),
        StrictMono ψ ∧ IsOpen U ∧
        (extChartAt I x₀ '' interior K₀ ⊆ U) ∧ Set.EqOn χ 1 U ∧
        ∀ (a : ℕ) (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _)),
          MapCInfConvOnCompacts U
            (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef
                (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ (ψ k)))) a) w
                  (fun a => V a w)) z)
            (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef
                (Tensor0SBundle.metricTensorField (I := I) gInf) a) w
                  (fun a => V a w)) z)







omit [I.Boundaryless] in
private theorem exists_patch_core
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hTower : TowerExtractor (I := I) gRef gSeq)
    (φ₀ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ₀ m)).inner x) Filter.atTop
      (nhds (gInf.inner x)))
    (x : M) :
    ∃ (W C : Set M), IsOpen W ∧ x ∈ W ∧ IsCompact C ∧ W ⊆ C ∧
      ∀ ρ : ℕ → ℕ, StrictMono ρ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ (p : ℕ) (ε : Real), 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p →
          ∀ z ∈ C, metricDerivNorm (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gRef z < ε := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K₀, hK₀cpt, hxK₀int, hK₀src⟩ :=
    exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)
  choose frame hframeσ using
    (fun i => exists_section_eqOn_compact (I := I) x (Module.finBasis Real E i) hK₀cpt hK₀src)
  obtain ⟨basisE, u', εgf, hu'open, hxu', hu'sub, -, -, -, -, -, hrev⟩ :=
    exists_goodFrame_compBound (I := I) gRef x
  obtain ⟨C, hCcpt, hxCint, hCsub⟩ :=
    exists_compact_subset (hu'open.inter isOpen_interior) ⟨hxu', hxK₀int⟩
  refine ⟨interior C, C, isOpen_interior, hxCint, hCcpt, interior_subset, fun ρ hρ => ?_⟩
  have hconv' : ∀ y : M, Filter.Tendsto (fun m => (gSeq ((φ₀ ∘ ρ) m)).inner y) Filter.atTop
      (nhds (gInf.inner y)) := fun y => (hconv y).comp hρ.tendsto_atTop
  obtain ⟨ψ, χ, U, hψ, hUopen, hImg, hχU, htower⟩ :=
    hTower x K₀ hK₀cpt hK₀src (φ₀ ∘ ρ) gInf hconv'
  refine ⟨ψ, hψ, fun p ε hε => ?_⟩

  have hCu' : C ⊆ u' := fun z hz => (hCsub hz).1
  have hCK₀ : C ⊆ interior K₀ := fun z hz => (hCsub hz).2
  have hCbase : C ⊆ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    fun z hz => hu'sub (hCu' hz)
  have hCsrc : C ⊆ (extChartAt I x).source := by
    rw [extChartAt_source]; exact fun z hz => hK₀src (interior_subset (hCK₀ hz))
  have hEcC : IsCompact (extChartAt I x '' C) :=
    hCcpt.image_of_continuousOn ((continuousOn_extChartAt (I := I) x).mono hCsrc)
  have hEcCU : extChartAt I x '' C ⊆ U := by
    rintro w ⟨z, hz, rfl⟩; exact hImg ⟨z, hCK₀ hz, rfl⟩

  set Vfun : (a : ℕ) → (Fin (a + 2) → Fin (Module.finrank Real E)) →
      Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    fun a I0 q => ∑ j : Fin (Module.finrank Real E),
      (Module.finBasis Real E).repr (basisE (I0 q)) j • frame j with hVfun

  have hcarval : ∀ (a : ℕ) (I0 : Fin (a + 2) → Fin (Module.finrank Real E))
      (g : SmoothRiemannianMetric I M) {z : M} (hz : z ∈ C),
      χ (extChartAt I x z) * writtenInExtChartAt I 𝓘(Real, Real) x
          (fun w : M => (covDerivOfField (I := I) gRef
            (Tensor0SBundle.metricTensorField (I := I) g) a) w (fun q => Vfun a I0 q w))
          (extChartAt I x z)
        = Tensor0SBundle.component0S (I := I)
            (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                I 1 basisE).toBasisAt (hCbase hz)) (metricCovDeriv (I := I) g gRef a z) I0 := by
    intro a I0 g z hz
    rw [hχU (hEcCU ⟨z, hz, rfl⟩), Pi.one_apply, one_mul, writtenInExtChartAt_real_apply,
      (extChartAt I x).left_inv (hCsrc hz)]
    exact (componentBz_eq_covDeriv (I := I) gRef x basisE frame hframeσ a I0 g
      (hCbase hz) (interior_subset (hCK₀ hz))).symm

  have key : ∀ a : ℕ, ∃ k0a : ℕ, a ≤ p → ∀ k : ℕ, k0a ≤ k → ∀ z ∈ C,
      metricDerivNorm (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gRef z < ε := by
    intro a
    by_cases ha : a ≤ p
    · set cardI : ℕ := Fintype.card (Fin (a + 2) → Fin (Module.finrank Real E)) with hcardI
      set Cgf : Real :=
        ((3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1)) ^ (a + 2) with hCgf
      have hcard0 : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) := Nat.cast_nonneg _
      have hCgf1 : (1 : Real) ≤ Cgf := one_le_pow₀ (by nlinarith)
      have hCgf0 : (0 : Real) < Cgf := lt_of_lt_of_le one_pos hCgf1
      have hsqc : (0 : Real) ≤ Real.sqrt (cardI : Real) := Real.sqrt_nonneg _
      have hden0 : (0 : Real) < 2 * Cgf * (Real.sqrt (cardI : Real) + 1) := by positivity
      set ε' : Real := ε / (2 * Cgf * (Real.sqrt (cardI : Real) + 1)) with hε'
      have hε'0 : 0 < ε' := div_pos hε hden0
      have perI0 : ∀ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
          ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ z : M, ∀ hz : z ∈ C,
            |Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt (hCbase hz))
                (metricDiffCovDerivAt (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gRef z) I0| ≤ ε' := by
        intro I0
        obtain ⟨k0, hk0⟩ := htower a (Vfun a I0) (extChartAt I x '' C) hEcC hEcCU 0 ε' hε'0
        refine ⟨k0, fun k hk z hz => ?_⟩
        have hb := hk0 k hk 0 le_rfl (extChartAt I x z) ⟨z, hz, rfl⟩
        simp only [mapDerivNorm, norm_iteratedFDeriv_zero, Function.comp_apply,
          Real.norm_eq_abs] at hb
        rw [hcarval a I0 (gSeq (φ₀ (ρ (ψ k)))) hz, hcarval a I0 gInf hz] at hb
        exact hb
      choose k0fn hk0fn using perI0
      refine ⟨Finset.univ.sup k0fn, fun _ k hk z hz => ?_⟩
      rw [metricDerivNorm]
      have hsumle : (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
            Tensor0SBundle.component0S (I := I)
              (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                  I 1 basisE).toBasisAt (hCbase hz))
              (metricDiffCovDerivAt (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gRef z) I0 ^ 2)
          ≤ (cardI : Real) * ε' ^ 2 := by
        calc (∑ I0 : Fin (a + 2) → Fin (Module.finrank Real E),
              Tensor0SBundle.component0S (I := I)
                (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet
                    I 1 basisE).toBasisAt (hCbase hz))
                (metricDiffCovDerivAt (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gRef z) I0 ^ 2)
            ≤ ∑ _I0 : Fin (a + 2) → Fin (Module.finrank Real E), ε' ^ 2 :=
              Finset.sum_le_sum (fun I0 _ => by
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _)
                  (hk0fn I0 k (le_trans (Finset.le_sup (Finset.mem_univ I0)) hk) z hz) 2)
          _ = (cardI : Real) * ε' ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardI]
      have hnormle : Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
          (metricDiffCovDerivAt (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gRef z) ≤ Cgf * ((cardI : Real) * ε' ^ 2) :=
        le_trans (hrev z (hCbase hz) (hCu' hz) (a + 2) _) (by gcongr)
      have hCgfsq : Cgf ≤ Cgf ^ 2 := le_self_pow₀ hCgf1 (by norm_num)
      have hsqCgf : Real.sqrt Cgf ≤ Cgf :=
        (Real.sqrt_le_sqrt hCgfsq).trans_eq (Real.sqrt_sq hCgf0.le)
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (a + 2) _)
          ≤ Real.sqrt (Cgf * ((cardI : Real) * ε' ^ 2)) := Real.sqrt_le_sqrt hnormle
        _ = Real.sqrt (Cgf * (cardI : Real)) * ε' := by
            rw [show Cgf * ((cardI : Real) * ε' ^ 2) = Cgf * (cardI : Real) * ε' ^ 2 by ring,
              Real.sqrt_mul (by positivity), Real.sqrt_sq hε'0.le]
        _ ≤ Cgf * (Real.sqrt (cardI : Real) + 1) * ε' := by
            gcongr ?_ * ε'
            rw [Real.sqrt_mul hCgf0.le]
            nlinarith [mul_le_mul_of_nonneg_right hsqCgf hsqc, hCgf0.le, hsqc]
        _ = ε / 2 := by rw [hε']; field_simp
        _ < ε := by linarith
    · exact ⟨0, fun h => absurd h ha⟩
  choose k0fn hk0fn using key
  refine ⟨(Finset.range (p + 1)).sup k0fn, fun k hk a ha z hz => ?_⟩
  exact hk0fn a ha k (le_trans (Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_of_le ha))) hk) z hz


theorem exists_uniform_patch
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (φ₀ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ₀ m)).inner x) Filter.atTop
      (nhds (gInf.inner x)))
    (x : M) :
    ∃ (W C : Set M), IsOpen W ∧ x ∈ W ∧ IsCompact C ∧ W ⊆ C ∧
      ∀ ρ : ℕ → ℕ, StrictMono ρ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ (p : ℕ) (ε : Real), 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p →
          ∀ z ∈ C, metricDerivNorm (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gRef z < ε := by
  apply exists_patch_core (I := I) gRef gSeq ?_ φ₀ gInf hconv x
  intro x₀ K₀ hK₀ hK₀chart φ gLim hLim
  exact exists_tower_conv (I := I) gRef gSeq hbdd x₀ hK₀ hK₀chart φ gLim hLim


theorem exists_patch_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (φ₀ : ℕ → ℕ) (gInf : SmoothRiemannianMetric I M)
    (hconv : ∀ x : M, Filter.Tendsto (fun m => (gSeq (φ₀ m)).inner x) Filter.atTop
      (nhds (gInf.inner x)))
    (x : M) :
    ∃ (W C : Set M), IsOpen W ∧ x ∈ W ∧ IsCompact C ∧ W ⊆ C ∧
      ∀ ρ : ℕ → ℕ, StrictMono ρ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ (p : ℕ) (ε : Real), 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p →
          ∀ z ∈ C, metricDerivNorm (I := I) a (gSeq (φ₀ (ρ (ψ k)))) gInf gBase z < ε := by
  apply exists_patch_core (I := I) gBase gSeq ?_ φ₀ gInf hconv x
  intro x₀ K₀ hK₀ hK₀chart φ gLim hLim
  exact exists_tower_refs (I := I) gBase gRef gSeq hbdd x₀ hK₀ hK₀chart φ gLim hLim

set_option maxHeartbeats 800000 in






theorem metricPreconvInf (hne : Nonempty M)
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (hlow : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M,
      MetricCInfConvOnCompacts (I := I) (fun k => gSeq (φ k)) gInf gRef := by
  classical
  obtain ⟨φ₀, hφ₀, gInf, hconv⟩ := metricPreconv_gInf (I := I) hne gRef gSeq hbdd hlow
  choose W C hWopen hxW hCcpt hWC hpatch using
    exists_uniform_patch (I := I) gRef gSeq hbdd φ₀ gInf hconv
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover W hWopen
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y⟩ := hne
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ y))
    exact ⟨z, hz⟩
  obtain ⟨e, hse⟩ := hscount.exists_eq_range hsne
  have hcovN : (Set.univ : Set M) ⊆ ⋃ n : ℕ, W (e n) := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (hscov hz)
    rw [hse] at hw
    obtain ⟨n, rfl⟩ := hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩
  obtain ⟨φd, hφd, hPφd⟩ := exists_diag_subseq
    (fun n φ => ∀ (p : ℕ) (ε : Real), 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p →
      ∀ z ∈ C (e n), metricDerivNorm (I := I) a (gSeq (φ₀ (φ k))) gInf gRef z < ε)
    (fun n φ hφ => by
      obtain ⟨ψ, hψ, hu⟩ := hpatch (e n) φ hφ
      refine ⟨ψ, hψ, fun p ε hε => ?_⟩
      obtain ⟨k0, hk0⟩ := hu p ε hε
      refine ⟨k0, fun k hk a ha z hz => ?_⟩
      simpa only [Function.comp_apply] using hk0 k hk a ha z hz)
    (fun n φ ψ hψ hP p ε hε => by
      obtain ⟨k0, hk0⟩ := hP p ε hε
      exact ⟨k0, fun k hk a ha z hz => hk0 (ψ k) (le_trans hk hψ.le_apply) a ha z hz⟩)
    (fun n φ m hP p ε hε => by
      obtain ⟨k0, hk0⟩ := hP p ε hε
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m ≤ k by omega)] at hval
      exact hval)
  refine ⟨φ₀ ∘ φd, hφ₀.comp hφd, gInf,
    metricCInfConvOnCompacts_of_normConv (I := I) (fun k => gSeq ((φ₀ ∘ φd) k)) gInf gRef ?_⟩
  intro p K hK ε hε
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun n => W (e n)) (fun n => hWopen (e n))
    (fun z hz => hcovN (Set.mem_univ z))
  have perN : ∀ n ∈ F, ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p →
      ∀ z ∈ C (e n), metricDerivNorm (I := I) a (gSeq (φ₀ (φd k))) gInf gRef z < ε :=
    fun n _ => hPφd n p ε hε
  choose k0fn hk0fn using perN
  refine ⟨F.attach.sup (fun n => k0fn n.1 n.2), fun k hk a ha z hz => ?_⟩
  obtain ⟨n, hn, hzw⟩ := Set.mem_iUnion₂.1 (hF hz)
  simpa only [Function.comp_apply] using
    hk0fn n hn k (le_trans (Finset.le_sup (f := fun n => k0fn n.1 n.2)
      (Finset.mem_attach F ⟨n, hn⟩)) hk) a ha z (hWC (e n) hzw)

set_option maxHeartbeats 800000 in

theorem metricCInf_refs (hne : Nonempty M)
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (hlow : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : M) (v : TangentSpace I x),
      c * gBase.inner x v v ≤ (gSeq k).inner x v v) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M,
      MetricCInfConvOnCompacts (I := I) (fun k => gSeq (φ k)) gInf gBase := by
  classical
  obtain ⟨φ₀, hφ₀, gInf, hconv⟩ :=
    metricPreconv_refs (I := I) hne gBase gRef gSeq hbdd hlow
  choose W C hWopen hxW hCcpt hWC hpatch using
    exists_patch_refs (I := I) gBase gRef gSeq hbdd φ₀ gInf hconv
  obtain ⟨s, hscount, hscov⟩ :=
    (isLindelof_univ (X := M)).elim_countable_subcover W hWopen
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y⟩ := hne
    obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.1 (hscov (Set.mem_univ y))
    exact ⟨z, hz⟩
  obtain ⟨e, hse⟩ := hscount.exists_eq_range hsne
  have hcovN : (Set.univ : Set M) ⊆ ⋃ n : ℕ, W (e n) := fun z hz => by
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 (hscov hz)
    rw [hse] at hw
    obtain ⟨n, rfl⟩ := hw
    exact Set.mem_iUnion.2 ⟨n, hzw⟩
  obtain ⟨φd, hφd, hPφd⟩ := exists_diag_subseq
    (fun n φ => ∀ (p : ℕ) (ε : Real), 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ a : ℕ, a ≤ p → ∀ z ∈ C (e n),
        metricDerivNorm (I := I) a (gSeq (φ₀ (φ k))) gInf gBase z < ε)
    (fun n φ hφ => by
      obtain ⟨ψ, hψ, hu⟩ := hpatch (e n) φ hφ
      refine ⟨ψ, hψ, fun p ε hε => ?_⟩
      obtain ⟨k0, hk0⟩ := hu p ε hε
      refine ⟨k0, fun k hk a ha z hz => ?_⟩
      simpa only [Function.comp_apply] using hk0 k hk a ha z hz)
    (fun n φ ψ hψ hP p ε hε => by
      obtain ⟨k0, hk0⟩ := hP p ε hε
      exact ⟨k0, fun k hk a ha z hz =>
        hk0 (ψ k) (le_trans hk hψ.le_apply) a ha z hz⟩)
    (fun n φ m hP p ε hε => by
      obtain ⟨k0, hk0⟩ := hP p ε hε
      refine ⟨k0 + m, fun k hk a ha z hz => ?_⟩
      have hval := hk0 (k - m) (by omega) a ha z hz
      simp only [Nat.sub_add_cancel (show m ≤ k by omega)] at hval
      exact hval)
  refine ⟨φ₀ ∘ φd, hφ₀.comp hφd, gInf,
    metricCInfConvOnCompacts_of_normConv (I := I)
      (fun k => gSeq ((φ₀ ∘ φd) k)) gInf gBase ?_⟩
  intro p K hK ε hε
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun n => W (e n)) (fun n => hWopen (e n))
    (fun z hz => hcovN (Set.mem_univ z))
  have perN : ∀ n ∈ F, ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ a : ℕ, a ≤ p →
      ∀ z ∈ C (e n), metricDerivNorm (I := I) a
        (gSeq (φ₀ (φd k))) gInf gBase z < ε :=
    fun n _ => hPφd n p ε hε
  choose k0fn hk0fn using perN
  refine ⟨F.attach.sup (fun n => k0fn n.1 n.2), fun k hk a ha z hz => ?_⟩
  obtain ⟨n, hn, hzw⟩ := Set.mem_iUnion₂.1 (hF hz)
  simpa only [Function.comp_apply] using
    hk0fn n hn k (le_trans (Finset.le_sup (f := fun n => k0fn n.1 n.2)
      (Finset.mem_attach F ⟨n, hn⟩)) hk) a ha z (hWC (e n) hzw)

end HCGCompactness
end DifferentialGeometry
