import Definitions.Def_DifferentialGeometry_SmoothRiemannianMetric
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.VectorBundle.Basic

/-! Induced metrics of smooth immersions. Supporting proofs are embedded
because they construct the proof fields of the metric definition.
Reused DifferentialGeometry code: Apache-2.0, commit 1b535dd102b94cc42b107cca27059687888f08b3. -/

section

/- Source: DifferentialGeometry.Bundle.Equiv -/

open Bundle

open scoped Manifold

section ToContMDiffVectorBundleEquivGeneral

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {n : WithTop ℕ∞}
  {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace HB B₁]
  {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace HB B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [ContMDiffVectorBundle n F₁ E₁ IB]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₂ E₂ IB]

lemma contMDiffAt_clm_of_pointwise
    {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
  have : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis 𝕜 F₁
  let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  have : FiniteDimensional 𝕜 (Fin (Module.finrank 𝕜 F₁) → F₂) := inferInstance
  obtain ⟨gLM, hgLM⟩ := evalBasis.toLinearMap.exists_leftInverse_of_injective
    (evalBasis.ker_eq_bot_of_injective evalBasis_inj)
  let g : (Fin (Module.finrank 𝕜 F₁) → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
    ⟨gLM, LinearMap.continuous_of_finiteDimensional _⟩
  have hg : ∀ x, g (evalBasis x) = x := fun x => congr($(hgLM) x)
  have hEA : ContMDiffAt IB 𝓘(𝕜, Fin _ → F₂) n (evalBasis ∘ A) x :=
    contMDiffAt_pi_space.mpr fun i => h (bF₁ i)
  have : A = g ∘ evalBasis ∘ A := by funext q; exact (hg (A q)).symm
  rw [this]
  exact g.contDiff.contMDiff.contMDiffAt.comp _ hEA

end ToContMDiffVectorBundleEquivGeneral

end

section

/- Source: DifferentialGeometry.Bundle.Frame -/

open scoped Manifold Topology ContDiff

open Bundle Filter

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 F]
  {n : ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, IsScalarTower ℝ 𝕜 (V x)]
  [VectorBundle ℝ F V]

variable {ι : Type*} {s : ι → (x : M) → V x} {u : Set M} {p : M}

theorem IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs.contMDiffOn i)
  · filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]

end

section

/- Source: DifferentialGeometry.Bundle.ClmSectionSmooth -/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set FiberBundle

open scoped Manifold Topology ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem cotangentCov_clmSection_smooth_aux
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    [T2Space M]
    (φ : ∀ x : M, TangentSpace I x →L[ℝ] V₂ x)
    (h : ∀ (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F₂)
        (E := fun x : M => TangentSpace I x →L[ℝ] V₂ x) x (φ x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
  intro v
  let e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ E
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hφY : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
      (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y i x))) := fun i => h (Y i)
  have hφY_fiber : ∀ i, ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := fun i => by
    have hi := (contMDiffAt_section (F := F₂) (E := V₂) x₀).mp ((hφY i) x₀)
    simpa [e₂, trivializationAt] using hi
  have hsum : ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => ∑ i, b.repr v i • (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := by
    apply ContMDiffAt.sum
    intro i _
    have hc : ContMDiffAt I 𝓘(ℝ) ∞ (fun _ : M => (b.repr v i : ℝ)) x₀ :=
      contMDiffAt_const
    exact hc.smul (hφY_fiber i)
  refine hsum.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet :=
    e₁.open_baseSet.mem_nhds he₁
  have h_base₂ : ∀ᶠ x in 𝓝 x₀, x ∈ e₂.baseSet :=
    e₂.open_baseSet.mem_nhds he₂
  filter_upwards [h_base₁, h_base₂, hY] with x hx₁ hx₂ hYx
  have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have h_inCoord :
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) F₂ V₂ x₀ x x₀ x (φ x)) v =
      e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x v)) := rfl
  rw [h_inCoord]
  have h₁ : e₁.symmL ℝ x v = ∑ i, (b.repr v) i • e₁.symmL ℝ x (b i) := by
    conv_lhs => rw [hv_decomp]
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₂ : (φ x) (∑ i, (b.repr v) i • e₁.symmL ℝ x (b i)) =
      ∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i)) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₃ : e₂.continuousLinearMapAt ℝ x
        (∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i))) =
      ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x (b i))) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  rw [h₁, h₂, h₃]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  have h_lf : e₁.symmL ℝ x (b i) = (Y i) x := by
    rw [hYx i]
    rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact e₁.symmL_apply hx₁ _
  rw [h_lf]
  change (Trivialization.continuousLinearMapAt ℝ e₂ x) ((φ x) ((Y i) x)) = _
  rw [show ⇑(e₂.continuousLinearMapAt ℝ x) = ⇑(e₂.linearMapAt ℝ x) from rfl,
    e₂.coe_linearMapAt_of_mem hx₂]

end DifferentialGeometry

end

end

section

/- Source: DifferentialGeometry.Geometry.Metric.MetricExistence -/

noncomputable section

open Bundle Manifold Set ContinuousLinearMap Bornology Metric

open scoped Manifold Topology ContDiff

namespace DifferentialGeometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem posDef_isVonNBounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < g v v) :
    Bornology.IsVonNBounded ℝ {v : E | g v v < 1} := by
  have hcont : Continuous (fun v : E => g v v) :=
    isBoundedBilinearMap_apply.continuous.comp (g.continuous.prodMk continuous_id)
  rw [NormedSpace.isVonNBounded_iff']
  obtain ⟨c, hc, hcoer⟩ : ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤ g v v := by
    rcases subsingleton_or_nontrivial E with hsub | hnt
    · exact ⟨1, one_pos, fun v => by
        have hv0 : v = 0 := Subsingleton.elim _ _
        subst hv0; simp⟩
    · have hsphere : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
      have hne : (Metric.sphere (0 : E) 1).Nonempty := by
        rw [NormedSpace.sphere_nonempty]; exact zero_le_one
      obtain ⟨v₀, hv₀, hmin⟩ := hsphere.exists_isMinOn hne hcont.continuousOn
      have hv₀0 : v₀ ≠ 0 := by intro h; rw [h] at hv₀; simp at hv₀
      refine ⟨g v₀ v₀, hpos v₀ hv₀0, ?_⟩
      intro v
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · have hvnorm : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
        have hscaleAll : ∀ (r : ℝ) (w : E), g (r • w) (r • w) = r ^ 2 * g w w := by
          intro r w
          rw [(g (r • w)).map_smul, map_smul, smul_apply,
            smul_eq_mul, smul_eq_mul]; ring
        have hu_sphere : ((‖v‖)⁻¹ • v) ∈ Metric.sphere (0 : E) 1 := by
          rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
          field_simp
        have hmin' : g v₀ v₀ ≤ g ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) := hmin hu_sphere
        have hvv : v = ‖v‖ • ((‖v‖)⁻¹ • v) := by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvnorm), one_smul]
        have hscale : g v v = ‖v‖ ^ 2 * g ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) := by
          conv_lhs => rw [hvv]
          rw [hscaleAll ‖v‖ ((‖v‖)⁻¹ • v)]
        rw [hscale]
        nlinarith [sq_nonneg ‖v‖, hvnorm, hmin']
  refine ⟨Real.sqrt (1 / c), fun v hv => ?_⟩
  simp only [Set.mem_ofPred_eq] at hv
  have h2 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hcoer v) hv
  have h3 : ‖v‖ ^ 2 < 1 / c := by rw [lt_div_iff₀ hc, mul_comm]; exact h2
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (1 / c) := Real.sqrt_le_sqrt h3.le

end Geometry

end DifferentialGeometry

end

end

section

/- Source: OpenGALib.Riemannian.Surface.InducedMetric -/

/-!
# Metrics induced by smooth immersions

The metric is pulled back by the actual manifold derivative. The assumptions
are smoothness and injectivity of the differential, with no injectivity of the
map itself. Thus immersed surfaces, including self-intersections, are allowed.

The smoothness argument adapts the pullback construction in
`DifferentialGeometry.Geometry.Metric.PullbackCross` from diffeomorphisms to
immersions. Boundedness follows from finite-dimensional positive definiteness.
Upstream: qinz1yang/differential-geometry, Apache-2.0, v0.1.2,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Reference: Lee, Introduction to Riemannian Manifolds, second edition, Chapter 8.
-/

noncomputable section

open Bundle

open scoped Manifold ContDiff

namespace OpenGA.Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]

/-- Pull back the ambient inner product along the differential of a map. -/
def inducedInner (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (x : N) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
    ((g.inner (f x)).comp (mfderiv I J f x))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
@[simp] theorem inducedInner_apply
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (x : N) (v w : TangentSpace I x) :
    inducedInner (I := I) g f x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
theorem inducedInner_pos
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : N) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < inducedInner (I := I) g f x v v := by
  apply g.pos
  intro h
  exact hv (hinj x (by simpa using h))

theorem inducedInner_contMDiff [T2Space N]
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hf : ContMDiff I J ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (inducedInner (I := I) g f x)) := by
  apply DifferentialGeometry.cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : N => TangentSpace I x →L[ℝ] ℝ)
  intro Y
  apply DifferentialGeometry.cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : N => ℝ)
  intro W
  have htf : ContMDiff I.tangent J.tangent ∞ (tangentMap I J f) :=
    hf.contMDiff_tangentMap (le_refl _)
  have hv := htf.comp Y.contMDiff
  have hw := htf.comp W.contMDiff
  have hg := g.contMDiff.comp hf
  have htotal := ContMDiff.clm_bundle_apply₂
    (E₁ := fun b : M => TangentSpace J b)
    (E₂ := fun b : M => TangentSpace J b)
    (E₃ := fun _ : M => ℝ)
    (b := f) (ψ := fun x => g.inner (f x))
    (v := fun x => mfderiv I J f x (Y x))
    (w := fun x => mfderiv I J f x (W x)) hg hv hw
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner (f x) (mfderiv I J f x (Y x)) (mfderiv I J f x (W x))) := by
    intro x
    have hx := htotal x
    rw [contMDiffAt_totalSpace] at hx
    simpa using hx.2
  intro x
  rw [contMDiffAt_section]
  exact hscalar x

/-- The smooth metric induced by a smooth map with injective differential. -/
def inducedMetric [T2Space N]
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    DifferentialGeometry.SmoothRiemannianMetric I N where
  inner := inducedInner (I := I) g f
  symm x v w := g.symm (f x) (mfderiv I J f x v) (mfderiv I J f x w)
  pos := inducedInner_pos g f hinj
  isVonNBounded x := DifferentialGeometry.Geometry.posDef_isVonNBounded (E := E)
    (inducedInner (I := I) g f x) (inducedInner_pos g f hinj x)
  contMDiff := inducedInner_contMDiff g f hf

@[simp] theorem inducedMetric_inner [T2Space N]
    (g : DifferentialGeometry.SmoothRiemannianMetric J M) (f : N → M)
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (x : N) (v w : TangentSpace I x) :
    (inducedMetric g f hf hinj).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

end OpenGA.Surface

end

end
