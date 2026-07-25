import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic



noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def IsGeodesicOnWithInitial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (s : Set ℝ)
    (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) s

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.isGeodesicAt
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (ht : s ∈ 𝓝 t)
    (ht_src : γ t ∈ (chartAt H p).source) :
    IsGeodesicAt (I := I) g γ t := by
  obtain ⟨f, hproj, _, hf⟩ := hγ
  refine ⟨p, f, hproj, ?_, hf.isMIntegralCurveAt ht⟩
  rw [hproj t]; exact ht_src

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.start_eq
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) :
    γ 0 = p := by
  obtain ⟨f, hproj, hf0, _⟩ := hγ
  have h := hproj 0
  simp [hf0] at h
  exact h.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.mono
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s s' : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (hs : s' ⊆ s) :
    IsGeodesicOnWithInitial (I := I) g γ s' p v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  exact ⟨f, hproj, hf0, hf.mono hs⟩

def MaximalGeodesicWitness
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v

def maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    Set ℝ :=
  {t : ℝ | MaximalGeodesicWitness (I := I) g p v t}

omit [NeZero (Module.finrank ℝ E)] in
lemma mem_maximalGeodesicInterval_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} :
    t ∈ maximalGeodesicInterval (I := I) g p v ↔
      MaximalGeodesicWitness (I := I) g p v t :=
  Iff.rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicInterval_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    IsOpen (maximalGeodesicInterval (I := I) g p v) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨γ, J, hJ, hJ_conn, h0, ht_in, hγ⟩ := ht
  refine Filter.mem_of_superset (hJ.mem_nhds ht_in) ?_
  intro t' ht'
  exact ⟨γ, J, hJ, hJ_conn, h0, ht', hγ⟩

section LocalExistence

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_maximalGeodesicWitness_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    MaximalGeodesicWitness (I := I) g p v 0 := by
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  rw [isMIntegralCurveAt_iff'] at hf
  obtain ⟨ε, hε, hf_on⟩ := hf
  refine ⟨projectCurve (I := I) f, Metric.ball (0 : ℝ) ε,
    Metric.isOpen_ball, ?_, Metric.mem_ball_self hε, Metric.mem_ball_self hε, ?_⟩
  · exact (convex_ball (0 : ℝ) ε).isPreconnected
  exact ⟨f, fun _ => rfl, hf0, hf_on⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem zero_mem_maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (0 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v :=
  exists_maximalGeodesicWitness_zero (I := I) g p v

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicInterval_nonempty
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (maximalGeodesicInterval (I := I) g p v).Nonempty :=
  ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩

end LocalExistence

section MaximalGeodesicDefinition

variable [I.Boundaryless] [CompleteSpace E]

def maximalGeodesicChosenCurve
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ℝ → M :=
  Classical.choose h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesicChosenCurve_spec
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g
        (maximalGeodesicChosenCurve (I := I) g p v h) J p v :=
  Classical.choose_spec h

def maximalGeodesic
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : M :=
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  if h : MaximalGeodesicWitness (I := I) g p v t then
    maximalGeodesicChosenCurve (I := I) g p v h t
  else p

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesic_of_not_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (ht : t ∉ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t = p := by
  unfold maximalGeodesic
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  exact dif_neg ht

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesic_of_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t =
      maximalGeodesicChosenCurve (I := I) g p v h t := by
  unfold maximalGeodesic
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  exact dif_pos h

end MaximalGeodesicDefinition

section MaximalGeodesicValue

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v 0 = p := by
  have h0 := zero_mem_maximalGeodesicInterval (I := I) g p v
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) h0]
  obtain ⟨_J, _hJ, _hJ_conn, _h0J, _h0J', hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v h0
  exact hγ.start_eq

end MaximalGeodesicValue

section MaximalGeodesicAtTime

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem exists_isGeodesicAt_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v)
    (ht_src : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p v →
        γ t ∈ (chartAt H p).source) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, _hJ_conn, h0, ht, hγ⟩ := h
  refine ⟨γ, J, hJ, h0, ht, hγ, ?_⟩
  exact hγ.isGeodesicAt (hJ.mem_nhds ht) (ht_src γ J hγ)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v)
    (ht_src : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p v →
        γ t ∈ (chartAt H p).source) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsGeodesicAt (I := I) g γ 0 ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, h0, ht, hγ_init, hγ_at⟩ :=
    exists_isGeodesicAt_of_mem_maximalGeodesicInterval (I := I) h ht_src
  refine ⟨γ, hγ_init.start_eq, ?_, hγ_at⟩
  refine hγ_init.isGeodesicAt (hJ.mem_nhds h0) ?_
  rw [hγ_init.start_eq]; exact mem_chart_source H p

end MaximalGeodesicAtTime

section MaximalGeodesicMain

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesic_structure_of_footInSource
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hsrc : ∀ t ∈ maximalGeodesicInterval (I := I) g p v,
      ∀ (γ : ℝ → M) (J : Set ℝ),
        IsGeodesicOnWithInitial (I := I) g γ J p v →
          γ t ∈ (chartAt H p).source) :
    let I_max := maximalGeodesicInterval (I := I) g p v
    let γ_max := maximalGeodesic (I := I) g p v
    IsOpen I_max ∧ (0 : ℝ) ∈ I_max ∧ γ_max 0 = p ∧
      (∀ t ∉ I_max, γ_max t = p) ∧
      (∀ t ∈ I_max, ∃ γ : ℝ → M, γ 0 = p ∧
        IsGeodesicAt (I := I) g γ 0 ∧ IsGeodesicAt (I := I) g γ t) := by
  refine ⟨maximalGeodesicInterval_isOpen (I := I) g p v,
    zero_mem_maximalGeodesicInterval (I := I) g p v,
    maximalGeodesic_zero (I := I) g p v, ?_, ?_⟩
  · intro t ht
    exact maximalGeodesic_of_not_mem (I := I) ht
  · intro t ht
    exact exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval (I := I) ht
      (hsrc t ht)

end MaximalGeodesicMain

section BridgeLemmas

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma isGeodesic_iff_isGeodesicOn_univ
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} :
    IsGeodesic (I := I) g γ ↔ IsGeodesicOn (I := I) g γ (Set.univ : Set ℝ) := by
  constructor
  · intro hγ
    exact hγ.isGeodesicOn _
  · intro hγ t
    exact hγ t (Set.mem_univ t)

end BridgeLemmas

section ArcLengthBridge

open MeasureTheory intervalIntegral

variable [I.Boundaryless]
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [T2Space M] [SigmaCompactSpace M]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [T2Space M] [SigmaCompactSpace M] in
private lemma continuousOn_velocityWithin_totalSpace_C1
    {η : ℝ → M} {a b : ℝ} (hab : a < b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b) := by
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := by
    intro x hx
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab) x hx
  have hTan := hη.continuousOn_tangentMapWithin (le_refl 1) hUnique
  have hLift : Continuous (fun t : ℝ =>
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    exact h_homeo.comp (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := by
    intro t ht
    simpa using ht
  have hComp : ContinuousOn
      (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b)
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) :=
    hTan.comp hLift.continuousOn hMaps
  refine hComp.congr ?_
  intro t _ht
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem pathELength_eq_arcLength_riemannianBundle
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Set.Icc a b) MeasureTheory.volume)
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    pathELength I γ a b
      = ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  classical
  set F : ℝ → ℝ := fun t : ℝ => Real.sqrt
      (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) with hF_def
  have hF_nn : ∀ t : ℝ, 0 ≤ F t := fun t => Real.sqrt_nonneg _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  change ∫⁻ t in Set.Icc a b, (fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ) t
    = ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
        (I := I) g γ a b)
  have h_lint_eq :=
    MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
      (f := fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ)
      (g := fun t : ℝ => ENNReal.ofReal (F t))
      (s := Set.Icc a b)
      measurableSet_Icc
      (fun t ht => by simpa [hF_def] using hEnorm t ht)
  rw [h_lint_eq]
  have h_ofReal :
      ENNReal.ofReal (∫ t in Set.Icc a b, F t)
        = ∫⁻ t in Set.Icc a b, ENNReal.ofReal (F t) := by
    have hF_nn_ae : 0 ≤ᵐ[(MeasureTheory.volume).restrict (Set.Icc a b)] F :=
      MeasureTheory.ae_of_all _ hF_nn
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hγ_int hF_nn_ae
  rw [← h_ofReal]
  have h_Icc_Ioc :
      ∫ t in Set.Icc a b, F t = ∫ t in Set.Ioc a b, F t := by
    have h_set : Set.Icc a b = {a} ∪ Set.Ioc a b := by
      ext x
      simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : x = a
        · left; exact h
        · right; exact ⟨lt_of_le_of_ne h1 (fun h' => h h'.symm), h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨le_refl _, hab⟩
        · exact ⟨le_of_lt h1, h2⟩
    rw [h_set]
    have hdisj : Disjoint ({a} : Set ℝ) (Set.Ioc a b) := by
      rw [Set.disjoint_left]
      rintro y hy hy'
      simp only [Set.mem_singleton_iff] at hy
      rw [hy] at hy'
      exact lt_irrefl _ hy'.1
    have h_int_singleton :
        MeasureTheory.IntegrableOn F ({a} : Set ℝ) MeasureTheory.volume := by
      rw [MeasureTheory.integrableOn_singleton_iff]
      exact Or.inr (by simp)
    have h_int_Ioc :
        MeasureTheory.IntegrableOn F (Set.Ioc a b) MeasureTheory.volume :=
      hγ_int.mono_set Set.Ioc_subset_Icc_self
    rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
      h_int_singleton h_int_Ioc]
    have h_singleton : ∫ t in ({a} : Set ℝ), F t = 0 := by
      simp
    rw [h_singleton, zero_add]
  have h_intInterval : ∫ t in a..b, F t = ∫ t in Set.Ioc a b, F t :=
    intervalIntegral.integral_of_le hab
  have h_arcLength :
      DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b
        = ∫ t in a..b, F t := by
    unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
    rfl
  rw [h_arcLength, h_intInterval, ← h_Icc_Ioc]


attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [T2Space M] [SigmaCompactSpace M] in
private lemma continuousOn_g_speedSq_velocityWithin
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ}
    (hVW : ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        g.inner (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
      (Set.Icc a b) := by
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _))
    (b := η)
    (v := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (w := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (s := Set.Icc a b) hVW hVW
  refine h.congr ?_
  intro t _ht
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [T2Space M] [SigmaCompactSpace M] in
lemma speedSqrt_integrableOn_Icc_of_C1
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (η t)
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))))
      (Set.Icc a b) MeasureTheory.volume := by
  classical
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    rw [Set.Icc_self, MeasureTheory.integrableOn_singleton_iff]
    exact Or.inr (by simp)
  · have hVW := continuousOn_velocityWithin_totalSpace_C1 (I := I) (M := M)
      hab_lt hη
    have hSpeedSq := continuousOn_g_speedSq_velocityWithin (I := I) (M := M) g hVW
    have hSqrtW : ContinuousOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) :=
      Real.continuous_sqrt.comp_continuousOn hSpeedSq
    have hIntW : MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) MeasureTheory.volume :=
      hSqrtW.integrableOn_Icc
    have hAgree : ∀ t ∈ Set.Ioo a b,
        Real.sqrt
            (g.inner (η t)
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
          = Real.sqrt
            (g.inner (η t)
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))) := by
      intro t ht
      have hmem : Set.Icc a b ∈ nhds t :=
        Icc_mem_nhds ht.1 ht.2
      rw [mfderivWithin_of_mem_nhds hmem]
    have hae : (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)]
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))) := by
      have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
          t ∈ Set.Ioo a b := by
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hIoo_ae] with t ht
      exact hAgree t ht
    exact hIntW.congr hae

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [T2Space M] [SigmaCompactSpace M] in
theorem pathELength_eq_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Set.Icc a b) MeasureTheory.volume)
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    pathELength I γ a b
      = ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  classical
  set F : ℝ → ℝ := fun t : ℝ => Real.sqrt
      (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) with hF_def
  have hF_nn : ∀ t : ℝ, 0 ≤ F t := fun t => Real.sqrt_nonneg _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  change ∫⁻ t in Set.Icc a b, (fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ) t
    = ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
        (I := I) g γ a b)
  have h_lint_eq :=
    MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
      (f := fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ)
      (g := fun t : ℝ => ENNReal.ofReal (F t))
      (s := Set.Icc a b)
      measurableSet_Icc
      (fun t ht => by simpa [hF_def] using hEnorm t ht)
  rw [h_lint_eq]
  have h_ofReal :
      ENNReal.ofReal (∫ t in Set.Icc a b, F t)
        = ∫⁻ t in Set.Icc a b, ENNReal.ofReal (F t) := by
    have hF_nn_ae : 0 ≤ᵐ[(MeasureTheory.volume).restrict (Set.Icc a b)] F :=
      MeasureTheory.ae_of_all _ hF_nn
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hγ_int hF_nn_ae
  rw [← h_ofReal]
  have h_Icc_Ioc :
      ∫ t in Set.Icc a b, F t = ∫ t in Set.Ioc a b, F t := by
    have h_set : Set.Icc a b = {a} ∪ Set.Ioc a b := by
      ext x
      simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : x = a
        · left; exact h
        · right; exact ⟨lt_of_le_of_ne h1 (fun h' => h h'.symm), h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨le_refl _, hab⟩
        · exact ⟨le_of_lt h1, h2⟩
    rw [h_set]
    have hdisj : Disjoint ({a} : Set ℝ) (Set.Ioc a b) := by
      rw [Set.disjoint_left]
      rintro y hy hy'
      simp only [Set.mem_singleton_iff] at hy
      rw [hy] at hy'
      exact lt_irrefl _ hy'.1
    have h_int_singleton :
        MeasureTheory.IntegrableOn F ({a} : Set ℝ) MeasureTheory.volume := by
      rw [MeasureTheory.integrableOn_singleton_iff]
      exact Or.inr (by simp)
    have h_int_Ioc :
        MeasureTheory.IntegrableOn F (Set.Ioc a b) MeasureTheory.volume :=
      hγ_int.mono_set Set.Ioc_subset_Icc_self
    rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
      h_int_singleton h_int_Ioc]
    have h_singleton : ∫ t in ({a} : Set ℝ), F t = 0 := by
      simp
    rw [h_singleton, zero_add]
  have h_intInterval : ∫ t in a..b, F t = ∫ t in Set.Ioc a b, F t :=
    intervalIntegral.integral_of_le hab
  have h_arcLength :
      DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b
        = ∫ t in a..b, F t := by
    unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
    rfl
  rw [h_arcLength, h_intInterval, ← h_Icc_Ioc]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianEDist_le_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    riemannianEDist I (γ a) (γ b)
      ≤ ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  have hle : riemannianEDist I (γ a) (γ b) ≤ pathELength I γ a b :=
    riemannianEDist_le_pathELength hγ rfl rfl hab
  rwa [pathELength_eq_arcLength_riemannianBundle (I := I) g hab
    (speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hγ) hEnorm] at hle

end ArcLengthBridge

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
