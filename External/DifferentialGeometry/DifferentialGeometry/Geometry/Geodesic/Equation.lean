import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Operator.HessianTrace
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.Transform



noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

def chartCoord (i : Fin (Module.finrank ℝ E)) (v : E) : ℝ :=
  (chartModelBasis E).repr v i

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartCoord_def (i : Fin (Module.finrank ℝ E)) (v : E) :
    chartCoord (E := E) i v = (chartModelBasis E).repr v i := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_smul (i : Fin (Module.finrank ℝ E)) (a : ℝ) (v : E) :
    chartCoord (E := E) i (a • v) = a * chartCoord (E := E) i v := by
  simp [chartCoord, map_smul]

omit [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_zero (i : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) i (0 : E) = 0 := by
  simp [chartCoord]

def chartChristoffelContraction (g : SmoothRiemannianMetric I M) (α : M)
    (v w : E) (y : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j w) •
      chartModelBasis E k

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartChristoffelContraction_def
    (g : SmoothRiemannianMetric I M) (α : M) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α v w y =
      ∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i j k y *
              chartCoord (E := E) i v * chartCoord (E := E) j w) •
          chartModelBasis E k := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_symm
    (g : SmoothRiemannianMetric I M) (α : M) (v w : E) (y : E) :
    chartChristoffelContraction (I := I) g α v w y =
      chartChristoffelContraction (I := I) g α w v y := by
  classical
  unfold chartChristoffelContraction
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [chartChristoffel_symm (I := I) g α j i k y]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_zero_left
    (g : SmoothRiemannianMetric I M) (α : M) (w : E) (y : E) :
    chartChristoffelContraction (I := I) g α (0 : E) w y = 0 := by
  classical
  unfold chartChristoffelContraction
  refine Finset.sum_eq_zero ?_
  intro k _
  have : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (0 : E) * chartCoord (E := E) j w) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    simp
  rw [this, zero_smul]

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_smul_smul
    (g : SmoothRiemannianMetric I M) (α : M) (a : ℝ) (v : E) (y : E) :
    chartChristoffelContraction (I := I) g α (a • v) (a • v) y =
      (a * a) • chartChristoffelContraction (I := I) g α v v y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_smul]
  congr 1
  calc ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i (a • v) * chartCoord (E := E) j (a • v)
      = ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          (a * chartCoord (E := E) i v) * (a * chartCoord (E := E) j v) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [chartCoord_smul, chartCoord_smul]
    _ = (a * a) * ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
          chartCoord (E := E) i v * chartCoord (E := E) j v := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_neg
    (g : SmoothRiemannianMetric I M) (α : M) (v : E) (y : E) :
    chartChristoffelContraction (I := I) g α (-v) (-v) y =
      chartChristoffelContraction (I := I) g α v v y := by
  have hneg : (-v : E) = ((-1 : ℝ) • v) := (neg_one_smul ℝ v).symm
  rw [hneg, chartChristoffelContraction_smul_smul (I := I) g α (-1 : ℝ) v y]
  norm_num

def geodesicVectorField (g : SmoothRiemannianMetric I M)
    (p : TangentBundle I M) : TangentSpace I.tangent p :=
  (p.2, - chartChristoffelContraction (I := I) g p.proj p.2 p.2
      (extChartAt I p.proj p.proj))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma geodesicVectorField_def
    (g : SmoothRiemannianMetric I M) (p : TangentBundle I M) :
    geodesicVectorField (I := I) g p =
      (p.2, - chartChristoffelContraction (I := I) g p.proj p.2 p.2
          (extChartAt I p.proj p.proj)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma geodesicVectorField_fst
    (g : SmoothRiemannianMetric I M) (p : TangentBundle I M) :
    (geodesicVectorField (I := I) g p).1 = p.2 := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma geodesicVectorField_snd
    (g : SmoothRiemannianMetric I M) (p : TangentBundle I M) :
    (geodesicVectorField (I := I) g p).2 =
      - chartChristoffelContraction (I := I) g p.proj p.2 p.2
          (extChartAt I p.proj p.proj) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma geodesicVectorField_zero_section
    (g : SmoothRiemannianMetric I M) (α : M) :
    geodesicVectorField (I := I) g (⟨α, (0 : E)⟩ : TangentBundle I M) =
      ((0 : E), (0 : E)) := by
  change (((0 : E), - chartChristoffelContraction (I := I) g α (0 : E) (0 : E) _)
    : E × E) = ((0 : E), (0 : E))
  rw [chartChristoffelContraction_zero_left]
  simp

def chartLocalCurve (γ : ℝ → M) (t : ℝ) : ℝ → E :=
  fun s => extChartAt I (γ t) (γ s)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma chartLocalCurve_def (γ : ℝ → M) (t s : ℝ) :
    chartLocalCurve (I := I) γ t s = extChartAt I (γ t) (γ s) := rfl

def HasGeodesicEquationAt (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (t : ℝ) : Prop :=
  ∃ v a : E,
    HasDerivAt (chartLocalCurve (I := I) γ t) v t ∧
    (∀ᶠ s in nhds t, HasDerivAt (chartLocalCurve (I := I) γ t)
        (deriv (chartLocalCurve (I := I) γ t) s) s) ∧
    HasDerivAt (fun s => deriv (chartLocalCurve (I := I) γ t) s) a t ∧
    a + chartChristoffelContraction (I := I) g (γ t) v v
        (extChartAt I (γ t) (γ t)) = 0

def chartFiberCoord (α : M) (p : TangentBundle I M) : E :=
  (trivializationAt E (TangentSpace I) α p).2

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartFiberCoord_def (α : M) (p : TangentBundle I M) :
    chartFiberCoord (I := I) α p =
      (trivializationAt E (TangentSpace I) α p).2 := rfl

def geodesicVectorFieldChartFiber (g : SmoothRiemannianMetric I M) (α : M)
    (p : TangentBundle I M) : E × E :=
  let v := chartFiberCoord (I := I) α p
  (v, - chartChristoffelContraction (I := I) g α v v
    (extChartAt I α p.proj))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma geodesicVectorFieldChartFiber_def
    (g : SmoothRiemannianMetric I M) (α : M) (p : TangentBundle I M) :
    geodesicVectorFieldChartFiber (I := I) g α p =
      let v := chartFiberCoord (I := I) α p
      (v, - chartChristoffelContraction (I := I) g α v v
        (extChartAt I α p.proj)) := rfl

def geodesicVectorFieldChart (g : SmoothRiemannianMetric I M) (α : M)
    (p : TangentBundle I M) : TangentSpace I.tangent p :=
  (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).symm p
    (geodesicVectorFieldChartFiber (I := I) g α p)

def geodesicChartDomain (α : M) : Set (TangentBundle I M) :=
  (Bundle.TotalSpace.proj : TangentBundle I M → M) ⁻¹' (chartAt H α).source

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma geodesicChartDomain_isOpen (α : M) :
    IsOpen (geodesicChartDomain (I := I) (M := M) α) :=
  (chartAt H α).open_source.preimage (FiberBundle.continuous_proj E (TangentSpace I))

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma mem_geodesicChartDomain_of_proj {α : M} {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source) : p ∈ geodesicChartDomain (I := I) α :=
  hp

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma proj_mem_chartAt_source_of_mem_geodesicChartDomain {α : M}
    {p : TangentBundle I M} (hp : p ∈ geodesicChartDomain (I := I) α) :
    p.proj ∈ (chartAt H α).source := hp

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma geodesicChartDomain_eq_trivBaseSet (α : M) :
    geodesicChartDomain (I := I) α =
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
  classical
  unfold geodesicChartDomain
  ext p
  rw [Set.mem_preimage,
    TangentBundle.trivializationAt_baseSet (I := I.tangent)
      (M := TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
  exact (TangentBundle.mem_chart_source_iff (I := I) (M := M) p
    (⟨α, (0 : E)⟩ : TangentBundle I M)).symm

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chartFiberCoord_self_zero (α : M) :
    chartFiberCoord (I := I) α
      (⟨α, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hα : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' α
  have hzero := (trivializationAt E (TangentSpace I) α).zeroSection ℝ (x := α) hα
  have hzero' : (trivializationAt E (TangentSpace I) α)
      (⟨α, (0 : TangentSpace I α)⟩ : TangentBundle I M) = (α, 0) := hzero
  change (trivializationAt E (TangentSpace I) α
      (⟨α, (0 : TangentSpace I α)⟩ : TangentBundle I M)).2 = 0
  rw [hzero']

omit [NeZero (Module.finrank ℝ E)] in
lemma geodesicVectorFieldChart_zero_section
    (g : SmoothRiemannianMetric I M) (α : M) :
    geodesicVectorFieldChart (I := I) g α
        (⟨α, (0 : E)⟩ : TangentBundle I M) = 0 := by
  classical
  have hcf : chartFiberCoord (I := I) α
      (⟨α, (0 : E)⟩ : TangentBundle I M) = 0 :=
    chartFiberCoord_self_zero (I := I) α
  have hfiber : geodesicVectorFieldChartFiber (I := I) g α
      (⟨α, (0 : E)⟩ : TangentBundle I M) = (0, 0) := by
    change (chartFiberCoord (I := I) α (⟨α, (0 : E)⟩ : TangentBundle I M),
        - chartChristoffelContraction (I := I) g α
            (chartFiberCoord (I := I) α (⟨α, (0 : E)⟩ : TangentBundle I M))
            (chartFiberCoord (I := I) α (⟨α, (0 : E)⟩ : TangentBundle I M))
            (extChartAt I α (⟨α, (0 : E)⟩ : TangentBundle I M).proj)) = (0, 0)
    rw [hcf, chartChristoffelContraction_zero_left, neg_zero]
  unfold geodesicVectorFieldChart
  rw [hfiber]
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hcoe := Bundle.Trivialization.coe_symmₗ (R := ℝ) e
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have : e.symm (⟨α, (0 : E)⟩ : TangentBundle I M) (0 : E × E) = 0 := by
    have h := congrFun hcoe (0 : E × E)
    rw [← h]
    exact map_zero _
  exact this

def IsGeodesicAt (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (t₀ : ℝ) : Prop :=
  ∃ (α : M) (f : ℝ → TangentBundle I M),
    (∀ t, (f t).proj = γ t) ∧
    (f t₀).proj ∈ (chartAt H α).source ∧
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀

def IsGeodesic (g : SmoothRiemannianMetric I M) (γ : ℝ → M) : Prop :=
  ∀ t : ℝ, HasGeodesicEquationAt (I := I) g γ t

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesic.hasGeodesicEquationAt {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (t : ℝ) :
    HasGeodesicEquationAt (I := I) g γ t :=
  hγ t

def IsGeodesicOn (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasGeodesicEquationAt (I := I) g γ t

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOn.hasGeodesicEquationAt {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (ht : t ∈ s) :
    HasGeodesicEquationAt (I := I) g γ t :=
  hγ t ht

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOn.mono {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} {s s' : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : s' ⊆ s) :
    IsGeodesicOn (I := I) g γ s' :=
  fun t ht => hγ t (hs ht)

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesic.isGeodesicOn {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (s : Set ℝ) :
    IsGeodesicOn (I := I) g γ s :=
  fun t _ => hγ t

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesic_const (g : SmoothRiemannianMetric I M) (p : M) :
    IsGeodesic (I := I) g (fun _ : ℝ => p) := by
  classical
  intro t
  have hconst : chartLocalCurve (I := I) (fun _ : ℝ => p) t =
      fun _ : ℝ => extChartAt I p p := by
    funext s; rfl
  refine ⟨(0 : E), (0 : E), ?_, ?_, ?_, ?_⟩
  · rw [hconst]; exact hasDerivAt_const t (extChartAt I p p)
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [hconst]
    have hd : deriv (fun _ : ℝ => extChartAt I p p) s = 0 := deriv_const s _
    rw [hd]; exact hasDerivAt_const s (extChartAt I p p)
  · have hd : (fun s => deriv (chartLocalCurve (I := I) (fun _ : ℝ => p) t) s)
        = fun _ : ℝ => (0 : E) := by
      funext s; rw [hconst]; exact deriv_const s _
    rw [hd]; exact hasDerivAt_const t (0 : E)
  · rw [chartChristoffelContraction_zero_left]
    simp

omit [NeZero (Module.finrank ℝ E)] in
theorem IsGeodesicAt.const (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    IsGeodesicAt (I := I) g (fun _ : ℝ => p) t := by
  classical
  refine ⟨p, fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M), fun _ => rfl,
    mem_chart_source H p, ?_⟩
  refine (isMIntegralCurve_const ?_).isMIntegralCurveAt t
  exact geodesicVectorFieldChart_zero_section (I := I) g p

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesic_comp_add
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (b : ℝ) :
    IsGeodesic (I := I) g (fun s => γ (s + b)) := by
  intro t
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ (t + b)
  have hshift : chartLocalCurve (I := I) (fun s => γ (s + b)) t =
      fun s => chartLocalCurve (I := I) γ (t + b) (s + b) := by
    funext s; rfl
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]
    exact hv.comp_add_const t b
  · rw [hshift]
    have hderiv : ∀ s,
        deriv (fun s => chartLocalCurve (I := I) γ (t + b) (s + b)) s =
          deriv (chartLocalCurve (I := I) γ (t + b)) (s + b) := by
      intro s
      exact deriv_comp_add_const (chartLocalCurve (I := I) γ (t + b)) b s
    have hev' : ∀ᶠ s in nhds t, HasDerivAt
        (chartLocalCurve (I := I) γ (t + b))
        (deriv (chartLocalCurve (I := I) γ (t + b)) (s + b)) (s + b) := by
      have hcont : Filter.Tendsto (fun s : ℝ => s + b) (nhds t) (nhds (t + b)) :=
        (continuous_add_const b).continuousAt
      exact hcont.eventually hev
    filter_upwards [hev'] with s hs
    rw [hderiv s]
    exact hs.comp_add_const s b
  · rw [hshift]
    have hd2 : (fun s => deriv
        (fun s => chartLocalCurve (I := I) γ (t + b) (s + b)) s) =
        fun s => deriv (chartLocalCurve (I := I) γ (t + b)) (s + b) := by
      funext s
      exact deriv_comp_add_const (chartLocalCurve (I := I) γ (t + b)) b s
    rw [hd2]
    exact ha.comp_add_const t b
  · exact hgeo

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma chartLocalCurve_comp_neg (γ : ℝ → M) (τ : ℝ) :
    chartLocalCurve (I := I) (fun s => γ (-s)) τ =
      (fun s => chartLocalCurve (I := I) γ (-τ) (-s)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem hasGeodesicEquationAt_comp_neg
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {τ : ℝ}
    (hγ : HasGeodesicEquationAt (I := I) g γ (-τ)) :
    HasGeodesicEquationAt (I := I) g (fun s => γ (-s)) τ := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ
  set u : ℝ → E := chartLocalCurve (I := I) γ (-τ) with hu_def
  have hrev : chartLocalCurve (I := I) (fun s => γ (-s)) τ = (fun s => u (-s)) :=
    chartLocalCurve_comp_neg (I := I) γ τ
  have hderiv_rev : deriv (chartLocalCurve (I := I) (fun s => γ (-s)) τ) =
      (fun s => -(deriv u (-s))) := by
    rw [hrev]; funext s; exact deriv_comp_neg u s
  refine ⟨-v, a, ?_, ?_, ?_, ?_⟩
  · rw [hrev]
    have hcomp : HasDerivAt (fun s => u (-s)) ((-1 : ℝ) • v) τ := by
      have := (hv.scomp τ (hasDerivAt_neg τ))
      simpa [Function.comp_def] using this
    simpa using hcomp
  · rw [hderiv_rev, hrev]
    have hcont : Filter.Tendsto (fun s : ℝ => -s) (nhds τ) (nhds (-τ)) :=
      (continuous_neg.tendsto τ)
    have hev' : ∀ᶠ s in nhds τ,
        HasDerivAt u (deriv u (-s)) (-s) := hcont.eventually hev
    filter_upwards [hev'] with s hs
    have := hs.scomp s (hasDerivAt_neg s)
    simpa [Function.comp_def] using this
  · rw [hderiv_rev]
    have hinner : HasDerivAt (fun s => deriv u (-s)) ((-1 : ℝ) • a) τ := by
      have := (ha.scomp τ (hasDerivAt_neg τ))
      simpa [Function.comp_def] using this
    have hfin := hinner.neg
    simpa using hfin
  · rw [chartChristoffelContraction_neg (I := I) g _ v]
    exact hgeo

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesic_comp_neg
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) :
    IsGeodesic (I := I) g (fun s => γ (-s)) := by
  intro τ
  exact hasGeodesicEquationAt_comp_neg (I := I) (hγ (-τ))

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_comp_neg
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := I) g (fun t => γ (-t)) (Neg.neg ⁻¹' s) := by
  intro τ hτ
  exact hasGeodesicEquationAt_comp_neg (I := I) (hγ (-τ) hτ)





omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma chartLocalCurve_comp_affine (γ : ℝ → M) (c d t : ℝ) :
    chartLocalCurve (I := I) (fun s => γ (c * s + d)) t =
      (fun s => chartLocalCurve (I := I) γ (c * t + d) (c * s + d)) := rfl








omit [NeZero (Module.finrank ℝ E)] in
theorem hasGeodesicEquationAt_comp_affine
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {c d t : ℝ}
    (hγ : HasGeodesicEquationAt (I := I) g γ (c * t + d)) :
    HasGeodesicEquationAt (I := I) g (fun s => γ (c * s + d)) t := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ
  set u : ℝ → E := chartLocalCurve (I := I) γ (c * t + d) with hu_def
  have haff : ∀ s : ℝ, HasDerivAt (fun x : ℝ => c * x + d) c s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul c).add_const d
  have hshift : chartLocalCurve (I := I) (fun s => γ (c * s + d)) t
      = (fun s => u (c * s + d)) := rfl
  have hcont : Filter.Tendsto (fun s : ℝ => c * s + d) (nhds t) (nhds (c * t + d)) :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt
  have hev_pb : ∀ᶠ s in nhds t, HasDerivAt u (deriv u (c * s + d)) (c * s + d) :=
    hcont.eventually hev
  have hderiv_ev : ∀ᶠ s in nhds t,
      deriv (fun x => u (c * x + d)) s = c • deriv u (c * s + d) := by
    filter_upwards [hev_pb] with s hs
    have hch := hs.scomp s (haff s)
    simpa [Function.comp_def] using hch.deriv
  refine ⟨c • v, (c * c) • a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]
    have := hv.scomp t (haff t)
    simpa [Function.comp_def] using this
  · rw [hshift]
    filter_upwards [hev_pb, hderiv_ev] with s hs hds
    have hch := hs.scomp s (haff s)
    rw [hds]
    simpa [Function.comp_def] using hch
  · rw [hshift]
    have hcongr : (fun s => deriv (fun x => u (c * x + d)) s)
        =ᶠ[nhds t] (fun s => c • deriv u (c * s + d)) := hderiv_ev
    refine HasDerivAt.congr_of_eventuallyEq ?_ hcongr
    have hinner : HasDerivAt (fun s => deriv u (c * s + d)) (c • a) t := by
      have := ha.scomp t (haff t)
      simpa [Function.comp_def] using this
    have hfin := hinner.const_smul c
    rw [smul_smul] at hfin
    exact hfin
  · rw [chartChristoffelContraction_smul_smul (I := I) g _ c v, ← smul_add, hgeo,
      smul_zero]




omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_comp_affine
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ} {c d : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := I) g (fun t => γ (c * t + d)) {t : ℝ | c * t + d ∈ s} := by
  intro t ht
  exact hasGeodesicEquationAt_comp_affine (I := I) (hγ (c * t + d) ht)

section ChartFixedSmoothness

variable [I.Boundaryless]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma trivializationAt_source_eq (α : M) :
    (trivializationAt E (TangentSpace I) α).source =
      geodesicChartDomain (I := I) (M := M) α := by
  rw [Trivialization.source_eq]; rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartFiberCoord_contMDiffOn (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (chartFiberCoord (I := I) (α := α)) (geodesicChartDomain (I := I) α) := by
  classical
  have he : MapsTo (id : TangentBundle I M → TangentBundle I M)
      (geodesicChartDomain (I := I) α)
      (trivializationAt E (TangentSpace I) α).source := by
    rw [trivializationAt_source_eq (I := I) α]
    intro p hp; exact hp
  have hiff :=
    (trivializationAt E (TangentSpace I) α).contMDiffOn_iff
      (IM := I.tangent) (IB := I) (n := (∞ : WithTop ℕ∞))
      (f := id) (s := geodesicChartDomain (I := I) α) he
  have hid : ContMDiffOn I.tangent (I.prod 𝓘(ℝ, E)) ∞
      (id : TangentBundle I M → TangentBundle I M)
      (geodesicChartDomain (I := I) α) := contMDiffOn_id
  exact (hiff.mp hid).2

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma proj_contMDiffOn (s : Set (TangentBundle I M)) :
    ContMDiffOn I.tangent I ∞
      (Bundle.TotalSpace.proj : TangentBundle I M → M) s :=
  (Bundle.contMDiff_proj (TangentSpace I) (n := (∞ : WithTop ℕ∞))).contMDiffOn

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma extChartAt_proj_contMDiffOn (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M => extChartAt I α p.proj)
      (geodesicChartDomain (I := I) α) := by
  classical
  have hproj : ContMDiffOn I.tangent I ∞
      (Bundle.TotalSpace.proj : TangentBundle I M → M)
      (geodesicChartDomain (I := I) α) :=
    proj_contMDiffOn (I := I) (M := M) _
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hsubset : geodesicChartDomain (I := I) α ⊆
      Bundle.TotalSpace.proj ⁻¹' (chartAt H α).source :=
    fun _ hp => hp
  exact hchart.comp hproj hsubset

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffel_extChartAt_proj_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M =>
        chartChristoffel (I := I) g α i j k (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) := by
  classical
  intro p hp
  have hp_src : p.proj ∈ (chartAt H α).source := hp
  have hp_ext_src : p.proj ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hp_src
  have hp_target : extChartAt I α p.proj ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hp_ext_src
  have hp_int : extChartAt I α p.proj ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hp_target
  set Γ : E → ℝ := chartChristoffel (I := I) g α i j k with hΓ_eq
  have hΓ_on : ContDiffOn ℝ ∞ Γ (interior (extChartAt I α).target) :=
    chartChristoffel_contDiffOn_interior (I := I) g α i j k
  have hΓ_at : ContDiffAt ℝ ∞ Γ (extChartAt I α p.proj) :=
    hΓ_on.contDiffAt (isOpen_interior.mem_nhds hp_int)
  have hbase : ContMDiffWithinAt I.tangent 𝓘(ℝ, E) ∞
      (fun q : TangentBundle I M => extChartAt I α q.proj)
      (geodesicChartDomain (I := I) α) p :=
    extChartAt_proj_contMDiffOn (I := I) α p hp
  have := (hΓ_at.contMDiffAt).comp_contMDiffWithinAt p hbase
  exact this

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_scalarCoeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k (extChartAt I α p.proj) *
            chartCoord (E := E) i (chartFiberCoord (I := I) α p) *
            chartCoord (E := E) j (chartFiberCoord (I := I) α p))
      (geodesicChartDomain (I := I) α) := by
  classical
  refine contMDiffOn_finset_sum (fun i _ => ?_)
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  have hΓ : ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M =>
        chartChristoffel (I := I) g α i j k (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) :=
    chartChristoffel_extChartAt_proj_contMDiffOn (I := I) g α i j k
  have hv : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (chartFiberCoord (I := I) (α := α)) (geodesicChartDomain (I := I) α) :=
    chartFiberCoord_contMDiffOn (I := I) α
  have hCLM_i : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (((chartModelBasis E).coord i).toContinuousLinearMap) :=
    (((chartModelBasis E).coord i).toContinuousLinearMap).contMDiff
  have hCLM_j : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (((chartModelBasis E).coord j).toContinuousLinearMap) :=
    (((chartModelBasis E).coord j).toContinuousLinearMap).contMDiff
  have hci : ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M => chartCoord (E := E) i (chartFiberCoord (I := I) α p))
      (geodesicChartDomain (I := I) α) := by
    intro p hp
    exact (hCLM_i.contMDiffAt).comp_contMDiffWithinAt _ (hv p hp)
  have hcj : ContMDiffOn I.tangent 𝓘(ℝ) ∞
      (fun p : TangentBundle I M => chartCoord (E := E) j (chartFiberCoord (I := I) α p))
      (geodesicChartDomain (I := I) α) := by
    intro p hp
    exact (hCLM_j.contMDiffAt).comp_contMDiffWithinAt _ (hv p hp)
  exact (hΓ.mul hci).mul hcj

omit [NeZero (Module.finrank ℝ E)] in
lemma chartChristoffelContraction_chartFiber_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M =>
        chartChristoffelContraction (I := I) g α
          (chartFiberCoord (I := I) α p)
          (chartFiberCoord (I := I) α p)
          (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) := by
  classical
  unfold chartChristoffelContraction
  refine contMDiffOn_finset_sum (fun k _ => ?_)
  have hscalar := chartChristoffelContraction_scalarCoeff_contMDiffOn (I := I) g α k
  have hconst : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun _ : TangentBundle I M => (chartModelBasis E) k)
      (geodesicChartDomain (I := I) α) := contMDiffOn_const
  exact hscalar.smul hconst

omit [NeZero (Module.finrank ℝ E)] in
lemma geodesicVectorFieldChartFiber_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
      (geodesicVectorFieldChartFiber (I := I) g α)
      (geodesicChartDomain (I := I) α) := by
  classical
  have hfst : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (chartFiberCoord (I := I) (α := α)) (geodesicChartDomain (I := I) α) :=
    chartFiberCoord_contMDiffOn (I := I) α
  have hΓ : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M =>
        chartChristoffelContraction (I := I) g α
          (chartFiberCoord (I := I) α p)
          (chartFiberCoord (I := I) α p)
          (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) :=
    chartChristoffelContraction_chartFiber_contMDiffOn (I := I) g α
  have hsnd : ContMDiffOn I.tangent 𝓘(ℝ, E) ∞
      (fun p : TangentBundle I M =>
        - chartChristoffelContraction (I := I) g α
          (chartFiberCoord (I := I) α p)
          (chartFiberCoord (I := I) α p)
          (extChartAt I α p.proj))
      (geodesicChartDomain (I := I) α) := hΓ.neg
  exact hfst.prodMk_space hsnd

private instance trivializationAt_tangent_tangent_isAtlas (α : M) :
    MemTrivializationAtlas
      (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)) :=
  ⟨FiberBundle.trivialization_mem_atlas (E × E) (TangentSpace I.tangent) _⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma trivializationAt_apply_geodesicVectorFieldChart
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M} (hp : p ∈ geodesicChartDomain (I := I) α) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M))
      ⟨p, geodesicVectorFieldChart (I := I) g α p⟩ =
        (p, geodesicVectorFieldChartFiber (I := I) g α p) := by
  classical
  have hp' : p ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [← geodesicChartDomain_eq_trivBaseSet (I := I) α]; exact hp
  exact (trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)).apply_mk_symm hp'
      (geodesicVectorFieldChartFiber (I := I) g α p)

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVectorFieldChart_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (geodesicChartDomain (I := I) α) := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  have hMapsTo : MapsTo
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (geodesicChartDomain (I := I) α) e.source := by
    intro p hp
    rw [Trivialization.source_eq]
    rw [← geodesicChartDomain_eq_trivBaseSet (I := I) α]
    exact hp
  rw [e.contMDiffOn_iff (IM := I.tangent) (IB := I.tangent)
    (n := (∞ : WithTop ℕ∞)) hMapsTo]
  refine ⟨?_, ?_⟩
  · have hid : (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)).proj) =
        (fun p : TangentBundle I M => p) := rfl
    rw [hid]
    exact contMDiffOn_id
  · have heq : ∀ p ∈ geodesicChartDomain (I := I) α,
        (e ⟨p, geodesicVectorFieldChart (I := I) g α p⟩).2 =
          geodesicVectorFieldChartFiber (I := I) g α p := by
      intro p hp
      rw [trivializationAt_apply_geodesicVectorFieldChart (I := I) g α hp]
    have hsmooth : ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
        (geodesicVectorFieldChartFiber (I := I) g α)
        (geodesicChartDomain (I := I) α) :=
      geodesicVectorFieldChartFiber_contMDiffOn (I := I) g α
    exact hsmooth.congr heq

omit [NeZero (Module.finrank ℝ E)] in
theorem geodesicVectorFieldChart_contMDiffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    {p₀ : TangentBundle I M}
    (hp₀ : p₀.proj ∈ (chartAt H α).source) :
    ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      p₀ := by
  have hop : IsOpen (geodesicChartDomain (I := I) α) :=
    geodesicChartDomain_isOpen (I := I) (M := M) α
  have hmem : p₀ ∈ geodesicChartDomain (I := I) α := hp₀
  have hsmooth_on := geodesicVectorFieldChart_contMDiffOn (I := I) g α
  exact (hsmooth_on p₀ hmem).contMDiffAt (hop.mem_nhds hmem)

end ChartFixedSmoothness

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
