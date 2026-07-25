import DifferentialGeometry.Analysis.Elliptic.Regularity.H1Compl.Intrinsic
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Geometry.Metric.MetricBounds


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace H1Intrinsic

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

def dirichletForm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) : ℝ :=
  ∫ x : M,
    g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
      ((gradL2 (I := I) (M := M) g v : M → E) x)
    ∂(riemannianVolumeMeasure I M g)

theorem dirichletForm_symm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u v =
      dirichletForm (I := I) (M := M) g v u := by
  unfold dirichletForm
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact g.symm x _ _

theorem dirichletForm_self_nonneg (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    0 ≤ dirichletForm (I := I) (M := M) g u u := by
  unfold dirichletForm
  apply integral_nonneg
  intro x
  change (0 : ℝ) ≤
    g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
      ((gradL2 (I := I) (M := M) g u : M → E) x)
  rcases eq_or_ne ((gradL2 (I := I) (M := M) g u : M → E) x) 0 with h0 | h0
  · have h_zero : g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
        ((gradL2 (I := I) (M := M) g u : M → E) x) = 0 := by
      rw [h0]
      change g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0
      rw [map_zero]
    linarith [h_zero]
  · exact (g.pos x _ h0).le

theorem dirichletForm_zero_left (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g 0 u = 0 := by
  unfold dirichletForm
  have h0 : (gradL2 (I := I) (M := M) g (0 : H1Intrinsic (I := I) (M := M) g) :
      Lp E 2 (riemannianVolumeMeasure I M g)) = 0 := by
    rw [(gradL2 (I := I) (M := M) g).map_zero]
  have h_ae : (fun x : M =>
        g.inner x ((gradL2 g (0 : H1Intrinsic g) : M → E) x)
          ((gradL2 g u : M → E) x)) =ᵐ[riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := by
    have hzero_fn : (fun x : M => ((gradL2 g (0 : H1Intrinsic g) :
          Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      rw [h0]
      filter_upwards [Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))] with x hx
      exact hx
    filter_upwards [hzero_fn] with x hx
    rw [hx]
    rw [show (0 : E) = (0 : TangentSpace I x) from rfl,
      map_zero, ContinuousLinearMap.zero_apply]
  rw [integral_congr_ae h_ae]
  simp

theorem dirichletForm_zero_right (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u 0 = 0 := by
  rw [dirichletForm_symm (I := I) (M := M) g u 0]
  exact dirichletForm_zero_left (I := I) (M := M) g u

def shiftedForm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) : ℝ :=
  dirichletForm (I := I) (M := M) g u v +
    ∫ x : M, ((toLp (I := I) (M := M) g u : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
    ∂(riemannianVolumeMeasure I M g)

theorem shiftedForm_symm (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u v =
      shiftedForm (I := I) (M := M) g v u := by
  unfold shiftedForm
  rw [dirichletForm_symm (I := I) (M := M) g u v]
  congr 1
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => mul_comm _ _)

theorem shiftedForm_self_nonneg (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    0 ≤ shiftedForm (I := I) (M := M) g u u := by
  unfold shiftedForm
  refine add_nonneg (dirichletForm_self_nonneg (I := I) (M := M) g u) ?_
  apply integral_nonneg
  intro x
  exact mul_self_nonneg _

theorem shiftedForm_zero_left (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g 0 u = 0 := by
  unfold shiftedForm
  rw [dirichletForm_zero_left (I := I) (M := M) g u]
  rw [zero_add]
  have hzero : (toLp (I := I) (M := M) g (0 : H1Intrinsic (I := I) (M := M) g) :
      Lp ℝ 2 (riemannianVolumeMeasure I M g)) = 0 := by
    rw [(toLp (I := I) (M := M) g).map_zero]
  have h_ae : (fun x : M => ((toLp g (0 : H1Intrinsic g) : M → ℝ) x) *
      ((toLp g u : M → ℝ) x)) =ᵐ[riemannianVolumeMeasure I M g]
      (fun _ : M => (0 : ℝ)) := by
    have hzero_fn : (fun x : M => ((toLp g (0 : H1Intrinsic g) :
          Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : ℝ)) := by
      rw [hzero]
      filter_upwards [Lp.coeFn_zero (E := ℝ) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))] with x hx
      exact hx
    filter_upwards [hzero_fn] with x hx
    rw [hx, zero_mul]
  rw [integral_congr_ae h_ae]
  simp

theorem shiftedForm_zero_right (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u 0 = 0 := by
  rw [shiftedForm_symm (I := I) (M := M) g u 0]
  exact shiftedForm_zero_left (I := I) (M := M) g u

private lemma dirichletForm_integrand_add_left
    (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g u₁ : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) +
        g.inner x ((gradL2 (I := I) (M := M) g u₂ : M → E) x)
          ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  have hgrad_add : (gradL2 (I := I) (M := M) g (u₁ + u₂) :
        Lp E 2 (riemannianVolumeMeasure I M g)) =
      gradL2 (I := I) (M := M) g u₁ + gradL2 (I := I) (M := M) g u₂ :=
    map_add (gradL2 (I := I) (M := M) g) u₁ u₂
  have hfn_add : (fun x : M => ((gradL2 (I := I) (M := M) g (u₁ + u₂) :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => ((gradL2 (I := I) (M := M) g u₁ :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x +
        ((gradL2 (I := I) (M := M) g u₂ :
          Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_add]
    filter_upwards [Lp.coeFn_add (gradL2 (I := I) (M := M) g u₁)
      (gradL2 (I := I) (M := M) g u₂)] with x hx
    exact hx
  filter_upwards [hfn_add] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (u₁ + u₂) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  calc g.inner x ((gradL2 g (u₁ + u₂) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x ((gradL2 g u₁ : M → E) x + (gradL2 g u₂ : M → E) x)
          ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (g.inner x ((gradL2 g u₁ : M → E) x) + g.inner x ((gradL2 g u₂ : M → E) x))
          ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_add (g.inner x) _ _
    _ = g.inner x ((gradL2 g u₁ : M → E) x) ((gradL2 g v : M → E) x) +
          g.inner x ((gradL2 g u₂ : M → E) x) ((gradL2 g v : M → E) x) := by
          rw [ContinuousLinearMap.add_apply]

private lemma dirichletForm_integrand_smul_left
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    (fun x : M => g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x))
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c * g.inner x ((gradL2 (I := I) (M := M) g u : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x)) := by
  have hgrad_smul : (gradL2 (I := I) (M := M) g (c • u) :
        Lp E 2 (riemannianVolumeMeasure I M g)) =
      c • gradL2 (I := I) (M := M) g u :=
    map_smul (gradL2 (I := I) (M := M) g) c u
  have hfn_smul : (fun x : M => ((gradL2 (I := I) (M := M) g (c • u) :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c • ((gradL2 (I := I) (M := M) g u :
        Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x) := by
    rw [hgrad_smul]
    filter_upwards [Lp.coeFn_smul c (gradL2 (I := I) (M := M) g u)] with x hx
    exact hx
  filter_upwards [hfn_smul] with x hx
  show g.inner x ((gradL2 (I := I) (M := M) g (c • u) : M → E) x)
        ((gradL2 (I := I) (M := M) g v : M → E) x) = _
  calc g.inner x ((gradL2 g (c • u) : M → E) x) ((gradL2 g v : M → E) x)
      = g.inner x (c • (gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by rw [hx]
    _ = (c • g.inner x ((gradL2 g u : M → E) x)) ((gradL2 g v : M → E) x) := by
          congr 1
          exact map_smul (g.inner x) c _
    _ = c * g.inner x ((gradL2 g u : M → E) x) ((gradL2 g v : M → E) x) := by
          rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem dirichletForm_add_left (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g (u₁ + u₂) v =
      dirichletForm (I := I) (M := M) g u₁ v +
        dirichletForm (I := I) (M := M) g u₂ v := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  unfold dirichletForm
  rw [integral_congr_ae (dirichletForm_integrand_add_left
    (I := I) (M := M) g u₁ u₂ v)]
  rw [integral_add ?_ ?_]
  · have hL2_u₁ := (u₁.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    have hL2_v := (v.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    refine MeasureTheory.Integrable.mono' (g := fun x =>
      Real.sqrt (g.inner x ((gradL2 g u₁ : M → E) x) ((gradL2 g u₁ : M → E) x)) *
        Real.sqrt (g.inner x ((gradL2 g v : M → E) x) ((gradL2 g v : M → E) x)))
      ?_ ?_ ?_
    · exact MemLp.integrable_mul hL2_u₁ hL2_v
    · have hpair_u₁ := (u₁.2 : IsH1Pair (I := I) (M := M) g _ _).2.2
      exact hpair_u₁ _ (Lp.aestronglyMeasurable (gradL2 g v))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M)
        g x ((gradL2 g u₁ : M → E) x) ((gradL2 g v : M → E) x)
      rwa [show ‖_‖ = |_| from Real.norm_eq_abs _]
  · have hL2_u₂ := (u₂.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    have hL2_v := (v.2 : IsH1Pair (I := I) (M := M) g _ _).2.1
    refine MeasureTheory.Integrable.mono' (g := fun x =>
      Real.sqrt (g.inner x ((gradL2 g u₂ : M → E) x) ((gradL2 g u₂ : M → E) x)) *
        Real.sqrt (g.inner x ((gradL2 g v : M → E) x) ((gradL2 g v : M → E) x)))
      ?_ ?_ ?_
    · exact MemLp.integrable_mul hL2_u₂ hL2_v
    · have hpair_u₂ := (u₂.2 : IsH1Pair (I := I) (M := M) g _ _).2.2
      exact hpair_u₂ _ (Lp.aestronglyMeasurable (gradL2 g v))
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M)
        g x ((gradL2 g u₂ : M → E) x) ((gradL2 g v : M → E) x)
      rwa [show ‖_‖ = |_| from Real.norm_eq_abs _]

theorem dirichletForm_smul_left (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g (c • u) v =
      c * dirichletForm (I := I) (M := M) g u v := by
  unfold dirichletForm
  rw [integral_congr_ae (dirichletForm_integrand_smul_left
    (I := I) (M := M) g c u v)]
  rw [integral_const_mul]

theorem dirichletForm_add_right (g : SmoothRiemannianMetric I M)
    (u v₁ v₂ : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u (v₁ + v₂) =
      dirichletForm (I := I) (M := M) g u v₁ +
        dirichletForm (I := I) (M := M) g u v₂ := by
  rw [dirichletForm_symm (I := I) (M := M) g u (v₁ + v₂),
    dirichletForm_add_left (I := I) (M := M) g v₁ v₂ u]
  rw [dirichletForm_symm (I := I) (M := M) g v₁ u,
    dirichletForm_symm (I := I) (M := M) g v₂ u]

theorem dirichletForm_smul_right (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletForm (I := I) (M := M) g u (c • v) =
      c * dirichletForm (I := I) (M := M) g u v := by
  rw [dirichletForm_symm (I := I) (M := M) g u (c • v),
    dirichletForm_smul_left (I := I) (M := M) g c v u,
    dirichletForm_symm (I := I) (M := M) g v u]

def dirichletFormLM (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ]
      H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => dirichletForm (I := I) (M := M) g u v
      map_add' := fun v₁ v₂ => dirichletForm_add_right (I := I) (M := M) g u v₁ v₂
      map_smul' := fun c v => by
        change dirichletForm (I := I) (M := M) g u (c • v) = _
        rw [dirichletForm_smul_right (I := I) (M := M) g c u v]
        rfl }
  map_add' u₁ u₂ := by
    ext v
    change dirichletForm (I := I) (M := M) g (u₁ + u₂) v = _
    rw [dirichletForm_add_left (I := I) (M := M) g u₁ u₂ v]
    rfl
  map_smul' c u := by
    ext v
    change dirichletForm (I := I) (M := M) g (c • u) v = _
    rw [dirichletForm_smul_left (I := I) (M := M) g c u v]
    rfl

@[simp] lemma dirichletFormLM_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    dirichletFormLM (I := I) (M := M) g u v =
      dirichletForm (I := I) (M := M) g u v := rfl

theorem shiftedForm_add_left (g : SmoothRiemannianMetric I M)
    (u₁ u₂ v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g (u₁ + u₂) v =
      shiftedForm (I := I) (M := M) g u₁ v +
        shiftedForm (I := I) (M := M) g u₂ v := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  unfold shiftedForm
  rw [dirichletForm_add_left (I := I) (M := M) g u₁ u₂ v]
  have h_to_add : (toLp (I := I) (M := M) g (u₁ + u₂) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) =
      toLp (I := I) (M := M) g u₁ + toLp (I := I) (M := M) g u₂ :=
    map_add (toLp (I := I) (M := M) g) u₁ u₂
  have h_fn_add : (fun x : M => ((toLp (I := I) (M := M) g (u₁ + u₂) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => ((toLp (I := I) (M := M) g u₁ :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x +
        ((toLp (I := I) (M := M) g u₂ :
          Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x) := by
    rw [h_to_add]
    filter_upwards [Lp.coeFn_add (toLp (I := I) (M := M) g u₁)
      (toLp (I := I) (M := M) g u₂)] with x hx
    exact hx
  have h_int_eq : ∫ x : M, ((toLp (I := I) (M := M) g (u₁ + u₂) : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
      ∂(riemannianVolumeMeasure I M g) =
      ∫ x : M, ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) +
      ∫ x : M, ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) := by
    have h_ae : (fun x : M => ((toLp (I := I) (M := M) g (u₁ + u₂) : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
          ((toLp (I := I) (M := M) g v : M → ℝ) x) +
          ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) := by
      filter_upwards [h_fn_add] with x hx
      rw [hx, add_mul]
    rw [integral_congr_ae h_ae]
    refine integral_add ?_ ?_
    · exact (MemLp.integrable_mul (Lp.memLp _) (Lp.memLp _) :
        Integrable (fun x : M => ((toLp (I := I) (M := M) g u₁ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) _)
    · exact (MemLp.integrable_mul (Lp.memLp _) (Lp.memLp _) :
        Integrable (fun x : M => ((toLp (I := I) (M := M) g u₂ : M → ℝ) x) *
            ((toLp (I := I) (M := M) g v : M → ℝ) x)) _)
  rw [h_int_eq]
  ring

theorem shiftedForm_smul_left (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g (c • u) v =
      c * shiftedForm (I := I) (M := M) g u v := by
  unfold shiftedForm
  rw [dirichletForm_smul_left (I := I) (M := M) g c u v]
  have h_to_smul : (toLp (I := I) (M := M) g (c • u) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) =
      c • toLp (I := I) (M := M) g u :=
    map_smul (toLp (I := I) (M := M) g) c u
  have h_fn_smul : (fun x : M => ((toLp (I := I) (M := M) g (c • u) :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
      =ᵐ[riemannianVolumeMeasure I M g]
      (fun x : M => c * ((toLp (I := I) (M := M) g u :
        Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x) := by
    rw [h_to_smul]
    filter_upwards [Lp.coeFn_smul c (toLp (I := I) (M := M) g u)] with x hx
    simpa using hx
  have h_int_eq : ∫ x : M, ((toLp (I := I) (M := M) g (c • u) : M → ℝ) x) *
      ((toLp (I := I) (M := M) g v : M → ℝ) x)
      ∂(riemannianVolumeMeasure I M g) =
      c * ∫ x : M, ((toLp (I := I) (M := M) g u : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x)
        ∂(riemannianVolumeMeasure I M g) := by
    have h_ae : (fun x : M => ((toLp (I := I) (M := M) g (c • u) : M → ℝ) x) *
        ((toLp (I := I) (M := M) g v : M → ℝ) x))
        =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c * (((toLp (I := I) (M := M) g u : M → ℝ) x) *
          ((toLp (I := I) (M := M) g v : M → ℝ) x))) := by
      filter_upwards [h_fn_smul] with x hx
      rw [hx]; ring
    rw [integral_congr_ae h_ae, integral_const_mul]
  rw [h_int_eq]; ring

theorem shiftedForm_add_right (g : SmoothRiemannianMetric I M)
    (u v₁ v₂ : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u (v₁ + v₂) =
      shiftedForm (I := I) (M := M) g u v₁ +
        shiftedForm (I := I) (M := M) g u v₂ := by
  rw [shiftedForm_symm (I := I) (M := M) g u (v₁ + v₂),
    shiftedForm_add_left (I := I) (M := M) g v₁ v₂ u]
  rw [shiftedForm_symm (I := I) (M := M) g v₁ u,
    shiftedForm_symm (I := I) (M := M) g v₂ u]

theorem shiftedForm_smul_right (g : SmoothRiemannianMetric I M) (c : ℝ)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedForm (I := I) (M := M) g u (c • v) =
      c * shiftedForm (I := I) (M := M) g u v := by
  rw [shiftedForm_symm (I := I) (M := M) g u (c • v),
    shiftedForm_smul_left (I := I) (M := M) g c v u,
    shiftedForm_symm (I := I) (M := M) g v u]

def shiftedFormLM (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ]
      H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => shiftedForm (I := I) (M := M) g u v
      map_add' := fun v₁ v₂ => shiftedForm_add_right (I := I) (M := M) g u v₁ v₂
      map_smul' := fun c v => by
        change shiftedForm (I := I) (M := M) g u (c • v) = _
        rw [shiftedForm_smul_right (I := I) (M := M) g c u v]
        rfl }
  map_add' u₁ u₂ := by
    ext v
    change shiftedForm (I := I) (M := M) g (u₁ + u₂) v = _
    rw [shiftedForm_add_left (I := I) (M := M) g u₁ u₂ v]
    rfl
  map_smul' c u := by
    ext v
    change shiftedForm (I := I) (M := M) g (c • u) v = _
    rw [shiftedForm_smul_left (I := I) (M := M) g c u v]
    rfl

@[simp] lemma shiftedFormLM_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Intrinsic (I := I) (M := M) g) :
    shiftedFormLM (I := I) (M := M) g u v =
      shiftedForm (I := I) (M := M) g u v := rfl

end H1Intrinsic

end Laplacian
end Analysis
end DifferentialGeometry

end
