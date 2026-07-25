import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDense
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Manifold.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.Measure.Family
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EquivalenceFull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Intrinsic
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

private lemma gradFun_eq_zero_off_tsupport_smooth
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ tsupport f) :
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g f x =
      (0 : TangentSpace I x) := by
  apply DifferentialGeometry.Integral.DivergenceTheorem.gradFun_eq_zero_of_mfderiv_eq_zero
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hx_mem : x ∈ (tsupport f)ᶜ := hx
  have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x := hopen.mem_nhds hx_mem
  have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_nhds] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hmfd : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x :=
    Filter.EventuallyEq.mfderiv_eq heqz
  rw [hmfd]
  exact mfderiv_const

noncomputable def gNormGrad
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (u : M → ℝ) (x : M) : ℝ :=
  Real.sqrt
    (g.inner x
      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x)
      (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g u x))

lemma gNormGrad_nonneg
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (u : M → ℝ) (x : M) :
    0 ≤ gNormGrad (I := I) (M := M) g u x :=
  Real.sqrt_nonneg _

lemma gNormGrad_eq_zero_of_notMem_tsupport
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ tsupport f) :
    gNormGrad (I := I) (M := M) g f x = 0 := by
  unfold gNormGrad
  rw [gradFun_eq_zero_off_tsupport_smooth (I := I) (M := M) g hf hx]
  simp

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma mdifferentiableAt_finset_sum
    {ι : Type*} (S : Finset ι) (h : ι → M → ℝ)
    (hh : ∀ α ∈ S, ∀ x : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => ∑ α ∈ S, h α y) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mdifferentiableAt_const
  | insert β B hβB ihB =>
    have hh_β : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h β) x :=
      fun x => hh β (Finset.mem_insert_self β B) x
    have hh_rest : ∀ α ∈ B, ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x :=
      fun α hα x => hh α (Finset.mem_insert_of_mem hα) x
    have h_eq : (fun y : M => ∑ α ∈ insert β B, h α y) =
        (fun y : M => h β y + ∑ α ∈ B, h α y) := by
      funext y
      rw [Finset.sum_insert hβB]
    rw [h_eq]
    exact (hh_β x).add (ihB hh_rest)

private lemma gradFun_finset_sum
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {ι : Type*} (S : Finset ι) (h : ι → M → ℝ)
    (hh : ∀ α ∈ S, ∀ x : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
        (fun y => ∑ α ∈ S, h α y) x =
      ∑ α ∈ S, DifferentialGeometry.Integral.DivergenceTheorem.gradFun
        (I := I) g (h α) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [DifferentialGeometry.Integral.DivergenceTheorem.gradFun_const
      (I := I) g 0 x]
  | insert α₀ S₀ hα₀_notMem ih =>
    have hh_α₀ : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α₀) x :=
      hh α₀ (Finset.mem_insert_self α₀ S₀)
    have hh_rest : ∀ α ∈ S₀, ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x :=
      fun α hα x => hh α (Finset.mem_insert_of_mem hα) x
    have hsum_diff : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ∑ α ∈ S₀, h α y) x :=
      fun x => mdifferentiableAt_finset_sum (I := I) (M := M) S₀ h hh_rest x
    have h_eq_sum : (fun y : M => ∑ α ∈ insert α₀ S₀, h α y) =
        h α₀ + (fun y : M => ∑ α ∈ S₀, h α y) := by
      funext y
      simp [Finset.sum_insert hα₀_notMem]
    rw [h_eq_sum]
    rw [DifferentialGeometry.Integral.DivergenceTheorem.gradFun_add
      (I := I) g (hh_α₀ x) (hsum_diff x)]
    rw [ih hh_rest]
    rw [Finset.sum_insert hα₀_notMem]

private lemma gradFun_eq_sum_gradFun_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x =
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
          (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) y * u y) x := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  set h : M → M → ℝ := fun α y =>
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y with hh_def
  have hh_smooth : ∀ α ∈ S, ContMDiff I 𝓘(ℝ, ℝ) ∞ (h α) := fun α _ =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu
  have hh_diff : ∀ α ∈ S, ∀ x : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x :=
    fun α hα x => (hh_smooth α hα).mdifferentiable (by simp) x
  have hu_eq_local : u =ᶠ[𝓝 x] (fun y => ∑ α ∈ S, h α y) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    change u y = ∑ α ∈ S, h α y
    have h_sum : (∑ α ∈ S, h α y) = (∑ α ∈ S,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) * u y := by
      rw [Finset.sum_mul]
    rw [h_sum]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I) (M := M) y, one_mul]
  have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) u x =
      mfderiv I 𝓘(ℝ, ℝ) (fun y => ∑ α ∈ S, h α y) x :=
    Filter.EventuallyEq.mfderiv_eq hu_eq_local
  have h_gradFun_eq : DifferentialGeometry.Integral.DivergenceTheorem.gradFun
      (I := I) g u x =
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
        (fun y => ∑ α ∈ S, h α y) x := by
    unfold DifferentialGeometry.Integral.DivergenceTheorem.gradFun
    unfold DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
    rw [h_mfderiv_eq]
  rw [h_gradFun_eq]
  exact gradFun_finset_sum (I := I) (M := M) g S h hh_diff x

lemma gNormGrad_le_finset_sum_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    gNormGrad (I := I) (M := M) g u x ≤
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        gNormGrad (I := I) (M := M) g
          (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) y * u y) x := by
  classical
  unfold gNormGrad
  rw [gradFun_eq_sum_gradFun_pou_mul (I := I) (M := M) g hu x]
  set v : M → TangentSpace I x := fun α =>
    DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
      (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) y * u y) x with hv_def
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hg_ip : ∀ v : TangentSpace I x, 0 ≤ g.inner x v v := by
    intro v
    by_cases hv : v = 0
    · rw [hv]
      simp [(g.inner x).map_zero]
    · exact (g.pos x v hv).le
  have h_triangle : ∀ S' : Finset M, ∀ w : M → TangentSpace I x,
      Real.sqrt (g.inner x (∑ α ∈ S', w α) (∑ α ∈ S', w α)) ≤
        ∑ α ∈ S', Real.sqrt (g.inner x (w α) (w α)) := by
    intro S' w
    classical
    induction S' using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      rw [show g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 from by
        have h := (g.inner x).map_zero
        simp [h]]
      rw [Real.sqrt_zero]
    | insert α₀ S₀ hα₀_notMem ih =>
      rw [Finset.sum_insert hα₀_notMem, Finset.sum_insert hα₀_notMem]
      set a : TangentSpace I x := w α₀
      set b : TangentSpace I x := ∑ α ∈ S₀, w α
      have hsym : g.inner x a b = g.inner x b a := g.symm x a b
      have h_innerab_sq : (g.inner x a b)^2 ≤
          g.inner x a a * g.inner x b b := by
        have h_expand : ∀ t : ℝ, g.inner x (a + t • b) (a + t • b) =
            g.inner x a a + 2 * t * g.inner x a b + t^2 * g.inner x b b := by
          intro t
          have h1 : g.inner x (a + t • b) (a + t • b) =
              g.inner x a (a + t • b) + g.inner x (t • b) (a + t • b) := by
            have := (g.inner x).map_add a (t • b)
            have h_apply : ((g.inner x).map_add a (t • b)).symm = ((g.inner x).map_add a (t • b)).symm := rfl
            rw [show ((g.inner x) (a + t • b)) =
                ((g.inner x) a) + ((g.inner x) (t • b)) from
              (g.inner x).map_add a (t • b)]
            simp [ContinuousLinearMap.add_apply]
          have h2 : g.inner x a (a + t • b) =
              g.inner x a a + t * g.inner x a b := by
            have h_dist : (g.inner x a) (a + t • b) =
                (g.inner x a) a + (g.inner x a) (t • b) :=
              (g.inner x a).map_add a (t • b)
            have h_smul : (g.inner x a) (t • b) = t * (g.inner x a) b := by
              rw [(g.inner x a).map_smul, smul_eq_mul]
            rw [h_dist, h_smul]
          have h3 : g.inner x (t • b) (a + t • b) =
              t * g.inner x b a + t^2 * g.inner x b b := by
            have h_smul1 : (g.inner x) (t • b) = t • ((g.inner x) b) :=
              (g.inner x).map_smul t b
            rw [h_smul1]
            change t * (g.inner x b) (a + t • b) =
              t * g.inner x b a + t^2 * g.inner x b b
            rw [(g.inner x b).map_add]
            rw [(g.inner x b).map_smul]
            simp [smul_eq_mul]
            ring
          rw [h1, h2, h3]
          rw [hsym]
          ring
        have h_polynom : ∀ t : ℝ, 0 ≤
            g.inner x a a + 2 * t * g.inner x a b + t^2 * g.inner x b b := fun t => by
          rw [← h_expand t]; exact hg_ip _
        have h_innerbb_nn : 0 ≤ g.inner x b b := hg_ip b
        have h_inneraa_nn : 0 ≤ g.inner x a a := hg_ip a
        by_cases h_bb_zero : g.inner x b b = 0
        · have h_zero : g.inner x a b = 0 := by
            by_contra h_ne
            set t₀ : ℝ := -(g.inner x a a + 1) / (2 * g.inner x a b)
            have h_poly_t₀ := h_polynom t₀
            rw [h_bb_zero] at h_poly_t₀
            have h_simp : g.inner x a a + 2 * t₀ * g.inner x a b + t₀^2 * 0 =
                g.inner x a a + 2 * t₀ * g.inner x a b := by ring
            rw [h_simp] at h_poly_t₀
            have h_2ne : 2 * g.inner x a b ≠ 0 := by
              intro h2
              have : g.inner x a b = 0 := by linarith
              exact h_ne this
            have h_eval : 2 * t₀ * g.inner x a b = -(g.inner x a a + 1) := by
              change 2 * (-(g.inner x a a + 1) / (2 * g.inner x a b)) * g.inner x a b =
                -(g.inner x a a + 1)
              field_simp
            linarith
          rw [h_zero]
          have hbb_nn : 0 ≤ g.inner x a a * g.inner x b b :=
            mul_nonneg h_inneraa_nn h_innerbb_nn
          linarith [sq_nonneg (g.inner x a b), h_zero]
        · have h_bb_pos : 0 < g.inner x b b :=
            lt_of_le_of_ne h_innerbb_nn (Ne.symm h_bb_zero)
          set t₀ : ℝ := -g.inner x a b / g.inner x b b
          have h_poly_t₀ := h_polynom t₀
          have h_eval : g.inner x a a + 2 * t₀ * g.inner x a b + t₀^2 * g.inner x b b =
              g.inner x a a - (g.inner x a b)^2 / g.inner x b b := by
            change g.inner x a a + 2 * (-g.inner x a b / g.inner x b b) * g.inner x a b +
                (-g.inner x a b / g.inner x b b)^2 * g.inner x b b =
              g.inner x a a - (g.inner x a b)^2 / g.inner x b b
            field_simp
            ring
          rw [h_eval] at h_poly_t₀
          have h_step : (g.inner x a b)^2 / g.inner x b b ≤ g.inner x a a := by linarith
          rw [div_le_iff₀ h_bb_pos] at h_step
          linarith
      have h_a_nn : 0 ≤ g.inner x a a := hg_ip a
      have h_b_nn : 0 ≤ g.inner x b b := hg_ip b
      have h_sqrt_ab_le : Real.sqrt ((g.inner x a b)^2) ≤
          Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
        rw [show Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) =
            Real.sqrt (g.inner x a a * g.inner x b b) from
          (Real.sqrt_mul h_a_nn _).symm]
        exact Real.sqrt_le_sqrt h_innerab_sq
      have h_abs_ab : |g.inner x a b| = Real.sqrt ((g.inner x a b)^2) := by
        rw [Real.sqrt_sq_eq_abs]
      have h_inner_ab_le : g.inner x a b ≤
          Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) :=
        le_trans (le_abs_self _) (h_abs_ab ▸ h_sqrt_ab_le)
      have h_apb_eq : g.inner x (a + b) (a + b) =
          g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
        have h_step : g.inner x (a + b) (a + b) =
            g.inner x a (a + b) + g.inner x b (a + b) := by
          have h1 : (g.inner x) (a + b) = (g.inner x) a + (g.inner x) b :=
            (g.inner x).map_add a b
          calc (g.inner x (a + b)) (a + b)
              = ((g.inner x) a + (g.inner x) b) (a + b) := by rw [h1]
            _ = (g.inner x) a (a + b) + (g.inner x) b (a + b) := rfl
        rw [h_step]
        rw [(g.inner x a).map_add, (g.inner x b).map_add]
        rw [hsym]
        ring
      have h_apb_nn : 0 ≤ g.inner x (a + b) (a + b) := hg_ip (a + b)
      have h_rhs_sq_nn : (0 : ℝ) ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have h_target : g.inner x (a + b) (a + b) ≤
          (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b))^2 := by
        rw [h_apb_eq]
        have h_sqrt_a : Real.sqrt (g.inner x a a)^2 = g.inner x a a :=
          Real.sq_sqrt h_a_nn
        have h_sqrt_b : Real.sqrt (g.inner x b b)^2 = g.inner x b b :=
          Real.sq_sqrt h_b_nn
        nlinarith [h_inner_ab_le, h_sqrt_a, h_sqrt_b,
          Real.sqrt_nonneg (g.inner x a a), Real.sqrt_nonneg (g.inner x b b)]
      have h_apb_sqrt_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤
          Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
        have h := Real.sqrt_le_sqrt h_target
        rw [Real.sqrt_sq h_rhs_sq_nn] at h
        exact h
      refine h_apb_sqrt_le.trans ?_
      have h_b_le := ih
      have h_a_eq : Real.sqrt (g.inner x a a) =
          Real.sqrt (g.inner x (w α₀) (w α₀)) := by rw [show a = w α₀ from rfl]
      have h_b_eq : Real.sqrt (g.inner x b b) =
          Real.sqrt (g.inner x (∑ α ∈ S₀, w α) (∑ α ∈ S₀, w α)) := by
        rw [show b = ∑ α ∈ S₀, w α from rfl]
      linarith
  exact h_triangle S v

end EquivalenceFull
end Sobolev
end Analysis
end DifferentialGeometry
