import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAll
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile

set_option autoImplicit false
set_option linter.style.longLine false












































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle
open Filter Topology Asymptotics
open DifferentialGeometry.PDE.RicciFlow










theorem hasDerivWithinAt_lim
    {s : Set Real} (hs : Convex Real s) {t : Real} (ht : t ∈ s)
    (f f' : Nat → Real → Real) (g h : Real → Real)
    (hderiv : ∀ k : Nat, ∀ u ∈ s, HasDerivWithinAt (f k) (f' k u) s u)
    (hfg : ∀ u ∈ s, Filter.Tendsto (fun k => f k u) Filter.atTop (nhds (g u)))
    (hunif : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ u ∈ s, |f' k u - h u| < ε) :
    HasDerivWithinAt g (h t) s t := by
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hc4 : (0 : Real) < c / 4 := by positivity
  obtain ⟨k0, hk0⟩ := hunif (c / 4) hc4


  have hA : ∀ u ∈ s, |f k0 u - g u - (f k0 t - g t)| ≤ 2 * (c / 4) * |u - t| := by
    intro u hu
    have hAm : ∀ m : Nat, k0 ≤ m →
        |f k0 u - f m u - (f k0 t - f m t)| ≤ 2 * (c / 4) * |u - t| := by
      intro m hm
      have hφ : ∀ r ∈ s, HasDerivWithinAt (fun r' => f k0 r' - f m r')
          (f' k0 r - f' m r) s r :=
        fun r hr => (hderiv k0 r hr).sub (hderiv m r hr)
      have hbound : ∀ r ∈ s, ‖f' k0 r - f' m r‖ ≤ 2 * (c / 4) := by
        intro r hr
        have h1 := hk0 k0 le_rfl r hr
        have h2 := hk0 m hm r hr
        rw [Real.norm_eq_abs]
        calc |f' k0 r - f' m r|
            ≤ |f' k0 r - h r| + |h r - f' m r| := abs_sub_le _ _ _
          _ ≤ c / 4 + c / 4 := by
              rw [abs_sub_comm (h r) (f' m r)]
              exact add_le_add h1.le h2.le
          _ = 2 * (c / 4) := by ring
      have hmvt := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hbound ht hu
      simpa [Real.norm_eq_abs] using hmvt
    have hlim : Filter.Tendsto (fun m => |f k0 u - f m u - (f k0 t - f m t)|)
        Filter.atTop (nhds (|f k0 u - g u - (f k0 t - g t)|)) :=
      (((tendsto_const_nhds.sub (hfg u hu)).sub
        (tendsto_const_nhds.sub (hfg t ht)))).abs
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop k0] with m hm
    exact hAm m hm

  have hB := hderiv k0 t ht
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff] at hB
  have hBev := hB hc4
  have hC : |f' k0 t - h t| < c / 4 := hk0 k0 le_rfl t ht
  filter_upwards [hBev, self_mem_nhdsWithin] with u hu_taylor hu_mem
  simp only [Real.norm_eq_abs, smul_eq_mul] at hu_taylor ⊢
  have hAu := hA u hu_mem
  have hdecomp : g u - g t - (u - t) * h t
      = (-(f k0 u - g u - (f k0 t - g t)))
        + (f k0 u - f k0 t - (u - t) * f' k0 t)
        + ((u - t) * (f' k0 t - h t)) := by ring
  have htri : |g u - g t - (u - t) * h t|
      ≤ |f k0 u - g u - (f k0 t - g t)|
        + |f k0 u - f k0 t - (u - t) * f' k0 t|
        + |(u - t) * (f' k0 t - h t)| := by
    rw [hdecomp]
    refine le_trans (abs_add_le _ _) ?_
    have habs2 := abs_add_le (-(f k0 u - g u - (f k0 t - g t)))
      (f k0 u - f k0 t - (u - t) * f' k0 t)
    rw [abs_neg] at habs2
    linarith
  have hCterm : |(u - t) * (f' k0 t - h t)| ≤ |u - t| * (c / 4) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hC.le (abs_nonneg _)
  have habs : (0 : Real) ≤ |u - t| := abs_nonneg _
  calc |g u - g t - (u - t) * h t|
      ≤ 2 * (c / 4) * |u - t| + c / 4 * |u - t| + |u - t| * (c / 4) := by linarith
    _ = c * |u - t| := by ring



variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricInner_tendsto
    [Module.Finite ℝ E]
    (gk : Nat → SmoothRiemannianMetric I M)
    (gLim gRef : SmoothRiemannianMetric I M) (x : M)
    (hconv : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      metricDerivNorm (I := I) 0 (gk k) gLim gRef x < ε)
    (v w : TangentSpace I x) :
    Filter.Tendsto (fun k => (gk k).inner x v w) Filter.atTop
      (nhds (gLim.inner x v w)) := by
  have hmd0 : Filter.Tendsto
      (fun k => metricDerivNorm (I := I) 0 (gk k) gLim gRef x)
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconv ε hε
    refine ⟨k0, fun k hk => ?_⟩
    have hnn : (0 : Real) ≤ metricDerivNorm (I := I) 0 (gk k) gLim gRef x :=
      Real.sqrt_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    exact hk0 k hk
  have hbound : ∀ k : Nat,
      dist ((gk k).inner x v w) (gLim.inner x v w)
        ≤ (Module.finrank Real (TangentSpace I x) : Real)
            * metricDerivNorm (I := I) 0 (gk k) gLim gRef x
            * (gRef.inner x (v + w) (v + w) + gRef.inner x v v
                + gRef.inner x w w) := by
    intro k
    rw [Real.dist_eq]
    exact metricInnerApply_diff_le (I := I) (gk k) gLim gRef x v w
  have hb : Filter.Tendsto (fun k =>
      (Module.finrank Real (TangentSpace I x) : Real)
        * metricDerivNorm (I := I) 0 (gk k) gLim gRef x
        * (gRef.inner x (v + w) (v + w) + gRef.inner x v v
            + gRef.inner x w w)) Filter.atTop (nhds 0) := by
    have hb0 := (hmd0.const_mul
      ((Module.finrank Real (TangentSpace I x) : Real))).mul_const
      (gRef.inner x (v + w) (v + w) + gRef.inner x v v + gRef.inner x w w)
    simpa using hb0
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun k => dist_nonneg) hbound hb











omit [Module.Finite ℝ E] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricLimit_pde
    [Module.Finite ℝ E]
    [NeZero (Module.finrank Real E)]
    {D : Nat → RealTimeInterval}
    (S : (k : Nat) → SolutionOn (I := I) (M := M) (D k))
    (hS : ∀ k, IsSolutionOn (I := I) (S k))
    (β ψ : Real)
    (hreg : ∀ k, Set.Icc β ψ ⊆ (D k).regular)
    (gInf : Real → SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x)
    (hinner : ∀ u ∈ Set.Icc β ψ,
      Filter.Tendsto (fun k => ((S k).family.metric u).inner x v w)
        Filter.atTop (nhds ((gInf u).inner x v w)))
    (hRicConv : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ u ∈ Set.Icc β ψ,
        |ricciTensor (I := I) ((S k).family.metric u) x v w
          - ricciTensor (I := I) (gInf u) x v w| < ε)
    {t : Real} (ht : t ∈ Set.Icc β ψ) :
    HasDerivWithinAt (fun s : Real => (gInf s).inner x v w)
      (-2 * ricciTensor (I := I) (gInf t) x v w) (Set.Icc β ψ) t := by


  have hkder : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ,
      HasDerivWithinAt (fun s : Real => ((S k).family.metric s).inner x v w)
        (-2 * ricciTensor (I := I) ((S k).family.metric u) x v w)
        (Set.Icc β ψ) u := by
    intro k u hu
    have h0 := metric_derivWithin_eq_neg_two_ricci (I := I) (S k) (hS k)
      ⟨u, hreg k hu⟩ x v w
    have h0' : HasDerivWithinAt
        (fun s : Real => ((S k).family.metric s).inner x v w)
        ((-2 : Real) * (S k).ricciAt u x (vec2 v w)) (D k).carrier u := h0
    have hval : (S k).ricciAt u x (vec2 v w)
        = ricciTensor (I := I) ((S k).family.metric u) x v w :=
      metricRicciAt_apply_eq_ricciTensor (I := I) ((S k).family.metric u) x v w
    rw [hval] at h0'
    exact h0'.mono (fun r hr => (D k).regular_subset (hreg k hr))
  refine hasDerivWithinAt_lim (convex_Icc β ψ) ht
    (fun k s => ((S k).family.metric s).inner x v w)
    (fun k u => -2 * ricciTensor (I := I) ((S k).family.metric u) x v w)
    (fun s => (gInf s).inner x v w)
    (fun u => -2 * ricciTensor (I := I) (gInf u) x v w)
    hkder hinner ?_
  intro ε hε
  obtain ⟨k0, hk0⟩ := hRicConv (ε / 2) (by positivity)
  refine ⟨k0, fun k hk u hu => ?_⟩
  have h1 := hk0 k hk u hu
  have hfactor : -2 * ricciTensor (I := I) ((S k).family.metric u) x v w
      - -2 * ricciTensor (I := I) (gInf u) x v w
      = -2 * (ricciTensor (I := I) ((S k).family.metric u) x v w
          - ricciTensor (I := I) (gInf u) x v w) := by ring
  rw [hfactor, abs_mul, show |(-2 : Real)| = 2 by norm_num]
  linarith








omit [Module.Finite ℝ E] in
omit [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem metricLimit_pdeOn
    [Module.Finite ℝ E]
    [NeZero (Module.finrank Real E)]
    {D : Nat → RealTimeInterval}
    (S : (k : Nat) → SolutionOn (I := I) (M := M) (D k))
    (hS : ∀ k, IsSolutionOn (I := I) (S k))
    (β ψ : Real)
    (hreg : ∀ k, Set.Icc β ψ ⊆ (D k).regular)
    (gInf : Real → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (K : Set M)
    (hconv : ∀ p : Nat, ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ p → ∀ z ∈ K,
        metricDerivNorm (I := I) a ((S k).family.metric u) (gInf u) gRef z < ε)
    (x : M) (hx : x ∈ K) (v w : TangentSpace I x)
    (hRicConv : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ u ∈ Set.Icc β ψ,
        |ricciTensor (I := I) ((S k).family.metric u) x v w
          - ricciTensor (I := I) (gInf u) x v w| < ε)
    {t : Real} (ht : t ∈ Set.Icc β ψ) :
    HasDerivWithinAt (fun s : Real => (gInf s).inner x v w)
      (-2 * ricciTensor (I := I) (gInf t) x v w) (Set.Icc β ψ) t := by
  refine metricLimit_pde S hS β ψ hreg gInf x v w ?_ hRicConv ht
  intro u hu
  refine metricInner_tendsto (fun k => (S k).family.metric u) (gInf u) gRef x
    ?_ v w
  intro ε hε
  obtain ⟨k0, hk0⟩ := hconv 0 ε hε
  exact ⟨k0, fun k hk => hk0 k hk u hu 0 le_rfl x hx⟩

end HCGCompactness
end DifferentialGeometry
