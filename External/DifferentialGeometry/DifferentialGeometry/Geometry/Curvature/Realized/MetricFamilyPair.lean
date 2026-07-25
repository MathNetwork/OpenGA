import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Bundle.LocalFrameRegularity

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry.Integral.Connection

open Bundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

namespace MetricFamilySmoothOn



omit [CompleteSpace E] in
theorem pairSmoothAt
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {t : Real} {x : M} (hDreg : D.regular ∈ 𝓝 t)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        (G.metric q.1).inner q.2 ((V 0) q.2) ((V 1) q.2))
      (t, x) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  have hcompOn := hG.frameCompSmooth (e.localFrame b) hframe
  have hmemProd : (D.regular ×ˢ e.baseSet : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds hDreg (e.open_baseSet.mem_nhds hxe)
  have hcompAt : ∀ i j,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          (G.metric q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2))
        (t, x) := fun i j =>
    (hcompOn i j).contMDiffAt hmemProd
  have hcoeff : ∀ (a : Fin 2) i,
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => e.localFrame_coeff I b i y ((V a) y)) x := fun a i =>
    contMDiffAt_localFrame_coeff (I := I) b hxe
      ((V a).contMDiff.contMDiffAt) i
  have hsum :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          ∑ i, ∑ j,
            e.localFrame_coeff I b i q.2 ((V 0) q.2) *
              e.localFrame_coeff I b j q.2 ((V 1) q.2) *
              (G.metric q.1).inner q.2
                (e.localFrame b i q.2) (e.localFrame b j q.2))
        (t, x) := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (((hcoeff 0 i).comp (t, x) contMDiffAt_snd).mul
      ((hcoeff 1 j).comp (t, x) contMDiffAt_snd)).mul (hcompAt i j)
  refine hsum.congr_of_eventuallyEq ?_
  have hev0 := e.eventually_eq_localFrame_sum_coeff_smul
    (I := I) b (s := fun y => (V 0) y) hxe
  have hev1 := e.eventually_eq_localFrame_sum_coeff_smul
    (I := I) b (s := fun y => (V 1) y) hxe
  have hev : ∀ᶠ q : Real × M in 𝓝 (t, x),
      ((V 0) q.2 =
        ∑ i, e.localFrame_coeff I b i q.2 ((V 0) q.2) • e.localFrame b i q.2) ∧
      ((V 1) q.2 =
        ∑ i, e.localFrame_coeff I b i q.2 ((V 1) q.2) • e.localFrame b i q.2) :=
    (continuous_snd.tendsto (t, x)).eventually (hev0.and hev1)
  filter_upwards [hev] with q hq
  have hexp :
      (G.metric q.1).inner q.2 ((V 0) q.2) ((V 1) q.2) =
        (G.metric q.1).inner q.2
          (∑ i, e.localFrame_coeff I b i q.2 ((V 0) q.2) • e.localFrame b i q.2)
          (∑ j, e.localFrame_coeff I b j q.2 ((V 1) q.2) • e.localFrame b j q.2) := by
    rw [← hq.1, ← hq.2]
  rw [hexp]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    ring

end MetricFamilySmoothOn
end DifferentialGeometry.Integral.Connection

end
