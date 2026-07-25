import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false










namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

section MapConvergence

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




noncomputable def mapDerivNorm (r : ℕ) (Φk Φinf : E → F) (x : E) : ℝ :=
  ‖iteratedFDeriv ℝ r (fun y => Φk y - Φinf y) x‖

theorem mapDerivNorm_nonneg (r : ℕ) (Φk Φinf : E → F) (x : E) :
    0 ≤ mapDerivNorm r Φk Φinf x :=
  norm_nonneg _




def MapCPConvOn (K : Set E) (p : ℕ) (Φ : ℕ → E → F) (Φinf : E → F) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    ∀ r : ℕ, r ≤ p → ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε






def MapCInfConvOnCompacts (U : Set E) (Φ : ℕ → E → F) (Φinf : E → F) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → ∀ p : ℕ, MapCPConvOn K p Φ Φinf



theorem MapCPConvOn.mono_order {K : Set E} {p p' : ℕ} (hp : p' ≤ p)
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvOn K p Φ Φinf) :
    MapCPConvOn K p' Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (hr.trans hp) x hx⟩


theorem MapCPConvOn.mono_set {K K' : Set E} (hK : K' ⊆ K) {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F} (h : MapCPConvOn K p Φ Φinf) :
    MapCPConvOn K' p Φ Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r hr x (hK hx)⟩




theorem MapCInfConvOnCompacts.cPConvOn {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) (p : ℕ) : MapCPConvOn K p Φ Φinf :=
  h K hK hKU p


theorem MapCPConvOn.comp_subseq {K : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvOn K p Φ Φinf) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MapCPConvOn K p (fun k => Φ (φ k)) Φinf := by
  intro ε hε
  obtain ⟨k0, hk0⟩ := h ε hε
  exact ⟨k0, fun k hk r hr x hx => hk0 (φ k) (le_trans hk (hφ.id_le k)) r hr x hx⟩


theorem MapCInfConvOnCompacts.comp_subseq {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MapCInfConvOnCompacts U (fun k => Φ (φ k)) Φinf :=
  fun K hK hKU p => (h K hK hKU p).comp_subseq hφ



theorem tendstoUniformlyOn_of_cPConv {K : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvOn K 0 Φ Φinf) : TendstoUniformlyOn Φ Φinf atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨k0, hk0⟩ := h (ε / 2) (by positivity)
  rw [eventually_atTop]
  refine ⟨k0, fun k hk x hx => ?_⟩
  have hb := hk0 k hk 0 le_rfl x hx
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at hb
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hb (by linarith)



theorem tendsto_of_cInf {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf) {x : E} (hx : x ∈ U) :
    Tendsto (fun k => Φ k x) atTop (𝓝 (Φinf x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k0, hk0⟩ :=
    h {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx) 0 (ε / 2) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  have hb := hk0 k hk 0 le_rfl x rfl
  rw [mapDerivNorm, norm_iteratedFDeriv_zero] at hb
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hb (by linarith)






theorem mapCPConvOn_of_tendstoUniformly {K : Set E} {p : ℕ}
    {Φ : ℕ → E → F} {Φinf : E → F}
    (hΦ : ∀ k, ContDiff ℝ (p : ℕ∞) (Φ k)) (hΦinf : ContDiff ℝ (p : ℕ∞) Φinf)
    (htu : ∀ r : ℕ, r ≤ p →
      TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ r (Φ k) x)
        (fun x => iteratedFDeriv ℝ r Φinf x) atTop K) :
    MapCPConvOn K p Φ Φinf := by
  intro ε hε
  have key : ∀ r : ℕ, r ≤ p →
      ∀ᶠ k in atTop, ∀ x ∈ K, mapDerivNorm r (Φ k) Φinf x ≤ ε := by
    intro r hr
    have h := (Metric.tendstoUniformlyOn_iff.mp (htu r hr)) ε hε
    filter_upwards [h] with k hk x hx
    have hsub : iteratedFDeriv ℝ r (fun y => Φ k y - Φinf y) x
        = iteratedFDeriv ℝ r (Φ k) x - iteratedFDeriv ℝ r Φinf x :=
      iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (x := x)
        ((hΦ k).contDiffAt.of_le (by exact_mod_cast hr))
        (hΦinf.contDiffAt.of_le (by exact_mod_cast hr))
    have hdist := hk x hx
    rw [dist_eq_norm, ← norm_sub_rev] at hdist
    rw [mapDerivNorm, hsub]
    exact hdist.le
  have hfin : ∀ᶠ k in atTop, ∀ r ∈ Set.Iic p, ∀ x ∈ K,
      mapDerivNorm r (Φ k) Φinf x ≤ ε :=
    (Set.finite_Iic p).eventually_all.2 (fun r hr => key r (Set.mem_Iic.mp hr))
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp hfin
  exact ⟨k0, fun k hk r hr x hx => hk0 k hk r (Set.mem_Iic.mpr hr) x hx⟩

end MapConvergence

end HCGCompactness
end DifferentialGeometry
