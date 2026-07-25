import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.IsometryCompactness
import DifferentialGeometry.Analysis.Calculus.PiDeriv

set_option autoImplicit false



































namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






def IsometryDerivBoundsOn (U : Set E) (Φ : ℕ → E → F) : Prop :=
  ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
    ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem IsometryDerivBoundsOn.comp_subseq {U : Set E} {Φ : ℕ → E → F}
    (h : IsometryDerivBoundsOn U Φ) (φ : ℕ → ℕ) :
    IsometryDerivBoundsOn U (fun k => Φ (φ k)) := by
  intro r K hK hKU
  obtain ⟨M, hM⟩ := h r K hK hKU
  exact ⟨M, fun k x hx => hM (φ k) x hx⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in


theorem IsometryDerivBoundsOn.pi
    {ι : Type*} [Fintype ι] {U : Set E} {Φ : ℕ → E → (ι → F)}
    (hU : IsOpen U)
    (hsmooth : ∀ k i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Φ k x i) U)
    (hbdd : ∀ i, IsometryDerivBoundsOn U (fun k x => Φ k x i)) :
    IsometryDerivBoundsOn U Φ := by
  classical
  intro r K hK hKU
  choose M hM using fun i => hbdd i r K hK hKU
  refine ⟨∑ i, max (M i) 0, fun k x hx => ?_⟩
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hcd : ∀ i, ContDiffAt ℝ ((r : ℕ∞) : WithTop ℕ∞)
      (fun y => Φ k y i) x := fun i =>
    ((hsmooth k i).contDiffAt (hU.mem_nhds (hKU hx))).of_le hr
  rw [iteratedFDeriv_pi hcd le_rfl, ContinuousMultilinearMap.opNorm_pi,
    pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right (M i) 0)]
  intro i
  calc
    ‖iteratedFDeriv ℝ r (fun y => Φ k y i) x‖ ≤ M i := hM i k x hx
    _ ≤ max (M i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (M j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right (M j) 0) (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem IsometryDerivBounds.toOn {Φ : ℕ → E → F} (h : IsometryDerivBounds Φ)
    (U : Set E) : IsometryDerivBoundsOn U Φ :=
  fun r K hK _ => h r K hK

omit [FiniteDimensional ℝ E] in









theorem comp_eq_id_of_cInf_on
    {U : Set E} {V : Set F}
    {Φ : ℕ → F → E} {Φinf : F → E} {Ψ : ℕ → E → F} {Ψinf : E → F}
    (hV : IsOpen V)
    (hΦ : MapCInfConvOnCompacts V Φ Φinf) (hΦc : ContinuousOn Φinf V)
    (hΨ : MapCInfConvOnCompacts U Ψ Ψinf)
    (hid : ∀ k, ∀ x' ∈ U, Φ k (Ψ k x') = x') {x : E} (hx : x ∈ U) (hΨinf : Ψinf x ∈ V) :
    Φinf (Ψinf x) = x := by
  have hΨx : Tendsto (fun k => Ψ k x) atTop (𝓝 (Ψinf x)) := tendsto_of_cInf hΨ hx
  obtain ⟨K, hKcomp, hKint, hKV⟩ := exists_compact_subset hV hΨinf
  have hKmem : K ∈ 𝓝 (Ψinf x) := mem_interior_iff_mem_nhds.mp hKint
  have hΦunif : TendstoUniformlyOn Φ Φinf atTop K :=
    tendstoUniformlyOn_of_cPConv (hΦ K hKcomp hKV 0)
  have hΨxK : Tendsto (fun k => Ψ k x) atTop (𝓝[K] (Ψinf x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hΨx (hΨx.eventually_mem hKmem)
  have hcomp : Tendsto (fun k => Φ k (Ψ k x)) atTop (𝓝 (Φinf (Ψinf x))) :=
    hΦunif.tendsto_comp ((hΦc (Ψinf x) hΨinf).mono hKV) hΨxK
  have hidx : ∀ k, Φ k (Ψ k x) = x := fun k => hid k x hx
  simp only [hidx] at hcomp
  exact (tendsto_nhds_unique tendsto_const_nhds hcomp).symm







theorem isometry_seq_cInf_on
    {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U) (hbdd : IsometryDerivBoundsOn U Φ) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧
        MapCInfConvOnCompacts U (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq_on hU Φ hΦ hbdd










theorem isometry_seq_diffeo_on
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : ℕ → E → F) (Ψ : ℕ → F → E)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hΨ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Ψ k) V)
    (hbΦ : IsometryDerivBoundsOn U Φ) (hbΨ : IsometryDerivBoundsOn V Ψ)
    (hLeft : ∀ k, ∀ x ∈ U, Ψ k (Φ k x) = x) (hRight : ∀ k, ∀ y ∈ V, Φ k (Ψ k y) = y) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F) (Ψinf : F → E),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧ ContDiffOn ℝ (⊤ : ℕ∞) Ψinf V ∧
        MapCInfConvOnCompacts U (fun k => Φ (φ k)) Φinf ∧
        MapCInfConvOnCompacts V (fun k => Ψ (φ k)) Ψinf ∧
        (∀ x ∈ U, Φinf x ∈ V → Ψinf (Φinf x) = x) ∧
        (∀ y ∈ V, Ψinf y ∈ U → Φinf (Ψinf y) = y) := by
  obtain ⟨φ1, Φinf, hφ1, hΦinf, hΦconv⟩ := exists_cInf_subseq_on hU Φ hΦ hbΦ
  obtain ⟨φ2, Ψinf, hφ2, hΨinf, hΨconv⟩ :=
    exists_cInf_subseq_on hV (fun k => Ψ (φ1 k)) (fun k => hΨ (φ1 k)) (hbΨ.comp_subseq φ1)
  have hΦconv' : MapCInfConvOnCompacts U (fun k => Φ (φ1 (φ2 k))) Φinf :=
    hΦconv.comp_subseq hφ2
  refine ⟨φ1 ∘ φ2, Φinf, Ψinf, hφ1.comp hφ2, hΦinf, hΨinf, hΦconv', hΨconv, ?_, ?_⟩
  · intro x hx hΦx
    exact comp_eq_id_of_cInf_on hV hΨconv hΨinf.continuousOn hΦconv'
      (fun k x' hx' => hLeft (φ1 (φ2 k)) x' hx') hx hΦx
  · intro y hy hΨy
    exact comp_eq_id_of_cInf_on hU hΦconv' hΦinf.continuousOn hΨconv
      (fun k y' hy' => hRight (φ1 (φ2 k)) y' hy') hy hΨy

end HCGCompactness
end DifferentialGeometry
