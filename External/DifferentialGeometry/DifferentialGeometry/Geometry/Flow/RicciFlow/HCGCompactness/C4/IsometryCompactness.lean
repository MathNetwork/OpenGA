import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false




















namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]








def IsometryDerivBounds (Φ : ℕ → E → F) : Prop :=
  ∀ r : ℕ, ∀ K : Set E, IsCompact K →
    ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem IsometryDerivBounds.comp_subseq {Φ : ℕ → E → F} (h : IsometryDerivBounds Φ)
    (φ : ℕ → ℕ) : IsometryDerivBounds (fun k => Φ (φ k)) := by
  intro r K hK
  obtain ⟨M, hM⟩ := h r K hK
  exact ⟨M, fun k x hx => hM (φ k) x hx⟩






theorem isometry_seq_cInf
    (Φ : ℕ → E → F) (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k))
    (hbdd : IsometryDerivBounds Φ) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq Φ hΦ hbdd

omit [FiniteDimensional ℝ E] in





theorem comp_eq_id_of_cInf
    {Φ : ℕ → F → E} {Φinf : F → E} {Ψ : ℕ → E → F} {Ψinf : E → F}
    (hΦ : MapCInfConvOnCompacts Set.univ Φ Φinf) (hΦc : Continuous Φinf)
    (hΨ : MapCInfConvOnCompacts Set.univ Ψ Ψinf)
    (hid : ∀ k x, Φ k (Ψ k x) = x) :
    ∀ x, Φinf (Ψinf x) = x := by
  intro x
  have hΨx : Tendsto (fun k => Ψ k x) atTop (𝓝 (Ψinf x)) :=
    tendsto_of_cInf hΨ (Set.mem_univ x)
  obtain ⟨K, hKmem, hKcomp, -⟩ := exists_mem_nhds_isCompact_isClosed (Ψinf x)
  have hΦunif : TendstoUniformlyOn Φ Φinf atTop K :=
    tendstoUniformlyOn_of_cPConv (hΦ K hKcomp (Set.subset_univ K) 0)
  have hΨxK : Tendsto (fun k => Ψ k x) atTop (𝓝[K] (Ψinf x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hΨx (hΨx.eventually_mem hKmem)
  have hcomp : Tendsto (fun k => Φ k (Ψ k x)) atTop (𝓝 (Φinf (Ψinf x))) :=
    hΦunif.tendsto_comp hΦc.continuousWithinAt hΨxK
  simp only [hid] at hcomp
  exact (tendsto_nhds_unique tendsto_const_nhds hcomp).symm







theorem isometry_seq_diffeo
    (Φ : ℕ → E → F) (Ψ : ℕ → F → E)
    (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k)) (hΨ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k))
    (hbΦ : IsometryDerivBounds Φ) (hbΨ : IsometryDerivBounds Ψ)
    (hLeft : ∀ k x, Ψ k (Φ k x) = x) (hRight : ∀ k y, Φ k (Ψ k y) = y) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F) (Ψinf : F → E),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧ ContDiff ℝ (⊤ : ℕ∞) Ψinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Φ (φ k)) Φinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Ψ (φ k)) Ψinf ∧
        (∀ x, Ψinf (Φinf x) = x) ∧ (∀ y, Φinf (Ψinf y) = y) := by
  obtain ⟨φ1, Φinf, hφ1, hΦinf, hΦconv⟩ := exists_cInf_subseq Φ hΦ hbΦ
  obtain ⟨φ2, Ψinf, hφ2, hΨinf, hΨconv⟩ :=
    exists_cInf_subseq (fun k => Ψ (φ1 k)) (fun k => hΨ (φ1 k)) (hbΨ.comp_subseq φ1)
  have hΦconv' : MapCInfConvOnCompacts Set.univ (fun k => Φ (φ1 (φ2 k))) Φinf :=
    hΦconv.comp_subseq hφ2
  refine ⟨φ1 ∘ φ2, Φinf, Ψinf, hφ1.comp hφ2, hΦinf, hΨinf, hΦconv', hΨconv, ?_, ?_⟩
  · exact comp_eq_id_of_cInf hΨconv hΨinf.continuous hΦconv'
      (fun k x => hLeft (φ1 (φ2 k)) x)
  · exact comp_eq_id_of_cInf hΦconv' hΦinf.continuous hΨconv
      (fun k y => hRight (φ1 (φ2 k)) y)

end HCGCompactness
end DifferentialGeometry
