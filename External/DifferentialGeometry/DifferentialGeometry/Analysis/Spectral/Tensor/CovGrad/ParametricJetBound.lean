import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth










noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open Tensor0SBundle TensorRSNabla

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_rfns_cont
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r s p.2
        ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
  have hsub : (K ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ x, hKS ht⟩
  have hswap : Continuous (fun p : ℝ × M => (p.2, p.1)) := by
    fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.2
        ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswap.continuousOn hsub).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hinner : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ)
        (E := fun x : M =>
          TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2))
      (K ×ˢ (Set.univ : Set M)) :=
    ((tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g₀ r s).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))
      (K ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂
      (F₁ := TensorRSModel r s ℝ E) (F₂ := TensorRSModel r s ℝ E)
      (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hinner hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))).mp
      (happ p hp)).2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
    (I := I) (M := M) g₀ r s x ((Φ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]



omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_iter_joint
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r (s + i) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + i) I z) p.1
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
      exact covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (s + j)
        (fun t => iteratedCovGrad (I := I) g₀ r s j (Φ t)) S ih



omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_jet_rfns
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2))
      (K ×ˢ (Set.univ : Set M)) :=
  joint_rfns_cont (I := I) (M := M) g₀ r (s + i)
    (fun t => iteratedCovGrad (I := I) g₀ r s i (Φ t)) hKS
    (covGrad_iter_joint (I := I) (M := M) g₀ r s i Φ S hjoint)

omit [T2Space M] [SigmaCompactSpace M] in


private theorem joint_small
    (f : ℝ → M → ℝ) {S : Set ℝ} {t₀ : ℝ}
    (hS : S ∈ 𝓝 t₀)
    (hf : ContinuousOn (fun p : ℝ × M => f p.1 p.2)
      (S ×ˢ (Set.univ : Set M)))
    (hzero : ∀ x : M, f t₀ x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ x : M, f t x < ε := by
  classical
  have hpatch (x : M) :
      ∃ V : Set ℝ, V ∈ 𝓝 t₀ ∧
        ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
          ∀ t ∈ V, ∀ y ∈ W, f t y < ε := by
    let F : ℝ × M → ℝ := fun p => f p.1 p.2
    have hdom : S ×ˢ (Set.univ : Set M) ∈ 𝓝 (t₀, x) :=
      prod_mem_nhds hS Filter.univ_mem
    have hFcont : ContinuousAt F (t₀, x) := by
      simpa only [F] using
        (hf (t₀, x) ⟨mem_of_mem_nhds hS, Set.mem_univ x⟩).continuousAt hdom
    have hsmall : {p : ℝ × M | F p < ε} ∈ 𝓝 (t₀, x) := by
      exact hFcont.eventually_lt_const (by simpa only [F, hzero x] using hε)
    obtain ⟨V, W, hVOpen, htV, hWOpen, hxW, hVW⟩ :=
      mem_nhds_prod_iff'.mp hsmall
    refine ⟨V, hVOpen.mem_nhds htV, W, hWOpen, hxW, ?_⟩
    intro t ht y hy
    have hty : (t, y) ∈ V ×ˢ W := ⟨ht, hy⟩
    simpa only [F] using hVW hty
  choose V hV W hWOpen hxW hloc using hpatch
  obtain ⟨F, _, hF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_nhds_subcover W
      (fun x _ => (hWOpen x).mem_nhds (hxW x))
  have htime :
      ∀ᶠ t in 𝓝 t₀, ∀ x ∈ F, t ∈ V x := by
    exact
      (Finset.eventually_all
        (I := F)
        (l := 𝓝 t₀)
        (p := fun x t => t ∈ V x)).2
        (fun x _ => hV x)
  filter_upwards [htime] with t ht
  intro y
  obtain ⟨x, hxF, hyW⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
  exact hloc x t (ht x hxF) y hyW




omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_jet_small
    (g₀ : SmoothRiemannianMetric I M) (r s p : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S : Set ℝ} {t₀ : ℝ}
    (hS : S ∈ 𝓝 t₀) (hzero : Φ t₀ = 0)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1
        ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε := by
  classical
  have hiter0 (i : ℕ) :
      iteratedCovGrad (I := I) g₀ r s i (0 : SmoothCcTensor g₀ r s) = 0 := by
    induction i with
    | zero => rw [iteratedCovGrad_zero]
    | succ j ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]
  have hi (i : ℕ) :
      ∀ᶠ t in 𝓝 t₀, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε := by
    apply joint_small (f := fun t x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x)) hS
    · exact joint_jet_rfns (I := I) (M := M) g₀ r s i Φ
        (S := S) (K := S) (fun _ ht => ht) hjoint
    · intro x
      rw [hzero, hiter0 i]
      rw [show ((0 : SmoothCcTensor g₀ r (s + i)).toSection x) =
        (0 : TensorRSSpace r (s + i) I x) from by
          rw [SmoothCcTensor.toSection_zero]
          rfl]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ r (s + i) x
    · exact hε
  have htime :
      ∀ᶠ t in 𝓝 t₀, ∀ i ∈ Finset.range (p + 1), ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε := by
    exact
      (Finset.eventually_all
        (I := Finset.range (p + 1))
        (l := 𝓝 t₀)
        (p := fun i t => ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) < ε)).2
        (fun i _ => hi i)
  filter_upwards [htime] with t ht
  intro i hip x
  exact ht i (by simp only [Finset.mem_range]; omega) x




omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem joint_jet_bdd
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ i t, t ∈ K → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) ≤ B i := by
  classical
  have hprod : IsCompact (K ×ˢ (Set.univ : Set M)) :=
    hK.prod isCompact_univ
  have hex : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t, t ∈ K → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x) ≤ C := by
    intro i
    let F : ℝ × M → ℝ := fun p =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2)
    have hcont : ContinuousOn F (K ×ˢ (Set.univ : Set M)) :=
      joint_jet_rfns (I := I) (M := M) g₀ r s i Φ hKS hjoint
    obtain ⟨C₀, hC₀⟩ := (hprod.image_of_continuousOn hcont).bddAbove
    refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
    intro t ht x
    refine le_trans (hC₀ ?_) (le_max_left _ _)
    exact ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩
  choose B hB_nonneg hB using hex
  exact ⟨B, hB_nonneg, hB⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
