import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.Manifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section
open Set Function Filter Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.ODE

section GlobalClosed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
open Bundle in

theorem autonomizedFlowVF_section_contMDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF X p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  have hψ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M =>
        (TotalSpace.mk' ℝ p.1 ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) p.1) :
          TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : ℝ =>
          (TotalSpace.mk' ℝ x ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) x) :
            TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      intro x₀
      rw [Bundle.contMDiffAt_section]
      simpa using (contMDiffAt_const (c := (1 : ℝ)))
    exact hone.comp contMDiff_fst
  have hχ : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M)) := hX
  have hpair : ContMDiff (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (I.prod 𝓘(ℝ, E))) ∞
      (fun p : ℝ × M =>
        ((TotalSpace.mk' ℝ p.1 ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) p.1) :
            TangentBundle 𝓘(ℝ, ℝ) ℝ),
          (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))) :=
    hψ.prodMk hχ
  have hsymm :
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (I.prod 𝓘(ℝ, E)))
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
        ((equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm) :=
    contMDiff_equivTangentBundleProd_symm
  exact hsymm.comp hpair

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in

theorem autonomizedFieldJointC1_of_contMDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))) :
    AutonomizedFieldJointC1 (I := I) X := by
  intro p
  have h1le : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  exact ((autonomizedFlowVF_section_contMDiff X hX).of_le h1le).contMDiffAt

theorem global_flow_jointContMDiffOn_on_closed_manifold
    [CompactSpace M] [CompleteSpace E] [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ : ℝ) :
    ∃ (T : ℝ) (_ : 0 < T) (Φ : M → ℝ → M),
      (∀ p, Φ p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ (Set.univ : Set M)) ∧
      (∀ p, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))) := by
  classical
  have hX_auto : AutonomizedFieldJointC1 (I := I) X :=
    autonomizedFieldJointC1_of_contMDiff X hX
  have hlocal : ∀ p₀ : M, ∃ (U : Set M) (_ : IsOpen U) (_ : p₀ ∈ U) (T : ℝ) (_ : 0 < T)
      (Φ : M → ℝ → M),
      (∀ p ∈ U, Φ p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) ∧
      (∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))) :=
    fun p₀ => local_flow_jointSmooth_and_integralCurve X hX t₀ p₀
  choose U hU_open hU_mem Tloc hTloc_pos Φloc hΦloc_init hΦloc_smooth hΦloc_bare
    using hlocal
  have hcover : (Set.univ : Set M) ⊆ ⋃ p₀, U p₀ :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨s, hs_cover⟩ :=
    (isCompact_univ (X := M)).elim_finite_subcover U hU_open hcover
  by_cases hMempty : IsEmpty M
  · refine ⟨1, one_pos, fun p _ => p, fun p => (hMempty.false p).elim,
      ?_, fun p => (hMempty.false p).elim⟩
    have huniv_empty : (Set.univ : Set M) = (∅ : Set M) :=
      Set.univ_eq_empty_iff.mpr hMempty
    rw [huniv_empty, Set.prod_empty]
    exact contMDiffOn_empty
  · rw [not_isEmpty_iff] at hMempty
    have hs_ne : s.Nonempty := by
      rcases hMempty with ⟨x₀⟩
      have hx : x₀ ∈ ⋃ i ∈ s, U i := hs_cover (Set.mem_univ x₀)
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨i, hi, _⟩ := hx
      exact ⟨i, hi⟩
    set T : ℝ := s.inf' hs_ne Tloc with hT_def
    have hT_pos : 0 < T := by
      rw [hT_def, Finset.lt_inf'_iff]
      exact fun i hi => hTloc_pos i
    have hT_le : ∀ i ∈ s, T ≤ Tloc i := fun i hi => Finset.inf'_le _ hi
    have ht₀_mem : t₀ ∈ Set.Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
    have hαRep : ∀ x : M, ∃ i, i ∈ s ∧ x ∈ U i := by
      intro x
      have hx : x ∈ ⋃ i ∈ s, U i := hs_cover (Set.mem_univ x)
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact ⟨i, hi, hxi⟩
    choose αRep hαRep_mem hαRep_in using hαRep
    set Φ : M → ℝ → M := fun x s => Φloc (αRep x) x s with hΦ_def
    have hagree : ∀ (i j : M) (x : M), i ∈ s → j ∈ s → x ∈ U i → x ∈ U j →
        ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T), Φloc i x t = Φloc j x t := by
      intro i j x hi hj hxi hxj t ht
      have hwin_i : Set.Ioo (t₀ - T) (t₀ + T) ⊆ Set.Ioo (t₀ - Tloc i) (t₀ + Tloc i) :=
        Set.Ioo_subset_Ioo (by linarith [hT_le i hi]) (by linarith [hT_le i hi])
      have hwin_j : Set.Ioo (t₀ - T) (t₀ + T) ⊆ Set.Ioo (t₀ - Tloc j) (t₀ + Tloc j) :=
        Set.Ioo_subset_Ioo (by linarith [hT_le j hj]) (by linarith [hT_le j hj])
      have hflow_i : ∀ u ∈ Set.Ioo (t₀ - T) (t₀ + T),
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun r : ℝ => (fun r' _ => Φloc i x r') r (x : M))
            (Set.Ioo (t₀ - T) (t₀ + T)) u
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X u ((fun r' _ => Φloc i x r') u (x : M)))) := by
        intro u hu
        exact (hΦloc_bare i x hxi u (hwin_i hu)).hasMFDerivWithinAt
      have hflow_j : ∀ u ∈ Set.Ioo (t₀ - T) (t₀ + T),
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun r : ℝ => (fun r' _ => Φloc j x r') r (x : M))
            (Set.Ioo (t₀ - T) (t₀ + T)) u
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X u ((fun r' _ => Φloc j x r') u (x : M)))) := by
        intro u hu
        exact (hΦloc_bare j x hxj u (hwin_j hu)).hasMFDerivWithinAt
      have hstart : (fun r' _ => Φloc i x r') t₀ (x : M) = (fun r' _ => Φloc j x r') t₀ (x : M) := by
        simp only
        rw [hΦloc_init i x hxi, hΦloc_init j x hxj]
      have := bare_integral_flow_eqOn_of_jointC1 (a := t₀ - T) (b := t₀ + T) (t₀ := t₀)
        X hX_auto (fun r' _ => Φloc i x r') (fun r' _ => Φloc j x r') x x
        ht₀_mem hflow_i hflow_j hstart t ht
      simpa using this
    have hinit : ∀ p, Φ p t₀ = p := by
      intro p
      have := hΦloc_init (αRep p) p (hαRep_in p)
      simpa [hΦ_def] using this
    have hbare : ∀ p, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u => Φ p u) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t))) := by
      intro p t ht
      have hi := hαRep_mem p
      have hwin : Set.Ioo (t₀ - T) (t₀ + T) ⊆ Set.Ioo (t₀ - Tloc (αRep p)) (t₀ + Tloc (αRep p)) :=
        Set.Ioo_subset_Ioo (by linarith [hT_le (αRep p) hi]) (by linarith [hT_le (αRep p) hi])
      have h := hΦloc_bare (αRep p) p (hαRep_in p) t (hwin ht)
      change HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u => Φloc (αRep p) p u) t _
      simpa [hΦ_def] using h
    have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ (Set.univ : Set M)) := by
      intro q hq
      obtain ⟨ht, _⟩ := hq
      set i : M := αRep q.2 with hi_def
      have hi_s : i ∈ s := hαRep_mem q.2
      have hq2_Ui : q.2 ∈ U i := hαRep_in q.2
      set W : Set (ℝ × M) := Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U i with hW_def
      have hW_open : IsOpen W := isOpen_Ioo.prod (hU_open i)
      have hq_W : q ∈ W := ⟨ht, hq2_Ui⟩
      have hwin_i : Set.Ioo (t₀ - T) (t₀ + T) ⊆ Set.Ioo (t₀ - Tloc i) (t₀ + Tloc i) :=
        Set.Ioo_subset_Ioo (by linarith [hT_le i hi_s]) (by linarith [hT_le i hi_s])
      have hΦi_W : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q' : ℝ × M => Φloc i q'.2 q'.1) W :=
        (hΦloc_smooth i).mono (Set.prod_mono hwin_i (subset_refl _))
      have hcongr : ∀ q' ∈ W, (fun q' : ℝ × M => Φ q'.2 q'.1) q' =
          (fun q' : ℝ × M => Φloc i q'.2 q'.1) q' := by
        rintro ⟨t', x'⟩ ⟨ht', hx'_Ui⟩
        change Φloc (αRep x') x' t' = Φloc i x' t'
        exact hagree (αRep x') i x' (hαRep_mem x') hi_s (hαRep_in x') hx'_Ui t' ht'
      have hWnhds : W ∈ 𝓝[Set.Ioo (t₀ - T) (t₀ + T) ×ˢ (Set.univ : Set M)] q :=
        mem_nhdsWithin_of_mem_nhds (hW_open.mem_nhds hq_W)
      have hΦi_at : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
          (fun q' : ℝ × M => Φloc i q'.2 q'.1) W q := hΦi_W q hq_W
      have hΦglob_W : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
          (fun q' : ℝ × M => Φ q'.2 q'.1) W q := by
        refine hΦi_at.congr_of_eventuallyEq ?_ (hcongr q hq_W)
        filter_upwards [self_mem_nhdsWithin] with q' hq' using hcongr q' hq'
      exact hΦglob_W.mono_of_mem_nhdsWithin hWnhds
    exact ⟨T, hT_pos, Φ, hinit, hsmooth, hbare⟩

end GlobalClosed

end DifferentialGeometry.PDE.RicciFlow.ODE
