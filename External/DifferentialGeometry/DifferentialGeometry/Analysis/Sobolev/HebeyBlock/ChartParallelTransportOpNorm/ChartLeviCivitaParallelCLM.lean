import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.TangentBundleTrivOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative

noncomputable section

open Bundle ContinuousLinearMap Set Filter Finset
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional ℝ E] in
private lemma exists_W_and_constant_tangent_symmL
    (g : SmoothRiemannianMetric I M)
    (α y₀ : M)
    (h_y₀_α : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ∃ W : Set M, IsOpen W ∧ y₀ ∈ W ∧ ∃ N : ℝ, 0 < N ∧ ∀ b ∈ W,
      ‖(trivializationAt E (TangentSpace I) α).symmL ℝ b‖ ≤ N := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  obtain ⟨C₁, hC₁_pos, hC₁_ev⟩ :=
    eventually_norm_symmL_trivializationAt_lt E (fun b : M => TangentSpace I b) y₀
  set ccF : M → (E →L[ℝ] E) := fun b =>
    (trivializationAt E (TangentSpace I) α).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) y₀) b with hccF_def
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ ccF
        ((trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) y₀).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
      (F := E)
      (E := fun y : M => TangentSpace I y)
      (trivializationAt E (TangentSpace I) α)
      (trivializationAt E (TangentSpace I) y₀)
  have hy₀_y₀ : y₀ ∈ (trivializationAt E (TangentSpace I) y₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' y₀
  have hy₀_inter :
      y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) y₀).baseSet :=
    ⟨h_y₀_α, hy₀_y₀⟩
  have h_cont : ContinuousOn ccF
      ((trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) y₀).baseSet) :=
    h_smooth.continuousOn
  have h_open_inter :
      IsOpen ((trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) y₀).baseSet) :=
    (trivializationAt E (TangentSpace I) α).open_baseSet.inter
      (trivializationAt E (TangentSpace I) y₀).open_baseSet
  have h_cc_continuousAt : ContinuousAt ccF y₀ :=
    h_cont.continuousAt (h_open_inter.mem_nhds hy₀_inter)
  have h_norm_continuousAt : ContinuousAt (fun b => ‖ccF b‖) y₀ :=
    continuous_norm.continuousAt.comp h_cc_continuousAt
  set C₂ : ℝ := ‖ccF y₀‖ + 1 with hC₂_def
  have hC₂_pos : 0 < C₂ := by rw [hC₂_def]; positivity
  have h_cc_ev : ∀ᶠ b in 𝓝 y₀, ‖ccF b‖ < C₂ := by
    exact h_norm_continuousAt (Iio_mem_nhds (by rw [hC₂_def]; linarith))
  rcases (Filter.eventually_iff_exists_mem.mp hC₁_ev) with ⟨U₁, hU₁_nhd, hU₁_bound⟩
  rcases mem_nhds_iff.mp hU₁_nhd with ⟨V₁, hV₁_sub, hV₁_open, hV₁_mem⟩
  rcases (Filter.eventually_iff_exists_mem.mp h_cc_ev) with ⟨U₂, hU₂_nhd, hU₂_bound⟩
  rcases mem_nhds_iff.mp hU₂_nhd with ⟨V₂, hV₂_sub, hV₂_open, hV₂_mem⟩
  refine ⟨V₁ ∩ V₂ ∩ (trivializationAt E (TangentSpace I) y₀).baseSet ∩
    (trivializationAt E (TangentSpace I) α).baseSet,
    ((hV₁_open.inter hV₂_open).inter
      (trivializationAt E (TangentSpace I) y₀).open_baseSet).inter
      (trivializationAt E (TangentSpace I) α).open_baseSet,
    ⟨⟨⟨hV₁_mem, hV₂_mem⟩, hy₀_y₀⟩, h_y₀_α⟩, ?_⟩
  refine ⟨C₁ * C₂, by positivity, ?_⟩
  intro b hb
  obtain ⟨⟨⟨hb_V₁, hb_V₂⟩, hb_y₀⟩, hb_α⟩ := hb
  have h_symm_norm_le :
      ‖(trivializationAt E (TangentSpace I) y₀).symmL ℝ b‖ ≤ C₁ :=
    le_of_lt (hU₁_bound b (hV₁_sub hb_V₁))
  have h_cc_norm_le : ‖ccF b‖ ≤ C₂ :=
    le_of_lt (hU₂_bound b (hV₂_sub hb_V₂))
  set ey₀ := trivializationAt E (TangentSpace I) y₀ with hey₀_def
  set eα := trivializationAt E (TangentSpace I) α with heα_def
  have hboth_αy₀ : b ∈ eα.baseSet ∩ ey₀.baseSet := ⟨hb_α, hb_y₀⟩
  have h_cc_factor (w : E) :
      (eα.coordChangeL ℝ ey₀ b : E →L[ℝ] E) w =
        ey₀.continuousLinearMapAt ℝ b (eα.symmL ℝ b w) := by
    change (eα.coordChangeL ℝ ey₀ b) w = _
    rw [Trivialization.coordChangeL_apply _ _ hboth_αy₀]
    have h_symm_eq : eα.symm b w = eα.symmL ℝ b w := by
      rw [Trivialization.symmL_apply]
    rw [h_symm_eq]
    rw [Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ ey₀ b hb_y₀,
      Trivialization.coe_continuousLinearEquivAt_eq ey₀ hb_y₀]
  have h_pointwise (w : E) :
      eα.symmL ℝ b w =
      ey₀.symmL ℝ b ((eα.coordChangeL ℝ ey₀ b : E →L[ℝ] E) w) := by
    rw [h_cc_factor w]
    exact (Trivialization.symmL_continuousLinearMapAt (R := ℝ) ey₀ hb_y₀
      (eα.symmL ℝ b w)).symm
  have h_norm_w (w : E) :
      ‖eα.symmL ℝ b w‖ ≤ C₁ * C₂ * ‖w‖ := by
    rw [h_pointwise w]
    calc ‖ey₀.symmL ℝ b ((eα.coordChangeL ℝ ey₀ b : E →L[ℝ] E) w)‖
        ≤ ‖ey₀.symmL ℝ b‖ *
            ‖(eα.coordChangeL ℝ ey₀ b : E →L[ℝ] E) w‖ :=
          (ey₀.symmL ℝ b).le_opNorm _
      _ ≤ C₁ * (C₂ * ‖w‖) := by
          have h1 : ‖(eα.coordChangeL ℝ ey₀ b : E →L[ℝ] E) w‖ ≤ C₂ * ‖w‖ :=
            ((eα.coordChangeL ℝ ey₀ b : E →L[ℝ] E).le_opNorm w).trans
              (mul_le_mul_of_nonneg_right h_cc_norm_le (norm_nonneg _))
          exact mul_le_mul h_symm_norm_le h1 (norm_nonneg _) (le_of_lt hC₁_pos)
      _ = C₁ * C₂ * ‖w‖ := by ring
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) h_norm_w

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional ℝ E] in
theorem chartTrivInv_opNorm_isBounded_on_compact_unconditional
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) {K : Set M} (hK : IsCompact K)
    (hK_base : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K,
      ‖(trivializationAt E (TangentSpace I) α).symmL ℝ b‖ ≤ C := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  let W : M → Set M := fun y₀ =>
    if hy : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet then
      (exists_W_and_constant_tangent_symmL (I := I) (M := M) g α y₀ hy).choose
    else ∅
  have hW_open : ∀ y₀, IsOpen (W y₀) := by
    intro y₀; simp only [W]
    split_ifs with hy
    · exact (exists_W_and_constant_tangent_symmL
        (I := I) (M := M) g α y₀ hy).choose_spec.1
    · exact isOpen_empty
  have hW_mem : ∀ y₀, y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet → y₀ ∈ W y₀ := by
    intro y₀ hy; simp only [W, dif_pos hy]
    exact (exists_W_and_constant_tangent_symmL
      (I := I) (M := M) g α y₀ hy).choose_spec.2.1
  let N : M → ℝ := fun y₀ =>
    if hy : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet then
      (exists_W_and_constant_tangent_symmL
        (I := I) (M := M) g α y₀ hy).choose_spec.2.2.choose
    else 1
  have hN_pos : ∀ y₀, 0 < N y₀ := by
    intro y₀; simp only [N]
    split_ifs with hy
    · exact (exists_W_and_constant_tangent_symmL
        (I := I) (M := M) g α y₀ hy).choose_spec.2.2.choose_spec.1
    · exact one_pos
  have hN_bound : ∀ y₀, y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ b ∈ W y₀,
      ‖(trivializationAt E (TangentSpace I) α).symmL ℝ b‖ ≤ N y₀ := by
    intro y₀ hy b hb
    simp only [W, dif_pos hy] at hb
    simp only [N, dif_pos hy]
    exact (exists_W_and_constant_tangent_symmL
      (I := I) (M := M) g α y₀ hy).choose_spec.2.2.choose_spec.2 b hb
  have h_cover : K ⊆ ⋃ y₀ ∈ K, W y₀ := fun b hb =>
    Set.mem_iUnion₂.mpr ⟨b, hb, hW_mem b (hK_base hb)⟩
  rcases hK.elim_finite_subcover_image (b := K) (c := W)
    (fun y₀ _ => hW_open y₀) h_cover with ⟨S, hS_sub, hS_finite, hS_cover⟩
  set S' : Finset M := hS_finite.toFinset with hS'_def
  have hS_cover' : K ⊆ ⋃ y₀ ∈ S', W y₀ := by
    intro b hb
    rcases Set.mem_iUnion.mp (hS_cover hb) with ⟨y₀, hy₀⟩
    rcases Set.mem_iUnion.mp hy₀ with ⟨hy₀_S, hb_in⟩
    refine Set.mem_iUnion.mpr ⟨y₀, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hb_in⟩
    rw [hS'_def]; exact hS_finite.mem_toFinset.mpr hy₀_S
  have hS_sub_K : ∀ y₀ ∈ S', y₀ ∈ K := by
    intro y₀ hy₀; rw [hS'_def] at hy₀
    exact hS_sub (hS_finite.mem_toFinset.mp hy₀)
  by_cases hS_empty : S' = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro b hb
    have : b ∈ ⋃ y₀ ∈ S', W y₀ := hS_cover' hb
    rw [hS_empty] at this; simp at this
  have hS_nonempty : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set C_max : ℝ := S'.sup' hS_nonempty N with hCmax_def
  have h_C_max_pos : 0 < C_max := by
    rcases hS_nonempty with ⟨y₀, hy₀⟩
    exact (hN_pos y₀).trans_le (Finset.le_sup' (f := N) hy₀)
  refine ⟨C_max, le_of_lt h_C_max_pos, ?_⟩
  intro b hb
  rcases Set.mem_iUnion.mp (hS_cover' hb) with ⟨y₀, hy₀⟩
  rcases Set.mem_iUnion.mp hy₀ with ⟨hy₀_S, hb_in⟩
  have hy₀_base : y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hK_base (hS_sub_K y₀ hy₀_S)
  have hN_b := hN_bound y₀ hy₀_base b hb_in
  have h_le_Cmax : N y₀ ≤ C_max := Finset.le_sup' (f := N) hy₀_S
  exact hN_b.trans h_le_Cmax

variable [NeZero (Module.finrank ℝ E)]

private noncomputable def modelBasisCoordSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)

private lemma modelBasisCoordSup_nonneg :
    0 ≤ modelBasisCoordSup (E := E) := by
  classical
  unfold modelBasisCoordSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨i₀, hi₀⟩ := hne
  have h_nn : (0 : ℝ) ≤ ‖((chartModelBasis E).coord i₀).toContinuousLinearMap‖ :=
    norm_nonneg _
  exact h_nn.trans (Finset.le_sup'
    (f := fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) hi₀)

private lemma norm_coord_le_modelBasisCoordSup
    (i : Fin (Module.finrank ℝ E)) :
    ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ ≤
      modelBasisCoordSup (E := E) := by
  classical
  unfold modelBasisCoordSup
  exact Finset.le_sup'
    (f := fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)
    (Finset.mem_univ _)

private noncomputable def modelBasisVecSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

private lemma modelBasisVecSup_nonneg :
    0 ≤ modelBasisVecSup (E := E) := by
  classical
  unfold modelBasisVecSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  have h_nn : (0 : ℝ) ≤ ‖(chartModelBasis E) k₀‖ := norm_nonneg _
  exact h_nn.trans (Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

private lemma norm_basis_le_modelBasisVecSup
    (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ modelBasisVecSup (E := E) := by
  classical
  unfold modelBasisVecSup
  exact Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖)
    (Finset.mem_univ _)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma christoffelCorrection_summand_opNorm_le_unconditional
    [I.Boundaryless] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) (Y : E)
    (i j k : Fin (Module.finrank ℝ E))
    (C_J : ℝ)
    (hCJ : letI cg : Bundle.ContinuousRiemannianMetric E
              (TangentSpace I : M → Type _) :=
            g.toContinuousRiemannianMetric
          letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
            ⟨cg.toRiemannianMetric⟩
          ‖(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b‖ ≤ C_J)
    (hCJ_nn : 0 ≤ C_J)
    (C_Γ : ℝ) (hCΓ : |chartChristoffel (I := I) g α i j k (extChartAt I α b)| ≤ C_Γ)
    (hCΓ_nn : 0 ≤ C_Γ) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ‖(((chartModelBasis E).coord i).toContinuousLinearMap.comp
          (trivToE (I := I) α b)).smulRight
        (((chartModelBasis E).repr Y j *
            chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
          (chartModelBasis E) k)‖ ≤
      modelBasisCoordSup (E := E) * C_J *
        (modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
        modelBasisVecSup (E := E) := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  set L_i : E →L[ℝ] ℝ := ((chartModelBasis E).coord i).toContinuousLinearMap
  set L_j : E →L[ℝ] ℝ := ((chartModelBasis E).coord j).toContinuousLinearMap
  set Γijk : ℝ := chartChristoffel (I := I) g α i j k (extChartAt I α b)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  have hcomp_le :
      ‖L_i.comp (trivToE (I := I) α b)‖ ≤
        ‖L_i‖ * ‖trivToE (I := I) α b‖ :=
    ContinuousLinearMap.opNorm_comp_le L_i (trivToE (I := I) α b)
  have h_triv_le : ‖trivToE (I := I) α b‖ ≤ C_J := hCJ
  have h_scalar_norm :
      ‖((chartModelBasis E).repr Y j * Γijk) • (chartModelBasis E) k‖ =
        |(chartModelBasis E).repr Y j * Γijk| * ‖(chartModelBasis E) k‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  rw [h_scalar_norm]
  have h_repr_eq : (chartModelBasis E).repr Y j = L_j Y := rfl
  have h_repr_bound : |(chartModelBasis E).repr Y j| ≤ ‖L_j‖ * ‖Y‖ := by
    rw [h_repr_eq]
    have := L_j.le_opNorm Y
    have h_abs : ‖L_j Y‖ = |L_j Y| := Real.norm_eq_abs _
    rw [h_abs] at this
    exact this
  have h_abs_mul : |(chartModelBasis E).repr Y j * Γijk| =
      |(chartModelBasis E).repr Y j| * |Γijk| := abs_mul _ _
  have h_Lj_le : ‖L_j‖ ≤ modelBasisCoordSup (E := E) :=
    norm_coord_le_modelBasisCoordSup (E := E) j
  have h_Lj_nn : 0 ≤ ‖L_j‖ := norm_nonneg _
  have h_Y_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have h_abs_Γ_nn : 0 ≤ |Γijk| := abs_nonneg _
  have h_scalar_bound :
      |(chartModelBasis E).repr Y j * Γijk| ≤
        modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ := by
    rw [h_abs_mul]
    have h1 : |(chartModelBasis E).repr Y j| * |Γijk| ≤
        (‖L_j‖ * ‖Y‖) * C_Γ := by
      have hpos : 0 ≤ ‖L_j‖ * ‖Y‖ := by positivity
      have h_mid : |(chartModelBasis E).repr Y j| * |Γijk| ≤
          (‖L_j‖ * ‖Y‖) * |Γijk| :=
        mul_le_mul_of_nonneg_right h_repr_bound h_abs_Γ_nn
      have h_end : (‖L_j‖ * ‖Y‖) * |Γijk| ≤ (‖L_j‖ * ‖Y‖) * C_Γ :=
        mul_le_mul_of_nonneg_left hCΓ hpos
      linarith
    have hΓ_nn : 0 ≤ C_Γ := hCΓ_nn
    have h_step : (‖L_j‖ * ‖Y‖) * C_Γ ≤
        (modelBasisCoordSup (E := E) * ‖Y‖) * C_Γ := by
      have h_left : ‖L_j‖ * ‖Y‖ ≤ modelBasisCoordSup (E := E) * ‖Y‖ :=
        mul_le_mul_of_nonneg_right h_Lj_le h_Y_nn
      exact mul_le_mul_of_nonneg_right h_left hΓ_nn
    have h_eq : (modelBasisCoordSup (E := E) * ‖Y‖) * C_Γ =
        modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ := by ring
    linarith
  have h_ek_le : ‖(chartModelBasis E) k‖ ≤ modelBasisVecSup (E := E) :=
    norm_basis_le_modelBasisVecSup (E := E) k
  have h_ek_nn : 0 ≤ ‖(chartModelBasis E) k‖ := norm_nonneg _
  have h_Li_le : ‖L_i‖ ≤ modelBasisCoordSup (E := E) :=
    norm_coord_le_modelBasisCoordSup (E := E) i
  have h_Li_nn : 0 ≤ ‖L_i‖ := norm_nonneg _
  have h_J_nn : 0 ≤ ‖trivToE (I := I) α b‖ := norm_nonneg _
  have h_coord_nn : 0 ≤ modelBasisCoordSup (E := E) := modelBasisCoordSup_nonneg
  have h_vec_nn : 0 ≤ modelBasisVecSup (E := E) := modelBasisVecSup_nonneg
  set A : ℝ := ‖L_i.comp (trivToE (I := I) α b)‖
  set B : ℝ := |(chartModelBasis E).repr Y j * Γijk| * ‖(chartModelBasis E) k‖
  have hA_nn : 0 ≤ A := norm_nonneg _
  have hB_nn : 0 ≤ B := by
    refine mul_nonneg ?_ h_ek_nn
    exact abs_nonneg _
  have hA_le : A ≤ modelBasisCoordSup (E := E) * C_J := by
    refine hcomp_le.trans ?_
    have h_first : ‖L_i‖ * ‖trivToE (I := I) α b‖ ≤
        modelBasisCoordSup (E := E) * ‖trivToE (I := I) α b‖ :=
      mul_le_mul_of_nonneg_right h_Li_le h_J_nn
    have h_second :
        modelBasisCoordSup (E := E) * ‖trivToE (I := I) α b‖ ≤
          modelBasisCoordSup (E := E) * C_J :=
      mul_le_mul_of_nonneg_left h_triv_le h_coord_nn
    linarith
  have hB_le : B ≤ (modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
      modelBasisVecSup (E := E) := by
    have h_first :
        |(chartModelBasis E).repr Y j * Γijk| * ‖(chartModelBasis E) k‖ ≤
          (modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
            ‖(chartModelBasis E) k‖ :=
      mul_le_mul_of_nonneg_right h_scalar_bound h_ek_nn
    have h_second :
        (modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) * ‖(chartModelBasis E) k‖ ≤
          (modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
            modelBasisVecSup (E := E) := by
      have h_left_nn : 0 ≤ modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ := by positivity
      exact mul_le_mul_of_nonneg_left h_ek_le h_left_nn
    linarith
  have hRHS_nn : 0 ≤ (modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
      modelBasisVecSup (E := E) := by positivity
  have h_AB_le :
      A * B ≤ (modelBasisCoordSup (E := E) * C_J) *
        ((modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
          modelBasisVecSup (E := E)) := by
    have h_lhs : A * B ≤ (modelBasisCoordSup (E := E) * C_J) * B :=
      mul_le_mul_of_nonneg_right hA_le hB_nn
    have h_lhs2_nn : 0 ≤ modelBasisCoordSup (E := E) * C_J := by positivity
    have h_rhs : (modelBasisCoordSup (E := E) * C_J) * B ≤
        (modelBasisCoordSup (E := E) * C_J) *
          ((modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
            modelBasisVecSup (E := E)) :=
      mul_le_mul_of_nonneg_left hB_le h_lhs2_nn
    linarith
  have h_rearrange :
      (modelBasisCoordSup (E := E) * C_J) *
        ((modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
          modelBasisVecSup (E := E)) =
      modelBasisCoordSup (E := E) * C_J *
        (modelBasisCoordSup (E := E) * ‖Y‖ * C_Γ) *
        modelBasisVecSup (E := E) := by ring
  linarith

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem christoffelCorrection_opNorm_isBounded_on_pouTsupport_unconditional
    [I.Boundaryless] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ Y : E, ‖christoffelCorrection (I := I) g α b Y‖ ≤ C * ‖Y‖ := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  set K : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_base : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  obtain ⟨C_J, hCJ_nn, hCJ_bound⟩ :=
    chartTriv_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g α hK_compact hK_base
  obtain ⟨C_Γ, hCΓ_nn, hCΓ_bound⟩ :=
    chartChristoffel_bdd_on_pou_tsupport (I := I) (M := M) g α
  set n : ℕ := Module.finrank ℝ E with hn_def
  set C_coord : ℝ := modelBasisCoordSup (E := E) with hC_coord_def
  set C_vec : ℝ := modelBasisVecSup (E := E) with hC_vec_def
  set C : ℝ := (n : ℝ) ^ 3 *
    (C_coord * C_J * (C_coord * C_Γ) * C_vec) with hC_def
  have hC_coord_nn : 0 ≤ C_coord := modelBasisCoordSup_nonneg
  have hC_vec_nn : 0 ≤ C_vec := modelBasisVecSup_nonneg
  have hC_nn : 0 ≤ C := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    have hrest_nn : 0 ≤ C_coord * C_J * (C_coord * C_Γ) * C_vec := by positivity
    exact mul_nonneg this hrest_nn
  refine ⟨C, hC_nn, ?_⟩
  intro b hb Y
  have hb_chartJ :
      ‖(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b‖ ≤ C_J :=
    hCJ_bound b hb
  have hb_extImg : extChartAt I α b ∈
      (extChartAt I α) ''
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
    exact ⟨b, hb, rfl⟩
  have hb_Γ : ∀ i j k : Fin (Module.finrank ℝ E),
      |chartChristoffel (I := I) g α i j k (extChartAt I α b)| ≤ C_Γ := by
    intro i j k
    exact hCΓ_bound (extChartAt I α b) hb_extImg i j k
  set D : ℝ := C_coord * C_J * (C_coord * ‖Y‖ * C_Γ) * C_vec with hD_def
  have hD_nn : 0 ≤ D := by
    have : 0 ≤ C_coord * ‖Y‖ * C_Γ := by positivity
    have : 0 ≤ C_coord * C_J := by positivity
    positivity
  have h_per : ∀ i j k : Fin (Module.finrank ℝ E),
      ‖(((chartModelBasis E).coord i).toContinuousLinearMap.comp
            (trivToE (I := I) α b)).smulRight
          (((chartModelBasis E).repr Y j *
              chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
            (chartModelBasis E) k)‖ ≤ D := by
    intro i j k
    exact christoffelCorrection_summand_opNorm_le_unconditional (I := I)
      g α b Y i j k C_J hb_chartJ hCJ_nn C_Γ (hb_Γ i j k) hCΓ_nn
  unfold christoffelCorrection
  have h_outer_norm :
      ‖∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).coord i).toContinuousLinearMap.comp
                  (trivToE (I := I) α b)).smulRight
                (((chartModelBasis E).repr Y j *
                    chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
                  (chartModelBasis E) k)‖ ≤
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E), D := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact h_per i j k
  have h_sum_const :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), D = (n : ℝ) ^ 3 * D := by
    have h_inner :
        ∀ i j : Fin (Module.finrank ℝ E),
          (∑ _k : Fin (Module.finrank ℝ E), D) = (n : ℝ) * D := by
      intro i j
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp [nsmul_eq_mul, hn_def]
    have h_middle :
        ∀ i : Fin (Module.finrank ℝ E),
          (∑ _j : Fin (Module.finrank ℝ E),
            (∑ _k : Fin (Module.finrank ℝ E), D)) = (n : ℝ) ^ 2 * D := by
      intro i
      calc (∑ _j : Fin (Module.finrank ℝ E),
              (∑ _k : Fin (Module.finrank ℝ E), D))
            = ∑ _j : Fin (Module.finrank ℝ E), (n : ℝ) * D := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              exact h_inner i j
          _ = (n : ℝ) * ((n : ℝ) * D) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp [nsmul_eq_mul, hn_def]
          _ = (n : ℝ) ^ 2 * D := by ring
    calc (∑ i : Fin (Module.finrank ℝ E),
            (∑ _j : Fin (Module.finrank ℝ E),
              (∑ _k : Fin (Module.finrank ℝ E), D)))
          = ∑ i : Fin (Module.finrank ℝ E), (n : ℝ) ^ 2 * D := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact h_middle i
        _ = (n : ℝ) * ((n : ℝ) ^ 2 * D) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul, hn_def]
        _ = (n : ℝ) ^ 3 * D := by ring
  rw [h_sum_const] at h_outer_norm
  have h_C_eq : (n : ℝ) ^ 3 * D = C * ‖Y‖ := by
    rw [hC_def, hD_def]
    ring
  rw [h_C_eq] at h_outer_norm
  exact h_outer_norm

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem chartLeviCivitaParallelCLM_general_X_opNorm_isBounded_on_pouTsupport_unconditional
    [I.Boundaryless] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
      g.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨cg.toRiemannianMetric⟩
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ X : Π b' : M, TangentSpace I b',
          ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ ≤ C * ‖X b‖ := by
  classical
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  set K : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  have hK_base : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  obtain ⟨C_J, hCJ_nn, hCJ_bound⟩ :=
    chartTriv_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g α hK_compact hK_base
  obtain ⟨C_Jinv, hCJinv_nn, hCJinv_bound⟩ :=
    chartTrivInv_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g α hK_compact hK_base
  obtain ⟨C_χ, hCχ_nn, hCχ_bound⟩ :=
    christoffelCorrection_opNorm_isBounded_on_pouTsupport_unconditional
      (I := I) (M := M) g α
  set C : ℝ := C_Jinv * C_χ * C_J with hC_def
  have hC_nn : 0 ≤ C := by positivity
  refine ⟨C, hC_nn, ?_⟩
  intro b hb X
  unfold chartLeviCivitaParallelCLM
  set Y : E := trivToE (I := I) α b (X b) with hY_def
  have h_comp_le :
      ‖(trivFromE (I := I) α b).comp
          (christoffelCorrection (I := I) g α b Y)‖ ≤
        ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h_trivFromE_le : ‖trivFromE (I := I) α b‖ ≤ C_Jinv := hCJinv_bound b hb
  have h_trivFromE_nn : 0 ≤ ‖trivFromE (I := I) α b‖ := norm_nonneg _
  have h_Y_le_triv : ‖Y‖ ≤ ‖trivToE (I := I) α b‖ * ‖X b‖ := by
    rw [hY_def]
    exact (trivToE (I := I) α b).le_opNorm (X b)
  have h_Xb_nn : 0 ≤ ‖X b‖ := norm_nonneg _
  have h_Y_le : ‖Y‖ ≤ C_J * ‖X b‖ := by
    refine h_Y_le_triv.trans ?_
    exact mul_le_mul_of_nonneg_right (hCJ_bound b hb) h_Xb_nn
  have h_χ_Y : ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * ‖Y‖ :=
    hCχ_bound (b := b) hb Y
  have h_Y_nn : 0 ≤ ‖Y‖ := norm_nonneg _
  have h_χ_le : ‖christoffelCorrection (I := I) g α b Y‖ ≤ C_χ * (C_J * ‖X b‖) :=
    h_χ_Y.trans (mul_le_mul_of_nonneg_left h_Y_le hCχ_nn)
  have h_χ_nn : 0 ≤ ‖christoffelCorrection (I := I) g α b Y‖ := norm_nonneg _
  have h_step1 :
      ‖trivFromE (I := I) α b‖ *
          ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ :=
    mul_le_mul_of_nonneg_right h_trivFromE_le h_χ_nn
  have h_step2 :
      C_Jinv * ‖christoffelCorrection (I := I) g α b Y‖ ≤
        C_Jinv * (C_χ * (C_J * ‖X b‖)) :=
    mul_le_mul_of_nonneg_left h_χ_le hCJinv_nn
  have h_rearrange :
      C_Jinv * (C_χ * (C_J * ‖X b‖)) = C * ‖X b‖ := by
    rw [hC_def]; ring
  linarith

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock

end
