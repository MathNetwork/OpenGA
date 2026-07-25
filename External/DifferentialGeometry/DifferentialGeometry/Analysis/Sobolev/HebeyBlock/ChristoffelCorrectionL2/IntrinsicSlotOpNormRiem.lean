import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCorrectionModelNormBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartKernel


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorRSTriv_baseSet_eq_chartSource (r s : ℕ) (α : M) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
  classical
  change (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet = _
  have h_r : (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet =
        (trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_s : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet =
        (trivializationAt E (TangentSpace I) α).baseSet := rfl
  rw [h_r, h_s, Set.inter_self,
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotConjFactor_self_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (w : E) :
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b X).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) w =
      christoffelCorrection (I := I) g α b
        (trivToE (I := I) α b (X b))
        (trivFromE (I := I) α b w) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  rw [ContinuousLinearMap.comp_apply]
  change chartTrivializationLinearMap (I := I) (M := M) α b
      ((chartLeviCivitaParallelCLM (I := I) g α b X)
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b w)) = _
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X
    (chartTrivializationLinearMapSymm (I := I) (M := M) α b w)]
  change trivToE (I := I) α b
      (trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b))
          (trivFromE (I := I) α b w))) = _
  rw [trivToE_trivFromE (I := I) α hb_base]

private lemma slotConjFactor_basis_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)),
          ‖(chartTrivializationLinearMap (I := I) (M := M) α b).comp
              ((chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)).comp
                (chartTrivializationLinearMapSymm (I := I) (M := M) α b))‖ ≤ C := by
  classical
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    christoffelCorrection_norm_le_on_pouTsupport (I := I) (M := M) g α
  set Cvec : ℝ :=
    (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
      (fun k => ‖(chartModelBasis E) k‖) with hCvec_def
  have hCvec_nn : 0 ≤ Cvec := by
    rw [hCvec_def]
    obtain ⟨k₀, hk₀⟩ :=
      (Finset.univ_nonempty_iff.mpr
        ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩ : Fin (Module.finrank ℝ E))⟩)
    exact le_trans (norm_nonneg _)
      (Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) hk₀)
  refine ⟨Cχ * Cvec, mul_nonneg hCχ_nn hCvec_nn, ?_⟩
  intro b hb k
  have hb_src : b ∈ (chartAt H α).source := by
    have := chartAtlasPOU_isSubordinate (I := I) (M := M) α hb
    exact this
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb_src
  have hX_triv :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α k b) =
        (chartModelBasis E) k := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b ((chartModelBasis E) k)) = _
    exact trivToE_trivFromE (I := I) α hb_base ((chartModelBasis E) k)
  have h_basis_le : ‖(chartModelBasis E) k‖ ≤ Cvec := by
    rw [hCvec_def]
    exact Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) (Finset.mem_univ k)
  have hpt : ∀ w : E,
      ‖(chartTrivializationLinearMap (I := I) (M := M) α b).comp
          ((chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α k)).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) w‖ ≤ Cχ * Cvec * ‖w‖ := by
    intro w
    rw [slotConjFactor_self_apply (I := I) (M := M) g α
      (chartBasisVecFiber (I := I) α k) hb_src w, hX_triv]
    have hround :
        trivToE (I := I) α b (trivFromE (I := I) α b w) = w :=
      trivToE_trivFromE (I := I) α hb_base w
    have hbound := hCχ_bound (b := b) hb ((chartModelBasis E) k)
      (trivFromE (I := I) α b w)
    rw [hround] at hbound
    calc ‖christoffelCorrection (I := I) g α b ((chartModelBasis E) k)
            (trivFromE (I := I) α b w)‖
        ≤ Cχ * ‖(chartModelBasis E) k‖ * ‖w‖ := hbound
      _ ≤ Cχ * Cvec * ‖w‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_basis_le hCχ_nn) (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hCχ_nn hCvec_nn) hpt

private lemma slotInputConjCLM_prod_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin r),
          (∏ j : Fin r,
            ‖slotInputConjCLM (I := I) g r α
              (chartBasisVecFiber (I := I) α k) i b j‖) ≤ C := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    slotConjFactor_basis_norm_le_on_pouTsupport (I := I) (M := M) g α
  refine ⟨(max C₀ 1) ^ r,
    pow_nonneg (le_trans zero_le_one (le_max_right _ _)) r, ?_⟩
  intro b hb k i
  have h_factor_le : ∀ j : Fin r,
      ‖slotInputConjCLM (I := I) g r α
        (chartBasisVecFiber (I := I) α k) i b j‖ ≤ max C₀ 1 := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [slotInputConjCLM_self]
      exact le_trans (hC₀_bound hb k) (le_max_left _ _)
    · rw [slotInputConjCLM_other (I := I) g r α
        (chartBasisVecFiber (I := I) α k) i b hji]
      exact le_trans ContinuousLinearMap.norm_id_le (le_max_right _ _)
  calc (∏ j : Fin r,
        ‖slotInputConjCLM (I := I) g r α
          (chartBasisVecFiber (I := I) α k) i b j‖)
      ≤ ∏ _j : Fin r, max C₀ 1 :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => h_factor_le j)
    _ = (max C₀ 1) ^ r := by rw [Finset.prod_const]; simp

private lemma slotOutputConjCLM_prod_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (l : Fin s),
          (∏ j : Fin s,
            ‖slotOutputConjCLM (I := I) g s α
              (chartBasisVecFiber (I := I) α k) l b j‖) ≤ C := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    slotConjFactor_basis_norm_le_on_pouTsupport (I := I) (M := M) g α
  refine ⟨(max C₀ 1) ^ s,
    pow_nonneg (le_trans zero_le_one (le_max_right _ _)) s, ?_⟩
  intro b hb k l
  have h_factor_le : ∀ j : Fin s,
      ‖slotOutputConjCLM (I := I) g s α
        (chartBasisVecFiber (I := I) α k) l b j‖ ≤ max C₀ 1 := by
    intro j
    by_cases hjl : j = l
    · subst hjl
      rw [slotOutputConjCLM_self]
      exact le_trans (hC₀_bound hb k) (le_max_left _ _)
    · rw [slotOutputConjCLM_other (I := I) g s α
        (chartBasisVecFiber (I := I) α k) l b hjl]
      exact le_trans ContinuousLinearMap.norm_id_le (le_max_right _ _)
  calc (∏ j : Fin s,
        ‖slotOutputConjCLM (I := I) g s α
          (chartBasisVecFiber (I := I) α k) l b j‖)
      ≤ ∏ _j : Fin s, max C₀ 1 :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => h_factor_le j)
    _ = (max C₀ 1) ^ s := by rw [Finset.prod_const]; simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma inputSlotChartKernel_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b') (i : Fin r) (b : M)
    (S : TensorRSModel r s ℝ E) :
    ‖inputSlotChartKernel (I := I) g r s α X i b S‖ ≤
      (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) * ‖S‖ := by
  classical
  rw [inputSlotChartKernel_apply]
  calc ‖S.comp (inputSlotPrecompCLM (I := I) g r α X i b)‖
      ≤ ‖S‖ * ‖inputSlotPrecompCLM (I := I) g r α X i b‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖S‖ * (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        unfold inputSlotPrecompCLM
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
          (𝕜 := ℝ) (E := fun _ : Fin r => E) ℝ
          (slotInputConjCLM (I := I) g r α X i b)
    _ = (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) * ‖S‖ := by
        ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma outputSlotChartKernel_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (S : TensorRSModel r s ℝ E) :
    ‖outputSlotChartKernel (I := I) g r s α X l b S‖ ≤
      (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α X l b j‖) * ‖S‖ := by
  classical
  rw [outputSlotChartKernel_apply]
  calc ‖(outputSlotPostcompCLM (I := I) g s α X l b).comp S‖
      ≤ ‖outputSlotPostcompCLM (I := I) g s α X l b‖ * ‖S‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α X l b j‖) * ‖S‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        unfold outputSlotPostcompCLM
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
          (𝕜 := ℝ) (E := fun _ : Fin s => E) ℝ
          (slotOutputConjCLM (I := I) g s α X l b)

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin r),
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α k) b i‖ ≤
            M_F * ‖T b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hK_cpt : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro x hx; exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
  obtain ⟨Cto, hCto_pos, hCto_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cfrom, hCfrom_pos, hCfrom_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cprod, hCprod_nn, hCprod_bound⟩ :=
    slotInputConjCLM_prod_norm_le_on_pouTsupport (I := I) (M := M) g r α
  refine ⟨Cfrom * Cprod * Cto,
    mul_nonneg (mul_nonneg (le_of_lt hCfrom_pos) hCprod_nn) (le_of_lt hCto_pos), ?_⟩
  intro T b hb k i
  set Y : TensorRSSpace r s I b :=
    chartTensorRSInputSlotCorrection (I := I) r s g α T
      (chartBasisVecFiber (I := I) α k) b i with hY_def
  have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRSTriv_baseSet_eq_chartSource (I := I) (M := M) r s α]
    exact hK_sub hb
  have h_roundtrip :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y) = Y :=
    Trivialization.symmL_continuousLinearMapAt _ hb_base Y
  have h_from :
      ‖Y‖ ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := by
    have := hCfrom_bound b hb
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y)
    rwa [h_roundtrip] at this
  have h_fact :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y =
        (inputSlotChartKernel (I := I) g r s α
            (chartBasisVecFiber (I := I) α k) i b)
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T b)) :=
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α T (chartBasisVecFiber (I := I) α k)
      (hK_sub hb) i
  have h_kernel :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ ≤
        Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ := by
    rw [h_fact]
    refine le_trans (inputSlotChartKernel_apply_norm_le (I := I) (M := M)
      g r s α (chartBasisVecFiber (I := I) α k) i b _) ?_
    exact mul_le_mul_of_nonneg_right (hCprod_bound hb k i) (norm_nonneg _)
  have h_to :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ ≤
        Cto * ‖T b‖ :=
    hCto_bound b hb (T b)
  have hCto_nn : 0 ≤ Cto := le_of_lt hCto_pos
  have hCfrom_nn : 0 ≤ Cfrom := le_of_lt hCfrom_pos
  calc ‖Y‖
      ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := h_from
    _ ≤ Cfrom * (Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖) :=
        mul_le_mul_of_nonneg_left h_kernel hCfrom_nn
    _ ≤ Cfrom * (Cprod * (Cto * ‖T b‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_to hCprod_nn) hCfrom_nn
    _ = Cfrom * Cprod * Cto * ‖T b‖ := by ring

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (l : Fin s),
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α k) b l‖ ≤
            M_F * ‖T b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hK_cpt : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro x hx; exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
  obtain ⟨Cto, hCto_pos, hCto_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cfrom, hCfrom_pos, hCfrom_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cprod, hCprod_nn, hCprod_bound⟩ :=
    slotOutputConjCLM_prod_norm_le_on_pouTsupport (I := I) (M := M) g s α
  refine ⟨Cfrom * Cprod * Cto,
    mul_nonneg (mul_nonneg (le_of_lt hCfrom_pos) hCprod_nn) (le_of_lt hCto_pos), ?_⟩
  intro T b hb k l
  set Y : TensorRSSpace r s I b :=
    chartTensorRSOutputSlotCorrection (I := I) r s g α T
      (chartBasisVecFiber (I := I) α k) b l with hY_def
  have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [tensorRSTriv_baseSet_eq_chartSource (I := I) (M := M) r s α]
    exact hK_sub hb
  have h_roundtrip :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y) = Y :=
    Trivialization.symmL_continuousLinearMapAt _ hb_base Y
  have h_from :
      ‖Y‖ ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := by
    have := hCfrom_bound b hb
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y)
    rwa [h_roundtrip] at this
  have h_fact :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y =
        (outputSlotChartKernel (I := I) g r s α
            (chartBasisVecFiber (I := I) α k) l b)
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T b)) :=
    chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α T (chartBasisVecFiber (I := I) α k)
      (hK_sub hb) l
  have h_kernel :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ ≤
        Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ := by
    rw [h_fact]
    refine le_trans (outputSlotChartKernel_apply_norm_le (I := I) (M := M)
      g r s α (chartBasisVecFiber (I := I) α k) l b _) ?_
    exact mul_le_mul_of_nonneg_right (hCprod_bound hb k l) (norm_nonneg _)
  have h_to :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ ≤
        Cto * ‖T b‖ :=
    hCto_bound b hb (T b)
  have hCto_nn : 0 ≤ Cto := le_of_lt hCto_pos
  have hCfrom_nn : 0 ≤ Cfrom := le_of_lt hCfrom_pos
  calc ‖Y‖
      ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := h_from
    _ ≤ Cfrom * (Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖) :=
        mul_le_mul_of_nonneg_left h_kernel hCfrom_nn
    _ ≤ Cfrom * (Cprod * (Cto * ‖T b‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_to hCprod_nn) hCfrom_nn
    _ = Cfrom * Cprod * Cto * ‖T b‖ := by ring

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
