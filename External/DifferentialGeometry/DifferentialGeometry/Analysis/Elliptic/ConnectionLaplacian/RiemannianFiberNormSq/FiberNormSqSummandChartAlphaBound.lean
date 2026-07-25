import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.ChartGramMatrixQuadFormUpperBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartGramMatrix_pou_uniform_entry_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ i j : Fin (Module.finrank ℝ E),
          |chartGramMatrix (I := I) g α b i j| ≤ C := by
  classical
  set Kα : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hKα_def
  have hKα_compact : IsCompact Kα :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hKα_sub_base :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  have hKα_sub_src : Kα ⊆ (chartAt H α).source := by
    have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
        = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
    rw [← h_set_eq]
    exact hKα_sub_base
  have hchoice : ∀ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      ∃ K : ℝ, 0 < K ∧
        ∀ b ∈ Kα, |chartGramMatrix (I := I) g α b ij.1 ij.2| ≤ K := by
    intro ij
    exact chartGramMatrix_entry_isBounded_on_compact (I := I) (M := M)
      g α ij.1 ij.2 hKα_compact hKα_sub_src
  choose K hK_pos hK_le using hchoice
  set V : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :=
    Finset.univ with hV_def
  set C : ℝ := ∑ ij ∈ V, K ij with hC_def
  have hC_nonneg : 0 ≤ C := by
    refine Finset.sum_nonneg ?_
    intro ij _
    exact le_of_lt (hK_pos ij)
  refine ⟨C, hC_nonneg, ?_⟩
  intro b hb i j
  have hK_ij_le_C : K (i, j) ≤ C := by
    refine Finset.single_le_sum (s := V) (f := fun ij => K ij) ?_
      (Finset.mem_univ (i, j))
    intro ij _
    exact le_of_lt (hK_pos ij)
  have h_entry : |chartGramMatrix (I := I) g α b i j| ≤ K (i, j) :=
    hK_le (i, j) b hb
  linarith

omit [NeZero (Module.finrank ℝ E)] in
private lemma trivAt_cLMA_chartBasisVecFiber
    (α : M) (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        (chartBasisVecFiber (I := I) α i b)
      = (chartModelBasis E) i := by
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with hT_def
  have heq : chartBasisVecFiber (I := I) α i b = T.symm b ((chartModelBasis E) i) :=
    rfl
  rw [heq]
  have hSymmL : T.symm b ((chartModelBasis E) i)
      = T.symmL ℝ b ((chartModelBasis E) i) := by
    rw [Trivialization.symmL_apply]
  rw [hSymmL, Trivialization.continuousLinearMapAt_symmL T (b := b) hb]

omit [NeZero (Module.finrank ℝ E)] in
private lemma omega_eIdx_eq_sum_gram_compCLM
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r : ℕ) (Idx : Fin r → Fin (Module.finrank ℝ E)) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ from
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k : Fin r =>
          g.inner b (chartBasisVecFiber (I := I) α (Idx k) b)))) =
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) •
          ((dualCoordinateProductMultilinearMap (E := E) r Idx').compContinuousLinearMap
            (fun _ : Fin r =>
              (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b)) := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with hT_def
  set cLMA : TangentSpace I b →L[ℝ] E := T.continuousLinearMapAt ℝ b with hcLMA_def
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  have h_inner_expand : ∀ k : Fin r,
      g.inner b (chartBasisVecFiber (I := I) α (Idx k) b) (v k) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α b (Idx k) l *
            ((chartModelBasis E).coord l) (cLMA (v k)) := by
    intro k
    set c : Fin (Module.finrank ℝ E) → ℝ :=
      fun l => ((chartModelBasis E).coord l) (cLMA (v k)) with hc_def
    have h_v_expand : v k =
        ∑ l : Fin (Module.finrank ℝ E),
          c l • chartBasisVecFiber (I := I) α l b := by
      have h_round : T.symmL ℝ b (cLMA (v k)) = v k :=
        T.symmL_continuousLinearMapAt (R := ℝ) hb (v k)
      have h_basis_expand :
          cLMA (v k) =
            ∑ l : Fin (Module.finrank ℝ E),
              c l • chartModelBasis E l := by
        have hsum := (chartModelBasis E).sum_repr (cLMA (v k))
        conv_lhs => rw [← hsum]
        refine Finset.sum_congr rfl ?_
        intro l _
        have h_c_eq : c l = ((chartModelBasis E).repr (cLMA (v k))) l := by
          change ((chartModelBasis E).coord l) (cLMA (v k)) =
            ((chartModelBasis E).repr (cLMA (v k))) l
          rw [Module.Basis.coord_apply]
        rw [h_c_eq]
      have : T.symmL ℝ b (cLMA (v k)) =
          ∑ l : Fin (Module.finrank ℝ E),
            c l • T.symmL ℝ b (chartModelBasis E l) := by
        rw [h_basis_expand, map_sum]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [map_smul]
      have h_basis_vec : ∀ l : Fin (Module.finrank ℝ E),
          T.symmL ℝ b (chartModelBasis E l) = chartBasisVecFiber (I := I) α l b := by
        intro l
        rw [Trivialization.symmL_apply]
        rfl
      rw [← h_round, this]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [h_basis_vec l]
    calc g.inner b (chartBasisVecFiber (I := I) α (Idx k) b) (v k)
        = g.inner b (chartBasisVecFiber (I := I) α (Idx k) b)
            (∑ l : Fin (Module.finrank ℝ E),
              c l • chartBasisVecFiber (I := I) α l b) := by
          rw [h_v_expand]
      _ = ∑ l : Fin (Module.finrank ℝ E),
            c l * g.inner b (chartBasisVecFiber (I := I) α (Idx k) b)
              (chartBasisVecFiber (I := I) α l b) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro l _
          rw [map_smul, smul_eq_mul]
      _ = ∑ l : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g α b (Idx k) l * c l := by
          refine Finset.sum_congr rfl ?_
          intro l _
          rw [show g.inner b (chartBasisVecFiber (I := I) α (Idx k) b)
                (chartBasisVecFiber (I := I) α l b) =
              chartGramMatrix (I := I) g α b (Idx k) l from
            (chartGramMatrix_apply g α b (Idx k) l).symm]
          ring
  trans (∏ k : Fin r,
        ∑ l : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α b (Idx k) l *
            ((chartModelBasis E).coord l) (cLMA (v k)))
  · exact Finset.prod_congr rfl (fun k _ => h_inner_expand k)
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  refine Eq.trans ?_ (ContinuousMultilinearMap.sum_apply _ v).symm
  refine Finset.sum_congr rfl ?_
  intro Idx' _
  change ∏ i, chartGramMatrix (I := I) g α b (Idx i) (Idx' i) *
      ((chartModelBasis E).coord (Idx' i)) (cLMA (v i)) =
    (∏ k, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) •
      ((dualCoordinateProductMultilinearMap (E := E) r Idx').compContinuousLinearMap
        (fun _ : Fin r => cLMA)) v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    dualCovariantCMM_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]

omit [NeZero (Module.finrank ℝ E)] in
private lemma section_compCLM_eval_eq_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Idx' : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ((S.toSection b :
        Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        ((dualCoordinateProductMultilinearMap (E := E) r Idx').compContinuousLinearMap
          (fun _ : Fin r =>
            (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b) :
          Tensor0SSpace r I b) :
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (fun k : Fin s => chartBasisVecFiber (I := I) α (Jdx k) b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with hT_def
  set eRS := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with heRS_def
  set er := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with her_def
  set es := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with hes_def
  have hb_r : b ∈ er.baseSet := hb
  have hb_s : b ∈ es.baseSet := hb
  have hb_RS : b ∈ eRS.baseSet := ⟨hb_r, hb_s⟩
  have hA :
      ((er.symmL ℝ b (dualCoordinateProductMultilinearMap (E := E) r Idx')) :
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
      (dualCoordinateProductMultilinearMap (E := E) r Idx').compContinuousLinearMap
        (fun _ : Fin r => T.continuousLinearMapAt ℝ b) :=
    Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (s := r)
      α b hb_r (dualCoordinateProductMultilinearMap (E := E) r Idx')
  have hA' :
      ((dualCoordinateProductMultilinearMap (E := E) r Idx').compContinuousLinearMap
        (fun _ : Fin r => T.continuousLinearMapAt ℝ b) :
        Tensor0SSpace r I b) =
      (er.symmL ℝ b (dualCoordinateProductMultilinearMap (E := E) r Idx') :
        Tensor0SSpace r I b) := hA.symm
  rw [hA']
  set X : Tensor0SSpace s I b :=
    (S.toSection b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
      (er.symmL ℝ b (dualCoordinateProductMultilinearMap (E := E) r Idx')) with hX_def
  have hForward :
      (eRS.continuousLinearMapAt ℝ b (S.toSection b) :
        Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (dualCoordinateProductMultilinearMap (E := E) r Idx') =
        es.continuousLinearMapAt ℝ b X := by
    have h_coe := eRS.coe_linearMapAt_of_mem (R := ℝ) hb_RS
    have h := congrFun h_coe (S.toSection b)
    have h_cLMA :
        (eRS.continuousLinearMapAt ℝ b (S.toSection b) :
          Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) =
          (eRS ⟨b, S.toSection b⟩).2 := by
      simpa [Bundle.Trivialization.continuousLinearMapAt_apply] using h
    rw [h_cLMA]
    rfl
  have h_round :
      es.symmL ℝ b (es.continuousLinearMapAt ℝ b X) = X :=
    Bundle.Trivialization.symmL_continuousLinearMapAt es hb_s X
  have h_symmL_s :=
    Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
      (𝕜 := ℝ) (F := E) (E := (TangentSpace I : M → Type _)) (s := s)
      α b hb_s (es.continuousLinearMapAt ℝ b X)
  have h_X_eval :
      (X : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
          (fun k : Fin s => chartBasisVecFiber (I := I) α (Jdx k) b) =
        (es.continuousLinearMapAt ℝ b X)
          (fun k : Fin s =>
            T.continuousLinearMapAt ℝ b
              (chartBasisVecFiber (I := I) α (Jdx k) b)) := by
    conv_lhs => rw [← h_round]
    rw [show (es.symmL ℝ b (es.continuousLinearMapAt ℝ b X) :
            ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
          (es.continuousLinearMapAt ℝ b X).compContinuousLinearMap
            (fun _ : Fin s => T.continuousLinearMapAt ℝ b) from h_symmL_s]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have h_basis_subst :
      (fun k : Fin s => T.continuousLinearMapAt ℝ b
        (chartBasisVecFiber (I := I) α (Jdx k) b)) =
        (fun k : Fin s => chartModelBasis E (Jdx k)) := by
    funext k
    exact trivAt_cLMA_chartBasisVecFiber (I := I) α (Jdx k) hb
  rw [h_X_eval, h_basis_subst]
  change (es.continuousLinearMapAt ℝ b X)
          (fun k : Fin s => chartModelBasis E (Jdx k)) =
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b
  have h_def : tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b =
      ((tensorTrivProj (I := I) (M := M) g r s S α b :
        Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (dualCoordinateProductMultilinearMap (E := E) r Idx'))
        (fun k : Fin s => chartModelBasis E (Jdx k)) := rfl
  rw [h_def]
  unfold tensorTrivProj
  rw [hForward]

omit [NeZero (Module.finrank ℝ E)] in
private lemma section_omega_eIdx_apply_eq_sum_gram_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (((S.toSection b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        (((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
          (fun k : Fin r =>
            g.inner b (chartBasisVecFiber (I := I) α (Idx k) b))) :
            Tensor0SSpace r I b)) :
            ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
        (fun k : Fin s => chartBasisVecFiber (I := I) α (Jdx k) b) =
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with hT_def
  have h_omega_eq :=
    omega_eIdx_eq_sum_gram_compCLM (I := I) (M := M) g α hb r Idx
  have h_omega_TSp :
      (((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k : Fin r =>
          g.inner b (chartBasisVecFiber (I := I) α (Idx k) b))) :
            Tensor0SSpace r I b) =
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) •
            (((dualCoordinateProductMultilinearMap (E := E) r Idx').compContinuousLinearMap
              (fun _ : Fin r => T.continuousLinearMapAt ℝ b)) :
                Tensor0SSpace r I b) := h_omega_eq
  rw [h_omega_TSp]
  rw [map_sum]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro Idx' _
  rw [map_smul]
  rw [ContinuousMultilinearMap.smul_apply]
  rw [smul_eq_mul]
  rw [section_compCLM_eval_eq_tensorChartComponentRaw (I := I) (M := M)
    g r s S α hb Idx' Jdx]

private lemma sum_prod_gram_sq_le_uniform_const
    {r : ℕ} {n : ℕ}
    (G : Fin n → Fin n → ℝ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hG : ∀ i j : Fin n, |G i j| ≤ C)
    (Idx : Fin r → Fin n) :
    ∑ Idx' : Fin r → Fin n,
        (∏ k : Fin r, G (Idx k) (Idx' k)) ^ 2 ≤
      (n : ℝ) ^ r * C ^ (2 * r) := by
  classical
  have h_per_Idx' : ∀ Idx' : Fin r → Fin n,
      (∏ k : Fin r, G (Idx k) (Idx' k)) ^ 2 ≤ C ^ (2 * r) := by
    intro Idx'
    have h_sq : (∏ k : Fin r, G (Idx k) (Idx' k)) ^ 2 =
        ∏ k : Fin r, G (Idx k) (Idx' k) ^ 2 := by
      rw [← Finset.prod_pow]
    rw [h_sq]
    have h_each : ∀ k : Fin r,
        G (Idx k) (Idx' k) ^ 2 ≤ C ^ 2 := by
      intro k
      have h_abs : |G (Idx k) (Idx' k)| ≤ C := hG (Idx k) (Idx' k)
      have h_abs2 : G (Idx k) (Idx' k) ^ 2 = |G (Idx k) (Idx' k)| ^ 2 := by
        rw [sq_abs]
      rw [h_abs2]
      exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    have h_prod_le :
        ∏ k : Fin r, G (Idx k) (Idx' k) ^ 2 ≤ ∏ _k : Fin r, C ^ 2 := by
      refine Finset.prod_le_prod ?_ ?_
      · intro k _
        exact sq_nonneg _
      · intro k _
        exact h_each k
    have h_const_prod : (∏ _k : Fin r, (C ^ 2 : ℝ)) = (C ^ 2) ^ r := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h_const_prod] at h_prod_le
    have hC2r : (C ^ 2) ^ r = C ^ (2 * r) := by
      rw [← pow_mul, mul_comm]
    rw [← hC2r]
    exact h_prod_le
  calc ∑ Idx' : Fin r → Fin n,
          (∏ k : Fin r, G (Idx k) (Idx' k)) ^ 2
      ≤ ∑ Idx' : Fin r → Fin n, C ^ (2 * r) := by
        refine Finset.sum_le_sum ?_
        intro Idx' _
        exact h_per_Idx' Idx'
    _ = ((Finset.univ : Finset (Fin r → Fin n)).card : ℝ) * C ^ (2 * r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n : ℝ) ^ r * C ^ (2 * r) := by
        rw [Finset.card_univ]
        congr 1
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        push_cast
        rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem fiberNormSqSummand_chartAlpha_le_raw_components_sq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s),
        ∀ {b : M},
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b)
            (Module.finrank ℝ E)
            (fun i : Fin (Module.finrank ℝ E) =>
              chartBasisVecFiber (I := I) α i b)
            Idx Jdx ≤
          C *
            (∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx' b) ^ 2) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨CG, hCG_nonneg, hCG_bound⟩ :=
    chartGramMatrix_pou_uniform_entry_bound (I := I) (M := M) g α
  set C : ℝ := (n : ℝ) ^ r * CG ^ (2 * r) with hC_def
  have hC_nonneg : 0 ≤ C := by
    refine mul_nonneg ?_ ?_
    · exact pow_nonneg (Nat.cast_nonneg n) r
    · exact pow_nonneg hCG_nonneg (2 * r)
  refine ⟨C, hC_nonneg, ?_⟩
  intro S b hb Idx Jdx
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsub :
        tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α
    exact hsub hb
  unfold fiberNormSqSummand
  have h_expand :=
    section_omega_eIdx_apply_eq_sum_gram_components (I := I) (M := M)
      g r s S α hb_base Idx Jdx
  rw [h_expand]
  have h_CS :
      (∑ Idx' : Fin r → Fin n,
        (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2 ≤
      (∑ Idx' : Fin r → Fin n,
        (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) ^ 2) *
      (∑ Idx' : Fin r → Fin n,
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ)
      (s := (Finset.univ : Finset (Fin r → Fin n)))
      (f := fun Idx' : Fin r → Fin n =>
        ∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k))
      (g := fun Idx' : Fin r → Fin n =>
        tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b)
  have h_uniform :
      ∑ Idx' : Fin r → Fin n,
          (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) ^ 2 ≤
        (n : ℝ) ^ r * CG ^ (2 * r) :=
    sum_prod_gram_sq_le_uniform_const
      (n := n) (r := r)
      (G := fun i j : Fin n => chartGramMatrix (I := I) g α b i j)
      hCG_nonneg (fun i j => hCG_bound hb i j) Idx
  have h_sum_Jdx_nn :
      0 ≤ ∑ Idx' : Fin r → Fin n,
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_step :
      (∑ Idx' : Fin r → Fin n,
        (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2 ≤
      C * (∑ Idx' : Fin r → Fin n,
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2) := by
    calc (∑ Idx' : Fin r → Fin n,
          (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) *
            tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2
        ≤ (∑ Idx' : Fin r → Fin n,
            (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) ^ 2) *
          (∑ Idx' : Fin r → Fin n,
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2) :=
          h_CS
      _ ≤ ((n : ℝ) ^ r * CG ^ (2 * r)) *
          (∑ Idx' : Fin r → Fin n,
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2) := by
          exact mul_le_mul_of_nonneg_right h_uniform h_sum_Jdx_nn
      _ = C * (∑ Idx' : Fin r → Fin n,
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2) := by
          rw [hC_def]
  have h_single_Jdx_le_full :
      (∑ Idx' : Fin r → Fin n,
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2) ≤
      (∑ Idx' : Fin r → Fin n,
        ∑ Jdx' : Fin s → Fin n,
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx' b) ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro Idx' _
    refine Finset.single_le_sum (s := (Finset.univ : Finset (Fin s → Fin n)))
      (f := fun Jdx' : Fin s → Fin n =>
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx' b) ^ 2) ?_
      (Finset.mem_univ Jdx)
    intro Jdx' _
    exact sq_nonneg _
  have h_final :
      (∑ Idx' : Fin r → Fin n,
        (∏ k : Fin r, chartGramMatrix (I := I) g α b (Idx k) (Idx' k)) *
          tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx b) ^ 2 ≤
      C * (∑ Idx' : Fin r → Fin n,
        ∑ Jdx' : Fin s → Fin n,
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx' b) ^ 2) :=
    h_step.trans (mul_le_mul_of_nonneg_left h_single_Jdx_le_full hC_nonneg)
  exact h_final

end Connection
end Integral
end DifferentialGeometry

end
