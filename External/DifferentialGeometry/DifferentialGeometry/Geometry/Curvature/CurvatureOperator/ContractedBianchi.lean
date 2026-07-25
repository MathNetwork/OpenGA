import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Geometry.Curvature.Bochner.TensorWeitzenbockIdentity
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile

set_option linter.flexible false

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

section NablaRicci

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def nablaRicci (g : SmoothRiemannianMetric I M)
    (X V W : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  extDerivFun (I := I) (fun b => ricciTensor (I := I) g b (V b) (W b)) x (X x)
    - ricciTensor (I := I) g x ((LeviCivita (I := I) g).toFun V x (X x)) (W x)
    - ricciTensor (I := I) g x (V x) ((LeviCivita (I := I) g).toFun W x (X x))

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaRicci_def (g : SmoothRiemannianMetric I M)
    (X V W : Π b : M, TangentSpace I b) (x : M) :
    nablaRicci (I := I) g X V W x =
      extDerivFun (I := I) (fun b => ricciTensor (I := I) g b (V b) (W b)) x (X x)
        - ricciTensor (I := I) g x ((LeviCivita (I := I) g).toFun V x (X x)) (W x)
        - ricciTensor (I := I) g x (V x) ((LeviCivita (I := I) g).toFun W x (X x)) := rfl

end NablaRicci

section FrameExpansion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem orthonormal_frame_vector_expansion
    (g : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    u = ∑ i : Fin (Module.finrank ℝ E), g.inner x u (B i) • B i := by
  classical
  refine SmoothRiemannianMetric.eq_of_inner_eq g (fun ζ => ?_)
  rw [g_inner_eq_orthonormal_parseval_sum (I := I) g x u ζ B hB]
  rw [map_sum]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

end FrameExpansion

section ScalarCurv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def scalarCurv (g : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ricciTensor (I := I) g x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem symm_bilin_orthonormal_trace_invariant
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hTsymm : ∀ a b : TangentSpace I x, T a b = T b a)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (C i) (C j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E), T (C i) (C i) =
      ∑ i : Fin (Module.finrank ℝ E), T (B i) (B i) := by
  classical
  have hexpand : ∀ i, T (C i) (C i) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (g.inner x (C i) (B k) * g.inner x (C i) (B l)) * T (B k) (B l) := by
    intro i
    conv_lhs => rw [orthonormal_frame_vector_expansion (I := I) g x (C i) B hB]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [show (T (∑ l, g.inner x (C i) (B l) • B l)) (B k) =
        ∑ l, g.inner x (C i) (B l) • (T (B l)) (B k) from by
          rw [map_sum]
          simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul, smul_eq_mul,
            ContinuousLinearMap.smul_apply]]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [smul_eq_mul, hTsymm (B l) (B k)]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hexpand i)]
  rw [Finset.sum_comm]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        (g.inner x (C i) (B k) * g.inner x (C i) (B l)) * T (B k) (B l)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          g.inner x (B k) (C i) * g.inner x (C i) (B l)) * T (B k) (B l) from by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [g.symm x (B k) (C i)]]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          g.inner x (B k) (C i) * g.inner x (C i) (B l)) * T (B k) (B l)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        g.inner x (B k) (B l) * T (B k) (B l) from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [← g_inner_eq_orthonormal_parseval_sum (I := I) g x (B k) (B l) C hC]]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
  · rw [hB k k]; simp
  · intro l _ hlk
    rw [hB k l, if_neg (fun h => hlk h.symm)]; ring

omit [SigmaCompactSpace M] in
theorem scalarCurv_eq_orthonormal_trace
    (g : SmoothRiemannianMetric I M) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    scalarCurv (I := I) g x =
      ∑ i : Fin (Module.finrank ℝ E), ricciTensor (I := I) g x (B i) (B i) := by
  classical
  unfold scalarCurv
  exact symm_bilin_orthonormal_trace_invariant (I := I) g x (ricciTensor (I := I) g x)
    (fun a b => ricciTensor_symm (I := I) g x a b) B
    (fun i => smoothOrthoFrame (I := I) g x i x) hB
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)



omit [SigmaCompactSpace M] in
theorem metricScalar_eq_scal
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricScalarAt (I := I) g x = scalarCurv (I := I) g x := by
  classical
  let B : Fin (Module.finrank Real E) -> TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have hB : forall i j : Fin (Module.finrank Real E),
      g.inner x (B i) (B j) = if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hgram : forall i j : Fin (Module.finrank Real E),
      g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j) =
        chartGramMatrix (I := I) g x x i j := by
    intro i j
    rw [chartGramMatrix_apply, chartBasisVecFiber_self, chartBasisVecFiber_self]
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x
      (chartModelBasis E) (fun i j => chartInvGramMatrix (I := I) g x x i j) := by
    intro i j
    constructor
    · change (∑ k : Fin (Module.finrank Real E),
          chartInvGramMatrix (I := I) g x x i k *
            g.inner x ((chartModelBasis E) k) ((chartModelBasis E) j)) = _
      simp_rw [hgram]
      rw [← Matrix.mul_apply,
        chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hbase, Matrix.one_apply]
    · change (∑ k : Fin (Module.finrank Real E),
          g.inner x ((chartModelBasis E) i) ((chartModelBasis E) k) *
            chartInvGramMatrix (I := I) g x x k j) = _
      simp_rw [hgram]
      rw [← Matrix.mul_apply,
        chartGramMatrix_mul_chartInvGramMatrix (I := I) g x hbase, Matrix.one_apply]
  calc
    metricScalarAt (I := I) g x =
        metricTracePair0SAt (I := I) g (metricRicciAt (I := I) g x) :=
      metricScalarAt_def (I := I) g x
    _ = ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) g x x i j *
          metricRicciAt (I := I) g x
            (vec2 ((chartModelBasis E) i) ((chartModelBasis E) j)) :=
      metricTracePair0SAt_eq_sum_basis (I := I) g (chartModelBasis E)
        (fun i j => chartInvGramMatrix (I := I) g x x i j) hinv
        (metricRicciAt (I := I) g x)
    _ = ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        chartInvGramMatrix (I := I) g x x i j *
          ricciTensor (I := I) g x ((chartModelBasis E) i) ((chartModelBasis E) j) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [metricRicciAt_apply_eq_ricciTensor]
    _ = ∑ i : Fin (Module.finrank Real E), ricciTensor (I := I) g x (B i) (B i) :=
      (orthonormal_basis_bilin_trace (I := I) g x (ricciTensor (I := I) g x) B hB).symm
    _ = scalarCurv (I := I) g x :=
      (scalarCurv_eq_orthonormal_trace (I := I) g x B hB).symm

end ScalarCurv

section TraceBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

private lemma mdiffAt_finsetSum_aux {ι : Type*} (t : Finset ι) (f : ι → M → ℝ) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ) (f i) x) :
    MDifferentiableAt I 𝓘(ℝ) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp; exact mdifferentiableAt_const
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(ℝ) (f i) x := hf i (by simp)
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ) (f j) x :=
        fun j hj => hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(ℝ) (t.sum f) x := ih hft
      simpa [Finset.sum_insert, hit] using hfi.add hsum

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in

private lemma extDerivFun_finsetSum_aux {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(ℝ) (f i) x := hf i (by simp)
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(ℝ) (f j) x :=
        fun j hj => hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(ℝ) (t.sum f) x :=
        mdiffAt_finsetSum_aux (I := I) t f hft
      have hstep : extDerivFun (I := I) ((insert i t).sum f) x v =
          extDerivFun (I := I) (f i) x v + extDerivFun (I := I) (t.sum f) x v := by
        rw [Finset.sum_insert hit]
        have hadd := congr($(extDerivFun_add (I := I) (g := f i) (g' := t.sum f)
          (x := x) hfi hsum) v)
        simpa [Pi.add_apply] using hadd
      rw [hstep, ih hft, Finset.sum_insert hit]

omit [SigmaCompactSpace M] in
theorem orthonormal_frame_correction_sum_eq_zero
    (g : SmoothRiemannianMetric I M)
    {X V W : Π b : M, TangentSpace I b} {x : M} :
    ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (riemannOp (LeviCivita (I := I) g) x
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x (X x))
            (V x) (W x)) (smoothOrthoFrame (I := I) g x i x)
          + g.inner x (riemannOp (LeviCivita (I := I) g) x
            (smoothOrthoFrame (I := I) g x i x) (V x) (W x))
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x (X x))) = 0 := by
  classical
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  set u : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x (X x)
    with hu_def
  have hBon : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => g.inner x (u i) (B j) with ha_def
  set Tm : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) (V x) (W x)) (B j)
    with hTm_def
  have hskew : ∀ i j, a i j = - a j i := by
    intro i j
    simp only [ha_def, hB_def, hu_def]
    rw [smoothOrthoFrame_cov_skew (I := I) g x i j (X x),
      g.symm x (smoothOrthoFrame (I := I) g x i x) _]
  have hriemann_smul : ∀ (c : ℝ) (j i : Fin (Module.finrank ℝ E)),
      g.inner x (riemannOp (LeviCivita (I := I) g) x (c • B j) (V x) (W x)) (B i) =
        c * g.inner x (riemannOp (LeviCivita (I := I) g) x (B j) (V x) (W x)) (B i) := by
    intro c j i
    have he1 : riemannOp (LeviCivita (I := I) g) x (c • B j) (V x) (W x) =
        ricciEndo (I := I) g x (V x) (W x) (c • B j) := (ricciEndo_apply _ _ _ _ _).symm
    have he2 : riemannOp (LeviCivita (I := I) g) x (B j) (V x) (W x) =
        ricciEndo (I := I) g x (V x) (W x) (B j) := (ricciEndo_apply _ _ _ _ _).symm
    rw [he1, he2, LinearMap.map_smul (ricciEndo (I := I) g x (V x) (W x)) c (B j),
      (g.inner x).map_smul c (ricciEndo (I := I) g x (V x) (W x) (B j)),
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hfirst : ∀ i, g.inner x (riemannOp (LeviCivita (I := I) g) x (u i) (V x) (W x)) (B i) =
      ∑ j, a i j * Tm j i := by
    intro i
    have hexp : u i = ∑ j, g.inner x (u i) (B j) • B j :=
      orthonormal_frame_vector_expansion (I := I) g x (u i) B hBon
    have hri : riemannOp (LeviCivita (I := I) g) x (u i) (V x) (W x) =
        ricciEndo (I := I) g x (V x) (W x) (u i) := (ricciEndo_apply _ _ _ _ _).symm
    rw [hri, hexp, map_sum, map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [LinearMap.map_smul (ricciEndo (I := I) g x (V x) (W x)) (g.inner x (u i) (B j)) (B j),
      (g.inner x).map_smul (g.inner x (u i) (B j)) (ricciEndo (I := I) g x (V x) (W x) (B j)),
      ContinuousLinearMap.smul_apply, smul_eq_mul, ricciEndo_apply]
  have hsecond : ∀ i, g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) (V x) (W x)) (u i) =
      ∑ j, a i j * Tm i j := by
    intro i
    have hexp : u i = ∑ j, g.inner x (u i) (B j) • B j :=
      orthonormal_frame_vector_expansion (I := I) g x (u i) B hBon
    conv_lhs => rw [hexp]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ha_def, hTm_def]
  have hsum_eq : ∑ i, (g.inner x (riemannOp (LeviCivita (I := I) g) x (u i) (V x) (W x)) (B i)
        + g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) (V x) (W x)) (u i)) =
      (∑ i, ∑ j, a i j * Tm j i) + (∑ i, ∑ j, a i j * Tm i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hfirst i, hsecond i]
  rw [hsum_eq]
  have hcancel : (∑ i, ∑ j, a i j * Tm j i) = - (∑ i, ∑ j, a i j * Tm i j) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hskew j i]
    ring
  rw [hcancel]
  ring

omit [SigmaCompactSpace M] in
theorem nablaRicci_eq_frame_trace_nablaCurvSec
    (g : SmoothRiemannianMetric I M)
    {X V W : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaRicci (I := I) g X V W x =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (nablaCurvSec (LeviCivita (I := I) g) X
          (smoothOrthoFrame (I := I) g x i) V W x) (smoothOrthoFrame (I := I) g x i x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB_def
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i
  set S : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i b => riemannSec cov (B i) V W b with hS_def
  have hSsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (S i)) :=
    fun i => riemannSec_contMDiff cov (hBsm i) hV hW
  have hVX : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hWX : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hnbhd : (fun b => ricciTensor (I := I) g b (V b) (W b)) =ᶠ[𝓝 x]
      (fun b => ∑ i, g.inner b (S i b) (B i b)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with b hb
    rw [ricciTensor_eq_orthonormal_trace (I := I) g b (V b) (W b)
      (fun i => B i b) (fun i j => smoothOrthoFrame_orthonormal (I := I) g x hb i j)]
    refine Finset.sum_congr rfl ?_
    intro i _
    change g.inner b (riemannOp cov b (B i b) (V b) (W b)) (B i b) =
      g.inner b (riemannSec cov (B i) V W b) (B i b)
    rw [riemannOp_apply_smooth cov (hBsm i) hV hW]
  have hginner_sm : ∀ i, ContMDiff I 𝓘(ℝ) ∞ (fun b => g.inner b (S i b) (B i b)) := by
    intro i
    exact DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g
      ⟨fun b => S i b, hSsm i⟩ ⟨fun b => B i b, hBsm i⟩
  have hmd : ∀ i, MDifferentiableAt I 𝓘(ℝ) (fun b => g.inner b (S i b) (B i b)) x :=
    fun i => ((hginner_sm i) x).mdifferentiableAt (by simp)
  have hsum_deriv : extDerivFun (I := I)
      (fun b => ricciTensor (I := I) g b (V b) (W b)) x (X x) =
      ∑ i, (g.inner x (cov.toFun (S i) x (X x)) (B i x)
        + g.inner x (S i x) (cov.toFun (B i) x (X x))) := by
    have hmfd : mfderiv I 𝓘(ℝ, ℝ) (fun b => ricciTensor (I := I) g b (V b) (W b)) x =
        mfderiv I 𝓘(ℝ, ℝ) (fun b => ∑ i, g.inner b (S i b) (B i b)) x :=
      Filter.EventuallyEq.mfderiv_eq hnbhd
    have hmf_eq : extDerivFun (I := I)
        (fun b => ricciTensor (I := I) g b (V b) (W b)) x (X x) =
        extDerivFun (I := I) (fun b => ∑ i, g.inner b (S i b) (B i b)) x (X x) :=
      DFunLike.congr_fun hmfd (X x)
    rw [hmf_eq]
    rw [show (fun b => ∑ i, g.inner b (S i b) (B i b)) =
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun i => fun b => g.inner b (S i b) (B i b)) from by
      funext b; rw [Finset.sum_apply]]
    rw [extDerivFun_finsetSum_aux (I := I) _ _ (X x) (fun i _ => hmd i)]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply
      ((hSsm i x).mdifferentiableAt (by simp)) ((hBsm i x).mdifferentiableAt (by simp)) (X x)
    exact hmc
  have hdecomp : ∀ i, cov.toFun (S i) x (X x) =
      nablaCurvSec cov X (B i) V W x
        + riemannSec cov (covApply cov X (B i)) V W x
        + riemannSec cov (B i) (covApply cov X V) W x
        + riemannSec cov (B i) V (covApply cov X W) x := by
    intro i
    have hnc : nablaCurvSec cov X (B i) V W x =
        cov.toFun (fun b => riemannSec cov (B i) V W b) x (X x)
          - riemannSec cov (covApply cov X (B i)) V W x
          - riemannSec cov (B i) (covApply cov X V) W x
          - riemannSec cov (B i) V (covApply cov X W) x := nablaCurvSec_def cov X (B i) V W x
    rw [hnc]
    change cov.toFun (fun b => riemannSec cov (B i) V W b) x (X x) = _
    abel
  have hriS : ∀ i, S i x = riemannOp cov x (B i x) (V x) (W x) := by
    intro i
    change riemannSec cov (B i) V W x = riemannOp cov x (B i x) (V x) (W x)
    rw [← riemannOp_apply_smooth cov (hBsm i) hV hW]
  have hcVsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X V)) :=
    covApply_contMDiff (cov := cov) hX hV
  have hcWsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X W)) :=
    covApply_contMDiff (cov := cov) hX hW
  have hri_cV : ∀ i, riemannSec cov (B i) (covApply cov X V) W x =
      riemannOp cov x (B i x) (covApply cov X V x) (W x) :=
    fun i => (riemannOp_apply_smooth cov (hBsm i) hcVsm hW).symm
  have hri_cW : ∀ i, riemannSec cov (B i) V (covApply cov X W) x =
      riemannOp cov x (B i x) (V x) (covApply cov X W x) :=
    fun i => (riemannOp_apply_smooth cov (hBsm i) hV hcWsm).symm
  rw [nablaRicci_def, hsum_deriv]
  have hexpand : ∑ i, (g.inner x (cov.toFun (S i) x (X x)) (B i x)
        + g.inner x (S i x) (cov.toFun (B i) x (X x))) =
      (∑ i, g.inner x (nablaCurvSec cov X (B i) V W x) (B i x))
        + (∑ i, (g.inner x (riemannOp cov x (covApply cov X (B i) x) (V x) (W x)) (B i x)
            + g.inner x (riemannOp cov x (B i x) (V x) (W x)) (cov.toFun (B i) x (X x))))
        + (∑ i, g.inner x (riemannOp cov x (B i x) (covApply cov X V x) (W x)) (B i x))
        + (∑ i, g.inner x (riemannOp cov x (B i x) (V x) (covApply cov X W x)) (B i x)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hdecomp i, hriS i]
    rw [map_add, ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.add_apply,
      map_add, ContinuousLinearMap.add_apply]
    have hrcB : riemannSec cov (covApply cov X (B i)) V W x =
        riemannOp cov x (covApply cov X (B i) x) (V x) (W x) :=
      (riemannOp_apply_smooth cov (covApply_contMDiff (cov := cov) hX (hBsm i)) hV hW).symm
    rw [hrcB, hri_cV i, hri_cW i]
    ring
  rw [hexpand]
  have hframe0 : (∑ i, (g.inner x (riemannOp cov x (covApply cov X (B i) x) (V x) (W x)) (B i x)
      + g.inner x (riemannOp cov x (B i x) (V x) (W x)) (cov.toFun (B i) x (X x)))) = 0 := by
    have h := orthonormal_frame_correction_sum_eq_zero (I := I) g (X := X) (V := V) (W := W)
      (x := x)
    simpa [hcov_def, hB_def, covApply] using h
  have hVcorr : (∑ i, g.inner x (riemannOp cov x (B i x) (covApply cov X V x) (W x)) (B i x)) =
      ricciTensor (I := I) g x (covApply cov X V x) (W x) :=
    (ricciTensor_eq_orthonormal_trace (I := I) g x (covApply cov X V x) (W x)
      (fun i => B i x)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)).symm
  have hWcorr : (∑ i, g.inner x (riemannOp cov x (B i x) (V x) (covApply cov X W x)) (B i x)) =
      ricciTensor (I := I) g x (V x) (covApply cov X W x) :=
    (ricciTensor_eq_orthonormal_trace (I := I) g x (V x) (covApply cov X W x)
      (fun i => B i x)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)).symm
  rw [hframe0, hVcorr, hWcorr]
  simp only [covApply_apply]
  ring

end TraceBridge

section NablaScalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def nablaScalar (g : SmoothRiemannianMetric I M)
    (X : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  extDerivFun (I := I) (scalarCurv (I := I) g) x (X x)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma nablaScalar_def (g : SmoothRiemannianMetric I M)
    (X : Π b : M, TangentSpace I b) (x : M) :
    nablaScalar (I := I) g X x =
      extDerivFun (I := I) (scalarCurv (I := I) g) x (X x) := rfl

omit [SigmaCompactSpace M] in
theorem ricci_orthonormal_frame_correction_eq_zero
    (g : SmoothRiemannianMetric I M)
    {X : Π b : M, TangentSpace I b} {x : M} :
    ∑ i : Fin (Module.finrank ℝ E),
        ricciTensor (I := I) g x
          ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x (X x))
          (smoothOrthoFrame (I := I) g x i x) = 0 := by
  classical
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  set u : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x (X x)
    with hu_def
  have hBon : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => g.inner x (u i) (B j) with ha_def
  set Rm : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => ricciTensor (I := I) g x (B i) (B j) with hRm_def
  have hskew : ∀ i j, a i j = - a j i := by
    intro i j
    simp only [ha_def, hB_def, hu_def]
    rw [smoothOrthoFrame_cov_skew (I := I) g x i j (X x),
      g.symm x (smoothOrthoFrame (I := I) g x i x) _]
  have hRsymm : ∀ i j, Rm j i = Rm i j := by
    intro i j
    rw [hRm_def]
    exact ricciTensor_symm (I := I) g x (B j) (B i)
  have hexp : ∀ i, ricciTensor (I := I) g x (u i) (B i) = ∑ j, a i j * Rm j i := by
    intro i
    have he : u i = ∑ j, g.inner x (u i) (B j) • B j :=
      orthonormal_frame_vector_expansion (I := I) g x (u i) B hBon
    rw [he, map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ha_def, hRm_def]
  have hsumeq : (∑ i, ricciTensor (I := I) g x (u i) (B i)) = ∑ i, ∑ j, a i j * Rm j i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact hexp i
  rw [hsumeq]
  have hzero : (∑ i, ∑ j, a i j * Rm j i) = - (∑ i, ∑ j, a i j * Rm j i) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hskew j i, hRsymm j i]
    ring
  linarith [hzero]

omit [SigmaCompactSpace M] in
theorem nablaScalar_eq_frame_trace_nablaRicci
    (g : SmoothRiemannianMetric I M)
    {X : Π b : M, TangentSpace I b} {x : M} :
    nablaScalar (I := I) g X x =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaRicci (I := I) g X (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i) x := by
  classical
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB_def
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i
  have hRicpair : ∀ i, ContMDiff I 𝓘(ℝ) ∞
      (fun b => ricciTensor (I := I) g b (B i b) (B i b)) :=
    fun i => ricciTensor_pairing_contMDiff (I := I) g (hBsm i) (hBsm i)
  have hmd : ∀ i, MDifferentiableAt I 𝓘(ℝ)
      (fun b => ricciTensor (I := I) g b (B i b) (B i b)) x :=
    fun i => ((hRicpair i) x).mdifferentiableAt (by simp)
  have hnbhd : scalarCurv (I := I) g =ᶠ[𝓝 x]
      (fun b => ∑ i, ricciTensor (I := I) g b (B i b) (B i b)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with b hb
    exact scalarCurv_eq_orthonormal_trace (I := I) g b (fun i => B i b)
      (fun i j => smoothOrthoFrame_orthonormal (I := I) g x hb i j)
  rw [nablaScalar_def]
  have hmfd : mfderiv I 𝓘(ℝ, ℝ) (scalarCurv (I := I) g) x =
      mfderiv I 𝓘(ℝ, ℝ) (fun b => ∑ i, ricciTensor (I := I) g b (B i b) (B i b)) x :=
    Filter.EventuallyEq.mfderiv_eq hnbhd
  have hext_eq : extDerivFun (I := I) (scalarCurv (I := I) g) x (X x) =
      extDerivFun (I := I) (fun b => ∑ i, ricciTensor (I := I) g b (B i b) (B i b)) x (X x) :=
    DFunLike.congr_fun hmfd (X x)
  rw [hext_eq]
  rw [show (fun b => ∑ i, ricciTensor (I := I) g b (B i b) (B i b)) =
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
        (fun i => fun b => ricciTensor (I := I) g b (B i b) (B i b)) from by
    funext b; rw [Finset.sum_apply]]
  rw [extDerivFun_finsetSum_aux (I := I) _ _ (X x) (fun i _ => hmd i)]
  have hper : ∀ i, extDerivFun (I := I)
      (fun b => ricciTensor (I := I) g b (B i b) (B i b)) x (X x) =
      nablaRicci (I := I) g X (B i) (B i) x
        + (ricciTensor (I := I) g x
            ((LeviCivita (I := I) g).toFun (B i) x (X x)) (B i x)
          + ricciTensor (I := I) g x (B i x)
            ((LeviCivita (I := I) g).toFun (B i) x (X x))) := by
    intro i
    rw [nablaRicci_def]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hper i)]
  rw [Finset.sum_add_distrib]
  have hcorr0 : (∑ i, (ricciTensor (I := I) g x
        ((LeviCivita (I := I) g).toFun (B i) x (X x)) (B i x)
      + ricciTensor (I := I) g x (B i x)
        ((LeviCivita (I := I) g).toFun (B i) x (X x)))) = 0 := by
    have hc1 := ricci_orthonormal_frame_correction_eq_zero (I := I) g (X := X) (x := x)
    have hc2 : (∑ i, ricciTensor (I := I) g x (B i x)
        ((LeviCivita (I := I) g).toFun (B i) x (X x))) = 0 := by
      rw [← hc1]
      refine Finset.sum_congr rfl ?_
      intro i _
      exact ricciTensor_symm (I := I) g x (B i x)
        ((LeviCivita (I := I) g).toFun (B i) x (X x))
    rw [Finset.sum_add_distrib, hc1, hc2, add_zero]
  rw [hcorr0, add_zero]

end NablaScalar

section NablaCurvSymmetries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaCurvSec_swap23
    (g : SmoothRiemannianMetric I M)
    {X Y Z W : Π b : M, TangentSpace I b} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    nablaCurvSec (LeviCivita (I := I) g) X Y Z W x =
      - nablaCurvSec (LeviCivita (I := I) g) X Z Y W x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  rw [nablaCurvSec_def, nablaCurvSec_def]
  have hsec_eq : (fun b => riemannSec cov Z Y W b) =
      -(fun b => riemannSec cov Y Z W b) := by
    funext b; rw [Pi.neg_apply]; exact riemannSec_swap cov Z Y W b
  have hsec_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y Z W b)) :=
    riemannSec_contMDiff cov hY hZ hW
  have hneg : cov.toFun (fun b => riemannSec cov Z Y W b) x (X x) =
      - cov.toFun (fun b => riemannSec cov Y Z W b) x (X x) := by
    rw [hsec_eq, cov_toFun_neg cov (hsec_sm.mdifferentiableAt (by simp))]
    rfl
  rw [hneg]
  rw [riemannSec_swap cov (covApply cov X Z) Y W x,
      riemannSec_swap cov Z (covApply cov X Y) W x,
      riemannSec_swap cov Z Y (covApply cov X W) x]
  abel

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaCurvSec_metric_skew45
    (g : SmoothRiemannianMetric I M)
    {X Y Z W U : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U)) :
    g.inner x (nablaCurvSec (LeviCivita (I := I) g) X Y Z W x) (U x) +
      g.inner x (nablaCurvSec (LeviCivita (I := I) g) X Y Z U x) (W x) = 0 := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hRW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y Z W b)) :=
    riemannSec_contMDiff cov hY hZ hW
  have hRU_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y Z U b)) :=
    riemannSec_contMDiff cov hY hZ hU
  have hskew_sec : ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
        + (fun b => g.inner b (riemannSec cov Y Z U b) (W b))) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards with b
    have h1 : riemannSec cov Y Z W b = riemannOp cov b (Y b) (Z b) (W b) :=
      (riemannOp_apply_smooth cov hY hZ hW).symm
    have h2 : riemannSec cov Y Z U b = riemannOp cov b (Y b) (Z b) (U b) :=
      (riemannOp_apply_smooth cov hY hZ hU).symm
    have hsk := riemannOp_metric_skew (I := I) g b (Y b) (Z b) (W b) (U b)
    rw [g.symm b (W b) (riemannOp cov b (Y b) (Z b) (U b))] at hsk
    change g.inner b (riemannSec cov Y Z W b) (U b)
        + g.inner b (riemannSec cov Y Z U b) (W b) = 0
    rw [h1, h2]; exact hsk
  have hRWat : MDiffAt (T% (fun b => riemannSec cov Y Z W b)) x :=
    hRW_sm.mdifferentiableAt (by simp)
  have hRUat : MDiffAt (T% (fun b => riemannSec cov Y Z U b)) x :=
    hRU_sm.mdifferentiableAt (by simp)
  have hUat : MDiffAt (T% U) x := (hU x).mdifferentiableAt (by simp)
  have hWat : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hmd1 : MDifferentiableAt I 𝓘(ℝ)
      (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x :=
    ((DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g
      ⟨_, hRW_sm⟩ ⟨fun b => U b, hU⟩) x).mdifferentiableAt (by simp)
  have hmd2 : MDifferentiableAt I 𝓘(ℝ)
      (fun b => g.inner b (riemannSec cov Y Z U b) (W b)) x :=
    ((DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g
      ⟨_, hRU_sm⟩ ⟨fun b => W b, hW⟩) x).mdifferentiableAt (by simp)
  have hmf0 : extDerivFun (I := I) (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x (X x)
      + extDerivFun (I := I) (fun b => g.inner b (riemannSec cov Y Z U b) (W b)) x (X x) = 0 := by
    have hsum0 : extDerivFun (I := I)
        ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
          + (fun b => g.inner b (riemannSec cov Y Z U b) (W b))) x (X x) = 0 := by
      have hmfd0 : mfderiv I 𝓘(ℝ, ℝ)
          ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
            + (fun b => g.inner b (riemannSec cov Y Z U b) (W b))) x =
          mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x :=
        Filter.EventuallyEq.mfderiv_eq hskew_sec
      change (mfderiv I 𝓘(ℝ, ℝ)
        ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
          + (fun b => g.inner b (riemannSec cov Y Z U b) (W b))) x) (X x) = 0
      rw [hmfd0, mfderiv_const]; rfl
    rw [extDerivFun_add (I := I) hmd1 hmd2] at hsum0
    simpa [Pi.add_apply] using hsum0
  rw [show extDerivFun (I := I) (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x (X x) =
      (mfderiv I 𝓘(ℝ) (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x) (X x) from rfl,
    show extDerivFun (I := I) (fun b => g.inner b (riemannSec cov Y Z U b) (W b)) x (X x) =
      (mfderiv I 𝓘(ℝ) (fun b => g.inner b (riemannSec cov Y Z U b) (W b)) x) (X x) from rfl,
    (LeviCivita_isMetricCompatible (I := I) g).apply hRWat hUat (X x),
    (LeviCivita_isMetricCompatible (I := I) g).apply hRUat hWat (X x)] at hmf0
  have hexpand : ∀ {T : Π b : M, TangentSpace I b}
      (hT : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% T)),
      cov.toFun (fun b => riemannSec cov Y Z T b) x (X x) =
        nablaCurvSec cov X Y Z T x
          + riemannSec cov (covApply cov X Y) Z T x
          + riemannSec cov Y (covApply cov X Z) T x
          + riemannSec cov Y Z (covApply cov X T) x := by
    intro T hT
    rw [nablaCurvSec_def]; abel
  rw [hexpand hW, hexpand hU] at hmf0
  have hsk : ∀ (a b c d : Π bb : M, TangentSpace I bb)
      (_ha : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% a))
      (_hb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% b))
      (_hc : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% c))
      (_hd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% d)),
      g.inner x (riemannSec cov a b c x) (d x)
        + g.inner x (riemannSec cov a b d x) (c x) = 0 := by
    intro a b c d ha hb hc hd
    rw [show riemannSec cov a b c x = riemannOp cov x (a x) (b x) (c x) from
        (riemannOp_apply_smooth cov ha hb hc).symm,
      show riemannSec cov a b d x = riemannOp cov x (a x) (b x) (d x) from
        (riemannOp_apply_smooth cov ha hb hd).symm]
    have hsk0 := riemannOp_metric_skew (I := I) g x (a x) (b x) (c x) (d x)
    rw [g.symm x (c x) (riemannOp cov x (a x) (b x) (d x))] at hsk0
    exact hsk0
  have hcXY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X Y)) :=
    covApply_contMDiff (cov := cov) hX hY
  have hcXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X Z)) :=
    covApply_contMDiff (cov := cov) hX hZ
  have hcXW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X W)) :=
    covApply_contMDiff (cov := cov) hX hW
  have hcXU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X U)) :=
    covApply_contMDiff (cov := cov) hX hU
  have p1 := hsk (covApply cov X Y) Z W U hcXY hZ hW hU
  have p2 := hsk Y (covApply cov X Z) W U hY hcXZ hW hU
  have p3 := hsk Y Z (covApply cov X W) U hY hZ hcXW hU
  have p4 := hsk Y Z W (covApply cov X U) hY hZ hW hcXU
  simp only [map_add, ContinuousLinearMap.add_apply] at hmf0
  rw [show ((LeviCivita (I := I) g).toFun U x) (X x) = covApply cov X U x from rfl,
      show ((LeviCivita (I := I) g).toFun W x) (X x) = covApply cov X W x from rfl] at hmf0
  linarith [hmf0, p1, p2, p3, p4]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaCurvSec_inner_pair_symm
    (g : SmoothRiemannianMetric I M)
    {X Y Z W U : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U)) :
    g.inner x (nablaCurvSec (LeviCivita (I := I) g) X Y Z W x) (U x) =
      g.inner x (nablaCurvSec (LeviCivita (I := I) g) X W U Y x) (Z x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  have hRYZW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov Y Z W b)) :=
    riemannSec_contMDiff cov hY hZ hW
  have hRWUY_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b => riemannSec cov W U Y b)) :=
    riemannSec_contMDiff cov hW hU hY
  have hUat : MDiffAt (T% U) x := (hU x).mdifferentiableAt (by simp)
  have hZat : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have hRYZWat : MDiffAt (T% (fun b => riemannSec cov Y Z W b)) x :=
    hRYZW_sm.mdifferentiableAt (by simp)
  have hRWUYat : MDiffAt (T% (fun b => riemannSec cov W U Y b)) x :=
    hRWUY_sm.mdifferentiableAt (by simp)
  have hps_sec : ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
        - (fun b => g.inner b (riemannSec cov W U Y b) (Z b))) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards with b
    have h1 : riemannSec cov Y Z W b = riemannOp cov b (Y b) (Z b) (W b) :=
      (riemannOp_apply_smooth cov hY hZ hW).symm
    have h2 : riemannSec cov W U Y b = riemannOp cov b (W b) (U b) (Y b) :=
      (riemannOp_apply_smooth cov hW hU hY).symm
    change g.inner b (riemannSec cov Y Z W b) (U b)
        - g.inner b (riemannSec cov W U Y b) (Z b) = 0
    rw [h1, h2, riemannOp_inner_pair_symm (I := I) g b (Y b) (Z b) (W b) (U b), sub_self]
  have hmd1 : MDifferentiableAt I 𝓘(ℝ)
      (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x :=
    ((DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g
      ⟨_, hRYZW_sm⟩ ⟨fun b => U b, hU⟩) x).mdifferentiableAt (by simp)
  have hmd2 : MDifferentiableAt I 𝓘(ℝ)
      (fun b => g.inner b (riemannSec cov W U Y b) (Z b)) x :=
    ((DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g
      ⟨_, hRWUY_sm⟩ ⟨fun b => Z b, hZ⟩) x).mdifferentiableAt (by simp)
  have hmf0 : extDerivFun (I := I) (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x (X x)
      - extDerivFun (I := I) (fun b => g.inner b (riemannSec cov W U Y b) (Z b)) x (X x) = 0 := by
    have hsub0 : extDerivFun (I := I)
        ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
          - (fun b => g.inner b (riemannSec cov W U Y b) (Z b))) x (X x) = 0 := by
      have hmfd0 : mfderiv I 𝓘(ℝ, ℝ)
          ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
            - (fun b => g.inner b (riemannSec cov W U Y b) (Z b))) x =
          mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x :=
        Filter.EventuallyEq.mfderiv_eq hps_sec
      change (mfderiv I 𝓘(ℝ, ℝ)
        ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
          - (fun b => g.inner b (riemannSec cov W U Y b) (Z b))) x) (X x) = 0
      rw [hmfd0, mfderiv_const]; rfl
    have hsubeq : extDerivFun (I := I)
        ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
          - (fun b => g.inner b (riemannSec cov W U Y b) (Z b))) x =
        extDerivFun (I := I) (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x
          - extDerivFun (I := I) (fun b => g.inner b (riemannSec cov W U Y b) (Z b)) x := by
      have hadd := extDerivFun_add (I := I)
        (g := (fun b => g.inner b (riemannSec cov Y Z W b) (U b))
          - (fun b => g.inner b (riemannSec cov W U Y b) (Z b)))
        (g' := (fun b => g.inner b (riemannSec cov W U Y b) (Z b))) (x := x)
        (hmd1.sub hmd2) hmd2
      have hcancel : ((fun b => g.inner b (riemannSec cov Y Z W b) (U b))
          - (fun b => g.inner b (riemannSec cov W U Y b) (Z b)))
          + (fun b => g.inner b (riemannSec cov W U Y b) (Z b)) =
          (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) := by
        funext b; simp
      rw [hcancel] at hadd
      rw [eq_sub_iff_add_eq, ← hadd]
    have := hsub0
    rw [hsubeq] at this
    simpa [ContinuousLinearMap.sub_apply] using this
  rw [show extDerivFun (I := I) (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x (X x) =
      (mfderiv I 𝓘(ℝ) (fun b => g.inner b (riemannSec cov Y Z W b) (U b)) x) (X x) from rfl,
    show extDerivFun (I := I) (fun b => g.inner b (riemannSec cov W U Y b) (Z b)) x (X x) =
      (mfderiv I 𝓘(ℝ) (fun b => g.inner b (riemannSec cov W U Y b) (Z b)) x) (X x) from rfl,
    (LeviCivita_isMetricCompatible (I := I) g).apply hRYZWat hUat (X x),
    (LeviCivita_isMetricCompatible (I := I) g).apply hRWUYat hZat (X x)] at hmf0
  have hexpand : ∀ {A B C : Π b : M, TangentSpace I b}
      (_hA : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% A))
      (_hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
      (_hC : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% C)),
      cov.toFun (fun b => riemannSec cov A B C b) x (X x) =
        nablaCurvSec cov X A B C x
          + riemannSec cov (covApply cov X A) B C x
          + riemannSec cov A (covApply cov X B) C x
          + riemannSec cov A B (covApply cov X C) x := by
    intro A B C _ _ _
    rw [nablaCurvSec_def]; abel
  rw [hexpand hY hZ hW, hexpand hW hU hY] at hmf0
  have hps : ∀ (a b c d e f : Π bb : M, TangentSpace I bb)
      (_ha : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% a))
      (_hb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% b))
      (_hc : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% c)),
      g.inner x (riemannSec cov a b c x) (d x) =
        g.inner x (riemannOp cov x (c x) (d x) (a x)) (b x) := by
    intro a b c d _ _ ha hb hc
    rw [show riemannSec cov a b c x = riemannOp cov x (a x) (b x) (c x) from
        (riemannOp_apply_smooth cov ha hb hc).symm]
    exact riemannOp_inner_pair_symm (I := I) g x (a x) (b x) (c x) (d x)
  have hcXY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X Y)) :=
    covApply_contMDiff (cov := cov) hX hY
  have hcXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X Z)) :=
    covApply_contMDiff (cov := cov) hX hZ
  have hcXW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X W)) :=
    covApply_contMDiff (cov := cov) hX hW
  have hcXU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X U)) :=
    covApply_contMDiff (cov := cov) hX hU
  have q1 := hps (covApply cov X Y) Z W U W U hcXY hZ hW
  have q2 := hps Y (covApply cov X Z) W U W U hY hcXZ hW
  have q3 := hps Y Z (covApply cov X W) U W U hY hZ hcXW
  have q4 : g.inner x (riemannSec cov Y Z W x) (covApply cov X U x) =
      g.inner x (riemannOp cov x (W x) (covApply cov X U x) (Y x)) (Z x) := by
    rw [show riemannSec cov Y Z W x = riemannOp cov x (Y x) (Z x) (W x) from
        (riemannOp_apply_smooth cov hY hZ hW).symm]
    exact riemannOp_inner_pair_symm (I := I) g x (Y x) (Z x) (W x) (covApply cov X U x)
  have r1 : riemannSec cov (covApply cov X W) U Y x =
      riemannOp cov x (covApply cov X W x) (U x) (Y x) :=
    (riemannOp_apply_smooth cov hcXW hU hY).symm
  have r2 : riemannSec cov W (covApply cov X U) Y x =
      riemannOp cov x (W x) (covApply cov X U x) (Y x) :=
    (riemannOp_apply_smooth cov hW hcXU hY).symm
  have r3 : riemannSec cov W U (covApply cov X Y) x =
      riemannOp cov x (W x) (U x) (covApply cov X Y x) :=
    (riemannOp_apply_smooth cov hW hU hcXY).symm
  have r5 : riemannSec cov W U Y x = riemannOp cov x (W x) (U x) (Y x) :=
    (riemannOp_apply_smooth cov (x := x) hW hU hY).symm
  simp only [map_add, ContinuousLinearMap.add_apply] at hmf0
  rw [show ((LeviCivita (I := I) g).toFun U x) (X x) = covApply cov X U x from rfl,
      show ((LeviCivita (I := I) g).toFun Z x) (X x) = covApply cov X Z x from rfl] at hmf0
  rw [q1, q2, q3, q4, r1, r2, r3, r5] at hmf0
  linarith [hmf0]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem nablaCurvSec_bianchi_paired
    (g : SmoothRiemannianMetric I M)
    {X Y Z W U : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W)) :
    g.inner x (nablaCurvSec (LeviCivita (I := I) g) X Y Z W x) (U x)
      + g.inner x (nablaCurvSec (LeviCivita (I := I) g) Y Z X W x) (U x)
      + g.inner x (nablaCurvSec (LeviCivita (I := I) g) Z X Y W x) (U x) = 0 := by
  have hb := second_bianchi_levi_civita_metric (I := I) g hX hY hZ hW (x := x)
  have hsum : g.inner x (nablaCurvSec (LeviCivita (I := I) g) X Y Z W x
        + nablaCurvSec (LeviCivita (I := I) g) Y Z X W x
        + nablaCurvSec (LeviCivita (I := I) g) Z X Y W x) (U x) = 0 := by
    rw [hb]; simp
  rw [map_add, map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply] at hsum
  exact hsum

end NablaCurvSymmetries

section ContractedBianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [SigmaCompactSpace M] in
theorem contracted_second_bianchi
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b} {x : M}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) :
    ∑ j : Fin (Module.finrank ℝ E),
        nablaRicci (I := I) g (smoothOrthoFrame (I := I) g x j)
          (smoothOrthoFrame (I := I) g x j) V x =
      (1 / 2 : ℝ) * nablaScalar (I := I) g V x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB_def
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i
  set NR : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun A C D F i => g.inner x (nablaCurvSec cov A C D F x) (B i x) with hNR_def
  have hLHS : ∑ j, nablaRicci (I := I) g (B j) (B j) V x =
      ∑ j, ∑ i, NR (B j) (B i) (B j) V i := by
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g (hBsm j) (hBsm j) hV]
  have hRHS : nablaScalar (I := I) g V x = ∑ k, ∑ i, NR V (B i) (B k) (B k) i := by
    rw [nablaScalar_eq_frame_trace_nablaRicci (I := I) g]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hV (hBsm k) (hBsm k)]
  rw [hLHS, hRHS]
  have hAB : ∀ j i, NR (B j) (B i) (B j) V i = - NR (B j) V (B i) (B j) i := by
    intro j i
    have hbi := nablaCurvSec_bianchi_paired (I := I) g (X := B j) (Y := B i) (Z := B j)
      (W := V) (U := B i) (x := x) (hBsm j) (hBsm i) (hBsm j) hV
    have hmidzero : nablaCurvSec cov (B i) (B j) (B j) V x = 0 := by
      have h := nablaCurvSec_swap23 (I := I) g (X := B i) (Y := B j) (Z := B j) (W := V)
        (x := x) (hBsm j) (hBsm j) hV
      have : (2 : ℝ) • nablaCurvSec cov (B i) (B j) (B j) V x = 0 := by
        rw [two_smul]; nth_rewrite 2 [h]; abel
      simpa using this
    have hmid : g.inner x (nablaCurvSec cov (B i) (B j) (B j) V x) (B i x) = 0 := by
      rw [hmidzero]; simp
    have hstep : NR (B j) (B i) (B j) V i = - NR (B j) (B j) (B i) V i := by
      simp only [hNR_def] at hbi ⊢
      rw [hmid] at hbi
      linarith [hbi]
    have hps : NR (B j) (B j) (B i) V i = NR (B j) V (B i) (B j) i := by
      simp only [hNR_def]
      exact nablaCurvSec_inner_pair_symm (I := I) g (X := B j) (Y := B j) (Z := B i)
        (W := V) (U := B i) (hBsm j) (hBsm j) (hBsm i) hV (hBsm i)
    rw [hstep, hps]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hAB j i))]
  set P : ℝ := ∑ j, ∑ i, NR (B j) V (B i) (B j) i with hP_def
  rw [show (∑ j, ∑ i, - NR (B j) V (B i) (B j) i) = -P from by
    rw [hP_def]; rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← Finset.sum_neg_distrib]]
  set Q : ℝ := ∑ k, ∑ i, NR V (B i) (B k) (B k) i with hQ_def
  set R3 : ℝ := ∑ j, ∑ i, NR (B i) (B j) V (B j) i with hR3_def
  have hC : P + Q + R3 = 0 := by
    have hPQR : P + Q + R3 =
        ∑ j, ∑ i, (NR (B j) V (B i) (B j) i + NR V (B i) (B j) (B j) i
          + NR (B i) (B j) V (B j) i) := by
      rw [hP_def, hQ_def, hR3_def]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [hPQR]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro i _
    have hbi := nablaCurvSec_bianchi_paired (I := I) g (X := B j) (Y := V) (Z := B i)
      (W := B j) (U := B i) (x := x) (hBsm j) hV (hBsm i) (hBsm j)
    simp only [hNR_def]
    exact hbi
  have hD : R3 = P := by
    have hterm : ∀ j i, NR (B i) (B j) V (B j) i = NR (B i) V (B j) (B i) j := by
      intro j i
      have hs2 := nablaCurvSec_metric_skew45 (I := I) g (X := B i) (Y := B j) (Z := V)
        (W := B j) (U := B i) (x := x) (hBsm i) (hBsm j) hV (hBsm j) (hBsm i)
      have hs1 := nablaCurvSec_swap23 (I := I) g (X := B i) (Y := B j) (Z := V) (W := B i)
        (x := x) (hBsm j) hV (hBsm i)
      simp only [hNR_def]
      rw [hs1] at hs2
      simp only [map_neg, ContinuousLinearMap.neg_apply] at hs2
      linarith [hs2]
    rw [hR3_def, hP_def]
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hterm j i))]
    rw [Finset.sum_comm]
  rw [hD] at hC
  have : Q = -2 * P := by linarith [hC]
  rw [this]; ring

end ContractedBianchi

end Connection
end Integral
end DifferentialGeometry
