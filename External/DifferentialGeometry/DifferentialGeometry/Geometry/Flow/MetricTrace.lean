import DifferentialGeometry.Geometry.Flow.ConnectionDifference
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def deTurckChartLocal (g g' : SmoothRiemannianMetric I M) (α : M) (x : M) :
    TangentSpace I x :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x j k •
      connDiff (I := I) g g' x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
lemma deTurckChartLocal_def (g g' : SmoothRiemannianMetric I M) (α : M) (x : M) :
    deTurckChartLocal (I := I) g g' α x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x j k •
          connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma clm_bilinear_expand_two_sums_vector
    {x : M}
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (a b : Fin n → ℝ) (u w : Fin n → TangentSpace I x) :
    B (∑ p : Fin n, a p • u p) (∑ q : Fin n, b q • w q) =
      ∑ p : Fin n, ∑ q : Fin n, (a p * b q) • B (u p) (w q) := by
  classical
  have houter : B (∑ p : Fin n, a p • u p) = ∑ p : Fin n, a p • B (u p) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [map_smul]
  rw [houter, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.smul_apply]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [map_smul, smul_smul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma clm_bilinear_expand_two_sums_scalar
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (a b : Fin n → ℝ) (u w : Fin n → TangentSpace I x) :
    g.inner x (∑ p : Fin n, a p • u p) (∑ q : Fin n, b q • w q) =
      ∑ p : Fin n, ∑ q : Fin n, (a p * b q) * g.inner x (u p) (w q) := by
  classical
  have houter : g.inner x (∑ p : Fin n, a p • u p) =
      ∑ p : Fin n, a p • g.inner x (u p) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [map_smul]
  rw [houter, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [map_smul, smul_eq_mul]
  ring

private def deTurckCobMatrix (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k =>
    (chartModelBasis E).repr
      ((chartBasisVecFiber (I := I) α i x : TangentSpace I x)) k

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartBasisVecFiber_eq_sum_model (α : M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        deTurckCobMatrix (I := I) α x i k •
          ((chartModelBasis E) k : TangentSpace I x) := by
  classical
  unfold deTurckCobMatrix
  simp only [Matrix.of_apply]
  exact (((chartModelBasis E).sum_repr
    (chartBasisVecFiber (I := I) α i x : TangentSpace I x))).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma deTurckCobMatrix_eq_toMatrix_transpose (α : M) (x : M) :
    deTurckCobMatrix (I := I) α x =
      ((chartModelBasis E).toMatrix
        (fun i : Fin (Module.finrank ℝ E) =>
          chartBasisVecFiber (I := I) α i x))ᵀ := by
  classical
  unfold deTurckCobMatrix
  ext i k
  rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, Matrix.of_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma deTurckCobMatrix_isUnit (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (deTurckCobMatrix (I := I) α x) := by
  classical
  rw [deTurckCobMatrix_eq_toMatrix_transpose]
  set chartBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hx with hCB_def
  have hfam_eq : (fun i : Fin (Module.finrank ℝ E) =>
      chartBasisVecFiber (I := I) α i x)
      = (chartBasis : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
    funext i
    rw [hCB_def]
    exact (chartBasisFamily_apply (I := I) α hx i).symm
  rw [hfam_eq]
  have hbase_unit : IsUnit ((chartModelBasis E).toMatrix
      (chartBasis : Fin (Module.finrank ℝ E) → TangentSpace I x)) :=
    ⟨⟨_, chartBasis.toMatrix (chartModelBasis E),
        Module.Basis.toMatrix_mul_toMatrix_flip _ _,
        Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, rfl⟩
  rw [Matrix.isUnit_iff_isUnit_det] at hbase_unit ⊢
  rwa [Matrix.det_transpose]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartGramMatrix_self_eq_model (g : SmoothRiemannianMetric I M) (x : M)
    (k l : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g x x k l =
      g.inner x ((chartModelBasis E) k : TangentSpace I x)
        ((chartModelBasis E) l : TangentSpace I x) := by
  rw [chartGramMatrix_apply, chartBasisVecFiber_self (I := I) x k,
    chartBasisVecFiber_self (I := I) x l]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartGramMatrix_eq_cob_conj (g : SmoothRiemannianMetric I M)
    (α : M) (x : M) :
    chartGramMatrix (I := I) g α x =
      deTurckCobMatrix (I := I) α x *
        chartGramMatrix (I := I) g x x *
        (deTurckCobMatrix (I := I) α x)ᵀ := by
  classical
  set P := deTurckCobMatrix (I := I) α x with hP_def
  ext i j
  rw [chartGramMatrix_apply]
  have hbilinear :
      g.inner x (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x)
        = ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (P i k * P j l) *
              g.inner x ((chartModelBasis E) k : TangentSpace I x)
                ((chartModelBasis E) l : TangentSpace I x) := by
    rw [chartBasisVecFiber_eq_sum_model (I := I) α x i,
        chartBasisVecFiber_eq_sum_model (I := I) α x j]
    exact clm_bilinear_expand_two_sums_scalar (n := Module.finrank ℝ E) g x
      (fun k => P i k) (fun l => P j l)
      (fun k => ((chartModelBasis E) k : TangentSpace I x))
      (fun l => ((chartModelBasis E) l : TangentSpace I x))
  rw [hbilinear]
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.transpose_apply, chartGramMatrix_self_eq_model (I := I) g x k l]
  ring

private def deTurckModelTrace (g g' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x :=
  ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
    (chartGramMatrix (I := I) g x x)⁻¹ p q •
      connDiff (I := I) g g' x
        ((chartModelBasis E) p : TangentSpace I x)
        ((chartModelBasis E) q : TangentSpace I x)

private lemma transpose_mul_conj_inv_mul
    {n : ℕ} (P Gx : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsUnit P) :
    Pᵀ * (P * Gx * Pᵀ)⁻¹ * P = Gx⁻¹ := by
  classical
  have hPdet : IsUnit P.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hP
  have hPtdet : IsUnit (Pᵀ).det := by rwa [Matrix.det_transpose]
  have hinv : (P * Gx * Pᵀ)⁻¹ = (Pᵀ)⁻¹ * (Gx⁻¹ * P⁻¹) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  rw [hinv]
  rw [show Pᵀ * ((Pᵀ)⁻¹ * (Gx⁻¹ * P⁻¹)) * P
        = (Pᵀ * (Pᵀ)⁻¹) * Gx⁻¹ * (P⁻¹ * P) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.mul_nonsing_inv _ hPtdet, Matrix.nonsing_inv_mul _ hPdet,
    Matrix.one_mul, Matrix.mul_one]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
private lemma deTurckChartLocal_eq_modelTrace (g g' : SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    deTurckChartLocal (I := I) g g' α x = deTurckModelTrace (I := I) g g' x := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set P := deTurckCobMatrix (I := I) α x with hP_def
  set Gx := chartGramMatrix (I := I) g x x with hGx_def
  set Gα := chartGramMatrix (I := I) g α x with hGα_def
  set A := connDiff (I := I) g g' x with hA_def
  set e := fun k : Fin n => ((chartModelBasis E) k : TangentSpace I x) with he_def
  have hP_unit : IsUnit P := deTurckCobMatrix_isUnit (I := I) α hx
  have hGα_eq : Gα = P * Gx * Pᵀ := chartGramMatrix_eq_cob_conj (I := I) g α x
  have hframe : ∀ j : Fin n,
      (chartBasisVecFiber (I := I) α j x : TangentSpace I x) =
        ∑ p : Fin n, P j p • e p := fun j =>
    chartBasisVecFiber_eq_sum_model (I := I) α x j
  rw [deTurckChartLocal_def]
  have hstep1 : ∀ j k : Fin n,
      A (chartBasisVecFiber (I := I) α j x)
          (chartBasisVecFiber (I := I) α k x) =
        ∑ p : Fin n, ∑ q : Fin n, (P j p * P k q) • A (e p) (e q) := by
    intro j k
    rw [hframe j, hframe k]
    exact clm_bilinear_expand_two_sums_vector A
      (fun p => P j p) (fun q => P k q) e e
  have hcoeff : ∀ j k : Fin n,
      chartInvGramMatrix (I := I) g α x j k = Gα⁻¹ j k := fun _ _ => rfl
  calc
    ∑ j : Fin n, ∑ k : Fin n,
        chartInvGramMatrix (I := I) g α x j k •
          A (chartBasisVecFiber (I := I) α j x)
            (chartBasisVecFiber (I := I) α k x)
        = ∑ j : Fin n, ∑ k : Fin n,
            Gα⁻¹ j k •
              ∑ p : Fin n, ∑ q : Fin n, (P j p * P k q) • A (e p) (e q) := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [hcoeff j k, hstep1 j k]
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q) := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [smul_smul]
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q) := by
          rw [show (∑ j : Fin n, ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
                (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q))
              = ∑ jk : Fin n × Fin n, ∑ pq : Fin n × Fin n,
                  (Gα⁻¹ jk.1 jk.2 * (P jk.1 pq.1 * P jk.2 pq.2)) •
                    A (e pq.1) (e pq.2) by
            rw [← Finset.sum_product', Finset.univ_product_univ]
            refine Finset.sum_congr rfl (fun jk _ => ?_)
            rw [← Finset.sum_product', Finset.univ_product_univ]]
          rw [show (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q))
              = ∑ pq : Fin n × Fin n, ∑ jk : Fin n × Fin n,
                  (Gα⁻¹ jk.1 jk.2 * (P jk.1 pq.1 * P jk.2 pq.2)) •
                    A (e pq.1) (e pq.2) by
            rw [← Finset.sum_product', Finset.univ_product_univ]
            refine Finset.sum_congr rfl (fun pq _ => ?_)
            rw [← Finset.sum_product', Finset.univ_product_univ]]
          rw [Finset.sum_comm]
    _ = ∑ p : Fin n, ∑ q : Fin n,
            (Pᵀ * Gα⁻¹ * P) p q • A (e p) (e q) := by
          refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
          have hpull : ∑ j : Fin n, ∑ k : Fin n,
                (Gα⁻¹ j k * (P j p * P k q)) • A (e p) (e q)
              = (∑ j : Fin n, ∑ k : Fin n, Gα⁻¹ j k * (P j p * P k q)) •
                  A (e p) (e q) := by
            rw [Finset.sum_smul]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Finset.sum_smul]
          rw [hpull]
          congr 1
          rw [Matrix.mul_apply]
          rw [show (∑ a : Fin n, (Pᵀ * Gα⁻¹) p a * P a q)
                = ∑ a : Fin n, ∑ b : Fin n,
                    P b p * Gα⁻¹ b a * P a q from ?_]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            refine Finset.sum_congr rfl (fun k _ => ?_)
            ring
          · refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Matrix.mul_apply, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [Matrix.transpose_apply]
    _ = ∑ p : Fin n, ∑ q : Fin n, Gx⁻¹ p q • A (e p) (e q) := by
          have hconj : Pᵀ * Gα⁻¹ * P = Gx⁻¹ := by
            rw [hGα_eq]
            exact transpose_mul_conj_inv_mul P Gx hP_unit
          rw [hconj]
    _ = deTurckModelTrace (I := I) g g' x := rfl

def deTurckFun (g g' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x :=
  deTurckChartLocal (I := I) g g' x x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
lemma deTurckFun_def (g g' : SmoothRiemannianMetric I M) (x : M) :
    deTurckFun (I := I) g g' x = deTurckChartLocal (I := I) g g' x x := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem deTurckChartLocal_eq_deTurckFun (g g' : SmoothRiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    deTurckChartLocal (I := I) g g' α x = deTurckFun (I := I) g g' x := by
  have hbase_x : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  rw [deTurckFun_def]
  rw [deTurckChartLocal_eq_modelTrace (I := I) g g' α hx,
    deTurckChartLocal_eq_modelTrace (I := I) g g' x hbase_x]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem deTurckChartLocal_eq_deTurckFun_of_mem_source
    (g g' : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    deTurckChartLocal (I := I) g g' α x = deTurckFun (I := I) g g' x := by
  refine deTurckChartLocal_eq_deTurckFun (I := I) g g' α ?_
  rwa [trivializationAt_baseSet_eq_chartAt_source]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
lemma deTurckChartLocal_self (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    deTurckChartLocal (I := I) g g α x = (0 : TangentSpace I x) := by
  classical
  rw [deTurckChartLocal_def]
  refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ => ?_))
  rw [connDiff_self (I := I) g]
  simp

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
@[simp]
theorem deTurckFun_self (g : SmoothRiemannianMetric I M) :
    deTurckFun (I := I) g g = fun x => (0 : TangentSpace I x) := by
  funext x
  rw [deTurckFun_def]
  exact deTurckChartLocal_self (I := I) g x x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem deTurckFun_self_apply (g : SmoothRiemannianMetric I M) (x : M) :
    deTurckFun (I := I) g g x = (0 : TangentSpace I x) := by
  rw [deTurckFun_self]

end DeTurck
end PDE
end DifferentialGeometry
