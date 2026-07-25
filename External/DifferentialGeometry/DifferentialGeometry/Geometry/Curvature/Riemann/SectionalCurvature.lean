import DifferentialGeometry.Geometry.Curvature.Riemann.Defs



noncomputable section

open Bundle Manifold Set Finset
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

def chartRiemannLower (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α l m y *
      chartRiemannTensor (I := I) g α i j k m y

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartRiemannLower_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannLower (I := I) g α i j k l y =
      ∑ m : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α l m y *
          chartRiemannTensor (I := I) g α i j k m y := rfl

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannLower_antisymm_jk
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannLower (I := I) g α i j k l y =
      - chartRiemannLower (I := I) g α i k j l y := by
  classical
  rw [chartRiemannLower_def, chartRiemannLower_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [chartRiemannTensor_antisymm_jk]
  ring

def sectionalCurvatureNumerator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) l *
            ((chartModelBasis E).repr w) i *
              ((chartModelBasis E).repr v) j *
                ((chartModelBasis E).repr w) k *
                  chartRiemannLower (I := I) g p i j k l (extChartAt I p p)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sectionalCurvatureNumerator_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) l *
                ((chartModelBasis E).repr w) i *
                  ((chartModelBasis E).repr v) j *
                    ((chartModelBasis E).repr w) k *
                      chartRiemannLower (I := I) g p i j k l
                        (extChartAt I p p) := rfl

def sectionalCurvatureDenominator (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sectionalCurvatureDenominator_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v w =
      g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 := rfl

def sectionalCurvature (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  sectionalCurvatureNumerator (I := I) g p v w /
    sectionalCurvatureDenominator (I := I) g p v w

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sectionalCurvature_def
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v w =
      sectionalCurvatureNumerator (I := I) g p v w /
        sectionalCurvatureDenominator (I := I) g p v w := rfl

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chart_metric_cauchy_schwarz
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    (g.inner p v w) ^ 2 ≤ g.inner p v v * g.inner p w w := by
  have hq_nonneg : ∀ t : ℝ, 0 ≤ g.inner p (t • v + w) (t • v + w) := by
    intro t
    by_cases htv : t • v + w = 0
    · rw [htv]; simp
    · exact (g.pos p _ htv).le
  have hq_expand : ∀ t : ℝ,
      g.inner p (t • v + w) (t • v + w) =
        t ^ 2 * g.inner p v v + 2 * t * g.inner p v w + g.inner p w w := by
    intro t
    have h_first : g.inner p (t • v + w) =
        t • g.inner p v + g.inner p w := by
      rw [map_add, map_smul]
    rw [h_first, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, ContinuousLinearMap.map_add, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
        smul_eq_mul, smul_eq_mul, g.symm p w v]
    ring
  have hA_nonneg : 0 ≤ g.inner p v v := by
    by_cases hv : v = 0
    · rw [hv]; simp
    · exact (g.pos p v hv).le
  have hC_nonneg : 0 ≤ g.inner p w w := by
    by_cases hw : w = 0
    · rw [hw]; simp
    · exact (g.pos p w hw).le
  by_cases hA_zero : g.inner p v v = 0
  · have hv_zero : v = 0 := by
      by_contra hv_ne
      exact absurd hA_zero (ne_of_gt (g.pos p v hv_ne))
    have hB_zero : g.inner p v w = 0 := by
      rw [hv_zero]
      simp
    rw [hB_zero, hA_zero]
    simp
  · have hA_pos : 0 < g.inner p v v :=
      lt_of_le_of_ne hA_nonneg (Ne.symm hA_zero)
    have h_at_t := hq_nonneg (-g.inner p v w / g.inner p v v)
    rw [hq_expand] at h_at_t
    have h_simplify :
        (-g.inner p v w / g.inner p v v) ^ 2 * g.inner p v v +
            2 * (-g.inner p v w / g.inner p v v) * g.inner p v w +
            g.inner p w w =
          g.inner p w w - (g.inner p v w) ^ 2 / g.inner p v v := by
      field_simp; ring
    rw [h_simplify] at h_at_t
    have h_expand :
        g.inner p v v *
          (g.inner p w w - (g.inner p v w) ^ 2 / g.inner p v v) =
          g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 := by
      field_simp
    have h_mul := mul_nonneg hA_pos.le h_at_t
    rw [h_expand] at h_mul
    linarith

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_nonneg
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    0 ≤ sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def]
  linarith [chart_metric_cauchy_schwarz (I := I) g p v w]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_eq_zero_of_left_smul
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p (c • v) v = 0 := by
  rw [sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hLL : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hL : g.inner p (c • v) v = c * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hLL, hL]; ring

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_eq_zero_of_right_smul
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v (c • v) = 0 := by
  rw [sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hRR : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hR : g.inner p v (c • v) = c * g.inner p v v := by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hRR, hR]; ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureNumerator_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p (c • v) w =
      c ^ 2 * sectionalCurvatureNumerator (I := I) g p v w := by
  classical
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def,
      Finset.mul_sum]
  refine Finset.sum_congr rfl ?_; intro i _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro j _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro k _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro l _
  have h_repr : (chartModelBasis E).repr (c • v) =
      c • (chartModelBasis E).repr v := map_smul _ _ _
  rw [h_repr]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureNumerator_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v (c • w) =
      c ^ 2 * sectionalCurvatureNumerator (I := I) g p v w := by
  classical
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def,
      Finset.mul_sum]
  refine Finset.sum_congr rfl ?_; intro i _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro j _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro k _
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro l _
  have h_repr : (chartModelBasis E).repr (c • w) =
      c • (chartModelBasis E).repr w := map_smul _ _ _
  rw [h_repr]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p (c • v) w =
      c ^ 2 * sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • v) = c • g.inner p v := map_smul _ _ _
  have hLL : g.inner p (c • v) (c • v) = c ^ 2 * g.inner p v v := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hL : g.inner p (c • v) w = c * g.inner p v w := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hLL, hL]; ring

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v (c • w) =
      c ^ 2 * sectionalCurvatureDenominator (I := I) g p v w := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  have h1 : g.inner p (c • w) = c • g.inner p w := map_smul _ _ _
  have hRR : g.inner p (c • w) (c • w) = c ^ 2 * g.inner p w w := by
    rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]; ring
  have hR : g.inner p v (c • w) = c * g.inner p v w := by
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [hRR, hR]; ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) w =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_def, sectionalCurvature_def,
      sectionalCurvatureNumerator_smul_left,
      sectionalCurvatureDenominator_smul_left,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (c • w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_def, sectionalCurvature_def,
      sectionalCurvatureNumerator_smul_right,
      sectionalCurvatureDenominator_smul_right,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_of_linearly_dependent_left
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) v = 0 := by
  rw [sectionalCurvature_def,
      sectionalCurvatureDenominator_eq_zero_of_left_smul]
  exact div_zero _

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_of_linearly_dependent_right
    (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (c • v) = 0 := by
  rw [sectionalCurvature_def,
      sectionalCurvatureDenominator_eq_zero_of_right_smul]
  exact div_zero _

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_self
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v v = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_left (I := I) g p 1 v
  rw [one_smul] at h; exact h

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_zero_left
    (g : SmoothRiemannianMetric I M) (p : M)
    (w : TangentSpace I p) :
    sectionalCurvature (I := I) g p 0 w = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_left (I := I) g p 0 w
  rw [zero_smul] at h; exact h

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_zero_right
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    sectionalCurvature (I := I) g p v 0 = 0 := by
  have h := sectionalCurvature_of_linearly_dependent_right (I := I) g p 0 v
  rw [zero_smul] at h; exact h

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_left
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-v) w =
      sectionalCurvature (I := I) g p v w := by
  have h := sectionalCurvature_smul_left (I := I) g p
    (c := (-1 : ℝ)) (by norm_num) v w
  rw [neg_one_smul] at h
  exact h

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_right
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (-w) =
      sectionalCurvature (I := I) g p v w := by
  have h := sectionalCurvature_smul_right (I := I) g p
    (c := (-1 : ℝ)) (by norm_num) v w
  rw [neg_one_smul] at h
  exact h

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_neg
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-v) (-w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_left (I := I) g p v (-w),
      sectionalCurvature_neg_right (I := I) g p v w]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_smul_smul
    (g : SmoothRiemannianMetric I M) (p : M) {c d : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (c • v) (d • w) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_smul_left (I := I) g p hc v (d • w),
      sectionalCurvature_smul_right (I := I) g p hd v w]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_smul_left
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p (-(c • v)) w =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_left (I := I) g p (c • v) w,
      sectionalCurvature_smul_left (I := I) g p hc v w]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_neg_smul_right
    (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : c ≠ 0)
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v (-(c • w)) =
      sectionalCurvature (I := I) g p v w := by
  rw [sectionalCurvature_neg_right (I := I) g p v (c • w),
      sectionalCurvature_smul_right (I := I) g p hc v w]

private lemma chartFourFold_reverse_sum
    {n : ℕ}
    (α β : Fin n → ℝ) (T : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        α l * β i * α j * β k * T i j k l) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        β l * α i * β j * α k * T l k j i) := by
  classical
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, l, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l]; rw [Finset.sum_comm]
  conv_lhs => enter [2, l, 2, k]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_; intro l _
  refine Finset.sum_congr rfl ?_; intro k _
  refine Finset.sum_congr rfl ?_; intro j _
  refine Finset.sum_congr rfl ?_; intro i _
  ring

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm
    (g : SmoothRiemannianMetric I M) (p : M)
    (h_pair : ∀ i j k l : Fin (Module.finrank ℝ E),
        chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
          - chartRiemannLower (I := I) g p l j k i (extChartAt I p p))
    (v w : TangentSpace I p) :
    sectionalCurvatureNumerator (I := I) g p v w =
      sectionalCurvatureNumerator (I := I) g p w v := by
  classical
  have h_combined : ∀ i j k l : Fin (Module.finrank ℝ E),
      chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
        chartRiemannLower (I := I) g p l k j i (extChartAt I p p) := by
    intro i j k l
    rw [chartRiemannLower_antisymm_jk (I := I) g p i j k l, h_pair i k j l]
    ring
  rw [sectionalCurvatureNumerator_def, sectionalCurvatureNumerator_def]
  refine Eq.trans ?_ (chartFourFold_reverse_sum (n := Module.finrank ℝ E)
    (α := fun i => ((chartModelBasis E).repr v) i)
    (β := fun i => ((chartModelBasis E).repr w) i)
    (T := fun a b c d =>
      chartRiemannLower (I := I) g p d c b a (extChartAt I p p)))
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [h_combined i j k l]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvatureDenominator_symm
    (g : SmoothRiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    sectionalCurvatureDenominator (I := I) g p v w =
      sectionalCurvatureDenominator (I := I) g p w v := by
  rw [sectionalCurvatureDenominator_def, sectionalCurvatureDenominator_def]
  rw [g.symm p v w]
  ring

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem sectionalCurvature_symm_of_chartRiemannLower_second_pair_antisymm
    (g : SmoothRiemannianMetric I M) (p : M)
    (h_pair : ∀ i j k l : Fin (Module.finrank ℝ E),
        chartRiemannLower (I := I) g p i j k l (extChartAt I p p) =
          - chartRiemannLower (I := I) g p l j k i (extChartAt I p p))
    (v w : TangentSpace I p) :
    sectionalCurvature (I := I) g p v w =
      sectionalCurvature (I := I) g p w v := by
  rw [sectionalCurvature_def, sectionalCurvature_def]
  rw [sectionalCurvatureNumerator_symm_of_chartRiemannLower_second_pair_antisymm
        (I := I) g p h_pair v w,
      sectionalCurvatureDenominator_symm (I := I) g p v w]

end Riemannian
end Geometry
end DifferentialGeometry
