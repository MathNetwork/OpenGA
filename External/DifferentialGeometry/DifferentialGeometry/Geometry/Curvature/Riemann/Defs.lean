import DifferentialGeometry.Geometry.Operator.Hessian


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def chartRiemannTensor (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
    partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y +
    (∑ m : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g α j m l y *
          chartChristoffel (I := I) g α i k m y -
        chartChristoffel (I := I) g α k m l y *
          chartChristoffel (I := I) g α i j m y))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartRiemannTensor_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannTensor (I := I) g α i j k l y =
      partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y -
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j l) y +
        (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemannTensor_antisymm_jk
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannTensor (I := I) g α i j k l y =
      - chartRiemannTensor (I := I) g α i k j l y := by
  classical
  rw [chartRiemannTensor_def, chartRiemannTensor_def]
  have hsum :
      (∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y -
            chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y)) =
      -(∑ m : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g α k m l y *
              chartChristoffel (I := I) g α i j m y -
            chartChristoffel (I := I) g α j m l y *
              chartChristoffel (I := I) g α i k m y)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro m _
    ring
  rw [hsum]
  ring

def chartRicciTensor (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartRiemannTensor (I := I) g α i j k j y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartRicciTensor_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciTensor (I := I) g α i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α i j k j y := rfl

def ricciFun (g : SmoothRiemannianMetric I M) :
    pointwiseBilin (M := M) I :=
  fun x => LinearMap.mk₂ ℝ
    (fun v w =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) k *
            chartRicciTensor (I := I) g x i k (extChartAt I x x))
    (fun v₁ v₂ w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (v₁ + v₂) =
          (chartModelBasis E).repr v₁ + (chartModelBasis E).repr v₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (c • v) =
          c • (chartModelBasis E).repr v := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring)
    (fun v w₁ w₂ => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (w₁ + w₂) =
          (chartModelBasis E).repr w₁ + (chartModelBasis E).repr w₂ := map_add _ _ _
      rw [hrepr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      simp only [Finsupp.coe_add, Pi.add_apply]
      ring)
    (fun c v w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (c • w) =
          c • (chartModelBasis E).repr w := map_smul _ _ _
      rw [hrepr]
      simp only [smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring)

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciFun_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciFun (I := I) g x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) k *
            chartRicciTensor (I := I) g x i k (extChartAt I x x) := by
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma ricciFun_basis_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciFun (I := I) g x
        ((chartModelBasis E) i) ((chartModelBasis E) k) =
      chartRicciTensor (I := I) g x i k (extChartAt I x x) := by
  classical
  rw [ricciFun_apply]
  conv_lhs => rw [show
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ k' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
            ((chartModelBasis E).repr ((chartModelBasis E) k)) k' *
            chartRicciTensor (I := I) g x i' k' (extChartAt I x x)) =
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ k' : Fin (Module.finrank ℝ E),
          (if i = i' then (1 : ℝ) else 0) *
            (if k = k' then (1 : ℝ) else 0) *
            chartRicciTensor (I := I) g x i' k' (extChartAt I x x)) from
      Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun k' _ => by
        rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]))]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'_ne
      have hkk' : ¬ k = k' := fun h => hk'_ne h.symm
      simp [hkk']
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · intro i' _ hi'_ne
    apply Finset.sum_eq_zero
    intro k' _
    have hii' : ¬ i = i' := fun h => hi'_ne h.symm
    simp [hii']
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciFun_symm_of_chartRicciTensor_symm
    (g : SmoothRiemannianMetric I M)
    (h_chart_symm : ∀ x : M, ∀ i k : Fin (Module.finrank ℝ E),
        chartRicciTensor (I := I) g x i k (extChartAt I x x) =
          chartRicciTensor (I := I) g x k i (extChartAt I x x)) :
    IsPointwiseSymm (ricciFun (I := I) (M := M) g) := by
  intro x v w
  classical
  rw [ricciFun_apply, ricciFun_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [h_chart_symm x k i]
  ring

end DivergenceTheorem
end Integral
end DifferentialGeometry
