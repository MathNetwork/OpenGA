import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric

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

def deTurckOp (g g' : SmoothRiemannianMetric I M) :
    pointwiseBilin (M := M) I :=
  fun x => (-2 : ℝ) • ricciFun (I := I) g x +
    lieDerivMetric (I := I) g (deTurckVF (I := I) g g') x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma deTurckOp_def (g g' : SmoothRiemannianMetric I M) (x : M) :
    deTurckOp (I := I) g g' x =
      (-2 : ℝ) • ricciFun (I := I) g x +
        lieDerivMetric (I := I) g (deTurckVF (I := I) g g') x := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckOp_apply (g g' : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    deTurckOp (I := I) g g' x v w =
      -2 * ricciFun (I := I) g x v w +
        lieDerivMetric (I := I) g (deTurckVF (I := I) g g') x v w := by
  rw [deTurckOp_def, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckOp_self [I.Boundaryless] (g : SmoothRiemannianMetric I M) :
    deTurckOp (I := I) g g = fun x => (-2 : ℝ) • ricciFun (I := I) g x := by
  funext x
  rw [deTurckOp_def, deTurckVF_self (I := I) g, lieDerivMetric_zero (I := I) g]
  rw [add_zero]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckOp_self_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    deTurckOp (I := I) g g x v w = -2 * ricciFun (I := I) g x v w := by
  rw [deTurckOp_apply, deTurckVF_self (I := I) g, lieDerivMetric_zero (I := I) g]
  simp

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckOp_isPointwiseSymm [I.Boundaryless]
    (g g' : SmoothRiemannianMetric I M) :
    IsPointwiseSymm (deTurckOp (I := I) (M := M) g g') := by
  intro x v w
  rw [deTurckOp_apply, deTurckOp_apply]
  rw [ricciFun_isPointwiseSymm_of_boundaryless (I := I) g x v w,
    lieDerivMetric_isPointwiseSymm (I := I) g (deTurckVF (I := I) g g') x v w]

def chartDeTurckOpMatrix (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  -2 * chartRicciTensor (I := I) g x i j (extChartAt I x x) +
    lieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g') i j x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma chartDeTurckOpMatrix_def (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartDeTurckOpMatrix (I := I) g g' i j x =
      -2 * chartRicciTensor (I := I) g x i j (extChartAt I x x) +
        lieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g') i j x := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckOp_basis_apply (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    deTurckOp (I := I) g g' x
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      chartDeTurckOpMatrix (I := I) g g' i j x := by
  rw [deTurckOp_apply, chartDeTurckOpMatrix_def,
    ricciFun_basis_apply (I := I) g x i j,
    lieDerivMetric_basis_apply (I := I) g (deTurckVF (I := I) g g') x i j]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartDeTurckOpMatrix_eq (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartDeTurckOpMatrix (I := I) g g' i j x =
      -2 * chartRicciTensor (I := I) g x i j (extChartAt I x x)
      + ((∑ k : Fin (Module.finrank ℝ E),
            chartCoeff (I := I) x (deTurckVF (I := I) g g') k x *
              partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
                (extChartAt I x x))
          + (∑ k : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g x x k j *
                partialDeriv (E := E) i
                  (chartCoeffOnE (I := I) x (deTurckVF (I := I) g g') k)
                  (extChartAt I x x))
          + (∑ k : Fin (Module.finrank ℝ E),
              chartGramMatrix (I := I) g x x i k *
                partialDeriv (E := E) j
                  (chartCoeffOnE (I := I) x (deTurckVF (I := I) g g') k)
                  (extChartAt I x x))) := by
  rw [chartDeTurckOpMatrix_def, lieDerivMetricMatrix_def]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartDeTurckOpMatrix_symm [I.Boundaryless]
    (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartDeTurckOpMatrix (I := I) g g' i j x =
      chartDeTurckOpMatrix (I := I) g g' j i x := by
  rw [chartDeTurckOpMatrix_def, chartDeTurckOpMatrix_def,
    lieDerivMetricMatrix_symm (I := I) g (deTurckVF (I := I) g g') i j,
    chartRicciTensor_symm_of_boundaryless (I := I) g x i j (mem_chart_source H x)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartDeTurckOpMatrix_contMDiffOn (g g' : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (α : M)
    (hRic : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => chartRicciTensor (I := I) g x i j (extChartAt I x x))
      (chartAt H α).source)
    (hLie : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (lieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g') i j)
      (chartAt H α).source) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (chartDeTurckOpMatrix (I := I) g g' i j) (chartAt H α).source := by
  refine ContMDiffOn.congr ?_ (fun x _ => chartDeTurckOpMatrix_def
    (I := I) g g' i j x)
  exact ((contMDiffOn_const (c := (-2 : ℝ))).mul hRic).add hLie

end DeTurck
end PDE
end DifferentialGeometry
