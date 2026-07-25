import DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol
import DifferentialGeometry.Geometry.Flow.VectorField


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

def chartLieMetricConvective (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    chartCoeff (I := I) α W k x *
      partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (extChartAt I α x)

def chartLieMetricDeform (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    chartGramMatrix (I := I) g α x k j *
      partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k) (extChartAt I α x)

def chartLieDerivMetricMatrix (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  chartLieMetricConvective (I := I) g W α i j x +
    chartLieMetricDeform (I := I) g W α i j x +
    chartLieMetricDeform (I := I) g W α j i x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartLieMetricConvective_def (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartLieMetricConvective (I := I) g W α i j x =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α W k x *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
            (extChartAt I α x) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartLieMetricDeform_def (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartLieMetricDeform (I := I) g W α i j x =
      ∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g α x k j *
          partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k)
            (extChartAt I α x) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLieDerivMetricMatrix_def (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartLieDerivMetricMatrix (I := I) g W α i j x =
      (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α W k x *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
              (extChartAt I α x))
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x k j *
            partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k)
              (extChartAt I α x))
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i k *
            partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k)
              (extChartAt I α x)) := by
  classical
  rw [chartLieDerivMetricMatrix, chartLieMetricConvective_def,
    chartLieMetricDeform_def, chartLieMetricDeform_def]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show chartGramMatrix (I := I) g α x k i =
      chartGramMatrix (I := I) g α x i k from by
    rw [chartGramMatrix_apply, chartGramMatrix_apply]
    exact g.symm x _ _]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartLieMetricConvective_symm (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartLieMetricConvective (I := I) g W α i j x =
      chartLieMetricConvective (I := I) g W α j i x := by
  classical
  rw [chartLieMetricConvective_def, chartLieMetricConvective_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hsym : chartGramOnE (I := I) g α i j = chartGramOnE (I := I) g α j i :=
    funext (fun y => chartGramOnE_symm (I := I) g α i j y)
  rw [hsym]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLieDerivMetricMatrix_symm (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartLieDerivMetricMatrix (I := I) g W α i j x =
      chartLieDerivMetricMatrix (I := I) g W α j i x := by
  rw [chartLieDerivMetricMatrix, chartLieDerivMetricMatrix]
  rw [chartLieMetricConvective_symm (I := I) g W α i j]
  ring

def lieDerivMetricMatrix (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i j : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  chartLieDerivMetricMatrix (I := I) g W x i j x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma lieDerivMetricMatrix_def_chart (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    lieDerivMetricMatrix (I := I) g W i j x =
      chartLieDerivMetricMatrix (I := I) g W x i j x := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetricMatrix_def (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    lieDerivMetricMatrix (I := I) g W i j x =
      (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) x W k x *
            partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
              (extChartAt I x x))
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k j *
            partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x))
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x i k *
            partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x)) := by
  rw [lieDerivMetricMatrix, chartLieDerivMetricMatrix_def]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetricMatrix_symm (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    lieDerivMetricMatrix (I := I) g W i j x =
      lieDerivMetricMatrix (I := I) g W j i x := by
  rw [lieDerivMetricMatrix, lieDerivMetricMatrix,
    chartLieDerivMetricMatrix_symm (I := I) g W x i j]

def lieDerivMetric (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    pointwiseBilin (M := M) I :=
  fun x => LinearMap.mk₂ ℝ
    (fun v w =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) j *
            lieDerivMetricMatrix (I := I) g W i j x)
    (fun v₁ v₂ w => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (v₁ + v₂) =
          (chartModelBasis E).repr v₁ + (chartModelBasis E).repr v₂ := map_add _ _ _
      rw [hrepr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
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
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring)
    (fun v w₁ w₂ => by
      classical
      dsimp only
      have hrepr : (chartModelBasis E).repr (w₁ + w₂) =
          (chartModelBasis E).repr w₁ + (chartModelBasis E).repr w₂ := map_add _ _ _
      rw [hrepr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
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
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma lieDerivMetric_apply (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (v w : TangentSpace I x) :
    lieDerivMetric (I := I) g W x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
            ((chartModelBasis E).repr w) j *
            lieDerivMetricMatrix (I := I) g W i j x :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma lieDerivMetric_basis_apply (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    lieDerivMetric (I := I) g W x
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      lieDerivMetricMatrix (I := I) g W i j x := by
  classical
  rw [lieDerivMetric_apply]
  conv_lhs => rw [show
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
            ((chartModelBasis E).repr ((chartModelBasis E) j)) j' *
            lieDerivMetricMatrix (I := I) g W i' j' x) =
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          (if i = i' then (1 : ℝ) else 0) *
            (if j = j' then (1 : ℝ) else 0) *
            lieDerivMetricMatrix (I := I) g W i' j' x) from
      Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => by
        rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]))]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'_ne
      have hjj' : ¬ j = j' := fun h => hj'_ne h.symm
      simp [hjj']
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'_ne
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    have hii' : ¬ i = i' := fun h => hi'_ne h.symm
    simp [hii']
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetric_isPointwiseSymm (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    IsPointwiseSymm (lieDerivMetric (I := I) (M := M) g W) := by
  intro x v w
  classical
  rw [lieDerivMetric_apply, lieDerivMetric_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [lieDerivMetricMatrix_symm (I := I) g W j i]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartCoeff_zero_of_mem (α : M) (k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartCoeff (I := I) α (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x = 0 := by
  rw [chartCoeff_def]
  have hsec : (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x
      = (0 : TangentSpace I x) := rfl
  have hzero : ((trivializationAt E (TangentSpace I) α)
      ⟨x, (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x⟩).2 = 0 := by
    rw [hsec]
    have h := (trivializationAt E (TangentSpace I) α).zeroSection
      (R := ℝ) (E := (TangentSpace I : M → Type _)) hx
    exact congrArg Prod.snd h
  rw [hzero, map_zero]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartCoeffOnE_zero_of_mem (α : M) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartCoeffOnE (I := I) α (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k y = 0 := by
  rw [chartCoeffOnE]
  refine chartCoeff_zero_of_mem (I := I) α k ?_
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rwa [trivializationAt_baseSet_eq_chartAt_source]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem lieDerivMetricMatrix_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    lieDerivMetricMatrix (I := I) g
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i j x = 0 := by
  classical
  rw [lieDerivMetricMatrix_def]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target := by
    refine (extChartAt I x).map_source ?_
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hconv : (∑ k : Fin (Module.finrank ℝ E),
      chartCoeff (I := I) x (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k x *
        partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
          (extChartAt I x x)) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [chartCoeff_zero_of_mem (I := I) x k hxbase, zero_mul]
  have hdeform : ∀ (c : Fin (Module.finrank ℝ E) → ℝ)
      (b : Fin (Module.finrank ℝ E)),
      (∑ k : Fin (Module.finrank ℝ E),
        c k *
          partialDeriv (E := E) b
            (chartCoeffOnE (I := I) x
              (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k)
            (extChartAt I x x)) = 0 := by
    intro c b
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hzeroOn : ∀ z ∈ (extChartAt I x).target,
        chartCoeffOnE (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k z = 0 :=
      fun z hz => chartCoeffOnE_zero_of_mem (I := I) x k hz
    have hpd : partialDeriv (E := E) b
        (chartCoeffOnE (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k)
        (extChartAt I x x) = 0 := by
      rw [partialDeriv]
      have htargetnhds : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
        (isOpen_extChartAt_target (I := I) x).mem_nhds hxtgt
      have heq : chartCoeffOnE (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) k
          =ᶠ[𝓝 (extChartAt I x x)] (fun _ : E => (0 : ℝ)) := by
        filter_upwards [htargetnhds] with z hz using hzeroOn z hz
      rw [heq.fderiv_eq]
      simp
    rw [hpd, mul_zero]
  rw [hconv, hdeform (fun k => chartGramMatrix (I := I) g x x k j) i,
    hdeform (fun k => chartGramMatrix (I := I) g x x i k) j]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem lieDerivMetric_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    lieDerivMetric (I := I) (M := M) g
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (fun _ => 0 : pointwiseBilin (M := M) I) := by
  funext x
  refine LinearMap.ext (fun v => LinearMap.ext (fun w => ?_))
  rw [lieDerivMetric_apply]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  rw [lieDerivMetricMatrix_zero (I := I) g i j x]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartCoeff_add_of_mem (α : M) (k : Fin (Module.finrank ℝ E))
    (W₁ W₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartCoeff (I := I) α (W₁ + W₂) k x =
      chartCoeff (I := I) α W₁ k x + chartCoeff (I := I) α W₂ k x := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with hT_def
  have hadd : (T ⟨x, (W₁ + W₂) x⟩).2 = (T ⟨x, W₁ x⟩).2 + (T ⟨x, W₂ x⟩).2 := by
    have h := (T.linear ℝ hx).map_add (W₁ x) (W₂ x)
    change (T ⟨x, W₁ x + W₂ x⟩).2 = (T ⟨x, W₁ x⟩).2 + (T ⟨x, W₂ x⟩).2
    exact h
  rw [chartCoeff_def, chartCoeff_def, chartCoeff_def, hadd,
    LinearEquiv.map_add, Finsupp.add_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartCoeff_smul_of_mem (α : M) (k : Fin (Module.finrank ℝ E))
    (c : ℝ) (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartCoeff (I := I) α (c • W) k x = c * chartCoeff (I := I) α W k x := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with hT_def
  have hsmul : (T ⟨x, (c • W) x⟩).2 = c • (T ⟨x, W x⟩).2 := by
    have h := (T.linear ℝ hx).map_smul c (W x)
    change (T ⟨x, c • W x⟩).2 = c • (T ⟨x, W x⟩).2
    exact h
  rw [chartCoeff_def, chartCoeff_def, hsmul, LinearEquiv.map_smul,
    Finsupp.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartCoeffOnE_add_of_mem (α : M) (k : Fin (Module.finrank ℝ E))
    (W₁ W₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartCoeffOnE (I := I) α (W₁ + W₂) k y =
      chartCoeffOnE (I := I) α W₁ k y + chartCoeffOnE (I := I) α W₂ k y := by
  rw [chartCoeffOnE, chartCoeffOnE, chartCoeffOnE]
  refine chartCoeff_add_of_mem (I := I) α k W₁ W₂ ?_
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rwa [trivializationAt_baseSet_eq_chartAt_source]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartCoeffOnE_smul_of_mem (α : M) (k : Fin (Module.finrank ℝ E))
    (c : ℝ) (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartCoeffOnE (I := I) α (c • W) k y =
      c * chartCoeffOnE (I := I) α W k y := by
  rw [chartCoeffOnE, chartCoeffOnE]
  refine chartCoeff_smul_of_mem (I := I) α k c W ?_
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  rwa [trivializationAt_baseSet_eq_chartAt_source]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetricMatrix_add_vectorField [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W₁ W₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    lieDerivMetricMatrix (I := I) g (W₁ + W₂) i j x =
      lieDerivMetricMatrix (I := I) g W₁ i j x +
        lieDerivMetricMatrix (I := I) g W₂ i j x := by
  classical
  rw [lieDerivMetricMatrix_def, lieDerivMetricMatrix_def, lieDerivMetricMatrix_def]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact mem_chart_source H x
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target := by
    refine (extChartAt I x).map_source ?_
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact mem_chart_source H x
  have htargetnhds : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hxtgt
  have hconv :
      (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) x (W₁ + W₂) k x *
            partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
              (extChartAt I x x))
        = (∑ k : Fin (Module.finrank ℝ E),
            chartCoeff (I := I) x W₁ k x *
              partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
                (extChartAt I x x))
          + (∑ k : Fin (Module.finrank ℝ E),
              chartCoeff (I := I) x W₂ k x *
                partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
                  (extChartAt I x x)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartCoeff_add_of_mem (I := I) x k W₁ W₂ hxbase]
    ring
  have hdeform : ∀ (c : Fin (Module.finrank ℝ E) → ℝ)
      (b : Fin (Module.finrank ℝ E)),
      (∑ k : Fin (Module.finrank ℝ E),
          c k *
            partialDeriv (E := E) b (chartCoeffOnE (I := I) x (W₁ + W₂) k)
              (extChartAt I x x))
        = (∑ k : Fin (Module.finrank ℝ E),
            c k *
              partialDeriv (E := E) b (chartCoeffOnE (I := I) x W₁ k)
                (extChartAt I x x))
          + (∑ k : Fin (Module.finrank ℝ E),
              c k *
                partialDeriv (E := E) b (chartCoeffOnE (I := I) x W₂ k)
                  (extChartAt I x x)) := by
    intro c b
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hpd : partialDeriv (E := E) b
        (chartCoeffOnE (I := I) x (W₁ + W₂) k) (extChartAt I x x) =
        partialDeriv (E := E) b (chartCoeffOnE (I := I) x W₁ k) (extChartAt I x x) +
          partialDeriv (E := E) b (chartCoeffOnE (I := I) x W₂ k)
            (extChartAt I x x) := by
      rw [partialDeriv, partialDeriv, partialDeriv]
      have heq : chartCoeffOnE (I := I) x (W₁ + W₂) k
          =ᶠ[𝓝 (extChartAt I x x)]
            (fun z => chartCoeffOnE (I := I) x W₁ k z +
              chartCoeffOnE (I := I) x W₂ k z) := by
        filter_upwards [htargetnhds] with z hz
        exact chartCoeffOnE_add_of_mem (I := I) x k W₁ W₂ hz
      rw [heq.fderiv_eq]
      have hsmooth₁ : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x W₁ k)
          (extChartAt I x).target := chartCoeffOnE_contDiffOn (I := I) x W₁ k
      have hsmooth₂ : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x W₂ k)
          (extChartAt I x).target := chartCoeffOnE_contDiffOn (I := I) x W₂ k
      have hdiff₁ : DifferentiableAt ℝ (chartCoeffOnE (I := I) x W₁ k)
          (extChartAt I x x) :=
        ((hsmooth₁.contDiffAt htargetnhds).differentiableAt (by simp))
      have hdiff₂ : DifferentiableAt ℝ (chartCoeffOnE (I := I) x W₂ k)
          (extChartAt I x x) :=
        ((hsmooth₂.contDiffAt htargetnhds).differentiableAt (by simp))
      rw [fderiv_fun_add hdiff₁ hdiff₂]
      rfl
    rw [hpd]
    ring
  rw [hconv, hdeform (fun k => chartGramMatrix (I := I) g x x k j) i,
    hdeform (fun k => chartGramMatrix (I := I) g x x i k) j]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetricMatrix_smul_vectorField [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    lieDerivMetricMatrix (I := I) g (c • W) i j x =
      c * lieDerivMetricMatrix (I := I) g W i j x := by
  classical
  rw [lieDerivMetricMatrix_def, lieDerivMetricMatrix_def]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact mem_chart_source H x
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target := by
    refine (extChartAt I x).map_source ?_
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact mem_chart_source H x
  have htargetnhds : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hxtgt
  have hconv :
      (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) x (c • W) k x *
            partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
              (extChartAt I x x))
        = c * (∑ k : Fin (Module.finrank ℝ E),
            chartCoeff (I := I) x W k x *
              partialDeriv (E := E) k (chartGramOnE (I := I) g x i j)
                (extChartAt I x x)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartCoeff_smul_of_mem (I := I) x k c W hxbase]
    ring
  have hdeform : ∀ (a : Fin (Module.finrank ℝ E) → ℝ)
      (b : Fin (Module.finrank ℝ E)),
      (∑ k : Fin (Module.finrank ℝ E),
          a k *
            partialDeriv (E := E) b (chartCoeffOnE (I := I) x (c • W) k)
              (extChartAt I x x))
        = c * (∑ k : Fin (Module.finrank ℝ E),
            a k *
              partialDeriv (E := E) b (chartCoeffOnE (I := I) x W k)
                (extChartAt I x x)) := by
    intro a b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hpd : partialDeriv (E := E) b
        (chartCoeffOnE (I := I) x (c • W) k) (extChartAt I x x) =
        c * partialDeriv (E := E) b (chartCoeffOnE (I := I) x W k)
          (extChartAt I x x) := by
      rw [partialDeriv, partialDeriv]
      have heq : chartCoeffOnE (I := I) x (c • W) k
          =ᶠ[𝓝 (extChartAt I x x)]
            (fun z => c • chartCoeffOnE (I := I) x W k z) := by
        filter_upwards [htargetnhds] with z hz
        rw [chartCoeffOnE_smul_of_mem (I := I) x k c W hz, smul_eq_mul]
      have hsmooth : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x W k)
          (extChartAt I x).target := chartCoeffOnE_contDiffOn (I := I) x W k
      have hdiff : DifferentiableAt ℝ (chartCoeffOnE (I := I) x W k)
          (extChartAt I x x) :=
        (hsmooth.contDiffAt htargetnhds).differentiableAt (by simp)
      rw [heq.fderiv_eq, fderiv_fun_const_smul hdiff,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hpd]
    ring
  rw [hconv, hdeform (fun k => chartGramMatrix (I := I) g x x k j) i,
    hdeform (fun k => chartGramMatrix (I := I) g x x i k) j]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetric_add_vectorField [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W₁ W₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (v w : TangentSpace I x) :
    lieDerivMetric (I := I) g (W₁ + W₂) x v w =
      lieDerivMetric (I := I) g W₁ x v w + lieDerivMetric (I := I) g W₂ x v w := by
  classical
  rw [lieDerivMetric_apply, lieDerivMetric_apply, lieDerivMetric_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [lieDerivMetricMatrix_add_vectorField (I := I) g W₁ W₂ i j x]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem lieDerivMetric_smul_vectorField [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (v w : TangentSpace I x) :
    lieDerivMetric (I := I) g (c • W) x v w =
      c * lieDerivMetric (I := I) g W x v w := by
  classical
  rw [lieDerivMetric_apply, lieDerivMetric_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [lieDerivMetricMatrix_smul_vectorField (I := I) g c W i j x]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma partialDeriv_chartGramOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) k (chartGramOnE (I := I) g α i j))
      (interior (extChartAt I α).target) := by
  have hbase : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target :=
    chartGramOnE_contDiffOn (I := I) g α i j
  have hbase_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α i j))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) k)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma partialDeriv_chartCoeffOnE_contDiffOn_interior
    (α : M) (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k))
      (interior (extChartAt I α).target) := by
  have hbase : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) α W k)
      (extChartAt I α).target :=
    chartCoeffOnE_contDiffOn (I := I) α W k
  have hbase_int : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) α W k)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartCoeffOnE (I := I) α W k))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma comp_extChartAt_contMDiffOn_source [I.Boundaryless]
    (α : M) {u : E → ℝ}
    (hu : ContDiffOn ℝ ∞ u (interior (extChartAt I α).target)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => u (extChartAt I α x)) (chartAt H α).source := by
  have huM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u
      (interior (extChartAt I α).target) := hu.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hmaps : MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (interior (extChartAt I α).target) := by
    intro x hx
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
    have hxtgt : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hxtgt
  exact huM.comp hchart hmaps

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartLieMetricConvective_summand_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartCoeff (I := I) α W k x *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
            (extChartAt I α x))
      (chartAt H α).source := by
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartCoeff (I := I) α W k)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartCoeff_contMDiffOn (I := I) α W k
    rwa [trivializationAt_baseSet_eq_chartAt_source] at h1
  · exact comp_extChartAt_contMDiffOn_source (I := I) α
      (partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α i j k)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartLieMetricDeform_summand_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        chartGramMatrix (I := I) g α x k j *
          partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k)
            (extChartAt I α x))
      (chartAt H α).source := by
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => chartGramMatrix (I := I) g α x k j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartGramMatrix_entry_contMDiffOn (I := I) g α k j
    rwa [trivializationAt_baseSet_eq_chartAt_source] at h1
  · exact comp_extChartAt_contMDiffOn_source (I := I) α
      (partialDeriv_chartCoeffOnE_contDiffOn_interior (I := I) α W i k)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartLieMetricConvective_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (chartLieMetricConvective (I := I) g W α i j) (chartAt H α).source := by
  refine ContMDiffOn.congr ?_ (fun x _ => (chartLieMetricConvective_def
    (I := I) g W α i j x))
  exact contMDiffOn_finset_sum (fun k _ =>
    chartLieMetricConvective_summand_contMDiffOn (I := I) g W α i j k)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartLieMetricDeform_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (chartLieMetricDeform (I := I) g W α i j) (chartAt H α).source := by
  refine ContMDiffOn.congr ?_ (fun x _ => (chartLieMetricDeform_def
    (I := I) g W α i j x))
  exact contMDiffOn_finset_sum (fun k _ =>
    chartLieMetricDeform_summand_contMDiffOn (I := I) g W α i j k)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLieDerivMetricMatrix_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (chartLieDerivMetricMatrix (I := I) g W α i j) (chartAt H α).source := by
  have hconv := chartLieMetricConvective_contMDiffOn (I := I) g W α i j
  have hdef1 := chartLieMetricDeform_contMDiffOn (I := I) g W α i j
  have hdef2 := chartLieMetricDeform_contMDiffOn (I := I) g W α j i
  exact (hconv.add hdef1).add hdef2

end DeTurck
end PDE
end DifferentialGeometry
