import DifferentialGeometry.Geometry.Operator.HessianTrace


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev OperatorSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] : Type _ :=
  ∀ x : M, E → (F x →ₗ[ℝ] F x)

variable (I M) in

abbrev TensorSymbol : Type _ :=
  OperatorSymbol (E := E)
    (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)

variable (M) in

abbrev ScalarSymbol : Type _ :=
  OperatorSymbol (E := E) (fun _ : M => ℝ)

def metricCovectorNormSq (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j *
        ((chartModelBasis E).repr ξ i) * ((chartModelBasis E).repr ξ j)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma metricCovectorNormSq_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    metricCovectorNormSq (I := I) g x ξ =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            ((chartModelBasis E).repr ξ i) * ((chartModelBasis E).repr ξ j) := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma metricCovectorNormSq_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricCovectorNormSq (I := I) g x 0 = 0 := by
  simp [metricCovectorNormSq]

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartInvGramMatrix_self_posDef (g : SmoothRiemannianMetric I M) (x : M) :
    (chartInvGramMatrix (I := I) g x x).PosDef := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hG : (chartGramMatrix (I := I) g x x).PosDef :=
    chartGramMatrix_posDef (I := I) g x hx
  rw [chartInvGramMatrix]
  exact hG.inv

omit [NeZero (Module.finrank ℝ E)] in
private lemma metricCovectorNormSq_eq_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    metricCovectorNormSq (I := I) g x ξ =
      star (fun i => (chartModelBasis E).repr ξ i) ⬝ᵥ
        (chartInvGramMatrix (I := I) g x x) *ᵥ
          (fun i => (chartModelBasis E).repr ξ i) := by
  classical
  rw [metricCovectorNormSq_def]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem metricCovectorNormSq_nonneg (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    0 ≤ metricCovectorNormSq (I := I) g x ξ := by
  classical
  rw [metricCovectorNormSq_eq_dotProduct_mulVec]
  exact (chartInvGramMatrix_self_posDef (I := I) g x).posSemidef.dotProduct_mulVec_nonneg _

omit [NeZero (Module.finrank ℝ E)] in
theorem metricCovectorNormSq_pos (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) :
    0 < metricCovectorNormSq (I := I) g x ξ := by
  classical
  rw [metricCovectorNormSq_eq_dotProduct_mulVec]
  have hcoord : (fun i => (chartModelBasis E).repr ξ i) ≠ 0 := by
    intro hzero
    apply hξ
    have hrepr : (chartModelBasis E).repr ξ = 0 := by
      ext i
      exact congrFun hzero i
    have := congrArg (chartModelBasis E).repr.symm hrepr
    simpa using this
  exact (chartInvGramMatrix_self_posDef (I := I) g x).dotProduct_mulVec_pos hcoord

def isotropicSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) :
    OperatorSymbol (E := E) F :=
  fun x ξ => (c x ξ) • LinearMap.id

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] in
@[simp] lemma isotropicSymbol_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) (x : M) (ξ : E) :
    isotropicSymbol (E := E) F c x ξ = (c x ξ) • LinearMap.id := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] in
@[simp] lemma isotropicSymbol_apply_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (c : M → E → ℝ) (x : M) (ξ : E)
    (v : F x) :
    isotropicSymbol (E := E) F c x ξ v = (c x ξ) • v := by
  rw [isotropicSymbol_apply]
  rfl

def deTurckSymbolCoeff (g : SmoothRiemannianMetric I M) : M → E → ℝ :=
  fun x ξ => -metricCovectorNormSq (I := I) g x ξ

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma deTurckSymbolCoeff_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    deTurckSymbolCoeff (I := I) g x ξ = -metricCovectorNormSq (I := I) g x ξ := rfl

def IsStrictlyParabolic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (g : SmoothRiemannianMetric I M) (σ : OperatorSymbol (E := E) F) : Prop :=
  ∀ x : M, ∀ ξ : E, ξ ≠ 0 →
    σ x ξ = isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g) x ξ

omit [NeZero (Module.finrank ℝ E)] in
lemma isStrictlyParabolic_iff (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (g : SmoothRiemannianMetric I M) (σ : OperatorSymbol (E := E) F) :
    IsStrictlyParabolic (E := E) F g σ ↔
      ∀ x : M, ∀ ξ : E, ξ ≠ 0 →
        σ x ξ = (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id :=
  Iff.rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem isStrictlyParabolic_isotropic_deTurckSymbolCoeff (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) F g
      (isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g)) :=
  fun _ _ _ => rfl

def secondOrderSymbol (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
    OperatorSymbol (E := E) F :=
  fun x ξ =>
    (-∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          a x i j * ((chartModelBasis E).repr ξ i) * ((chartModelBasis E).repr ξ j)) •
      LinearMap.id

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] in
@[simp] lemma secondOrderSymbol_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x : M) (ξ : E) :
    secondOrderSymbol (E := E) F a x ξ =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            a x i j * ((chartModelBasis E).repr ξ i) *
              ((chartModelBasis E).repr ξ j)) • LinearMap.id := rfl

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] in
@[simp] lemma secondOrderSymbol_apply_apply (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)]
    (a : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x : M) (ξ : E) (v : F x) :
    secondOrderSymbol (E := E) F a x ξ v =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            a x i j * ((chartModelBasis E).repr ξ i) *
              ((chartModelBasis E).repr ξ j)) • v := by
  rw [secondOrderSymbol_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem secondOrderSymbol_invGram_eq_isotropic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    secondOrderSymbol (E := E) F (fun x => chartInvGramMatrix (I := I) g x x) =
      isotropicSymbol (E := E) F (deTurckSymbolCoeff (I := I) g) := by
  funext x ξ
  rw [secondOrderSymbol_apply, isotropicSymbol_apply, deTurckSymbolCoeff_apply,
    metricCovectorNormSq_def]

omit [NeZero (Module.finrank ℝ E)] in
theorem secondOrderSymbol_invGram_isStrictlyParabolic (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) F g
      (secondOrderSymbol (E := E) F (fun x => chartInvGramMatrix (I := I) g x x)) := by
  rw [secondOrderSymbol_invGram_eq_isotropic]
  exact isStrictlyParabolic_isotropic_deTurckSymbolCoeff (E := E) F g

def laplacianSymbol (g : SmoothRiemannianMetric I M) : ScalarSymbol (E := E) M :=
  secondOrderSymbol (E := E) (fun _ : M => ℝ)
    (fun x => chartInvGramMatrix (I := I) g x x)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma laplacianSymbol_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    laplacianSymbol (I := I) g x ξ =
      (-∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              ((chartModelBasis E).repr ξ i) *
                ((chartModelBasis E).repr ξ j)) • LinearMap.id := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_eq_isotropic (g : SmoothRiemannianMetric I M) :
    laplacianSymbol (I := I) g =
      isotropicSymbol (E := E) (fun _ : M => ℝ) (deTurckSymbolCoeff (I := I) g) := by
  rw [laplacianSymbol, secondOrderSymbol_invGram_eq_isotropic]

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_apply_eq (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    laplacianSymbol (I := I) g x ξ =
      (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id := by
  rw [laplacianSymbol_eq_isotropic, isotropicSymbol_apply, deTurckSymbolCoeff_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_apply_apply (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : ℝ) :
    laplacianSymbol (I := I) g x ξ t =
      (-metricCovectorNormSq (I := I) g x ξ) • t := by
  rw [laplacianSymbol_apply_eq]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_isStrictlyParabolic (g : SmoothRiemannianMetric I M) :
    IsStrictlyParabolic (E := E) (fun _ : M => ℝ) g (laplacianSymbol (I := I) g) := by
  rw [laplacianSymbol_eq_isotropic]
  exact isStrictlyParabolic_isotropic_deTurckSymbolCoeff (E := E) (fun _ : M => ℝ) g

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianSymbol_neg_of_ne_zero (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) :
    laplacianSymbol (I := I) g x ξ =
        (-metricCovectorNormSq (I := I) g x ξ) • LinearMap.id ∧
      metricCovectorNormSq (I := I) g x ξ > 0 :=
  ⟨laplacianSymbol_apply_eq (I := I) g x ξ,
    metricCovectorNormSq_pos (I := I) g x hξ⟩

end DeTurck
end PDE
end DifferentialGeometry
