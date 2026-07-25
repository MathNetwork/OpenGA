import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.ChartVectorField


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartGramOnE_det_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s) :
    ContinuousOn
      (fun t : ℝ => (Matrix.of fun i j => chartGramOnE (I := I) (g_DT t) α i j y).det)
      s := by
  classical
  have hrewrite :
      (fun t : ℝ => (Matrix.of fun i j => chartGramOnE (I := I) (g_DT t) α i j y).det)
        = fun t : ℝ =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k : Fin (Module.finrank ℝ E),
                  (Matrix.of fun i j => chartGramOnE (I := I) (g_DT t) α i j y) (σ k) k := by
    funext t
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun σ _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_prod _ (fun k _ => ?_)
  have h := h_entry (σ k) k
  refine h.congr ?_
  intro t _
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartGramOnE_adjugate_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun t : ℝ =>
        (Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).adjugate i j)
      s := by
  classical
  have hrewrite :
      (fun t : ℝ =>
          (Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).adjugate i j)
        = fun t : ℝ =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k : Fin (Module.finrank ℝ E),
                  ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).updateRow j
                    (Pi.single i (1 : ℝ))) (σ k) k := by
    funext t
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun σ _ => ?_)
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_prod _ (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq :
        (fun t : ℝ =>
            ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).updateRow j
              (Pi.single i (1 : ℝ))) (σ k) k)
          = fun _ : ℝ =>
              (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i (1 : ℝ)) k := by
      funext t
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact continuousOn_const
  · have heq :
        (fun t : ℝ =>
            ((Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y).updateRow j
              (Pi.single i (1 : ℝ))) (σ k) k)
          = fun t : ℝ =>
              (Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y) (σ k) k := by
      funext t
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    have h := h_entry (σ k) k
    refine h.congr ?_
    intro t _
    rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartInvGramOnE_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun t : ℝ => chartInvGramOnE (I := I) (g_DT t) α i j y) s := by
  classical
  set Gmat : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun t => Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y with hGmat_def
  have hGmat_eq : ∀ t, Gmat t = chartGramMatrix (I := I) (g_DT t) α
      ((extChartAt I α).symm y) := by
    intro t
    ext a b
    rw [hGmat_def]
    simp only [Matrix.of_apply]
    rw [chartGramOnE_def]
  have hcongr : ∀ t ∈ s,
      chartInvGramOnE (I := I) (g_DT t) α i j y =
        ((Gmat t).det)⁻¹ * (Gmat t).adjugate i j := by
    intro t _
    rw [chartInvGramOnE_def]
    unfold chartInvGramMatrix
    have hpos := chartGramMatrix_det_pos (I := I) (g_DT t) α hx
    have hdet_ne : (chartGramMatrix (I := I) (g_DT t) α
        ((extChartAt I α).symm y)).det ≠ 0 := ne_of_gt hpos
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (g_DT t) α
            ((extChartAt I α).symm y)).det •
          (chartGramMatrix (I := I) (g_DT t) α
            ((extChartAt I α).symm y)).adjugate) i j =
      ((Gmat t).det)⁻¹ * (Gmat t).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [hGmat_eq t]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContinuousOn.congr ?_ hcongr
  refine ContinuousOn.mul ?_ ?_
  · have hdet_cont : ContinuousOn (fun t : ℝ => (Gmat t).det) s := by
      have h := chartGramOnE_det_continuous_in_metric_at (I := I) g_DT α y s h_entry
      exact h
    refine hdet_cont.inv₀ ?_
    intro t _
    have hpos := chartGramMatrix_det_pos (I := I) (g_DT t) α hx
    have : (Gmat t).det = (chartGramMatrix (I := I) (g_DT t) α
        ((extChartAt I α).symm y)).det := by
      rw [hGmat_eq t]
    rw [this]
    exact ne_of_gt hpos
  · exact chartGramOnE_adjugate_continuous_in_metric_at (I := I) g_DT α y s h_entry i j

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_continuous_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ => partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y) s)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (a b k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b k y) s := by
  classical
  have hrewrite : (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b k y) =
      fun t : ℝ =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) (g_DT t) α ((extChartAt I α).symm y) k l *
            (partialDeriv (E := E) a (chartGramOnE (I := I) (g_DT t) α l b) y +
             partialDeriv (E := E) b (chartGramOnE (I := I) (g_DT t) α l a) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α a b) y) := by
    funext t
    rw [chartChristoffel_def]
  rw [hrewrite]
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ (fun l _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · have hcongr : (fun t : ℝ => chartInvGramMatrix (I := I) (g_DT t) α
            ((extChartAt I α).symm y) k l)
        = fun t : ℝ => chartInvGramOnE (I := I) (g_DT t) α k l y := by
      funext t
      rfl
    rw [hcongr]
    exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s h_entry hx k l
  · refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.add ?_ ?_
      · exact h_partial a l b
      · exact h_partial b l a
    · exact h_partial l a b

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckVFComp_continuous_in_metric_at
    (g' : SmoothRiemannianMetric I M) (α : M) (y : E)
    (s : Set ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (h_entry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α i j y) s)
    (h_partial : ∀ l i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun t : ℝ => partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y) s)
    (hx : ((extChartAt I α).symm y) ∈
      (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun t : ℝ =>
        DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g' α k y) s := by
  classical
  have hrewrite :
      (fun t : ℝ => DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT t) g' α k y)
        = fun t : ℝ =>
            ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (g_DT t) α a b y *
                (chartChristoffel (I := I) (g_DT t) α a b k y -
                  chartChristoffel (I := I) g' α a b k y) := by
    funext t
    rw [DeTurckLinearization.chartDeTurckVFComp_def]
  rw [hrewrite]
  refine continuousOn_finset_sum _ (fun a _ => ?_)
  refine continuousOn_finset_sum _ (fun b _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · exact chartInvGramOnE_continuous_in_metric_at (I := I) g_DT α y s h_entry hx a b
  · refine ContinuousOn.sub ?_ ?_
    · exact chartChristoffel_continuous_in_metric_at (I := I) g_DT α y s h_entry h_partial hx a b k
    · exact continuousOn_const

end DeTurck
end PDE
end DifferentialGeometry
