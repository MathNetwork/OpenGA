import DifferentialGeometry.Geometry.Geodesic.ChartTransitionMap
import DifferentialGeometry.Geometry.Geodesic.ChartTransitionJacobian
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartGramChristoffel
import DifferentialGeometry.Analysis.Integration.Measure.Invariance
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma fderivWithin_range_I_eq_fderiv' [I.Boundaryless]
    (f : E → E) (y : E) :
    fderivWithin ℝ f (Set.range I) y = fderiv ℝ f y := by
  have h : (Set.range I : Set E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ (I := I)
  rw [h, fderivWithin_univ]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma tangentCoordChange_eq_chartTransitionAt' [I.Boundaryless]
    (α β : M) (p : M) :
    tangentCoordChange I α β p =
      chartTransitionAt (I := I) α β (extChartAt I α p) := by
  rw [tangentCoordChange_def]
  rw [chartTransitionAt_def]
  rw [chartTransitionMap_def]
  exact fderivWithin_range_I_eq_fderiv' (I := I)
    (extChartAt I β ∘ (extChartAt I α).symm) (extChartAt I α p)

omit [InnerProductSpace ℝ E] in
private theorem chartGramOnE_eq_sum_chartTransition' [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (x : E)
    (hx : x ∈ (extChartAt I α) ''
              ((chartAt H α).source ∩ (chartAt H β).source))
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j x =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β x a i *
        chartTransitionJacEntry (I := I) α β x b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) := by
  classical
  obtain ⟨p, ⟨hp_α_src, hp_β_src⟩, hp_eq⟩ := hx
  have hp_ext_α : p ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hp_α_src
  have hp_ext_β : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β_src
  have hx_eq : extChartAt I α p = x := hp_eq
  have hp_symm : (extChartAt I α).symm x = p := by
    rw [← hx_eq, (extChartAt I α).left_inv hp_ext_α]
  have h_tβ : chartTransitionMap (I := I) α β x = extChartAt I β p := by
    change extChartAt I β ((extChartAt I α).symm x) = extChartAt I β p
    rw [hp_symm]
  have hp_triv_α : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source; exact hp_α_src
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β_src
  have h_lhs :
      chartGramOnE (I := I) g α i j x =
        chartGramMatrix g α p i j := by
    change chartGramMatrix g α ((extChartAt I α).symm x) i j =
        chartGramMatrix g α p i j
    rw [hp_symm]
  have h_rhs_inner : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g β a b
        (chartTransitionMap (I := I) α β x) =
      chartGramMatrix g β p a b := by
    intro a b
    change chartGramMatrix g β
        ((extChartAt I β).symm (chartTransitionMap (I := I) α β x)) a b =
      chartGramMatrix g β p a b
    rw [h_tβ, (extChartAt I β).left_inv hp_ext_β]
  rw [h_lhs]
  rw [chartGramMatrix_pullback_eq_sum (I := I) g β α
        hp_triv_β hp_triv_α i j]
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [h_rhs_inner k l]
  congr 1
  congr 1
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt' (I := I) α β p]
    simp only [chartTransitionJacEntry_def, hx_eq]
  · rw [transitionMatrix_apply]
    rw [tangentCoordChange_eq_chartTransitionAt' (I := I) α β p]
    simp only [chartTransitionJacEntry_def, hx_eq]

private def invGramPullbackCandidate [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) (p : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      chartTransitionJacEntry (I := I) β α
        (chartTransitionMap (I := I) α β (extChartAt I α p)) i a *
      chartTransitionJacEntry (I := I) β α
        (chartTransitionMap (I := I) α β (extChartAt I α p)) j b *
      chartInvGramMatrix (I := I) g β p a b

omit [InnerProductSpace ℝ E] in
private theorem chartGramMatrix_mul_invGramPullbackCandidate [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source) :
    chartGramMatrix (I := I) g α p *
        invGramPullbackCandidate (I := I) g α β p = 1 := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β
  set J : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a i => chartTransitionJacEntry (I := I) α β x a i with hJ_def
  set K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i a => chartTransitionJacEntry (I := I) β α Tx i a with hK_def
  set Gβinv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartInvGramMatrix (I := I) g β p a b with hGβinv_def
  have hx_mem : x ∈ (extChartAt I α) ''
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    refine ⟨p, ⟨hp_α, hp_β⟩, rfl⟩
  have hGram : ∀ k m : Fin (Module.finrank ℝ E),
      chartGramMatrix (I := I) g α p k m =
        ∑ a, ∑ b, J a k * J b m *
          chartGramMatrix (I := I) g β p a b := by
    intro k m
    have h := chartGramOnE_eq_sum_chartTransition' (I := I) g α β x hx_mem k m
    have hp_ext_α : p ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hp_α
    have hsymm : (extChartAt I α).symm x = p := by
      rw [hx_def, (extChartAt I α).left_inv hp_ext_α]
    have hp_ext_β : p ∈ (extChartAt I β).source := by
      rw [extChartAt_source (I := I)]; exact hp_β
    have hTx_eq : Tx = extChartAt I β p := by
      rw [hTx_def, hx_def]
      change extChartAt I β ((extChartAt I α).symm (extChartAt I α p)) = _
      rw [(extChartAt I α).left_inv hp_ext_α]
    have hLHS : chartGramOnE (I := I) g α k m x = chartGramMatrix (I := I) g α p k m := by
      rw [chartGramOnE_def (I := I) g α k m x, hsymm]
    rw [hLHS] at h
    rw [h]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    have hGβ : chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β x) =
        chartGramMatrix (I := I) g β p a b := by
      rw [chartGramOnE_def (I := I) g β a b (chartTransitionMap (I := I) α β x),
        ← hTx_def, hTx_eq, (extChartAt I β).left_inv hp_ext_β]
    rw [hGβ]
  have hx_src : x ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  have hMut : ∀ c i : Fin (Module.finrank ℝ E),
      ∑ a, J a i * K c a = (if c = i then (1 : ℝ) else 0) := by
    intro c i
    have h := chartTransitionJacEntry_mul_sum (I := I) α β hx_src c i
    rw [← hTx_def] at h
    exact h
  have hGβinvR : ∀ a d : Fin (Module.finrank ℝ E),
      ∑ b, chartGramMatrix (I := I) g β p a b * Gβinv b d =
        (if a = d then (1 : ℝ) else 0) := by
    intro a d
    have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g β hp_triv_β
    have := congrFun (congrFun hmul a) d
    rw [Matrix.mul_apply] at this
    rw [hGβinv_def]
    rw [show (∑ b, chartGramMatrix (I := I) g β p a b *
        chartInvGramMatrix (I := I) g β p b d) =
        (1 : Matrix _ _ ℝ) a d from this]
    rw [Matrix.one_apply]
  have hMut' : ∀ b i : Fin (Module.finrank ℝ E),
      ∑ m, J b m * K m i = (if b = i then (1 : ℝ) else 0) := by
    intro b i
    have h := chartTransitionJacEntry_mul_sum' (I := I) α β hx_src b i
    rw [← hTx_def] at h
    exact h
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hH : ∀ m : Fin (Module.finrank ℝ E),
      invGramPullbackCandidate (I := I) g α β p m l =
        ∑ i, ∑ j, K m i * K l j * Gβinv i j := by
    intro m
    rfl
  set Φ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun a b i j m =>
      (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j) *
        (J b m * K m i) with hΦ_def
  calc ∑ m, chartGramMatrix (I := I) g α p k m *
          invGramPullbackCandidate (I := I) g α β p m l
      = ∑ m, (∑ a, ∑ b, J a k * J b m *
            chartGramMatrix (I := I) g β p a b) *
          (∑ i, ∑ j, K m i * K l j * Gβinv i j) := by
        refine Finset.sum_congr rfl ?_
        intro m _
        rw [hGram k m, hH m]
    _ = ∑ m, ∑ a, ∑ b, ∑ i, ∑ j, Φ a b i j m := by
        refine Finset.sum_congr rfl ?_
        intro m _
        rw [Fintype.sum_mul_sum]
        rw [Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun i _ => by
            rw [Finset.sum_mul_sum]))]
        refine Finset.sum_congr rfl ?_; intro a _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        refine Finset.sum_congr rfl ?_; intro i _
        refine Finset.sum_congr rfl ?_; intro j _
        rw [hΦ_def]; ring
    _ = ∑ a, ∑ b, ∑ i, ∑ j, ∑ m, Φ a b i j m := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro a _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro i _
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
          (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j) *
            (if b = i then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        refine Finset.sum_congr rfl ?_; intro i _
        refine Finset.sum_congr rfl ?_; intro j _
        rw [hΦ_def, ← Finset.mul_sum, hMut' b i]
    _ = ∑ a, ∑ b, ∑ j,
          (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv b j) := by
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro j _
        rw [show (∑ i, (J a k * chartGramMatrix (I := I) g β p a b) *
                (K l j * Gβinv i j) * (if b = i then (1 : ℝ) else 0)) =
              ∑ i, (if b = i then
                (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j)
                else 0) from by
          refine Finset.sum_congr rfl ?_; intro i _
          by_cases h : b = i
          · rw [if_pos h, if_pos h, mul_one]
          · rw [if_neg h, if_neg h, mul_zero]]
        rw [Finset.sum_ite_eq Finset.univ b
          (fun i => (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv i j))]
        rw [if_pos (Finset.mem_univ b)]
    _ = ∑ a, J a k * K l a := by
        refine Finset.sum_congr rfl ?_; intro a _
        rw [Finset.sum_comm]
        have hstep : ∀ j : Fin (Module.finrank ℝ E),
            (∑ b, (J a k * chartGramMatrix (I := I) g β p a b) * (K l j * Gβinv b j)) =
              (if a = j then J a k * K l j else 0) := by
          intro j
          have : (∑ b, (J a k * chartGramMatrix (I := I) g β p a b) *
                (K l j * Gβinv b j)) =
              J a k * K l j *
                (∑ b, chartGramMatrix (I := I) g β p a b * Gβinv b j) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_; intro b _
            ring
          rw [this, hGβinvR a j]
          by_cases h : a = j
          · rw [if_pos h, if_pos h, mul_one]
          · rw [if_neg h, if_neg h, mul_zero]
        rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hstep j)]
        rw [Finset.sum_ite_eq Finset.univ a (fun j => J a k * K l j)]
        rw [if_pos (Finset.mem_univ a)]
    _ = (if k = l then (1 : ℝ) else 0) := by
        rw [hMut l k]
        by_cases h : k = l
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hh : l = k => h hh.symm)]

omit [InnerProductSpace ℝ E] in
theorem chartInvGramMatrix_eq_sum_chartTransition [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (i j : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g α p i j =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) i a *
        chartTransitionJacEntry (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p)) j b *
        chartInvGramMatrix (I := I) g β p a b := by
  have hright := chartGramMatrix_mul_invGramPullbackCandidate (I := I) g α β hp_α hp_β
  have hinv : chartInvGramMatrix (I := I) g α p =
      invGramPullbackCandidate (I := I) g α β p := by
    unfold chartInvGramMatrix
    exact Matrix.inv_eq_right_inv hright
  have hentry := congrFun (congrFun hinv i) j
  rw [hentry]
  rfl

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma mem_overlap_image_of_mem_chartTransitionSource
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    y ∈ (extChartAt I α) ''
      ((chartAt H α).source ∩ (chartAt H β).source) := by
  obtain ⟨hy_tgt, hy_pre⟩ := hy
  have hy_pre' : (extChartAt I α).symm y ∈ (extChartAt I β).source := hy_pre
  set p := (extChartAt I α).symm y with hp_def
  have hp_α_ext : p ∈ (extChartAt I α).source := (extChartAt I α).map_target hy_tgt
  have hp_β_ext : p ∈ (extChartAt I β).source := hy_pre'
  have hp_α : p ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact hp_α_ext
  have hp_β : p ∈ (chartAt H β).source := by
    rw [← extChartAt_source (I := I)]; exact hp_β_ext
  refine ⟨p, ⟨hp_α, hp_β⟩, ?_⟩
  rw [hp_def]
  exact (extChartAt I α).right_inv hy_tgt

omit [InnerProductSpace ℝ E] in
lemma chartGramOnE_eq_sum_chartTransition_on_source [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j y =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y a i *
        chartTransitionJacEntry (I := I) α β y b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) :=
  chartGramOnE_eq_sum_chartTransition' (I := I) g α β y
    (mem_overlap_image_of_mem_chartTransitionSource (I := I) α β hy) i j

omit [InnerProductSpace ℝ E] in
lemma chartTransitionJacEntry_contDiffOn [I.Boundaryless]
    (α β : M) (a i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y => chartTransitionJacEntry (I := I) α β y a i)
      (chartTransitionSource (I := I) α β) := by
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord a) with hcoordCLM
  set evalCoord : (E →L[ℝ] E) →L[ℝ] ℝ :=
    coordCLM.comp
      (ContinuousLinearMap.apply ℝ E ((chartModelBasis E) i)) with hevalCoord
  have hfun : (fun y => chartTransitionJacEntry (I := I) α β y a i) =
      evalCoord ∘ (fun y => (chartTransitionAt (I := I) α β y : E →L[ℝ] E)) := by
    funext y
    rw [chartTransitionJacEntry_def, hevalCoord, hcoordCLM]
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [hfun]
  exact evalCoord.contDiff.comp_contDiffOn (chartTransitionAt_smooth (I := I) α β)

omit [InnerProductSpace ℝ E] in
lemma chartTransitionJacEntry_differentiableAt [I.Boundaryless]
    (α β : M) (a i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i) y := by
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hcd : ContDiffOn ℝ ∞
      (fun z => chartTransitionJacEntry (I := I) α β z a i)
      (chartTransitionSource (I := I) α β) :=
    chartTransitionJacEntry_contDiffOn (I := I) α β a i
  exact (hcd.contDiffAt (h_open.mem_nhds hy)).differentiableAt (by simp)

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma chartTransitionMap_mem_interior_target [I.Boundaryless]
    (α β : M) {y : E} (hy : y ∈ chartTransitionSource (I := I) α β) :
    chartTransitionMap (I := I) α β y ∈ interior (extChartAt I β).target := by
  have hTy : chartTransitionMap (I := I) α β y ∈ chartTransitionSource (I := I) β α :=
    chartTransitionMap_mapsTo_source (I := I) α β hy
  have hTy_tgt : chartTransitionMap (I := I) α β y ∈ (extChartAt I β).target :=
    hTy.1
  rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
  exact hTy_tgt

omit [InnerProductSpace ℝ E] in
lemma partialDeriv_chartGramOnE_comp_chartTransitionMap [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (a b k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) k
        (fun z => chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y =
      ∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y c k *
          partialDeriv (E := E) c (chartGramOnE (I := I) g β a b)
            (chartTransitionMap (I := I) α β y) := by
  classical
  set T := chartTransitionMap (I := I) α β with hT_def
  set Ty := T y with hTy_def
  have hTy_int : Ty ∈ interior (extChartAt I β).target := by
    rw [hTy_def, hT_def]
    exact chartTransitionMap_mem_interior_target (I := I) α β hy
  have hGβ_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g β a b) Ty := by
    have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
        (extChartAt I β).target := chartGramOnE_contDiffOn (I := I) g β a b
    have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
        (interior (extChartAt I β).target) := hcd.mono interior_subset
    exact (hcd_int.contDiffAt
      (isOpen_interior.mem_nhds hTy_int)).differentiableAt (by simp)
  have hT_diff : DifferentiableAt ℝ T y := by
    rw [hT_def]; exact chartTransitionMap_differentiableAt (I := I) α β hy
  unfold partialDeriv
  have hcomp_eq :
      (fun z => chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) =
        (chartGramOnE (I := I) g β a b) ∘ T := by
    funext z; rw [hT_def]; rfl
  rw [hcomp_eq]
  rw [fderiv_comp y hGβ_diff hT_diff]
  rw [ContinuousLinearMap.comp_apply]
  have hTk : fderiv ℝ T y ((chartModelBasis E) k) =
      ∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β y c k • (chartModelBasis E) c := by
    have hexp : chartTransitionAt (I := I) α β y ((chartModelBasis E) k) =
        ∑ c : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) α β y c k • (chartModelBasis E) c := by
      conv_lhs => rw [← (chartModelBasis E).sum_repr
        (chartTransitionAt (I := I) α β y ((chartModelBasis E) k))]
      rfl
    rw [chartTransitionAt_def] at hexp
    rw [hT_def]
    exact hexp
  rw [hTk]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [map_smul]
  rw [smul_eq_mul]

omit [IsManifold I ∞ M] [InnerProductSpace ℝ E] in
lemma partialDeriv_mul (k : Fin (Module.finrank ℝ E)) (u v : E → ℝ) {y : E}
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) k (fun z => u z * v z) y =
      partialDeriv (E := E) k u y * v y + u y * partialDeriv (E := E) k v y := by
  unfold partialDeriv
  have hmul : fderiv ℝ (fun z => u z * v z) y =
      u y • fderiv ℝ v y + v y • fderiv ℝ u y := fderiv_mul hu hv
  rw [hmul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] in
lemma partialDeriv_chartTransition_pullback_summand [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (a b i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) k
        (fun z => chartTransitionJacEntry (I := I) α β z a i *
          chartTransitionJacEntry (I := I) α β z b j *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y =
      (partialDeriv (E := E) k
          (fun z => chartTransitionJacEntry (I := I) α β z a i) y) *
        chartTransitionJacEntry (I := I) α β y b j *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
      chartTransitionJacEntry (I := I) α β y a i *
        (partialDeriv (E := E) k
          (fun z => chartTransitionJacEntry (I := I) α β z b j) y) *
        chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
      chartTransitionJacEntry (I := I) α β y a i *
        chartTransitionJacEntry (I := I) α β y b j *
        (partialDeriv (E := E) k
          (fun z => chartGramOnE (I := I) g β a b
            (chartTransitionMap (I := I) α β z)) y) := by
  classical
  have hJa : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i) y :=
    chartTransitionJacEntry_differentiableAt (I := I) α β a i hy
  have hJb : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z b j) y :=
    chartTransitionJacEntry_differentiableAt (I := I) α β b j hy
  have hG : DifferentiableAt ℝ
      (fun z => chartGramOnE (I := I) g β a b
        (chartTransitionMap (I := I) α β z)) y := by
    set T := chartTransitionMap (I := I) α β with hT_def
    have hTy_int : T y ∈ interior (extChartAt I β).target := by
      rw [hT_def]; exact chartTransitionMap_mem_interior_target (I := I) α β hy
    have hGβ_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g β a b) (T y) := by
      have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
          (extChartAt I β).target := chartGramOnE_contDiffOn (I := I) g β a b
      have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
          (interior (extChartAt I β).target) := hcd.mono interior_subset
      exact (hcd_int.contDiffAt
        (isOpen_interior.mem_nhds hTy_int)).differentiableAt (by simp)
    have hT_diff : DifferentiableAt ℝ T y := by
      rw [hT_def]; exact chartTransitionMap_differentiableAt (I := I) α β hy
    exact hGβ_diff.comp y hT_diff
  have hJab : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i *
        chartTransitionJacEntry (I := I) α β z b j) y := hJa.mul hJb
  rw [partialDeriv_mul k _ _ hJab hG]
  rw [partialDeriv_mul k _ _ hJa hJb]
  ring

omit [IsManifold I ∞ M] [InnerProductSpace ℝ E] in
lemma partialDeriv_finset_sum {ι : Type*} (s : Finset ι)
    (k : Fin (Module.finrank ℝ E)) (f : ι → E → ℝ) {y : E}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) y) :
    partialDeriv (E := E) k (fun z => ∑ i ∈ s, f i z) y =
      ∑ i ∈ s, partialDeriv (E := E) k (f i) y := by
  unfold partialDeriv
  rw [fderiv_fun_sum hf]
  rw [ContinuousLinearMap.sum_apply]

omit [IsManifold I ∞ M] [InnerProductSpace ℝ E] in
lemma partialDeriv_double_finset_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (k : Fin (Module.finrank ℝ E)) (f : ι → κ → E → ℝ) {y : E}
    (hf : ∀ a ∈ s, ∀ b ∈ t, DifferentiableAt ℝ (f a b) y) :
    partialDeriv (E := E) k (fun z => ∑ a ∈ s, ∑ b ∈ t, f a b z) y =
      ∑ a ∈ s, ∑ b ∈ t, partialDeriv (E := E) k (f a b) y := by
  rw [partialDeriv_finset_sum s k (fun a z => ∑ b ∈ t, f a b z)
    (fun a ha => DifferentiableAt.fun_sum (fun b hb => hf a ha b hb))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  exact partialDeriv_finset_sum t k (fun b z => f a b z) (fun b hb => hf a ha b hb)

omit [InnerProductSpace ℝ E] in
theorem partialDeriv_chartGramOnE_eq_sum_chartTransition [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        ((partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) y) *
          chartTransitionJacEntry (I := I) α β y b j *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
        chartTransitionJacEntry (I := I) α β y a i *
          (partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z b j) y) *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β y) +
        chartTransitionJacEntry (I := I) α β y a i *
          chartTransitionJacEntry (I := I) α β y b j *
          (∑ c : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) α β y c k *
              partialDeriv (E := E) c (chartGramOnE (I := I) g β a b)
                (chartTransitionMap (I := I) α β y))) := by
  classical
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have h_nhds : chartTransitionSource (I := I) α β ∈ nhds y := h_open.mem_nhds hy
  have h_eventually :
      chartGramOnE (I := I) g α i j =ᶠ[nhds y]
        (fun z => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) α β z a i *
            chartTransitionJacEntry (I := I) α β z b j *
            chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) := by
    filter_upwards [h_nhds] with z hz
    exact chartGramOnE_eq_sum_chartTransition_on_source (I := I) g α β hz i j
  have h_pd_eq : partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y =
      partialDeriv (E := E) k
        (fun z => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) α β z a i *
            chartTransitionJacEntry (I := I) α β z b j *
            chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y := by
    unfold partialDeriv
    rw [h_eventually.fderiv_eq]
  rw [h_pd_eq]
  have hdiff : ∀ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      ∀ b ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      DifferentiableAt ℝ
        (fun z => chartTransitionJacEntry (I := I) α β z a i *
          chartTransitionJacEntry (I := I) α β z b j *
          chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) y := by
    intro a _ b _
    have hJa : DifferentiableAt ℝ
        (fun z => chartTransitionJacEntry (I := I) α β z a i) y :=
      chartTransitionJacEntry_differentiableAt (I := I) α β a i hy
    have hJb : DifferentiableAt ℝ
        (fun z => chartTransitionJacEntry (I := I) α β z b j) y :=
      chartTransitionJacEntry_differentiableAt (I := I) α β b j hy
    have hG : DifferentiableAt ℝ
        (fun z => chartGramOnE (I := I) g β a b
          (chartTransitionMap (I := I) α β z)) y := by
      set T := chartTransitionMap (I := I) α β with hT_def
      have hTy_int : T y ∈ interior (extChartAt I β).target := by
        rw [hT_def]; exact chartTransitionMap_mem_interior_target (I := I) α β hy
      have hGβ_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g β a b) (T y) := by
        have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
            (extChartAt I β).target := chartGramOnE_contDiffOn (I := I) g β a b
        have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g β a b)
            (interior (extChartAt I β).target) := hcd.mono interior_subset
        exact (hcd_int.contDiffAt
          (isOpen_interior.mem_nhds hTy_int)).differentiableAt (by simp)
      have hT_diff : DifferentiableAt ℝ T y := by
        rw [hT_def]; exact chartTransitionMap_differentiableAt (I := I) α β hy
      exact hGβ_diff.comp y hT_diff
    exact (hJa.mul hJb).mul hG
  rw [partialDeriv_double_finset_sum Finset.univ Finset.univ k
    (fun a b z => chartTransitionJacEntry (I := I) α β z a i *
      chartTransitionJacEntry (I := I) α β z b j *
      chartGramOnE (I := I) g β a b (chartTransitionMap (I := I) α β z)) hdiff]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [partialDeriv_chartTransition_pullback_summand (I := I) g α β a b i j k hy]
  rw [partialDeriv_chartGramOnE_comp_chartTransitionMap (I := I) g α β a b k hy]

omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
lemma chartCoord_chartTransitionAt (α β : M) (x : E) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) a (chartTransitionAt (I := I) α β x v) =
      ∑ i : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β x a i * chartCoord (E := E) i v := by
  classical
  unfold chartCoord chartTransitionJacEntry
  have hexp : chartTransitionAt (I := I) α β x v =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr v i •
          chartTransitionAt (I := I) α β x ((chartModelBasis E) i) := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul]
  rw [hexp, map_sum]
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

def chartTransitionSecondDerivCorrection (α β : M) (v w : E) (x : E) : E :=
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ c : Fin (Module.finrank ℝ E),
      chartTransitionJacEntry (I := I) β α (chartTransitionMap (I := I) α β x) k c *
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
            chartCoord (E := E) i v * chartCoord (E := E) j w)) •
      chartModelBasis E k

omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
@[simp] lemma chartTransitionSecondDerivCorrection_def
    (α β : M) (v w : E) (x : E) :
    chartTransitionSecondDerivCorrection (I := I) α β v w x =
      ∑ k : Fin (Module.finrank ℝ E),
        (∑ c : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) k c *
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
                chartCoord (E := E) i v * chartCoord (E := E) j w)) •
          chartModelBasis E k := rfl

omit [InnerProductSpace ℝ E] in
lemma partialDeriv_chartTransitionJacEntry_swap [I.Boundaryless]
    (α β : M) (a i l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ chartTransitionSource (I := I) α β) :
    partialDeriv (E := E) i
        (fun z => chartTransitionJacEntry (I := I) α β z a l) y =
      partialDeriv (E := E) l
        (fun z => chartTransitionJacEntry (I := I) α β z a i) y := by
  classical
  set T := chartTransitionMap (I := I) α β with hT_def
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord a) with hcoordCLM
  have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
    chartTransitionSource_isOpen (I := I) α β
  have hcontDiffAt : ContDiffAt ℝ ∞ T y := by
    rw [hT_def]; exact chartTransitionMap_contDiffAt (I := I) α β hy
  have hsymm : IsSymmSndFDerivAt ℝ T y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hsmooth_on : ContDiffOn ℝ ∞ T (chartTransitionSource (I := I) α β) := by
    rw [hT_def]; exact chartTransitionMap_contDiffOn (I := I) α β
  have hT_diff : DifferentiableAt ℝ (fderiv ℝ T) y := by
    have hfderiv_smooth : ContDiffOn ℝ ∞ (fderiv ℝ T)
        (chartTransitionSource (I := I) α β) :=
      hsmooth_on.fderiv_of_isOpen h_open (by rw [ENat.coe_top_add_one])
    exact (hfderiv_smooth.contDiffAt (h_open.mem_nhds hy)).differentiableAt (by simp)
  have hkey : ∀ p q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) p
          (fun z => chartTransitionJacEntry (I := I) α β z a q) y =
        coordCLM ((fderiv ℝ (fderiv ℝ T) y ((chartModelBasis E) p))
          ((chartModelBasis E) q)) := by
    intro p q
    unfold partialDeriv
    set L : (E →L[ℝ] E) →L[ℝ] ℝ :=
      coordCLM.comp (ContinuousLinearMap.apply ℝ E ((chartModelBasis E) q)) with hL
    have hcomp_eq : (fun z : E =>
          chartTransitionJacEntry (I := I) α β z a q) = L ∘ (fderiv ℝ T) := by
      funext z
      rw [chartTransitionJacEntry_def, hL, hcoordCLM]
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, LinearMap.coe_toContinuousLinearMap',
        Module.Basis.coord_apply, chartTransitionAt_def, hT_def]
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hT_diff]
    rw [ContinuousLinearMap.comp_apply, L.fderiv]
    rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hkey i l, hkey l i]
  rw [hsymm ((chartModelBasis E) i) ((chartModelBasis E) l)]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma chartTransitionMap_extChartAt_symm
    (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source) :
    (extChartAt I β).symm
        (chartTransitionMap (I := I) α β (extChartAt I α p)) = p := by
  rw [chartTransitionMap_apply_extChartAt (I := I) α β hp_α]
  have hp_β_src : p ∈ (extChartAt I β).source := by
    rw [extChartAt_source (I := I)]; exact hp_β
  exact (extChartAt I β).left_inv hp_β_src

omit [InnerProductSpace ℝ E] in
lemma chartInvGramBeta_mul_chartGramOnE_diag
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (c b : Fin (Module.finrank ℝ E)) :
    ∑ d : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g β p c d *
        chartGramOnE (I := I) g β d b
          (chartTransitionMap (I := I) α β (extChartAt I α p)) =
      (if c = b then (1 : ℝ) else 0) := by
  classical
  have hp_triv_β : p ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    change p ∈ (chartAt H β).source; exact hp_β
  have hsymm : (extChartAt I β).symm
      (chartTransitionMap (I := I) α β (extChartAt I α p)) = p :=
    chartTransitionMap_extChartAt_symm (I := I) α β hp_α hp_β
  have hG : ∀ d : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g β d b
          (chartTransitionMap (I := I) α β (extChartAt I α p)) =
        chartGramMatrix (I := I) g β p d b := by
    intro d
    rw [chartGramOnE_def, hsymm]
  rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
    congrArg (fun t => chartInvGramMatrix (I := I) g β p c d * t) (hG d))]
  have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g β hp_triv_β
  have := congrFun (congrFun hmul c) b
  rw [Matrix.mul_apply] at this
  rw [this, Matrix.one_apply]

omit [InnerProductSpace ℝ E] in
lemma chartChristoffelNumerator_transitionIdentity [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (i j d : Fin (Module.finrank ℝ E)) :
    ∑ l : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) l d *
          (partialDeriv (E := E) i
              (chartGramOnE (I := I) g α l j) (extChartAt I α p) +
            partialDeriv (E := E) j
              (chartGramOnE (I := I) g α l i) (extChartAt I α p) -
            partialDeriv (E := E) l
              (chartGramOnE (I := I) g α i j) (extChartAt I α p)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) a
              (chartGramOnE (I := I) g β d b)
              (chartTransitionMap (I := I) α β (extChartAt I α p)) +
            partialDeriv (E := E) b
              (chartGramOnE (I := I) g β d a)
              (chartTransitionMap (I := I) α β (extChartAt I α p)) -
            partialDeriv (E := E) d
              (chartGramOnE (I := I) g β a b)
              (chartTransitionMap (I := I) α β (extChartAt I α p))) *
            chartTransitionJacEntry (I := I) α β (extChartAt I α p) a i *
            chartTransitionJacEntry (I := I) α β (extChartAt I α p) b j) +
      2 * ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g β d b
            (chartTransitionMap (I := I) α β (extChartAt I α p)) *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z b j)
              (extChartAt I α p) := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  have hx_src : x ∈ chartTransitionSource (I := I) α β :=
    extChartAt_mem_chartTransitionSource (I := I) α β hp_α hp_β
  set J : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a r => chartTransitionJacEntry (I := I) α β x a r with hJ
  set K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun l c => chartTransitionJacEntry (I := I) β α Tx l c with hK
  set dJ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun t a r => partialDeriv (E := E) t
      (fun z => chartTransitionJacEntry (I := I) α β z a r) x with hdJ
  set Gb : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartGramOnE (I := I) g β a b Tx with hGb
  set dGb : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun t a b => partialDeriv (E := E) t (chartGramOnE (I := I) g β a b) Tx with hdGb
  have hFR : ∀ a d : Fin (Module.finrank ℝ E),
      ∑ l, J a l * K l d = (if a = d then (1 : ℝ) else 0) := by
    intro a d
    have h := chartTransitionJacEntry_forward_reverse_collapse (I := I) α β hp_α hp_β a d
    simpa [hJ, hK, hx_def, hTx_def] using h
  have hGbsymm : ∀ a b : Fin (Module.finrank ℝ E), Gb a b = Gb b a := by
    intro a b; rw [hGb]; exact chartGramOnE_symm (I := I) g β a b Tx
  have hSchwarz : ∀ t a r : Fin (Module.finrank ℝ E), dJ t a r = dJ r a t := by
    intro t a r
    rw [hdJ]
    exact partialDeriv_chartTransitionJacEntry_swap (I := I) α β a t r hx_src
  have hDG : ∀ t r s : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) t (chartGramOnE (I := I) g α r s) x =
        ∑ a, ∑ b, (dJ t a r * J b s * Gb a b
          + J a r * dJ t b s * Gb a b
          + J a r * J b s * (∑ c, J c t * dGb c a b)) := by
    intro t r s
    have h := partialDeriv_chartGramOnE_eq_sum_chartTransition (I := I) g α β r s t hx_src
    rw [h]
  have hCol : ∀ (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      ∑ l, ∑ a, ∑ b, (K l d * J a l) * W a b = ∑ b, W d b := by
    intro W
    have hreorder :
        (∑ l, ∑ a, ∑ b, (K l d * J a l) * W a b) =
          ∑ a, ∑ b, ∑ l, (K l d * J a l) * W a b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
    rw [hreorder]
    have hinner : ∀ a b : Fin (Module.finrank ℝ E),
        (∑ l, (K l d * J a l) * W a b) =
          (if a = d then (1 : ℝ) else 0) * W a b := by
      intro a b
      rw [← Finset.sum_mul]
      congr 1
      rw [← hFR a d]
      refine Finset.sum_congr rfl ?_; intro l _
      ring
    rw [Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => hinner a b))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_; intro b _
    rw [Finset.sum_eq_single d]
    · rw [if_pos rfl, one_mul]
    · intro a _ ha; rw [if_neg ha, zero_mul]
    · intro hd; exact absurd (Finset.mem_univ d) hd
  set Acoef : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun t a => ∑ l, K l d * dJ t a l with hAcoef
  set A1 : ℝ := ∑ a, ∑ b, Acoef i a * J b j * Gb a b with hA1
  set A2 : ℝ := ∑ a, ∑ b, Acoef j a * J b i * Gb a b with hA2
  set BB : ℝ := ∑ b, Gb d b * dJ i b j with hBB
  set C1 : ℝ := ∑ a, ∑ b, J a i * J b j * dGb a d b with hC1
  set C2 : ℝ := ∑ a, ∑ b, J a i * J b j * dGb b d a with hC2
  set C3 : ℝ := ∑ a, ∑ b, J a i * J b j * dGb d a b with hC3
  have hTerm1 :
      (∑ l, K l d * partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x) =
        A1 + BB + C1 := by
    have hstep : ∀ l, K l d * partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x =
        (∑ a, ∑ b, K l d * (dJ i a l * J b j * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (dJ i b j * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (J b j * (∑ c, J c i * dGb c a b))) := by
      intro l
      rw [hDG i l j, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hstep l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
    · rw [hA1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_; intro l _
      ring
    · rw [hBB]
      have := hCol (fun a b => dJ i b j * Gb a b)
      rw [this]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
    · rw [hC1]
      have := hCol (fun a b => J b j * (∑ c, J c i * dGb c a b))
      rw [this]
      rw [show (∑ b, J b j * (∑ c, J c i * dGb c d b)) =
            ∑ b, ∑ c, J c i * J b j * dGb c d b from by
        refine Finset.sum_congr rfl ?_; intro b _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro c _
        ring]
      rw [Finset.sum_comm]
  have hTerm2 :
      (∑ l, K l d * partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x) =
        A2 + BB + C2 := by
    have hstep : ∀ l, K l d * partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x =
        (∑ a, ∑ b, K l d * (dJ j a l * J b i * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (dJ j b i * Gb a b))
          + (∑ a, ∑ b, (K l d * J a l) * (J b i * (∑ c, J c j * dGb c a b))) := by
      intro l
      rw [hDG j l i, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hstep l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
    · rw [hA2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_; intro l _
      ring
    · rw [hBB]
      have := hCol (fun a b => dJ j b i * Gb a b)
      rw [this]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hSchwarz j b i]
      ring
    · rw [hC2]
      have := hCol (fun a b => J b i * (∑ c, J c j * dGb c a b))
      rw [this]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro b _
      ring
  have hTerm3 :
      (∑ l, K l d * partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x) =
        A1 + A2 + C3 := by
    have hstep : ∀ l, K l d * partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x =
        (∑ a, ∑ b, K l d * (dJ l a i * J b j * Gb a b))
          + (∑ a, ∑ b, K l d * (J a i * dJ l b j * Gb a b))
          + (∑ a, ∑ b, J a i * J b j * (∑ c, (K l d * J c l) * dGb c a b)) := by
      intro l
      rw [hDG l i j, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [show J a i * J b j * (∑ c, (K l d * J c l) * dGb c a b) =
            K l d * (J a i * J b j * (∑ c, J c l * dGb c a b)) from by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro c _
        ring]
      ring
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hstep l)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
    · rw [hA1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef]
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_; intro l _
      rw [hSchwarz l a i]
      ring
    · rw [hA2]
      rw [show (∑ l, ∑ a, ∑ b, K l d * (J a i * dJ l b j * Gb a b)) =
            ∑ a, ∑ b, (∑ l, K l d * dJ j b l) * J a i * Gb a b from by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro a _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_; intro l _
        rw [hSchwarz l b j]; ring]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      refine Finset.sum_congr rfl ?_; intro b _
      rw [hAcoef, hGbsymm b a]
    · rw [hC3]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro b _
      rw [show (∑ l, J a i * J b j * (∑ c, (K l d * J c l) * dGb c a b)) =
            J a i * J b j * (∑ c, (∑ l, K l d * J c l) * dGb c a b) from by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro c _
        rw [Finset.sum_mul]]
      congr 1
      rw [Finset.sum_eq_single d]
      · rw [show (∑ l, K l d * J d l) = (if d = d then (1 : ℝ) else 0) from by
          rw [← hFR d d]; refine Finset.sum_congr rfl ?_; intro l _; ring]
        rw [if_pos rfl, one_mul]
      · intro c _ hc
        rw [show (∑ l, K l d * J c l) = (if c = d then (1 : ℝ) else 0) from by
          rw [← hFR c d]; refine Finset.sum_congr rfl ?_; intro l _; ring]
        rw [if_neg hc, zero_mul]
      · intro hd; exact absurd (Finset.mem_univ d) hd
  have hSigma :
      (∑ l, K l d *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
        2 * BB + (C1 + C2 - C3) := by
    rw [show (∑ l, K l d *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
        (∑ l, K l d * partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x)
          + (∑ l, K l d * partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x)
          - (∑ l, K l d * partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x) from by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_; intro l _; ring]
    rw [hTerm1, hTerm2, hTerm3]
    ring
  rw [show (∑ l, chartTransitionJacEntry (I := I) β α Tx l d *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
      (∑ l, K l d *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) from rfl]
  rw [hSigma]
  have hRHS_S :
      (∑ a, ∑ b, (dGb a d b + dGb b d a - dGb d a b) * J a i * J b j) =
        C1 + C2 - C3 := by
    rw [hC1, hC2, hC3]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_; intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_; intro b _
    ring
  rw [show (∑ a, ∑ b,
        (partialDeriv (E := E) a (chartGramOnE (I := I) g β d b) Tx +
          partialDeriv (E := E) b (chartGramOnE (I := I) g β d a) Tx -
          partialDeriv (E := E) d (chartGramOnE (I := I) g β a b) Tx) *
          chartTransitionJacEntry (I := I) α β x a i *
          chartTransitionJacEntry (I := I) α β x b j) =
      (∑ a, ∑ b, (dGb a d b + dGb b d a - dGb d a b) * J a i * J b j) from rfl]
  rw [hRHS_S]
  rw [show (2 * ∑ b, chartGramOnE (I := I) g β d b Tx *
        partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) α β z b j) x) =
      2 * BB from rfl]
  ring

omit [InnerProductSpace ℝ E] in
theorem chartChristoffel_transform [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g α i j k (extChartAt I α p) =
      (∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) k c *
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g β a b c
                (chartTransitionMap (I := I) α β (extChartAt I α p)) *
              chartTransitionJacEntry (I := I) α β (extChartAt I α p) a i *
              chartTransitionJacEntry (I := I) α β (extChartAt I α p) b j)) +
      (∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) k c *
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z c j)
            (extChartAt I α p)) := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  have hsymm_α : (extChartAt I α).symm x = p := by
    rw [hx_def]
    have hp_ext_α : p ∈ (extChartAt I α).source := by
      rw [extChartAt_source (I := I)]; exact hp_α
    exact (extChartAt I α).left_inv hp_ext_α
  have hsymm_β : (extChartAt I β).symm Tx = p := by
    rw [hTx_def, hx_def]
    exact chartTransitionMap_extChartAt_symm (I := I) α β hp_α hp_β
  set K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun l c => chartTransitionJacEntry (I := I) β α Tx l c with hK
  set J : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a r => chartTransitionJacEntry (I := I) α β x a r with hJ
  set Gbinv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun c d => chartInvGramMatrix (I := I) g β p c d with hGbinv
  set Gb : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartGramOnE (I := I) g β a b Tx with hGb
  set S : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
      partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
      partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x with hS
  set Sbar : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun a b d => partialDeriv (E := E) a (chartGramOnE (I := I) g β d b) Tx +
      partialDeriv (E := E) b (chartGramOnE (I := I) g β d a) Tx -
      partialDeriv (E := E) d (chartGramOnE (I := I) g β a b) Tx with hSbar
  set dJ : Fin (Module.finrank ℝ E) → ℝ :=
    fun c => partialDeriv (E := E) i
      (fun z => chartTransitionJacEntry (I := I) α β z c j) x with hdJ
  have hGammaBar : ∀ a b c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g β a b c Tx =
        (1 / 2 : ℝ) * ∑ d, Gbinv c d * Sbar a b d := by
    intro a b c
    rw [chartChristoffel_def, hsymm_β]
  have hDiag : ∀ c b : Fin (Module.finrank ℝ E),
      ∑ d, Gbinv c d * Gb d b = (if c = b then (1 : ℝ) else 0) := by
    intro c b
    have h := chartInvGramBeta_mul_chartGramOnE_diag (I := I) g α β hp_α hp_β c b
    simpa [hGbinv, hGb, hx_def, hTx_def] using h
  have hRaw : ∀ d : Fin (Module.finrank ℝ E),
      ∑ l, K l d * S l =
        (∑ a, ∑ b, Sbar a b d * J a i * J b j)
          + 2 * ∑ b, Gb d b *
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z b j) x := by
    intro d
    have h := chartChristoffelNumerator_transitionIdentity (I := I) g α β hp_α hp_β i j d
    rw [hK, hS]
    rw [show (∑ l, chartTransitionJacEntry (I := I) β α Tx l d *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
        ∑ l, chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β (extChartAt I α p)) l d *
          (partialDeriv (E := E) i
              (chartGramOnE (I := I) g α l j) (extChartAt I α p) +
            partialDeriv (E := E) j
              (chartGramOnE (I := I) g α l i) (extChartAt I α p) -
            partialDeriv (E := E) l
              (chartGramOnE (I := I) g α i j) (extChartAt I α p)) from rfl]
    rw [h, hSbar, hGb]
  have hMaster : ∀ c : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ l, K l d * S l) =
        (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j)
          + dJ c := by
    intro c
    rw [Finset.sum_congr rfl (fun d (_ : d ∈ Finset.univ) =>
      congrArg (fun t => Gbinv c d * t) (hRaw d))]
    rw [show (∑ d, Gbinv c d * ((∑ a, ∑ b, Sbar a b d * J a i * J b j)
          + 2 * ∑ b, Gb d b *
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z b j) x)) =
        (∑ d, Gbinv c d * (∑ a, ∑ b, Sbar a b d * J a i * J b j))
          + (∑ d, Gbinv c d * (2 * ∑ b, Gb d b *
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z b j) x)) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_; intro d _; ring]
    rw [mul_add]
    congr 1
    · have hLHS : (1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ a, ∑ b, Sbar a b d * J a i * J b j) =
          ∑ d, ∑ a, ∑ b, (1 / 2 : ℝ) * (Gbinv c d * Sbar a b d * J a i * J b j) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro d _
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        ring
      have hRHS : (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j) =
          ∑ a, ∑ b, ∑ d, (1 / 2 : ℝ) * (Gbinv c d * Sbar a b d * J a i * J b j) := by
        refine Finset.sum_congr rfl ?_; intro a _
        refine Finset.sum_congr rfl ?_; intro b _
        rw [hGammaBar a b c]
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intro d _
        ring
      rw [hLHS, hRHS]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_; intro a _
      rw [Finset.sum_comm]
    · rw [hdJ]
      rw [show (∑ d, Gbinv c d * (2 * ∑ b, Gb d b *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z b j) x)) =
          2 * ∑ b, (∑ d, Gbinv c d * Gb d b) *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z b j) x from by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_; intro b _
        refine Finset.sum_congr rfl ?_; intro d _
        ring]
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) =>
        show (∑ d, Gbinv c d * Gb d b) * partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z b j) x =
          (if c = b then partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z b j) x else 0) from by
          rw [hDiag c b]
          by_cases h : c = b
          · rw [if_pos h, if_pos h, one_mul]
          · rw [if_neg h, if_neg h, zero_mul])]
      rw [Finset.sum_ite_eq Finset.univ c
        (fun b => partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) α β z b j) x)]
      rw [if_pos (Finset.mem_univ c)]
      ring
  rw [chartChristoffel_def, hsymm_α]
  rw [show ((1 / 2 : ℝ) * ∑ l, chartInvGramMatrix (I := I) g α p k l *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x)) =
      ∑ c, K k c * ((1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ l, K l d * S l)) from by
    rw [Finset.mul_sum]
    have hExpand : ∀ l, (1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g α p k l * S l) =
        ∑ c, ∑ d, (1 / 2 : ℝ) * (K k c * (K l d * Gbinv c d)) * S l := by
      intro l
      rw [chartInvGramMatrix_eq_sum_chartTransition (I := I) g α β hp_α hp_β k l]
      rw [← hx_def, ← hTx_def]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro c _
      refine Finset.sum_congr rfl ?_; intro d _
      rw [hK, hGbinv]
      ring
    rw [show (∑ l, (1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g α p k l *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
              partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
              partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x))) =
          ∑ l, ∑ c, ∑ d, (1 / 2 : ℝ) * (K k c * (K l d * Gbinv c d)) * S l from by
      refine Finset.sum_congr rfl ?_; intro l _
      rw [show chartInvGramMatrix (I := I) g α p k l *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) x +
              partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) x -
              partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) x) =
          chartInvGramMatrix (I := I) g α p k l * S l from rfl]
      rw [hExpand l]]
    rw [show (∑ c, K k c * ((1 / 2 : ℝ) * ∑ d, Gbinv c d * (∑ l, K l d * S l))) =
          ∑ c, ∑ d, ∑ l, (1 / 2 : ℝ) * (K k c * (K l d * Gbinv c d)) * S l from by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_; intro c _
      refine Finset.sum_congr rfl ?_; intro d _
      refine Finset.sum_congr rfl ?_; intro l _
      ring]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_; intro c _
    rw [Finset.sum_comm]]
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) =>
    congrArg (fun t => K k c * t) (hMaster c))]
  rw [show (∑ c, K k c *
        ((∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j) + dJ c)) =
      (∑ c, K k c * (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx * J a i * J b j))
        + (∑ c, K k c * dJ c) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_; intro c _; ring]

omit [InnerProductSpace ℝ E] in
lemma chartCoord_chartChristoffelContraction
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α : M) (v w y : E)
    (l : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) l
        (chartChristoffelContraction (I := I) g α v w y) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j l y *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
  classical
  rw [chartChristoffelContraction_def, chartCoord, map_sum, Finsupp.finset_sum_apply]
  have hbasis : ∀ k : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr ((chartModelBasis E) k) l = if k = l then 1 else 0 :=
    fun k => (chartModelBasis E).repr_self_apply k l
  calc
    ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) •
            chartModelBasis E k)) l
      = ∑ k : Fin (Module.finrank ℝ E),
          (∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) *
            ((chartModelBasis E).repr (chartModelBasis E k) l) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j l y *
            chartCoord (E := E) i v * chartCoord (E := E) j w := by
        rw [Finset.sum_eq_single l]
        · rw [hbasis l]; simp
        · intro k _ hkl; rw [hbasis k, if_neg hkl]; ring
        · intro hl; exact absurd (Finset.mem_univ l) hl

private lemma sum5_reorder {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ c, ∑ a, ∑ b, ∑ i, ∑ j, F c a b i j) =
      ∑ i, ∑ j, ∑ c, ∑ a, ∑ b, F c a b i j := by
  classical
  have hi : (∑ c, ∑ a, ∑ b, ∑ i, ∑ j, F c a b i j)
      = ∑ i, ∑ c, ∑ a, ∑ b, ∑ j, F c a b i j := by
    have s1 : (∑ c, ∑ a, ∑ b, ∑ i, ∑ j, F c a b i j)
        = ∑ c, ∑ a, ∑ i, ∑ b, ∑ j, F c a b i j := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_comm]
    have s2 : (∑ c, ∑ a, ∑ i, ∑ b, ∑ j, F c a b i j)
        = ∑ c, ∑ i, ∑ a, ∑ b, ∑ j, F c a b i j := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_comm]
    have s3 : (∑ c, ∑ i, ∑ a, ∑ b, ∑ j, F c a b i j)
        = ∑ i, ∑ c, ∑ a, ∑ b, ∑ j, F c a b i j := by
      rw [Finset.sum_comm]
    rw [s1, s2, s3]
  rw [hi]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have t1 : (∑ c, ∑ a, ∑ b, ∑ j, F c a b i j)
      = ∑ c, ∑ a, ∑ j, ∑ b, F c a b i j := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  have t2 : (∑ c, ∑ a, ∑ j, ∑ b, F c a b i j)
      = ∑ c, ∑ j, ∑ a, ∑ b, F c a b i j := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_comm]
  have t3 : (∑ c, ∑ j, ∑ a, ∑ b, F c a b i j)
      = ∑ j, ∑ c, ∑ a, ∑ b, F c a b i j := by
    rw [Finset.sum_comm]
  rw [t1, t2, t3]

private lemma sum3_reorder {n : ℕ} (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ c, ∑ i, ∑ j, F c i j) = ∑ i, ∑ j, ∑ c, F c i j := by
  classical
  have hi : (∑ c, ∑ i, ∑ j, F c i j) = ∑ i, ∑ c, ∑ j, F c i j := by
    rw [Finset.sum_comm]
  rw [hi]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

private lemma chartTransitionContractionReorderMain
    {n : ℕ} (K : Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ)
    (J : Fin n → Fin n → ℝ) (vi wj : Fin n → ℝ) :
    (∑ c, K c *
        (∑ a, ∑ b, Γ a b c *
          (∑ i, J a i * vi i) * (∑ j, J b j * wj j))) =
      ∑ i, ∑ j, (∑ c, K c *
        (∑ a, ∑ b, Γ a b c * J a i * J b j)) * vi i * wj j := by
  classical
  have hLHS : (∑ c, K c *
        (∑ a, ∑ b, Γ a b c *
          (∑ i, J a i * vi i) * (∑ j, J b j * wj j))) =
      ∑ c, ∑ a, ∑ b, ∑ i, ∑ j,
        K c * (Γ a b c * (J a i * vi i) * (J b j * wj j)) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [mul_assoc (Γ a b c), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hRHS : (∑ i, ∑ j, (∑ c, K c *
        (∑ a, ∑ b, Γ a b c * J a i * J b j)) * vi i * wj j) =
      ∑ i, ∑ j, ∑ c, ∑ a, ∑ b,
        K c * (Γ a b c * (J a i * vi i) * (J b j * wj j)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hLHS, hRHS]
  exact sum5_reorder
    (fun c a b i j => K c * (Γ a b c * (J a i * vi i) * (J b j * wj j)))

private lemma chartTransitionContractionReorderCorr
    {n : ℕ} (K : Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (vi wj : Fin n → ℝ) :
    (∑ c, K c *
        (∑ i, ∑ j, D c i j * vi i * wj j)) =
      ∑ i, ∑ j, (∑ c, K c * D c i j) * vi i * wj j := by
  classical
  have hLHS : (∑ c, K c *
        (∑ i, ∑ j, D c i j * vi i * wj j)) =
      ∑ c, ∑ i, ∑ j, K c * (D c i j * vi i * wj j) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hRHS : (∑ i, ∑ j, (∑ c, K c * D c i j) * vi i * wj j) =
      ∑ i, ∑ j, ∑ c, K c * (D c i j * vi i * wj j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  rw [hLHS, hRHS]
  exact sum3_reorder (fun c i j => K c * (D c i j * vi i * wj j))

omit [InnerProductSpace ℝ E] in
theorem chartChristoffelContraction_transform [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (α β : M) {p : M}
    (hp_α : p ∈ (chartAt H α).source) (hp_β : p ∈ (chartAt H β).source)
    (v w : E) :
    chartChristoffelContraction (I := I) g α v w (extChartAt I α p) =
      chartTransitionAt (I := I) β α
          (chartTransitionMap (I := I) α β (extChartAt I α p))
          (chartChristoffelContraction (I := I) g β
            (chartTransitionAt (I := I) α β (extChartAt I α p) v)
            (chartTransitionAt (I := I) α β (extChartAt I α p) w)
            (chartTransitionMap (I := I) α β (extChartAt I α p)))
        + chartTransitionSecondDerivCorrection (I := I) α β v w
            (extChartAt I α p) := by
  classical
  set x := extChartAt I α p with hx_def
  set Tx := chartTransitionMap (I := I) α β x with hTx_def
  set Jv := chartTransitionAt (I := I) α β x v with hJv
  set Jw := chartTransitionAt (I := I) α β x w with hJw
  refine (chartModelBasis E).ext_elem (fun l => ?_)
  change chartCoord (E := E) l
      (chartChristoffelContraction (I := I) g α v w x) =
    chartCoord (E := E) l
      (chartTransitionAt (I := I) β α Tx
          (chartChristoffelContraction (I := I) g β Jv Jw Tx)
        + chartTransitionSecondDerivCorrection (I := I) α β v w x)
  rw [chartCoord_chartChristoffelContraction (I := I) g α v w x l]
  have hcoord_add : ∀ a b : E,
      chartCoord (E := E) l (a + b) =
        chartCoord (E := E) l a + chartCoord (E := E) l b := by
    intro a b; simp [chartCoord, map_add]
  rw [hcoord_add]
  rw [chartCoord_chartTransitionAt (I := I) β α Tx
    (chartChristoffelContraction (I := I) g β Jv Jw Tx) l]
  have hcorr : chartCoord (E := E) l
      (chartTransitionSecondDerivCorrection (I := I) α β v w x) =
      ∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) β α Tx l c *
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
              chartCoord (E := E) i v * chartCoord (E := E) j w) := by
    rw [chartTransitionSecondDerivCorrection_def, chartCoord, map_sum,
      Finsupp.finset_sum_apply]
    rw [← hTx_def]
    rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply l l, if_pos rfl, mul_one]
    · intro k _ hkl
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply k l, if_neg hkl, mul_zero]
  rw [hcorr]
  have hinner : ∀ c : Fin (Module.finrank ℝ E),
      chartCoord (E := E) c
          (chartChristoffelContraction (I := I) g β Jv Jw Tx) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g β a b c Tx *
            (∑ i, chartTransitionJacEntry (I := I) α β x a i *
              chartCoord (E := E) i v) *
            (∑ j, chartTransitionJacEntry (I := I) α β x b j *
              chartCoord (E := E) j w) := by
    intro c
    rw [chartCoord_chartChristoffelContraction (I := I) g β Jv Jw Tx c]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hJv, hJw,
      chartCoord_chartTransitionAt (I := I) α β x v a,
      chartCoord_chartTransitionAt (I := I) α β x w b]
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) =>
    congrArg (fun t => chartTransitionJacEntry (I := I) β α Tx l c * t)
      (hinner c))]
  have htrans : ∀ i j : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α i j l x =
        (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
          (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx *
            chartTransitionJacEntry (I := I) α β x a i *
            chartTransitionJacEntry (I := I) α β x b j)) +
        (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z c j) x) := by
    intro i j
    rw [hx_def, hTx_def]
    exact chartChristoffel_transform (I := I) g α β hp_α hp_β i j l
  calc
    (∑ i, ∑ j, chartChristoffel (I := I) g α i j l x *
        chartCoord (E := E) i v * chartCoord (E := E) j w)
      = ∑ i, ∑ j,
          (((∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx *
              chartTransitionJacEntry (I := I) α β x a i *
              chartTransitionJacEntry (I := I) α β x b j)) +
          (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            partialDeriv (E := E) i
              (fun z => chartTransitionJacEntry (I := I) α β z c j) x))
            * chartCoord (E := E) i v * chartCoord (E := E) j w) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [htrans i j]
    _ = (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            (∑ a, ∑ b, chartChristoffel (I := I) g β a b c Tx *
              (∑ i, chartTransitionJacEntry (I := I) α β x a i *
                chartCoord (E := E) i v) *
              (∑ j, chartTransitionJacEntry (I := I) α β x b j *
                chartCoord (E := E) j w)))
        + (∑ c, chartTransitionJacEntry (I := I) β α Tx l c *
            (∑ i, ∑ j,
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z c j) x *
                chartCoord (E := E) i v * chartCoord (E := E) j w)) := by
        rw [chartTransitionContractionReorderMain
              (fun c => chartTransitionJacEntry (I := I) β α Tx l c)
              (fun a b c => chartChristoffel (I := I) g β a b c Tx)
              (fun a i => chartTransitionJacEntry (I := I) α β x a i)
              (fun i => chartCoord (E := E) i v)
              (fun j => chartCoord (E := E) j w)]
        rw [chartTransitionContractionReorderCorr
              (fun c => chartTransitionJacEntry (I := I) β α Tx l c)
              (fun c i j => partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z c j) x)
              (fun i => chartCoord (E := E) i v)
              (fun j => chartCoord (E := E) j w)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
lemma fderiv_chartTransitionJacEntry_eq_sum_partialDeriv
    (α β : M) (a i : Fin (Module.finrank ℝ E)) (y v : E) :
    fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a i) y v =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k v *
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) y := by
  classical
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      chartCoord (E := E) k v • (chartModelBasis E) k := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rfl
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul]
  rfl

omit [InnerProductSpace ℝ E] in
theorem chartTransitionJacEntry_comp_hasDerivAt [I.Boundaryless]
    (α β : M) (a i : Fin (Module.finrank ℝ E))
    {cE : ℝ → E} {cE' : ℝ → E} {t : ℝ}
    (hc : HasDerivAt cE (cE' t) t)
    (hmem : cE t ∈ chartTransitionSource (I := I) α β) :
    HasDerivAt (fun s => chartTransitionJacEntry (I := I) α β (cE s) a i)
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (cE' t) *
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)) t := by
  classical
  have hdiff : DifferentiableAt ℝ
      (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t) :=
    chartTransitionJacEntry_differentiableAt (I := I) α β a i hmem
  have hchain : HasDerivAt
      (fun s => chartTransitionJacEntry (I := I) α β (cE s) a i)
      (fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)
        (cE' t)) t :=
    hdiff.hasFDerivAt.comp_hasDerivAt t hc
  rw [fderiv_chartTransitionJacEntry_eq_sum_partialDeriv (I := I) α β a i] at hchain
  exact hchain

omit [InnerProductSpace ℝ E] in
theorem chartCoord_chartTransitionAt_comp_hasDerivAt [I.Boundaryless]
    (α β : M) (a : Fin (Module.finrank ℝ E)) (v : E)
    {cE : ℝ → E} {cE' : ℝ → E} {t : ℝ}
    (hc : HasDerivAt cE (cE' t) t)
    (hmem : cE t ∈ chartTransitionSource (I := I) α β) :
    HasDerivAt
      (fun s => chartCoord (E := E) a (chartTransitionAt (I := I) α β (cE s) v))
      (∑ i : Fin (Module.finrank ℝ E),
        (∑ k : Fin (Module.finrank ℝ E),
          chartCoord (E := E) k (cE' t) *
            partialDeriv (E := E) k
              (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)) *
          chartCoord (E := E) i v) t := by
  classical
  have hfun : (fun s => chartCoord (E := E) a
        (chartTransitionAt (I := I) α β (cE s) v)) =
      (fun s => ∑ i : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β (cE s) a i *
          chartCoord (E := E) i v) := by
    funext s
    rw [chartCoord_chartTransitionAt (I := I) α β (cE s) v a]
  rw [hfun]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  have hJ : HasDerivAt (fun s => chartTransitionJacEntry (I := I) α β (cE s) a i)
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (cE' t) *
          partialDeriv (E := E) k
            (fun z => chartTransitionJacEntry (I := I) α β z a i) (cE t)) t :=
    chartTransitionJacEntry_comp_hasDerivAt (I := I) α β a i hc hmem
  simpa using hJ.mul_const (chartCoord (E := E) i v)

omit [InnerProductSpace ℝ E] in
lemma chartCoord_fderiv_chartTransitionAt_general [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β)
    (a : Fin (Module.finrank ℝ E)) (v w : E) :
    chartCoord (E := E) a
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x v) w) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun z => chartTransitionJacEntry (I := I) α β z a j) x *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
  classical
  set A : E → (E →L[ℝ] E) := fun z => chartTransitionAt (I := I) α β z with hA
  have hcA : DifferentiableAt ℝ A x := by
    have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
      chartTransitionSource_isOpen (I := I) α β
    have hcd : ContDiffOn ℝ ∞
        (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E))
        (chartTransitionSource (I := I) α β) :=
      chartTransitionAt_smooth (I := I) α β
    exact (hcd.contDiffAt (h_open.mem_nhds hx)).differentiableAt (by simp)
  set coordCLM : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord a) with hcoordCLM
  set eval : (E →L[ℝ] E) →L[ℝ] ℝ :=
    coordCLM.comp (ContinuousLinearMap.apply ℝ E w) with heval
  have hstep1 :
      chartCoord (E := E) a ((fderiv ℝ A x v) w) = eval (fderiv ℝ A x v) := by
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    rfl
  have hstep2 : eval (fderiv ℝ A x v) = fderiv ℝ (fun z => eval (A z)) x v := by
    have hcomp_hasD : HasFDerivAt (fun z => eval (A z))
        (eval.comp (fderiv ℝ A x)) x :=
      eval.hasFDerivAt.comp x hcA.hasFDerivAt
    rw [hcomp_hasD.fderiv]
    rfl
  have heval_eq : (fun z => eval (A z)) =
      (fun z => ∑ j : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β z a j * chartCoord (E := E) j w) := by
    funext z
    rw [heval, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, hA,
      hcoordCLM]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    change chartCoord (E := E) a (chartTransitionAt (I := I) α β z w) = _
    exact chartCoord_chartTransitionAt (I := I) α β z w a
  rw [hstep1, hstep2, heval_eq]
  have hsum_fderiv :
      fderiv ℝ (fun z => ∑ j : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) α β z a j * chartCoord (E := E) j w) x v =
        ∑ j : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a j *
            chartCoord (E := E) j w) x v := by
    have hdiff : ∀ j : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (fun z => chartTransitionJacEntry (I := I) α β z a j *
          chartCoord (E := E) j w) x := by
      intro j
      exact (chartTransitionJacEntry_differentiableAt (I := I) α β a j hx).mul_const _
    rw [fderiv_fun_sum (fun j _ => hdiff j)]
    rw [ContinuousLinearMap.sum_apply]
  rw [hsum_fderiv]
  have hLHS_expand :
      (∑ j : Fin (Module.finrank ℝ E),
          fderiv ℝ (fun z => chartTransitionJacEntry (I := I) α β z a j *
            chartCoord (E := E) j w) x v) =
        ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun z => chartTransitionJacEntry (I := I) α β z a j) x *
            chartCoord (E := E) i v * chartCoord (E := E) j w := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [fderiv_mul_const (chartTransitionJacEntry_differentiableAt (I := I) α β a j hx) _]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_chartTransitionJacEntry_eq_sum_partialDeriv (I := I) α β a j x v]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hLHS_expand]
  rw [Finset.sum_comm]

omit [InnerProductSpace ℝ E] in
lemma fderiv_chartTransitionAt_apply_eq_pushCorrection [I.Boundaryless]
    (α β : M) {x : E} (hx : x ∈ chartTransitionSource (I := I) α β) (v w : E) :
    (fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x v) w =
      chartTransitionAt (I := I) α β x
        (chartTransitionSecondDerivCorrection (I := I) α β v w x) := by
  classical
  refine (chartModelBasis E).ext_elem (fun a => ?_)
  change chartCoord (E := E) a
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x v) w) =
    chartCoord (E := E) a
      (chartTransitionAt (I := I) α β x
        (chartTransitionSecondDerivCorrection (I := I) α β v w x))
  rw [chartCoord_fderiv_chartTransitionAt_general (I := I) α β hx a v w]
  rw [chartCoord_chartTransitionAt (I := I) α β x
    (chartTransitionSecondDerivCorrection (I := I) α β v w x) a]
  have hcorrCoord : ∀ c : Fin (Module.finrank ℝ E),
      chartCoord (E := E) c
          (chartTransitionSecondDerivCorrection (I := I) α β v w x) =
        ∑ d : Fin (Module.finrank ℝ E),
          chartTransitionJacEntry (I := I) β α
            (chartTransitionMap (I := I) α β x) c d *
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) i
                (fun z => chartTransitionJacEntry (I := I) α β z d j) x *
                chartCoord (E := E) i v * chartCoord (E := E) j w) := by
    intro c
    rw [chartTransitionSecondDerivCorrection_def, chartCoord, map_sum,
      Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply c c, if_pos rfl, mul_one]
    · intro k _ hkc
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul,
        (chartModelBasis E).repr_self_apply k c, if_neg hkc, mul_zero]
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) =>
    congrArg (fun t => chartTransitionJacEntry (I := I) α β x a c * t) (hcorrCoord c))]
  set D : Fin (Module.finrank ℝ E) → ℝ := fun d =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i
        (fun z => chartTransitionJacEntry (I := I) α β z d j) x *
        chartCoord (E := E) i v * chartCoord (E := E) j w with hD_def
  symm
  calc
    (∑ c : Fin (Module.finrank ℝ E),
        chartTransitionJacEntry (I := I) α β x a c *
          (∑ d : Fin (Module.finrank ℝ E),
            chartTransitionJacEntry (I := I) β α
              (chartTransitionMap (I := I) α β x) c d * D d))
        = ∑ d : Fin (Module.finrank ℝ E),
            (∑ c : Fin (Module.finrank ℝ E),
              chartTransitionJacEntry (I := I) α β x a c *
                chartTransitionJacEntry (I := I) β α
                  (chartTransitionMap (I := I) α β x) c d) * D d := by
          rw [show (∑ c : Fin (Module.finrank ℝ E),
                chartTransitionJacEntry (I := I) α β x a c *
                  (∑ d : Fin (Module.finrank ℝ E),
                    chartTransitionJacEntry (I := I) β α
                      (chartTransitionMap (I := I) α β x) c d * D d)) =
              ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                chartTransitionJacEntry (I := I) α β x a c *
                  (chartTransitionJacEntry (I := I) β α
                    (chartTransitionMap (I := I) α β x) c d * D d) from by
            refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [Finset.mul_sum]]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          ring
    _ = ∑ d : Fin (Module.finrank ℝ E),
            (if a = d then (1 : ℝ) else 0) * D d := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [chartTransitionJacEntry_mul_sum' (I := I) α β hx a d]
    _ = D a := by
          rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
          · rw [if_pos rfl, one_mul]
          · intro k _ hka
            rw [if_neg (fun h => hka h.symm), zero_mul]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
