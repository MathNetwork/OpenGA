import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula


noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartCoeffOnE_alpha_eq_basis_comp_pullback_eventuallyEq
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i : Fin (Module.finrank ℝ E)) :
    (chartCoeffOnE (I := I) α W i) =ᶠ[nhds (extChartAt I α x)]
      ((((chartModelBasis E).coord i).toContinuousLinearMap : E →L[ℝ] ℝ) ∘
        chartE_section_repr (I := I) α (W : ∀ x : M, TangentSpace I x) ∘
        (extChartAt I α).symm) := by
  classical
  have hint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  refine Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨interior ((extChartAt I α).target : Set E),
      isOpen_interior.mem_nhds hint, ?_⟩
  intro y hy_int
  have hy_tgt : y ∈ (extChartAt I α).target := interior_subset hy_int
  have hy_base : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_tgt
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  change chartCoeffOnE (I := I) α W i y =
    ((chartModelBasis E).coord i).toContinuousLinearMap
      (chartE_section_repr (I := I) α (W : ∀ x : M, TangentSpace I x)
        ((extChartAt I α).symm y))
  change (chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) α)
        ⟨((extChartAt I α).symm y), W ((extChartAt I α).symm y)⟩).2 i = _
  rw [← chartE_section_repr_eq_trivialization_snd (I := I) α
        (W : ∀ x : M, TangentSpace I x) hy_base]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma differentiableAt_chartE_pullback_W_alpha
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    DifferentiableAt ℝ
      (chartE_section_repr (I := I) α (W : ∀ x : M, TangentSpace I x) ∘
        (extChartAt I α).symm) (extChartAt I α x) := by
  classical
  have hW_at : MDiffAt (T% fun y => W y) x := W.mdifferentiableAt
  exact differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hW_at

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma chart_christoffel_expansion_nabla_W_alpha_chartBasis
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        (trivToE (I := I) α x
          ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x
            (chartBasisVecFiber (I := I) α j x)))) k =
      partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k) (extChartAt I α x)
      + (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j l k (extChartAt I α x) *
            chartCoeff (I := I) α W l x) := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hW_at : MDiffAt (T% fun y => W y) x := W.mdifferentiableAt
  set v : TangentSpace I x := chartBasisVecFiber (I := I) α j x with hv_def
  have h_trivToE_v : trivToE (I := I) α x v = (chartModelBasis E) j := by
    rw [hv_def]
    have heq : chartBasisVecFiber (I := I) α j x =
        trivFromE (I := I) α x ((chartModelBasis E) j) := rfl
    rw [heq, trivToE_trivFromE (I := I) α hx_base ((chartModelBasis E) j)]
  have hLC_apply :
      (LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v =
        chartLeviCivita (I := I) g α (W : ∀ x : M, TangentSpace I x) x v :=
    LeviCivita_chart_apply (I := I) g α hx hW_at v
  rw [hLC_apply]
  rw [chartLeviCivita_apply (I := I) g α (W : ∀ x : M, TangentSpace I x) hx v]
  rw [show trivToE (I := I) α x (trivFromE (I := I) α x
        (fderiv ℝ (chartE_section_repr (I := I) α
            (W : ∀ x : M, TangentSpace I x) ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α
              (W : ∀ x : M, TangentSpace I x) x) v)) =
        fderiv ℝ (chartE_section_repr (I := I) α
            (W : ∀ x : M, TangentSpace I x) ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α
              (W : ∀ x : M, TangentSpace I x) x) v from
      trivToE_trivFromE (I := I) α hx_base _]
  rw [map_add, Finsupp.add_apply]
  congr 1
  · rw [h_trivToE_v]
    rw [show ((chartModelBasis E).repr
          (fderiv ℝ (chartE_section_repr (I := I) α (W : ∀ x : M, TangentSpace I x) ∘
            (extChartAt I α).symm) (extChartAt I α x) ((chartModelBasis E) j))) k =
        (((chartModelBasis E).coord k).toContinuousLinearMap)
          (fderiv ℝ (chartE_section_repr (I := I) α (W : ∀ x : M, TangentSpace I x) ∘
            (extChartAt I α).symm) (extChartAt I α x) ((chartModelBasis E) j)) from by
      rw [← Module.Basis.coord_apply]; rfl]
    rw [← ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.fderiv (((chartModelBasis E).coord k).toContinuousLinearMap)]
    rw [← fderiv_comp (x := extChartAt I α x)
          (((chartModelBasis E).coord k).toContinuousLinearMap).differentiableAt
          (differentiableAt_chartE_pullback_W_alpha (I := I) W α hx)]
    unfold partialDeriv
    have hev := chartCoeffOnE_alpha_eq_basis_comp_pullback_eventuallyEq (I := I) W α hx k
    rw [hev.fderiv_eq]
  · rw [christoffelCorrection_apply (I := I) g α x
          (chartE_section_repr (I := I) α (W : ∀ x : M, TangentSpace I x) x) v]
    rw [h_trivToE_v]
    rw [show ((chartModelBasis E).repr
          (∑ i' : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E),
              ∑ k' : Fin (Module.finrank ℝ E),
                (((chartModelBasis E).repr ((chartModelBasis E) j)) i' *
                    ((chartModelBasis E).repr
                      (chartE_section_repr (I := I) α
                        (W : ∀ x : M, TangentSpace I x) x)) j' *
                    chartChristoffel (I := I) g α i' j' k' (extChartAt I α x)) •
                  (chartModelBasis E) k')) k =
        ∑ i' : Fin (Module.finrank ℝ E),
          ∑ j' : Fin (Module.finrank ℝ E),
            ∑ k' : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr ((chartModelBasis E) j)) i' *
                  ((chartModelBasis E).repr
                    (chartE_section_repr (I := I) α
                      (W : ∀ x : M, TangentSpace I x) x)) j' *
                  chartChristoffel (I := I) g α i' j' k' (extChartAt I α x)) *
                ((chartModelBasis E).repr ((chartModelBasis E) k')) k from by
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
        Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]]
    have hrepr_basis : ∀ (r s : Fin (Module.finrank ℝ E)),
        ((chartModelBasis E).repr ((chartModelBasis E) r)) s =
          if r = s then (1 : ℝ) else 0 := by
      intro r s
      rw [Module.Basis.repr_self]
      by_cases h : r = s
      · subst h; simp
      · simp [h]
    have hkc : ∀ (i' j' : Fin (Module.finrank ℝ E)),
        (∑ k' : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr ((chartModelBasis E) j)) i' *
                ((chartModelBasis E).repr
                  (chartE_section_repr (I := I) α
                    (W : ∀ x : M, TangentSpace I x) x)) j' *
                chartChristoffel (I := I) g α i' j' k' (extChartAt I α x)) *
              ((chartModelBasis E).repr ((chartModelBasis E) k')) k) =
        ((chartModelBasis E).repr ((chartModelBasis E) j)) i' *
          chartChristoffel (I := I) g α i' j' k (extChartAt I α x) *
          ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α
              (W : ∀ x : M, TangentSpace I x) x)) j' := by
      intro i' j'
      rw [Finset.sum_eq_single k
        (fun k' _ hne => by
          rw [hrepr_basis k' k, if_neg hne]; ring)
        (fun hm => (hm (Finset.mem_univ k)).elim)]
      rw [hrepr_basis k k, if_pos rfl]
      ring
    rw [show
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k' : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr ((chartModelBasis E) j)) i' *
                ((chartModelBasis E).repr
                  (chartE_section_repr (I := I) α
                    (W : ∀ x : M, TangentSpace I x) x)) j' *
                chartChristoffel (I := I) g α i' j' k' (extChartAt I α x)) *
              ((chartModelBasis E).repr ((chartModelBasis E) k')) k =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr ((chartModelBasis E) j)) i' *
            chartChristoffel (I := I) g α i' j' k (extChartAt I α x) *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α
                (W : ∀ x : M, TangentSpace I x) x)) j'
      from Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => hkc i' j'))]
    rw [show
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr ((chartModelBasis E) j)) i' *
            chartChristoffel (I := I) g α i' j' k (extChartAt I α x) *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α
                (W : ∀ x : M, TangentSpace I x) x)) j' =
      ∑ j' : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j j' k (extChartAt I α x) *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) α
                (W : ∀ x : M, TangentSpace I x) x)) j' from by
      rw [Finset.sum_eq_single j
        (fun i' _ hne => by
          refine Finset.sum_eq_zero (fun j' _ => ?_)
          have : ((chartModelBasis E).repr ((chartModelBasis E) j)) i' = 0 := by
            rw [hrepr_basis j i', if_neg (fun h => hne h.symm)]
          rw [this]; ring)
        (fun hm => (hm (Finset.mem_univ j)).elim)]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      have hjj : ((chartModelBasis E).repr ((chartModelBasis E) j)) j = 1 := by
        rw [hrepr_basis j j, if_pos rfl]
      rw [hjj]; ring]
    have hrepr_chartCoeff : ∀ (j' : Fin (Module.finrank ℝ E)),
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) α
            (W : ∀ x : M, TangentSpace I x) x)) j' =
        chartCoeff (I := I) α W j' x := by
      intro j'
      rw [chartE_section_repr_eq_trivialization_snd (I := I) α
            (W : ∀ x : M, TangentSpace I x) hx_base]
      rfl
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [hrepr_chartCoeff j']

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma metric_compat_coord_identity_alpha
    (g : SmoothRiemannianMetric I M)
    (α : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (extChartAt I α x) =
      (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k i l (extChartAt I α x) *
            chartGramOnE (I := I) g α l j (extChartAt I α x))
      + (∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k j l (extChartAt I α x) *
            chartGramOnE (I := I) g α l i (extChartAt I α x)) := by
  have hint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  exact
    partialDeriv_chartGramOnE_eq_chartChristoffel_sum (I := I) g α i j k hint

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLieDerivMetricMatrix_alpha_algebraic
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    chartLieDerivMetricMatrix (I := I) g W α i j x =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x k j *
            ((∑ l : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k)
                    (extChartAt I α x) *
                    (if l = k then (1 : ℝ) else 0))
              + (∑ l : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g α i l k (extChartAt I α x) *
                    chartCoeff (I := I) α W l x)))
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α x i k *
            ((∑ l : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k)
                    (extChartAt I α x) *
                    (if l = k then (1 : ℝ) else 0))
              + (∑ l : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g α j l k (extChartAt I α x) *
                    chartCoeff (I := I) α W l x))) := by
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  rw [chartLieDerivMetricMatrix_def (I := I) g W α i j x]
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b (extChartAt I α x) =
        chartGramMatrix (I := I) g α x a b := by
    intro a b
    unfold chartGramOnE
    rw [(extChartAt I α).left_inv hx_src]
  have hmc : ∀ k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (extChartAt I α x) =
        (∑ l, chartChristoffel (I := I) g α k i l (extChartAt I α x) *
            chartGramOnE (I := I) g α l j (extChartAt I α x))
        + (∑ l, chartChristoffel (I := I) g α k j l (extChartAt I α x) *
            chartGramOnE (I := I) g α l i (extChartAt I α x)) := fun k =>
    metric_compat_coord_identity_alpha (I := I) g α hx i j k
  have hcoll1 : ∀ k : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k) (extChartAt I α x) *
          (if l = k then (1 : ℝ) else 0)) =
      partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k) (extChartAt I α x) := by
    intro k
    rw [Finset.sum_eq_single k
      (fun l _ hl => by rw [if_neg hl]; ring)
      (fun hm => (hm (Finset.mem_univ k)).elim)]
    simp
  have hcoll2 : ∀ k : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k) (extChartAt I α x) *
          (if l = k then (1 : ℝ) else 0)) =
      partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k) (extChartAt I α x) := by
    intro k
    rw [Finset.sum_eq_single k
      (fun l _ hl => by rw [if_neg hl]; ring)
      (fun hm => (hm (Finset.mem_univ k)).elim)]
    simp
  conv_rhs =>
    rw [show
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g α x k j *
          ((∑ l, partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k)
              (extChartAt I α x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g α i l k (extChartAt I α x) *
                  chartCoeff (I := I) α W l x))) =
        (∑ k, chartGramMatrix (I := I) g α x k j *
          partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k) (extChartAt I α x))
        + (∑ k, chartGramMatrix (I := I) g α x k j *
          (∑ l, chartChristoffel (I := I) g α i l k (extChartAt I α x) *
              chartCoeff (I := I) α W l x))
      from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hcoll1 k, mul_add]]
    rw [show
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g α x i k *
          ((∑ l, partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k)
              (extChartAt I α x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g α j l k (extChartAt I α x) *
                  chartCoeff (I := I) α W l x))) =
        (∑ k, chartGramMatrix (I := I) g α x i k *
          partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k) (extChartAt I α x))
        + (∑ k, chartGramMatrix (I := I) g α x i k *
          (∑ l, chartChristoffel (I := I) g α j l k (extChartAt I α x) *
              chartCoeff (I := I) α W l x))
      from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hcoll2 k, mul_add]]
  rw [show
    (∑ k : Fin (Module.finrank ℝ E),
      chartCoeff (I := I) α W k x *
        partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (extChartAt I α x))
    = (∑ k, chartCoeff (I := I) α W k x *
      (∑ l, chartChristoffel (I := I) g α k i l (extChartAt I α x) *
          chartGramOnE (I := I) g α l j (extChartAt I α x)))
      + (∑ k, chartCoeff (I := I) α W k x *
      (∑ l, chartChristoffel (I := I) g α k j l (extChartAt I α x) *
          chartGramOnE (I := I) g α l i (extChartAt I α x))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hmc k, mul_add]]
  have hreshape_H1 :
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α W k x *
          (∑ l, chartChristoffel (I := I) g α k i l (extChartAt I α x) *
              chartGramOnE (I := I) g α l j (extChartAt I α x))) =
      (∑ k, chartGramMatrix (I := I) g α x k j *
        (∑ l, chartChristoffel (I := I) g α i l k (extChartAt I α x) *
            chartCoeff (I := I) α W l x)) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α W k x *
            (∑ l, chartChristoffel (I := I) g α k i l (extChartAt I α x) *
                chartGramOnE (I := I) g α l j (extChartAt I α x))) =
        ∑ k, ∑ l,
          chartCoeff (I := I) α W k x *
            chartChristoffel (I := I) g α k i l (extChartAt I α x) *
            chartGramOnE (I := I) g α l j (extChartAt I α x) from
      Finset.sum_congr rfl (fun k _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hgram l j]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α W k x *
            chartChristoffel (I := I) g α k i l (extChartAt I α x) *
            chartGramMatrix (I := I) g α x l j) =
        chartGramMatrix (I := I) g α x l j *
          ∑ k, chartChristoffel (I := I) g α i k l (extChartAt I α x) *
            chartCoeff (I := I) α W k x from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [chartChristoffel_symm (I := I) g α k i l (extChartAt I α x)]
        ring)]
  have hreshape_H2 :
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α W k x *
          (∑ l, chartChristoffel (I := I) g α k j l (extChartAt I α x) *
              chartGramOnE (I := I) g α l i (extChartAt I α x))) =
      (∑ k, chartGramMatrix (I := I) g α x i k *
        (∑ l, chartChristoffel (I := I) g α j l k (extChartAt I α x) *
            chartCoeff (I := I) α W l x)) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α W k x *
            (∑ l, chartChristoffel (I := I) g α k j l (extChartAt I α x) *
                chartGramOnE (I := I) g α l i (extChartAt I α x))) =
        ∑ k, ∑ l,
          chartCoeff (I := I) α W k x *
            chartChristoffel (I := I) g α k j l (extChartAt I α x) *
            chartGramOnE (I := I) g α l i (extChartAt I α x) from
      Finset.sum_congr rfl (fun k _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hgram l i]
    rw [show chartGramMatrix (I := I) g α x l i =
          chartGramMatrix (I := I) g α x i l from by
      rw [chartGramMatrix_apply, chartGramMatrix_apply]
      exact g.symm x _ _]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) α W k x *
            chartChristoffel (I := I) g α k j l (extChartAt I α x) *
            chartGramMatrix (I := I) g α x i l) =
        chartGramMatrix (I := I) g α x i l *
          ∑ k, chartChristoffel (I := I) g α j k l (extChartAt I α x) *
            chartCoeff (I := I) α W k x from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [chartChristoffel_symm (I := I) g α k j l (extChartAt I α x)]
        ring)]
  rw [hreshape_H1, hreshape_H2]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ∀ x ∈ chartLeviCivitaGoodSet (I := I) α,
      chartLieDerivMetricMatrix (I := I) g W α i j x =
        lieDerivMetric (I := I) g W x
          (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x) := by
  intro x hx
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  set vα : TangentSpace I x := chartBasisVecFiber (I := I) α i x with hvα_def
  set wα : TangentSpace I x := chartBasisVecFiber (I := I) α j x with hwα_def
  rw [cartan_formula_for_lie_deriv_metric (I := I) g W x vα wα]
  have hRHS1 :
      g.inner x ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x vα) wα =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr
              (trivToE (I := I) α x
                ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x vα))) i' *
            ((chartModelBasis E).repr (trivToE (I := I) α x wα)) j' *
            chartGramOnE (I := I) g α i' j' (extChartAt I α x) :=
    g_inner_eq_chart_sum (I := I) g α hx_base hx_src
      ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x vα) wα
  have hRHS2 :
      g.inner x vα ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x wα) =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (trivToE (I := I) α x vα)) i' *
            ((chartModelBasis E).repr
              (trivToE (I := I) α x
                ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x wα))) j' *
            chartGramOnE (I := I) g α i' j' (extChartAt I α x) :=
    g_inner_eq_chart_sum (I := I) g α hx_base hx_src vα
      ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x wα)
  rw [hRHS1, hRHS2]
  have h_trivToE_vα : trivToE (I := I) α x vα = (chartModelBasis E) i := by
    rw [hvα_def]
    have heq : chartBasisVecFiber (I := I) α i x =
        trivFromE (I := I) α x ((chartModelBasis E) i) := rfl
    rw [heq, trivToE_trivFromE (I := I) α hx_base ((chartModelBasis E) i)]
  have h_trivToE_wα : trivToE (I := I) α x wα = (chartModelBasis E) j := by
    rw [hwα_def]
    have heq : chartBasisVecFiber (I := I) α j x =
        trivFromE (I := I) α x ((chartModelBasis E) j) := rfl
    rw [heq, trivToE_trivFromE (I := I) α hx_base ((chartModelBasis E) j)]
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b (extChartAt I α x) =
        chartGramMatrix (I := I) g α x a b := by
    intro a b
    unfold chartGramOnE
    rw [(extChartAt I α).left_inv hx_src]
  have hrepr_basis : ∀ (r s : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr ((chartModelBasis E) r)) s =
        if r = s then (1 : ℝ) else 0 := by
    intro r s
    rw [Module.Basis.repr_self]
    by_cases h : r = s
    · subst h; simp
    · simp [h]
  rw [show
    (∑ i' : Fin (Module.finrank ℝ E),
      ∑ j' : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (trivToE (I := I) α x
              ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x vα))) i' *
          ((chartModelBasis E).repr (trivToE (I := I) α x wα)) j' *
          chartGramOnE (I := I) g α i' j' (extChartAt I α x)) =
    (∑ i' : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (trivToE (I := I) α x
            ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x vα))) i' *
        chartGramMatrix (I := I) g α x i' j)
    from by
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      rw [Finset.sum_eq_single j
        (fun j' _ hne => by
          rw [h_trivToE_wα, hrepr_basis j j', if_neg (fun h => hne h.symm)]
          ring)
        (fun hm => (hm (Finset.mem_univ j)).elim)]
      rw [h_trivToE_wα, hrepr_basis j j, if_pos rfl, hgram i' j]
      ring]
  rw [show
    (∑ i' : Fin (Module.finrank ℝ E),
      ∑ j' : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (trivToE (I := I) α x vα)) i' *
          ((chartModelBasis E).repr
            (trivToE (I := I) α x
              ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x wα))) j' *
          chartGramOnE (I := I) g α i' j' (extChartAt I α x)) =
    (∑ j' : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (trivToE (I := I) α x
            ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x wα))) j' *
        chartGramMatrix (I := I) g α x i j')
    from by
      rw [Finset.sum_eq_single i
        (fun i' _ hne => by
          refine Finset.sum_eq_zero (fun j' _ => ?_)
          rw [h_trivToE_vα, hrepr_basis i i', if_neg (fun h => hne h.symm)]
          ring)
        (fun hm => (hm (Finset.mem_univ i)).elim)]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [h_trivToE_vα, hrepr_basis i i, if_pos rfl, hgram i j']
      ring]
  have hLC_vα : ∀ (i' : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr
        (trivToE (I := I) α x
          ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x vα))) i' =
        partialDeriv (E := E) i (chartCoeffOnE (I := I) α W i') (extChartAt I α x)
        + (∑ l : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i l i' (extChartAt I α x) *
              chartCoeff (I := I) α W l x) := by
    intro i'
    rw [hvα_def]
    exact chart_christoffel_expansion_nabla_W_alpha_chartBasis (I := I) g W α hx i i'
  have hLC_wα : ∀ (j' : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr
        (trivToE (I := I) α x
          ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x wα))) j' =
        partialDeriv (E := E) j (chartCoeffOnE (I := I) α W j') (extChartAt I α x)
        + (∑ l : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j l j' (extChartAt I α x) *
              chartCoeff (I := I) α W l x) := by
    intro j'
    rw [hwα_def]
    exact chart_christoffel_expansion_nabla_W_alpha_chartBasis (I := I) g W α hx j j'
  rw [show
    (∑ i' : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (trivToE (I := I) α x
            ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x vα))) i' *
        chartGramMatrix (I := I) g α x i' j) =
    (∑ k : Fin (Module.finrank ℝ E),
      chartGramMatrix (I := I) g α x k j *
        ((∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k)
              (extChartAt I α x) *
              (if l = k then (1 : ℝ) else 0))
          + (∑ l : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α i l k (extChartAt I α x) *
                chartCoeff (I := I) α W l x)))
    from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hLC_vα k]
      have hpd_collapse :
          (∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k) (extChartAt I α x) *
              (if l = k then (1 : ℝ) else 0)) =
          partialDeriv (E := E) i (chartCoeffOnE (I := I) α W k) (extChartAt I α x) := by
        rw [Finset.sum_eq_single k
          (fun l _ hl => by rw [if_neg hl]; ring)
          (fun hm => (hm (Finset.mem_univ k)).elim)]
        simp
      rw [hpd_collapse]
      ring]
  rw [show
    (∑ j' : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          (trivToE (I := I) α x
            ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x wα))) j' *
        chartGramMatrix (I := I) g α x i j') =
    (∑ k : Fin (Module.finrank ℝ E),
      chartGramMatrix (I := I) g α x i k *
        ((∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k)
              (extChartAt I α x) *
              (if l = k then (1 : ℝ) else 0))
          + (∑ l : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α j l k (extChartAt I α x) *
                chartCoeff (I := I) α W l x)))
    from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hLC_wα k]
      have hpd_collapse :
          (∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k) (extChartAt I α x) *
              (if l = k then (1 : ℝ) else 0)) =
          partialDeriv (E := E) j (chartCoeffOnE (I := I) α W k) (extChartAt I α x) := by
        rw [Finset.sum_eq_single k
          (fun l _ hl => by rw [if_neg hl]; ring)
          (fun hm => (hm (Finset.mem_univ k)).elim)]
        simp
      rw [hpd_collapse]
      ring]
  exact chartLieDerivMetricMatrix_alpha_algebraic (I := I) g W α hx i j

end DeTurck
end PDE
end DifferentialGeometry

end
