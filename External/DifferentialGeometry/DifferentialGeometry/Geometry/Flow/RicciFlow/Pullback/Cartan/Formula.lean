import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metric_compat_coord_identity
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
    (mem_chartLeviCivitaGoodSet_iff.mp hx).2.2
  exact
    partialDeriv_chartGramOnE_eq_chartChristoffel_sum (I := I) g α i j k hint

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma cartan_trivToE_self_apply (x : M) (v : TangentSpace I x) :
    trivToE (I := I) x x v = v := by
  classical
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
    (x₀ := x) (x := x) (mem_chart_source H x)
  have h2 : (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    rw [show (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
          (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x from rfl]
    rw [h]; exact mfderiv_extChartAt_self (I := I) (x := x)
  rw [show trivToE (I := I) x x v = (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) v
        from rfl, h2]; rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma cartan_trivFromE_self_apply (x : M) (w : E) :
    trivFromE (I := I) x x w = w := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have h := trivToE_trivFromE (I := I) x hbase w
  rwa [cartan_trivToE_self_apply (I := I) x (trivFromE (I := I) x x w)] at h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private lemma chartCoeffOnE_self_eq_basis_comp_pullback_eventuallyEq
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (i : Fin (Module.finrank ℝ E)) :
    (chartCoeffOnE (I := I) x W i) =ᶠ[nhds (extChartAt I x x)]
      ((((chartModelBasis E).coord i).toContinuousLinearMap : E →L[ℝ] ℝ) ∘
        chartE_section_repr (I := I) x (W : ∀ x : M, TangentSpace I x) ∘
        (extChartAt I x).symm) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx_good
  refine Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨interior ((extChartAt I x).target : Set E),
      isOpen_interior.mem_nhds hint, ?_⟩
  intro y hy_int
  have hy_tgt : y ∈ (extChartAt I x).target := interior_subset hy_int
  have hy_base : (extChartAt I x).symm y ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    have hsource : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hy_tgt
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  change chartCoeffOnE (I := I) x W i y =
    ((chartModelBasis E).coord i).toContinuousLinearMap
      (chartE_section_repr (I := I) x (W : ∀ x : M, TangentSpace I x)
        ((extChartAt I x).symm y))
  change (chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) x)
        ⟨((extChartAt I x).symm y), W ((extChartAt I x).symm y)⟩).2 i = _
  rw [← chartE_section_repr_eq_trivialization_snd (I := I) x
        (W : ∀ x : M, TangentSpace I x) hy_base]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
private lemma differentiableAt_chartE_pullback_self
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    DifferentiableAt ℝ
      (chartE_section_repr (I := I) x (W : ∀ x : M, TangentSpace I x) ∘
        (extChartAt I x).symm) (extChartAt I x x) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hW_at : MDiffAt (T% fun y => W y) x := W.mdifferentiableAt
  exact differentiableAt_chartE_pullback_of_MDiff (I := I) x hx_good hW_at

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chart_christoffel_expansion_of_nabla_on_vf
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr
        ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v)) i =
      (∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) j *
            partialDeriv (E := E) j (chartCoeffOnE (I := I) x W i)
              (extChartAt I x x))
      + (∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) j *
              chartChristoffel (I := I) g x j k i (extChartAt I x x) *
              chartCoeff (I := I) x W k x) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good
  have hW_at : MDiffAt (T% fun y => W y) x := W.mdifferentiableAt
  have hLC_apply :
      (LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v =
        chartLeviCivita (I := I) g x (W : ∀ x : M, TangentSpace I x) x v :=
    LeviCivita_chart_apply (I := I) g x hx_good hW_at v
  rw [hLC_apply]
  rw [chartLeviCivita_apply (I := I) g x (W : ∀ x : M, TangentSpace I x) hx_good v]
  rw [cartan_trivFromE_self_apply (I := I) x _]
  rw [map_add, Finsupp.add_apply]
  congr 1
  · rw [cartan_trivToE_self_apply (I := I) x v]
    set u : E := v with hu_def
    set F : E → E := chartE_section_repr (I := I) x (W : ∀ x : M, TangentSpace I x) ∘
        (extChartAt I x).symm with hF_def
    have hudecomp : u = ∑ j, ((chartModelBasis E).repr u) j • (chartModelBasis E) j :=
      (Module.Basis.sum_repr (chartModelBasis E) u).symm
    have hfderiv_sum :
        fderiv ℝ F (extChartAt I x x) u =
          ∑ j, ((chartModelBasis E).repr u) j • fderiv ℝ F (extChartAt I x x)
            ((chartModelBasis E) j) := by
      conv_lhs => rw [hudecomp]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [(fderiv ℝ F (extChartAt I x x)).map_smul]
    rw [hfderiv_sum]
    rw [show
      ((chartModelBasis E).repr
        (∑ j : Fin (Module.finrank ℝ E), ((chartModelBasis E).repr u) j •
          fderiv ℝ F (extChartAt I x x) ((chartModelBasis E) j))) i =
      ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr u) j *
          ((chartModelBasis E).repr (fderiv ℝ F (extChartAt I x x)
            ((chartModelBasis E) j))) i from by
      rw [map_sum]
      simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul]]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [show ((chartModelBasis E).repr (fderiv ℝ F (extChartAt I x x)
          ((chartModelBasis E) j))) i =
        (((chartModelBasis E).coord i).toContinuousLinearMap)
          (fderiv ℝ F (extChartAt I x x) ((chartModelBasis E) j)) from by
      rw [← Module.Basis.coord_apply]; rfl]
    rw [← ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.fderiv (((chartModelBasis E).coord i).toContinuousLinearMap)]
    rw [← fderiv_comp (x := extChartAt I x x)
          (((chartModelBasis E).coord i).toContinuousLinearMap).differentiableAt
          (differentiableAt_chartE_pullback_self (I := I) W x)]
    unfold partialDeriv
    have hev := chartCoeffOnE_self_eq_basis_comp_pullback_eventuallyEq (I := I) W x i
    rw [hev.fderiv_eq]
  · rw [christoffelCorrection_apply (I := I) g x x
          (chartE_section_repr (I := I) x (W : ∀ x : M, TangentSpace I x) x) v]
    rw [cartan_trivToE_self_apply (I := I) x v]
    rw [show ((chartModelBasis E).repr
          (∑ i' : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E),
              ∑ k' : Fin (Module.finrank ℝ E),
                (((chartModelBasis E).repr v) i' *
                    ((chartModelBasis E).repr
                      (chartE_section_repr (I := I) x
                        (W : ∀ x : M, TangentSpace I x) x)) j' *
                    chartChristoffel (I := I) g x i' j' k' (extChartAt I x x)) •
                  (chartModelBasis E) k')) i =
        ∑ i' : Fin (Module.finrank ℝ E),
          ∑ j' : Fin (Module.finrank ℝ E),
            ∑ k' : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr v) i' *
                  ((chartModelBasis E).repr
                    (chartE_section_repr (I := I) x
                      (W : ∀ x : M, TangentSpace I x) x)) j' *
                  chartChristoffel (I := I) g x i' j' k' (extChartAt I x x)) *
                ((chartModelBasis E).repr ((chartModelBasis E) k')) i from by
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
            (((chartModelBasis E).repr v) i' *
                ((chartModelBasis E).repr
                  (chartE_section_repr (I := I) x
                    (W : ∀ x : M, TangentSpace I x) x)) j' *
                chartChristoffel (I := I) g x i' j' k' (extChartAt I x x)) *
              ((chartModelBasis E).repr ((chartModelBasis E) k')) i) =
        ((chartModelBasis E).repr v) i' *
          chartChristoffel (I := I) g x i' j' i (extChartAt I x x) *
          ((chartModelBasis E).repr
            (chartE_section_repr (I := I) x
              (W : ∀ x : M, TangentSpace I x) x)) j' := by
      intro i' j'
      rw [Finset.sum_eq_single i
        (fun k' _ hne => by
          rw [hrepr_basis k' i, if_neg hne]; ring)
        (fun hm => (hm (Finset.mem_univ i)).elim)]
      rw [hrepr_basis i i, if_pos rfl]
      ring
    rw [show
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k' : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr v) i' *
                ((chartModelBasis E).repr
                  (chartE_section_repr (I := I) x
                    (W : ∀ x : M, TangentSpace I x) x)) j' *
                chartChristoffel (I := I) g x i' j' k' (extChartAt I x x)) *
              ((chartModelBasis E).repr ((chartModelBasis E) k')) i =
      ∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i' *
            chartChristoffel (I := I) g x i' j' i (extChartAt I x x) *
            ((chartModelBasis E).repr
              (chartE_section_repr (I := I) x
                (W : ∀ x : M, TangentSpace I x) x)) j'
      from Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => hkc i' j'))]
    have hrepr_chartCoeff : ∀ (j' : Fin (Module.finrank ℝ E)),
        ((chartModelBasis E).repr
          (chartE_section_repr (I := I) x
            (W : ∀ x : M, TangentSpace I x) x)) j' =
        chartCoeff (I := I) x W j' x := by
      intro j'
      rw [chartE_section_repr_eq_trivialization_snd (I := I) x
            (W : ∀ x : M, TangentSpace I x) hx_base]
      rfl
    refine Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [hrepr_chartCoeff j']

omit [SigmaCompactSpace M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem cartan_formula_chart_algebra
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    chartLieDerivMetricMatrix (I := I) g W x i j x =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x k j *
            ((∑ l : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
                    (extChartAt I x x) *
                    (if l = k then (1 : ℝ) else 0))
              + (∑ l : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                    chartCoeff (I := I) x W l x)))
      + (∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g x x i k *
            ((∑ l : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
                    (extChartAt I x x) *
                    (if l = k then (1 : ℝ) else 0))
              + (∑ l : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                    chartCoeff (I := I) x W l x))) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hx_src : x ∈ (extChartAt I x).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx_good
  rw [chartLieDerivMetricMatrix_def (I := I) g W x i j x]
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x a b (extChartAt I x x) =
        chartGramMatrix (I := I) g x x a b := by
    intro a b
    unfold chartGramOnE
    rw [(extChartAt I x).left_inv hx_src]
  have hmc : ∀ k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartGramOnE (I := I) g x i j) (extChartAt I x x) =
        (∑ l, chartChristoffel (I := I) g x k i l (extChartAt I x x) *
            chartGramOnE (I := I) g x l j (extChartAt I x x))
        + (∑ l, chartChristoffel (I := I) g x k j l (extChartAt I x x) *
            chartGramOnE (I := I) g x l i (extChartAt I x x)) := fun k =>
    metric_compat_coord_identity (I := I) g x hx_good i j k
  have hcoll1 : ∀ k : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x) *
          (if l = k then (1 : ℝ) else 0)) =
      partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x) := by
    intro k
    rw [Finset.sum_eq_single k
      (fun l _ hl => by rw [if_neg hl]; ring)
      (fun hm => (hm (Finset.mem_univ k)).elim)]
    simp
  have hcoll2 : ∀ k : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x) *
          (if l = k then (1 : ℝ) else 0)) =
      partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x) := by
    intro k
    rw [Finset.sum_eq_single k
      (fun l _ hl => by rw [if_neg hl]; ring)
      (fun hm => (hm (Finset.mem_univ k)).elim)]
    simp
  conv_rhs =>
    rw [show
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x k j *
          ((∑ l, partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                  chartCoeff (I := I) x W l x))) =
        (∑ k, chartGramMatrix (I := I) g x x k j *
          partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x))
        + (∑ k, chartGramMatrix (I := I) g x x k j *
          (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
              chartCoeff (I := I) x W l x))
      from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hcoll1 k, mul_add]]
    rw [show
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x i k *
          ((∑ l, partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                  chartCoeff (I := I) x W l x))) =
        (∑ k, chartGramMatrix (I := I) g x x i k *
          partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x))
        + (∑ k, chartGramMatrix (I := I) g x x i k *
          (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
              chartCoeff (I := I) x W l x))
      from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hcoll2 k, mul_add]]
  rw [show
    (∑ k : Fin (Module.finrank ℝ E),
      chartCoeff (I := I) x W k x *
        partialDeriv (E := E) k (chartGramOnE (I := I) g x i j) (extChartAt I x x))
    = (∑ k, chartCoeff (I := I) x W k x *
      (∑ l, chartChristoffel (I := I) g x k i l (extChartAt I x x) *
          chartGramOnE (I := I) g x l j (extChartAt I x x)))
      + (∑ k, chartCoeff (I := I) x W k x *
      (∑ l, chartChristoffel (I := I) g x k j l (extChartAt I x x) *
          chartGramOnE (I := I) g x l i (extChartAt I x x))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hmc k, mul_add]]
  have hreshape_H1 :
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) x W k x *
          (∑ l, chartChristoffel (I := I) g x k i l (extChartAt I x x) *
              chartGramOnE (I := I) g x l j (extChartAt I x x))) =
      (∑ k, chartGramMatrix (I := I) g x x k j *
        (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
            chartCoeff (I := I) x W l x)) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) x W k x *
            (∑ l, chartChristoffel (I := I) g x k i l (extChartAt I x x) *
                chartGramOnE (I := I) g x l j (extChartAt I x x))) =
        ∑ k, ∑ l,
          chartCoeff (I := I) x W k x *
            chartChristoffel (I := I) g x k i l (extChartAt I x x) *
            chartGramOnE (I := I) g x l j (extChartAt I x x) from
      Finset.sum_congr rfl (fun k _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hgram l j]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) x W k x *
            chartChristoffel (I := I) g x k i l (extChartAt I x x) *
            chartGramMatrix (I := I) g x x l j) =
        chartGramMatrix (I := I) g x x l j *
          ∑ k, chartChristoffel (I := I) g x i k l (extChartAt I x x) *
            chartCoeff (I := I) x W k x from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [chartChristoffel_symm (I := I) g x k i l (extChartAt I x x)]
        ring)]
  have hreshape_H2 :
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) x W k x *
          (∑ l, chartChristoffel (I := I) g x k j l (extChartAt I x x) *
              chartGramOnE (I := I) g x l i (extChartAt I x x))) =
      (∑ k, chartGramMatrix (I := I) g x x i k *
        (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
            chartCoeff (I := I) x W l x)) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) x W k x *
            (∑ l, chartChristoffel (I := I) g x k j l (extChartAt I x x) *
                chartGramOnE (I := I) g x l i (extChartAt I x x))) =
        ∑ k, ∑ l,
          chartCoeff (I := I) x W k x *
            chartChristoffel (I := I) g x k j l (extChartAt I x x) *
            chartGramOnE (I := I) g x l i (extChartAt I x x) from
      Finset.sum_congr rfl (fun k _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hgram l i]
    rw [show chartGramMatrix (I := I) g x x l i =
          chartGramMatrix (I := I) g x x i l from by
      rw [chartGramMatrix_apply, chartGramMatrix_apply]
      exact g.symm x _ _]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          chartCoeff (I := I) x W k x *
            chartChristoffel (I := I) g x k j l (extChartAt I x x) *
            chartGramMatrix (I := I) g x x i l) =
        chartGramMatrix (I := I) g x x i l *
          ∑ k, chartChristoffel (I := I) g x j k l (extChartAt I x x) *
            chartCoeff (I := I) x W k x from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [chartChristoffel_symm (I := I) g x k j l (extChartAt I x x)]
        ring)]
  rw [hreshape_H1, hreshape_H2]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem cartan_formula_for_lie_deriv_metric
    (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) g W x v w =
      g.inner x ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v) w
      + g.inner x v
          ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w) := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx_good
  have hx_src : x ∈ (extChartAt I x).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx_good
  rw [lieDerivMetric_apply (I := I) g W x v w]
  have hLDM_eq : ∀ (i j : Fin (Module.finrank ℝ E)),
      lieDerivMetricMatrix (I := I) g W i j x =
        chartLieDerivMetricMatrix (I := I) g W x i j x := fun i j => rfl
  rw [show
    (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
      ((chartModelBasis E).repr w) j * lieDerivMetricMatrix (I := I) g W i j x) =
    (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
      ((chartModelBasis E).repr w) j *
      chartLieDerivMetricMatrix (I := I) g W x i j x)
    from Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by rw [hLDM_eq]))]
  rw [show
    (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
      ((chartModelBasis E).repr w) j *
      chartLieDerivMetricMatrix (I := I) g W x i j x) =
    (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
      ((chartModelBasis E).repr w) j *
      ((∑ k, chartGramMatrix (I := I) g x x k j *
          ((∑ l, partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                chartCoeff (I := I) x W l x)))
        + (∑ k, chartGramMatrix (I := I) g x x i k *
          ((∑ l, partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                chartCoeff (I := I) x W l x)))))
    from Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by
        rw [cartan_formula_chart_algebra (I := I) g W i j x]))]
  have hcoll : ∀ (a : Fin (Module.finrank ℝ E)) (k : Fin (Module.finrank ℝ E)),
      (∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) a (chartCoeffOnE (I := I) x W k) (extChartAt I x x) *
          (if l = k then (1 : ℝ) else 0)) =
        partialDeriv (E := E) a (chartCoeffOnE (I := I) x W k) (extChartAt I x x) := by
    intro a k
    rw [Finset.sum_eq_single k
      (fun l _ hl => by rw [if_neg hl]; ring)
      (fun hm => (hm (Finset.mem_univ k)).elim)]
    simp
  rw [show
    (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
      ((chartModelBasis E).repr w) j *
      ((∑ k, chartGramMatrix (I := I) g x x k j *
          ((∑ l, partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                chartCoeff (I := I) x W l x)))
        + (∑ k, chartGramMatrix (I := I) g x x i k *
          ((∑ l, partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
              (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
            + (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                chartCoeff (I := I) x W l x))))) =
    (∑ i, ∑ j, ∑ k,
      ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
        chartGramMatrix (I := I) g x x k j *
        partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x))
    + (∑ i, ∑ j, ∑ k, ∑ l,
      ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
        chartGramMatrix (I := I) g x x k j *
        chartChristoffel (I := I) g x i l k (extChartAt I x x) *
        chartCoeff (I := I) x W l x)
    + (∑ i, ∑ j, ∑ k,
      ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
        chartGramMatrix (I := I) g x x i k *
        partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x))
    + (∑ i, ∑ j, ∑ k, ∑ l,
      ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
        chartGramMatrix (I := I) g x x i k *
        chartChristoffel (I := I) g x j l k (extChartAt I x x) *
        chartCoeff (I := I) x W l x)
    from by
      rw [show
        (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
          ((chartModelBasis E).repr w) j *
          ((∑ k, chartGramMatrix (I := I) g x x k j *
              ((∑ l, partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
                  (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
                + (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                    chartCoeff (I := I) x W l x)))
            + (∑ k, chartGramMatrix (I := I) g x x i k *
              ((∑ l, partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
                  (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
                + (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                    chartCoeff (I := I) x W l x))))) =
        (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
          ((chartModelBasis E).repr w) j *
          (∑ k, chartGramMatrix (I := I) g x x k j *
            ((∑ l, partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
                (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
              + (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                  chartCoeff (I := I) x W l x))))
        + (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
          ((chartModelBasis E).repr w) j *
          (∑ k, chartGramMatrix (I := I) g x x i k *
            ((∑ l, partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
                (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
              + (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                  chartCoeff (I := I) x W l x))))
        from by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [mul_add]]
      rw [show
        (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
          ((chartModelBasis E).repr w) j *
          (∑ k, chartGramMatrix (I := I) g x x k j *
            ((∑ l, partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k)
                (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
              + (∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                  chartCoeff (I := I) x W l x)))) =
        (∑ i, ∑ j, ∑ k,
          ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
            chartGramMatrix (I := I) g x x k j *
            partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x))
        + (∑ i, ∑ j, ∑ k, ∑ l,
          ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
            chartGramMatrix (I := I) g x x k j *
            chartChristoffel (I := I) g x i l k (extChartAt I x x) *
            chartCoeff (I := I) x W l x)
        from by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [hcoll i k]
          rw [show
              ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
                (chartGramMatrix (I := I) g x x k j *
                  (partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x)
                    + ∑ l, chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                        chartCoeff (I := I) x W l x)) =
              ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
                chartGramMatrix (I := I) g x x k j *
                partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x)
              + ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
                    chartGramMatrix (I := I) g x x k j *
                    chartChristoffel (I := I) g x i l k (extChartAt I x x) *
                    chartCoeff (I := I) x W l x from by
            rw [mul_add, mul_add]
            congr 1
            · ring
            · rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun l _ => by ring)]]
      rw [show
        (∑ i, ∑ j, ((chartModelBasis E).repr v) i *
          ((chartModelBasis E).repr w) j *
          (∑ k, chartGramMatrix (I := I) g x x i k *
            ((∑ l, partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k)
                (extChartAt I x x) * (if l = k then (1 : ℝ) else 0))
              + (∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                  chartCoeff (I := I) x W l x)))) =
        (∑ i, ∑ j, ∑ k,
          ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
            chartGramMatrix (I := I) g x x i k *
            partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x))
        + (∑ i, ∑ j, ∑ k, ∑ l,
          ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
            chartGramMatrix (I := I) g x x i k *
            chartChristoffel (I := I) g x j l k (extChartAt I x x) *
            chartCoeff (I := I) x W l x)
        from by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [hcoll j k]
          rw [show
              ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
                (chartGramMatrix (I := I) g x x i k *
                  (partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x)
                    + ∑ l, chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                        chartCoeff (I := I) x W l x)) =
              ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
                chartGramMatrix (I := I) g x x i k *
                partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x)
              + ∑ l : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
                    chartGramMatrix (I := I) g x x i k *
                    chartChristoffel (I := I) g x j l k (extChartAt I x x) *
                    chartCoeff (I := I) x W l x from by
            rw [mul_add, mul_add]
            congr 1
            · ring
            · rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun l _ => by ring)]]
      ring]
  have hRHS1 :
      g.inner x ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v) w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr
              (trivToE (I := I) x x
                ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v))) i *
            ((chartModelBasis E).repr (trivToE (I := I) x x w)) j *
            chartGramOnE (I := I) g x i j (extChartAt I x x) :=
    g_inner_eq_chart_sum (I := I) g x (x := x) hx_base hx_src
      ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v) w
  have hRHS2 :
      g.inner x v ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (trivToE (I := I) x x v)) i *
            ((chartModelBasis E).repr
              (trivToE (I := I) x x
                ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w))) j *
            chartGramOnE (I := I) g x i j (extChartAt I x x) :=
    g_inner_eq_chart_sum (I := I) g x (x := x) hx_base hx_src v
      ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w)
  rw [hRHS1, hRHS2]
  have htrivId : ∀ u : TangentSpace I x, trivToE (I := I) x x u = u :=
    fun u => cartan_trivToE_self_apply (I := I) x u
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g x a b (extChartAt I x x) =
        chartGramMatrix (I := I) g x x a b := by
    intro a b
    unfold chartGramOnE
    rw [(extChartAt I x).left_inv hx_src]
  rw [show
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (trivToE (I := I) x x
              ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v))) i *
          ((chartModelBasis E).repr (trivToE (I := I) x x w)) j *
          chartGramOnE (I := I) g x i j (extChartAt I x x)) =
    (∑ i, ∑ j,
      ((chartModelBasis E).repr
        ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v)) i *
      ((chartModelBasis E).repr w) j *
      chartGramMatrix (I := I) g x x i j)
    from Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by
        rw [htrivId _, htrivId w, hgram i j]))]
  rw [show
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (trivToE (I := I) x x v)) i *
          ((chartModelBasis E).repr
            (trivToE (I := I) x x
              ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w))) j *
          chartGramOnE (I := I) g x i j (extChartAt I x x)) =
    (∑ i, ∑ j,
      ((chartModelBasis E).repr v) i *
      ((chartModelBasis E).repr
        ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w)) j *
      chartGramMatrix (I := I) g x x i j)
    from Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by
        rw [htrivId v, htrivId _, hgram i j]))]
  rw [show
    (∑ i, ∑ j,
      ((chartModelBasis E).repr
        ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v)) i *
      ((chartModelBasis E).repr w) j *
      chartGramMatrix (I := I) g x x i j) =
    (∑ i, ∑ j,
      ((∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) j' *
            partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i)
              (extChartAt I x x))
        + (∑ j' : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) j' *
                chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
                chartCoeff (I := I) x W k x)) *
      ((chartModelBasis E).repr w) j *
      chartGramMatrix (I := I) g x x i j)
    from Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by
        rw [chart_christoffel_expansion_of_nabla_on_vf (I := I) g W x v i]))]
  rw [show
    (∑ i, ∑ j,
      ((chartModelBasis E).repr v) i *
      ((chartModelBasis E).repr
        ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w)) j *
      chartGramMatrix (I := I) g x x i j) =
    (∑ i, ∑ j,
      ((chartModelBasis E).repr v) i *
      ((∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr w) j' *
            partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W j)
              (extChartAt I x x))
        + (∑ j' : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr w) j' *
                chartChristoffel (I := I) g x j' k j (extChartAt I x x) *
                chartCoeff (I := I) x W k x)) *
      chartGramMatrix (I := I) g x x i j)
    from Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by
        rw [chart_christoffel_expansion_of_nabla_on_vf (I := I) g W x w j]))]
  rw [show
    (∑ i, ∑ j,
      ((∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) j' *
            partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i)
              (extChartAt I x x))
        + (∑ j' : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) j' *
                chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
                chartCoeff (I := I) x W k x)) *
      ((chartModelBasis E).repr w) j *
      chartGramMatrix (I := I) g x x i j) =
    (∑ i, ∑ j, ∑ j',
      ((chartModelBasis E).repr v) j' *
        partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i) (extChartAt I x x) *
        ((chartModelBasis E).repr w) j *
        chartGramMatrix (I := I) g x x i j)
    + (∑ i, ∑ j, ∑ j', ∑ k,
      ((chartModelBasis E).repr v) j' *
        chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
        chartCoeff (I := I) x W k x *
        ((chartModelBasis E).repr w) j *
        chartGramMatrix (I := I) g x x i j)
    from by
      rw [show
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((∑ j' : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr v) j' *
                partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i)
                  (extChartAt I x x))
            + (∑ j' : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr v) j' *
                    chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
                    chartCoeff (I := I) x W k x)) *
          ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i j) =
        ∑ i, ∑ j,
          ((∑ j', ((chartModelBasis E).repr v) j' *
              partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i) (extChartAt I x x) *
              ((chartModelBasis E).repr w) j *
              chartGramMatrix (I := I) g x x i j)
          + (∑ j', ∑ k,
              ((chartModelBasis E).repr v) j' *
                chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
                chartCoeff (I := I) x W k x *
                ((chartModelBasis E).repr w) j *
                chartGramMatrix (I := I) g x x i j))
        from Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
          rw [add_mul, add_mul]
          congr 1
          · rw [Finset.sum_mul, Finset.sum_mul]
          · rw [Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun j' _ => ?_)
            rw [Finset.sum_mul, Finset.sum_mul]))]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]]
  rw [show
    (∑ i, ∑ j,
      ((chartModelBasis E).repr v) i *
      ((∑ j' : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr w) j' *
            partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W j)
              (extChartAt I x x))
        + (∑ j' : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr w) j' *
                chartChristoffel (I := I) g x j' k j (extChartAt I x x) *
                chartCoeff (I := I) x W k x)) *
      chartGramMatrix (I := I) g x x i j) =
    (∑ i, ∑ j, ∑ j',
      ((chartModelBasis E).repr v) i *
        (((chartModelBasis E).repr w) j' *
          partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W j) (extChartAt I x x)) *
        chartGramMatrix (I := I) g x x i j)
    + (∑ i, ∑ j, ∑ j', ∑ k,
      ((chartModelBasis E).repr v) i *
        (((chartModelBasis E).repr w) j' *
          chartChristoffel (I := I) g x j' k j (extChartAt I x x) *
          chartCoeff (I := I) x W k x) *
        chartGramMatrix (I := I) g x x i j)
    from by
      rw [show
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr v) i *
          ((∑ j' : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr w) j' *
                partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W j)
                  (extChartAt I x x))
            + (∑ j' : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  ((chartModelBasis E).repr w) j' *
                    chartChristoffel (I := I) g x j' k j (extChartAt I x x) *
                    chartCoeff (I := I) x W k x)) *
          chartGramMatrix (I := I) g x x i j) =
        ∑ i, ∑ j,
          ((∑ j', ((chartModelBasis E).repr v) i *
              (((chartModelBasis E).repr w) j' *
                partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W j) (extChartAt I x x)) *
              chartGramMatrix (I := I) g x x i j)
          + (∑ j', ∑ k,
              ((chartModelBasis E).repr v) i *
                (((chartModelBasis E).repr w) j' *
                  chartChristoffel (I := I) g x j' k j (extChartAt I x x) *
                  chartCoeff (I := I) x W k x) *
                chartGramMatrix (I := I) g x x i j))
        from Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
          rw [mul_add, add_mul]
          congr 1
          · rw [Finset.mul_sum, Finset.sum_mul]
          · rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun j' _ => ?_)
            rw [Finset.mul_sum, Finset.sum_mul]))]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]]
  have hL1_eq_R1 :
      (∑ i, ∑ j, ∑ k,
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x k j *
          partialDeriv (E := E) i (chartCoeffOnE (I := I) x W k) (extChartAt I x x)) =
      (∑ i, ∑ j, ∑ j',
        ((chartModelBasis E).repr v) j' *
          partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i) (extChartAt I x x) *
          ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i j) := by
    rw [show
      (∑ i, ∑ j, ∑ j',
        ((chartModelBasis E).repr v) j' *
          partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i) (extChartAt I x x) *
          ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i j) =
      (∑ j', ∑ j, ∑ i,
        ((chartModelBasis E).repr v) j' *
          partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i) (extChartAt I x x) *
          ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i j) from by
      rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) j' *
              partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i) (extChartAt I x x) *
              ((chartModelBasis E).repr w) j *
              chartGramMatrix (I := I) g x x i j) =
          (∑ i, ∑ j', ∑ j,
            ((chartModelBasis E).repr v) j' *
              partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W i) (extChartAt I x x) *
              ((chartModelBasis E).repr w) j *
              chartGramMatrix (I := I) g x x i j) from
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun _ _ => ?_)
      rw [Finset.sum_comm]]
    refine Finset.sum_congr rfl (fun iL _ => Finset.sum_congr rfl
      (fun jL _ => Finset.sum_congr rfl (fun kL _ => by ring)))
  have hL3_eq_R3 :
      (∑ i, ∑ j, ∑ k,
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i k *
          partialDeriv (E := E) j (chartCoeffOnE (I := I) x W k) (extChartAt I x x)) =
      (∑ i, ∑ j, ∑ j',
        ((chartModelBasis E).repr v) i *
          (((chartModelBasis E).repr w) j' *
            partialDeriv (E := E) j' (chartCoeffOnE (I := I) x W j) (extChartAt I x x)) *
          chartGramMatrix (I := I) g x x i j) := by
    refine Finset.sum_congr rfl (fun iL _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun jL _ => Finset.sum_congr rfl (fun kL _ => by ring))
  have hL2_eq_R2 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x k j *
          chartChristoffel (I := I) g x i l k (extChartAt I x x) *
          chartCoeff (I := I) x W l x) =
      (∑ i, ∑ j, ∑ j', ∑ k,
        ((chartModelBasis E).repr v) j' *
          chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
          chartCoeff (I := I) x W k x *
          ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i j) := by
    rw [show
      (∑ i, ∑ j, ∑ j', ∑ k,
        ((chartModelBasis E).repr v) j' *
          chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
          chartCoeff (I := I) x W k x *
          ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i j) =
      (∑ j', ∑ j, ∑ i, ∑ k,
        ((chartModelBasis E).repr v) j' *
          chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
          chartCoeff (I := I) x W k x *
          ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i j) from by
      rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ j' : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) j' *
              chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
              chartCoeff (I := I) x W k x *
              ((chartModelBasis E).repr w) j *
              chartGramMatrix (I := I) g x x i j) =
          (∑ i, ∑ j', ∑ j, ∑ k,
            ((chartModelBasis E).repr v) j' *
              chartChristoffel (I := I) g x j' k i (extChartAt I x x) *
              chartCoeff (I := I) x W k x *
              ((chartModelBasis E).repr w) j *
              chartGramMatrix (I := I) g x x i j) from
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun _ _ => ?_)
      rw [Finset.sum_comm]]
    refine Finset.sum_congr rfl (fun iL _ => Finset.sum_congr rfl
      (fun jL _ => Finset.sum_congr rfl (fun kL _ => Finset.sum_congr rfl
        (fun lL _ => by ring))))
  have hL4_eq_R4 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ((chartModelBasis E).repr v) i * ((chartModelBasis E).repr w) j *
          chartGramMatrix (I := I) g x x i k *
          chartChristoffel (I := I) g x j l k (extChartAt I x x) *
          chartCoeff (I := I) x W l x) =
      (∑ i, ∑ j, ∑ j', ∑ k,
        ((chartModelBasis E).repr v) i *
          (((chartModelBasis E).repr w) j' *
            chartChristoffel (I := I) g x j' k j (extChartAt I x x) *
            chartCoeff (I := I) x W k x) *
          chartGramMatrix (I := I) g x x i j) := by
    refine Finset.sum_congr rfl (fun iL _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun jL _ => Finset.sum_congr rfl
      (fun kL _ => Finset.sum_congr rfl (fun lL _ => by ring)))
  rw [hL1_eq_R1, hL2_eq_R2, hL3_eq_R3, hL4_eq_R4]
  ring

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
