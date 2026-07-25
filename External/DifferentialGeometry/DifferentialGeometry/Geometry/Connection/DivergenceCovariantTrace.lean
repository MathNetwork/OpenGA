import DifferentialGeometry.Geometry.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.ChartInvariance


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y = chartInvGramOnE (I := I) g α j i y := by
  classical
  rw [chartInvGramOnE_def, chartInvGramOnE_def]
  set x : M := (extChartAt I α).symm y
  have hHerm : (chartGramMatrix (I := I) g α x).IsHermitian :=
    chartGramMatrix_isHermitian (I := I) g α x
  have hHermInv : (chartInvGramMatrix (I := I) g α x).IsHermitian := by
    unfold chartInvGramMatrix
    exact hHerm.inv
  have h_apply := hHermInv.apply i j
  rw [star_trivial] at h_apply
  exact h_apply.symm

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sum_chartChristoffel_diag_eq_half_trace
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i k k y) =
      (1 / 2 : ℝ) * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y := by
  classical
  have hexpand : (∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i k k y) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y +
           partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartChristoffel_def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← chartInvGramOnE_def]
  rw [hexpand]
  rw [Finset.mul_sum]
  rw [show (∑ k : Fin (Module.finrank ℝ E), (1 / 2 : ℝ) *
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k l y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]]
  rw [← sub_eq_zero]
  rw [← Finset.sum_sub_distrib]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
          ((∑ l : Fin (Module.finrank ℝ E),
              (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y +
                 partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
                 partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y))) -
            ∑ l : Fin (Module.finrank ℝ E),
              (1 / 2 : ℝ) * (chartInvGramOnE (I := I) g α k l y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y))) =
        (1 / 2 : ℝ) * (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (chartInvGramOnE (I := I) g α k l y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
            chartInvGramOnE (I := I) g α k l y *
              partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring]
  rw [mul_eq_zero]
  right
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (chartInvGramOnE (I := I) g α k l y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y -
            chartInvGramOnE (I := I) g α k l y *
              partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y) -
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k l y *
              partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y from by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_sub_distrib]]
  rw [sub_eq_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hGUsym : chartInvGramOnE (I := I) g α l k y =
      chartInvGramOnE (I := I) g α k l y := chartInvGramOnE_symm (I := I) g α l k y
  have hdGsym : partialDeriv (E := E) l (chartGramOnE (I := I) g α k i) y =
      partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y := by
    congr 1
    funext z
    exact chartGramOnE_symm (I := I) g α k i z
  rw [hGUsym, hdGsym]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartDensityOnE_eq_sum_chartChristoffel_diag
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y =
      (∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i k k y) * chartDensityOnE (I := I) g α y := by
  classical
  have htrace : Matrix.trace
        ((chartGramMatrix (I := I) g α ((extChartAt I α).symm y))⁻¹ *
          Matrix.of (fun a b => partialDeriv (E := E) i
            (chartGramOnE (I := I) g α a b) y)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartInvGramOnE_def, Matrix.of_apply]
    rfl
  rw [partialDeriv_chartDensityOnE (I := I) g α y i hy]
  rw [sum_chartChristoffel_diag_eq_half_trace (I := I) g α i y]
  rw [htrace]

private noncomputable def coordProjE (k : Fin (Module.finrank ℝ E)) :
    E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.proj k).comp ((chartModelBasis E).equivFun.toLinearMap)) :
      E →ₗ[ℝ] ℝ)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma coordProjE_apply (k : Fin (Module.finrank ℝ E)) (v : E) :
    coordProjE (E := E) k v = ((chartModelBasis E).repr v) k := by
  classical
  unfold coordProjE
  change ((LinearMap.proj k).comp ((chartModelBasis E).equivFun.toLinearMap)) v = _
  rw [LinearMap.comp_apply]
  simp [Module.Basis.equivFun]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma trivToE_chartBasisVecFiber
    (α : M) (m : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b) = (chartModelBasis E) m := by
  classical
  have hcoe : chartBasisVecFiber (I := I) α m b = trivFromE (I := I) α b ((chartModelBasis E) m) := by
    unfold chartBasisVecFiber trivFromE
    rfl
  rw [hcoe, trivToE_trivFromE (I := I) α hb]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma chartCoord_leviCivita_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (m k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartModelBasis E).repr
        (trivToE (I := I) α b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            (chartBasisVecFiber (I := I) α m b))) k =
      partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) (extChartAt I α b) +
        ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α m j k (extChartAt I α b) *
            chartCoeffOnE (I := I) α Z j (extChartAt I α b) := by
  classical
  set y₀ : E := extChartAt I α b with hy₀_def
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hZ_mdiff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) y (Z.toFun y)) b :=
    (Z.contMDiff b).mdifferentiableAt (by simp)
  rw [LeviCivita_chart_apply (I := I) g α hb hZ_mdiff
    (chartBasisVecFiber (I := I) α m b)]
  rw [chartLeviCivita_apply (I := I) g α Z.toFun hb
    (chartBasisVecFiber (I := I) α m b)]
  rw [trivToE_trivFromE (I := I) α hb_base]
  rw [trivToE_chartBasisVecFiber (I := I) α m hb_base]
  rw [map_add]
  rw [Finsupp.add_apply]
  congr 1
  · set F : E → E :=
      chartE_section_repr (I := I) α Z.toFun ∘ (extChartAt I α).symm with hF_def
    have hb_src : b ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
    have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
    have hF_diff : DifferentiableAt ℝ F y₀ := by
      rw [hF_def, hy₀_def]
      exact (mdifferentiableAt_section_iff_chartE_fderiv I α Z.toFun
        hb_src hb_base hb_int).mp hZ_mdiff
    rw [show ((chartModelBasis E).repr (fderiv ℝ F y₀ ((chartModelBasis E) m))) k =
          coordProjE (E := E) k (fderiv ℝ F y₀ ((chartModelBasis E) m)) from by
        rw [coordProjE_apply]]
    rw [← ContinuousLinearMap.comp_apply]
    rw [show (coordProjE (E := E) k).comp (fderiv ℝ F y₀) =
          fderiv ℝ ((coordProjE (E := E) k : E → ℝ) ∘ F) y₀ from by
        rw [fderiv_comp y₀ (coordProjE (E := E) k).differentiableAt hF_diff,
            ContinuousLinearMap.fderiv]]
    change (fderiv ℝ ((coordProjE (E := E) k : E → ℝ) ∘ F) y₀) ((chartModelBasis E) m) =
        partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) y₀
    have htgt_nhd : (extChartAt I α).target ∈ 𝓝 y₀ :=
      (isOpen_extChartAt_target (I := I) α).mem_nhds (interior_subset hb_int)
    have hev : ((coordProjE (E := E) k : E → ℝ) ∘ F) =ᶠ[𝓝 y₀]
        chartCoeffOnE (I := I) α Z k := by
      filter_upwards [htgt_nhd] with z hz
      rw [hF_def]
      simp only [Function.comp_apply, coordProjE_apply]
      rw [chartCoeffOnE, chartCoeff_def]
      have hz_base : (extChartAt I α).symm z ∈
          (trivializationAt E (TangentSpace I) α).baseSet := by
        have hsource : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
          (extChartAt I α).map_target hz
        rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hsource
      rw [chartE_section_repr_eq_trivialization_snd (I := I) α Z.toFun hz_base]
      rfl
    rw [hev.fderiv_eq]
    rfl
  · rw [christoffelCorrection_apply (I := I) g α b
      (chartE_section_repr (I := I) α Z.toFun b)
      (chartBasisVecFiber (I := I) α m b)]
    rw [show ((chartModelBasis E).repr
            (∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                (((chartModelBasis E).repr
                    (trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b))) a *
                  ((chartModelBasis E).repr
                    (chartE_section_repr (I := I) α Z.toFun b)) c *
                  chartChristoffel (I := I) g α a c d (extChartAt I α b)) •
                  (chartModelBasis E) d)) k =
          coordProjE (E := E) k
            (∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                (((chartModelBasis E).repr
                    (trivToE (I := I) α b (chartBasisVecFiber (I := I) α m b))) a *
                  ((chartModelBasis E).repr
                    (chartE_section_repr (I := I) α Z.toFun b)) c *
                  chartChristoffel (I := I) g α a c d (extChartAt I α b)) •
                  (chartModelBasis E) d) from by rw [coordProjE_apply]]
    rw [map_sum]
    rw [trivToE_chartBasisVecFiber (I := I) α m hb_base]
    simp only [map_sum, map_smul, smul_eq_mul, coordProjE_apply,
      Module.Basis.repr_self_apply]
    have hZcoeff : ∀ c : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) α Z c y₀ =
          ((chartModelBasis E).repr
            (chartE_section_repr (I := I) α Z.toFun b)) c := by
      intro c
      rw [chartE_section_repr_eq_trivialization_snd (I := I) α Z.toFun hb_base]
      rw [chartCoeffOnE, chartCoeff_def, hy₀_def]
      rw [(extChartAt I α).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb)]
      rfl
    rw [Finset.sum_eq_single m]
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl, if_pos rfl, hZcoeff c]
        ring
      · intro d _ hdk
        rw [if_neg hdk]
        ring
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · intro a _ ham
      rw [if_neg (Ne.symm ham)]
      simp
    · intro hm
      exact absurd (Finset.mem_univ m) hm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tangent_eq_coordSum
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : TangentSpace I b) :
    w = ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (trivToE (I := I) α b w)) k •
        chartBasisVecFiber (I := I) α k b := by
  classical
  have hsum : trivToE (I := I) α b w =
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (trivToE (I := I) α b w)) k • (chartModelBasis E) k :=
    ((chartModelBasis E).sum_repr (trivToE (I := I) α b w)).symm
  calc w = trivFromE (I := I) α b (trivToE (I := I) α b w) :=
            (trivFromE_trivToE (I := I) α hb w).symm
    _ = trivFromE (I := I) α b
          (∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (trivToE (I := I) α b w)) k •
              (chartModelBasis E) k) := by rw [← hsum]
    _ = ∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (trivToE (I := I) α b w)) k •
            chartBasisVecFiber (I := I) α k b := by
          rw [map_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [map_smul]
          rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma inner_leviCivita_chartBasis_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (m n : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    g.inner b
        ((LeviCivita (I := I) g).toFun Z.toFun b (chartBasisVecFiber (I := I) α m b))
        (chartBasisVecFiber (I := I) α n b) =
      ∑ k : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) (extChartAt I α b) +
          ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α m j k (extChartAt I α b) *
              chartCoeffOnE (I := I) α Z j (extChartAt I α b)) *
          chartGramMatrix (I := I) g α b k n := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  rw [tangent_eq_coordSum (I := I) α hb_base
    ((LeviCivita (I := I) g).toFun Z.toFun b (chartBasisVecFiber (I := I) α m b))]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [chartCoord_leviCivita_chartBasis (I := I) g α Z m k hb]
  rw [chartGramMatrix_apply]

omit [I.Boundaryless] in
lemma frameTrace_eq_metricTrace
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (∑ i : Fin (Module.finrank ℝ E),
        g.inner b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (chartBasisVecFiber (I := I) α m b))
            (chartBasisVecFiber (I := I) α n b) := by
  classical
  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b with hC_def
  set L := (LeviCivita (I := I) g).toFun Z.toFun b with hL_def
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      g.inner b (L ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) =
        ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          C i m * C i n *
            g.inner b (L (chartBasisVecFiber (I := I) α m b))
              (chartBasisVecFiber (I := I) α n b) := by
    intro i
    have hFeq : (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
        ∑ m : Fin (Module.finrank ℝ E), C i m • chartBasisVecFiber (I := I) α m b := by
      rw [hC_def]
      exact chartFrameNormGlobalSmooth_eq_coordMatrix_sum (I := I) (M := M) g α i hb
    rw [hFeq]
    have hLslot : L (∑ m : Fin (Module.finrank ℝ E),
            C i m • chartBasisVecFiber (I := I) α m b) =
        ∑ m : Fin (Module.finrank ℝ E),
          C i m • L (chartBasisVecFiber (I := I) α m b) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul]
    rw [hLslot]
    have hslot1 : (g.inner b) (∑ m : Fin (Module.finrank ℝ E),
            C i m • L (chartBasisVecFiber (I := I) α m b)) =
        ∑ m : Fin (Module.finrank ℝ E),
          C i m • (g.inner b) (L (chartBasisVecFiber (I := I) α m b)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul]
    rw [hslot1, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [map_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_mul]
  rw [show (∑ i : Fin (Module.finrank ℝ E), C i m * C i n) =
        chartInvGramMatrix (I := I) g α b m n from by
      rw [hC_def]
      exact chartFrameNormGlobalSmoothCoordMatrix_orthonormality
        (I := I) (M := M) g α hb_pou hb m n]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma metricTrace_eq_coord_covariant_divergence
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (chartBasisVecFiber (I := I) α m b))
            (chartBasisVecFiber (I := I) α n b)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z m) (extChartAt I α b) +
          ∑ j : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α m j m (extChartAt I α b) *
              chartCoeffOnE (I := I) α Z j (extChartAt I α b)) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun m k =>
      partialDeriv (E := E) m (chartCoeffOnE (I := I) α Z k) (extChartAt I α b) +
        ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α m j k (extChartAt I α b) *
            chartCoeffOnE (I := I) α Z j (extChartAt I α b) with hA_def
  have hstep1 : (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (chartBasisVecFiber (I := I) α m b))
            (chartBasisVecFiber (I := I) α n b)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          ∑ k : Fin (Module.finrank ℝ E),
            A m k * chartGramMatrix (I := I) g α b k n := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [inner_leviCivita_chartBasis_eq (I := I) g α Z m n hb]
  rw [hstep1]
  rw [show (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α b m n *
            ∑ k : Fin (Module.finrank ℝ E),
              A m k * chartGramMatrix (I := I) g α b k n) =
        ∑ m : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          A m k * (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b m n *
              chartGramMatrix (I := I) g α b k n) from by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [show (∑ n : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α b m n *
                ∑ k : Fin (Module.finrank ℝ E),
                  A m k * chartGramMatrix (I := I) g α b k n) =
            ∑ n : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              A m k * (chartInvGramMatrix (I := I) g α b m n *
                chartGramMatrix (I := I) g α b k n) from by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]]
  have hδ : ∀ m k : Fin (Module.finrank ℝ E),
      (∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α b m n *
          chartGramMatrix (I := I) g α b k n) =
        if m = k then (1 : ℝ) else 0 := by
    intro m k
    have hGsym : ∀ n : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g α b k n = chartGramMatrix (I := I) g α b n k := by
      intro n
      rw [chartGramMatrix_apply, chartGramMatrix_apply, g.symm]
    rw [show (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b m n *
              chartGramMatrix (I := I) g α b k n) =
          (chartInvGramMatrix (I := I) g α b *
            chartGramMatrix (I := I) g α b) m k from by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hGsym n]]
    rw [chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hb_base]
    rw [Matrix.one_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show (∑ k : Fin (Module.finrank ℝ E),
          A m k * (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g α b m n *
              chartGramMatrix (I := I) g α b k n)) =
        ∑ k : Fin (Module.finrank ℝ E), A m k * (if m = k then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hδ m k]]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl, mul_one, hA_def]
  · intro k _ hkm
    rw [if_neg (Ne.symm hkm), mul_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma localDivergence_eq_coord_covariant_divergence
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    localDivergence (I := I) g α Z b =
      (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) (extChartAt I α b)) +
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) α Z i (extChartAt I α b) *
            (∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α i k k (extChartAt I α b)) := by
  classical
  set y₀ : E := extChartAt I α b with hy₀_def
  have hy₀_int : y₀ ∈ interior (extChartAt I α).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hy₀_target : y₀ ∈ (extChartAt I α).target := interior_subset hy₀_int
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy₀_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy₀_int
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hD_ne : chartDensity (I := I) g α b ≠ 0 :=
    ne_of_gt (chartDensity_pos (I := I) g α hb_base)
  have hcoeff_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartCoeffOnE (I := I) α Z i) y₀ := by
    intro i
    have hcd : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) α Z i)
        (extChartAt I α).target := chartCoeffOnE_contDiffOn (I := I) α Z i
    have hcd_int : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) α Z i)
        (interior (extChartAt I α).target) := hcd.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    chartDensityOnE_differentiableAt_interior (I := I) g α hy₀_int
  have hD_eq : chartDensity (I := I) g α b = chartDensityOnE (I := I) g α y₀ := by
    rw [chartDensityOnE]
    rw [hy₀_def]
    rw [(extChartAt I α).left_inv (by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb)]
  rw [localDivergence_def]
  rw [hD_eq]
  have hnum : (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y => chartCoeffOnE (I := I) α Z i y * chartDensityOnE (I := I) g α y) y₀) =
      ∑ i : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) y₀ *
            chartDensityOnE (I := I) g α y₀ +
          chartCoeffOnE (I := I) α Z i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold partialDeriv
    rw [fderiv_fun_mul (hcoeff_diff i) hdens_diff]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hnum]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) y₀ *
              chartDensityOnE (I := I) g α y₀ +
            chartCoeffOnE (I := I) α Z i y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((partialDeriv (E := E) i (chartCoeffOnE (I := I) α Z i) y₀ +
              chartCoeffOnE (I := I) α Z i y₀ *
                (∑ k : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g α i k k y₀)) *
            chartDensityOnE (I := I) g α y₀) from ?_]
  · have hDOnE_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := by
      rw [← hD_eq]; exact hD_ne
    rw [← Finset.sum_mul]
    rw [mul_div_assoc, div_self hDOnE_ne, mul_one]
    rw [Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialDeriv_chartDensityOnE_eq_sum_chartChristoffel_diag (I := I) g α i hy₀_int]
    ring

theorem voss_weyl_divergence_eq_leviCivita_frameTrace
    (g : SmoothRiemannianMetric I M) (α : M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {b : M}
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    divergence_g (I := I) g Z b =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))
          ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) := by
  classical
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  rw [voss_weyl_divergence_formula (I := I) g α Z hb_src]
  rw [localDivergence_eq_coord_covariant_divergence (I := I) g α Z hb]
  rw [frameTrace_eq_metricTrace (I := I) g α Z hb_pou hb]
  rw [metricTrace_eq_coord_covariant_divergence (I := I) g α Z hb]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) α Z i (extChartAt I α b) *
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g α i k k (extChartAt I α b)) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i k k (extChartAt I α b) *
            chartCoeffOnE (I := I) α Z i (extChartAt I α b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g α k i i]

end Connection
end Integral
end DifferentialGeometry

end
