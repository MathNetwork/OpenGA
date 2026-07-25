import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.ConjugatingFlowProperties
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciContinuityInMetricTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
set_option linter.style.longLine false




















namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]




omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricCLMSection_jointContMDiffOn_of_chartGram_Ioo
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2)))
      (Set.Ioo a b ×ˢ Set.univ) := by

  set gsh : ℝ → SmoothRiemannianMetric I M := fun s => g (s + a) with hgsh

  have haddC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 + a, p.2)) :=
    (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd

  have hsubC : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (p.1 - a, p.2)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd

  have hgram_sh : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (gsh p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1 + a, p.2))
        (Set.Ioo (0 : ℝ) (b - a) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      rintro ⟨s, m⟩ ⟨hs, hm⟩
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hm⟩
    exact (hgram x₀ i j).comp haddC.contMDiffOn hmaps

  have hsh := metricCLMSection_jointContMDiffOn_of_chartGram (I := I) gsh (b - a) hgram_sh

  have hmaps2 : Set.MapsTo (fun p : ℝ × M => (p.1 - a, p.2))
      (Set.Ioo a b ×ˢ (Set.univ : Set M))
      (Set.Ioo (0 : ℝ) (b - a) ×ˢ (Set.univ : Set M)) := by
    rintro ⟨t, m⟩ ⟨ht, _⟩
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, Set.mem_univ _⟩
  have hcomp := hsh.comp hsubC.contMDiffOn hmaps2

  refine hcomp.congr ?_
  rintro ⟨t, m⟩ _
  simp only [Function.comp_apply, hgsh, sub_add_cancel]













omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contOn_partial_iteratedFDeriv_of_contDiffOn
    {F : ℝ × E → ℝ} {U : Set (ℝ × E)} (hUopen : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (k : ℕ) :
    ContinuousOn
      (fun q : ℝ × E => iteratedFDeriv ℝ k (fun z : E => F (q.1, z)) q.2) U := by
  classical
  have hUniq : UniqueDiffOn ℝ U := hUopen.uniqueDiffOn

  have hfull : ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k F q) U := by
    refine (hF.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast le_top)
      hUniq).congr ?_
    intro q hq
    exact (iteratedFDerivWithin_of_isOpen k hUopen hq).symm

  have hslice : ∀ q ∈ U,
      iteratedFDeriv ℝ k (fun z : E => F (q.1, z)) q.2
        = (iteratedFDeriv ℝ k F q).compContinuousLinearMap
            (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E) := by
    intro q hq
    obtain ⟨t, y⟩ := q
    set inrE : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E with hinrE
    set s' : Set (ℝ × E) := (fun p : ℝ × E => p + ((t, 0) : ℝ × E)) ⁻¹' U with hs'def
    have hs'_open : IsOpen s' := hUopen.preimage (by fun_prop)
    have hsl_open : IsOpen ((fun z : E => ((t, z) : ℝ × E)) ⁻¹' U) :=
      hUopen.preimage (by fun_prop)
    have hy_sl : y ∈ (fun z : E => ((t, z) : ℝ × E)) ⁻¹' U := hq
    have hpre : inrE ⁻¹' s' = (fun z : E => ((t, z) : ℝ × E)) ⁻¹' U := by
      ext z
      simp only [hs'def, hinrE, Set.mem_preimage, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]
    have hfun : (fun z : E => F (t, z)) = (fun p : ℝ × E => F (p + (t, 0))) ∘ inrE := by
      ext z
      simp only [hinrE, Function.comp_apply, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]
    have hGcd : ContDiffOn ℝ ∞ (fun p : ℝ × E => F (p + (t, 0))) s' :=
      hF.comp (by fun_prop) (fun p hp => hp)
    have hxs' : inrE y ∈ s' := by
      simp only [hs'def, hinrE, Set.mem_preimage, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]; exact hq
    have hcr := ContinuousLinearMap.iteratedFDerivWithin_comp_right inrE hGcd
      hs'_open.uniqueDiffOn (by rw [hpre]; exact hsl_open.uniqueDiffOn) hxs'
      (i := k) (by exact_mod_cast le_top)
    rw [hpre] at hcr
    have htr : iteratedFDerivWithin ℝ k (fun p : ℝ × E => F (p + (t, 0))) s' (inrE y)
        = iteratedFDerivWithin ℝ k F U (t, y) := by
      have hpt : inrE y = ((0, y) : ℝ × E) := by
        simp only [hinrE, ContinuousLinearMap.inr_apply]
      rw [hpt, iteratedFDerivWithin_comp_add_right k ((t, 0) : ℝ × E) ((0, y) : ℝ × E)]
      congr 1
      · ext p
        simp only [hs'def, Set.mem_vadd_set, Set.mem_preimage]
        constructor
        · rintro ⟨r, hr, rfl⟩
          rw [vadd_eq_add, add_comm (t, 0) r]; exact hr
        · intro hp
          refine ⟨p - (t, 0), ?_, ?_⟩
          · simpa using hp
          · rw [vadd_eq_add]; abel
      · simp
    rw [hfun, ← iteratedFDerivWithin_of_isOpen k hsl_open hy_sl, hcr, htr,
      iteratedFDerivWithin_of_isOpen k hUopen hq]

  have hcomp : ContinuousOn
      (fun q : ℝ × E => (iteratedFDeriv ℝ k F q).compContinuousLinearMap
        (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) U := by
    refine ((ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)).continuous.comp_continuousOn
      hfull).congr ?_
    intro q _
    simp [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  exact hcomp.congr (fun q hq => hslice q hq)









omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_jointContDiffOn {G : ℝ × E → ℝ} {U : Set (ℝ × E)}
    (hUopen : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => partialDeriv (E := E) m (fun z : E => G (q.1, z)) q.2) U := by
  have hUniq : UniqueDiffOn ℝ U := hUopen.uniqueDiffOn

  have hfd : ContDiffOn ℝ ∞ (fun q : ℝ × E => fderiv ℝ G q) U :=
    (hG.fderivWithin hUniq (by simp)).congr
      (fun q hq => (fderivWithin_of_isOpen hUopen hq).symm)

  refine (hfd.clm_apply (contDiffOn_const
    (c := ((0, (chartModelBasis E) m) : ℝ × E)))).congr ?_
  intro q hq

  have hdiffAt : DifferentiableAt ℝ G q :=
    (hG.differentiableOn (by simp)).differentiableAt (hUopen.mem_nhds hq)
  have hι : HasFDerivAt (fun z : E => (q.1, z)) (ContinuousLinearMap.inr ℝ ℝ E) q.2 := by
    simpa using (hasFDerivAt_const (q.1) q.2).prodMk (hasFDerivAt_id q.2)
  have hslice : HasFDerivAt (fun z : E => G (q.1, z))
      ((fderiv ℝ G q).comp (ContinuousLinearMap.inr ℝ ℝ E)) q.2 :=
    hdiffAt.hasFDerivAt.comp q.2 hι
  change fderiv ℝ (fun z : E => G (q.1, z)) q.2 ((chartModelBasis E) m)
      = (fderiv ℝ G q) ((0, (chartModelBasis E) m) : ℝ × E)
  rw [hslice.fderiv]
  simp [ContinuousLinearMap.inr_apply]



set_option synthInstance.maxHeartbeats 200000 in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma spatialJet_set
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ → E → F} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V)) (k : ℕ) (hk : k ≤ 2) :
    ContDiffOn ℝ ∞
      (Function.uncurry (fun t y => iteratedFDeriv ℝ k (G t) y)) (J ×ˢ V) := by
  interval_cases k
  · refine ((continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hG).congr ?_
    rintro ⟨t, y⟩ _
    rfl
  · have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn hJ hV hG
    refine ((continuousMultilinearCurryFin1 ℝ E F).symm.contDiff.comp_contDiffOn hfd).congr ?_
    rintro ⟨t, y⟩ _
    ext v
    simp only [Function.comp_apply, Function.uncurry_apply_pair,
      continuousMultilinearCurryFin1_symm_apply, iteratedFDeriv_one_apply]
  · have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn hJ hV hG
    have hfd2 := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t y => fderiv ℝ (G t) y) hJ hV hfd
    have hcurried :=
      (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] F)).symm.contDiff.comp_contDiffOn hfd2
    refine ((continuousMultilinearCurryRightEquiv' ℝ 1 E F).symm.contDiff.comp_contDiffOn
      hcurried).congr ?_
    rintro ⟨t, y⟩ _
    ext v
    simp only [Function.comp_apply, Function.uncurry_apply_pair, iteratedFDeriv_two_apply,
      continuousMultilinearCurryRightEquiv_symm_apply',
      continuousMultilinearCurryFin1_symm_apply]
    rfl



omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_set {G : ℝ × E → ℝ} {J : Set ℝ} {V : Set E}
    (hJ : UniqueDiffOn ℝ J) (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ G (J ×ˢ V)) (m : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => partialDeriv (E := E) m (fun z : E => G (q.1, z)) q.2)
      (J ×ˢ V) := by
  have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => G (t, y)) hJ hV hG
  refine (hfd.clm_apply (contDiffOn_const (c := (chartModelBasis E) m))).congr ?_
  intro q _
  rfl



private lemma matrixDet_contDiffOn {n : ℕ} {s : Set ℝ}
    (N : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiffOn ℝ ∞ (fun t : ℝ => N t a b) s) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (N t).det) s := by
  classical
  simp_rw [Matrix.det_apply]
  refine ContDiffOn.sum (fun σ _ => ?_)
  exact ContDiffOn.const_smul (Equiv.Perm.sign σ) (contDiffOn_prod (fun i _ => hN (σ i) i))



private lemma matrixAdjugate_contDiffOn {n : ℕ} {s : Set ℝ}
    (N : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, ContDiffOn ℝ ∞ (fun t : ℝ => N t a b) s) (k l : Fin n) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (N t).adjugate k l) s := by
  classical
  simp_rw [Matrix.adjugate_apply]
  refine matrixDet_contDiffOn _ (fun a b => ?_)
  rcases eq_or_ne a l with h | h
  · subst h
    simp only [Matrix.updateRow_self]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_ne h]
    exact hN a b





omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartInvGramOnE_contDiff_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (y : E) (s : Set ℝ)
    (h_entry : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s)
    (hx : ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => chartInvGramOnE (I := I) (g_DT t) α i j y) s := by
  classical
  set Gmat : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun t => Matrix.of fun a b => chartGramOnE (I := I) (g_DT t) α a b y with hGmat_def
  have hGmat_eq : ∀ t, Gmat t = chartGramMatrix (I := I) (g_DT t) α ((extChartAt I α).symm y) := by
    intro t; ext a b; rw [hGmat_def]; simp only [Matrix.of_apply]; rw [chartGramOnE_def]
  have hentryG : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => Gmat t a b) s := by
    intro a b; simpa only [hGmat_def, Matrix.of_apply] using h_entry a b
  have hcongr : ∀ t ∈ s,
      chartInvGramOnE (I := I) (g_DT t) α i j y = ((Gmat t).det)⁻¹ * (Gmat t).adjugate i j := by
    intro t _
    rw [chartInvGramOnE_def]
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (g_DT t) α
            ((extChartAt I α).symm y)).det •
          (chartGramMatrix (I := I) (g_DT t) α ((extChartAt I α).symm y)).adjugate) i j =
        ((Gmat t).det)⁻¹ * (Gmat t).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul, hGmat_eq t]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContDiffOn.congr ?_ hcongr
  refine ContDiffOn.mul ?_ (matrixAdjugate_contDiffOn Gmat hentryG i j)
  refine (matrixDet_contDiffOn Gmat hentryG).inv ?_
  intro t _
  have hpos := chartGramMatrix_det_pos (I := I) (g_DT t) α hx
  have heq : (Gmat t).det
      = (chartGramMatrix (I := I) (g_DT t) α ((extChartAt I α).symm y)).det := by rw [hGmat_eq t]
  rw [heq]; exact ne_of_gt hpos


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gramBracket_contDiff
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (i j l : Fin (Module.finrank ℝ E))
    (y : E) (s : Set ℝ)
    (hp1 : ∀ m a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun t : ℝ => partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContDiffOn ℝ ∞ (fun t : ℝ => gramBracket (I := I) (g_DT t) α i j l y) s := by
  have heq : (fun t : ℝ => gramBracket (I := I) (g_DT t) α i j l y)
      = fun t : ℝ =>
          partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT t) α l j) y +
            partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT t) α l i) y -
            partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j) y := by
    funext t; rfl
  rw [heq]
  exact ((hp1 i l j).add (hp1 j l i)).sub (hp1 l i j)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gramBracketDeriv_contDiff
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (m i j l : Fin (Module.finrank ℝ E))
    (y : E) (s : Set ℝ)
    (hp2 : ∀ m' l' a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ =>
        partialDeriv (E := E) m' (partialDeriv (E := E) l' (chartGramOnE (I := I) (g_DT t) α a b)) y)
        s) :
    ContDiffOn ℝ ∞ (fun t : ℝ => gramBracketDeriv (I := I) (g_DT t) α m i j l y) s := by
  have heq : (fun t : ℝ => gramBracketDeriv (I := I) (g_DT t) α m i j l y)
      = fun t : ℝ =>
          partialDeriv (E := E) m
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g_DT t) α l j)) y +
            partialDeriv (E := E) m
              (partialDeriv (E := E) j (chartGramOnE (I := I) (g_DT t) α l i)) y -
            partialDeriv (E := E) m
              (partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α i j)) y := by
    funext t; rfl
  rw [heq]
  exact ((hp2 m i l j).add (hp2 m j l i)).sub (hp2 m l i j)



omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartInvGramOnE_contDiff
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (m k l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hp0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s)
    (hp1 : ∀ m' a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun t : ℝ => partialDeriv (E := E) m' (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContDiffOn ℝ ∞
      (fun t : ℝ => partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y) s := by
  have heq : ∀ t ∈ s,
      partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y =
        -∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) (g_DT t) α k a y *
              chartInvGramOnE (I := I) (g_DT t) α b l y *
              partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y := by
    intro t _
    exact partialDeriv_chartInvGramOnE_eq (I := I) (g_DT t) α y m k l hy
  refine ContDiffOn.congr ?_ heq
  refine ContDiffOn.neg ?_
  refine ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => ?_))
  exact ((chartInvGramOnE_contDiff_in_metric_at (I := I) g_DT α y s hp0 hx k a).mul
    (chartInvGramOnE_contDiff_in_metric_at (I := I) g_DT α y s hp0 hx b l)).mul (hp1 m a b)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartChristoffel_contDiff_in_metric_at
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (a b k : Fin (Module.finrank ℝ E))
    (y : E) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hp0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s)
    (hp1 : ∀ m a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun t : ℝ => partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y) s) :
    ContDiffOn ℝ ∞ (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b k y) s := by
  have hrewrite : (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b k y) =
      fun t : ℝ =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) (g_DT t) α ((extChartAt I α).symm y) k l *
            (partialDeriv (E := E) a (chartGramOnE (I := I) (g_DT t) α l b) y +
             partialDeriv (E := E) b (chartGramOnE (I := I) (g_DT t) α l a) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) (g_DT t) α a b) y) := by
    funext t; rw [chartChristoffel_def]
  rw [hrewrite]
  refine ContDiffOn.mul contDiffOn_const ?_
  refine ContDiffOn.sum (fun l _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · have hcongr : (fun t : ℝ => chartInvGramMatrix (I := I) (g_DT t) α
          ((extChartAt I α).symm y) k l)
        = fun t : ℝ => chartInvGramOnE (I := I) (g_DT t) α k l y := by funext t; rfl
    rw [hcongr]
    exact chartInvGramOnE_contDiff_in_metric_at (I := I) g_DT α y s hp0 hx k l
  · exact ((hp1 a l b).add (hp1 b l a)).sub (hp1 l a b)


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartChristoffel_contDiff
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (m i j k : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hp0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s)
    (hp1 : ∀ m a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun t : ℝ => partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (hp2 : ∀ m' l' a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ =>
        partialDeriv (E := E) m' (partialDeriv (E := E) l' (chartGramOnE (I := I) (g_DT t) α a b)) y)
        s) :
    ContDiffOn ℝ ∞
      (fun t : ℝ => partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT t) α i j k) y) s := by
  have heq : ∀ t ∈ s,
      partialDeriv (E := E) m (chartChristoffel (I := I) (g_DT t) α i j k) y =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) (g_DT t) α k l) y *
              gramBracket (I := I) (g_DT t) α i j l y +
            chartInvGramOnE (I := I) (g_DT t) α k l y *
              gramBracketDeriv (I := I) (g_DT t) α m i j l y) := by
    intro t _
    exact partialDeriv_chartChristoffel_eq (I := I) (g_DT t) α m i j k hy
  refine ContDiffOn.congr ?_ heq
  refine ContDiffOn.mul contDiffOn_const ?_
  refine ContDiffOn.sum (fun l _ => ?_)
  refine ContDiffOn.add (ContDiffOn.mul ?_ ?_) (ContDiffOn.mul ?_ ?_)
  · exact partialDeriv_chartInvGramOnE_contDiff (I := I) g_DT α m k l hy s hx hp0 hp1
  · exact gramBracket_contDiff (I := I) g_DT α i j l y s hp1
  · exact chartInvGramOnE_contDiff_in_metric_at (I := I) g_DT α y s hp0 hx k l
  · exact gramBracketDeriv_contDiff (I := I) g_DT α m i j l y s hp2


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRiemannTensor_contDiff
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (i j k r : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hp0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s)
    (hp1 : ∀ m a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun t : ℝ => partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (hp2 : ∀ m' l' a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ =>
        partialDeriv (E := E) m' (partialDeriv (E := E) l' (chartGramOnE (I := I) (g_DT t) α a b)) y)
        s) :
    ContDiffOn ℝ ∞ (fun t : ℝ => chartRiemannTensor (I := I) (g_DT t) α i j k r y) s := by
  have heq : (fun t : ℝ => chartRiemannTensor (I := I) (g_DT t) α i j k r y)
      = fun t : ℝ =>
          partialDeriv (E := E) j (chartChristoffel (I := I) (g_DT t) α i k r) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) (g_DT t) α i j r) y +
            (∑ n : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (g_DT t) α j n r y *
                  chartChristoffel (I := I) (g_DT t) α i k n y -
                chartChristoffel (I := I) (g_DT t) α k n r y *
                  chartChristoffel (I := I) (g_DT t) α i j n y)) := by
    funext t; rw [chartRiemannTensor_def]
  rw [heq]
  have hΓ : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => chartChristoffel (I := I) (g_DT t) α a b c y) s :=
    fun a b c => chartChristoffel_contDiff_in_metric_at (I := I) g_DT α a b c y s hx hp0 hp1
  refine ContDiffOn.add (ContDiffOn.sub ?_ ?_) ?_
  · exact partialDeriv_chartChristoffel_contDiff (I := I) g_DT α j i k r hy s hx hp0 hp1 hp2
  · exact partialDeriv_chartChristoffel_contDiff (I := I) g_DT α k i j r hy s hx hp0 hp1 hp2
  · refine ContDiffOn.sum (fun n _ => ?_)
    exact ((hΓ j n r).mul (hΓ i k n)).sub ((hΓ k n r).mul (hΓ i j n))


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartRicciTensor_contDiff
    (g_DT : ℝ → SmoothRiemannianMetric I M) (α : M) (i k : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) (s : Set ℝ)
    (hx : ((extChartAt I α).symm y) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hp0 : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ => chartGramOnE (I := I) (g_DT t) α a b y) s)
    (hp1 : ∀ m a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun t : ℝ => partialDeriv (E := E) m (chartGramOnE (I := I) (g_DT t) α a b) y) s)
    (hp2 : ∀ m' l' a b : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t : ℝ =>
        partialDeriv (E := E) m' (partialDeriv (E := E) l' (chartGramOnE (I := I) (g_DT t) α a b)) y)
        s) :
    ContDiffOn ℝ ∞ (fun t : ℝ => chartRicciTensor (I := I) (g_DT t) α i k y) s := by
  have heq : (fun t : ℝ => chartRicciTensor (I := I) (g_DT t) α i k y)
      = fun t : ℝ => ∑ j : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) (g_DT t) α i j k j y := by
    funext t; rw [chartRicciTensor_def]
  rw [heq]
  refine ContDiffOn.sum (fun j _ => ?_)
  exact chartRiemannTensor_contDiff (I := I) g_DT α i j k j hy s hx hp0 hp1 hp2



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTimeSlice_contDiffOn {α : M} {J : Set ℝ} {y : E}
    (hy : y ∈ interior (extChartAt I α).target) {f : ℝ × E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ interior (extChartAt I α).target)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => f (t, y)) J :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hy⟩)



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartGramOnE_set
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (α : M)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g p.1) α i j p.2)
      (J ×ˢ interior ((extChartAt I α).target)) := by
  classical




  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (extChartAt I α).target :=
    contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hσ1 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × E => p.1) (J ×ˢ interior ((extChartAt I α).target)) :=
    (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun p : ℝ × E => p.2)
      (J ×ˢ interior ((extChartAt I α).target)) :=
    (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
  have hmaps2 : Set.MapsTo (fun p : ℝ × E => p.2)
      (J ×ˢ interior ((extChartAt I α).target)) (extChartAt I α).target :=
    fun p hp => interior_subset hp.2
  have hσ2 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
      (fun p : ℝ × E => (extChartAt I α).symm p.2) (J ×ˢ interior ((extChartAt I α).target)) :=
    hsymm.comp hsnd hmaps2
  have hσ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2)) (J ×ˢ interior ((extChartAt I α).target)) :=
    hσ1.prodMk hσ2
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun p : ℝ × E =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g p.1) α i j p.2) (J ×ˢ interior ((extChartAt I α).target)) := by
    refine ((hsmooth α i j).comp hσ (fun p hp => ⟨hp.1, hsubset (interior_subset hp.2)⟩)).congr ?_
    intro p _
    rfl
  exact hcomp.contDiffOn


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartGramOnE_jointContDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ) (α : M)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        Integral.DivergenceTheorem.chartGramOnE (I := I) (g p.1) α i j p.2)
      (Set.Ioo a b ×ˢ interior ((extChartAt I α).target)) :=
  chartGramOnE_set (I := I) g (Set.Ioo a b) α hsmooth i j



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartGram_jet_set
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J) (α : M)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {Sp : Set (ℝ × M)}
    (hSp : Sp ⊆ J ×ˢ chartLeviCivitaGoodSet (I := I) α)
    (k : ℕ) (hk : k ≤ 2) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × M =>
        iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g q.1) α i j)
          (extChartAt I α q.2)) Sp := by
  have hF := chartGramOnE_set (I := I) g J α hsmooth i j
  have hcore := (spatialJet_set
    (G := fun t y => Integral.DivergenceTheorem.chartGramOnE (I := I) (g t) α i j y)
    hJ isOpen_interior hF k hk).continuousOn
  have hΨcont : ContinuousOn (fun q : ℝ × M => (q.1, extChartAt I α q.2)) Sp :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        (fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) (hSp hq).2))
  have hΨmaps : Set.MapsTo (fun q : ℝ × M => (q.1, extChartAt I α q.2)) Sp
      (J ×ˢ interior ((extChartAt I α).target)) :=
    fun q hq => ⟨(hSp hq).1, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) (hSp hq).2⟩
  refine (hcore.comp hΨcont hΨmaps).congr ?_
  intro q _
  rfl



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartGram_iteratedFDeriv_jointContinuousOn_of_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ) (α : M)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {Sp : Set (ℝ × M)}
    (hSp : Sp ⊆ Set.Ioo a b ×ˢ chartLeviCivitaGoodSet (I := I) α)
    (k : ℕ) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun q : ℝ × M =>
        iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g q.1) α i j)
          (extChartAt I α q.2)) Sp := by


  have hF := chartGramOnE_jointContDiffOn (I := I) g a b α hsmooth i j
  have hUopen : IsOpen (Set.Ioo a b ×ˢ interior ((extChartAt I α).target)) :=
    isOpen_Ioo.prod isOpen_interior
  have hcore := contOn_partial_iteratedFDeriv_of_contDiffOn hUopen hF k
  have hΨcont : ContinuousOn (fun q : ℝ × M => (q.1, extChartAt I α q.2)) Sp :=
    continuous_fst.continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) α).comp continuous_snd.continuousOn
        (fun q hq => chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) (hSp hq).2))
  have hΨmaps : Set.MapsTo (fun q : ℝ × M => (q.1, extChartAt I α q.2)) Sp
      (Set.Ioo a b ×ˢ interior ((extChartAt I α).target)) :=
    fun q hq => ⟨(hSp hq).1, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) (hSp hq).2⟩


  refine (hcore.comp hΨcont hΨmaps).congr ?_
  intro q _
  rfl









omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricFrameComp_jointContMDiffOn_of_chartGram
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    {Idx : Type} [Fintype Idx] (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2 (frame i p.2) (frame j p.2))
      (Set.Ioo a b ×ˢ u) := by



  have hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2
        ((g q.1).inner q.2)))
      (Set.Ioo a b ×ˢ u) :=
    (metricCLMSection_jointContMDiffOn_of_chartGram_Ioo (I := I) g a b hsmooth).mono
      (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame i p.2)) (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn i).comp contMDiffOn_snd (fun p hp => hp.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame j p.2)) (Set.Ioo a b ×ˢ u) :=
    (hframe.contMDiffOn j).comp contMDiffOn_snd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ)
    (b := fun p : ℝ × M => p.2)
    (s := Set.Ioo a b ×ˢ u)
    (ψ := fun p : ℝ × M => (g p.1).inner p.2)
    (v := fun p : ℝ × M => frame i p.2)
    (w := fun p : ℝ × M => frame j p.2)
    hψ hv hw
  intro p hp
  have hpx := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2







omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricVariationEquationOn_of_pde
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hpde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        ((-2 : ℝ) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g t) x v w)
        (Set.Ici a) t) :
    MetricVariationEquationOn (I := I)
      ({ base := { metric := g } } :
        SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab)) := by
  intro t x X Y


  have ht : (t : ℝ) ∈ Set.Ioo a b := t.2
  have htmem : (t : ℝ) ∈ Set.Ico a b := Set.Ioo_subset_Ico_self ht
  have h : HasDerivWithinAt (fun s : ℝ => (g s).inner x X Y)
      ((-2 : ℝ) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g (t : ℝ)) x X Y)
      (Set.Ico a b) (t : ℝ) :=
    (hpde (t : ℝ) htmem x X Y).mono Set.Ico_subset_Ici_self
  simpa [SolutionFamily.ricciAt, metricRicciAt, metricRicciAt_apply_eq_ricciTensor] using h

set_option maxHeartbeats 1000000 in






omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem metricFamilySmoothOn_of_chartGram
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.MetricFamilySmoothOn (I := I) (M := M)
      (RealTimeInterval.closedOpen a b hab)
      ({ base := { metric := g } } :
        SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab)).family := by

  have hcontTensor :
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
        (Set.Ico a b) (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x) := by
    apply metricTensorCont_of_chartGram (K := Set.Ico a b) g
    intro x₀ i j
    have hincl : ContinuousOn
        (fun q : {t : ℝ // t ∈ Set.Ico a b} × M => ((q.1 : ℝ), q.2))
        {q : {t : ℝ // t ∈ Set.Ico a b} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
    exact (hcont x₀ i j).comp hincl (fun q hq => ⟨q.1.2, hq⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·


    intro x X Y
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun t : ℝ => (t, x)) (Set.Ioo a b) :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have hψ' : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun t : ℝ => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
          ((g t).inner x))) (Set.Ioo a b) :=
      (metricCLMSection_jointContMDiffOn_of_chartGram_Ioo (I := I) g a b hsmooth).comp
        hcurve (fun t ht => ⟨ht, Set.mem_univ _⟩)
    have hv : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x X) (Set.Ioo a b) :=
      contMDiffOn_const
    have hw : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun _ : ℝ => TotalSpace.mk' E (E := fun y => TangentSpace I y) x Y) (Set.Ioo a b) :=
      contMDiffOn_const
    have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
      (E₃ := Bundle.Trivial M ℝ)
      (b := fun _ : ℝ => x)
      (ψ := fun t : ℝ => (g t).inner x)
      (v := fun _ : ℝ => X) (w := fun _ : ℝ => Y)
      hψ' hv hw
    have hscalar : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (g t).inner x X Y) (Set.Ioo a b) := by
      intro t ht
      have hpt := happ t ht
      rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
      exact hpt.2
    exact hscalar.contDiffOn
  ·

    intro x X Y
    have hbase :
        ContinuousOn
          (fun s : ℝ => Tensor0SBundle.metricTensorField (I := I) (g s) x
            (DifferentialGeometry.Integral.Connection.vec2 X Y))
          (Set.Ico a b) := by
      rw [continuousOn_iff_continuous_restrict]
      exact hcontTensor.eval_continuous (P := {s : ℝ // s ∈ Set.Ico a b})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun p => p.2) continuous_const
        (v := fun i _ => DifferentialGeometry.Integral.Connection.vec2 X Y i)
        (fun _ => continuous_const)
    refine hbase.congr (fun s _ => ?_)
    simp [Tensor0SBundle.metricTensorField_apply, DifferentialGeometry.Integral.Connection.vec2]
  ·
    exact hcontTensor
  ·
    intro Idx _ frame u hframe i j
    exact metricFrameComp_jointContMDiffOn_of_chartGram (I := I) g a b hsmooth frame hframe i j



omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciCont_of_joint [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      J (fun t x => metricRicciAt (I := I) (g t) x) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp _
    (fun x₀ => chartLeviCivitaGoodSet (I := I) x₀)
    (fun x₀ => (chartLeviCivitaGoodSet_isOpen (I := I) x₀).mem_nhds
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)))
  intro x₀ idx
  have hframe := ricciChartFrameComp_jointContinuousOn (I := I) g x₀
    (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) (fun q hq => hq.2)
    (fun a' b' => chartGram_jet_set
      (I := I) g J hJ x₀ hsmooth subset_rfl 0 (by omega) a' b')
    (fun a' b' => chartGram_jet_set
      (I := I) g J hJ x₀ hsmooth subset_rfl 1 (by omega) a' b')
    (fun a' b' => chartGram_jet_set
      (I := I) g J hJ x₀ hsmooth subset_rfl 2 (by omega) a' b')
    (idx 0) (idx 1)
  have hincl : ContinuousOn
      (fun q : {t : ℝ // t ∈ J} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ J} × M | q.2 ∈ chartLeviCivitaGoodSet (I := I) x₀} :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : Set.MapsTo
      (fun q : {t : ℝ // t ∈ J} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ J} × M | q.2 ∈ chartLeviCivitaGoodSet (I := I) x₀}
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) :=
    fun q hq => ⟨q.1.2, hq⟩
  refine (hframe.comp hincl hmaps).congr ?_
  intro q _
  have hvec : (fun k : Fin 2 => Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) q.2)
      = DifferentialGeometry.Integral.Connection.vec2
          (Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx 0) q.2)
          (Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx 1) q.2) := by
    funext k; fin_cases k <;> rfl
  show metricRicciAt (I := I) (g q.1.1) q.2
      (fun k : Fin 2 => Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) q.2) = _
  rw [hvec]
  exact metricRicciAt_apply_eq_ricciTensor (g q.1.1) q.2 _ _


omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciCont_interior_of_chartGram [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Ioo a b) (fun t x => metricRicciAt (I := I) (g t) x) :=
  ricciCont_of_joint (I := I) g (Set.Ioo a b) isOpen_Ioo.uniqueDiffOn hsmooth



omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rm04_coord_eq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (idx : Fin 4 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) x₀) :
    DifferentialGeometry.Integral.Connection.metricRm04At (I := I) g x
        (fun k : Fin 4 => Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) x)
      = ∑ l : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) g x₀ (idx 2) (idx 0) (idx 1) l (extChartAt I x₀ x) *
            Integral.Measure.chartGramMatrix (I := I) g x₀ x (idx 3) l := by
  have hcov := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  have hvec : (fun k : Fin 4 => Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx k) x)
      = DifferentialGeometry.Integral.Connection.vec4
          (Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx 0) x)
          (Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx 1) x)
          (Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx 2) x)
          (Integral.Measure.chartBasisVecFiber (I := I) x₀ (idx 3) x) := by
    funext k; fin_cases k <;> rfl
  rw [hvec, metricRm04At_eq_riemannCurvature04At,
    CovariantDerivative.riemannCurvature04At_apply_const,
    riemannCurvatureAux_tangentConst_eq_riemannOp (cov := LeviCivita (I := I) g) (hcov := hcov),
    riemannOp_chartBasisVec_alpha_eq (I := I) g x₀ (idx 2) (idx 0) (idx 1) hx, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, smul_eq_mul, ← Integral.Measure.chartGramMatrix_apply]



omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rm04Cont_of_joint [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      J
      (fun t x => DifferentialGeometry.Integral.Connection.metricRm04At (I := I) (g t) x) := by
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp _
    (fun x₀ => chartLeviCivitaGoodSet (I := I) x₀)
    (fun x₀ => (chartLeviCivitaGoodSet_isOpen (I := I) x₀).mem_nhds
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := x₀)))
  intro x₀ idx
  have hsum : ContinuousOn
      (fun q : ℝ × M =>
        ∑ l : Fin (Module.finrank ℝ E),
          chartRiemannTensor (I := I) (g q.1) x₀ (idx 2) (idx 0) (idx 1) l (extChartAt I x₀ q.2) *
            Integral.Measure.chartGramMatrix (I := I) (g q.1) x₀ q.2 (idx 3) l)
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
    refine continuousOn_finset_sum _ (fun l _ => ?_)
    refine (chartRiemann_jointContinuousOn (I := I) g x₀
        (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) (fun q hq => hq.2)
        (fun a' b' => chartGram_jet_set
          (I := I) g J hJ x₀ hsmooth subset_rfl 0 (by omega) a' b')
        (fun a' b' => chartGram_jet_set
          (I := I) g J hJ x₀ hsmooth subset_rfl 1 (by omega) a' b')
        (fun a' b' => chartGram_jet_set
          (I := I) g J hJ x₀ hsmooth subset_rfl 2 (by omega) a' b')
        (idx 2) (idx 0) (idx 1) l).mul ?_
    exact ((hsmooth x₀ (idx 3) l).continuousOn).mono
      (Set.prod_mono subset_rfl
        (fun y hy => chartLeviCivitaGoodSet_mem_baseSet (I := I) hy))
  have hincl : ContinuousOn
      (fun q : {t : ℝ // t ∈ J} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ J} × M | q.2 ∈ chartLeviCivitaGoodSet (I := I) x₀} :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : Set.MapsTo
      (fun q : {t : ℝ // t ∈ J} × M => ((q.1 : ℝ), q.2))
      {q : {t : ℝ // t ∈ J} × M | q.2 ∈ chartLeviCivitaGoodSet (I := I) x₀}
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) :=
    fun q hq => ⟨q.1.2, hq⟩
  refine (hsum.comp hincl hmaps).congr ?_
  intro q hq
  exact rm04_coord_eq (I := I) (g q.1.1) x₀ idx hq


omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rm04Cont_interior_of_chartGram [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
      (Set.Ioo a b)
      (fun t x => DifferentialGeometry.Integral.Connection.metricRm04At (I := I) (g t) x) :=
  rm04Cont_of_joint (I := I) g (Set.Ioo a b) isOpen_Ioo.uniqueDiffOn hsmooth



omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem scalarCont_of_joint [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (fun q : ℝ × M => metricScalarAt (I := I) (g q.1) q.2)
      (J ×ˢ (Set.univ : Set M)) := by
  refine continuousOn_of_locally_continuousOn ?_
  intro p hp
  have hgood : p.2 ∈ chartLeviCivitaGoodSet (I := I) p.2 :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := p.2)
  let U : Set (ℝ × M) := Set.univ ×ˢ chartLeviCivitaGoodSet (I := I) p.2
  refine ⟨U, isOpen_univ.prod (chartLeviCivitaGoodSet_isOpen (I := I) p.2),
    ⟨Set.mem_univ p.1, hgood⟩, ?_⟩
  have hcs := chartScalar_jointContinuousOn (I := I) g p.2
    (J ×ˢ chartLeviCivitaGoodSet (I := I) p.2) (fun q hq => hq.2)
    (fun a' b' => chartGram_jet_set
      (I := I) g J hJ p.2 hsmooth subset_rfl 0 (by omega) a' b')
    (fun a' b' => chartGram_jet_set
      (I := I) g J hJ p.2 hsmooth subset_rfl 1 (by omega) a' b')
    (fun a' b' => chartGram_jet_set
      (I := I) g J hJ p.2 hsmooth subset_rfl 2 (by omega) a' b')
  refine hcs.mono ?_
  intro q hq
  exact ⟨hq.1.1, hq.2.2⟩


omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem scalarCont_interior_of_chartGram [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (fun q : ℝ × M => metricScalarAt (I := I) (g q.1) q.2)
      (Set.Ioo a b ×ˢ (Set.univ : Set M)) :=
  scalarCont_of_joint (I := I) g (Set.Ioo a b) isOpen_Ioo.uniqueDiffOn hsmooth



omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem scalarTime_of_joint [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (t : ℝ) (ht : t ∈ J) (x : M) :
    DifferentiableWithinAt ℝ (fun s : ℝ => metricScalarAt (I := I) (g s) x) J t := by
  classical

  have hgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hyint : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hgood
  have hxbase : ((extChartAt I x).symm (extChartAt I x x)) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [(extChartAt I x).left_inv (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hgood)]
    exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hgood

  have hjoint : ∀ c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) (g p.1) x c d p.2)
        (J ×ˢ interior (extChartAt I x).target) :=
    fun c d => chartGramOnE_set (I := I) g J x hsmooth c d
  have hp0 : ∀ c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun s : ℝ => chartGramOnE (I := I) (g s) x c d (extChartAt I x x))
        J :=
    fun c d => chartTimeSlice_contDiffOn hyint (hjoint c d)
  have hp1 : ∀ m c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun s : ℝ =>
        partialDeriv (E := E) m (chartGramOnE (I := I) (g s) x c d) (extChartAt I x x)) J :=
    fun m c d => chartTimeSlice_contDiffOn hyint
      (partialDeriv_set hJ isOpen_interior (hjoint c d) m)
  have hp2 : ∀ m l c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun s : ℝ =>
        partialDeriv (E := E) m (partialDeriv (E := E) l (chartGramOnE (I := I) (g s) x c d))
          (extChartAt I x x)) J :=
    fun m l c d => chartTimeSlice_contDiffOn hyint
      (partialDeriv_set hJ isOpen_interior
        (partialDeriv_set hJ isOpen_interior (hjoint c d) l) m)

  have hcd : ContDiffOn ℝ ∞
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (g s) x i j (extChartAt I x x) *
          chartRicciTensor (I := I) (g s) x i j (extChartAt I x x)) J := by
    refine ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => ?_))
    exact (chartInvGramOnE_contDiff_in_metric_at (I := I) g x (extChartAt I x x) J
        hp0 hxbase i j).mul
      (chartRicciTensor_contDiff (I := I) g x i j hyint J hxbase hp0 hp1 hp2)

  have hsum_eq : ∀ s' : ℝ, metricScalarAt (I := I) (g s') x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (g s') x i j (extChartAt I x x) *
          chartRicciTensor (I := I) (g s') x i j (extChartAt I x x) := by
    intro s'
    change DifferentialGeometry.Integral.Connection.metricScalarAt (I := I) (g s') x = _
    rw [metricScalar_chartTrace_eq (I := I) (g s') x hgood]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ricciTensor_chartBasisVec_alpha_eq (I := I) (g s') x i j hgood]
  exact ((hcd.congr (fun s' _ => hsum_eq s')).differentiableOn (by simp)) t ht


omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem scalarTime_interior_of_chartGram [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (a b : ℝ)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : M) :
    DifferentiableWithinAt ℝ (fun s : ℝ => metricScalarAt (I := I) (g s) x) (Set.Ioo a b) t :=
  scalarTime_of_joint (I := I) g (Set.Ioo a b) isOpen_Ioo.uniqueDiffOn hsmooth t ht x



omit [I.Boundaryless] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem solutionOn_of_joint [I.Boundaryless]
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        ((-2 : ℝ) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g t) x v w)
        (Set.Ici a) t) :
    IsSolutionOn (I := I)
      ({ base := { metric := g } } :
        SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab)) := by
  have hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hjoint x₀ i j).mono (Set.prod_mono_left Set.Ioo_subset_Ico_self)
  have hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hjoint x₀ i j).continuousOn
  refine
    { smoothMetric := metricFamilySmoothOn_of_chartGram (I := I) g hab hsmooth hcont
      smoothConnection := ?_
      equation := metricVariationEquationOn_of_pde (I := I) g hab hpde
      scalarCont := ?_
      scalarTime := ?_
      ricciCont := ?_
      rm04Cont := ?_
      ricciNormSpace := ?_
      ricciNormGrad := ?_ }
  · intro t
    simpa [SolutionOn.family, SolutionFamily.connection,
      DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt]
      using leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) (g (t : ℝ))
  · exact (scalarCont_of_joint (I := I) g (Set.Ico a b) (uniqueDiffOn_Ico a b) hjoint).congr
      (fun _ _ => rfl)
  · intro K t ht hK x
    simpa [SolutionOn.scalar, SolutionFamily.scalar] using
      (scalarTime_of_joint (I := I) g (Set.Ico a b) (uniqueDiffOn_Ico a b) hjoint t
        (hK ht) x).mono hK
  · refine DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.congr
      (ricciCont_of_joint (I := I) g (Set.Ico a b) (uniqueDiffOn_Ico a b) hjoint)
      (fun t _ x => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
  · refine DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.congr
      (rm04Cont_of_joint (I := I) g (Set.Ico a b) (uniqueDiffOn_Ico a b) hjoint)
      (fun t _ x => ?_)
    simp only [SolutionFamily.rm04, metricRm04_apply]
  · intro t ht x
    have h := (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := M)
      (g (t : ℝ)) (metricRicci (I := I) (M := M) (g (t : ℝ)))).mdifferentiableAt
      (by simp) (x := x)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
      SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
  · intro t ht x
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (ricciNorm (I := I)
          ({ base := { metric := g } } : SolutionOn (I := I) (M := M)
            (RealTimeInterval.closedOpen a b hab)) (t : ℝ)) := by
      refine (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := M)
        (g (t : ℝ)) (metricRicci (I := I) (M := M) (g (t : ℝ)))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact gradientFun_mdiffAt (I := I) (g (t : ℝ)) hs x











omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem isSolutionOn_of_extendData
    {α omega b : ℝ} (hαb : α < b) (hαω : α < omega)
    (g_ext : ℝ → SmoothRiemannianMetric I M)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen α omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hagree : ∀ s : ℝ, s < omega → g_ext s = S.base.metric s)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
        (Set.Ioo α b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_ext p.1) x₀ p.2 i j)
        (Set.Ico α b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ t ∈ Set.Ico α b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g_ext s).inner x v w)
        ((-2 : ℝ) * DifferentialGeometry.Integral.Connection.ricciTensor (I := I) (g_ext t) x v w)
        (Set.Ici α) t) :
    IsSolutionOn (I := I)
      ({ base := { metric := g_ext } } :
        SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen α b hαb)) := by
  refine
    { smoothMetric := ?_
      smoothConnection := ?_
      equation := ?_
      scalarCont := ?_
      scalarTime := ?_
      ricciCont := ?_
      rm04Cont := ?_
      ricciNormSpace := ?_
      ricciNormGrad := ?_ }
  ·
    exact metricFamilySmoothOn_of_chartGram (I := I) g_ext hαb hsmooth hcont
  ·
    intro t
    simpa [SolutionOn.family, SolutionFamily.connection,
      DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt]
      using leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) (g_ext (t : ℝ))
  ·
    exact metricVariationEquationOn_of_pde (I := I) g_ext hαb hpde
  ·
    have hinterior : ContinuousOn (fun q : ℝ × M => metricScalarAt (I := I) (g_ext q.1) q.2)
        (Set.Ioo α b ×ˢ (Set.univ : Set M)) :=
      scalarCont_interior_of_chartGram (I := I) g_ext α b hsmooth
    have hhalf : ContinuousOn (fun q : ℝ × M => metricScalarAt (I := I) (g_ext q.1) q.2)
        (Set.Ico α omega ×ˢ (Set.univ : Set M)) := by
      refine hS.scalarCont.congr (fun q hq => ?_)
      simp only [SolutionOn.scalar, SolutionFamily.scalar, hagree q.1 hq.1.2]
    have hglue : ContinuousOn (fun q : ℝ × M => metricScalarAt (I := I) (g_ext q.1) q.2)
        (Set.Ico α b ×ˢ (Set.univ : Set M)) := by
      intro p hp
      rcases lt_or_ge p.1 omega with hlt | hge
      · have hU : {q : ℝ × M | q.1 < omega} ∈ nhds p :=
          (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
        refine (continuousWithinAt_inter hU).mp ((hhalf.mono ?_).continuousWithinAt ⟨hp, hlt⟩)
        rintro ⟨t, x⟩ ⟨ht, htω⟩
        exact ⟨⟨ht.1.1, htω⟩, Set.mem_univ x⟩
      · have hU : {q : ℝ × M | α < q.1} ∈ nhds p :=
          (isOpen_lt continuous_const continuous_fst).mem_nhds (lt_of_lt_of_le hαω hge)
        refine (continuousWithinAt_inter hU).mp ((hinterior.mono ?_).continuousWithinAt
          ⟨hp, lt_of_lt_of_le hαω hge⟩)
        rintro ⟨t, x⟩ ⟨ht, hαt⟩
        exact ⟨⟨hαt, ht.1.2⟩, Set.mem_univ x⟩
    exact hglue.congr (fun q _ => rfl)
  ·
    intro K t htK hKsub x
    have hmain : DifferentiableWithinAt ℝ (fun s : ℝ => metricScalarAt (I := I) (g_ext s) x)
        (Set.Ico α b) t := by
      rcases (hKsub htK).1.eq_or_lt with hα | hα
      ·
        have hgerm : Set.Ico α omega =ᶠ[nhds t] Set.Ico α b := by
          have h1 : Set.Iio omega ∈ nhds t := Iio_mem_nhds (hα ▸ hαω)
          have h2 : Set.Iio b ∈ nhds t := Iio_mem_nhds (hα ▸ hαb)
          filter_upwards [h1, h2] with s hs1 hs2
          simp only [Set.mem_Iio] at hs1 hs2
          exact propext ⟨fun h => ⟨h.1, hs2⟩, fun h => ⟨h.1, hs1⟩⟩
        refine (differentiableWithinAt_congr_set hgerm).mp ?_
        refine (hS.scalarTime (K := Set.Ico α omega) (t := t) ⟨hα.le, hα ▸ hαω⟩
          subset_rfl x).congr (fun s hs => ?_) ?_
        · simp only [SolutionOn.scalar, SolutionFamily.scalar, hagree s hs.2]
        · simp only [SolutionOn.scalar, SolutionFamily.scalar, hagree t (hα ▸ hαω)]
      ·
        have hgerm : Set.Ioo α b =ᶠ[nhds t] Set.Ico α b := by
          filter_upwards [Ioi_mem_nhds hα] with s hs1
          simp only [Set.mem_Ioi] at hs1
          exact propext ⟨fun h => ⟨h.1.le, h.2⟩, fun h => ⟨hs1, h.2⟩⟩
        refine (differentiableWithinAt_congr_set hgerm).mp ?_
        exact scalarTime_interior_of_chartGram (I := I) g_ext α b hsmooth t
          ⟨hα, (hKsub htK).2⟩ x
    exact hmain.mono hKsub
  ·
    have hinterior :
        DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
          (Set.Ioo α b) (fun t x => metricRicciAt (I := I) (g_ext t) x) :=
      ricciCont_interior_of_chartGram (I := I) g_ext α b hsmooth
    have hhalf :
        DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
          (Set.Ico α omega) (fun t x => metricRicciAt (I := I) (g_ext t) x) := by
      refine DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.congr
        hS.ricciCont (fun t ht x => ?_)
      have h : g_ext t = S.base.metric t := hagree t ht.2
      simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt, h]
    have hglued :=
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.of_union_closedOpen
        (I := I) (M := M) (a := α) (c := omega) (b := b) hαω hhalf hinterior
    refine DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.congr
      hglued (fun t _ x => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
  ·
    have hinterior :
        DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
          (Set.Ioo α b)
          (fun t x => DifferentialGeometry.Integral.Connection.metricRm04At (I := I) (g_ext t) x) :=
      rm04Cont_interior_of_chartGram (I := I) g_ext α b hsmooth
    have hhalf :
        DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4
          (Set.Ico α omega)
          (fun t x => DifferentialGeometry.Integral.Connection.metricRm04At (I := I) (g_ext t) x) := by
      refine DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.congr
        hS.rm04Cont (fun t ht x => ?_)
      have h : g_ext t = S.base.metric t := hagree t ht.2
      simp only [SolutionFamily.rm04, metricRm04_apply, h]
    have hglued :=
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.of_union_closedOpen
        (I := I) (M := M) (a := α) (c := omega) (b := b) hαω hhalf hinterior
    refine DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.congr
      hglued (fun t _ x => ?_)
    simp only [SolutionFamily.rm04, metricRm04_apply]
  ·
    intro t ht x
    have h := (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := M)
      (g_ext (t : ℝ)) (metricRicci (I := I) (M := M) (g_ext (t : ℝ)))).mdifferentiableAt
      (by simp) (x := x)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
      SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
  ·
    intro t ht x
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (ricciNorm (I := I)
          ({ base := { metric := g_ext } } : SolutionOn (I := I) (M := M)
            (RealTimeInterval.closedOpen α b hαb)) (t : ℝ)) := by
      refine (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := M)
        (g_ext (t : ℝ)) (metricRicci (I := I) (M := M) (g_ext (t : ℝ)))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact gradientFun_mdiffAt (I := I) (g_ext (t : ℝ)) hsmooth x

end DifferentialGeometry.PDE.RicciFlow
