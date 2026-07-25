import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Geometry.Connection.LeviCivita.LinearExtensionTangent
import DifferentialGeometry.Geometry.Connection.LeviCivita.CorrectionContraction
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  [NeZero (Module.finrank ℝ F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem chartRep_restrict
    (gamma : ℝ → M) (X : ∀ y : M, TangentSpace I y) (t : ℝ) :
    chartRepAt (I := I) gamma (fun r => X (gamma r)) t =
      chartE_section_repr (I := I) (gamma t) X ∘ gamma := by
  funext s
  rfl

omit [CompleteSpace E] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem deriv_repr_comp_at
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (gamma : ℝ → M)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t) :
    deriv (chartE_section_repr (I := I) (gamma t) (fun x : M => Y x) ∘ gamma) t =
      fderiv ℝ
          (chartE_section_repr (I := I) (gamma t) (fun x : M => Y x) ∘
            (extChartAt I (gamma t)).symm)
          (extChartAt I (gamma t) (gamma t))
        (deriv (chartCurve (I := I) (gamma t) gamma) t) := by
  classical
  set a : M := gamma t with ha_def
  set f : E → E :=
    chartE_section_repr (I := I) a (fun x : M => Y x) ∘
      (extChartAt I a).symm with hf_def
  set u : ℝ → E := chartCurve (I := I) a gamma with hu_def
  have hgood : a ∈ chartLeviCivitaGoodSet (I := I) a :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := a)
  have hY : MDiffAt (T% (fun x : M => Y x)) (gamma t) :=
    Y.mdifferentiableAt
  have hf_diff : DifferentiableAt ℝ f (extChartAt I a (gamma t)) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) a hgood hY
  have hu_hd : HasDerivAt u (deriv u t) t := by
    have hchart : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s => extChartAt I a (gamma s)) t :=
      (contMDiffAt_extChartAt (I := I) (x := a)).comp t hgamma
    exact ((contMDiffAt_iff_contDiffAt.mp hchart).differentiableAt (by simp)).hasDerivAt
  have hxu : u t = extChartAt I a (gamma t) := by
    rw [hu_def, chartCurve_def]
  have hcomp_hd : HasDerivAt (f ∘ u)
      (fderiv ℝ f (extChartAt I a (gamma t)) (deriv u t)) t := by
    have hf_hd : HasFDerivAt f (fderiv ℝ f (extChartAt I a (gamma t))) (u t) := by
      rw [hxu]
      exact hf_diff.hasFDerivAt
    exact hf_hd.comp_hasDerivAt t hu_hd
  have hsrc_nhds : gamma ⁻¹' (extChartAt I a).source ∈ 𝓝 t := by
    have hopen : IsOpen (extChartAt I a).source := isOpen_extChartAt_source (I := I) a
    have hmem : gamma t ∈ (extChartAt I a).source := by
      rw [extChartAt_source]
      exact mem_chart_source H (gamma t)
    exact hgamma.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)
  have heq : (f ∘ u) =ᶠ[𝓝 t]
      chartE_section_repr (I := I) a (fun x : M => Y x) ∘ gamma := by
    filter_upwards [hsrc_nhds] with s hs
    simp only [Function.comp_apply, hf_def, hu_def, chartCurve_def]
    rw [PartialEquiv.left_inv (extChartAt I a) hs]
  rw [← ha_def] at hcomp_hd
  rw [← heq.deriv_eq]
  exact hcomp_hd.deriv

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covAlong_restrict_at
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t) :
    covDerivAlong (I := I) g gamma (fun r => Y (gamma r)) t =
      (LeviCivita (I := I) g) (fun x : M => Y x) (gamma t)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma t : ℝ →L[ℝ] _) (1 : ℝ)) := by
  classical
  set a : M := gamma t with ha_def
  set v : TangentSpace I a :=
    (mfderiv 𝓘(ℝ, ℝ) I gamma t : ℝ →L[ℝ] _) (1 : ℝ) with hv_def
  have hgood : a ∈ chartLeviCivitaGoodSet (I := I) a :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := a)
  have hsrc : a ∈ (chartAt H a).source := mem_chart_source H a
  have hvel : trivToE (I := I) a a v =
      deriv (chartCurve (I := I) a gamma) t := by
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := gamma)
        (hgamma.mdifferentiableAt (by simp)) a (t := t) hsrc
    rw [trivToE]
    rw [show v =
      (mfderiv 𝓘(ℝ, ℝ) I gamma t : ℝ →L[ℝ] _) (1 : ℝ) from rfl]
    rw [hbridge]
    rw [show (extChartAt I a ∘ gamma) =
      chartCurve (I := I) a gamma from rfl]
    exact fderiv_apply_one_eq_deriv
  have hYmd : MDiffAt (T% (fun x : M => Y x)) a := Y.mdifferentiableAt
  rw [show (LeviCivita (I := I) g) (fun x : M => Y x) (gamma t)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma t : ℝ →L[ℝ] _) (1 : ℝ)) =
      (LeviCivita (I := I) g).toFun (fun x : M => Y x) a v from rfl]
  rw [LeviCivita_chart_apply (I := I) g a hgood hYmd v]
  rw [chartLeviCivita_apply (I := I) g a (fun x : M => Y x) hgood v]
  rw [covDerivAlong_def, chartCovDerivAlong_def]
  rw [chartRep_restrict (I := I) gamma (fun x : M => Y x) t]
  rw [show (trivializationAt E (TangentSpace I) a).symmL ℝ a =
    trivFromE (I := I) a a from rfl]
  congr 1
  have hchris :
      chartChristoffelContraction (I := I) g a
          (deriv (chartCurve (I := I) a gamma) t)
          ((chartE_section_repr (I := I) a (fun x : M => Y x) ∘ gamma) t)
          (chartCurve (I := I) a gamma t) =
        christoffelCorrection (I := I) g a a
          (chartE_section_repr (I := I) a (fun x : M => Y x) a) v := by
    rw [correction_eq_contr (I := I) g a a
      (chartE_section_repr (I := I) a (fun x : M => Y x) a) v]
    rw [hvel]
    rw [Function.comp_apply, ← ha_def, chartCurve_def, ← ha_def]
  have hderiv :
      deriv (chartE_section_repr (I := I) a (fun x : M => Y x) ∘ gamma) t =
        fderiv ℝ
            (chartE_section_repr (I := I) a (fun x : M => Y x) ∘
              (extChartAt I a).symm)
            (extChartAt I a a) (trivToE (I := I) a a v) := by
    rw [hvel]
    exact deriv_repr_comp_at (I := I) gamma Y t hgamma
  rw [hderiv, hchris]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
private theorem mfderiv_from_chart
    [I.Boundaryless] [IsManifold I 1 M]
    (f : M → F) (a p : M) (hp : p ∈ (chartAt H a).source)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f p) (v : E) :
    mfderiv I 𝓘(ℝ, F) f p (trivFromE (I := I) a p v) =
      fderiv ℝ (writtenInExtChartAt I 𝓘(ℝ, F) a f)
        (extChartAt I a p) v := by
  let z : E := extChartAt I a p
  have hsource : p ∈ (extChartAt I a).source := by
    simpa [extChartAt_source] using hp
  have hzTarget : z ∈ (extChartAt I a).target := by
    simpa [z] using (extChartAt I a).map_source hsource
  have hsymm : (extChartAt I a).symm z = p := by
    simpa [z] using (extChartAt I a).left_inv hsource
  have hrange : Set.range I ∈ nhds z := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  have hsymmDiff :
      MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I a).symm
        (Set.range I) z := by
    simpa [z] using mdifferentiableWithinAt_extChartAt_symm (I := I) hzTarget
  have hfUniv :
      MDifferentiableWithinAt I 𝓘(ℝ, F) f Set.univ
        ((extChartAt I a).symm z) := by
    rw [hsymm]
    exact hf.mdifferentiableWithinAt
  have hmaps :
      Set.range I ⊆ (extChartAt I a).symm ⁻¹' (Set.univ : Set M) := by
    intro y hy
    simp
  have huniq : UniqueMDiffWithinAt 𝓘(ℝ, E) (Set.range I) z := by
    exact (I.uniqueDiffOn.uniqueDiffWithinAt
      (by exact extChartAt_target_subset_range (I := I) a hzTarget)).uniqueMDiffWithinAt
  have hchain :=
    mfderivWithin_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, F))
      (x := z) (g := f) (f := (extChartAt I a).symm)
      hfUniv hsymmDiff hmaps huniq
  have hchainApply :
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, F) a f)
          (Set.range I) z v =
        mfderiv I 𝓘(ℝ, F) f p
          ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I a).symm
            (Set.range I) z) v) := by
    have happ := congrArg (fun L => L v) hchain
    rw [mfderivWithin_eq_fderivWithin, mfderivWithin_univ] at happ
    rw [hsymm] at happ
    simpa [writtenInExtChartAt, z, ContinuousLinearMap.comp_apply] using happ
  have hfield :
      trivFromE (I := I) a p v =
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I a).symm
          (Set.range I) z) v := by
    have hlin := TangentBundle.symmL_trivializationAt
      (𝕜 := ℝ) (I := I) (x₀ := a) (x := p) hp
    have happ := congrArg (fun L => L v) hlin
    simpa [trivFromE, z] using happ
  have hwithin :
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, F) a f)
          (Set.range I) z v =
        fderiv ℝ (writtenInExtChartAt I 𝓘(ℝ, F) a f) z v := by
    rw [fderivWithin_of_mem_nhds hrange]
  rw [hfield]
  exact hchainApply.symm.trans hwithin

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
private theorem triv_mfderiv_cross
    [I.Boundaryless] [J.Boundaryless]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (Phi : M ≃ₘ⟮I, J⟯ N) (a p : M) (b : N)
    (hp : p ∈ (chartAt H a).source)
    (hPhip : Phi p ∈ (chartAt G b).source) (v : E) :
    trivToE (I := J) b (Phi p)
        (mfderiv I J (Phi : M → N) p (trivFromE (I := I) a p v)) =
      fderiv ℝ
        (fun z : E => extChartAt J b (Phi ((extChartAt I a).symm z)))
        (extChartAt I a p) v := by
  have hPhi : MDifferentiableAt I J (Phi : M → N) p :=
    Phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hext : MDifferentiableAt J 𝓘(ℝ, F) (extChartAt J b) (Phi p) :=
    mdifferentiableAt_extChartAt (I := J) hPhip
  have htriv :
      trivToE (I := J) b (Phi p) =
        mfderiv J 𝓘(ℝ, F) (extChartAt J b) (Phi p) :=
    TangentBundle.continuousLinearMapAt_trivializationAt (I := J) hPhip
  have hcomp := mfderiv_comp_apply (I := I) (I' := J) (I'' := 𝓘(ℝ, F))
    (g := extChartAt J b) (f := (Phi : M → N)) (x := p)
    hext hPhi (trivFromE (I := I) a p v)
  rw [htriv]
  have hfixed := mfderiv_from_chart (I := I)
    (f := fun y : M => extChartAt J b (Phi y)) a p hp
    (hext.comp p hPhi) v
  calc
    mfderiv J 𝓘(ℝ, F) (extChartAt J b) (Phi p)
          (mfderiv I J (Phi : M → N) p (trivFromE (I := I) a p v)) =
        mfderiv I 𝓘(ℝ, F) (fun y : M => extChartAt J b (Phi y)) p
          (trivFromE (I := I) a p v) := by
      simpa [Function.comp_def] using hcomp.symm
    _ = fderiv ℝ
        (fun z : E => extChartAt J b (Phi ((extChartAt I a).symm z)))
        (extChartAt I a p) v := by
      simpa [writtenInExtChartAt, Function.comp_def] using hfixed

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
private theorem chartRep_mapCross_ev
    [I.Boundaryless] [J.Boundaryless]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (Phi : M ≃ₘ⟮I, J⟯ N) (gamma : ℝ → M)
    (V : ∀ s, TangentSpace I (gamma s)) (t : ℝ)
    (hgamma : ContinuousAt gamma t) :
    chartRepAt (I := J) (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)) t =ᶠ[nhds t]
      fun s =>
        fderiv ℝ (writtenInExtChartAt I J (gamma t) (Phi : M → N))
          (chartCurve (I := I) (gamma t) gamma s)
          (chartRepAt (I := I) gamma V t s) := by
  have hsrc : ∀ᶠ s in nhds t, gamma s ∈ (chartAt H (gamma t)).source := by
    exact hgamma.preimage_mem_nhds
      ((chartAt H (gamma t)).open_source.mem_nhds (mem_chart_source H (gamma t)))
  have htarget :
      ∀ᶠ s in nhds t, Phi (gamma s) ∈ (chartAt G (Phi (gamma t))).source := by
    have hcont : ContinuousAt (fun s => Phi (gamma s)) t :=
      Phi.continuous.continuousAt.comp hgamma
    exact hcont.preimage_mem_nhds
      ((chartAt G (Phi (gamma t))).open_source.mem_nhds
        (mem_chart_source G (Phi (gamma t))))
  filter_upwards [hsrc, htarget] with s hs hPhis
  have hbase : gamma s ∈
      (trivializationAt E (TangentSpace I) (gamma t)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hs
  rw [chartRepAt_apply, chartRepAt_apply]
  let w : E := trivToE (I := I) (gamma t) (gamma s) (V s)
  change trivToE (I := J) (Phi (gamma t)) (Phi (gamma s))
      (mfderiv I J (Phi : M → N) (gamma s) (V s)) =
    fderiv ℝ (writtenInExtChartAt I J (gamma t) (Phi : M → N))
      (chartCurve (I := I) (gamma t) gamma s) w
  have hV : V s = trivFromE (I := I) (gamma t) (gamma s) w := by
    exact (trivFromE_trivToE (I := I) (gamma t) hbase (V s)).symm
  rw [hV]
  simpa [writtenInExtChartAt, chartCurve, Function.comp_def] using
    (triv_mfderiv_cross (I := I) (J := J) Phi (gamma t) (gamma s)
      (Phi (gamma t)) hs hPhis w)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
private theorem deriv_fderiv_apply_zero
    (psi : E → F) (u w : ℝ → E) (t : ℝ)
    (hpsi : ContDiffAt ℝ 2 psi (u t))
    (hu : DifferentiableAt ℝ u t) (hw : DifferentiableAt ℝ w t)
    (hwt : w t = 0) :
    deriv (fun s => fderiv ℝ psi (u s) (w s)) t =
      fderiv ℝ psi (u t) (deriv w t) := by
  have hDpsi : DifferentiableAt ℝ (fun s => fderiv ℝ psi (u s)) t := by
    exact ((hpsi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp t hu
  rw [deriv_clm_apply hDpsi hw, hwt, map_zero, zero_add]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ F] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
private theorem chartRep_mapCross_diff
    [I.Boundaryless] [J.Boundaryless]
    [IsManifold I 1 M] [IsManifold J 1 N]
    (Phi : M ≃ₘ⟮I, J⟯ N) (gamma : ℝ → M)
    (V : ∀ s, TangentSpace I (gamma s)) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t) :
    DifferentiableAt ℝ
      (chartRepAt (I := J) (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)) t) t := by
  let a : M := gamma t
  let psi : E → F := writtenInExtChartAt I J a (Phi : M → N)
  let u : ℝ → E := chartCurve (I := I) a gamma
  let w : ℝ → E := chartRepAt (I := I) gamma V t
  have hu : DifferentiableAt ℝ u t := by
    have hchart : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s => extChartAt I a (gamma s)) t := by
      exact (contMDiffAt_extChartAt (I := I) (x := a)).comp t hgamma
    exact (contMDiffAt_iff_contDiffAt.mp hchart).differentiableAt (by simp)
  have hpsi : ContDiffAt ℝ 2 psi (u t) := by
    have hPhi := Phi.contMDiff.contMDiffAt (x := a)
    have hwithin := (contMDiffAt_iff.mp hPhi).2
    have hinfty : ContDiffAt ℝ ∞ psi (u t) := by
      simpa [psi, u, a, chartCurve,
        ModelWithCorners.Boundaryless.range_eq_univ (I := I)] using hwithin
    exact hinfty.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hDpsi : DifferentiableAt ℝ (fun s => fderiv ℝ psi (u s)) t := by
    exact ((hpsi.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp t hu
  have hright : DifferentiableAt ℝ (fun s => fderiv ℝ psi (u s) (w s)) t :=
    hDpsi.clm_apply hV
  have hev := chartRep_mapCross_ev (I := I) (J := J) Phi gamma V t
    hgamma.continuousAt
  exact hright.congr_of_eventuallyEq (by simpa [a, psi, u, w] using hev)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompleteSpace F] [NeZero (Module.finrank ℝ F)] in
private theorem covAlong_mapCross_zero
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (V : ∀ s, TangentSpace I (gamma s)) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t)
    (hVt : V t = 0) :
    mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma V t) =
      covDerivAlong (I := J) g (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)) t := by
  let a : M := gamma t
  let b : N := Phi a
  let delta : ℝ → N := fun s => Phi (gamma s)
  let W : ∀ s, TangentSpace J (delta s) :=
    fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)
  let psi : E → F := writtenInExtChartAt I J a (Phi : M → N)
  let u : ℝ → E := chartCurve (I := I) a gamma
  let w : ℝ → E := chartRepAt (I := I) gamma V t
  have hw0 : w t = 0 := by
    simp [w, chartRepAt_apply, hVt]
  have hW0 : W t = 0 := by
    simp [W, delta, hVt]
  have hu : DifferentiableAt ℝ u t := by
    have hchart : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s => extChartAt I a (gamma s)) t := by
      exact (contMDiffAt_extChartAt (I := I) (x := a)).comp t hgamma
    exact (contMDiffAt_iff_contDiffAt.mp hchart).differentiableAt (by simp)
  have hpsi : ContDiffAt ℝ 2 psi (u t) := by
    have hPhi := Phi.contMDiff.contMDiffAt (x := a)
    have hwithin := (contMDiffAt_iff.mp hPhi).2
    have hinfty : ContDiffAt ℝ ∞ psi (u t) := by
      simpa [psi, u, a, chartCurve,
        ModelWithCorners.Boundaryless.range_eq_univ (I := I)] using hwithin
    exact hinfty.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hrepEv :
      chartRepAt (I := J) delta W t =ᶠ[nhds t]
        fun s => fderiv ℝ psi (u s) (w s) := by
    simpa [a, b, delta, W, psi, u, w] using
      (chartRep_mapCross_ev (I := I) (J := J) Phi gamma V t
        hgamma.continuousAt)
  have hrepDeriv :
      deriv (chartRepAt (I := J) delta W t) t =
        fderiv ℝ psi (u t) (deriv w t) := by
    rw [hrepEv.deriv_eq]
    exact deriv_fderiv_apply_zero psi u w t hpsi hu hV hw0
  have hsourceChart :
      chartCovDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          a gamma w t = deriv w t := by
    rw [chartCovDerivAlong_def, hw0,
      ChartChristoffel.contraction_zero_right, add_zero]
  have htargetChart :
      chartCovDerivAlong (I := J) g b delta
          (chartRepAt (I := J) delta W t) t =
        fderiv ℝ psi (u t) (deriv w t) := by
    rw [chartCovDerivAlong_def, hrepDeriv]
    have hrep0 : chartRepAt (I := J) delta W t t = 0 := by
      simp [chartRepAt_apply, hW0]
    rw [hrep0, ChartChristoffel.contraction_zero_right, add_zero]
  have haSrc : a ∈ (chartAt H a).source := mem_chart_source H a
  have hbSrc : b ∈ (chartAt G b).source := mem_chart_source G b
  have hleftCoord :
      trivToE (I := J) b b
          (mfderiv I J (Phi : M → N) a
            (covDerivAlong (I := I)
              (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
              gamma V t)) =
        fderiv ℝ psi (u t) (deriv w t) := by
    rw [covDerivAlong_def]
    change trivToE (I := J) b b
        (mfderiv I J (Phi : M → N) a
          (trivFromE (I := I) a a
            (chartCovDerivAlong (I := I)
              (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
              a gamma w t))) = _
    rw [hsourceChart]
    simpa [psi, u, a, b, chartCurve, writtenInExtChartAt, Function.comp_def] using
      (triv_mfderiv_cross (I := I) (J := J) Phi a a b haSrc hbSrc (deriv w t))
  have hrightCoord :
      trivToE (I := J) b b (covDerivAlong (I := J) g delta W t) =
        fderiv ℝ psi (u t) (deriv w t) := by
    have hcoord := covDerivAlong_chartCoord (I := J) g delta W t
    change trivToE (I := J) b b (covDerivAlong (I := J) g delta W t) =
      chartCovDerivAlong (I := J) g b delta
        (chartRepAt (I := J) delta W t) t at hcoord
    exact hcoord.trans htargetChart
  change mfderiv I J (Phi : M → N) a
      (covDerivAlong (I := I)
        (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
        gamma V t) = covDerivAlong (I := J) g delta W t
  have hbBase : b ∈ (trivializationAt F (TangentSpace J) b).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hbSrc
  rw [← trivFromE_trivToE (I := J) b hbBase
      (mfderiv I J (Phi : M → N) a
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma V t)),
    ← trivFromE_trivToE (I := J) b hbBase
      (covDerivAlong (I := J) g delta W t), hleftCoord, hrightCoord]



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem covAlong_mapCrossAt
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t) :
    mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma (fun s => Y (gamma s)) t) =
      covDerivAlong (I := J) g (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (Y (gamma s))) t := by
  let delta : ℝ → N := fun s => Phi (gamma s)
  let Ypush := DifferentialGeometry.Integral.Connection.pushFwdSectionCross
    (I := I) (J := J) Phi Y
  let v : TangentSpace I (gamma t) :=
    (mfderiv 𝓘(ℝ, ℝ) I gamma t : ℝ →L[ℝ] TangentSpace I (gamma t)) (1 : ℝ)
  have hdelta : ContMDiffAt 𝓘(ℝ, ℝ) J ∞ delta t := by
    exact Phi.contMDiff.contMDiffAt.comp t hgamma
  have hleft := covAlong_restrict_at
    (I := I)
    (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
    gamma Y t hgamma
  have hright := covAlong_restrict_at
    (I := J) g delta Ypush t hdelta
  have hPhi : MDifferentiableAt I J (Phi : M → N) (gamma t) :=
    Phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hgammaAt : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t :=
    hgamma.mdifferentiableAt (by simp)
  have hvel :
      (mfderiv 𝓘(ℝ, ℝ) J delta t : ℝ →L[ℝ] TangentSpace J (delta t)) (1 : ℝ) =
        mfderiv I J (Phi : M → N) (gamma t) v := by
    simpa [delta, v, Function.comp_def] using
      (mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := J)
        (g := (Phi : M → N)) (f := gamma) (x := t) hPhi hgammaAt (1 : ℝ))
  have hcov := DifferentialGeometry.Integral.Connection.metricCov_pullbackCross
    (I := I) (J := J) g Phi Y (gamma t) v
  calc
    mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma (fun s => Y (gamma s)) t) =
      mfderiv I J (Phi : M → N) (gamma t)
        ((LeviCivita (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi))
          (fun x : M => Y x) (gamma t) v) := by rw [hleft]
    _ = (LeviCivita (I := J) g) (fun x : N => Ypush x) (Phi (gamma t))
        (mfderiv I J (Phi : M → N) (gamma t) v) := by
      simpa [LeviCivita, DifferentialGeometry.Integral.Connection.metricCov,
        Ypush] using hcov
    _ = (LeviCivita (I := J) g) (fun x : N => Ypush x) (delta t)
        ((mfderiv 𝓘(ℝ, ℝ) J delta t : ℝ →L[ℝ] TangentSpace J (delta t)) (1 : ℝ)) := by
      rw [hvel]
    _ = covDerivAlong (I := J) g delta (fun s => Ypush (delta s)) t := hright.symm
    _ = covDerivAlong (I := J) g (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (Y (gamma s))) t := by
      simp [delta, Ypush]



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem covAlong_mapCross
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (t : ℝ)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma) :
    mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma (fun s => Y (gamma s)) t) =
      covDerivAlong (I := J) g (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (Y (gamma s))) t :=
  covAlong_mapCrossAt (I := I) (J := J) g Phi gamma Y t hgamma.contMDiffAt



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem covAlong_natCrossAt
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (V : ∀ s, TangentSpace I (gamma s)) (t : ℝ)
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ gamma t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t) :
    mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma V t) =
      covDerivAlong (I := J) g (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)) t := by
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    { toFun := linearExtensionTangent (I := I) (gamma t) (V t)
      contMDiff_toFun := linearExtensionTangent_smooth (I := I) (gamma t) (V t) }
  let Yalong : ∀ s, TangentSpace I (gamma s) := fun s => Y (gamma s)
  let R : ∀ s, TangentSpace I (gamma s) := fun s => V s - Yalong s
  let delta : ℝ → N := fun s => Phi (gamma s)
  let Ymap : ∀ s, TangentSpace J (delta s) :=
    fun s => mfderiv I J (Phi : M → N) (gamma s) (Yalong s)
  let Rmap : ∀ s, TangentSpace J (delta s) :=
    fun s => mfderiv I J (Phi : M → N) (gamma s) (R s)
  let Vmap : ∀ s, TangentSpace J (delta s) :=
    fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)
  have hbase : gamma t ∈
      (trivializationAt E (TangentSpace I) (gamma t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (gamma t)
  have hYmd : MDiffAt
      (chartE_section_repr (I := I) (gamma t) (fun x : M => Y x)) (gamma t) :=
    (mdifferentiableAt_section_iff_chartE I (gamma t) (fun x : M => Y x) hbase).mp
      Y.mdifferentiableAt
  have hYrep :
      chartRepAt (I := I) gamma Yalong t =
        chartE_section_repr (I := I) (gamma t) (fun x : M => Y x) ∘ gamma := by
    funext s
    rfl
  have hYdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) gamma Yalong t) t := by
    rw [hYrep]
    exact mdifferentiableAt_iff_differentiableAt.mp
      (hYmd.comp t (hgamma.mdifferentiableAt (by simp)))
  have hRrep :
      chartRepAt (I := I) gamma R t =
        fun s => chartRepAt (I := I) gamma V t s -
          chartRepAt (I := I) gamma Yalong t s := by
    funext s
    simp [R, Yalong, chartRepAt_apply, map_sub]
  have hRdiff : DifferentiableAt ℝ (chartRepAt (I := I) gamma R t) t := by
    rw [hRrep]
    exact hV.sub hYdiff
  have hRt : R t = 0 := by
    simp [R, Yalong, Y]
  have hYmapDiff : DifferentiableAt ℝ
      (chartRepAt (I := J) delta Ymap t) t := by
    simpa [delta, Ymap] using
      (chartRep_mapCross_diff (I := I) (J := J) Phi gamma Yalong t hgamma hYdiff)
  have hRmapDiff : DifferentiableAt ℝ
      (chartRepAt (I := J) delta Rmap t) t := by
    simpa [delta, Rmap] using
      (chartRep_mapCross_diff (I := I) (J := J) Phi gamma R t hgamma hRdiff)
  have hYnat := covAlong_mapCrossAt (I := I) (J := J) g Phi gamma Y t hgamma
  have hRnat := covAlong_mapCross_zero (I := I) (J := J) g Phi gamma R t
    hgamma hRdiff hRt
  have hsourceAdd := covDerivAlong_add
    (I := I) (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
    gamma Yalong R t hYdiff hRdiff
  have htargetAdd := covDerivAlong_add
    (I := J) g delta Ymap Rmap t hYmapDiff hRmapDiff
  have hsource : (fun s => Yalong s + R s) = V := by
    funext s
    simp [R]
  have htarget : (fun s => Ymap s + Rmap s) = Vmap := by
    funext s
    simp [Ymap, Rmap, Vmap, R, map_sub]
  calc
    mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma V t) =
      mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma (fun s => Yalong s + R s) t) := by rw [hsource]
    _ = mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
            gamma Yalong t +
          covDerivAlong (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
            gamma R t) := by rw [hsourceAdd]
    _ = mfderiv I J (Phi : M → N) (gamma t)
          (covDerivAlong (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
            gamma Yalong t) +
        mfderiv I J (Phi : M → N) (gamma t)
          (covDerivAlong (I := I)
            (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
            gamma R t) := by rw [map_add]
    _ = covDerivAlong (I := J) g delta Ymap t +
        covDerivAlong (I := J) g delta Rmap t := by
      rw [hYnat, hRnat]
    _ = covDerivAlong (I := J) g delta
        (fun s => Ymap s + Rmap s) t := htargetAdd.symm
    _ = covDerivAlong (I := J) g delta Vmap t := by rw [htarget]



omit [NeZero (Module.finrank ℝ E)] [NeZero (Module.finrank ℝ F)] in
theorem covAlong_natCross
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (gamma : ℝ → M) (V : ∀ s, TangentSpace I (gamma s)) (t : ℝ)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) gamma V t) t) :
    mfderiv I J (Phi : M → N) (gamma t)
        (covDerivAlong (I := I)
          (Diffeomorph.pullbackMetricCross (I := I) (J := J) g Phi)
          gamma V t) =
      covDerivAlong (I := J) g (fun s => Phi (gamma s))
        (fun s => mfderiv I J (Phi : M → N) (gamma s) (V s)) t :=
  covAlong_natCrossAt (I := I) (J := J) g Phi gamma V t
    hgamma.contMDiffAt hV

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
