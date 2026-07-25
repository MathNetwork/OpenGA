import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCCenterOfMass
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Exponential.DiagInvReadout
import Mathlib.Analysis.Calculus.Implicit

set_option autoImplicit false
set_option linter.style.longLine false



































noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Topology
















theorem cmSolution_hasStrictFDerivAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {Ey : Type*} [NormedAddCommGroup Ey] [NormedSpace 𝕜 Ey] [CompleteSpace Ey]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    (φ : ImplicitFunctionData 𝕜 (Ey × P) F P) :
    HasStrictFDerivAt
      (fun params : P => (φ.implicitFunction (φ.leftFun φ.pt) params).1)
      ((ContinuousLinearMap.fst 𝕜 Ey P).comp
        (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)))
      (φ.rightFun φ.pt) :=
  (ContinuousLinearMap.fst 𝕜 Ey P).hasStrictFDerivAt.comp (φ.rightFun φ.pt)
    φ.hasStrictFDerivAt_implicitFunction_fderiv

section ChartEquation

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]







noncomputable def chartCmEqn (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (p : M) (z : E) (params : (ι → ℝ) × (ι → E)) : E :=
  ∑ i : ι, params.1 i •
    (NormalCoordinates.normalChartAt (I := I) g
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) : E)







theorem chartCmEqn_center (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r)
    (hcm : (centerOfMass (I := I) g μ pts join p r h) ∈
      (NormalCoordinates.normalChartAt (I := I) g p).source)
    (hpts : ∀ i : ι, pts i ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    chartCmEqn (I := I) g p
        (NormalCoordinates.normalChartAt (I := I) g p (centerOfMass (I := I) g μ pts join p r h))
        (μ, fun i => NormalCoordinates.normalChartAt (I := I) g p (pts i))
      = ∑ i : ι, μ i •
          (NormalCoordinates.normalChartAt (I := I) g
            (centerOfMass (I := I) g μ pts join p r h) (pts i) : E) := by
  unfold chartCmEqn
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [NormalCoordinates.normalChartAt_left_inv (I := I) g p hcm,
    NormalCoordinates.normalChartAt_left_inv (I := I) g p (hpts i)]









def CmHessianInput (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (p : M) (z₀ : E) (params : (ι → ℝ) × (ι → E)) : Prop :=
  ∃ L : E ≃L[ℝ] E,
    HasFDerivAt (fun z : E => chartCmEqn (I := I) g p z params) (L : E →L[ℝ] E) z₀

















omit [NeZero (Module.finrank ℝ E)] in
theorem implicitSol_hasStrictFDerivAt
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (D : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E)
    (hjoint : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) D (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E, HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀ : G z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀, G (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          G zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  classical
  obtain ⟨L, hL⟩ := hinv

  have hk : HasFDerivAt (fun z : E => (z, params₀))
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) z₀ :=
    (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const params₀ z₀)
  have hDL : D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) = (L : E →L[ℝ] E) := by
    have h1 : HasFDerivAt
        ((fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) ∘
          (fun z : E => (z, params₀)))
        (D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E)))) z₀ :=
      hjoint.hasFDerivAt.comp z₀ hk
    exact h1.unique hL
  have hDv : ∀ v : E, D (v, (0 : (ι → ℝ) × (ι → E))) = L v := by
    intro v
    have h := DFunLike.congr_fun hDL v
    simpa [ContinuousLinearMap.inl_apply] using h
  have hDsurj : Function.Surjective ⇑D := fun w =>
    ⟨(L.symm w, 0), by rw [hDv]; exact L.apply_symm_apply w⟩

  let φ : ImplicitFunctionData ℝ (E × ((ι → ℝ) × (ι → E))) E ((ι → ℝ) × (ι → E)) :=
    { leftFun := fun w => G w.1 w.2
      leftDeriv := D
      rightFun := Prod.snd
      rightDeriv := ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))
      pt := (z₀, params₀)
      hasStrictFDerivAt_leftFun := hjoint
      hasStrictFDerivAt_rightFun := hasStrictFDerivAt_snd
      range_leftDeriv := LinearMap.range_eq_top.mpr hDsurj
      range_rightDeriv := LinearMap.range_eq_top.mpr Prod.snd_surjective
      isCompl_ker := by
        constructor
        · rw [disjoint_iff, Submodule.eq_bot_iff]
          rintro ⟨z, q⟩ hmem
          rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hmem
          obtain ⟨hzD, hzS⟩ := hmem
          have hq : q = 0 := hzS
          subst hq
          have hLz : L z = 0 := by rw [← hDv]; exact hzD
          have hz : z = 0 := by have := congrArg L.symm hLz; simpa using this
          simp [hz]
        · rw [codisjoint_iff, Submodule.eq_top_iff']
          rintro ⟨z, q⟩
          rw [Submodule.mem_sup]
          refine ⟨(-(L.symm (D (0, q))), q), ?_, (z + L.symm (D (0, q)), 0), ?_, ?_⟩
          · rw [LinearMap.mem_ker]
            change D (-(L.symm (D ((0 : E), q))), q) = 0
            have hsplit : D (-(L.symm (D ((0 : E), q))), q)
                = D (-(L.symm (D ((0 : E), q))), (0 : (ι → ℝ) × (ι → E))) + D ((0 : E), q) := by
              rw [← ContinuousLinearMap.map_add]; congr 1; simp
            rw [hsplit, hDv]
            simp [map_neg, ContinuousLinearEquiv.apply_symm_apply]
          · rw [LinearMap.mem_ker]; rfl
          · simp }

  have hf0 : (φ.implicitFunction (φ.leftFun φ.pt) params₀).1 = z₀ := by
    have hpt : φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun φ.pt) = φ.pt := by
      rw [ImplicitFunctionData.implicitFunction_apply, ← ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      exact φ.toOpenPartialHomeomorph.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
    have hr : φ.rightFun φ.pt = params₀ := rfl
    rw [← hr, hpt]
  refine ⟨fun params => (φ.implicitFunction (φ.leftFun φ.pt) params).1,
    (ContinuousLinearMap.fst ℝ E ((ι → ℝ) × (ι → E))).comp
      (fderiv ℝ (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)),
    hf0, cmSolution_hasStrictFDerivAt φ, ?_, ?_⟩
  ·
    have htend : Filter.Tendsto
        (fun params : (ι → ℝ) × (ι → E) => (φ.leftFun φ.pt, params))
        (nhds params₀) (nhds (φ.prodFun φ.pt)) :=
      tendsto_const_nhds.prodMk_nhds Filter.tendsto_id
    have hleft := htend.eventually φ.leftFun_implicitFunction
    have hright := htend.eventually φ.rightFun_implicitFunction
    filter_upwards [hleft, hright] with params hl hr
    set x := φ.implicitFunction (φ.leftFun φ.pt) params with hx
    have hr' : x.2 = params := hr
    calc G x.1 params
        = φ.leftFun (x.1, params) := rfl
      _ = φ.leftFun x := by rw [← hr']
      _ = φ.leftFun φ.pt := hl
      _ = 0 := hz₀
  ·
    filter_upwards [φ.leftFun_eq_iff_implicitFunction] with zp hzp hGzp
    have hle : φ.leftFun zp = φ.leftFun φ.pt := hGzp.trans hz₀.symm
    exact congrArg Prod.fst (hzp.mp hle).symm




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem existsPinnedDeriv
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E)
    (params₀ : (ι → ℝ) × (ι → E)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hjoint : ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀) :
    ∃ Deq : (E × ((ι → ℝ) × (ι → E))) ≃L[ℝ]
        (E × ((ι → ℝ) × (ι → E))),
      HasStrictFDerivAt
        (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
        (Deq : (E × ((ι → ℝ) × (ι → E))) →L[ℝ]
          (E × ((ι → ℝ) × (ι → E)))) (z₀, params₀) := by
  classical
  obtain ⟨L, hL⟩ := hinv
  have hjoint_strict : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2)
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
      (z₀, params₀) := hjoint.hasStrictFDerivAt hn
  set D := fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2)
    (z₀, params₀)
  have hjoint_hd : HasFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) D (z₀, params₀) :=
    hjoint_strict.hasFDerivAt
  have hk : HasFDerivAt (fun z : E => (z, params₀))
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) z₀ :=
    (hasFDerivAt_id z₀).prodMk (hasFDerivAt_const params₀ z₀)
  have hDL : D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))) =
      (L : E →L[ℝ] E) := by
    have h1 : HasFDerivAt
        ((fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) ∘
          (fun z : E => (z, params₀)))
        (D.comp (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E)))) z₀ :=
      hjoint_hd.comp z₀ hk
    exact h1.unique hL
  have hDv : ∀ v : E, D (v, (0 : (ι → ℝ) × (ι → E))) = L v := by
    intro v
    have h := DFunLike.congr_fun hDL v
    simpa [ContinuousLinearMap.inl_apply] using h
  have hDsplit : ∀ (v : E) (u : (ι → ℝ) × (ι → E)),
      D (v, u) = L v + D ((0 : E), u) := by
    intro v u
    have hsum : ((v, u) : E × ((ι → ℝ) × (ι → E))) =
        (v, (0 : (ι → ℝ) × (ι → E))) + ((0 : E), u) := by
      ext <;> simp
    rw [hsum, map_add, hDv]
  let Deq : (E × ((ι → ℝ) × (ι → E))) ≃L[ℝ]
      (E × ((ι → ℝ) × (ι → E))) :=
    ContinuousLinearEquiv.equivOfInverse
      (D.prod (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))))
      (((L.symm : E →L[ℝ] E).comp
          (ContinuousLinearMap.fst ℝ E ((ι → ℝ) × (ι → E)) -
            (D.comp (ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E)))).comp
              (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))))).prod
        (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E))))
      (by
        rintro ⟨v, u⟩
        have hk2 : D (v, u) - D ((0 : E), u) = L v := by
          rw [hDsplit v u]
          abel
        simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply,
          ContinuousLinearEquiv.coe_coe, Prod.mk.injEq, and_true]
        rw [hk2]
        exact L.symm_apply_apply v)
      (by
        rintro ⟨a, b⟩
        simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply,
          ContinuousLinearEquiv.coe_coe, Prod.mk.injEq, and_true]
        rw [hDsplit (L.symm (a - D ((0 : E), b))) b, L.apply_symm_apply]
        abel)
  have hΦ_hd : HasFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
      (Deq : (E × ((ι → ℝ) × (ι → E))) →L[ℝ]
        (E × ((ι → ℝ) × (ι → E)))) (z₀, params₀) := by
    change HasFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
      (D.prod (ContinuousLinearMap.snd ℝ E ((ι → ℝ) × (ι → E)))) (z₀, params₀)
    exact hjoint_hd.prodMk hasFDerivAt_snd
  have hΦcd : ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2)) (z₀, params₀) :=
    hjoint.prodMk contDiffAt_snd
  exact ⟨Deq, hΦcd.hasStrictFDerivAt' hΦ_hd hn⟩




omit [NeZero (Module.finrank ℝ E)] in
theorem existsPinnedLocal
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E)
    (params₀ : (ι → ℝ) × (ι → E)) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (hjoint : ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀) :
    ∃ e : OpenPartialHomeomorph
        (E × ((ι → ℝ) × (ι → E))) (E × ((ι → ℝ) × (ι → E))),
      (z₀, params₀) ∈ e.source ∧
        (e : (E × ((ι → ℝ) × (ι → E))) →
          (E × ((ι → ℝ) × (ι → E)))) =
          fun w => (G w.1 w.2, w.2) := by
  obtain ⟨Deq, hΦ⟩ := existsPinnedDeriv G z₀ params₀ hn hjoint hinv
  exact ⟨hΦ.toOpenPartialHomeomorph _, hΦ.mem_toOpenPartialHomeomorph_source, rfl⟩









omit [NeZero (Module.finrank ℝ E)] in
theorem implicitSol_contDiffAt
    {ι : Type} [Fintype ι]
    (G : E → ((ι → ℝ) × (ι → E)) → E) (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ) (hn : 1 ≤ n)
    (hjoint : ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) => G w.1 w.2) (z₀, params₀))
    (hinv : ∃ L : E ≃L[ℝ] E, HasFDerivAt (fun z : E => G z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀ : G z₀ params₀ = 0) :
    ∃ f : ((ι → ℝ) × (ι → E)) → E,
      f params₀ = z₀ ∧ ContDiffAt ℝ (n : ℕ∞) f params₀ ∧
        (∀ᶠ params in nhds params₀, G (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          G zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  classical
  have hn0 : ((n : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨Deq, hΦstrict⟩ := existsPinnedDeriv G z₀ params₀ hn0 hjoint hinv
  have hΦ_hd := hΦstrict.hasFDerivAt
  have hΦcd : ContDiffAt ℝ (n : ℕ∞) (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2))
      (z₀, params₀) := hjoint.prodMk contDiffAt_snd
  set invF := hΦstrict.localInverse
    (fun w : E × ((ι → ℝ) × (ι → E)) => (G w.1 w.2, w.2)) Deq (z₀, params₀) with hinvF

  have hinvF_cd : ContDiffAt ℝ (n : ℕ∞) invF
      ((G z₀ params₀, params₀) : E × ((ι → ℝ) × (ι → E))) :=
    hΦcd.to_localInverse hΦ_hd hn0
  rw [hz₀] at hinvF_cd
  refine ⟨fun params => (invF ((0 : E), params)).1, ?_, ?_, ?_, ?_⟩
  · change (invF ((0 : E), params₀)).1 = z₀
    have him : invF ((G z₀ params₀, params₀) : E × ((ι → ℝ) × (ι → E))) = (z₀, params₀) :=
      hΦstrict.localInverse_apply_image
    rw [hz₀] at him
    rw [him]
  · have hg1 : ContDiffAt ℝ (n : ℕ∞)
        (fun params : (ι → ℝ) × (ι → E) => ((0 : E), params)) params₀ :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (hinvF_cd.comp params₀ hg1).fst
  · have htend : Filter.Tendsto (fun params : (ι → ℝ) × (ι → E) => ((0 : E), params))
        (nhds params₀) (nhds ((0 : E), params₀)) :=
      tendsto_const_nhds.prodMk_nhds Filter.tendsto_id
    have hri : ∀ᶠ y in nhds ((G z₀ params₀, params₀) : E × ((ι → ℝ) × (ι → E))),
        (G (invF y).1 (invF y).2, (invF y).2) = y := hΦstrict.eventually_right_inverse
    rw [hz₀] at hri
    have hpb := htend.eventually hri
    filter_upwards [hpb] with params hq
    have hq2 : (invF ((0 : E), params)).2 = params := congrArg Prod.snd hq
    have hq1 : G (invF ((0 : E), params)).1 (invF ((0 : E), params)).2 = 0 :=
      congrArg Prod.fst hq
    change G (invF ((0 : E), params)).1 params = 0
    rw [hq2] at hq1; exact hq1
  · have hli : ∀ᶠ x in nhds ((z₀, params₀) : E × ((ι → ℝ) × (ι → E))),
        invF (G x.1 x.2, x.2) = x := hΦstrict.eventually_left_inverse
    filter_upwards [hli] with zp hzp
    intro hG
    have hΦzp : ((G zp.1 zp.2, zp.2) : E × ((ι → ℝ) × (ι → E))) = ((0 : E), zp.2) := by rw [hG]
    rw [hΦzp] at hzp
    change zp.1 = (invF ((0 : E), zp.2)).1
    rw [hzp]


omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [T3Space M] in
theorem chartCm_hasStrictFDerivAt
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (p : M) (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (D : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E)
    (hjoint : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn (I := I) g p w.1 w.2) D (z₀, params₀))
    (hinv : CmHessianInput (I := I) g p z₀ params₀)
    (hz₀ : chartCmEqn (I := I) g p z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀, chartCmEqn (I := I) g p (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqn (I := I) g p zp.1 zp.2 = 0 → zp.1 = f zp.2) :=
  implicitSol_hasStrictFDerivAt (fun z params => chartCmEqn (I := I) g p z params)
    z₀ params₀ D hjoint hinv hz₀

end ChartEquation

section DiagExpIdentification

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in










omit [T3Space M] in
omit [ConnectedSpace M] in
theorem normalChart_eq_diagExpInv_snd
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p y q : M)
    (hsrc : (diagExpInv (I := I) g hEnorm p (y, q)).snd ∈
      (NormalCoordinates.expMapDiffeo (I := I) g y).source)
    (hexp : NormalCoordinates.expMapDiffeo (I := I) g y
        (show TangentSpace I y from (diagExpInv (I := I) g hEnorm p (y, q)).snd) = q) :
    (NormalCoordinates.normalChartAt (I := I) g y q : E)
      = (diagExpInv (I := I) g hEnorm p (y, q)).snd := by
  have h := (NormalCoordinates.expMapDiffeo (I := I) g y).left_inv hsrc
  rw [hexp] at h
  exact h

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem diagExpInv_eq_normal
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p y q : M)
    (hproj : (diagExpInv (I := I) g hEnorm p (y, q)).proj = y)
    (hsrc : (diagExpInv (I := I) g hEnorm p (y, q)).snd ∈
      (NormalCoordinates.expMapDiffeo (I := I) g y).source)
    (hexp : NormalCoordinates.expMapDiffeo (I := I) g y
        (show TangentSpace I y from
          (diagExpInv (I := I) g hEnorm p (y, q)).snd) = q) :
    diagExpInv (I := I) g hEnorm p (y, q) =
      (⟨y, (show TangentSpace I y from
        NormalCoordinates.normalChartAt (I := I) g y q)⟩ : TangentBundle I M) := by
  refine TotalSpace.ext hproj ?_
  exact heq_of_eq
    (normalChart_eq_diagExpInv_snd (I := I) g hEnorm p y q hsrc hexp).symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [T3Space M] in
omit [ConnectedSpace M] in
theorem diagInv_eq_normal_lt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p y q : M)
    (hproj : (diagExpInv (I := I) g hEnorm p (y, q)).proj = y)
    (hintr : expMapIntrinsic (I := I) g hEnorm y
      (diagExpInv (I := I) g hEnorm p (y, q)).snd = q)
    (hsmall : Real.sqrt
      (g.inner y
        (diagExpInv (I := I) g hEnorm p (y, q)).snd
        (diagExpInv (I := I) g hEnorm p (y, q)).snd) <
      expDiffeoRadius (I := I) g hEnorm y) :
    diagExpInv (I := I) g hEnorm p (y, q) =
      (⟨y, (show TangentSpace I y from
        NormalCoordinates.normalChartAt (I := I) g y q)⟩ : TangentBundle I M) := by
  have hsrc := expDiffeo_mem_of_lt (I := I) g hEnorm y hsmall
  have hcompat := expDiffeo_eq_intr (I := I) g hEnorm y hsmall
  exact diagExpInv_eq_normal (I := I) g hEnorm p y q
    hproj hsrc (hcompat.trans hintr)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







omit [T3Space M] in
omit [ConnectedSpace M] in
theorem diagExpReadout_contMDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M =>
        (trivializationAt E (TangentSpace I) p (diagExpInv (I := I) g hEnorm p yq)).2) (p, p) := by
  have h := diagExpInv_contMDiffAt (I := I) g hEnorm p
  rw [contMDiffAt_totalSpace] at h
  have hproj : (diagExpInv (I := I) g hEnorm p (p, p)).proj = p := by
    rw [diagExpInv_center]
  rw [hproj] at h
  exact h.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem diagExpReadout_contMDiffAt_order
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M =>
        (trivializationAt E (TangentSpace I) p (diagExpInv (I := I) g hEnorm p yq)).2) (p, p) := by
  have h := diagExpInv_contMDiffAt_order (I := I) g hEnorm p n hn
  rw [contMDiffAt_totalSpace] at h
  have hproj : (diagExpInv (I := I) g hEnorm p (p, p)).proj = p := by
    rw [diagExpInv_center]
  rw [hproj] at h
  exact h.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [T3Space M] in
omit [ConnectedSpace M] in
theorem diagReadout_of_md
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (yq : M × M) (n : ℕ)
    (hsm : ContMDiffAt (I.prod I) I.tangent (n : ℕ∞)
      (diagExpInv (I := I) g hEnorm p) yq)
    (hbase : (diagExpInv (I := I) g hEnorm p yq).proj ∈
      (trivializationAt E (TangentSpace I) p).baseSet) :
    ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun w : M × M =>
        (trivializationAt E (TangentSpace I) p
          (diagExpInv (I := I) g hEnorm p w)).2) yq := by
  exact (((trivializationAt E (TangentSpace I) p).contMDiffAt_iff
    ((trivializationAt E (TangentSpace I) p).mem_source.2 hbase)).mp hsm).2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [T3Space M] in
omit [ConnectedSpace M] in
theorem exists_readoutDom
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set (M × M), IsOpen U ∧ (p, p) ∈ U ∧
      ∀ y ∈ U,
        ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
          (fun w : M × M =>
            (trivializationAt E (TangentSpace I) p
              (diagExpInv (I := I) g hEnorm p w)).2) y ∧
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  obtain ⟨U, hUopen, hpU, hU⟩ := exists_diagInvDom (I := I) g hEnorm p n hn
  let e := trivializationAt E (TangentSpace I) p
  let V := U ∩ Prod.fst ⁻¹' e.baseSet
  have hVopen : IsOpen V := hUopen.inter (e.open_baseSet.preimage continuous_fst)
  have hpV : (p, p) ∈ V :=
    ⟨hpU, mem_baseSet_trivializationAt E (TangentSpace I) p⟩
  refine ⟨V, hVopen, hpV, ?_⟩
  intro y hy
  have hbranch := hU y hy.1
  have hbase : (diagExpInv (I := I) g hEnorm p y).proj ∈ e.baseSet := by
    rw [hbranch.2.2.1]
    exact hy.2
  exact ⟨diagReadout_of_md (I := I) g hEnorm p y n hbranch.1 hbase,
    hbranch.2⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [T3Space M] in
omit [ConnectedSpace M] in
theorem exists_readoutDom_inf
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ U : Set (M × M), IsOpen U ∧ (p, p) ∈ U ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
        (fun y : M × M =>
          (trivializationAt E (TangentSpace I) p
            (diagExpInv (I := I) g hEnorm p y)).2) U ∧
      ∀ y ∈ U,
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  obtain ⟨U, hUopen, hpU, hUsmooth, hU⟩ :=
    exists_diagInvDom_inf (I := I) g hEnorm p
  let e := trivializationAt E (TangentSpace I) p
  let V := U ∩ Prod.fst ⁻¹' e.baseSet
  have hVopen : IsOpen V := hUopen.inter (e.open_baseSet.preimage continuous_fst)
  have hpV : (p, p) ∈ V :=
    ⟨hpU, mem_baseSet_trivializationAt E (TangentSpace I) p⟩
  have hVsmooth : ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
      (fun y : M × M =>
        (trivializationAt E (TangentSpace I) p
          (diagExpInv (I := I) g hEnorm p y)).2) V := by
    intro y hy
    have hbranchAt : ContMDiffAt (I.prod I) I.tangent ∞
        (diagExpInv (I := I) g hEnorm p) y :=
      (hUsmooth y hy.1).contMDiffAt (hUopen.mem_nhds hy.1)
    have hbase : (diagExpInv (I := I) g hEnorm p y).proj ∈ e.baseSet := by
      rw [(hU y hy.1).2.1]
      exact hy.2
    have hreadAt : ContMDiffAt (I.prod I) 𝓘(ℝ, E) ∞
        (fun w : M × M =>
          (trivializationAt E (TangentSpace I) p
            (diagExpInv (I := I) g hEnorm p w)).2) y :=
      (((trivializationAt E (TangentSpace I) p).contMDiffAt_iff
        ((trivializationAt E (TangentSpace I) p).mem_source.2 hbase)).mp hbranchAt).2
    exact hreadAt.contMDiffWithinAt
  refine ⟨V, hVopen, hpV, hVsmooth, ?_⟩
  intro y hy
  exact hU y hy.1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [ConnectedSpace M] in
theorem exists_readoutEBall
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ δ < ⊤ ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
        (fun y : M × M =>
          (trivializationAt E (TangentSpace I) p
            (diagExpInv (I := I) g hEnorm p y)).2)
        {y : M × M |
          max (riemannianEDist I y.1 p) (riemannianEDist I y.2 p) < δ} ∧
      ∀ y : M × M,
        max (riemannianEDist I y.1 p) (riemannianEDist I y.2 p) < δ →
        diagExp (I := I) g hEnorm (diagExpInv (I := I) g hEnorm p y) = y ∧
        (diagExpInv (I := I) g hEnorm p y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1
          (diagExpInv (I := I) g hEnorm p y).snd = y.2 := by
  obtain ⟨U, hUopen, hpU, hUsmooth, hU⟩ :=
    exists_readoutDom_inf (I := I) g hEnorm p
  have hextract : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ < ⊤ ∧
      {y : M × M |
        max (riemannianEDist I y.1 p) (riemannianEDist I y.2 p) < δ} ⊆ U := by
    haveI : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (M := M) I
    haveI : RegularSpace M := inferInstance
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    obtain ⟨ε, hεpos, hεball⟩ := EMetric.isOpen_iff.mp hUopen (p, p) hpU
    let δ : ℝ≥0∞ := min ε 1
    have hδpos : 0 < δ := lt_min hεpos (by norm_num)
    have hδtop : δ < (⊤ : ℝ≥0∞) :=
      lt_of_le_of_lt (min_le_right ε 1) (by simp)
    have hball : Metric.eball (p, p) δ ⊆ U :=
      (Metric.eball_subset_eball (min_le_left ε 1)).trans hεball
    refine ⟨δ, hδpos, hδtop, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_eball, Prod.edist_eq]
    exact hy
  obtain ⟨δ, hδpos, hδtop, hball⟩ := hextract
  refine ⟨δ, hδpos, hδtop, hUsmooth.mono hball, ?_⟩
  intro y hy
  exact hU y (hball hy)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem centerPairs_lt_of
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (q : M) {δ : ℝ≥0∞}
    (hδ :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      ENNReal.ofReal (dist p q + 2 * r) < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    ∀ i : ι,
      max
        (riemannianEDist I (centerOfMass (I := I) g μ pts join p r h) q)
        (riemannianEDist I (pts i) q) < δ := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
  have hriem (x y : M) :
      riemannianEDist I x y = ENNReal.ofReal (dist x y) := by
    rw [HopfRinow.riemMetric_dist_eq (I := I) x y]
    exact (ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) x y)).symm
  have hcm :
      dist (centerOfMass (I := I) g μ pts join p r h) p ≤ 2 * r := by
    simpa [Metric.mem_closedBall, dist_comm] using
      (centerOfMass.mem (I := I) (g := g) (μ := μ) (pts := pts)
        (join := join) (p := p) (r := r) h)
  intro i
  apply max_lt
  · rw [hriem]
    apply lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hδ
    calc
      dist (centerOfMass (I := I) g μ pts join p r h) q
          ≤ dist (centerOfMass (I := I) g μ pts join p r h) p + dist p q :=
        dist_triangle _ _ _
      _ ≤ 2 * r + dist p q := add_le_add_left hcm _
      _ = dist p q + 2 * r := add_comm _ _
  · rw [hriem]
    apply lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hδ
    calc
      dist (pts i) q ≤ dist (pts i) p + dist p q := dist_triangle _ _ _
      _ ≤ r + dist p q := by
        apply add_le_add_left
        simpa [dist_comm] using (h.pts_mem i).le
      _ ≤ 2 * r + dist p q := by linarith [h.r_pos]
      _ = dist p q + 2 * r := add_comm _ _

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem centerPairs_lt_le
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) (q : M) (R : ℝ) {δ : ℝ≥0∞}
    (hpq :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
      dist p q ≤ R)
    (hδ : ENNReal.ofReal (R + 2 * r) < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    ∀ i : ι,
      max
        (riemannianEDist I (centerOfMass (I := I) g μ pts join p r h) q)
        (riemannianEDist I (pts i) q) < δ := by
  apply centerPairs_lt_of (I := I) g μ pts join p r h q
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (add_le_add_left hpq _)) hδ

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [RiemannianBundle (fun x : M => TangentSpace I x)] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem centerPairs_lt
    (g : SmoothRiemannianMetric I M) {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (pts : ι → M) (join : M → M → ℝ → M) (p : M) (r : ℝ)
    (h : CenterInput (I := I) g μ pts join p r) {δ : ℝ≥0∞}
    (hδ : ENNReal.ofReal (2 * r) < δ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    ∀ i : ι,
      max
        (riemannianEDist I (centerOfMass (I := I) g μ pts join p r h) p)
        (riemannianEDist I (pts i) p) < δ := by
  simpa using
    (centerPairs_lt_of (I := I) g μ pts join p r h p (by simpa using hδ))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



noncomputable def chartCmEqnB
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z : E) (params : (ι → ℝ) × (ι → E)) : E :=
  ∑ i : ι, params.1 i •
    B.diagReadout
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







noncomputable def chartCmEqn'
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z : E) (params : (ι → ℝ) × (ι → E)) : E :=
  ∑ i : ι, params.1 i •
    (trivializationAt E (TangentSpace I) p
      (diagExpInv (I := I) g hEnorm p
        ((NormalCoordinates.normalChartAt (I := I) g p).symm z,
          (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)))).2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem chartCmEqnB_std
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z : E) (params : (ι → ℝ) × (ι → E)) :
    chartCmEqnB (I := I) g hEnorm p (stdBranch (I := I) g hEnorm p) z params =
      chartCmEqn' (I := I) g hEnorm p z params := by
  unfold chartCmEqnB chartCmEqn' DiagInvBranch.diagReadout
  rw [std_inv_eq (I := I) g hEnorm p]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem chartCmEqnB_cdAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ∞)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I n
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I n
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) n
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))) :
    ContDiffAt ℝ n
      (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2) (z₀, params₀) := by
  unfold chartCmEqnB
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.smul
  · fun_prop
  · rw [← contMDiffAt_iff_contDiffAt]
    have hfst : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) n
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.1) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    have hproj : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) n
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.2.2 i) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]
      fun_prop
    have hinner : ContMDiffAt
        𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) (I.prod I) n
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.normalChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.normalChartAt (I := I) g p).symm (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.prodMk (ContMDiffAt.comp (z₀, params₀) hchz hfst)
        (ContMDiffAt.comp (z₀, params₀) (hchξ i) hproj)
    have hcomp : ContMDiffAt
        𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) n
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          B.diagReadout
            ((NormalCoordinates.normalChartAt (I := I) g p).symm w.1,
              (NormalCoordinates.normalChartAt (I := I) g p).symm (w.2.2 i)))
        (z₀, params₀) :=
      ContMDiffAt.comp
        (I := 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))))
        (I' := I.prod I) (I'' := 𝓘(ℝ, E))
        (f := fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.normalChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.normalChartAt (I := I) g p).symm (w.2.2 i)))
        (g := fun yq : M × M => B.diagReadout yq)
        (z₀, params₀) (hsm i) hinner
    exact hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readoutB_sum_eq
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, B.inv (y, qs i) =
      (⟨y, (show TangentSpace I y from
        (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • B.diagReadout (y, qs i)) =
      (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
        (show TangentSpace I y from
          ∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
  have hterm : ∀ i, B.diagReadout (y, qs i) =
      (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
        (show TangentSpace I y from
          (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
    intro i
    unfold DiagInvBranch.diagReadout
    rw [hpt i]
    exact congrArg Prod.snd
      ((trivializationAt E (TangentSpace I) p).apply_eq_prod_continuousLinearEquivAt ℝ y hy _)
  simp_rw [hterm]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (map_smul _ (μ i) _).symm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readoutB_zero_iff
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, B.inv (y, qs i) =
      (⟨y, (show TangentSpace I y from
        (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • B.diagReadout (y, qs i)) = 0 ↔
      (∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) = 0 := by
  rw [readoutB_sum_eq (I := I) g hEnorm p B μ y qs hy hpt]
  exact (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy |>.map_eq_zero_iff

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readoutSolB_strict
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E)
      (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀,
          chartCmEqnB (I := I) g hEnorm p B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqnB (I := I) g hEnorm p B zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2)
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2) (z₀, params₀))
      (z₀, params₀) :=
    (chartCmEqnB_cdAt (I := I) g hEnorm p B z₀ params₀ 1 hchz hchξ hsm).hasStrictFDerivAt
      one_ne_zero
  exact implicitSol_hasStrictFDerivAt
    (fun z params => chartCmEqnB (I := I) g hEnorm p B z params)
    z₀ params₀ _ hjoint hinv hzero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readoutSolB_cdAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0) :
    ∃ f : ((ι → ℝ) × (ι → E)) → E,
      f params₀ = z₀ ∧ ContDiffAt ℝ (n : ℕ∞) f params₀ ∧
        (∀ᶠ params in nhds params₀,
          chartCmEqnB (I := I) g hEnorm p B (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqnB (I := I) g hEnorm p B zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint : ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) =>
        chartCmEqnB (I := I) g hEnorm p B w.1 w.2) (z₀, params₀) :=
    chartCmEqnB_cdAt (I := I) g hEnorm p B z₀ params₀ n hchz hchξ hsm
  exact implicitSol_contDiffAt
    (fun z params => chartCmEqnB (I := I) g hEnorm p B z params)
    z₀ params₀ n hn hjoint hinv hzero

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readout_sum_eq_clm
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, diagExpInv (I := I) g hEnorm p (y, qs i)
      = (⟨y, (show TangentSpace I y from
          (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p (y, qs i))).2)
      = (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
          (show TangentSpace I y from
            ∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
  have hterm : ∀ i, (trivializationAt E (TangentSpace I) p
      (diagExpInv (I := I) g hEnorm p (y, qs i))).2
      = (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy
          (show TangentSpace I y from
            (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) := by
    intro i
    rw [hpt i]
    exact congrArg Prod.snd
      ((trivializationAt E (TangentSpace I) p).apply_eq_prod_continuousLinearEquivAt ℝ y hy _)
  simp_rw [hterm]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (map_smul _ (μ i) _).symm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readout_sum_eq_zero_iff
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (μ : ι → ℝ) (y : M) (qs : ι → M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hpt : ∀ i, diagExpInv (I := I) g hEnorm p (y, qs i)
      = (⟨y, (show TangentSpace I y from
          (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E))⟩ : TangentBundle I M)) :
    (∑ i, μ i • (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p (y, qs i))).2) = 0
      ↔ (∑ i, μ i • (NormalCoordinates.normalChartAt (I := I) g y (qs i) : E)) = 0 := by
  rw [readout_sum_eq_clm (I := I) g hEnorm p μ y qs hy hpt]
  exact (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy |>.map_eq_zero_iff

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





omit [T3Space M] in
omit [ConnectedSpace M] in
theorem chartCmEqn'_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))) :
    ContDiffAt ℝ 1
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2) (z₀, params₀) := by
  unfold chartCmEqn'
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.smul
  · fun_prop
  · rw [← contMDiffAt_iff_contDiffAt]
    have hfst : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) 1
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.1) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hproj : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) 1
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.2.2 i) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hinner : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) (I.prod I) 1
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.normalChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.normalChartAt (I := I) g p).symm (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.prodMk (ContMDiffAt.comp (z₀, params₀) hchz hfst)
        (ContMDiffAt.comp (z₀, params₀) (hchξ i) hproj)
    have hcomp := (hsm i).comp (z₀, params₀) hinner
    exact hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in




omit [T3Space M] in
omit [ConnectedSpace M] in
theorem chartCmEqn'_contDiffAt_order
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i))) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
      (z₀, params₀) := by
  unfold chartCmEqn'
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.smul
  · fun_prop
  · rw [← contMDiffAt_iff_contDiffAt]
    have hfst : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) (n : ℕ∞)
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.1) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hproj : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) 𝓘(ℝ, E) (n : ℕ∞)
        (fun w : E × ((ι → ℝ) × (ι → E)) => w.2.2 i) (z₀, params₀) := by
      rw [contMDiffAt_iff_contDiffAt]; fun_prop
    have hinner : ContMDiffAt 𝓘(ℝ, E × ((ι → ℝ) × (ι → E))) (I.prod I) (n : ℕ∞)
        (fun w : E × ((ι → ℝ) × (ι → E)) =>
          ((NormalCoordinates.normalChartAt (I := I) g p).symm w.1,
            (NormalCoordinates.normalChartAt (I := I) g p).symm (w.2.2 i))) (z₀, params₀) :=
      ContMDiffAt.prodMk (ContMDiffAt.comp (z₀, params₀) hchz hfst)
        (ContMDiffAt.comp (z₀, params₀) (hchξ i) hproj)
    have hcomp := (hsm i).comp (z₀, params₀) hinner
    exact hcomp

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in








omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readoutSol_hasStrictFDerivAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0) :
    ∃ (f : ((ι → ℝ) × (ι → E)) → E) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E),
      f params₀ = z₀ ∧ HasStrictFDerivAt f Df params₀ ∧
        (∀ᶠ params in nhds params₀, chartCmEqn' (I := I) g hEnorm p (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqn' (I := I) g hEnorm p zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint' : HasStrictFDerivAt
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2)
        (z₀, params₀)) (z₀, params₀) :=
    (chartCmEqn'_contDiffAt (I := I) g hEnorm p z₀ params₀ hchz hchξ hsm).hasStrictFDerivAt
      one_ne_zero
  exact implicitSol_hasStrictFDerivAt
    (fun z params => chartCmEqn' (I := I) g hEnorm p z params) z₀ params₀ _ hjoint' hinv' hz₀'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [T3Space M] in
omit [ConnectedSpace M] in
theorem readoutSol_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0) :
    ∃ f : ((ι → ℝ) × (ι → E)) → E,
      f params₀ = z₀ ∧ ContDiffAt ℝ (n : ℕ∞) f params₀ ∧
        (∀ᶠ params in nhds params₀, chartCmEqn' (I := I) g hEnorm p (f params) params = 0) ∧
        (∀ᶠ zp in nhds (z₀, params₀),
          chartCmEqn' (I := I) g hEnorm p zp.1 zp.2 = 0 → zp.1 = f zp.2) := by
  have hjoint_cd : ContDiffAt ℝ (n : ℕ∞)
      (fun w : E × ((ι → ℝ) × (ι → E)) => chartCmEqn' (I := I) g hEnorm p w.1 w.2) (z₀, params₀) :=
    chartCmEqn'_contDiffAt_order (I := I) g hEnorm p z₀ params₀ n hchz hchξ hsm
  exact implicitSol_contDiffAt
    (fun z params => chartCmEqn' (I := I) g hEnorm p z params) z₀ params₀ n hn hjoint_cd hinv' hz₀'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem centerB_hasStrict
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqnB (I := I) g hEnorm p B
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ∃ Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E,
      HasStrictFDerivAt
        (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df params₀ := by
  obtain ⟨f, Df, hf0, hfderiv, hsolves, huniq⟩ :=
    readoutSolB_strict (I := I) g hEnorm p B z₀ params₀ hchz hchξ hsm hinv hzero
  refine ⟨Df, ?_⟩
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfderiv.congr_of_eventuallyEq hid.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [T3Space M] in
omit [ConnectedSpace M] in
theorem centerB_contDiff
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : DiagInvBranch (I := I) g hEnorm p)
    {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => B.diagReadout yq)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqnB (I := I) g hEnorm p B z params₀)
        (L : E →L[ℝ] E) z₀)
    (hzero : chartCmEqnB (I := I) g hEnorm p B z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqnB (I := I) g hEnorm p B
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀ := by
  obtain ⟨f, hf0, hfcd, hsolves, huniq⟩ :=
    readoutSolB_cdAt (I := I) g hEnorm p B z₀ params₀ n hn hchz hchξ hsm hinv hzero
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfcd.congr_of_eventuallyEq hid

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in









omit [T3Space M] in
omit [ConnectedSpace M] in
theorem center_hasStrictFDerivAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ∃ Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E,
      HasStrictFDerivAt
        (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df params₀ := by
  obtain ⟨f, Df, hf0, hfderiv, hsolves, huniq⟩ :=
    readoutSol_hasStrictFDerivAt (I := I) g hEnorm p z₀ params₀ hchz hchξ hsm hinv' hz₀'
  refine ⟨Df, ?_⟩
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfderiv.congr_of_eventuallyEq hid.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in






omit [T3Space M] in
omit [ConnectedSpace M] in
theorem center_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ) (hn : 1 ≤ n)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (c : ((ι → ℝ) × (ι → E)) → M)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      (nhds params₀) (nhds z₀)) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀ := by
  obtain ⟨f, hf0, hfcd, hsolves, huniq⟩ :=
    readoutSol_contDiffAt (I := I) g hEnorm p z₀ params₀ n hn hchz hchξ hsm hinv' hz₀'
  have huniq' := (hc_cont.prodMk_nhds Filter.tendsto_id).eventually huniq
  have hid : (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E))
      =ᶠ[nhds params₀] f := by
    filter_upwards [huniq', hc_solves] with params hu hs
    exact hu hs
  exact hfcd.congr_of_eventuallyEq hid

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


















theorem centerOfMass_hasStrictFDerivAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (join : M → M → ℝ → M) (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) join p r)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I 1
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I 1
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) 1
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
            join p r (H params))) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E))
      (nhds params₀) (nhds z₀)) :
    ∃ Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E,
      HasStrictFDerivAt
        (fun params => (NormalCoordinates.normalChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
            join p r (H params)) : E)) Df params₀ :=
  center_hasStrictFDerivAt (I := I) g hEnorm p z₀ params₀ hchz hchξ hsm hinv' hz₀'
    (fun params => centerOfMass (I := I) g params.1
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) join p r (H params))
    hc_solves hc_cont

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in





theorem centerOfMass_contDiffAt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) (n : ℕ) (hn : 1 ≤ n)
    (join : M → M → ℝ → M) (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) join p r)
    (hchz : ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun z : E => (NormalCoordinates.normalChartAt (I := I) g p).symm z) z₀)
    (hchξ : ∀ i, ContMDiffAt 𝓘(ℝ, E) I (n : ℕ∞)
      (fun ξ : E => (NormalCoordinates.normalChartAt (I := I) g p).symm ξ) (params₀.2 i))
    (hsm : ∀ i, ContMDiffAt (I.prod I) 𝓘(ℝ, E) (n : ℕ∞)
      (fun yq : M × M => (trivializationAt E (TangentSpace I) p
        (diagExpInv (I := I) g hEnorm p yq)).2)
      ((NormalCoordinates.normalChartAt (I := I) g p).symm z₀,
        (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)))
    (hinv' : ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => chartCmEqn' (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀)
    (hz₀' : chartCmEqn' (I := I) g hEnorm p z₀ params₀ = 0)
    (hc_solves : ∀ᶠ params in nhds params₀,
      chartCmEqn' (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p
          (centerOfMass (I := I) g params.1
            (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
            join p r (H params))) params = 0)
    (hc_cont : Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E))
      (nhds params₀) (nhds z₀)) :
    ContDiffAt ℝ (n : ℕ∞)
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
          join p r (H params)) : E)) params₀ :=
  center_contDiffAt (I := I) g hEnorm p z₀ params₀ n hn hchz hchξ hsm hinv' hz₀'
    (fun params => centerOfMass (I := I) g params.1
      (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) join p r (H params))
    hc_solves hc_cont

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in







omit [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] in
theorem centerOfMassChart_cont
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (p : M) {ι : Type} [Fintype ι] (params₀ : (ι → ℝ) × (ι → E))
    (join : M → M → ℝ → M) (r : ℝ)
    (H : ∀ params : (ι → ℝ) × (ι → E),
      CenterInput (I := I) g params.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) join p r)
    (hpts : Continuous (fun params : (ι → ℝ) × (ι → E) =>
      fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)))
    (hsrc : centerOfMass (I := I) g params₀.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)) join p r
        (H params₀) ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) :
    Filter.Tendsto
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i)) join p r
          (H params)) : E))
      (nhds params₀)
      (nhds (NormalCoordinates.normalChartAt (I := I) g p
        (centerOfMass (I := I) g params₀.1
          (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)) join p r
          (H params₀)))) := by
  have hcm := centerOfMass_cont (I := I) g (fun params : (ι → ℝ) × (ι → E) => params.1)
    (fun params => fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params.2 i))
    join p r params₀ H continuous_fst hpts
  have hchart : ContinuousAt (fun q : M => (NormalCoordinates.normalChartAt (I := I) g p q : E))
      (centerOfMass (I := I) g params₀.1
        (fun i => (NormalCoordinates.normalChartAt (I := I) g p).symm (params₀.2 i)) join p r
        (H params₀)) :=
    (NormalCoordinates.normalChartAt_contMDiffOn (I := I) g p).continuousOn.continuousAt
      ((NormalCoordinates.normalChartAt (I := I) g p).open_source.mem_nhds hsrc)
  exact hchart.tendsto.comp hcm

end DiagExpIdentification

end HCGCompactness
end DifferentialGeometry
