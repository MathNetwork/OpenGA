import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryComp
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsometryCompHigher
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiRestrictOpen
import DifferentialGeometry.Tensor.RSTensor.Coordinates.OpensRestrict
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility

set_option autoImplicit false
set_option linter.style.longLine false














noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

set_option synthInstance.maxHeartbeats 200000 in








omit [CompleteSpace E] in
theorem exists_pullbackField
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ Φ.source)
    (h : SmoothRiemannianMetric I N) (gM : SmoothRiemannianMetric I M) :
    ∃ (P : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2) (G : SmoothRiemannianMetric I M),
      P = Tensor0SBundle.metricTensorField (I := I) G ∧
      (∀ x ∈ K, ∀ v w : TangentSpace I x,
        G.inner x v w = h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w)) ∧
      ∀ x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
        P x v = h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x (v 0)) (mfderiv I I (Φ : M → N) x (v 1)) := by
  classical
  obtain ⟨χ, P₀, hP₀smooth, hχ, hχK, hχsupp, hχ01, hP₀def⟩ :=
    exists_pullbackInner (I := I) Φ hK hKs h

  set G : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
    P₀ x + (1 - χ x) • gM.inner x with hG
  have hGapply : ∀ (x : M) (v w : TangentSpace I x),
      G x v w = χ x * (h.inner ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w))
        + (1 - χ x) * gM.inner x v w := by
    intro x v w
    simp only [hG, hP₀def x, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply, smul_eq_mul]
  have hGpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < G x v v := by
    intro x v hv
    rw [hGapply]
    have ha : 0 ≤ χ x := (hχ01 x).1
    have hb : 0 ≤ 1 - χ x := by linarith [(hχ01 x).2]
    have hgM := gM.pos x v hv
    rcases lt_or_eq_of_le ha with ha' | ha'
    · have hxs : x ∈ Φ.source :=
        hχsupp (subset_tsupport χ (Function.mem_support.mpr (ne_of_gt ha')))
      have hpull := pullInner_pos (I := I) Φ hxs h v hv
      nlinarith
    · rw [← ha']
      simpa using hgM
  set Gmetric : SmoothRiemannianMetric I M :=
    { inner := G
      symm := by
        intro x v w
        rw [hGapply, hGapply, gM.symm x v w, h.symm]
      pos := hGpos
      isVonNBounded := fun x =>
        DifferentialGeometry.Geometry.posDef_isVonNBounded (E := E)
          ((G x : E →L[ℝ] E →L[ℝ] ℝ)) (fun v hv => hGpos x v hv)
      contMDiff := by
        have hgM' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (∞ : WithTop ℕ∞)
            (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
              x ((1 - χ x) • gM.inner x)) := by
          have hcoef : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) (fun x : M => 1 - χ x) :=
            contMDiff_const.sub hχ
          exact fun x₀ => (hcoef.contMDiffAt).smul_section (gM.contMDiff x₀)
        exact fun x₀ => (hP₀smooth x₀).add_section (hgM' x₀) }
    with hGmetric
  have hGinner : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      Gmetric.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) := by
    intro x hx v w
    show G x v w = _
    rw [hGapply, hχK hx]
    simp
  refine ⟨Tensor0SBundle.metricTensorField (I := I) Gmetric, Gmetric, rfl, hGinner, ?_⟩
  intro x hx v
  rw [Tensor0SBundle.metricTensorField_apply]
  exact hGinner x hx (v 0) (v 1)

section CodRestrict

omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in




omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem contMDiffAt_codRestr {N' : Type u} [TopologicalSpace N'] [ChartedSpace H N']
    {V' : TopologicalSpace.Opens N'} {f : M → N'}
    (hmem : ∀ y, f y ∈ V') {x : M}
    (hf : ContMDiffAt I I (∞ : WithTop ℕ∞) f x) :
    ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y => (⟨f y, hmem y⟩ : V')) x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hcont, hdiff⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (by simpa [Function.comp_def] using hcont), ?_⟩
  convert hdiff using 2

end CodRestrict

section OpensDiffeo

open TopologicalSpace Topology



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [IsManifold I ∞ N] in
theorem image_opens_isOpen (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {V : Opens M} (hV : (V : Set M) ⊆ Φ.source) :
    IsOpen ((Φ : M → N) '' (V : Set M)) := by
  have himg : (Φ : M → N) '' (V : Set M)
      = Φ.target ∩ ((Φ.symm : N → M) ⁻¹' (V : Set M)) := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨Φ.map_source' (hV hv), ?_⟩
      have hl : (Φ.symm : N → M) ((Φ : M → N) v) = v := Φ.left_inv' (hV hv)
      show (Φ.symm : N → M) ((Φ : M → N) v) ∈ (V : Set M)
      rw [hl]
      exact hv
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Φ.symm : N → M) y, hy2, Φ.right_inv' hy1⟩
  rw [himg]
  exact Φ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_target V.2





noncomputable def PartialDiffeomorph.toOpensDiffeo
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {V : Opens M} (hV : (V : Set M) ⊆ Φ.source) :
    Diffeomorph I I V (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N)
      (∞ : WithTop ℕ∞) where
  toFun p := ⟨(Φ : M → N) p.1, ⟨p.1, p.2, rfl⟩⟩
  invFun q := ⟨(Φ.symm : N → M) q.1, by
    obtain ⟨v, hv, hveq⟩ := q.2
    rw [← hveq]
    have hl : (Φ.symm : N → M) ((Φ : M → N) v) = v := Φ.left_inv' (hV hv)
    show (Φ.symm : N → M) ((Φ : M → N) v) ∈ V
    rw [hl]
    exact hv⟩
  left_inv p := by
    apply Subtype.ext
    exact Φ.left_inv' (hV p.2)
  right_inv q := by
    apply Subtype.ext
    obtain ⟨v, hv, hveq⟩ := q.2
    have hyt : (q : N) ∈ Φ.target := by
      rw [← hveq]; exact Φ.map_source' (hV hv)
    exact Φ.right_inv' hyt
  contMDiff_toFun := by
    intro p
    have hbase : ContMDiffAt I I (∞ : WithTop ℕ∞) (fun p : V => (Φ : M → N) p.1) p := by
      rw [contMDiffAt_subtype_iff]
      exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hV p.2))
    exact contMDiffAt_codRestr
      (V' := (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N))
      (f := fun p : V => (Φ : M → N) p.1)
      (fun y => ⟨y.1, y.2, rfl⟩) hbase
  contMDiff_invFun := by
    intro q
    have hmem : ∀ y : (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N),
        (Φ.symm : N → M) y.1 ∈ V := by
      intro y
      obtain ⟨v, hv, hveq⟩ := y.2
      rw [← hveq]
      have hl : (Φ.symm : N → M) ((Φ : M → N) v) = v := Φ.left_inv' (hV hv)
      show (Φ.symm : N → M) ((Φ : M → N) v) ∈ V
      rw [hl]
      exact hv
    have hbase : ContMDiffAt I I (∞ : WithTop ℕ∞)
        (fun y : (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N) =>
          (Φ.symm : N → M) y.1) q := by
      rw [contMDiffAt_subtype_iff]
      obtain ⟨v, hv, hveq⟩ := q.2
      have hqt : (q : N) ∈ Φ.target := by
        rw [← hveq]; exact Φ.map_source' (hV hv)
      exact Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hqt)
    exact contMDiffAt_codRestr hmem hbase



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensDiffeo_mfderiv
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} (hU : (U : Set M) ⊆ Φ.source) (p : U) (v : TangentSpace I p) :
    mfderiv I I
        (PartialDiffeomorph.toOpensDiffeo Φ hU : U →
          (⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩ : Opens N)) p v
      = mfderiv I I (Φ : M → N) (p : M) v := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hFd : MDifferentiableAt I I (F : U → W) p :=
    F.contMDiff.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalW : MDifferentiableAt I I (Subtype.val : W → N) (F p) :=
    ((contMDiff_subtype_val (I := I) (U := W)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalU : MDifferentiableAt I I (Subtype.val : U → M) p :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦd : MDifferentiableAt I I (Φ : M → N) (p : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU p.2))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h1 : mfderiv I I (fun y : U => ((F y : W) : N)) p
      = (mfderiv I I (Subtype.val : W → N) (F p)).comp
          (mfderiv I I (F : U → W) p) :=
    mfderiv_comp p hvalW hFd
  have h2 : mfderiv I I (fun y : U => (Φ : M → N) (y : M)) p
      = (mfderiv I I (Φ : M → N) (p : M)).comp
          (mfderiv I I (Subtype.val : U → M) p) :=
    mfderiv_comp p hΦd hvalU
  have happ := DFunLike.congr_fun (h1.symm.trans h2) v
  simpa only [F, ContinuousLinearMap.comp_apply,
    mfderiv_subtype_val (I := I) W (F p), mfderiv_subtype_val (I := I) U p] using happ



noncomputable def PartialDiffeomorph.opensMap
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (_hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) : U → V :=
  fun x => ⟨(Φ : M → N) x, hUV ⟨x, x.2, rfl⟩⟩


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_isOpenEmb
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    IsOpenEmbedding (PartialDiffeomorph.opensMap Φ hU hUV) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  have hWV : W ≤ V := hUV
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hinc : IsOpenEmbedding (Opens.inclusion hWV : W → V) :=
    Opens.isOpenEmbedding_of_le hWV
  have hfun : PartialDiffeomorph.opensMap Φ hU hUV =
      (Opens.inclusion hWV : W → V) ∘ F := rfl
  rw [hfun]
  exact hinc.comp F.toHomeomorph.isOpenEmbedding


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_contMDiff
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    ContMDiff I I ∞ (PartialDiffeomorph.opensMap Φ hU hUV) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  have hWV : W ≤ V := hUV
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hfun : PartialDiffeomorph.opensMap Φ hU hUV =
      (Opens.inclusion hWV : W → V) ∘ F := rfl
  rw [hfun]
  exact (contMDiff_inclusion hWV).comp F.contMDiff



omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_mfderiv
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N))
    (p : U) (v : TangentSpace I p) :
    mfderiv I I (PartialDiffeomorph.opensMap Φ hU hUV) p v =
      mfderiv I I (Φ : M → N) (p : M) v := by
  let F : U → V := PartialDiffeomorph.opensMap Φ hU hUV
  have hFd : MDifferentiableAt I I F p :=
    ((PartialDiffeomorph.opensMap_contMDiff Φ hU hUV).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalV : MDifferentiableAt I I (Subtype.val : V → N) (F p) :=
    ((contMDiff_subtype_val (I := I) (U := V)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalU : MDifferentiableAt I I (Subtype.val : U → M) p :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hΦd : MDifferentiableAt I I (Φ : M → N) (p : M) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU p.2))).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have h1 : mfderiv I I (fun y : U => ((F y : V) : N)) p =
      (mfderiv I I (Subtype.val : V → N) (F p)).comp (mfderiv I I F p) :=
    mfderiv_comp p hvalV hFd
  have h2 : mfderiv I I (fun y : U => (Φ : M → N) (y : M)) p =
      (mfderiv I I (Φ : M → N) (p : M)).comp
        (mfderiv I I (Subtype.val : U → M) p) :=
    mfderiv_comp p hΦd hvalU
  have happ := DFunLike.congr_fun (h1.symm.trans h2) v
  simpa only [F, ContinuousLinearMap.comp_apply,
    mfderiv_subtype_val (I := I) V (F p), mfderiv_subtype_val (I := I) U p] using happ


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [IsManifold I ∞ N] in
theorem PartialDiffeomorph.opensMap_inv_mdiff
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {U : Opens M} {V : Opens N} [Nonempty U] (hU : (U : Set M) ⊆ Φ.source)
    (hUV : (Φ : M → N) '' (U : Set M) ⊆ (V : Set N)) :
    ContMDiffOn I I ∞ (Function.invFun (PartialDiffeomorph.opensMap Φ hU hUV))
      (Set.range (PartialDiffeomorph.opensMap Φ hU hUV)) := by
  let W : Opens N := ⟨(Φ : M → N) '' (U : Set M), image_opens_isOpen Φ hU⟩
  letI : Nonempty W := by
    obtain ⟨x⟩ := (inferInstance : Nonempty U)
    exact ⟨⟨(Φ : M → N) x, ⟨x, x.2, rfl⟩⟩⟩
  have hWV : W ≤ V := hUV
  let inc : W → V := Opens.inclusion hWV
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  have hinc : IsOpenEmbedding inc := by
    exact Opens.isOpenEmbedding_of_le hWV
  have htotal : Function.Injective (inc ∘ F) := hinc.injective.comp F.injective
  have hinvInc : ContMDiffOn I I ∞ (Function.invFun inc) (Set.range inc) := by
    intro y hy
    have hamb : ContMDiffAt I I ∞
        (fun z : V => ((Function.invFun inc z : W) : N)) y := by
      refine ((contMDiff_subtype_val (I := I) (U := V)).contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [hinc.isOpen_range.mem_nhds hy] with z hz
      obtain ⟨w, rfl⟩ := hz
      exact congrArg Subtype.val (Function.leftInverse_invFun hinc.injective w)
    exact (contMDiffAt_codRestr (fun z => (Function.invFun inc z).2) hamb).contMDiffWithinAt
  have hfun : PartialDiffeomorph.opensMap Φ hU hUV = inc ∘ F := rfl
  rw [hfun]
  have hsub : Set.range (inc ∘ F) ⊆ Set.range inc := by
    rintro y ⟨x, rfl⟩
    exact ⟨F x, rfl⟩
  have hFsmooth : ContMDiffOn I I ∞ F.symm (Set.univ : Set W) :=
    F.symm.contMDiff.contMDiffOn
  have hsmooth : ContMDiffOn I I ∞ (F.symm ∘ Function.invFun inc)
      (Set.range (inc ∘ F)) :=
    hFsmooth.comp (hinvInc.mono hsub) (fun _ _ => Set.mem_univ _)
  refine hsmooth.congr (fun y hy => ?_)
  obtain ⟨x, rfl⟩ := hy
  simp only [Function.comp_apply]
  rw [Function.leftInverse_invFun hinc.injective, F.symm_apply_apply]
  change Function.invFun (inc ∘ F) ((inc ∘ F) x) = x
  exact Function.leftInverse_invFun htotal x



omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem invSubtype_mdiff (U : Opens N) [Nonempty U] :
    ContMDiffOn I I ∞ (Function.invFun (Subtype.val : U → N))
      (Set.range (Subtype.val : U → N)) := by
  intro y hy
  have hamb : ContMDiffAt I I ∞
      (fun z : N => ((Function.invFun (Subtype.val : U → N) z : U) : N)) y := by
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [U.isOpenEmbedding'.isOpen_range.mem_nhds hy] with z hz
    obtain ⟨u, rfl⟩ := hz
    exact congrArg Subtype.val
      (Function.leftInverse_invFun U.isOpenEmbedding'.injective u)
  exact (contMDiffAt_codRestr
    (fun z => (Function.invFun (Subtype.val : U → N) z).2) hamb).contMDiffWithinAt




noncomputable def PartialDiffeomorph.liftTargetOpen
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    PartialDiffeomorph I I M N (∞ : WithTop ℕ∞) where
  toFun := fun x => (Φ x : N)
  invFun := fun y => Φ.toPartialEquiv.invFun
    (Function.invFun (Subtype.val : U → N) y)
  source := Φ.source
  target := U
  map_source' := fun x hx => (Φ x).2
  map_target' := by
    intro y hy
    let u : U := ⟨y, hy⟩
    have hinv : Function.invFun (Subtype.val : U → N) y = u := by
      exact Function.leftInverse_invFun U.isOpenEmbedding'.injective u
    rw [hinv]
    exact Φ.map_target' (htarget.symm ▸ Set.mem_univ u)
  left_inv' := by
    intro x hx
    rw [Function.leftInverse_invFun U.isOpenEmbedding'.injective]
    exact Φ.left_inv' hx
  right_inv' := by
    intro y hy
    let u : U := ⟨y, hy⟩
    have hinv : Function.invFun (Subtype.val : U → N) y = u := by
      exact Function.leftInverse_invFun U.isOpenEmbedding'.injective u
    change ((Φ (Φ.toPartialEquiv.invFun
      (Function.invFun (Subtype.val : U → N) y)) : U) : N) = y
    rw [hinv, Φ.right_inv' (htarget.symm ▸ Set.mem_univ u)]
  open_source := Φ.open_source
  open_target := U.isOpen
  contMDiffOn_toFun := by
    intro x hx
    exact ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt.comp x
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds hx))).contMDiffWithinAt
  contMDiffOn_invFun := by
    intro y hy
    let u : U := ⟨y, hy⟩
    have hyrange : y ∈ Set.range (Subtype.val : U → N) := ⟨u, rfl⟩
    have hinvAt : ContMDiffAt I I ∞
        (Function.invFun (Subtype.val : U → N)) y :=
      (invSubtype_mdiff (I := I) U).contMDiffAt
        (U.isOpenEmbedding'.isOpen_range.mem_nhds hyrange)
    have hinv : Function.invFun (Subtype.val : U → N) y = u := by
      exact Function.leftInverse_invFun U.isOpenEmbedding'.injective u
    have hΦAt : ContMDiffAt I I ∞ Φ.toPartialEquiv.invFun
        (Function.invFun (Subtype.val : U → N) y) := by
      rw [hinv]
      exact Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (htarget.symm ▸ Set.mem_univ u))
    exact (hΦAt.comp y hinvAt).contMDiffWithinAt


omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem PartialDiffeomorph.liftOpen_source
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    (PartialDiffeomorph.liftTargetOpen Φ htarget).source = Φ.source := rfl


omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem PartialDiffeomorph.liftOpen_target
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) :
    (PartialDiffeomorph.liftTargetOpen Φ htarget).target = (U : Set N) := rfl


omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem PartialDiffeomorph.liftOpen_apply
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) (x : M) :
    PartialDiffeomorph.liftTargetOpen Φ htarget x = (Φ x : N) := rfl



omit [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
omit [IsManifold I ∞ N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem PartialDiffeomorph.liftOpen_mfderiv
    {U : Opens N} [Nonempty U] (Φ : PartialDiffeomorph I I M U (∞ : WithTop ℕ∞))
    (htarget : Φ.target = Set.univ) {x : M} (hx : x ∈ Φ.source)
    (v : TangentSpace I x) :
    mfderiv I I (PartialDiffeomorph.liftTargetOpen Φ htarget : M → N) x v =
      mfderiv I I (Φ : M → U) x v := by
  have hΦd : MDifferentiableAt I I (Φ : M → U) x :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds hx)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I (Subtype.val : U → N) (Φ x) :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hΦd
  have happ := DFunLike.congr_fun hcomp v
  change mfderiv I I (fun y : M => ((Φ y : U) : N)) x v = _
  simpa only [ContinuousLinearMap.comp_apply,
    mfderiv_subtype_val (I := I) U (Φ x)] using happ

end OpensDiffeo



section PartialCovNaturality

open TopologicalSpace




omit [SigmaCompactSpace M] in
theorem tensor02_eq_covDOF
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) :
    ∀ a : ℕ, tensor02CovDeriv (I := I) A gRef a = covDerivOfField (I := I) gRef A a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
      show metricCovDerivStep (I := I) gRef a (tensor02CovDeriv (I := I) A gRef a)
        = covDerivOfField (I := I) gRef A (a + 1)
      rw [ih, covDerivOfField_succ]




omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem srm_ext {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] {g g' : SmoothRiemannianMetric I M'}
    (h : ∀ (x : M') (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) : g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl












omit [SigmaCompactSpace M] in
theorem covNormWith_pd_zone [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [T2Space N] [SigmaCompactSpace N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {V : Opens M} [Nonempty V]
    [SigmaCompactSpace V]
    (hV : (V : Set M) ⊆ Φ.source)
    [SigmaCompactSpace
      (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N)]
    (g' : SmoothRiemannianMetric I N)
    (δN : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2)
    (δM : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (G : SmoothRiemannianMetric I M)
    (hδ : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      δM x v = δN ((Φ : M → N) x)
        (fun q => mfderiv I I (Φ : M → N) x (v q)))
    (hG : ∀ x ∈ (V : Set M), ∀ v w : TangentSpace I x,
      G.inner x v w = g'.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w))
    (a : ℕ) (x : M) (hx : x ∈ (V : Set M)) :
    tensor02CovDerivNormWith (I := I) a δM G G x
      = tensor02CovDerivNormWith (I := I) a δN g' g' ((Φ : M → N) x) := by
  classical
  set W : Opens N := ⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ with hWdef
  haveI : Nonempty W := ⟨⟨(Φ : M → N) x, x, hx, rfl⟩⟩
  set F := PartialDiffeomorph.toOpensDiffeo Φ hV with hFdef
  set xV : V := ⟨x, hx⟩ with hxVdef

  have hmfd : ∀ (p : V) (v : TangentSpace I p),
      mfderiv I I (F : V → W) p v = mfderiv I I (Φ : M → N) (p : M) v := by
    intro p v
    have hFd : MDifferentiableAt I I (F : V → W) p :=
      F.contMDiff.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hvalW : MDifferentiableAt I I (Subtype.val : W → N) (F p) :=
      ((contMDiff_subtype_val (I := I) (U := W)).contMDiffAt).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hvalV : MDifferentiableAt I I (Subtype.val : V → M) p :=
      ((contMDiff_subtype_val (I := I) (U := V)).contMDiffAt).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦd : MDifferentiableAt I I (Φ : M → N) (p : M) :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hV p.2))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have h1 : mfderiv I I (fun y : V => ((F y : W) : N)) p
        = (mfderiv I I (Subtype.val : W → N) (F p)).comp
            (mfderiv I I (F : V → W) p) :=
      mfderiv_comp p hvalW hFd
    have h2 : mfderiv I I (fun y : V => (Φ : M → N) (y : M)) p
        = (mfderiv I I (Φ : M → N) (p : M)).comp
            (mfderiv I I (Subtype.val : V → M) p) :=
      mfderiv_comp p hΦd hvalV
    have happ := DFunLike.congr_fun (h1.symm.trans h2) v
    simpa [ContinuousLinearMap.comp_apply,
      mfderiv_subtype_val (I := I) W (F p),
      mfderiv_subtype_val (I := I) V p] using happ

  set δMV := restrictOpen0S (I := I) 2 (V := V) δM with hδMVdef
  set δNW := restrictOpen0S (I := I) 2 (V := W) δN with hδNWdef
  have hδMV_apply : ∀ (p : V) (slots : Fin 2 → TangentSpace I p),
      δMV p slots = δM (p : M) slots := fun _ _ => rfl
  have hδNW_apply : ∀ (q : W) (slots : Fin 2 → TangentSpace I q),
      δNW q slots = δN (q : N) slots := fun _ _ => rfl

  have hswap : G.restrictOpen (I := I) V
      = Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F := by
    apply srm_ext
    intro p v w
    have hL : (G.restrictOpen (I := I) V).inner p v w = G.inner (p : M) v w := rfl
    have hR : (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F).inner p v w
        = g'.inner ((F p : W) : N)
            (mfderiv I I (F : V → W) p v) (mfderiv I I (F : V → W) p w) := by
      rw [Diffeomorph.pullbackMetric_inner]
      rfl
    rw [hL, hR, hmfd, hmfd]
    exact hG (p : M) p.2 v w

  have hA0 : ∀ (p : V) (slots : Fin 2 → TangentSpace I p),
      δMV p slots = δNW (F p) (fun q => mfderiv I I (F : V → W) p (slots q)) := by
    intro p slots
    rw [hδMV_apply, hδNW_apply, hδ (p : M) p.2]
    show δN ((Φ : M → N) (p : M)) _ = δN ((F p : W) : N) _
    congr 1
    funext q
    rw [hmfd]

  have hres1 := covDerivOfField_restrictOpen (I := I) G V δMV δM hδMV_apply a xV

  have hpull := covDerivOfField_pullback (I := I) (g'.restrictOpen (I := I) W) F δMV δNW
    hA0 a xV

  have hres2 := covDerivOfField_restrictOpen (I := I) g' W δNW δN hδNW_apply a (F xV)

  have htensor1 : ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) G δM a x slots
        = covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
            (g'.restrictOpen (I := I) W) F) δMV a xV slots := by
    intro slots
    rw [← hswap]
    exact (hres1 slots).symm
  have htensor2 : ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
          (g'.restrictOpen (I := I) W) F) δMV a xV slots
        = covDerivOfField (I := I) g' δN a ((Φ : M → N) x)
            (fun q => mfderiv I I (F : V → W) xV (slots q)) := by
    intro slots
    rw [hpull]
    have := hres2 (fun q => mfderiv I I (F : V → W) xV (slots q))
    convert this using 2

  have hT1 : covDerivOfField (I := I) G δM a x
      = covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
          (g'.restrictOpen (I := I) W) F) δMV a xV :=
    ContinuousMultilinearMap.ext htensor1
  have hT2 : covDerivOfField (I := I) g' δN a ((Φ : M → N) x)
      = covDerivOfField (I := I) (g'.restrictOpen (I := I) W) δNW a (F xV) :=
    (ContinuousMultilinearMap.ext hres2).symm

  unfold tensor02CovDerivNormWith
  rw [tensor02_eq_covDOF, tensor02_eq_covDOF]
  obtain ⟨basis, hONb⟩ := DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I)
    (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F) xV
  have hnorm1 : Tensor0SBundle.normSq0S (I := I) G x (a + 2)
        (covDerivOfField (I := I) G δM a x)
      = Tensor0SBundle.normSq0S (I := I)
          (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F) xV (a + 2)
          (covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
            (g'.restrictOpen (I := I) W) F) δMV a xV) := by
    rw [hT1, ← hswap]
    exact (normSq0S_restrictOpen_apply (I := I) G V (a + 2) xV _).symm
  have hnorm2 : Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F) xV (a + 2)
        (covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
          (g'.restrictOpen (I := I) W) F) δMV a xV)
      = Tensor0SBundle.normSq0S (I := I) (g'.restrictOpen (I := I) W) (F xV) (a + 2)
          (covDerivOfField (I := I) (g'.restrictOpen (I := I) W) δNW a (F xV)) :=
    normSq0S_pullback_eval_of_orthonormal (I := I) (g'.restrictOpen (I := I) W) F
      xV (a + 2) basis hONb _ _ (hpull)
  have hnorm3 : Tensor0SBundle.normSq0S (I := I) (g'.restrictOpen (I := I) W) (F xV) (a + 2)
        (covDerivOfField (I := I) (g'.restrictOpen (I := I) W) δNW a (F xV))
      = Tensor0SBundle.normSq0S (I := I) g' ((Φ : M → N) x) (a + 2)
          (covDerivOfField (I := I) g' δN a ((Φ : M → N) x)) := by
    rw [hT2]
    exact normSq0S_restrictOpen_apply (I := I) g' W (a + 2) (F xV) _
  rw [hnorm1, hnorm2, hnorm3]

end PartialCovNaturality

section PartialTrans




noncomputable def PartialDiffeomorph.trans {P : Type u} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞)) :
    PartialDiffeomorph I I M P (∞ : WithTop ℕ∞) where
  toPartialEquiv := Φ.toPartialEquiv.trans Φ'.toPartialEquiv
  open_source := by
    have hsrc : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).source
        = Φ.source ∩ (Φ : M → N) ⁻¹' Φ'.source := rfl
    rw [hsrc]
    exact Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source
      Φ'.open_source
  open_target := by
    have htgt : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).target
        = Φ'.target ∩ (Φ'.symm : P → N) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ'.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ'.open_target
      Φ.open_target
  contMDiffOn_toFun := by
    have hsrc : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).source
        = Φ.source ∩ (Φ : M → N) ⁻¹' Φ'.source := rfl
    rw [hsrc]
    exact Φ'.contMDiffOn_toFun.comp
      (Φ.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)
  contMDiffOn_invFun := by
    have htgt : (Φ.toPartialEquiv.trans Φ'.toPartialEquiv).target
        = Φ'.target ∩ (Φ'.symm : P → N) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ.symm.contMDiffOn_toFun.comp
      (Φ'.symm.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)

end PartialTrans

section TowerZero

set_option backward.isDefEq.respectTransparency false in

omit [SigmaCompactSpace M] in
theorem covStep_zero (gRef : SmoothRiemannianMetric I M) (s : Nat)
    [SigmaCompactSpace M] :
    covStep (I := I) gRef s
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
      = 0 := by
  have h := (covStep_add (I := I) gRef s 0 0).symm
  rw [add_zero] at h
  have h2 : covStep (I := I) gRef s 0 + covStep (I := I) gRef s 0
      = covStep (I := I) gRef s 0 + 0 := by rw [add_zero]; exact h
  exact add_left_cancel h2

set_option backward.isDefEq.respectTransparency false in





theorem iterCov_metric_zero (g : SmoothRiemannianMetric I M) (a : Nat) :
    iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) (a + 1) = 0 := by
  induction a with
  | zero =>
      refine DFunLike.ext _ _ (fun x => ?_)
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
        (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
      have hslots : slots = Fin.cons (X x) (Fin.tail slots) := by
        rw [hX]
        exact (Fin.cons_self_tail slots).symm
      rw [show iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) 1
          = covStep (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) from rfl]
      rw [covStep_apply, hslots,
        Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 _ X (Tensor0SBundle.metricTensorField (I := I) g) x _,
        Tensor0SBundle.nabla_metric_zero (I := I) _ g
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
            (I := I) g) X x]
      simp
  | succ a ih =>
      rw [show iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) (a + 1 + 1)
          = covStep (I := I) g (2 + (a + 1))
              (iterCov (I := I) g 2 (Tensor0SBundle.metricTensorField (I := I) g) (a + 1))
          from rfl]
      rw [ih, covStep_zero]

set_option backward.isDefEq.respectTransparency false in

omit [SigmaCompactSpace M] in
theorem iterCov_sub (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 B0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r (A0 - B0) a
      = iterCov (I := I) gRef r A0 a - iterCov (I := I) gRef r B0 a := by
  have h := iterCov_add (I := I) gRef r (A0 - B0) B0 a
  rw [sub_add_cancel] at h
  rw [h]
  abel

set_option backward.isDefEq.respectTransparency false in

omit [SigmaCompactSpace M] in
theorem covDOF_zero (gRef : SmoothRiemannianMetric I M) (a : Nat) :
    covDerivOfField (I := I) gRef
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) a
      = 0 := by
  have h := covDerivOfField_sub (I := I) gRef 0 0 a
  simpa using h

set_option backward.isDefEq.respectTransparency false in




omit [SigmaCompactSpace M] in
theorem t02Norm_eq_iterCov [I.Boundaryless] {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    tensor02CovDerivNormWith (I := I) a A gRef gRef x
      = Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + a)
          (iterCov (I := I) gRef 2 A a x)) := by
  unfold tensor02CovDerivNormWith
  rw [tensor02_eq_covDOF, covDerivOfField_eq_iterCov]
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (ContinuousMultilinearMap.domDomCongr (acEquiv a)
        (iterCov (I := I) gRef 2 A a x)))
    = Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + a)
        (iterCov (I := I) gRef 2 A a x))
  rw [Tensor0SBundle.normSq0S_domDomCongr (I := I) gRef x basis hinv (acEquiv a)
      (iterCov (I := I) gRef 2 A a x)]

end TowerZero

section C0Equiv






omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem inner_le_of_c0
    (Gm g : SmoothRiemannianMetric I M) {K : Set M} {ε : ℝ}
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) Gm) g x ≤ ε) :
    ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - ε) * g.inner x v v ≤ Gm.inner x v v ∧
        Gm.inner x v v ≤ (1 + ε) * g.inner x v v := by
  classical
  intro x hx v
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I)
    g x 2 basis (fun i j => hON i j)
    ((Tensor0SBundle.metricTensorField (I := I) Gm) x
      - Tensor0SBundle.metricTensorField (I := I) g x)
    (fun _ => v)
  have hval : ((Tensor0SBundle.metricTensorField (I := I) Gm) x
      - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)
      = Gm.inner x v v - g.inner x v v := by
    calc
      ((Tensor0SBundle.metricTensorField (I := I) Gm) x -
          Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v) =
          Tensor0SBundle.metricTensorField (I := I) Gm x (fun _ => v) -
            Tensor0SBundle.metricTensorField (I := I) g x (fun _ => v) :=
        Tensor0SBundle.Tensor0SSpace.sub_apply 2 x _ _ _
      _ = Gm.inner x v v - g.inner x v v := by
        rw [Tensor0SBundle.metricTensorField_apply,
          Tensor0SBundle.metricTensorField_apply]
  have hnn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · simp [hv]
    · exact le_of_lt (g.pos x v hv)
  have hprod : (∏ _a : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt hnn]
  have habs : |Gm.inner x v v - g.inner x v v| ≤ ε * g.inner x v v := by
    have herr := hc0 x hx
    calc |Gm.inner x v v - g.inner x v v|
        = |((Tensor0SBundle.metricTensorField (I := I) Gm) x
            - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)| := by rw [hval]
      _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
            ((Tensor0SBundle.metricTensorField (I := I) Gm) x
              - Tensor0SBundle.metricTensorField (I := I) g x))
            * ∏ _a : Fin 2, Real.sqrt (g.inner x v v) := hCS
      _ ≤ ε * g.inner x v v := by
          rw [hprod]
          exact mul_le_mul_of_nonneg_right herr hnn
  constructor
  · nlinarith [abs_le.mp habs]
  · nlinarith [abs_le.mp habs]

set_option backward.isDefEq.respectTransparency false in



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem sqrt_normSq_two_le
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K)
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 A) ≤
      Real.sqrt (C ^ 2) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 A) := by
  obtain ⟨μ, basis, hginv, hhinv, hμ_nonneg, hμ_le⟩ :=
    exists_diagInv_of_metricUniformEquivalentOn
      (I := I) (K := K) (g := g) (h := h) (C := C) hEq hx
  have hle :
      Tensor0SBundle.normSq0S (I := I) h x 2 A ≤
        C ^ 2 * Tensor0SBundle.normSq0S (I := I) g x 2 A := by
    simpa using
      Tensor0SBundle.normSq0S_diag_le
        (I := I) (g := g) (h := h) (x := x) (s := 2)
        basis μ C hginv hhinv hμ_nonneg hμ_le A
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 A)
      ≤ Real.sqrt (C ^ 2 * Tensor0SBundle.normSq0S (I := I) g x 2 A) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (C ^ 2) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 A) :=
        Real.sqrt_mul (by positivity) _

end C0Equiv

section PartialDataComp

open TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
















theorem partialData_comp [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {P : Type u} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    [T2Space N] [SigmaCompactSpace N] [T2Space P] [SigmaCompactSpace P]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [IsManifold I 1 P] [IsManifold I 2 P] [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {U₁ : Opens M} [Nonempty U₁] (hU₁ : (U₁ : Set M) ⊆ Φ.source)
    {K₂ : Opens N} [Nonempty K₂] (hK₂ : (K₂ : Set N) ⊆ Φ'.source)
    (himg : (Φ : M → N) '' (U₁ : Set M) ⊆ (K₂ : Set N))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U₁ : Set M))
    {ε ε' : ℝ} {p : ℕ} (hε2 : ε ≤ 1/2) (hε'2 : ε' ≤ 1/2)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
      [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
      [IsManifold I 1 M'] [IsManifold I 2 M']
      [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
      {u : Set M'}, IsOpen u →
      ∀ (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoPartialData (I := I) (U₁ : Set M) ε p Φ g h)
    (D₂ : BookApproxIsoPartialData (I := I) (K₂ : Set N) ε' p Φ' h h') :
    ∀ ε'' : ℝ,
      ε / (1 - ε) + ε' * max C 2 ≤ ε'' →
      ε' / (1 - ε') + ε * max C 2 ≤ ε'' →
      ε'' < 1 →
      Nonempty (BookApproxIsoPartialData (I := I) K ε'' p
        (PartialDiffeomorph.trans (I := I) Φ Φ') g h') := by
  classical
  set Ψ := PartialDiffeomorph.trans (I := I) Φ Φ' with hΨdef

  have hsrcU : (U₁ : Set M) ⊆ Ψ.source := by
    intro y hy
    exact ⟨hU₁ hy, hK₂ (himg (Set.mem_image_of_mem _ hy))⟩
  have hKsrc : K ⊆ Ψ.source := fun y hy => hsrcU (hKU hy)

  have hΨcoe : ∀ y : M, (Ψ : M → P) y = (Φ' : N → P) ((Φ : M → N) y) := fun _ => rfl

  have hchain : ∀ y ∈ (U₁ : Set M), ∀ v : TangentSpace I y,
      mfderiv I I (Ψ : M → P) y v
        = mfderiv I I (Φ' : N → P) ((Φ : M → N) y) (mfderiv I I (Φ : M → N) y v) := by
    intro y hy v
    have hΦd : MDifferentiableAt I I (Φ : M → N) y :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hU₁ hy))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦ'd : MDifferentiableAt I I (Φ' : N → P) ((Φ : M → N) y) :=
      (Φ'.contMDiffOn_toFun.contMDiffAt
        (Φ'.open_source.mem_nhds (hK₂ (himg (Set.mem_image_of_mem _ hy))))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have h := mfderiv_comp y hΦ'd hΦd
    have happ := DFunLike.congr_fun h v
    simpa [ContinuousLinearMap.comp_apply] using happ

  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨KG, hKGcpt, hKKG, hKGU⟩ := exists_compact_between hK U₁.2 hKU
  set V : Opens M := ⟨interior KG, isOpen_interior⟩ with hVdef
  have hKV : K ⊆ (V : Set M) := hKKG
  have hVKG : (V : Set M) ⊆ KG := interior_subset

  obtain ⟨P₁, G₁, hPG₁, hG₁inner, hP₁apply⟩ :=
    exists_pullbackField (I := I) Φ hKGcpt
      (fun y hy => hU₁ (hKGU hy)) h g

  obtain ⟨P'', G'', hPG'', hG''inner, hP''apply⟩ :=
    exists_pullbackField (I := I) Ψ hKGcpt
      (fun y hy => hsrcU (hKGU hy)) h' g

  have hc0T : ∀ x ∈ KG, metricTensorErrorNorm (I := I) P₁ g x ≤ ε := by
    intro x hxKG
    have hval : P₁ x = D₁.forward.pullback x := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₁apply x hxKG w, D₁.forward.pullback_apply x (hKGU hxKG) w]
    unfold metricTensorErrorNorm
    rw [hval]
    exact D₁.forward.c0_small x (hKGU hxKG)

  have hG₁c0 : ∀ x ∈ KG, metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G₁) g x ≤ ε := by
    intro x hx
    rw [← hPG₁]
    exact hc0T x hx
  have hEqG₁ := inner_le_of_c0 (I := I) G₁ g hG₁c0

  set δ₀ := D₁.forward.pullback - Tensor0SBundle.metricTensorField (I := I) g with hδ₀def
  set δ₁ := P'' - P₁ with hδ₁def
  set δN₂ := D₂.forward.pullback - Tensor0SBundle.metricTensorField (I := I) h with hδN₂def

  haveI : SecondCountableTopology H := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H M
  haveI : LocallyCompactSpace (V : Set M) := V.2.locallyCompactSpace
  haveI : SigmaCompactSpace (V : Set M) := inferInstance

  have hδ₁pt : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      δ₁ x v = δN₂ ((Φ : M → N) x)
        (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
    intro x hxV v
    have hxKG : x ∈ KG := hVKG hxV
    have hxU : x ∈ (U₁ : Set M) := hKGU hxKG
    have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ hxU)
    have hL : δ₁ x v = P'' x v - P₁ x v := by
      simp [hδ₁def, ContMDiffSection.coe_sub, Pi.sub_apply]
    have hR : δN₂ ((Φ : M → N) x) (fun q => mfderiv I I (Φ : M → N) x (v q))
        = D₂.forward.pullback ((Φ : M → N) x) (fun q => mfderiv I I (Φ : M → N) x (v q))
          - Tensor0SBundle.metricTensorField (I := I) h ((Φ : M → N) x)
              (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
      simp [hδN₂def, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hL, hR, hP''apply x hxKG v, hP₁apply x hxKG v,
      D₂.forward.pullback_apply ((Φ : M → N) x) hΦxK₂
        (fun q => mfderiv I I (Φ : M → N) x (v q)),
      Tensor0SBundle.metricTensorField_apply]
    rw [hchain x hxU (v 0), hchain x hxU (v 1)]
    rfl

  have hG₁V : ∀ x ∈ (V : Set M), ∀ v w : TangentSpace I x,
      G₁.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) :=
    fun x hx v w => hG₁inner x (hVKG hx) v w

  haveI : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H N
  haveI : LocallyCompactSpace ((Φ : M → N) '' (V : Set M) : Set N) :=
    (image_opens_isOpen (I := I) Φ
      (fun y hy => hU₁ (hKGU (hVKG hy)))).locallyCompactSpace
  haveI : SigmaCompactSpace ((Φ : M → N) '' (V : Set M) : Set N) := inferInstance

  have hδ₁tow : ∀ (hNV : Nonempty V) (a : ℕ) (x : M) (hx : x ∈ (V : Set M)),
      tensor02CovDerivNormWith (I := I) a δ₁ G₁ G₁ x
        = tensor02CovDerivNormWith (I := I) a δN₂ h h ((Φ : M → N) x) := by
    intro hNV a x hx
    exact covNormWith_pd_zone (I := I) Φ (V := V)
      (fun y hy => hU₁ (hKGU (hVKG hy))) h δN₂ δ₁ G₁ hδ₁pt hG₁V a x hx

  have hgpt : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      Tensor0SBundle.metricTensorField (I := I) g x v
        = D₁.reverse.pullback ((Φ : M → N) x)
            (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
    intro x hxV v
    have hxU : x ∈ (U₁ : Set M) := hKGU (hVKG hxV)
    have hxs : x ∈ Φ.source := hU₁ hxU
    have hΦxImg : (Φ : M → N) x ∈ (Φ : M → N) '' (U₁ : Set M) :=
      Set.mem_image_of_mem _ hxU

    have hfg : (Φ.symm : N → M) ∘ (Φ : M → N) =ᶠ[nhds x] id := by
      filter_upwards [Φ.open_source.mem_nhds hxs] with y hy
      exact Φ.left_inv' hy
    have hΦd : MDifferentiableAt I I (Φ : M → N) x :=
      ((Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hxs))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ : M → N) x) :=
      ((Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.symm.open_source.mem_nhds (Φ.map_source' hxs)))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp : (mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)).comp
        (mfderiv I I (Φ : M → N) x) = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      rw [← mfderiv_comp x hΦsd hΦd, hfg.mfderiv_eq]
      exact mfderiv_id
    have happ : ∀ w : TangentSpace I x,
        mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x w) = w := by
      intro w
      simpa using DFunLike.congr_fun hcomp w
    rw [D₁.reverse.pullback_apply ((Φ : M → N) x) hΦxImg
        (fun q => mfderiv I I (Φ : M → N) x (v q))]
    rw [Tensor0SBundle.metricTensorField_apply]
    have hl : (Φ.symm : N → M) ((Φ : M → N) x) = x := Φ.left_inv' hxs
    rw [happ (v 0), happ (v 1), hl]

  have hgKtow : ∀ (hNV : Nonempty V) (a : ℕ) (x : M) (hx : x ∈ (V : Set M)),
      tensor02CovDerivNormWith (I := I) a
          (Tensor0SBundle.metricTensorField (I := I) g) G₁ G₁ x
        = tensor02CovDerivNormWith (I := I) a D₁.reverse.pullback h h ((Φ : M → N) x) := by
    intro hNV a x hx
    exact covNormWith_pd_zone (I := I) Φ (V := V)
      (fun y hy => hU₁ (hKGU (hVKG hy))) h D₁.reverse.pullback
      (Tensor0SBundle.metricTensorField (I := I) g) G₁ hgpt hG₁V a x hx

  have hε0 : 0 < ε := D₁.forward.eps_pos
  have hε1 : ε < 1 := D₁.forward.eps_lt_one
  have h1ε : 0 < 1 - ε := by linarith
  set ε₀ : ℝ := ε / (1 - ε) with hε₀def
  have hε₀0 : 0 ≤ ε₀ := le_of_lt (div_pos hε0 h1ε)
  have hε₀1 : ε₀ ≤ 1 := by
    rw [hε₀def, div_le_one h1ε]
    linarith
  have hεε₀ : ε ≤ ε₀ := by
    rw [hε₀def, le_div_iff₀ h1ε]
    nlinarith

  have hequivF5 : ∀ x ∈ (V : Set M), ∀ v : TangentSpace I x,
      (1 + ε₀)⁻¹ * G₁.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + ε₀) * G₁.inner x v v := by
    intro x hxV v
    have hE := hEqG₁ x (hVKG hxV) v
    have hgnn : 0 ≤ g.inner x v v := metricInner_nonneg (I := I) g x v
    have h1ε₀ : 0 < 1 + ε₀ := by linarith
    have hkey : (1 + ε₀) * (1 - ε) = 1 + ε₀ - ε - ε₀ * ε := by ring
    constructor
    · rw [inv_mul_le_iff₀ h1ε₀]
      calc G₁.inner x v v ≤ (1 + ε) * g.inner x v v := hE.2
        _ ≤ (1 + ε₀) * g.inner x v v := by nlinarith
    · have : (1 - ε) * g.inner x v v ≤ G₁.inner x v v := hE.1
      have hmul : (1 + ε₀) * ((1 - ε) * g.inner x v v) ≤ (1 + ε₀) * G₁.inner x v v :=
        mul_le_mul_of_nonneg_left this (le_of_lt h1ε₀)
      have hone : g.inner x v v ≤ (1 + ε₀) * ((1 - ε) * g.inner x v v) := by
        have : (1 : ℝ) ≤ (1 + ε₀) * (1 - ε) := by
          rw [hε₀def]
          field_simp
          nlinarith
        nlinarith
      linarith

  have hδ₀F5 : ∀ x ∈ (V : Set M), ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (2 + r)
        (iterCov (I := I) g 2 δ₀ r x)) ≤ ε₀ := by
    intro x hxV r hr0 hrp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hsub := iterCov_sub (I := I) g 2 D₁.forward.pullback
      (Tensor0SBundle.metricTensorField (I := I) g) (r' + 1)
    rw [hδ₀def, hsub, iterCov_metric_zero, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    rw [← t02Norm_eq_iterCov (I := I) D₁.forward.pullback g (r' + 1) basis hinv]
    calc tensor02CovDerivNormWith (I := I) (r' + 1) D₁.forward.pullback g g x
        ≤ ε := D₁.forward.cov_deriv_small (r' + 1) (by omega) hrp x (hKGU (hVKG hxV))
      _ ≤ ε₀ := hεε₀

  have hgKF5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + j)
        (iterCov (I := I) G₁ 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ ε₀ := by
    intro hNV x hxV j hj1 hjp
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₁ x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₁ basis hON
    rw [← t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) g) G₁ j basis hinv]
    rw [hgKtow hNV j x hxV]
    calc tensor02CovDerivNormWith (I := I) j D₁.reverse.pullback h h ((Φ : M → N) x)
        ≤ ε := D₁.reverse.cov_deriv_small j hj1 hjp ((Φ : M → N) x)
          (Set.mem_image_of_mem _ (hKGU (hVKG hxV)))
      _ ≤ ε₀ := hεε₀

  have hδ₁F5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ k : ℕ, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + k)
        (iterCov (I := I) G₁ 2 δ₁ k x)) ≤ ε' := by
    intro hNV x hxV k hkp
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₁ x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₁ basis hON
    rw [← t02Norm_eq_iterCov (I := I) δ₁ G₁ k basis hinv]
    rw [hδ₁tow hNV k x hxV]
    have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) :=
      himg (Set.mem_image_of_mem _ (hKGU (hVKG hxV)))
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hc0 := D₂.forward.c0_small ((Φ : M → N) x) hΦxK₂
      calc tensor02CovDerivNormWith (I := I) 0 δN₂ h h ((Φ : M → N) x)
          = metricTensorErrorNorm (I := I) D₂.forward.pullback h ((Φ : M → N) x) := by
            unfold tensor02CovDerivNormWith metricTensorErrorNorm
            congr 1
        _ ≤ ε' := hc0
    · calc tensor02CovDerivNormWith (I := I) k δN₂ h h ((Φ : M → N) x)
          = tensor02CovDerivNormWith (I := I) k D₂.forward.pullback h h ((Φ : M → N) x) := by
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            have hfield : tensor02CovDeriv (I := I) δN₂ h (k' + 1)
                = tensor02CovDeriv (I := I) D₂.forward.pullback h (k' + 1) := by
              rw [hδN₂def, tensor02_eq_covDOF, tensor02_eq_covDOF, covDerivOfField_sub,
                covDerivOfField_eq_iterCov (I := I) h
                  (Tensor0SBundle.metricTensorField (I := I) h) (k' + 1),
                iterCov_metric_zero]
              simp
            unfold tensor02CovDerivNormWith
            rw [hfield]
        _ ≤ ε' := D₂.forward.cov_deriv_small k hk1 hkp ((Φ : M → N) x) hΦxK₂

  have hCp := hC (M' := M) (u := (V : Set M)) V.2 g G₁ δ₀ δ₁ ε₀ ε'
    hε₀0 hε₀1 (le_of_lt D₂.forward.eps_pos)
    hequivF5
    (fun x hx j hj1 hjp => hgKF5 ⟨⟨x, hx⟩⟩ x hx j hj1 hjp)
    hδ₀F5
    (fun x hx k hkp => hδ₁F5 ⟨⟨x, hx⟩⟩ x hx k hkp)

  have hgermz : ∀ (a : ℕ) (x : M), x ∈ (V : Set M) →
      ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) g (P₁ - D₁.forward.pullback) a x slots = 0 := by
    intro a x hxV slots
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hA0 : ∀ (q : V) (w : Fin 2 → TangentSpace I q),
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) 2) q w
          = (P₁ - D₁.forward.pullback) (q : M) w := by
      intro q w
      have hv : P₁ (q : M) w = D₁.forward.pullback (q : M) w := by
        rw [hP₁apply _ (hVKG q.2) w, D₁.forward.pullback_apply _ (hKGU (hVKG q.2)) w]
      simp [ContMDiffSection.coe_sub, Pi.sub_apply, hv]
    have hres := covDerivOfField_restrictOpen (I := I) g V
      (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) 2)
      (P₁ - D₁.forward.pullback) hA0 a ⟨x, hxV⟩ slots
    rw [← hres, covDOF_zero]
    simp

  have hcovP'' : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a P'' g g x ≤ ε₀ + ε' * C := by
    intro a ha1 hap x hxK
    have hxV : x ∈ (V : Set M) := hKV hxK
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩

    have hgermzI : ∀ slots : Fin (2 + (a' + 1)) → TangentSpace I x,
        iterCov (I := I) g 2 (P₁ - D₁.forward.pullback) (a' + 1) x slots = 0 := by
      intro slots
      have hfe := covDerivOfField_eq_iterCov (I := I) g
        (P₁ - D₁.forward.pullback) (a' + 1)
      have hx1 := DFunLike.congr_fun hfe x
      have hx2 := DFunLike.congr_fun hx1
        (fun q => slots ((acEquiv (a' + 1)).symm q))
      change _ = (ContinuousMultilinearMap.domDomCongr
        (acEquiv (a' + 1)) _) _ at hx2
      rw [ContinuousMultilinearMap.domDomCongr_apply] at hx2
      have hslots : (fun q => slots ((acEquiv (a' + 1)).symm
          ((acEquiv (a' + 1)) q))) = slots := by
        funext q
        rw [Equiv.symm_apply_apply]
      rw [hslots] at hx2
      exact hx2.symm.trans (hgermz (a' + 1) x hxV _)

    have hdecI : iterCov (I := I) g 2 P'' (a' + 1) x
        = iterCov (I := I) g 2 (δ₀ + δ₁) (a' + 1) x := by
      have hsplit : (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E)
          (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
          = (P'' - Tensor0SBundle.metricTensorField (I := I) g)
            - (P₁ - D₁.forward.pullback) := by
        rw [hδ₀def, hδ₁def]
        abel
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      rw [hsplit, iterCov_sub, iterCov_sub, iterCov_metric_zero, sub_zero]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [Tensor0SBundle.Tensor0SSpace.sub_apply, hgermzI slots, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    rw [t02Norm_eq_iterCov (I := I) P'' g (a' + 1) basis hinv, hdecI]
    exact hCp x hxV (a' + 1) (by omega) hap

  have hc0P'' : ∀ x ∈ K,
      metricTensorErrorNorm (I := I) P'' g x ≤ ε + ε' * (1 + ε₀) := by
    intro x hxK
    have hxV : x ∈ (V : Set M) := hKV hxK
    have hxKG : x ∈ KG := hVKG hxV
    have h3 : P₁ x = D₁.forward.pullback x := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₁apply x hxKG w, D₁.forward.pullback_apply x (hKGU hxKG) w]
    have hval : P'' x - Tensor0SBundle.metricTensorField (I := I) g x
        = δ₀ x + δ₁ x := by
      simp only [hδ₀def, hδ₁def, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h3]
      abel
    unfold metricTensorErrorNorm
    rw [hval]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    have htri := sqrt_normSq0S_add_le (I := I) g (δ₀ x) (δ₁ x) basis hinv
    have ht0 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x)) ≤ ε := by
      have hc := D₁.forward.c0_small x (hKGU hxKG)
      unfold metricTensorErrorNorm at hc
      have h1 : δ₀ x = D₁.forward.pullback x
          - Tensor0SBundle.metricTensorField (I := I) g x := by
        simp [hδ₀def, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h1]
      exact hc
    have ht1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
        ≤ (1 + ε₀) * ε' := by
      have hMUE : MetricUniformEquivalentOn (I := I) (V : Set M) G₁ g (1 + ε₀) :=
        ⟨by linarith, fun y hy v => hequivF5 y hy v⟩
      have hcompn := sqrt_normSq_two_le (I := I) hMUE hxV (δ₁ x)
      have hG₁δ : Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) ≤ ε' := by
        have h := hδ₁F5 ⟨⟨x, hxV⟩⟩ x hxV 0 (Nat.zero_le p)
        simpa using h
      have hsq : Real.sqrt ((1 + ε₀) ^ 2) = 1 + ε₀ := by
        rw [Real.sqrt_sq (by linarith)]
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
          ≤ Real.sqrt ((1 + ε₀) ^ 2)
            * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := hcompn
        _ = (1 + ε₀) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := by
            rw [hsq]
        _ ≤ (1 + ε₀) * ε' := mul_le_mul_of_nonneg_left hG₁δ (by linarith)
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x + δ₁ x))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x))
          + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x)) := htri
      _ ≤ ε + (1 + ε₀) * ε' := add_le_add ht0 ht1
      _ = ε + ε' * (1 + ε₀) := by ring

  have hε₀2ε : ε₀ ≤ 2 * ε := by
    rw [hε₀def, div_le_iff₀ h1ε]
    nlinarith
  have hε'0 : 0 ≤ ε' := le_of_lt D₂.forward.eps_pos


  have hΨcont : ContinuousOn (Ψ : M → P) KG :=
    Ψ.contMDiffOn_toFun.continuousOn.mono (fun y hy => hsrcU (hKGU hy))
  have hΨKG_cpt : IsCompact ((Ψ : M → P) '' KG) := hKGcpt.image_of_continuousOn hΨcont
  have hΨKG_tgt : (Ψ : M → P) '' KG ⊆ Ψ.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact Ψ.map_source' (hsrcU (hKGU hy))
  obtain ⟨Pr, Gr, hPGr, hGrinner, hPrapply⟩ :=
    exists_pullbackField (I := I) Ψ.symm hΨKG_cpt hΨKG_tgt g h'
  have hKimg : (Ψ : M → P) '' K ⊆ (Ψ : M → P) '' KG :=
    Set.image_mono (fun y hy => hVKG (hKV hy))

  have hVsrc : (V : Set M) ⊆ Ψ.source := fun y hy => hsrcU (hKGU (hVKG hy))
  set VP : Opens P := ⟨(Ψ : M → P) '' (V : Set M), image_opens_isOpen (I := I) Ψ hVsrc⟩
    with hVPdef
  have hVPKG : (VP : Set P) ⊆ (Ψ : M → P) '' KG := Set.image_mono hVKG

  have hΨKG_tgt' : (Ψ : M → P) '' KG ⊆ Φ'.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    have : (Φ : M → N) y ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ (hKGU hy))
    exact Φ'.map_source' (hK₂ this)
  obtain ⟨P₂r, G₂r, hPG₂r, hG₂rinner, hP₂rapply⟩ :=
    exists_pullbackField (I := I) Φ'.symm hΨKG_cpt hΨKG_tgt' h h'

  have hε'0' : 0 < ε' := D₂.forward.eps_pos
  have hε'1 : ε' < 1 := D₂.forward.eps_lt_one
  have h1ε' : 0 < 1 - ε' := by linarith
  set ε₀' : ℝ := ε' / (1 - ε') with hε₀'def
  have hε₀'0 : 0 ≤ ε₀' := le_of_lt (div_pos hε'0' h1ε')
  have hε₀'1 : ε₀' ≤ 1 := by
    rw [hε₀'def, div_le_one h1ε']
    linarith
  have hε'ε₀' : ε' ≤ ε₀' := by
    rw [hε₀'def, le_div_iff₀ h1ε']
    nlinarith
  have hε₀'2ε' : ε₀' ≤ 2 * ε' := by
    rw [hε₀'def, div_le_iff₀ h1ε']
    nlinarith

  set δ₀r := D₂.reverse.pullback - Tensor0SBundle.metricTensorField (I := I) h'
    with hδ₀rdef
  set δ₁r := Pr - P₂r with hδ₁rdef
  set δN₁r := D₁.reverse.pullback - Tensor0SBundle.metricTensorField (I := I) h
    with hδN₁rdef

  have hVPmem : ∀ y ∈ (VP : Set P), ∃ m ∈ (V : Set M), (Ψ : M → P) m = y := by
    rintro y ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  have hVPimgK₂ : ∀ y ∈ (VP : Set P), (Φ'.symm : P → N) y ∈ (K₂ : Set N) ∧
      (Φ'.symm : P → N) y ∈ (Φ : M → N) '' (U₁ : Set M) ∧ y ∈ Φ'.target := by
    rintro y ⟨m, hm, rfl⟩
    have hmU : m ∈ (U₁ : Set M) := hKGU (hVKG hm)
    have hΦm : (Φ : M → N) m ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ hmU)
    have hyt : ((Ψ : M → P) m) ∈ Φ'.target := by
      have : (Ψ : M → P) m = (Φ' : N → P) ((Φ : M → N) m) := rfl
      rw [this]
      exact Φ'.map_source' (hK₂ hΦm)
    have hsymm : (Φ'.symm : P → N) ((Ψ : M → P) m) = (Φ : M → N) m := by
      have : (Ψ : M → P) m = (Φ' : N → P) ((Φ : M → N) m) := rfl
      rw [this]
      exact Φ'.left_inv' (hK₂ hΦm)
    refine ⟨?_, ?_, hyt⟩
    · rw [hsymm]; exact hΦm
    · rw [hsymm]; exact Set.mem_image_of_mem _ hmU

  have hc0Tr : ∀ y ∈ (VP : Set P),
      metricTensorErrorNorm (I := I) P₂r h' y ≤ ε' := by
    intro y hyVP
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyKG : y ∈ (Ψ : M → P) '' KG := hVPKG hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) := by
      refine ⟨(Φ'.symm : P → N) y, hyK₂, ?_⟩
      exact Φ'.right_inv' hyt
    have hval : P₂r y = D₂.reverse.pullback y := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₂rapply y hyKG w, D₂.reverse.pullback_apply y hyΦ'K₂ w]
    unfold metricTensorErrorNorm
    rw [hval]
    exact D₂.reverse.c0_small y hyΦ'K₂
  have hG₂rc0 : ∀ y ∈ (VP : Set P), metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G₂r) h' y ≤ ε' := by
    intro y hy
    rw [← hPG₂r]
    exact hc0Tr y hy
  have hEqG₂r := inner_le_of_c0 (I := I) G₂r h' hG₂rc0

  have hchainr : ∀ y ∈ (VP : Set P), ∀ v : TangentSpace I y,
      mfderiv I I (Ψ.symm : P → M) y v
        = mfderiv I I (Φ.symm : N → M) ((Φ'.symm : P → N) y)
            (mfderiv I I (Φ'.symm : P → N) y v) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hΦ'sd : MDifferentiableAt I I (Φ'.symm : P → N) y :=
      (Φ'.symm.contMDiffOn_toFun.contMDiffAt
        (Φ'.symm.open_source.mem_nhds hyt)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦst : (Φ'.symm : P → N) y ∈ Φ.target := by
      obtain ⟨m, hmU, hmeq⟩ := hyU₁img
      rw [← hmeq]
      exact Φ.map_source' (hU₁ hmU)
    have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ'.symm : P → N) y) :=
      (Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.symm.open_source.mem_nhds hΦst)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have h := mfderiv_comp y hΦsd hΦ'sd
    have happ := DFunLike.congr_fun h v
    simpa [ContinuousLinearMap.comp_apply] using happ

  have hδ₁rpt : ∀ y ∈ (VP : Set P), ∀ v : Fin 2 → TangentSpace I y,
      δ₁r y v = δN₁r ((Φ'.symm : P → N) y)
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyKG : y ∈ (Ψ : M → P) '' KG := hVPKG hyVP
    have hL : δ₁r y v = Pr y v - P₂r y v := by
      simp [hδ₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
    have hR : δN₁r ((Φ'.symm : P → N) y)
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))
        = D₁.reverse.pullback ((Φ'.symm : P → N) y)
            (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))
          - Tensor0SBundle.metricTensorField (I := I) h ((Φ'.symm : P → N) y)
              (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
      simp [hδN₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hL, hR, hPrapply y hyKG v, hP₂rapply y hyKG v,
      D₁.reverse.pullback_apply ((Φ'.symm : P → N) y) hyU₁img
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)),
      Tensor0SBundle.metricTensorField_apply]
    rw [hchainr y hyVP (v 0), hchainr y hyVP (v 1)]
    rfl

  have hG₂rV : ∀ y ∈ (VP : Set P), ∀ v w : TangentSpace I y,
      G₂r.inner y v w = h.inner ((Φ'.symm : P → N) y)
        (mfderiv I I (Φ'.symm : P → N) y v) (mfderiv I I (Φ'.symm : P → N) y w) :=
    fun y hy v w => hG₂rinner y (hVPKG hy) v w

  haveI : LocallyCompactSpace P := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H P
  haveI : LocallyCompactSpace (VP : Set P) := VP.2.locallyCompactSpace
  haveI : SigmaCompactSpace (VP : Set P) := inferInstance
  haveI : LocallyCompactSpace ((Φ'.symm : P → N) '' (VP : Set P) : Set N) :=
    (image_opens_isOpen (I := I) Φ'.symm
      (fun y hy => (hVPimgK₂ y hy).2.2)).locallyCompactSpace
  haveI : SigmaCompactSpace ((Φ'.symm : P → N) '' (VP : Set P) : Set N) := inferInstance

  have hδ₁rtow : ∀ (hNVP : Nonempty VP) (a : ℕ) (y : P) (hy : y ∈ (VP : Set P)),
      tensor02CovDerivNormWith (I := I) a δ₁r G₂r G₂r y
        = tensor02CovDerivNormWith (I := I) a δN₁r h h ((Φ'.symm : P → N) y) := by
    intro hNVP a y hy
    exact covNormWith_pd_zone (I := I) Φ'.symm (V := VP)
      (fun z hz => (hVPimgK₂ z hz).2.2) h δN₁r δ₁r G₂r hδ₁rpt hG₂rV a y hy

  have hgptr : ∀ y ∈ (VP : Set P), ∀ v : Fin 2 → TangentSpace I y,
      Tensor0SBundle.metricTensorField (I := I) h' y v
        = D₂.forward.pullback ((Φ'.symm : P → N) y)
            (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hfg : (Φ' : N → P) ∘ (Φ'.symm : P → N) =ᶠ[nhds y] id := by
      filter_upwards [Φ'.open_target.mem_nhds hyt] with z hz
      exact Φ'.right_inv' hz
    have hΦ'sd : MDifferentiableAt I I (Φ'.symm : P → N) y :=
      (Φ'.symm.contMDiffOn_toFun.contMDiffAt
        (Φ'.symm.open_source.mem_nhds hyt)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦ'd : MDifferentiableAt I I (Φ' : N → P) ((Φ'.symm : P → N) y) :=
      (Φ'.contMDiffOn_toFun.contMDiffAt
        (Φ'.open_source.mem_nhds (Φ'.map_target' hyt))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp : (mfderiv I I (Φ' : N → P) ((Φ'.symm : P → N) y)).comp
        (mfderiv I I (Φ'.symm : P → N) y) = ContinuousLinearMap.id ℝ (TangentSpace I y) := by
      rw [← mfderiv_comp y hΦ'd hΦ'sd, hfg.mfderiv_eq]
      exact mfderiv_id
    have happ : ∀ w : TangentSpace I y,
        mfderiv I I (Φ' : N → P) ((Φ'.symm : P → N) y)
          (mfderiv I I (Φ'.symm : P → N) y w) = w := by
      intro w
      simpa using DFunLike.congr_fun hcomp w
    rw [D₂.forward.pullback_apply ((Φ'.symm : P → N) y) hyK₂
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))]
    rw [Tensor0SBundle.metricTensorField_apply]
    have hr : (Φ' : N → P) ((Φ'.symm : P → N) y) = y := Φ'.right_inv' hyt
    rw [happ (v 0), happ (v 1), hr]

  have hgKrtow : ∀ (hNVP : Nonempty VP) (a : ℕ) (y : P) (hy : y ∈ (VP : Set P)),
      tensor02CovDerivNormWith (I := I) a
          (Tensor0SBundle.metricTensorField (I := I) h') G₂r G₂r y
        = tensor02CovDerivNormWith (I := I) a D₂.forward.pullback h h
            ((Φ'.symm : P → N) y) := by
    intro hNVP a y hy
    exact covNormWith_pd_zone (I := I) Φ'.symm (V := VP)
      (fun z hz => (hVPimgK₂ z hz).2.2) h D₂.forward.pullback
      (Tensor0SBundle.metricTensorField (I := I) h') G₂r hgptr hG₂rV a y hy

  have hequivF5r : ∀ y ∈ (VP : Set P), ∀ v : TangentSpace I y,
      (1 + ε₀')⁻¹ * G₂r.inner y v v ≤ h'.inner y v v ∧
        h'.inner y v v ≤ (1 + ε₀') * G₂r.inner y v v := by
    intro y hy v
    have hE := hEqG₂r y hy v
    have hnn : 0 ≤ h'.inner y v v := metricInner_nonneg (I := I) h' y v
    have h1ε₀' : 0 < 1 + ε₀' := by linarith
    constructor
    · rw [inv_mul_le_iff₀ h1ε₀']
      calc G₂r.inner y v v ≤ (1 + ε') * h'.inner y v v := hE.2
        _ ≤ (1 + ε₀') * h'.inner y v v := by nlinarith
    · have hlow : (1 - ε') * h'.inner y v v ≤ G₂r.inner y v v := hE.1
      have hmul : (1 + ε₀') * ((1 - ε') * h'.inner y v v)
          ≤ (1 + ε₀') * G₂r.inner y v v :=
        mul_le_mul_of_nonneg_left hlow (le_of_lt h1ε₀')
      have hone : h'.inner y v v ≤ (1 + ε₀') * ((1 - ε') * h'.inner y v v) := by
        have : (1 : ℝ) ≤ (1 + ε₀') * (1 - ε') := by
          rw [hε₀'def]
          field_simp
          nlinarith
        nlinarith
      linarith
  have hδ₀rF5 : ∀ y ∈ (VP : Set P), ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y (2 + r)
        (iterCov (I := I) h' 2 δ₀r r y)) ≤ ε₀' := by
    intro y hyVP r hr0 hrp
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) :=
      ⟨(Φ'.symm : P → N) y, hyK₂, Φ'.right_inv' hyt⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hsub := iterCov_sub (I := I) h' 2 D₂.reverse.pullback
      (Tensor0SBundle.metricTensorField (I := I) h') (r' + 1)
    rw [hδ₀rdef, hsub, iterCov_metric_zero, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    rw [← t02Norm_eq_iterCov (I := I) D₂.reverse.pullback h' (r' + 1) basis hinv]
    calc tensor02CovDerivNormWith (I := I) (r' + 1) D₂.reverse.pullback h' h' y
        ≤ ε' := D₂.reverse.cov_deriv_small (r' + 1) (by omega) hrp y hyΦ'K₂
      _ ≤ ε₀' := hε'ε₀'
  have hgKrF5 : ∀ (hNVP : Nonempty VP), ∀ y ∈ (VP : Set P), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y (2 + j)
        (iterCov (I := I) G₂r 2 (Tensor0SBundle.metricTensorField (I := I) h') j y))
        ≤ ε₀' := by
    intro hNVP y hyVP j hj1 hjp
    obtain ⟨hyK₂, _, _⟩ := hVPimgK₂ y hyVP
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₂r y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₂r basis hON
    rw [← t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) h') G₂r j basis hinv]
    rw [hgKrtow hNVP j y hyVP]
    calc tensor02CovDerivNormWith (I := I) j D₂.forward.pullback h h
          ((Φ'.symm : P → N) y)
        ≤ ε' := D₂.forward.cov_deriv_small j hj1 hjp ((Φ'.symm : P → N) y) hyK₂
      _ ≤ ε₀' := hε'ε₀'
  have hδ₁rF5 : ∀ (hNVP : Nonempty VP), ∀ y ∈ (VP : Set P), ∀ k : ℕ, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y (2 + k)
        (iterCov (I := I) G₂r 2 δ₁r k y)) ≤ ε := by
    intro hNVP y hyVP k hkp
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₂r y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₂r basis hON
    rw [← t02Norm_eq_iterCov (I := I) δ₁r G₂r k basis hinv]
    rw [hδ₁rtow hNVP k y hyVP]
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hc0 := D₁.reverse.c0_small ((Φ'.symm : P → N) y) hyU₁img
      calc tensor02CovDerivNormWith (I := I) 0 δN₁r h h ((Φ'.symm : P → N) y)
          = metricTensorErrorNorm (I := I) D₁.reverse.pullback h
              ((Φ'.symm : P → N) y) := by
            unfold tensor02CovDerivNormWith metricTensorErrorNorm
            congr 1
        _ ≤ ε := hc0
    · calc tensor02CovDerivNormWith (I := I) k δN₁r h h ((Φ'.symm : P → N) y)
          = tensor02CovDerivNormWith (I := I) k D₁.reverse.pullback h h
              ((Φ'.symm : P → N) y) := by
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            have hfield : tensor02CovDeriv (I := I) δN₁r h (k' + 1)
                = tensor02CovDeriv (I := I) D₁.reverse.pullback h (k' + 1) := by
              rw [hδN₁rdef, tensor02_eq_covDOF, tensor02_eq_covDOF, covDerivOfField_sub,
                covDerivOfField_eq_iterCov (I := I) h
                  (Tensor0SBundle.metricTensorField (I := I) h) (k' + 1),
                iterCov_metric_zero]
              simp
            unfold tensor02CovDerivNormWith
            rw [hfield]
        _ ≤ ε := D₁.reverse.cov_deriv_small k hk1 hkp ((Φ'.symm : P → N) y) hyU₁img

  have hCpr := hC (M' := P) (u := (VP : Set P)) VP.2 h' G₂r
    δ₀r δ₁r ε₀' ε hε₀'0 hε₀'1 hε0.le
    hequivF5r
    (fun y hy j hj1 hjp => hgKrF5 ⟨⟨y, hy⟩⟩ y hy j hj1 hjp)
    hδ₀rF5
    (fun y hy k hkp => hδ₁rF5 ⟨⟨y, hy⟩⟩ y hy k hkp)

  have hgermzr : ∀ (a : ℕ) (y : P), y ∈ (VP : Set P) →
      ∀ slots : Fin (a + 2) → TangentSpace I y,
      covDerivOfField (I := I) h' (P₂r - D₂.reverse.pullback) a y slots = 0 := by
    intro a y hyVP slots
    haveI : Nonempty VP := ⟨⟨y, hyVP⟩⟩
    have hA0 : ∀ (q : VP) (w : Fin 2 → TangentSpace I q),
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := VP) (n := (∞ : WithTop ℕ∞)) 2) q w
          = (P₂r - D₂.reverse.pullback) (q : P) w := by
      intro q w
      obtain ⟨hqK₂, _, hqt⟩ := hVPimgK₂ (q : P) q.2
      have hqΦ'K₂ : (q : P) ∈ (Φ' : N → P) '' (K₂ : Set N) :=
        ⟨(Φ'.symm : P → N) q, hqK₂, Φ'.right_inv' hqt⟩
      have hv : P₂r (q : P) w = D₂.reverse.pullback (q : P) w := by
        rw [hP₂rapply _ (hVPKG q.2) w, D₂.reverse.pullback_apply _ hqΦ'K₂ w]
      simp [ContMDiffSection.coe_sub, Pi.sub_apply, hv]
    have hres := covDerivOfField_restrictOpen (I := I) h' VP
      (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := VP) (n := (∞ : WithTop ℕ∞)) 2)
      (P₂r - D₂.reverse.pullback) hA0 a ⟨y, hyVP⟩ slots
    rw [← hres, covDOF_zero]
    simp

  have hcovPr : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ (Ψ : M → P) '' K,
      tensor02CovDerivNormWith (I := I) a Pr h' h' y ≤ ε₀' + ε * C := by
    intro a ha1 hap y hyK
    have hyVP : y ∈ (VP : Set P) := by
      obtain ⟨m, hm, rfl⟩ := hyK
      exact ⟨m, hKV hm, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hgermzrI : ∀ slots : Fin (2 + (a' + 1)) → TangentSpace I y,
        iterCov (I := I) h' 2 (P₂r - D₂.reverse.pullback) (a' + 1) y slots = 0 := by
      intro slots
      have hfe := covDerivOfField_eq_iterCov (I := I) h'
        (P₂r - D₂.reverse.pullback) (a' + 1)
      have hx1 := DFunLike.congr_fun hfe y
      have hx2 := DFunLike.congr_fun hx1
        (fun q => slots ((acEquiv (a' + 1)).symm q))
      change _ = (ContinuousMultilinearMap.domDomCongr
        (acEquiv (a' + 1)) _) _ at hx2
      rw [ContinuousMultilinearMap.domDomCongr_apply] at hx2
      have hslots : (fun q => slots ((acEquiv (a' + 1)).symm
          ((acEquiv (a' + 1)) q))) = slots := by
        funext q
        rw [Equiv.symm_apply_apply]
      rw [hslots] at hx2
      exact hx2.symm.trans (hgermzr (a' + 1) y hyVP _)
    have hdecI : iterCov (I := I) h' 2 Pr (a' + 1) y
        = iterCov (I := I) h' 2 (δ₀r + δ₁r) (a' + 1) y := by
      have hsplit : (δ₀r + δ₁r : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E)
          (H := H) (I := I) (M := P) (n := (∞ : WithTop ℕ∞)) 2)
          = (Pr - Tensor0SBundle.metricTensorField (I := I) h')
            - (P₂r - D₂.reverse.pullback) := by
        rw [hδ₀rdef, hδ₁rdef]
        abel
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      rw [hsplit, iterCov_sub, iterCov_sub, iterCov_metric_zero, sub_zero]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [Tensor0SBundle.Tensor0SSpace.sub_apply, hgermzrI slots, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    rw [t02Norm_eq_iterCov (I := I) Pr h' (a' + 1) basis hinv, hdecI]
    exact hCpr y hyVP (a' + 1) (by omega) hap

  have hc0Pr : ∀ y ∈ (Ψ : M → P) '' K,
      metricTensorErrorNorm (I := I) Pr h' y ≤ ε' + ε * (1 + ε₀') := by
    intro y hyK
    have hyVP : y ∈ (VP : Set P) := by
      obtain ⟨m, hm, rfl⟩ := hyK
      exact ⟨m, hKV hm, rfl⟩
    obtain ⟨hyK₂, _, hyt⟩ := hVPimgK₂ y hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) :=
      ⟨(Φ'.symm : P → N) y, hyK₂, Φ'.right_inv' hyt⟩
    have h3 : P₂r y = D₂.reverse.pullback y := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₂rapply _ (hVPKG hyVP) w, D₂.reverse.pullback_apply _ hyΦ'K₂ w]
    have hval : Pr y - Tensor0SBundle.metricTensorField (I := I) h' y
        = δ₀r y + δ₁r y := by
      simp only [hδ₀rdef, hδ₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [← h3]
      abel
    unfold metricTensorErrorNorm
    rw [hval]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    have htri := sqrt_normSq0S_add_le (I := I) h' (δ₀r y) (δ₁r y) basis hinv
    have ht0 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y)) ≤ ε' := by
      have hc := D₂.reverse.c0_small y hyΦ'K₂
      unfold metricTensorErrorNorm at hc
      have h1 : δ₀r y = D₂.reverse.pullback y
          - Tensor0SBundle.metricTensorField (I := I) h' y := by
        simp [hδ₀rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h1]
      exact hc
    have ht1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y))
        ≤ (1 + ε₀') * ε := by
      have hMUE : MetricUniformEquivalentOn (I := I) (VP : Set P) G₂r h' (1 + ε₀') :=
        ⟨by linarith, fun z hz v => hequivF5r z hz v⟩
      have hcompn := sqrt_normSq_two_le (I := I) hMUE hyVP (δ₁r y)
      have hG₂δ : Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) ≤ ε := by
        have h := hδ₁rF5 ⟨⟨y, hyVP⟩⟩ y hyVP 0 (Nat.zero_le p)
        simpa using h
      have hsq : Real.sqrt ((1 + ε₀') ^ 2) = 1 + ε₀' := by
        rw [Real.sqrt_sq (by linarith)]
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y))
          ≤ Real.sqrt ((1 + ε₀') ^ 2)
            * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) := hcompn
        _ = (1 + ε₀') * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) := by
            rw [hsq]
        _ ≤ (1 + ε₀') * ε := mul_le_mul_of_nonneg_left hG₂δ (by linarith)
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y + δ₁r y))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y))
          + Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y)) := htri
      _ ≤ ε' + (1 + ε₀') * ε := add_le_add ht0 ht1
      _ = ε' + ε * (1 + ε₀') := by ring

  intro ε'' hlb1 hlb2 hub
  have hCm0 : (0 : ℝ) ≤ max C 2 := le_trans hC0 (le_max_left _ _)
  have hC_le : C ≤ max C 2 := le_max_left _ _
  have h1ε₀le : 1 + ε₀ ≤ max C 2 := le_trans (by linarith) (le_max_right _ _)
  have h1ε₀'le : 1 + ε₀' ≤ max C 2 := le_trans (by linarith) (le_max_right _ _)
  have harithc0 : ε + ε' * (1 + ε₀) ≤ ε'' := by
    have h1 : ε' * (1 + ε₀) ≤ ε' * max C 2 := mul_le_mul_of_nonneg_left h1ε₀le hε'0
    nlinarith [hεε₀]
  have harithcov : ε₀ + ε' * C ≤ ε'' := by
    have h1 : ε' * C ≤ ε' * max C 2 := mul_le_mul_of_nonneg_left hC_le hε'0
    nlinarith
  have harithc0r : ε' + ε * (1 + ε₀') ≤ ε'' := by
    have h1 : ε * (1 + ε₀') ≤ ε * max C 2 := mul_le_mul_of_nonneg_left h1ε₀'le hε0.le
    nlinarith [hε'ε₀']
  have harithcovr : ε₀' + ε * C ≤ ε'' := by
    have h1 : ε * C ≤ ε * max C 2 := mul_le_mul_of_nonneg_left hC_le hε0.le
    nlinarith
  have hε''0 : 0 < ε'' := by
    have : 0 < ε₀ := div_pos hε0 h1ε
    nlinarith [mul_nonneg hε'0 hCm0]
  refine ⟨⟨hKsrc, ?_, ?_⟩⟩
  ·
    exact
      { eps_pos := hε''0
        eps_lt_one := hub
        smoothOn := Ψ.contMDiffOn_toFun.mono hKsrc
        pullback := P''
        pullback_apply := fun x hx v => hP''apply x (hVKG (hKV hx)) v
        c0_small := fun x hx => le_trans (hc0P'' x hx) harithc0
        cov_deriv_small := fun a h1 h2 x hx =>
          le_trans (hcovP'' a h1 h2 x hx) harithcov }
  ·
    refine
      { eps_pos := hε''0
        eps_lt_one := hub
        smoothOn := Ψ.symm.contMDiffOn_toFun.mono
          (fun y hy => hΨKG_tgt (hKimg hy))
        pullback := Pr
        pullback_apply := fun y hy v => hPrapply y (hKimg hy) v
        c0_small := fun y hy => le_trans (hc0Pr y hy) harithc0r
        cov_deriv_small := fun a h1 h2 y hy =>
          le_trans (hcovPr a h1 h2 y hy) harithcovr }

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in







noncomputable def compSepFwd [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {P : Type u} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    [T2Space N] [SigmaCompactSpace N] [T2Space P] [SigmaCompactSpace P]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [IsManifold I 1 P] [IsManifold I 2 P] [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {U₁ : Opens M} [Nonempty U₁] (hU₁ : (U₁ : Set M) ⊆ Φ.source)
    {K₂ : Opens N} [Nonempty K₂] (hK₂ : (K₂ : Set N) ⊆ Φ'.source)
    (himg : (Φ : M → N) '' (U₁ : Set M) ⊆ (K₂ : Set N))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U₁ : Set M))
    {c0 cov c0' cov' q e1 c0'' cov'' : Real} {p : Nat}
    (hc0_half : c0 ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hq_c0 : c0 / (1 - c0) ≤ q) (hq_cov : cov ≤ q)
    (he1_0 : 0 ≤ e1) (he1_c0 : c0' ≤ e1) (he1_cov : cov' ≤ e1)
    (C : Real) (hC0 : 0 ≤ C)
    (hc0_out : c0 + c0' * (1 + q) ≤ c0'')
    (hcov_out : q + e1 * C ≤ cov'')
    (hC : ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
      [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
      [IsManifold I 1 M'] [IsManifold I 2 M']
      [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
      {u : Set M'}, IsOpen u →
      ∀ (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2
              (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoSep (I := I) (U₁ : Set M) c0 cov p Φ g h)
    (D₂ : BookApproxIsoSep (I := I) (K₂ : Set N) c0' cov' p Φ' h h') :
    PreApproxIsoSep (I := I) K c0'' cov'' p
      (PartialDiffeomorph.trans (I := I) Φ Φ' : M → P) g h' := by
  classical
  set Ψ := PartialDiffeomorph.trans (I := I) Φ Φ' with hΨdef
  have hsrcU : (U₁ : Set M) ⊆ Ψ.source := by
    intro y hy
    exact ⟨hU₁ hy, hK₂ (himg (Set.mem_image_of_mem _ hy))⟩
  have hKsrc : K ⊆ Ψ.source := fun y hy => hsrcU (hKU hy)
  have hchain : ∀ y ∈ (U₁ : Set M), ∀ v : TangentSpace I y,
      mfderiv I I (Ψ : M → P) y v
        = mfderiv I I (Φ' : N → P) ((Φ : M → N) y)
            (mfderiv I I (Φ : M → N) y v) := by
    intro y hy v
    have hΦd : MDifferentiableAt I I (Φ : M → N) y :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hU₁ hy))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦ'd : MDifferentiableAt I I (Φ' : N → P) ((Φ : M → N) y) :=
      (Φ'.contMDiffOn_toFun.contMDiffAt
        (Φ'.open_source.mem_nhds
          (hK₂ (himg (Set.mem_image_of_mem _ hy))))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp := mfderiv_comp y hΦ'd hΦd
    have happ := DFunLike.congr_fun hcomp v
    simpa [ContinuousLinearMap.comp_apply] using happ
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let KG : Set M := Classical.choose (exists_compact_between hK U₁.2 hKU)
  have hKGspec := Classical.choose_spec (exists_compact_between hK U₁.2 hKU)
  have hKGcpt : IsCompact KG := hKGspec.1
  have hKKG : K ⊆ interior KG := hKGspec.2.1
  have hKGU : KG ⊆ (U₁ : Set M) := hKGspec.2.2
  set V : Opens M := ⟨interior KG, isOpen_interior⟩ with hVdef
  have hKV : K ⊆ (V : Set M) := hKKG
  have hVKG : (V : Set M) ⊆ KG := interior_subset
  let pull1 := exists_pullbackField (I := I) Φ hKGcpt
    (fun y hy => hU₁ (hKGU hy)) h g
  let P₁ := Classical.choose pull1
  let G₁ := Classical.choose (Classical.choose_spec pull1)
  have hP₁spec := Classical.choose_spec (Classical.choose_spec pull1)
  have hPG₁ : P₁ = Tensor0SBundle.metricTensorField (I := I) G₁ := hP₁spec.1
  have hG₁inner : ∀ x ∈ KG, ∀ v w : TangentSpace I x,
      G₁.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) :=
    hP₁spec.2.1
  have hP₁apply : ∀ x ∈ KG, ∀ v : Fin 2 → TangentSpace I x,
      P₁ x v = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x (v 0)) (mfderiv I I (Φ : M → N) x (v 1)) :=
    hP₁spec.2.2
  let pullComp := exists_pullbackField (I := I) Ψ hKGcpt
    (fun y hy => hsrcU (hKGU hy)) h' g
  let P'' := Classical.choose pullComp
  let G'' := Classical.choose (Classical.choose_spec pullComp)
  have hP''spec := Classical.choose_spec (Classical.choose_spec pullComp)
  have hPG'' : P'' = Tensor0SBundle.metricTensorField (I := I) G'' := hP''spec.1
  have hG''inner : ∀ x ∈ KG, ∀ v w : TangentSpace I x,
      G''.inner x v w = h'.inner ((Ψ : M → P) x)
        (mfderiv I I (Ψ : M → P) x v) (mfderiv I I (Ψ : M → P) x w) :=
    hP''spec.2.1
  have hP''apply : ∀ x ∈ KG, ∀ v : Fin 2 → TangentSpace I x,
      P'' x v = h'.inner ((Ψ : M → P) x)
        (mfderiv I I (Ψ : M → P) x (v 0)) (mfderiv I I (Ψ : M → P) x (v 1)) :=
    hP''spec.2.2
  have hc0T : ∀ x ∈ KG, metricTensorErrorNorm (I := I) P₁ g x ≤ c0 := by
    intro x hxKG
    have hval : P₁ x = D₁.forward.pullback x := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₁apply x hxKG w, D₁.forward.pullback_apply x (hKGU hxKG) w]
    unfold metricTensorErrorNorm
    rw [hval]
    exact D₁.forward.c0_small x (hKGU hxKG)
  have hG₁c0 : ∀ x ∈ KG, metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G₁) g x ≤ c0 := by
    intro x hx
    rw [← hPG₁]
    exact hc0T x hx
  have hEqG₁ := inner_le_of_c0 (I := I) G₁ g hG₁c0
  set δ₀ := D₁.forward.pullback - Tensor0SBundle.metricTensorField (I := I) g with hδ₀def
  set δ₁ := P'' - P₁ with hδ₁def
  set δN₂ := D₂.forward.pullback - Tensor0SBundle.metricTensorField (I := I) h with hδN₂def
  haveI : SecondCountableTopology H := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H M
  haveI : LocallyCompactSpace (V : Set M) := V.2.locallyCompactSpace
  haveI : SigmaCompactSpace (V : Set M) := inferInstance
  have hδ₁pt : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      δ₁ x v = δN₂ ((Φ : M → N) x)
        (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
    intro x hxV v
    have hxKG : x ∈ KG := hVKG hxV
    have hxU : x ∈ (U₁ : Set M) := hKGU hxKG
    have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) :=
      himg (Set.mem_image_of_mem _ hxU)
    have hL : δ₁ x v = P'' x v - P₁ x v := by
      simp [hδ₁def, ContMDiffSection.coe_sub, Pi.sub_apply]
    have hR : δN₂ ((Φ : M → N) x) (fun q => mfderiv I I (Φ : M → N) x (v q))
        = D₂.forward.pullback ((Φ : M → N) x)
            (fun q => mfderiv I I (Φ : M → N) x (v q))
          - Tensor0SBundle.metricTensorField (I := I) h ((Φ : M → N) x)
              (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
      simp [hδN₂def, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hL, hR, hP''apply x hxKG v, hP₁apply x hxKG v,
      D₂.forward.pullback_apply ((Φ : M → N) x) hΦxK₂
        (fun q => mfderiv I I (Φ : M → N) x (v q)),
      Tensor0SBundle.metricTensorField_apply]
    rw [hchain x hxU (v 0), hchain x hxU (v 1)]
    rfl
  have hG₁V : ∀ x ∈ (V : Set M), ∀ v w : TangentSpace I x,
      G₁.inner x v w = h.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w) :=
    fun x hx v w => hG₁inner x (hVKG hx) v w
  haveI : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H N
  haveI : LocallyCompactSpace ((Φ : M → N) '' (V : Set M) : Set N) :=
    (image_opens_isOpen (I := I) Φ
      (fun y hy => hU₁ (hKGU (hVKG hy)))).locallyCompactSpace
  haveI : SigmaCompactSpace ((Φ : M → N) '' (V : Set M) : Set N) := inferInstance
  have hδ₁tow : ∀ (hNV : Nonempty V) (a : ℕ) (x : M) (hx : x ∈ (V : Set M)),
      tensor02CovDerivNormWith (I := I) a δ₁ G₁ G₁ x
        = tensor02CovDerivNormWith (I := I) a δN₂ h h ((Φ : M → N) x) := by
    intro hNV a x hx
    exact covNormWith_pd_zone (I := I) Φ (V := V)
      (fun y hy => hU₁ (hKGU (hVKG hy))) h δN₂ δ₁ G₁ hδ₁pt hG₁V a x hx
  have hgpt : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      Tensor0SBundle.metricTensorField (I := I) g x v
        = D₁.reverse.pullback ((Φ : M → N) x)
            (fun q => mfderiv I I (Φ : M → N) x (v q)) := by
    intro x hxV v
    have hxU : x ∈ (U₁ : Set M) := hKGU (hVKG hxV)
    have hxs : x ∈ Φ.source := hU₁ hxU
    have hΦxImg : (Φ : M → N) x ∈ (Φ : M → N) '' (U₁ : Set M) :=
      Set.mem_image_of_mem _ hxU
    have hfg : (Φ.symm : N → M) ∘ (Φ : M → N) =ᶠ[nhds x] id := by
      filter_upwards [Φ.open_source.mem_nhds hxs] with y hy
      exact Φ.left_inv' hy
    have hΦd : MDifferentiableAt I I (Φ : M → N) x :=
      ((Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hxs))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ : M → N) x) :=
      ((Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.symm.open_source.mem_nhds (Φ.map_source' hxs)))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp : (mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)).comp
        (mfderiv I I (Φ : M → N) x) = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      rw [← mfderiv_comp x hΦsd hΦd, hfg.mfderiv_eq]
      exact mfderiv_id
    have happ : ∀ w : TangentSpace I x,
        mfderiv I I (Φ.symm : N → M) ((Φ : M → N) x)
          (mfderiv I I (Φ : M → N) x w) = w := by
      intro w
      simpa using DFunLike.congr_fun hcomp w
    rw [D₁.reverse.pullback_apply ((Φ : M → N) x) hΦxImg
        (fun q => mfderiv I I (Φ : M → N) x (v q))]
    rw [Tensor0SBundle.metricTensorField_apply]
    have hl : (Φ.symm : N → M) ((Φ : M → N) x) = x := Φ.left_inv' hxs
    rw [happ (v 0), happ (v 1), hl]
  have hgKtow : ∀ (hNV : Nonempty V) (a : ℕ) (x : M) (hx : x ∈ (V : Set M)),
      tensor02CovDerivNormWith (I := I) a
          (Tensor0SBundle.metricTensorField (I := I) g) G₁ G₁ x
        = tensor02CovDerivNormWith (I := I) a D₁.reverse.pullback h h ((Φ : M → N) x) := by
    intro hNV a x hx
    exact covNormWith_pd_zone (I := I) Φ (V := V)
      (fun y hy => hU₁ (hKGU (hVKG hy))) h D₁.reverse.pullback
      (Tensor0SBundle.metricTensorField (I := I) g) G₁ hgpt hG₁V a x hx
  have hc0_nonneg : 0 ≤ c0 := D₁.forward.c0_nonneg
  have hc0'_nonneg : 0 ≤ c0' := D₂.forward.c0_nonneg
  have hden : 0 < 1 - c0 := by nlinarith
  have hc0_le_q : c0 ≤ q := by
    have hfrac_ge : c0 ≤ c0 / (1 - c0) := by
      rw [le_div_iff₀ hden]
      nlinarith [sq_nonneg c0]
    exact le_trans hfrac_ge hq_c0
  have hqden : c0 ≤ q * (1 - c0) := by
    rwa [div_le_iff₀ hden] at hq_c0
  have hequivF5 : ∀ x ∈ (V : Set M), ∀ v : TangentSpace I x,
      (1 + q)⁻¹ * G₁.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + q) * G₁.inner x v v := by
    intro x hxV v
    have hE := hEqG₁ x (hVKG hxV) v
    have hgnn : 0 ≤ g.inner x v v := metricInner_nonneg (I := I) g x v
    have h1q : 0 < 1 + q := by linarith
    constructor
    · rw [inv_mul_le_iff₀ h1q]
      calc G₁.inner x v v ≤ (1 + c0) * g.inner x v v := hE.2
        _ ≤ (1 + q) * g.inner x v v := by nlinarith
    · have hlow : (1 - c0) * g.inner x v v ≤ G₁.inner x v v := hE.1
      have hmul : (1 + q) * ((1 - c0) * g.inner x v v)
          ≤ (1 + q) * G₁.inner x v v :=
        mul_le_mul_of_nonneg_left hlow (le_of_lt h1q)
      have hone : g.inner x v v ≤ (1 + q) * ((1 - c0) * g.inner x v v) := by
        have hcoef : (1 : ℝ) ≤ (1 + q) * (1 - c0) := by
          nlinarith
        nlinarith
      linarith
  have hδ₀F5 : ∀ x ∈ (V : Set M), ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (2 + r)
        (iterCov (I := I) g 2 δ₀ r x)) ≤ q := by
    intro x hxV r hr0 hrp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hsub := iterCov_sub (I := I) g 2 D₁.forward.pullback
      (Tensor0SBundle.metricTensorField (I := I) g) (r' + 1)
    rw [hδ₀def, hsub, iterCov_metric_zero, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    rw [← t02Norm_eq_iterCov (I := I) D₁.forward.pullback g (r' + 1) basis hinv]
    calc tensor02CovDerivNormWith (I := I) (r' + 1) D₁.forward.pullback g g x
        ≤ cov := D₁.forward.cov_small (r' + 1) (by omega) hrp x (hKGU (hVKG hxV))
      _ ≤ q := hq_cov
  have hgKF5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + j)
        (iterCov (I := I) G₁ 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ q := by
    intro hNV x hxV j hj1 hjp
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₁ x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₁ basis hON
    rw [← t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) g) G₁ j basis hinv]
    rw [hgKtow hNV j x hxV]
    calc tensor02CovDerivNormWith (I := I) j D₁.reverse.pullback h h ((Φ : M → N) x)
        ≤ cov := D₁.reverse.cov_small j hj1 hjp ((Φ : M → N) x)
          (Set.mem_image_of_mem _ (hKGU (hVKG hxV)))
      _ ≤ q := hq_cov
  have hδ₁F5 : ∀ (hNV : Nonempty V), ∀ x ∈ (V : Set M), ∀ k : ℕ, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x (2 + k)
        (iterCov (I := I) G₁ 2 δ₁ k x)) ≤ e1 := by
    intro hNV x hxV k hkp
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₁ x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₁ basis hON
    rw [← t02Norm_eq_iterCov (I := I) δ₁ G₁ k basis hinv]
    rw [hδ₁tow hNV k x hxV]
    have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) :=
      himg (Set.mem_image_of_mem _ (hKGU (hVKG hxV)))
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hc0 := D₂.forward.c0_small ((Φ : M → N) x) hΦxK₂
      calc tensor02CovDerivNormWith (I := I) 0 δN₂ h h ((Φ : M → N) x)
          = metricTensorErrorNorm (I := I) D₂.forward.pullback h ((Φ : M → N) x) := by
            unfold tensor02CovDerivNormWith metricTensorErrorNorm
            congr 1
        _ ≤ c0' := hc0
        _ ≤ e1 := he1_c0
    · calc tensor02CovDerivNormWith (I := I) k δN₂ h h ((Φ : M → N) x)
          = tensor02CovDerivNormWith (I := I) k D₂.forward.pullback h h ((Φ : M → N) x) := by
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            have hfield : tensor02CovDeriv (I := I) δN₂ h (k' + 1)
                = tensor02CovDeriv (I := I) D₂.forward.pullback h (k' + 1) := by
              rw [hδN₂def, tensor02_eq_covDOF, tensor02_eq_covDOF, covDerivOfField_sub,
                covDerivOfField_eq_iterCov (I := I) h
                  (Tensor0SBundle.metricTensorField (I := I) h) (k' + 1),
                iterCov_metric_zero]
              simp
            unfold tensor02CovDerivNormWith
            rw [hfield]
        _ ≤ cov' := D₂.forward.cov_small k hk1 hkp ((Φ : M → N) x) hΦxK₂
        _ ≤ e1 := he1_cov
  have hCp := hC (M' := M) (u := (V : Set M)) V.2 g G₁ δ₀ δ₁ q e1
    hq0 hq1 he1_0
    hequivF5
    (fun x hx j hj1 hjp => hgKF5 ⟨⟨x, hx⟩⟩ x hx j hj1 hjp)
    hδ₀F5
    (fun x hx k hkp => hδ₁F5 ⟨⟨x, hx⟩⟩ x hx k hkp)
  have hgermz : ∀ (a : ℕ) (x : M), x ∈ (V : Set M) →
      ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) g (P₁ - D₁.forward.pullback) a x slots = 0 := by
    intro a x hxV slots
    haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hA0 : ∀ (q : V) (w : Fin 2 → TangentSpace I q),
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) 2) q w
          = (P₁ - D₁.forward.pullback) (q : M) w := by
      intro q w
      have hv : P₁ (q : M) w = D₁.forward.pullback (q : M) w := by
        rw [hP₁apply _ (hVKG q.2) w, D₁.forward.pullback_apply _ (hKGU (hVKG q.2)) w]
      simp [ContMDiffSection.coe_sub, Pi.sub_apply, hv]
    have hres := covDerivOfField_restrictOpen (I := I) g V
      (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) 2)
      (P₁ - D₁.forward.pullback) hA0 a ⟨x, hxV⟩ slots
    rw [← hres, covDOF_zero]
    simp
  have hcovP'' : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) a P'' g g x ≤ q + e1 * C := by
    intro a ha1 hap x hxK
    have hxV : x ∈ (V : Set M) := hKV hxK
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hgermzI : ∀ slots : Fin (2 + (a' + 1)) → TangentSpace I x,
        iterCov (I := I) g 2 (P₁ - D₁.forward.pullback) (a' + 1) x slots = 0 := by
      intro slots
      have hfe := covDerivOfField_eq_iterCov (I := I) g
        (P₁ - D₁.forward.pullback) (a' + 1)
      have hx1 := DFunLike.congr_fun hfe x
      have hx2 := DFunLike.congr_fun hx1
        (fun q => slots ((acEquiv (a' + 1)).symm q))
      change _ = (ContinuousMultilinearMap.domDomCongr
        (acEquiv (a' + 1)) _) _ at hx2
      rw [ContinuousMultilinearMap.domDomCongr_apply] at hx2
      have hslots : (fun q => slots ((acEquiv (a' + 1)).symm
          ((acEquiv (a' + 1)) q))) = slots := by
        funext q
        rw [Equiv.symm_apply_apply]
      rw [hslots] at hx2
      exact hx2.symm.trans (hgermz (a' + 1) x hxV _)
    have hdecI : iterCov (I := I) g 2 P'' (a' + 1) x
        = iterCov (I := I) g 2 (δ₀ + δ₁) (a' + 1) x := by
      have hsplit : (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E)
          (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
          = (P'' - Tensor0SBundle.metricTensorField (I := I) g)
            - (P₁ - D₁.forward.pullback) := by
        rw [hδ₀def, hδ₁def]
        abel
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      rw [hsplit, iterCov_sub, iterCov_sub, iterCov_metric_zero, sub_zero]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [Tensor0SBundle.Tensor0SSpace.sub_apply, hgermzI slots, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    rw [t02Norm_eq_iterCov (I := I) P'' g (a' + 1) basis hinv, hdecI]
    exact hCp x hxV (a' + 1) (by omega) hap
  have hc0P'' : ∀ x ∈ K,
      metricTensorErrorNorm (I := I) P'' g x ≤ c0 + c0' * (1 + q) := by
    intro x hxK
    have hxV : x ∈ (V : Set M) := hKV hxK
    have hxKG : x ∈ KG := hVKG hxV
    have h3 : P₁ x = D₁.forward.pullback x := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₁apply x hxKG w, D₁.forward.pullback_apply x (hKGU hxKG) w]
    have hval : P'' x - Tensor0SBundle.metricTensorField (I := I) g x
        = δ₀ x + δ₁ x := by
      simp only [hδ₀def, hδ₁def, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h3]
      abel
    unfold metricTensorErrorNorm
    rw [hval]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
    have htri := sqrt_normSq0S_add_le (I := I) g (δ₀ x) (δ₁ x) basis hinv
    have ht0 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x)) ≤ c0 := by
      have hc := D₁.forward.c0_small x (hKGU hxKG)
      unfold metricTensorErrorNorm at hc
      have h1 : δ₀ x = D₁.forward.pullback x
          - Tensor0SBundle.metricTensorField (I := I) g x := by
        simp [hδ₀def, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h1]
      exact hc
    have ht1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
        ≤ (1 + q) * c0' := by
      have hMUE : MetricUniformEquivalentOn (I := I) (V : Set M) G₁ g (1 + q) :=
        ⟨by linarith, fun y hy v => hequivF5 y hy v⟩
      have hcompn := sqrt_normSq_two_le (I := I) hMUE hxV (δ₁ x)
      have hG₁δ : Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) ≤ c0' := by
        change tensor02CovDerivNormWith (I := I) 0 δ₁ G₁ G₁ x ≤ c0'
        rw [hδ₁tow ⟨⟨x, hxV⟩⟩ 0 x hxV]
        have hΦxK₂ : (Φ : M → N) x ∈ (K₂ : Set N) :=
          himg (Set.mem_image_of_mem _ (hKGU hxKG))
        have hc := D₂.forward.c0_small ((Φ : M → N) x) hΦxK₂
        calc tensor02CovDerivNormWith (I := I) 0 δN₂ h h ((Φ : M → N) x)
            = metricTensorErrorNorm (I := I) D₂.forward.pullback h ((Φ : M → N) x) := by
              unfold tensor02CovDerivNormWith metricTensorErrorNorm
              congr 1
          _ ≤ c0' := hc
      have hsq : Real.sqrt ((1 + q) ^ 2) = 1 + q := by
        rw [Real.sqrt_sq (by linarith)]
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x))
          ≤ Real.sqrt ((1 + q) ^ 2)
            * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := hcompn
        _ = (1 + q) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₁ x 2 (δ₁ x)) := by
            rw [hsq]
        _ ≤ (1 + q) * c0' := mul_le_mul_of_nonneg_left hG₁δ (by linarith)
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x + δ₁ x))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₀ x))
          + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 (δ₁ x)) := htri
      _ ≤ c0 + (1 + q) * c0' := add_le_add ht0 ht1
      _ = c0 + c0' * (1 + q) := by ring
  have hc0''0 : 0 ≤ c0'' := by
    have hbase : 0 ≤ c0 + c0' * (1 + q) := by
      nlinarith
    exact le_trans hbase hc0_out
  have hcov''0 : 0 ≤ cov'' := by
    have hbase : 0 ≤ q + e1 * C := add_nonneg hq0 (mul_nonneg he1_0 hC0)
    exact le_trans hbase hcov_out
  exact
    { c0_nonneg := hc0''0
      cov_nonneg := hcov''0
      smoothOn := Ψ.contMDiffOn_toFun.mono hKsrc
      pullback := P''
      pullback_apply := fun x hx v => hP''apply x (hVKG (hKV hx)) v
      c0_small := fun x hx => le_trans (hc0P'' x hx) hc0_out
      cov_small := fun a h1 h2 x hx => le_trans (hcovP'' a h1 h2 x hx) hcov_out }

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in





noncomputable def compSepRev [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {P : Type u} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    [T2Space N] [SigmaCompactSpace N] [T2Space P] [SigmaCompactSpace P]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [IsManifold I 1 P] [IsManifold I 2 P] [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {U₁ : Opens M} [Nonempty U₁] (hU₁ : (U₁ : Set M) ⊆ Φ.source)
    {K₂ : Opens N} [Nonempty K₂] (hK₂ : (K₂ : Set N) ⊆ Φ'.source)
    (himg : (Φ : M → N) '' (U₁ : Set M) ⊆ (K₂ : Set N))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U₁ : Set M))
    {c0 cov c0' cov' q e1 c0'' cov'' : Real} {p : Nat}
    (hc0'_half : c0' ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hq_c0 : c0' / (1 - c0') ≤ q) (hq_cov : cov' ≤ q)
    (he1_0 : 0 ≤ e1) (he1_c0 : c0 ≤ e1) (he1_cov : cov ≤ e1)
    (C : Real) (hC0 : 0 ≤ C)
    (hc0_out : c0' + c0 * (1 + q) ≤ c0'')
    (hcov_out : q + e1 * C ≤ cov'')
    (hC : ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
      [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
      [IsManifold I 1 M'] [IsManifold I 2 M']
      [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
      {u : Set M'}, IsOpen u →
      ∀ (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2
              (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoSep (I := I) (U₁ : Set M) c0 cov p Φ g h)
    (D₂ : BookApproxIsoSep (I := I) (K₂ : Set N) c0' cov' p Φ' h h') :
    PreApproxIsoSep (I := I)
      ((PartialDiffeomorph.trans (I := I) Φ Φ' : M → P) '' K)
      c0'' cov'' p
      ((PartialDiffeomorph.trans (I := I) Φ Φ').symm : P → M) h' g := by
  classical
  set Ψ := PartialDiffeomorph.trans (I := I) Φ Φ' with hΨdef
  have hsrcU : (U₁ : Set M) ⊆ Ψ.source := by
    intro y hy
    exact ⟨hU₁ hy, hK₂ (himg (Set.mem_image_of_mem _ hy))⟩
  have hKsrc : K ⊆ Ψ.source := fun y hy => hsrcU (hKU hy)
  haveI : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let KG : Set M := Classical.choose (exists_compact_between hK U₁.2 hKU)
  have hKGspec := Classical.choose_spec (exists_compact_between hK U₁.2 hKU)
  have hKGcpt : IsCompact KG := hKGspec.1
  have hKKG : K ⊆ interior KG := hKGspec.2.1
  have hKGU : KG ⊆ (U₁ : Set M) := hKGspec.2.2
  set V : Opens M := ⟨interior KG, isOpen_interior⟩ with hVdef
  have hKV : K ⊆ (V : Set M) := hKKG
  have hVKG : (V : Set M) ⊆ KG := interior_subset
  have hΨcont : ContinuousOn (Ψ : M → P) KG :=
    Ψ.contMDiffOn_toFun.continuousOn.mono (fun y hy => hsrcU (hKGU hy))
  have hΨKG_cpt : IsCompact ((Ψ : M → P) '' KG) := hKGcpt.image_of_continuousOn hΨcont
  have hΨKG_tgt : (Ψ : M → P) '' KG ⊆ Ψ.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact Ψ.map_source' (hsrcU (hKGU hy))
  let pullRev := exists_pullbackField (I := I) Ψ.symm hΨKG_cpt hΨKG_tgt g h'
  let Pr := Classical.choose pullRev
  let Gr := Classical.choose (Classical.choose_spec pullRev)
  have hPrspec := Classical.choose_spec (Classical.choose_spec pullRev)
  have hPGr : Pr = Tensor0SBundle.metricTensorField (I := I) Gr := hPrspec.1
  have hGrinner : ∀ y ∈ (Ψ : M → P) '' KG, ∀ v w : TangentSpace I y,
      Gr.inner y v w = g.inner ((Ψ.symm : P → M) y)
        (mfderiv I I (Ψ.symm : P → M) y v) (mfderiv I I (Ψ.symm : P → M) y w) :=
    hPrspec.2.1
  have hPrapply : ∀ y ∈ (Ψ : M → P) '' KG, ∀ v : Fin 2 → TangentSpace I y,
      Pr y v = g.inner ((Ψ.symm : P → M) y)
        (mfderiv I I (Ψ.symm : P → M) y (v 0))
        (mfderiv I I (Ψ.symm : P → M) y (v 1)) :=
    hPrspec.2.2
  have hKimg : (Ψ : M → P) '' K ⊆ (Ψ : M → P) '' KG :=
    Set.image_mono (fun y hy => hVKG (hKV hy))
  have hVsrc : (V : Set M) ⊆ Ψ.source := fun y hy => hsrcU (hKGU (hVKG hy))
  set VP : Opens P := ⟨(Ψ : M → P) '' (V : Set M), image_opens_isOpen (I := I) Ψ hVsrc⟩
    with hVPdef
  have hVPKG : (VP : Set P) ⊆ (Ψ : M → P) '' KG := Set.image_mono hVKG
  have hΨKG_tgt' : (Ψ : M → P) '' KG ⊆ Φ'.symm.source := by
    rintro _ ⟨y, hy, rfl⟩
    have : (Φ : M → N) y ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ (hKGU hy))
    exact Φ'.map_source' (hK₂ this)
  let pullMid := exists_pullbackField (I := I) Φ'.symm hΨKG_cpt hΨKG_tgt' h h'
  let P₂r := Classical.choose pullMid
  let G₂r := Classical.choose (Classical.choose_spec pullMid)
  have hP₂rspec := Classical.choose_spec (Classical.choose_spec pullMid)
  have hPG₂r : P₂r = Tensor0SBundle.metricTensorField (I := I) G₂r := hP₂rspec.1
  have hG₂rinner : ∀ y ∈ (Ψ : M → P) '' KG, ∀ v w : TangentSpace I y,
      G₂r.inner y v w = h.inner ((Φ'.symm : P → N) y)
        (mfderiv I I (Φ'.symm : P → N) y v)
        (mfderiv I I (Φ'.symm : P → N) y w) :=
    hP₂rspec.2.1
  have hP₂rapply : ∀ y ∈ (Ψ : M → P) '' KG, ∀ v : Fin 2 → TangentSpace I y,
      P₂r y v = h.inner ((Φ'.symm : P → N) y)
        (mfderiv I I (Φ'.symm : P → N) y (v 0))
        (mfderiv I I (Φ'.symm : P → N) y (v 1)) :=
    hP₂rspec.2.2
  set δ₀r := D₂.reverse.pullback - Tensor0SBundle.metricTensorField (I := I) h'
    with hδ₀rdef
  set δ₁r := Pr - P₂r with hδ₁rdef
  set δN₁r := D₁.reverse.pullback - Tensor0SBundle.metricTensorField (I := I) h
    with hδN₁rdef
  have hVPimgK₂ : ∀ y ∈ (VP : Set P), (Φ'.symm : P → N) y ∈ (K₂ : Set N) ∧
      (Φ'.symm : P → N) y ∈ (Φ : M → N) '' (U₁ : Set M) ∧ y ∈ Φ'.target := by
    rintro y ⟨m, hm, rfl⟩
    have hmU : m ∈ (U₁ : Set M) := hKGU (hVKG hm)
    have hΦm : (Φ : M → N) m ∈ (K₂ : Set N) := himg (Set.mem_image_of_mem _ hmU)
    have hyt : ((Ψ : M → P) m) ∈ Φ'.target := by
      have : (Ψ : M → P) m = (Φ' : N → P) ((Φ : M → N) m) := rfl
      rw [this]
      exact Φ'.map_source' (hK₂ hΦm)
    have hsymm : (Φ'.symm : P → N) ((Ψ : M → P) m) = (Φ : M → N) m := by
      have : (Ψ : M → P) m = (Φ' : N → P) ((Φ : M → N) m) := rfl
      rw [this]
      exact Φ'.left_inv' (hK₂ hΦm)
    refine ⟨?_, ?_, hyt⟩
    · rw [hsymm]; exact hΦm
    · rw [hsymm]; exact Set.mem_image_of_mem _ hmU
  have hc0Tr : ∀ y ∈ (VP : Set P),
      metricTensorErrorNorm (I := I) P₂r h' y ≤ c0' := by
    intro y hyVP
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyKG : y ∈ (Ψ : M → P) '' KG := hVPKG hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) := by
      refine ⟨(Φ'.symm : P → N) y, hyK₂, ?_⟩
      exact Φ'.right_inv' hyt
    have hval : P₂r y = D₂.reverse.pullback y := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₂rapply y hyKG w, D₂.reverse.pullback_apply y hyΦ'K₂ w]
    unfold metricTensorErrorNorm
    rw [hval]
    exact D₂.reverse.c0_small y hyΦ'K₂
  have hG₂rc0 : ∀ y ∈ (VP : Set P), metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G₂r) h' y ≤ c0' := by
    intro y hy
    rw [← hPG₂r]
    exact hc0Tr y hy
  have hEqG₂r := inner_le_of_c0 (I := I) G₂r h' hG₂rc0
  have hchainr : ∀ y ∈ (VP : Set P), ∀ v : TangentSpace I y,
      mfderiv I I (Ψ.symm : P → M) y v
        = mfderiv I I (Φ.symm : N → M) ((Φ'.symm : P → N) y)
            (mfderiv I I (Φ'.symm : P → N) y v) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hΦ'sd : MDifferentiableAt I I (Φ'.symm : P → N) y :=
      (Φ'.symm.contMDiffOn_toFun.contMDiffAt
        (Φ'.symm.open_source.mem_nhds hyt)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦst : (Φ'.symm : P → N) y ∈ Φ.target := by
      obtain ⟨m, hmU, hmeq⟩ := hyU₁img
      rw [← hmeq]
      exact Φ.map_source' (hU₁ hmU)
    have hΦsd : MDifferentiableAt I I (Φ.symm : N → M) ((Φ'.symm : P → N) y) :=
      (Φ.symm.contMDiffOn_toFun.contMDiffAt
        (Φ.symm.open_source.mem_nhds hΦst)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have h := mfderiv_comp y hΦsd hΦ'sd
    have happ := DFunLike.congr_fun h v
    simpa [ContinuousLinearMap.comp_apply] using happ
  have hδ₁rpt : ∀ y ∈ (VP : Set P), ∀ v : Fin 2 → TangentSpace I y,
      δ₁r y v = δN₁r ((Φ'.symm : P → N) y)
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyKG : y ∈ (Ψ : M → P) '' KG := hVPKG hyVP
    have hL : δ₁r y v = Pr y v - P₂r y v := by
      simp [hδ₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
    have hR : δN₁r ((Φ'.symm : P → N) y)
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))
        = D₁.reverse.pullback ((Φ'.symm : P → N) y)
            (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))
          - Tensor0SBundle.metricTensorField (I := I) h ((Φ'.symm : P → N) y)
              (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
      simp [hδN₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
    rw [hL, hR, hPrapply y hyKG v, hP₂rapply y hyKG v,
      D₁.reverse.pullback_apply ((Φ'.symm : P → N) y) hyU₁img
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)),
      Tensor0SBundle.metricTensorField_apply]
    rw [hchainr y hyVP (v 0), hchainr y hyVP (v 1)]
    rfl
  have hG₂rV : ∀ y ∈ (VP : Set P), ∀ v w : TangentSpace I y,
      G₂r.inner y v w = h.inner ((Φ'.symm : P → N) y)
        (mfderiv I I (Φ'.symm : P → N) y v)
        (mfderiv I I (Φ'.symm : P → N) y w) :=
    fun y hy v w => hG₂rinner y (hVPKG hy) v w
  haveI : SecondCountableTopology H := I.secondCountableTopology
  haveI : LocallyCompactSpace P := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H P
  haveI : LocallyCompactSpace (VP : Set P) := VP.2.locallyCompactSpace
  haveI : SigmaCompactSpace (VP : Set P) := inferInstance
  haveI : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional I
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H N
  haveI : LocallyCompactSpace ((Φ'.symm : P → N) '' (VP : Set P) : Set N) :=
    (image_opens_isOpen (I := I) Φ'.symm
      (fun y hy => (hVPimgK₂ y hy).2.2)).locallyCompactSpace
  haveI : SigmaCompactSpace ((Φ'.symm : P → N) '' (VP : Set P) : Set N) := inferInstance
  have hδ₁rtow : ∀ (hNVP : Nonempty VP) (a : ℕ) (y : P) (hy : y ∈ (VP : Set P)),
      tensor02CovDerivNormWith (I := I) a δ₁r G₂r G₂r y
        = tensor02CovDerivNormWith (I := I) a δN₁r h h ((Φ'.symm : P → N) y) := by
    intro hNVP a y hy
    exact covNormWith_pd_zone (I := I) Φ'.symm (V := VP)
      (fun z hz => (hVPimgK₂ z hz).2.2) h δN₁r δ₁r G₂r hδ₁rpt hG₂rV a y hy
  have hgptr : ∀ y ∈ (VP : Set P), ∀ v : Fin 2 → TangentSpace I y,
      Tensor0SBundle.metricTensorField (I := I) h' y v
        = D₂.forward.pullback ((Φ'.symm : P → N) y)
            (fun q => mfderiv I I (Φ'.symm : P → N) y (v q)) := by
    intro y hyVP v
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hfg : (Φ' : N → P) ∘ (Φ'.symm : P → N) =ᶠ[nhds y] id := by
      filter_upwards [Φ'.open_target.mem_nhds hyt] with z hz
      exact Φ'.right_inv' hz
    have hΦ'sd : MDifferentiableAt I I (Φ'.symm : P → N) y :=
      (Φ'.symm.contMDiffOn_toFun.contMDiffAt
        (Φ'.symm.open_source.mem_nhds hyt)).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦ'd : MDifferentiableAt I I (Φ' : N → P) ((Φ'.symm : P → N) y) :=
      (Φ'.contMDiffOn_toFun.contMDiffAt
        (Φ'.open_source.mem_nhds (Φ'.map_target' hyt))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp : (mfderiv I I (Φ' : N → P) ((Φ'.symm : P → N) y)).comp
        (mfderiv I I (Φ'.symm : P → N) y) = ContinuousLinearMap.id ℝ (TangentSpace I y) := by
      rw [← mfderiv_comp y hΦ'd hΦ'sd, hfg.mfderiv_eq]
      exact mfderiv_id
    have happ : ∀ w : TangentSpace I y,
        mfderiv I I (Φ' : N → P) ((Φ'.symm : P → N) y)
          (mfderiv I I (Φ'.symm : P → N) y w) = w := by
      intro w
      simpa using DFunLike.congr_fun hcomp w
    rw [D₂.forward.pullback_apply ((Φ'.symm : P → N) y) hyK₂
        (fun q => mfderiv I I (Φ'.symm : P → N) y (v q))]
    rw [Tensor0SBundle.metricTensorField_apply]
    have hr : (Φ' : N → P) ((Φ'.symm : P → N) y) = y := Φ'.right_inv' hyt
    rw [happ (v 0), happ (v 1), hr]
  have hgKrtow : ∀ (hNVP : Nonempty VP) (a : ℕ) (y : P) (hy : y ∈ (VP : Set P)),
      tensor02CovDerivNormWith (I := I) a
          (Tensor0SBundle.metricTensorField (I := I) h') G₂r G₂r y
        = tensor02CovDerivNormWith (I := I) a D₂.forward.pullback h h
            ((Φ'.symm : P → N) y) := by
    intro hNVP a y hy
    exact covNormWith_pd_zone (I := I) Φ'.symm (V := VP)
      (fun z hz => (hVPimgK₂ z hz).2.2) h D₂.forward.pullback
      (Tensor0SBundle.metricTensorField (I := I) h') G₂r hgptr hG₂rV a y hy
  have hc0'_nonneg : 0 ≤ c0' := D₂.forward.c0_nonneg
  have hc0_nonneg : 0 ≤ c0 := D₁.forward.c0_nonneg
  have hden : 0 < 1 - c0' := by nlinarith
  have hc0'_le_q : c0' ≤ q := by
    have hfrac_ge : c0' ≤ c0' / (1 - c0') := by
      rw [le_div_iff₀ hden]
      nlinarith [sq_nonneg c0']
    exact le_trans hfrac_ge hq_c0
  have hqden : c0' ≤ q * (1 - c0') := by
    rwa [div_le_iff₀ hden] at hq_c0
  have hequivF5r : ∀ y ∈ (VP : Set P), ∀ v : TangentSpace I y,
      (1 + q)⁻¹ * G₂r.inner y v v ≤ h'.inner y v v ∧
        h'.inner y v v ≤ (1 + q) * G₂r.inner y v v := by
    intro y hy v
    have hE := hEqG₂r y hy v
    have hnn : 0 ≤ h'.inner y v v := metricInner_nonneg (I := I) h' y v
    have h1q : 0 < 1 + q := by linarith
    constructor
    · rw [inv_mul_le_iff₀ h1q]
      calc G₂r.inner y v v ≤ (1 + c0') * h'.inner y v v := hE.2
        _ ≤ (1 + q) * h'.inner y v v := by nlinarith
    · have hlow : (1 - c0') * h'.inner y v v ≤ G₂r.inner y v v := hE.1
      have hmul : (1 + q) * ((1 - c0') * h'.inner y v v)
          ≤ (1 + q) * G₂r.inner y v v :=
        mul_le_mul_of_nonneg_left hlow (le_of_lt h1q)
      have hone : h'.inner y v v ≤ (1 + q) * ((1 - c0') * h'.inner y v v) := by
        have hcoef : (1 : ℝ) ≤ (1 + q) * (1 - c0') := by
          nlinarith
        nlinarith
      linarith
  have hδ₀rF5 : ∀ y ∈ (VP : Set P), ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y (2 + r)
        (iterCov (I := I) h' 2 δ₀r r y)) ≤ q := by
    intro y hyVP r hr0 hrp
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) :=
      ⟨(Φ'.symm : P → N) y, hyK₂, Φ'.right_inv' hyt⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hsub := iterCov_sub (I := I) h' 2 D₂.reverse.pullback
      (Tensor0SBundle.metricTensorField (I := I) h') (r' + 1)
    rw [hδ₀rdef, hsub, iterCov_metric_zero, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    rw [← t02Norm_eq_iterCov (I := I) D₂.reverse.pullback h' (r' + 1) basis hinv]
    calc tensor02CovDerivNormWith (I := I) (r' + 1) D₂.reverse.pullback h' h' y
        ≤ cov' := D₂.reverse.cov_small (r' + 1) (by omega) hrp y hyΦ'K₂
      _ ≤ q := hq_cov
  have hgKrF5 : ∀ (hNVP : Nonempty VP), ∀ y ∈ (VP : Set P), ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y (2 + j)
        (iterCov (I := I) G₂r 2 (Tensor0SBundle.metricTensorField (I := I) h') j y))
        ≤ q := by
    intro hNVP y hyVP j hj1 hjp
    obtain ⟨hyK₂, _, _⟩ := hVPimgK₂ y hyVP
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₂r y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₂r basis hON
    rw [← t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) h') G₂r j basis hinv]
    rw [hgKrtow hNVP j y hyVP]
    calc tensor02CovDerivNormWith (I := I) j D₂.forward.pullback h h
          ((Φ'.symm : P → N) y)
        ≤ cov' := D₂.forward.cov_small j hj1 hjp ((Φ'.symm : P → N) y) hyK₂
      _ ≤ q := hq_cov
  have hδ₁rF5 : ∀ (hNVP : Nonempty VP), ∀ y ∈ (VP : Set P), ∀ k : ℕ, k ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y (2 + k)
        (iterCov (I := I) G₂r 2 δ₁r k y)) ≤ e1 := by
    intro hNVP y hyVP k hkp
    obtain ⟨hyK₂, hyU₁img, hyt⟩ := hVPimgK₂ y hyVP
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) G₂r y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) G₂r basis hON
    rw [← t02Norm_eq_iterCov (I := I) δ₁r G₂r k basis hinv]
    rw [hδ₁rtow hNVP k y hyVP]
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0
      have hc0 := D₁.reverse.c0_small ((Φ'.symm : P → N) y) hyU₁img
      calc tensor02CovDerivNormWith (I := I) 0 δN₁r h h ((Φ'.symm : P → N) y)
          = metricTensorErrorNorm (I := I) D₁.reverse.pullback h
              ((Φ'.symm : P → N) y) := by
            unfold tensor02CovDerivNormWith metricTensorErrorNorm
            congr 1
        _ ≤ c0 := hc0
        _ ≤ e1 := he1_c0
    · calc tensor02CovDerivNormWith (I := I) k δN₁r h h ((Φ'.symm : P → N) y)
          = tensor02CovDerivNormWith (I := I) k D₁.reverse.pullback h h
              ((Φ'.symm : P → N) y) := by
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
            have hfield : tensor02CovDeriv (I := I) δN₁r h (k' + 1)
                = tensor02CovDeriv (I := I) D₁.reverse.pullback h (k' + 1) := by
              rw [hδN₁rdef, tensor02_eq_covDOF, tensor02_eq_covDOF, covDerivOfField_sub,
                covDerivOfField_eq_iterCov (I := I) h
                  (Tensor0SBundle.metricTensorField (I := I) h) (k' + 1),
                iterCov_metric_zero]
              simp
            unfold tensor02CovDerivNormWith
            rw [hfield]
        _ ≤ cov := D₁.reverse.cov_small k hk1 hkp ((Φ'.symm : P → N) y) hyU₁img
        _ ≤ e1 := he1_cov
  have hCpr := hC (M' := P) (u := (VP : Set P)) VP.2 h' G₂r
    δ₀r δ₁r q e1 hq0 hq1 he1_0
    hequivF5r
    (fun y hy j hj1 hjp => hgKrF5 ⟨⟨y, hy⟩⟩ y hy j hj1 hjp)
    hδ₀rF5
    (fun y hy k hkp => hδ₁rF5 ⟨⟨y, hy⟩⟩ y hy k hkp)
  have hgermzr : ∀ (a : ℕ) (y : P), y ∈ (VP : Set P) →
      ∀ slots : Fin (a + 2) → TangentSpace I y,
      covDerivOfField (I := I) h' (P₂r - D₂.reverse.pullback) a y slots = 0 := by
    intro a y hyVP slots
    haveI : Nonempty VP := ⟨⟨y, hyVP⟩⟩
    have hA0 : ∀ (q : VP) (w : Fin 2 → TangentSpace I q),
        (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := VP) (n := (∞ : WithTop ℕ∞)) 2) q w
          = (P₂r - D₂.reverse.pullback) (q : P) w := by
      intro q w
      obtain ⟨hqK₂, _, hqt⟩ := hVPimgK₂ (q : P) q.2
      have hqΦ'K₂ : (q : P) ∈ (Φ' : N → P) '' (K₂ : Set N) :=
        ⟨(Φ'.symm : P → N) q, hqK₂, Φ'.right_inv' hqt⟩
      have hv : P₂r (q : P) w = D₂.reverse.pullback (q : P) w := by
        rw [hP₂rapply _ (hVPKG q.2) w, D₂.reverse.pullback_apply _ hqΦ'K₂ w]
      simp [ContMDiffSection.coe_sub, Pi.sub_apply, hv]
    have hres := covDerivOfField_restrictOpen (I := I) h' VP
      (0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := VP) (n := (∞ : WithTop ℕ∞)) 2)
      (P₂r - D₂.reverse.pullback) hA0 a ⟨y, hyVP⟩ slots
    rw [← hres, covDOF_zero]
    simp
  have hcovPr : ∀ a : ℕ, 1 ≤ a → a ≤ p → ∀ y ∈ (Ψ : M → P) '' K,
      tensor02CovDerivNormWith (I := I) a Pr h' h' y ≤ q + e1 * C := by
    intro a ha1 hap y hyK
    have hyVP : y ∈ (VP : Set P) := by
      obtain ⟨m, hm, rfl⟩ := hyK
      exact ⟨m, hKV hm, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hgermzrI : ∀ slots : Fin (2 + (a' + 1)) → TangentSpace I y,
        iterCov (I := I) h' 2 (P₂r - D₂.reverse.pullback) (a' + 1) y slots = 0 := by
      intro slots
      have hfe := covDerivOfField_eq_iterCov (I := I) h'
        (P₂r - D₂.reverse.pullback) (a' + 1)
      have hx1 := DFunLike.congr_fun hfe y
      have hx2 := DFunLike.congr_fun hx1
        (fun q => slots ((acEquiv (a' + 1)).symm q))
      change _ = (ContinuousMultilinearMap.domDomCongr
        (acEquiv (a' + 1)) _) _ at hx2
      rw [ContinuousMultilinearMap.domDomCongr_apply] at hx2
      have hslots : (fun q => slots ((acEquiv (a' + 1)).symm
          ((acEquiv (a' + 1)) q))) = slots := by
        funext q
        rw [Equiv.symm_apply_apply]
      rw [hslots] at hx2
      exact hx2.symm.trans (hgermzr (a' + 1) y hyVP _)
    have hdecI : iterCov (I := I) h' 2 Pr (a' + 1) y
        = iterCov (I := I) h' 2 (δ₀r + δ₁r) (a' + 1) y := by
      have hsplit : (δ₀r + δ₁r : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E)
          (H := H) (I := I) (M := P) (n := (∞ : WithTop ℕ∞)) 2)
          = (Pr - Tensor0SBundle.metricTensorField (I := I) h')
            - (P₂r - D₂.reverse.pullback) := by
        rw [hδ₀rdef, hδ₁rdef]
        abel
      refine ContinuousMultilinearMap.ext (fun slots => ?_)
      rw [hsplit, iterCov_sub, iterCov_sub, iterCov_metric_zero, sub_zero]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [Tensor0SBundle.Tensor0SSpace.sub_apply, hgermzrI slots, sub_zero]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    rw [t02Norm_eq_iterCov (I := I) Pr h' (a' + 1) basis hinv, hdecI]
    exact hCpr y hyVP (a' + 1) (by omega) hap
  have hc0Pr : ∀ y ∈ (Ψ : M → P) '' K,
      metricTensorErrorNorm (I := I) Pr h' y ≤ c0' + c0 * (1 + q) := by
    intro y hyK
    have hyVP : y ∈ (VP : Set P) := by
      obtain ⟨m, hm, rfl⟩ := hyK
      exact ⟨m, hKV hm, rfl⟩
    obtain ⟨hyK₂, _, hyt⟩ := hVPimgK₂ y hyVP
    have hyΦ'K₂ : y ∈ (Φ' : N → P) '' (K₂ : Set N) :=
      ⟨(Φ'.symm : P → N) y, hyK₂, Φ'.right_inv' hyt⟩
    have h3 : P₂r y = D₂.reverse.pullback y := by
      refine ContinuousMultilinearMap.ext (fun w => ?_)
      rw [hP₂rapply _ (hVPKG hyVP) w, D₂.reverse.pullback_apply _ hyΦ'K₂ w]
    have hval : Pr y - Tensor0SBundle.metricTensorField (I := I) h' y
        = δ₀r y + δ₁r y := by
      simp only [hδ₀rdef, hδ₁rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [← h3]
      abel
    unfold metricTensorErrorNorm
    rw [hval]
    obtain ⟨basis, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) h' y
    have hinv := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) h' basis hON
    have htri := sqrt_normSq0S_add_le (I := I) h' (δ₀r y) (δ₁r y) basis hinv
    have ht0 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y)) ≤ c0' := by
      have hc := D₂.reverse.c0_small y hyΦ'K₂
      unfold metricTensorErrorNorm at hc
      have h1 : δ₀r y = D₂.reverse.pullback y
          - Tensor0SBundle.metricTensorField (I := I) h' y := by
        simp [hδ₀rdef, ContMDiffSection.coe_sub, Pi.sub_apply]
      rw [h1]
      exact hc
    have ht1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y))
        ≤ (1 + q) * c0 := by
      have hMUE : MetricUniformEquivalentOn (I := I) (VP : Set P) G₂r h' (1 + q) :=
        ⟨by linarith, fun z hz v => hequivF5r z hz v⟩
      have hcompn := sqrt_normSq_two_le (I := I) hMUE hyVP (δ₁r y)
      have hG₂δ : Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) ≤ c0 := by
        change tensor02CovDerivNormWith (I := I) 0 δ₁r G₂r G₂r y ≤ c0
        rw [hδ₁rtow ⟨⟨y, hyVP⟩⟩ 0 y hyVP]
        have hc := D₁.reverse.c0_small ((Φ'.symm : P → N) y) (hVPimgK₂ y hyVP).2.1
        calc tensor02CovDerivNormWith (I := I) 0 δN₁r h h ((Φ'.symm : P → N) y)
            = metricTensorErrorNorm (I := I) D₁.reverse.pullback h
                ((Φ'.symm : P → N) y) := by
              unfold tensor02CovDerivNormWith metricTensorErrorNorm
              congr 1
          _ ≤ c0 := hc
      have hsq : Real.sqrt ((1 + q) ^ 2) = 1 + q := by
        rw [Real.sqrt_sq (by linarith)]
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y))
          ≤ Real.sqrt ((1 + q) ^ 2)
            * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) := hcompn
        _ = (1 + q) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) G₂r y 2 (δ₁r y)) := by
            rw [hsq]
        _ ≤ (1 + q) * c0 := mul_le_mul_of_nonneg_left hG₂δ (by linarith)
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y + δ₁r y))
        ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₀r y))
          + Real.sqrt (Tensor0SBundle.normSq0S (I := I) h' y 2 (δ₁r y)) := htri
      _ ≤ c0' + (1 + q) * c0 := add_le_add ht0 ht1
      _ = c0' + c0 * (1 + q) := by ring
  have hc0''0 : 0 ≤ c0'' := by
    have hbase : 0 ≤ c0' + c0 * (1 + q) := by
      nlinarith
    exact le_trans hbase hc0_out
  have hcov''0 : 0 ≤ cov'' := by
    have hbase : 0 ≤ q + e1 * C := add_nonneg hq0 (mul_nonneg he1_0 hC0)
    exact le_trans hbase hcov_out
  exact
    { c0_nonneg := hc0''0
      cov_nonneg := hcov''0
      smoothOn := Ψ.symm.contMDiffOn_toFun.mono
        (fun y hy => hΨKG_tgt (hKimg hy))
      pullback := Pr
      pullback_apply := fun y hy v => hPrapply y (hKimg hy) v
      c0_small := fun y hy => le_trans (hc0Pr y hy) hc0_out
      cov_small := fun a h1 h2 y hy => le_trans (hcovPr a h1 h2 y hy) hcov_out }

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in

noncomputable def sepData_comp [I.Boundaryless] [NeZero (Module.finrank Real E)]
    {P : Type u} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    [T2Space N] [SigmaCompactSpace N] [T2Space P] [SigmaCompactSpace P]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [IsManifold I 1 P] [IsManifold I 2 P] [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {U₁ : Opens M} [Nonempty U₁] (hU₁ : (U₁ : Set M) ⊆ Φ.source)
    {K₂ : Opens N} [Nonempty K₂] (hK₂ : (K₂ : Set N) ⊆ Φ'.source)
    (himg : (Φ : M → N) '' (U₁ : Set M) ⊆ (K₂ : Set N))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U₁ : Set M))
    {c0 cov c0' cov' qF eF qR eR c0'' cov'' : Real} {p : Nat}
    (hc0_half : c0 ≤ 1 / 2) (hc0'_half : c0' ≤ 1 / 2)
    (hqF0 : 0 ≤ qF) (hqF1 : qF ≤ 1)
    (hqF_c0 : c0 / (1 - c0) ≤ qF) (hqF_cov : cov ≤ qF)
    (heF0 : 0 ≤ eF) (heF_c0 : c0' ≤ eF) (heF_cov : cov' ≤ eF)
    (hqR0 : 0 ≤ qR) (hqR1 : qR ≤ 1)
    (hqR_c0 : c0' / (1 - c0') ≤ qR) (hqR_cov : cov' ≤ qR)
    (heR0 : 0 ≤ eR) (heR_c0 : c0 ≤ eR) (heR_cov : cov ≤ eR)
    (C : Real) (hC0 : 0 ≤ C)
    (hc0F_out : c0 + c0' * (1 + qF) ≤ c0'')
    (hcovF_out : qF + eF * C ≤ cov'')
    (hc0R_out : c0' + c0 * (1 + qR) ≤ c0'')
    (hcovR_out : qR + eR * C ≤ cov'')
    (hC : ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
      [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
      [IsManifold I 1 M'] [IsManifold I 2 M']
      [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
      {u : Set M'}, IsOpen u →
      ∀ (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2
              (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoSep (I := I) (U₁ : Set M) c0 cov p Φ g h)
    (D₂ : BookApproxIsoSep (I := I) (K₂ : Set N) c0' cov' p Φ' h h') :
    BookApproxIsoSep (I := I) K c0'' cov'' p
      (PartialDiffeomorph.trans (I := I) Φ Φ') g h' where
  source_sub := by
    intro y hy
    exact ⟨hU₁ (hKU hy), hK₂ (himg (Set.mem_image_of_mem _ (hKU hy)))⟩
  forward := compSepFwd (I := I) Φ Φ' hU₁ hK₂ himg hK hKU hc0_half
    hqF0 hqF1 hqF_c0 hqF_cov heF0 heF_c0 heF_cov C hC0 hc0F_out hcovF_out hC
    g h h' D₁ D₂
  reverse := compSepRev (I := I) Φ Φ' hU₁ hK₂ himg hK hKU hc0'_half
    hqR0 hqR1 hqR_c0 hqR_cov heR0 heR_c0 heR_cov C hC0 hc0R_out hcovR_out hC
    g h h' D₁ D₂

end PartialDataComp

section DataMono



def PreApproxIsoDataOn.mono [T2Space N] [SigmaCompactSpace N]
    {K K' : Set M} {ε ε' : ℝ} {p : ℕ}
    {Phi : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoDataOn (I := I) K ε p Phi g h)
    (hK : K' ⊆ K) (hε : ε ≤ ε') (hε1 : ε' < 1) :
    PreApproxIsoDataOn (I := I) K' ε' p Phi g h where
  eps_pos := lt_of_lt_of_le D.eps_pos hε
  eps_lt_one := hε1
  smoothOn := D.smoothOn.mono hK
  pullback := D.pullback
  pullback_apply := fun x hx v => D.pullback_apply x (hK hx) v
  c0_small := fun x hx => le_trans (D.c0_small x (hK hx)) hε
  cov_deriv_small := fun a h1 h2 x hx =>
    le_trans (D.cov_deriv_small a h1 h2 x (hK hx)) hε


def BookApproxIsoPartialData.mono [T2Space N] [SigmaCompactSpace N]
    {K K' : Set M} {ε ε' : ℝ} {p : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoPartialData (I := I) K ε p Phi g h)
    (hK : K' ⊆ K) (hε : ε ≤ ε') (hε1 : ε' < 1) :
    BookApproxIsoPartialData (I := I) K' ε' p Phi g h where
  source_sub := fun _ hx => D.source_sub (hK hx)
  forward := D.forward.mono hK hε hε1
  reverse := (D.reverse.mono (Set.image_mono hK) hε hε1 :)



def PreApproxIsoDataOn.monoP [T2Space N] [SigmaCompactSpace N]
    {K : Set M} {ε : ℝ} {p p' : ℕ}
    {Phi : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoDataOn (I := I) K ε p Phi g h) (hp : p' ≤ p) :
    PreApproxIsoDataOn (I := I) K ε p' Phi g h where
  eps_pos := D.eps_pos
  eps_lt_one := D.eps_lt_one
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := D.c0_small
  cov_deriv_small := fun a h1 h2 x hx =>
    D.cov_deriv_small a h1 (le_trans h2 hp) x hx


def BookApproxIsoPartialData.monoP [T2Space N] [SigmaCompactSpace N]
    {K : Set M} {ε : ℝ} {p p' : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoPartialData (I := I) K ε p Phi g h) (hp : p' ≤ p) :
    BookApproxIsoPartialData (I := I) K ε p' Phi g h where
  source_sub := D.source_sub
  forward := D.forward.monoP hp
  reverse := D.reverse.monoP hp

end DataMono

end HCGCompactness
end DifferentialGeometry
