import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormRestrict
import DifferentialGeometry.Geometry.Curvature.RestrictOpenRm04
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core

set_option autoImplicit false
set_option linter.style.longLine false



















noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn MetricVariationEquationOn
  ricciNorm SolutionFamily RicciAtFamily)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I 2 M]







omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciTensor_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (v w : TangentSpace I x) :
    ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x v w
      = ricciTensor (I := I) (M := M) g (x : M) v w := by
  classical
  obtain ⟨B, hB⟩ := exists_gOrthonormalBasis (I := I) (M := M) g (x : M)
  have hBU : ∀ i j,
      (g.restrictOpen (I := I) U).inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    exact hB i j
  rw [ricciTensor_eq_orthonormal_trace (I := I) (M := U) (g.restrictOpen (I := I) U) x v w B hBU,
    ricciTensor_eq_orthonormal_trace (I := I) (M := M) g (x : M) v w B hB]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [(g.restrictOpen (I := I) U).symm x
        (riemannOp (LeviCivita (I := I) (g.restrictOpen (I := I) U)) x (B i) v w) (B i),
    ← metricRm04StdAt_eq_inner_riemannOp (I := I) (M := U) (g.restrictOpen (I := I) U)
        x (B i) v w (B i),
    metricRm04StdAt_restrictOpen (I := I) g U x (B i) v w (B i),
    metricRm04StdAt_eq_inner_riemannOp (I := I) (M := M) g (x : M) (B i) v w (B i),
    g.symm (x : M) (B i) (riemannOp (LeviCivita (I := I) g) (x : M) (B i) v w)]



omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricRicci_restrictOpen_eval
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (slots : Fin 2 → TangentSpace I x) :
    metricRicci (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRicci (I := I) (M := M) g (x : M) slots := by
  have hLHS : metricRicci (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (slots 0) (slots 1) := by
    have hcmm : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
        = metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x (vec2 (slots 0) (slots 1)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [metricRicci_apply, hcmm]
    exact metricRicciAt_apply_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (slots 0) (slots 1)
  have hRHS : metricRicci (I := I) (M := M) g (x : M) slots
      = ricciTensor (I := I) (M := M) g (x : M) (slots 0) (slots 1) := by
    have hcmm : metricRicciAt (I := I) (M := M) g (x : M) slots
        = metricRicciAt (I := I) (M := M) g (x : M) (vec2 (slots 0) (slots 1)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [metricRicci_apply, hcmm]
    exact metricRicciAt_apply_eq_ricciTensor (I := I) g (x : M) (slots 0) (slots 1)
  rw [hLHS, hRHS]
  exact ricciTensor_restrictOpen (I := I) g U x (slots 0) (slots 1)




omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricScalarAt_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) :
    metricScalarAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
      = metricScalarAt (I := I) (M := M) g (x : M) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) (M := M) g (x : M)
  have hONU : ∀ i j,
      (g.restrictOpen (I := I) U).inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    exact hON i j
  have hinvU : MetricInverseInBasis_gen (I := I) (M := U) (g.restrictOpen (I := I) U) x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) (M := U) (g.restrictOpen (I := I) U) basis hONU
  have hinvM : MetricInverseInBasis_gen (I := I) (M := M) g (x : M) basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) (M := M) g basis hON
  rw [metricScalarAt_def, metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis (I := I) (M := U) (g.restrictOpen (I := I) U) basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinvU
      (metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x),
    metricTracePair0SAt_eq_sum_basis (I := I) (M := M) g basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinvM
      (metricRicciAt (I := I) (M := M) g (x : M))]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have e1 : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x (vec2 (basis i) (basis j))
      = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (basis i) (basis j) :=
    metricRicciAt_apply_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (basis i) (basis j)
  have e2 : metricRicciAt (I := I) (M := M) g (x : M) (vec2 (basis i) (basis j))
      = ricciTensor (I := I) (M := M) g (x : M) (basis i) (basis j) :=
    metricRicciAt_apply_eq_ricciTensor (I := I) g (x : M) (basis i) (basis j)
  have hric : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
        (vec2 (basis i) (basis j))
      = metricRicciAt (I := I) (M := M) g (x : M) (vec2 (basis i) (basis j)) := by
    rw [e1, e2]
    exact ricciTensor_restrictOpen (I := I) g U x (basis i) (basis j)
  exact congrArg (fun r => identityInvMetric i j * r) hric






omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricRm04_restrictOpen_eval
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04 (I := I) (M := M) g (x : M) slots := by
  have hLHS : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04StdAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    have hcmm : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
        = metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x
            (vec4 (slots 0) (slots 1) (slots 2) (slots 3)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [hcmm, metricRm04_apply]
    exact (metricRm04StdAt_apply (I := I) (M := U) (g.restrictOpen (I := I) U) x
      (slots 0) (slots 1) (slots 2) (slots 3)).symm
  have hRHS : metricRm04 (I := I) (M := M) g (x : M) slots
      = metricRm04StdAt (I := I) (M := M) g (x : M)
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    have hcmm : metricRm04 (I := I) (M := M) g (x : M) slots
        = metricRm04 (I := I) (M := M) g (x : M)
            (vec4 (slots 0) (slots 1) (slots 2) (slots 3)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [hcmm, metricRm04_apply]
    exact (metricRm04StdAt_apply (I := I) (M := M) g (x : M)
      (slots 0) (slots 1) (slots 2) (slots 3)).symm
  rw [hLHS, hRHS]
  exact metricRm04StdAt_restrictOpen (I := I) g U x (slots 0) (slots 1) (slots 2) (slots 3)








variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}


def solutionOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] :
    SolutionOn (I := I) (M := U) D where
  base := { metric := fun t => (S.base.metric t).restrictOpen (I := I) U }

open Classical in



omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] [IsManifold I 2 M] in
theorem restrictOpenPush_contMDiffWithinAt
    {Idx : Type} (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {frame : Idx → (x : U) → TangentSpace I x} {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i : Idx) (x : U) (hxu : x ∈ u) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (if h : y ∈ U then frame i ⟨y, h⟩ else 0)) (Subtype.val '' u) (x : M) := by
  haveI : Inhabited U := ⟨x⟩

  set cor : M → U := fun y => if h : y ∈ U then ⟨y, h⟩ else default with hcor_def


  have hcorval : ∀ z : U, cor (z : M) = z := by
    intro z; rw [hcor_def]; simp only [dif_pos z.2, Subtype.coe_eta]
  have hcor : ContMDiffAt I I (∞ : WithTop ℕ∞) cor (x : M) := by
    rw [← contMDiffAt_subtype_iff (I := I) (I' := I) (U := U) (n := ∞) (x := x)]
    have hid : (fun z : U => cor (z : M)) = id := by funext z; simpa using hcorval z
    rw [hid]
    exact contMDiffAt_id

  have hpush : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) u x :=
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).contMDiff_tangentMap
      (by simp)).contMDiffAt.comp_contMDiffWithinAt x (hframe.contMDiffOn i x hxu)

  have hmaps : Set.MapsTo cor (Subtype.val '' u) u := by
    rintro y ⟨z, hz, rfl⟩
    rw [hcorval z]; exact hz

  have hpush' : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) u (cor (x : M)) := by
    rw [hcorval x]; exact hpush

  have hgcor : ∀ z : M, (hz : z ∈ U) →
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) (cor z)
        = TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
            (if h : z ∈ U then frame i ⟨z, h⟩ else 0) := by
    intro z hz
    have hcz : cor z = ⟨z, hz⟩ := by simp only [hcor_def, dif_pos hz]
    rw [dif_pos hz, hcz]
    show tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) (⟨z, hz⟩ : U) (frame i ⟨z, hz⟩))
      = TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (frame i ⟨z, hz⟩)
    show TotalSpace.mk' E (E := fun w : M => TangentSpace I w) ((⟨z, hz⟩ : U) : M)
        (mfderiv I I (Subtype.val : U → M) (⟨z, hz⟩ : U) (frame i ⟨z, hz⟩))
      = TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (frame i ⟨z, hz⟩)
    rw [mfderiv_subtype_val_apply]

  refine (hpush'.comp (x : M) hcor.contMDiffWithinAt hmaps).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds ((U.isOpen).mem_nhds x.2)] with z hz
    exact (hgcor z hz).symm
  · exact (hgcor (x : M) x.2).symm

open Classical in






omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] [IsManifold I 2 M] in
theorem isLocalFrameOn_restrictOpenPush
    {Idx : Type} (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {frame : Idx → (x : U) → TangentSpace I x} {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) :
    IsLocalFrameOn (V := (TangentSpace I : M → Type _)) I E (∞ : WithTop ℕ∞)
      (fun i (y : M) => if h : y ∈ U then frame i ⟨y, h⟩ else 0) (Subtype.val '' u) where
  linearIndependent {y} hy := by
    obtain ⟨x, hxu, rfl⟩ := hy
    have hxU : (x : M) ∈ U := x.2
    have hval : (fun i => if h : (x : M) ∈ U then frame i ⟨(x : M), h⟩ else 0)
        = fun i => frame i x := by
      funext i; rw [dif_pos hxU]
    exact hval ▸ hframe.linearIndependent hxu
  generating {y} hy := by
    obtain ⟨x, hxu, rfl⟩ := hy
    have hxU : (x : M) ∈ U := x.2
    have hval : (fun i => if h : (x : M) ∈ U then frame i ⟨(x : M), h⟩ else 0)
        = fun i => frame i x := by
      funext i; rw [dif_pos hxU]
    exact hval ▸ hframe.generating hxu
  contMDiffOn i := by



    intro y hy
    obtain ⟨x, hxu, rfl⟩ := hy
    exact restrictOpenPush_contMDiffWithinAt (I := I) U hframe i x hxu







omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem frameCompSmooth_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {Idx : Type} [Fintype Idx] (frame : Idx → (x : U) → TangentSpace I x) {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × U =>
        ((solutionOn_restrictOpen (I := I) S U).family.metric p.1).inner p.2
          (frame i p.2) (frame j p.2))
      (D.regular ×ˢ u) := by
  classical

  set frameM : Idx → (y : M) → TangentSpace I y :=
    fun k (y : M) => if h : y ∈ U then frame k ⟨y, h⟩ else 0 with hframeM_def
  have hframeM : IsLocalFrameOn (V := (TangentSpace I : M → Type _)) I E (∞ : WithTop ℕ∞)
      frameM (Subtype.val '' u) := isLocalFrameOn_restrictOpenPush (I := I) U hframe
  have hpf := hS.smoothMetric.frameCompSmooth frameM hframeM i j

  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (∞ : WithTop ℕ∞)
      (fun p : ℝ × U => (p.1, (p.2 : M))) :=
    contMDiff_fst.prodMk ((contMDiff_subtype_val (I := I) (U := U)).comp contMDiff_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × U => (p.1, (p.2 : M)))
      (D.regular ×ˢ u) (D.regular ×ˢ (Subtype.val '' u)) :=
    fun p hp => ⟨hp.1, Set.mem_image_of_mem _ hp.2⟩
  have hcomp := hpf.comp hmap.contMDiffOn hmaps
  refine hcomp.congr ?_
  intro p hp
  have hxU : (p.2 : M) ∈ U := p.2.2
  have hval : ∀ k, frameM k (p.2 : M) = frame k p.2 := by
    intro k
    rw [hframeM_def]
    simp only [dif_pos hxU]
  simp only [Function.comp_apply, hval]
  rfl





omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem metricFamilySmoothOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    MetricFamilySmoothOn (I := I) D (solutionOn_restrictOpen (I := I) S U).family where
  coeff x X Y := hS.smoothMetric.coeff (x : M) X Y
  coeff_cont x X Y := hS.smoothMetric.coeff_cont (x : M) X Y
  metricTensor_cont := by
    apply Tensor0SFamilyContinuousOnSet.congr
      (Tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
        (fun t x => Tensor0SBundle.metricTensorField (I := I) (S.family.metric t) x)
        hS.smoothMetric.metricTensor_cont U)
    intro t _ht x
    ext slots
    rfl
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    exact frameCompSmooth_restrictOpen (I := I) S hS U frame hframe i j




omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricVariationEquation_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    MetricVariationEquationOn (I := I) (solutionOn_restrictOpen (I := I) S U) := by
  intro t x X Y
  have hric :
      RicciAtFamily.toTensorField (I := I)
          (solutionOn_restrictOpen (I := I) S U).ricciAt (t : ℝ) x X Y
        = RicciAtFamily.toTensorField (I := I) S.ricciAt (t : ℝ) (x : M) X Y := by
    simp only [RicciAtFamily.toTensorField_apply]
    change metricRicciAt (I := I)
          ((S.base.metric (t : ℝ)).restrictOpen (I := I) U) x (vec2 X Y)
        = metricRicciAt (I := I) (S.base.metric (t : ℝ)) (x : M) (vec2 X Y)
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact ricciTensor_restrictOpen (I := I) (S.base.metric (t : ℝ)) U x X Y
  rw [hric]
  exact hS.equation t (x : M) X Y


omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    (solutionOn_restrictOpen (I := I) S U).scalar t x = S.scalar t (x : M) := by
  simp only [SolutionOn.scalar, SolutionFamily.scalar, solutionOn_restrictOpen]
  exact metricScalarAt_restrictOpen (I := I) (S.base.metric t) U x



omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarCont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    ContinuousOn (fun q : ℝ × U => (solutionOn_restrictOpen (I := I) S U).scalar q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set U)) := by
  have heq : (fun q : ℝ × U => (solutionOn_restrictOpen (I := I) S U).scalar q.1 q.2)
      = (fun p : ℝ × M => S.scalar p.1 p.2)
          ∘ (fun q : ℝ × U => ((q.1, (q.2 : M)) : ℝ × M)) := by
    funext q; exact scalar_restrictOpen (I := I) S U q.1 q.2
  rw [heq]
  exact hS.scalarCont.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    (fun q hq => ⟨hq.1, Set.mem_univ _⟩)




omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarTime_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {K : Set ℝ} {t : ℝ} (htK : t ∈ K) (hKsub : K ⊆ D.carrier) (x : U) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => (solutionOn_restrictOpen (I := I) S U).scalar s x) K t := by
  have heq : (fun s : ℝ => (solutionOn_restrictOpen (I := I) S U).scalar s x)
      = fun s : ℝ => S.scalar s (x : M) := by
    funext s; exact scalar_restrictOpen (I := I) S U s x
  rw [heq]
  exact hS.scalarTime htK hKsub (x : M)




omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciCont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    Tensor0SFamilyContinuousOnSet (I := I) (M := U) 2 D.carrier
      (fun t x => (solutionOn_restrictOpen (I := I) S U).ricci t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
      (fun t x => S.ricci t x) hS.ricciCont U)
  intro t _ht x
  ext slots
  exact (metricRicci_restrictOpen_eval (I := I) (S.base.metric t) U x slots).symm




omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem rm04Cont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    Tensor0SFamilyContinuousOnSet (I := I) (M := U) 4 D.carrier
      (fun t x => (solutionOn_restrictOpen (I := I) S U).base.rm04 t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
      (fun t x => S.base.rm04 t x) hS.rm04Cont U)
  intro t _ht x
  ext slots
  exact (metricRm04_restrictOpen_eval (I := I) (S.base.metric t) U x slots).symm



omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciNorm_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t x
      = ricciNorm (I := I) S t (x : M) := by



  have hsec : metricRicci (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x
      = metricRicci (I := I) (M := M) (S.base.metric t) (x : M) := by
    ext slots
    exact metricRicci_restrictOpen_eval (I := I) (S.base.metric t) U x slots
  have hnorm := normSq0S_restrictOpen_apply (I := I) (S.base.metric t) U 2 x
    (metricRicci (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x)
  simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family, SolutionFamily.ricci_apply,
    SolutionFamily.ricciAt, metricRicci_apply, solutionOn_restrictOpen] at *
  rw [hnorm, hsec]



omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem ricciNormSpace_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t) x := by
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t) := by
    refine (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := U)
      ((solutionOn_restrictOpen (I := I) S U).family.metric t)
      (metricRicci (I := I) (M := U)
        ((solutionOn_restrictOpen (I := I) S U).family.metric t))).congr ?_
    intro y
    simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
      SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
  exact hsmooth.contMDiffAt.mdifferentiableAt (by simp)




omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem smoothConnection_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    ConnectionFamilySmoothOn (I := I) (solutionOn_restrictOpen (I := I) S U).family := by
  intro t
  exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I)
    ((solutionOn_restrictOpen (I := I) S U).base.metric (t : ℝ))






omit [IsManifold I 2 M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isSolutionOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    IsSolutionOn (I := I) (solutionOn_restrictOpen (I := I) S U) where
  smoothMetric := metricFamilySmoothOn_restrictOpen (I := I) S hS U
  smoothConnection := smoothConnection_restrictOpen (I := I) S U
  equation := metricVariationEquation_restrictOpen (I := I) S hS U
  scalarCont := scalarCont_restrictOpen (I := I) S hS U
  scalarTime := fun htK hKsub x => scalarTime_restrictOpen (I := I) S hS U htK hKsub x
  ricciCont := ricciCont_restrictOpen (I := I) S hS U
  rm04Cont := rm04Cont_restrictOpen (I := I) S hS U
  ricciNormSpace := fun t _ht x => ricciNormSpace_restrictOpen (I := I) S U t x
  ricciNormGrad := by
    intro t _ht x
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        (ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t) := by
      refine (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := U)
        ((solutionOn_restrictOpen (I := I) S U).family.metric t)
        (metricRicci (I := I) (M := U)
          ((solutionOn_restrictOpen (I := I) S U).family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I)
      ((solutionOn_restrictOpen (I := I) S U).family.metric t) hsmooth x

end HCGCompactness
end DifferentialGeometry
