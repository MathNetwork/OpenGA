import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Geometry.Connection.TensorNabla.Slot0CurryCovariantLeibniz


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorInnerPointwise_0s_succ_eq_sum_curryLeft_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x S T =
      ∑ a : Fin (Module.finrank ℝ E),
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a)) := by
  classical
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (s + 1) frame horth S T]
  rw [show (∑ a : Fin (Module.finrank ℝ E),
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a))) =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ φ : Fin s → Fin (Module.finrank ℝ E),
          (S.curryLeft (frame a)) (fun k => frame (φ k)) *
            (T.curryLeft (frame a)) (fun k => frame (φ k)) from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x s frame horth]]
  rw [← (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E)))
        (fun pr : Fin (Module.finrank ℝ E) × (Fin s → Fin (Module.finrank ℝ E)) =>
          (S.curryLeft (frame pr.1)) (fun k => frame (pr.2 k)) *
            (T.curryLeft (frame pr.1)) (fun k => frame (pr.2 k)))
        (fun ψ : Fin (s + 1) → Fin (Module.finrank ℝ E) =>
          S (fun k => frame (ψ k)) * T (fun k => frame (ψ k)))
        ?_)]
  · rw [Fintype.sum_prod_type]
  · intro pr
    simp only [Fin.consEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]
    have hcons : (Fin.cons (frame pr.1) (fun k => frame (pr.2 k)) : Fin (s + 1) → E) =
        fun k => frame ((Fin.cons pr.1 pr.2 : Fin (s + 1) → Fin (Module.finrank ℝ E)) k) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · simp
      · intro j; simp
    rw [hcons]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma contract_covariant_smul_left (s : ℕ) (x : M) (c : ℝ) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) :
    contract_covariant 0 s x (c • v) A =
      c • contract_covariant 0 s x v A := by
  classical
  have hmodel : ∀ w : E,
      model_interior_product (𝕜 := ℝ) (E := E) s w = model_interior_bilinear ℝ E s w :=
    fun w => rfl
  unfold contract_covariant
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [hmodel, hmodel, map_smul, map_smul, ContinuousLinearMap.smul_apply, map_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma contract_covariant_add_left (s : ℕ) (x : M) (v w : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) :
    contract_covariant 0 s x (v + w) A =
      contract_covariant 0 s x v A + contract_covariant 0 s x w A := by
  classical
  have hmodel : ∀ z : E,
      model_interior_product (𝕜 := ℝ) (E := E) s z = model_interior_bilinear ℝ E s z :=
    fun z => rfl
  unfold contract_covariant
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [hmodel, hmodel, hmodel, map_add, map_add, ContinuousLinearMap.add_apply, map_add]

noncomputable def covDivergenceBilinear
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y :=
  TensorialAt.mkHom₂
    (I := I) (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _))
    (V' := (TangentSpace I : M → Type _))
    (A := TensorRSSpace 0 s I y)
    (Φ := fun (X Y : Π b : M, TangentSpace I b) =>
      contract_covariant 0 s y (Y y)
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
            (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)))
    y
    (fun Y _hY => by
      refine ⟨?_, ?_⟩
      · intro f X _hf _hX
        have hsmul : (f • X : Π b : M, TangentSpace I b) y = f y • X y := rfl
        change contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y ((f • X) y)) =
          f y • contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hsmul, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
      · intro X X' _hX _hX'
        have hadd : (X + X' : Π b : M, TangentSpace I b) y = X y + X' y := rfl
        change contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y ((X + X') y)) =
          contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) +
          contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X' y))
        rw [hadd, ContinuousLinearMap.map_add, ContinuousLinearMap.map_add])
    (fun X _hX => by
      refine ⟨?_, ?_⟩
      · intro f Y _hf _hY
        have hsmul : (f • Y : Π b : M, TangentSpace I b) y = f y • Y y := rfl
        change contract_covariant 0 s y ((f • Y) y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) =
          f y • contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hsmul]
        exact contract_covariant_smul_left s y (f y) (Y y) _
      · intro Y Y' _hY _hY'
        have hadd : (Y + Y' : Π b : M, TangentSpace I b) y = Y y + Y' y := rfl
        change contract_covariant 0 s y ((Y + Y') y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) =
          contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) +
          contract_covariant 0 s y (Y' y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hadd]
        exact contract_covariant_add_left s y (Y y) (Y' y) _)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem codiffPsi_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (y : M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (X z)) y)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (Y z)) y) :
    covDivergenceBilinear (I := I) (M := M) g s V y (X y) (Y y) =
      contract_covariant 0 s y (Y y)
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
            (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) := by
  classical
  unfold covDivergenceBilinear
  exact TensorialAt.mkHom₂_apply _ _ hX hY

def covDivergenceRaw
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TensorRSSpace 0 s I b :=
  ∑ i : Fin (Module.finrank ℝ E),
    covDivergenceBilinear (I := I) (M := M) g s V b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b)

def covDivergenceFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    TensorRSSpace 0 s I b :=
  ∑ i : Fin (Module.finrank ℝ E),
    contract_covariant 0 s b (B i b)
      (tensorCovDerivAt (I := I) (M := M) g 0 (s + 1) V b (B i b))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDivergenceFixedFrame_eq_sum_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    covDivergenceFixedFrame (I := I) (M := M) g s V B b =
      ∑ i : Fin (Module.finrank ℝ E),
        (contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
          (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i)) (B i)) b :=
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDivergenceFixedFrame_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V B b)) := by
  classical
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
        (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) b
          ((contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
            (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i))
            (B i)) b)) :=
    fun i =>
      (contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
        (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i)) (B i)).contMDiff
  have heq : (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V B b)) =
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (∑ i : Fin (Module.finrank ℝ E),
          (contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
            (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i))
            (B i)) b)) := by
    funext b
    rw [covDivergenceFixedFrame_eq_sum_section (I := I) (M := M) g s V B b]
  rw [heq]
  exact ContMDiff.sum_section (fun i _ => hsummand i)

def smoothOrthoFrameSection
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun b : M => smoothOrthoFrame (I := I) g x₀ i b, smoothOrthoFrame_smooth (I := I) g x₀ i⟩

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma smoothOrthoFrameSection_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    smoothOrthoFrameSection (I := I) (M := M) g x₀ i b =
      smoothOrthoFrame (I := I) g x₀ i b := rfl

omit [CompactSpace M] [I.Boundaryless] in
lemma covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    covDivergenceRaw (I := I) (M := M) g s V b =
      ∑ i : Fin (Module.finrank ℝ E),
        covDivergenceBilinear (I := I) (M := M) g s V b (B i) (B i) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) b
  have hcentral : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hcentral_trace := orthonormal_basis_bilin_trace_chartα (I := I)
    (A := TensorRSSpace 0 s I b) g b hb_base (covDivergenceBilinear (I := I) (M := M) g s V b)
    (fun i => smoothOrthoFrame (I := I) g b i b) hcentral
  have hB_trace := orthonormal_basis_bilin_trace_chartα (I := I)
    (A := TensorRSSpace 0 s I b) g b hb_base (covDivergenceBilinear (I := I) (M := M) g s V b) B hB_orth
  rw [covDivergenceRaw, hcentral_trace, ← hB_trace]

omit [CompactSpace M] in
lemma covDivergenceRaw_eq_fixedFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (x₀ : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    covDivergenceRaw (I := I) (M := M) g s V b =
      covDivergenceFixedFrame (I := I) (M := M) g s V
        (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b := by
  classical
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g x₀ i b) (smoothOrthoFrame (I := I) g x₀ j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hb i j
  rw [covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace (I := I) (M := M) g s V b
    (fun i => smoothOrthoFrame (I := I) g x₀ i b) hB_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g x₀ i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g x₀ i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
  rfl

omit [CompactSpace M] in
theorem covDivergenceRaw_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  intro x₀
  have h_fixed : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V
          (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b)) :=
    covDivergenceFixedFrame_contMDiff (I := I) (M := M) g s V
      (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i)
  have h_fixed_at := h_fixed x₀
  have h_eventuallyEq :
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceRaw (I := I) (M := M) g s V b)) =ᶠ[𝓝 x₀]
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V
          (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with b hb
    exact congrArg (TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) b)
      (covDivergenceRaw_eq_fixedFrame_on_nbhd (I := I) (M := M) g s V x₀ hb)
  exact h_fixed_at.congr_of_eventuallyEq h_eventuallyEq

omit [CompactSpace M] in
lemma covDivergenceRaw_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    {b : M} (hb : b ∉ tsupport V.toFun) :
    covDivergenceRaw (I := I) (M := M) g s V b = 0 := by
  classical
  rw [covDivergenceRaw]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hzero : (TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
      (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) b
        (smoothOrthoFrame (I := I) g b i b) = 0 := by
    have := tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g 0 (s + 1) V hb
      (smoothOrthoFrame (I := I) g b i b)
    exact this
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g b i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g b i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
  rw [hzero, map_zero]

lemma covDivergenceRaw_toModel_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    HasCompactSupport
      (fun b : M => TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact V.hasCompactSupport ?_
  intro b hb
  rw [Function.mem_support] at hb
  by_contra hbnot
  apply hb
  rw [covDivergenceRaw_eq_zero_off_tsupport (I := I) (M := M) g s V hbnot,
    TensorRSSpace.toModel_zero]

noncomputable def covDivergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun b : M => covDivergenceRaw (I := I) (M := M) g s V b
      contMDiff_toFun := covDivergenceRaw_contMDiff (I := I) (M := M) g s V }
  hasCompactSupport := covDivergenceRaw_toModel_hasCompactSupport (I := I) (M := M) g s V

@[simp] lemma covDivergence_toSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    (covDivergence (I := I) (M := M) g s V).toSection b =
      covDivergenceRaw (I := I) (M := M) g s V b := rfl

@[simp] lemma covDivergence_toFun_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    (covDivergence (I := I) (M := M) g s V).toFun b =
      TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b) := rfl

def oneSidedDirichletForm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g 0 s b
    (TensorRSSpace.toModel (T.toSection b))
    (TensorRSSpace.toModel (contract_covariant 0 s b X (V.toSection b)))
  map_add' X Y := by
    rw [contract_covariant_add_left (I := I) (M := M) s b X Y (V.toSection b),
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_right]
  map_smul' c X := by
    rw [contract_covariant_smul_left (I := I) (M := M) s b c X (V.toSection b),
      TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_right]
    rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma oneSidedDirichletForm_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) (X : TangentSpace I b) :
    oneSidedDirichletForm (I := I) (M := M) g s T V b X =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel (T.toSection b))
        (TensorRSSpace.toModel (contract_covariant 0 s b X (V.toSection b))) := rfl

def oneSidedDirichletVF
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (oneSidedDirichletForm (I := I) (M := M) g s T V b)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma inner_oneSidedDirichletVF
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) (X : TangentSpace I b) :
    g.inner b (oneSidedDirichletVF (I := I) (M := M) g s T V b) X =
      oneSidedDirichletForm (I := I) (M := M) g s T V b X := by
  rw [oneSidedDirichletVF]
  exact inner_metricSharp (I := I) g b (oneSidedDirichletForm (I := I) (M := M) g s T V b) X

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma contract_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun y : M => TensorRSSpace 0 s I y) b
        (contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (s + 1)
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 s
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  have hV_on : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun y : M => TensorRSSpace 0 (s + 1) I y) b (V.toSection b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    V.toSection.contMDiff.contMDiffOn
  have hX_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α j b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartBasisVec_contMDiffOn (I := I) α j
  set biop : E →L[ℝ] (TensorRSModel 0 (s + 1) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) :=
    (ContinuousLinearMap.compL ℝ
      (Tensor0SModel 0 ℝ E) (Tensor0SModel (s + 1) ℝ E) (Tensor0SModel s ℝ E)).comp
      (model_interior_bilinear ℝ E s) with hbiop
  intro x₀ hx₀
  refine ContMDiffWithinAt.mono ?_ (Set.subset_univ _)
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [Bundle.contMDiffAt_section (F := TensorRSModel 0 s ℝ E)
    (E := fun z : M => TensorRSSpace 0 s I z)]
  have hV_at := (hV_on x₀ hx₀).contMDiffAt
    ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have hX_at := (hX_on x₀ hx₀).contMDiffAt
    ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have hV' := (Bundle.contMDiffAt_section (F := TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x₀).mp hV_at
  have hX' := (Bundle.contMDiffAt_section (F := E) (E := TangentSpace I) x₀).mp hX_at
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
        (fun b : M => biop
          ((trivializationAt E (TangentSpace I) x₀ ⟨b, chartBasisVecFiber (I := I) α j b⟩).2)
          ((trivializationAt (TensorRSModel 0 (s + 1) ℝ E)
            (fun z : M => TensorRSSpace 0 (s + 1) I z) x₀ ⟨b, V.toSection b⟩).2)) x₀ :=
    ((contMDiffAt_const (c := biop)).clm_apply hX').clm_apply hV'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with b hb
  refine ContinuousLinearMap.ext fun γ => ?_
  refine ContinuousMultilinearMap.ext fun w => ?_
  set sL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ b with hsL
  set Xtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨b, chartBasisVecFiber (I := I) α j b⟩).2
    with hXtilde
  set gtilde : Tensor0SSpace 0 I b :=
    (trivializationAt (Tensor0SModel 0 ℝ E) (fun z : M => Tensor0SSpace 0 I z) x₀).symmL ℝ b γ
    with hgtilde
  have h_cLMAt_s : ∀ (Tm : Tensor0SSpace s I b) (v : Fin s → E),
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ b Tm v =
      Tm (fun i => sL (v i)) := by
    intro Tm v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SSpace s I z) x₀).linearMapAt ℝ b) =
        fun y => (trivializationAt (Tensor0SModel s ℝ E)
          (fun z : M => Tensor0SSpace s I z) x₀ ⟨b, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rfl
  have h_cLMAt_s1 : ∀ (Tm : Tensor0SSpace (s + 1) I b) (v : Fin (s + 1) → E),
      (trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ b Tm v =
      Tm (fun i => sL (v i)) := by
    intro Tm v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) x₀).linearMapAt ℝ b) =
        fun y => (trivializationAt (Tensor0SModel (s + 1) ℝ E)
          (fun z : M => Tensor0SSpace (s + 1) I z) x₀ ⟨b, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rfl
  change (trivializationAt (Tensor0SModel s ℝ E)
      (fun z : M => Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ b
      (model_interior_product s (chartBasisVecFiber (I := I) α j b : E)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)) w =
    (trivializationAt (Tensor0SModel (s + 1) ℝ E)
      (fun z : M => Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ b
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)
      (Fin.cons Xtilde w)
  rw [h_cLMAt_s, h_cLMAt_s1]
  change ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde :
        Tensor0SModel (s + 1) ℝ E)
      (@Fin.cons s (fun _ => E) (chartBasisVecFiber (I := I) α j b : E) (fun i => sL (w i))) =
    ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)
      (fun i => sL (@Fin.cons s (fun _ => E) Xtilde w i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change (chartBasisVecFiber (I := I) α j b : E) = sL Xtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := ℝ) hb (chartBasisVecFiber (I := I) α j b)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b
        (chartBasisVecFiber (I := I) α j b) = Xtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ b
        (chartBasisVecFiber (I := I) α j b) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rw [hcl] at h
    exact h.symm
  · intro jj
    rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma oneSidedDirichletForm_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => oneSidedDirichletForm (I := I) (M := M) g s T V b
        (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  have hT_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel (T.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g 0 s T.toSection α
  have hcontract_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel
          (contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g 0 s
      (fun b : M => contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))
      α (contract_chartBasis_contMDiffOn (I := I) (M := M) g s V α j)
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel
            (contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g 0 s
      (fun b : M => T.toSection b)
      (fun b : M => contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))
      α hT_lowered hcontract_lowered
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [oneSidedDirichletForm_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma oneSidedDirichletVF_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (oneSidedDirichletVF (I := I) (M := M) g s T V b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => oneSidedDirichletForm (I := I) (M := M) g s T V b)
    (fun α j => oneSidedDirichletForm_chartBasis_component_contMDiffOn
      (I := I) (M := M) g s T V α j)

def oneSidedDirichletVFSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => oneSidedDirichletVF (I := I) (M := M) g s T V b)
    (oneSidedDirichletVF_contMDiff (I := I) (M := M) g s T V)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma oneSidedDirichletVFSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    oneSidedDirichletVFSection (I := I) (M := M) g s T V b =
      oneSidedDirichletVF (I := I) (M := M) g s T V b := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contract_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s+1) I x) (D : Tensor0SSpace 0 I x) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          contract_covariant 0 s x v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A) D)
        (Fin.cons (v : E) m) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contract_bare_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s+1) I x) (D : Tensor0SSpace 0 I x) (m : Fin s → E) :
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        contract_covariant 0 s x v A) D) m =
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A) D)
        (Fin.cons (v : E) m) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma D_eq_scalar_smul_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (tensor00Scalar (I := I) (M := M) x D) • (unitZeroSec (I := I) (M := M) x) := by
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel D =
    Tensor0SSpace.toModel ((tensor00Scalar (I := I) (M := M) x D) • (unitZeroSec (I := I) (M := M) x))
  rw [Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.smul_apply]
  rw [unitZeroSec_apply, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [tensor00Scalar_apply (I := I) (M := M) x D m, smul_eq_mul, mul_one]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contract_eq_tensor0SAsRS_curry (s : ℕ) (x : M) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s+1) I x) :
    contract_covariant 0 s x v A =
      tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
            (unitZeroSec (I := I) (M := M) x)) v) := by
  apply tensorRSSpace_ext 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [contract_eval (I := I) (M := M) s x v A D m]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor0SToTensorRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
              (unitZeroSec (I := I) (M := M) x)) v)) D =
      tensor00Scalar (I := I) (M := M) x D •
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
            (unitZeroSec (I := I) (M := M) x)) v) from
    tensor0SAsRS_apply (I := I) (M := M) x _ D]
  change _ = Tensor0SSpace.toModel
      (tensor00Scalar (I := I) (M := M) x D •
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
            (unitZeroSec (I := I) (M := M) x)) v)) m
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    TensorMultilinear.tensor0S_curry_apply_eval]
  conv_lhs => rw [D_eq_scalar_smul_unit (I := I) (M := M) x D]
  rw [ContinuousLinearMap.map_smul]
  change Tensor0SSpace.toModel
      (tensor00Scalar (I := I) (M := M) x D •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
          (unitZeroSec (I := I) (M := M) x))) (Fin.cons (v : E) m) = _
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rs_zero_recover (s : ℕ) (x : M) (Φ : TensorRSSpace 0 s I x) :
    Φ = tensor0SToTensorRS (I := I) (M := M) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ)
        (unitZeroSec (I := I) (M := M) x)) := by
  apply tensorRSSpace_ext 0 s x
  intro D
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor0SToTensorRS (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ)
            (unitZeroSec (I := I) (M := M) x))) D =
      tensor00Scalar (I := I) (M := M) x D •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ)
          (unitZeroSec (I := I) (M := M) x)) from
    tensor0SAsRS_apply (I := I) (M := M) x _ D]
  conv_lhs => rw [D_eq_scalar_smul_unit (I := I) (M := M) x D, ContinuousLinearMap.map_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_add (s : ℕ) (x : M) (C D : Tensor0SSpace s I x) :
    tensor0SToTensorRS (I := I) (M := M) x (C + D) =
      tensor0SToTensorRS (I := I) (M := M) x C + tensor0SToTensorRS (I := I) (M := M) x D := by
  apply ContinuousLinearMap.ext
  intro u
  change (tensor00Scalar (I := I) (M := M) x u) • (C + D) =
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from tensor0SToTensorRS (I := I) (M := M) x C) u +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from tensor0SToTensorRS (I := I) (M := M) x D) u
  rw [tensor0SAsRS_apply, tensor0SAsRS_apply, smul_add]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma contract_covariant_leibniz
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s+1))
    {W X : Π b:M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, W b⟩ : TotalSpace E (TangentSpace I))))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
        (fun y : M => contract_covariant 0 s y (X y) (V.toSection y)) x (W x) =
      contract_covariant 0 s x (X x)
          ((tensorRSCovariantDerivative I M 0 (s+1) (LeviCivita (I := I) g)).toFun
            (fun y : M => V.toSection y) x (W x))
        + contract_covariant 0 s x ((LeviCivita (I := I) g).toFun X x (W x)) (V.toSection x) := by
  classical
  have hsec : (fun y : M => contract_covariant 0 s y (X y) (V.toSection y)) =
      (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s+1) I y from V.toSection y)
            (unitZeroSec (I := I) (M := M) y)) (X y))) := by
    funext y
    exact contract_eq_tensor0SAsRS_curry (I := I) (M := M) s y (X y) (V.toSection y)
  rw [hsec]
  rw [contract_eq_tensor0SAsRS_curry (I := I) (M := M) s x (X x)
    ((tensorRSCovariantDerivative I M 0 (s+1) (LeviCivita (I := I) g)).toFun
      (fun y : M => V.toSection y) x (W x))]
  rw [contract_eq_tensor0SAsRS_curry (I := I) (M := M) s x
    ((LeviCivita (I := I) g).toFun X x (W x)) (V.toSection x)]
  rw [rs_zero_recover (I := I) (M := M) s x
    ((tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
      (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s+1) I y from V.toSection y)
            (unitZeroSec (I := I) (M := M) y)) (X y))) x (W x))]
  rw [← tensor0SAsRS_add]
  congr 1
  have hleib := tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s V hW hX x
  rw [eq_sub_iff_add_eq] at hleib
  exact hleib.symm

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma contract_covGrad_eq_covDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    contract_covariant 0 s x v ((covGrad (I := I) (M := M) g 0 s T).toSection x) =
      tensorCovDerivAt (I := I) (M := M) g 0 s T x v := by
  apply tensorRSSpace_ext 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [contract_eval (I := I) (M := M) s x v _ D m]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s T x D (Fin.cons (v : E) m)]
  rw [Fin.cons_zero, Matrix.vecTail, show (Fin.cons (v : E) m ∘ Fin.succ) = m from by funext i; simp]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_contract (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (n : ℕ) (e : Fin n → TangentSpace I x) (i : Fin n)
    (A : TensorRSSpace 0 (s + 1) I x) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s
        (contract_covariant 0 s x (e i) A) n e (fun k => k.elim0) J =
      fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0)
        (Fin.cons i J) := by
  unfold fiberNormSqComponent
  rw [contract_bare_eval (I := I) (M := M) s x (e i) A _ (fun k => e (J k))]
  congr 1
  funext k
  refine Fin.cases ?_ ?_ k
  · simp
  · intro j; simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorInnerPointwise_succ_eq_sum_contract_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (A B : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel A) (TensorRSSpace.toModel B) =
      ∑ i : Fin n,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (contract_covariant 0 s x (e i) A))
          (TensorRSSpace.toModel (contract_covariant 0 s x (e i) B)) := by
  classical
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 (s + 1) x
    e bse hn hbse horth A B]
  rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
  · rw [show (∑ i : Fin n,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (contract_covariant 0 s x (e i) A))
            (TensorRSSpace.toModel (contract_covariant 0 s x (e i) B))) =
        ∑ i : Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0)
            (Fin.cons i J) *
          fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e (fun k => k.elim0)
            (Fin.cons i J) from ?_]
    · rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun p : Fin n × (Fin s → Fin n) =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0)
              (Fin.cons p.1 p.2) *
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e (fun k => k.elim0)
              (Fin.cons p.1 p.2))
          (fun ψ : Fin (s + 1) → Fin n =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0) ψ *
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e (fun k => k.elim0) ψ)
          (fun p => rfl)]
      rw [Fintype.sum_prod_type]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 s x
        e bse hn hbse horth (contract_covariant 0 s x (e i) A) (contract_covariant 0 s x (e i) B)]
      rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
      · refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [fiberNormSqComponent_contract (I := I) (M := M) g s x n e i A J,
          fiberNormSqComponent_contract (I := I) (M := M) g s x n e i B J]
      · intro K _ hK; exact absurd (funext fun k => k.elim0) hK
      · intro h; exact absurd (Finset.mem_univ _) h
  · intro K _ hK; exact absurd (funext fun k => k.elim0) hK
  · intro h; exact absurd (Finset.mem_univ _) h

private def contractFrameSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯ :=
  contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
    V.toSection (smoothOrthoFrameSection (I := I) (M := M) g b i)

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma contractFrameSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (i : Fin (Module.finrank ℝ E)) (y : M) :
    contractFrameSection (I := I) (M := M) g s V b i y =
      contract_covariant 0 s y (smoothOrthoFrame (I := I) g b i y) (V.toSection y) := rfl

omit [CompactSpace M] in
private lemma divergence_oneSidedVF_summand_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (oneSidedDirichletVFSection (I := I) (M := M) g s T V).toFun b
          (smoothOrthoFrame (I := I) g b i b))
        (smoothOrthoFrame (I := I) g b i b) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (contract_covariant 0 s b (smoothOrthoFrame (I := I) g b i b)
              (V.toSection b)))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel
            (contract_covariant 0 s b (smoothOrthoFrame (I := I) g b i b)
              ((tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)).toFun
                (fun y : M => V.toSection y) b
                (smoothOrthoFrame (I := I) g b i b)))) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g b i y,
      smoothOrthoFrame_smooth (I := I) g b i⟩ with hB_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    oneSidedDirichletVFSection (I := I) (M := M) g s T V with hZ_def
  set C : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯ :=
    contractFrameSection (I := I) (M := M) g s V b i with hC_def
  have hBb : (B : ∀ y, TangentSpace I y) b = smoothOrthoFrame (I := I) g b i b := rfl
  have hleib := leibniz_inner (I := I) g
    (V := fun y : M => Z y) (W := fun y : M => B y)
    Z.contMDiff B.contMDiff
    (x := b) ((B : ∀ y, TangentSpace I y) b)
  have hfun : (fun y : M => g.inner y (Z y) (B y)) =
      tensorInnerScalar (I := I) (M := M) g 0 s T.toSection C := by
    funext y
    rw [hZ_def, oneSidedDirichletVFSection_apply, inner_oneSidedDirichletVF,
      oneSidedDirichletForm_apply, tensorInnerScalar_apply]
    rfl
  have hprod : tangentSectionAction (I := I) B
        (fun y : M => g.inner y (Z y) (B y)) b =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B b))
          (TensorRSSpace.toModel (C b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionGen (I := I) (M := M) g s C B b)) := by
    have hint := loweringIntertwiner_gen (I := I) (M := M) g s
    rw [show tangentSectionAction (I := I) B
            (fun y : M => g.inner y (Z y) (B y)) =
          tangentSectionAction (I := I) B
            (tensorInnerScalar (I := I) (M := M) g 0 s T.toSection C) from by rw [hfun]]
    rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g 0 s
      T.toSection C B b]
    congr 1
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B) C b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionGen (I := I) (M := M) g s hint
        T.toSection B b]
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        T.toSection (covDerivAlongVFSectionGen (I := I) (M := M) g s C B) b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionGen (I := I) (M := M) g s hint
        C B b]
  have haccel : g.inner b (Z b)
        ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
          ((B : ∀ y, TangentSpace I y) b)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel (T.toSection b))
        (TensorRSSpace.toModel
          (contract_covariant 0 s b
            ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
              ((B : ∀ y, TangentSpace I y) b)) (V.toSection b))) := by
    rw [hZ_def, oneSidedDirichletVFSection_apply, inner_oneSidedDirichletVF,
      oneSidedDirichletForm_apply]
  have hCleib : covDerivAlongVFSectionGen (I := I) (M := M) g s C B b =
      contract_covariant 0 s b ((B : ∀ y, TangentSpace I y) b)
          ((tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)).toFun
            (fun y : M => V.toSection y) b ((B : ∀ y, TangentSpace I y) b))
        + contract_covariant 0 s b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b ((B : ∀ y, TangentSpace I y) b))
          (V.toSection b) := by
    rw [show covDerivAlongVFSectionGen (I := I) (M := M) g s C B b =
          (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
            (fun y : M => C y) b ((B : ∀ y, TangentSpace I y) b) from rfl]
    rw [hC_def]
    exact contract_covariant_leibniz (I := I) (M := M) g s V
      (W := fun y : M => B y) (X := fun y : M => B y) B.contMDiff B.contMDiff b
  have hsummand : g.inner b
        ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
          ((B : ∀ y, TangentSpace I y) b))
        ((B : ∀ y, TangentSpace I y) b) =
      tangentSectionAction (I := I) B (fun y : M => g.inner y (Z y) (B y)) b
        - g.inner b (Z b)
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := by
    rw [tangentSectionAction_def]
    rw [hleib]; ring
  change g.inner b
      ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
        ((B : ∀ y, TangentSpace I y) b))
      ((B : ∀ y, TangentSpace I y) b) = _
  rw [hsummand, hprod, haccel]
  rw [hCleib, TensorRSSpace.toModel_add, tensorInnerPointwise_add_right]
  rw [show covDerivAlongVFSectionGen (I := I) (M := M) g s T.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b ((B : ∀ y, TangentSpace I y) b) from rfl]
  rw [hC_def, contractFrameSection_apply]
  rw [hBb]
  rw [show (fun y : M => (B : ∀ z : M, TangentSpace I z) y) =
        (fun y : M => smoothOrthoFrame (I := I) g b i y) from rfl]
  ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma centeredFrame_basis_exists
    (g : SmoothRiemannianMetric I M) (b : M) :
    ∃ (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b)),
      (∀ i, frame i = smoothOrthoFrame (I := I) g b i b) ∧
      (∀ i j, g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0) := by
  classical
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hB_li hcard, ?_, ?_⟩
  · intro i
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I b) i = smoothOrthoFrame (I := I) g b i b
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  · intro i j
    rw [show (basisOfLinearIndependentOfCardEqFinrank hB_li hcard : Fin (Module.finrank ℝ E) → TangentSpace I b) i =
          smoothOrthoFrame (I := I) g b i b from by rw [coe_basisOfLinearIndependentOfCardEqFinrank],
      show (basisOfLinearIndependentOfCardEqFinrank hB_li hcard : Fin (Module.finrank ℝ E) → TangentSpace I b) j =
          smoothOrthoFrame (I := I) g b j b from by rw [coe_basisOfLinearIndependentOfCardEqFinrank]]
    exact hB_orth i j

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tip_sum_right
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (S : TensorRSModel 0 s ℝ E) {ι : Type*} (fs : Finset ι)
    (C : ι → TensorRSModel 0 s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g 0 s b S (∑ i ∈ fs, C i) =
      ∑ i ∈ fs, tensorInnerPointwise (I := I) (M := M) g 0 s b S (C i) := by
  classical
  induction fs using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, tensorInnerPointwise_zero_right]
  | insert a fs ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        tensorInnerPointwise_add_right, ih]

theorem divergence_oneSidedVF_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    divergence_g (I := I) g (oneSidedDirichletVFSection (I := I) (M := M) g s T V) b =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  obtain ⟨frame, hframe_eq, hframe_orth⟩ :=
    centeredFrame_basis_exists (I := I) (M := M) g b
  have horth_e : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g
    (oneSidedDirichletVFSection (I := I) (M := M) g s T V) b]
  rw [Finset.sum_congr rfl (fun i _ =>
    divergence_oneSidedVF_summand_eq (I := I) (M := M) g s T V b i)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [tensorInnerPointwise_succ_eq_sum_contract_orthoFrame (I := I) (M := M) g s b
      (e := fun i => smoothOrthoFrame (I := I) g b i b) frame rfl hframe_eq horth_e
      ((covGrad (I := I) (M := M) g 0 s T).toSection b) (V.toSection b)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [contract_covGrad_eq_covDeriv (I := I) (M := M) g s T b
      (smoothOrthoFrame (I := I) g b i b)]
  · rw [covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace (I := I) (M := M) g s V b
      (fun i => smoothOrthoFrame (I := I) g b i b) horth_e]
    rw [show TensorRSSpace.toModel
          (∑ i : Fin (Module.finrank ℝ E),
            covDivergenceBilinear (I := I) (M := M) g s V b
              (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b)) =
        ∑ i : Fin (Module.finrank ℝ E),
          TensorRSSpace.toModel
            (covDivergenceBilinear (I := I) (M := M) g s V b
              (smoothOrthoFrame (I := I) g b i b)
              (smoothOrthoFrame (I := I) g b i b)) from by
      rw [show (TensorRSSpace.toModel
            (∑ i : Fin (Module.finrank ℝ E),
              covDivergenceBilinear (I := I) (M := M) g s V b
                (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b))) =
          (TensorRSSpace.toModelL (I := I) 0 s b)
            (∑ i : Fin (Module.finrank ℝ E),
              covDivergenceBilinear (I := I) (M := M) g s V b
                (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b)) from rfl,
        map_sum]
      rfl]
    rw [tip_sum_right (I := I) (M := M) g s b]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hcodiff : covDivergenceBilinear (I := I) (M := M) g s V b
          (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b) =
        contract_covariant 0 s b (smoothOrthoFrame (I := I) g b i b)
          ((tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)).toFun
            (fun y : M => V.toSection y) b (smoothOrthoFrame (I := I) g b i b)) := by
      have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
            (smoothOrthoFrame (I := I) g b i z)) b :=
        (smoothOrthoFrame_smooth (I := I) g b i).contMDiffAt.mdifferentiableAt (by simp)
      rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
    rw [hcodiff]

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun V.toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          T.toFun (covDivergence (I := I) (M := M) g s V).toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    oneSidedDirichletVFSection (I := I) (M := M) g s T V with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hdiv_zero : ∫ b, divergence_g (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergence_g (I := I) g Z b =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
    intro b; rw [hZ_def]; exact divergence_oneSidedVF_eq (I := I) (M := M) g s T V b
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))) :=
    (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s T).toSection V.toSection).continuous
  have hsecond_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) := by
    have heq : (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) =
        (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel ((covDivergence (I := I) (M := M) g s V).toSection b))) := by
      funext b
      rw [covDivergence_toSection_apply]
    rw [heq]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 s
      T.toSection (covDivergence (I := I) (M := M) g s V).toSection).continuous
  have hcross_int : Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hcross_cont (HasCompactSupport.of_compactSpace _)
  have hsecond_int : Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hsecond_cont (HasCompactSupport.of_compactSpace _)
  rw [integral_add hcross_int hsecond_int] at hdiv_zero
  rw [show tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun V.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b)) ∂μ from ?_]
  · rw [show tensorL2Inner (I := I) (M := M) g 0 s
          T.toFun (covDivergence (I := I) (M := M) g s V).toFun =
        ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel (T.toSection b))
            (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) ∂μ from ?_]
    · linarith [hdiv_zero]
    · unfold tensorL2Inner
      rw [← hμ_def]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
      simp only [SmoothCcTensor.toFun_apply, covDivergence_toSection_apply]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply]

end Connection
end Integral
end DifferentialGeometry

end
