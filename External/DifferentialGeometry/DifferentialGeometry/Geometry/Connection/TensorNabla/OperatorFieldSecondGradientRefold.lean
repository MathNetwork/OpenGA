import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculusRS
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SPartialEval
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def tensorLeadingSlotEvalCLM (s : ℕ) (x : M) (p : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace s I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun G => (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x) G p
      map_add' := fun G G' => by
        rw [map_add]
        rfl
      map_smul' := fun c G => by
        rw [map_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma slotFeedFib_apply (s : ℕ) (x : M) (p : TangentSpace I x)
    (G : Tensor0SSpace (s + 1) I x) :
    tensorLeadingSlotEvalCLM (I := I) (M := M) s x p G =
      (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x) G p := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma slotFeedFib_toModel (s : ℕ) (x : M) (p : TangentSpace I x)
    (G : Tensor0SSpace (s + 1) I x) (v : Fin s → E) :
    Tensor0SSpace.toModel (tensorLeadingSlotEvalCLM (I := I) (M := M) s x p G) v =
      Tensor0SSpace.toModel G (Fin.cons (p : E) v) :=
  TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := G) (v0 := p) (vs := v)

def tensorLeadingPairSlotEvalCLM (s : ℕ) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x :=
  (tensorLeadingSlotEvalCLM (I := I) (M := M) s x q).comp
    (tensorLeadingSlotEvalCLM (I := I) (M := M) (s + 1) x p)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma leadingPairFeedFib_toModel (s : ℕ) (x : M) (p q : TangentSpace I x)
    (G : Tensor0SSpace (s + 2) I x) (v : Fin s → E) :
    Tensor0SSpace.toModel (tensorLeadingPairSlotEvalCLM (I := I) (M := M) s x p q G) v =
      Tensor0SSpace.toModel G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [tensorLeadingPairSlotEvalCLM, ContinuousLinearMap.comp_apply, slotFeedFib_toModel,
    slotFeedFib_toModel]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma ofModel4_add {x : M}
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x) (f + g) : Tensor0SSpace 4 I x) =
      Tensor0SSpace.ofModel f + Tensor0SSpace.ofModel g :=
  map_add (tensor0SSpace_continuousLinearEquiv 4 x).symm f g

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma ofModel4_smul {x : M} (c : ℝ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x) (c • f) : Tensor0SSpace 4 I x) =
      c • Tensor0SSpace.ofModel f :=
  map_smul (tensor0SSpace_continuousLinearEquiv 4 x).symm c f

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private lemma domDomCongr4_add (σ : Equiv.Perm (Fin 4))
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (f + g) =
      ContinuousMultilinearMap.domDomCongr σ f +
        ContinuousMultilinearMap.domDomCongr σ g := by
  ext m
  simp [ContinuousMultilinearMap.domDomCongr_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private lemma domDomCongr4_smul (σ : Equiv.Perm (Fin 4)) (c : ℝ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (c • f) =
      c • ContinuousMultilinearMap.domDomCongr σ f := by
  ext m
  simp [ContinuousMultilinearMap.domDomCongr_apply]

def tensorRank4PermuteCLM (x : M) (σ : Equiv.Perm (Fin 4)) :
    Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 4 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 4 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun G => Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ (Tensor0SSpace.toModel (𝕜 := ℝ) G))
      map_add' := fun G₁ G₂ => by
        rw [Tensor0SSpace.toModel_add, domDomCongr4_add, ofModel4_add]
      map_smul' := fun c G => by
        rw [Tensor0SSpace.toModel_smul, domDomCongr4_smul, ofModel4_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma slotPerm4Fib_apply (x : M) (σ : Equiv.Perm (Fin 4)) (G : Tensor0SSpace 4 I x) :
    tensorRank4PermuteCLM (I := I) (M := M) x σ G =
      Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ (Tensor0SSpace.toModel (𝕜 := ℝ) G)) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma slotPerm4Fib_toModel (x : M) (σ : Equiv.Perm (Fin 4)) (G : Tensor0SSpace 4 I x) :
    Tensor0SSpace.toModel (tensorRank4PermuteCLM (I := I) (M := M) x σ G) =
      ContinuousMultilinearMap.domDomCongr σ (Tensor0SSpace.toModel (𝕜 := ℝ) G) := by
  rw [slotPerm4Fib_apply, Tensor0SSpace.toModel_ofModel]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem slotPerm4Fib_apply_section_contMDiff (σ : Equiv.Perm (Fin 4))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x
        (tensorRank4PermuteCLM (I := I) (M := M) x σ (Y x))) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
      (E := fun z : M => Tensor0SSpace 4 I z) x
      (tensorRank4PermuteCLM (I := I) (M := M) x σ (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x
        ((Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ
              (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x))) : Tensor0SSpace 4 I x))) := by
    funext x; rfl
  rw [heq]
  have hYfield : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x
        (Tensor0SSpace.ofModel (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x)))) := by
    simpa only [Tensor0SSpace.ofModel_toModel] using Y.contMDiff
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x))) :
          Tensor0SSpace 4 I x))).mpr ?_
  have hY := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x)) :
      Tensor0SSpace 4 I x))).mp hYfield
  intro τ x₀
  refine (hY (fun j => τ (σ j)) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SSpace.toModel (𝕜 := ℝ) (Y x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

def curvatureActionMonomialCLM (x : M) (tw : ℝ) (σ : Equiv.Perm (Fin 4))
    (p q : TangentSpace I x) :
    Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x :=
  tw • ((tensorLeadingPairSlotEvalCLM (I := I) (M := M) 2 x p q).comp
    (tensorRank4PermuteCLM (I := I) (M := M) x σ))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma curvatureRefoldMonomialFib_apply (x : M) (tw : ℝ) (σ : Equiv.Perm (Fin 4))
    (p q : TangentSpace I x) (G : Tensor0SSpace 4 I x) :
    curvatureActionMonomialCLM (I := I) (M := M) x tw σ p q G =
      tw • (tensorLeadingPairSlotEvalCLM (I := I) (M := M) 2 x p q)
        (tensorRank4PermuteCLM (I := I) (M := M) x σ G) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma curvatureRefoldMonomialFib_toModel (x : M) (tw : ℝ) (σ : Equiv.Perm (Fin 4))
    (p q : TangentSpace I x) (G : Tensor0SSpace 4 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (curvatureActionMonomialCLM (I := I) (M := M) x tw σ p q G) v =
      tw * Tensor0SSpace.toModel G
        (fun i => (Fin.cons (p : E) (Fin.cons (q : E) v) : Fin 4 → E) (σ i)) := by
  rw [curvatureRefoldMonomialFib_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, leadingPairFeedFib_toModel,
    slotPerm4Fib_toModel, ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma curvatureRefoldMonomialFib_zero_weight (x : M) (σ : Equiv.Perm (Fin 4))
    (p q : TangentSpace I x) :
    curvatureActionMonomialCLM (I := I) (M := M) x 0 σ p q = 0 := by
  rw [curvatureActionMonomialCLM, zero_smul]

def curvatureActionKernelCLM (x : M) (tw : ℝ)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) (p q : TangentSpace I x) :
    Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (1 / 2 : ℝ) •
    (curvatureActionMonomialCLM (I := I) (M := M) x tw σ₁ p q
      + curvatureActionMonomialCLM (I := I) (M := M) x tw σ₂ p q
      - curvatureActionMonomialCLM (I := I) (M := M) x tw σ₃ p q
      - curvatureActionMonomialCLM (I := I) (M := M) x tw σ₄ p q)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma curvatureRefoldKernelFib_zero_weight (x : M)
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) (p q : TangentSpace I x) :
    curvatureActionKernelCLM (I := I) (M := M) x 0 σ₁ σ₂ σ₃ σ₄ p q = 0 := by
  rw [curvatureActionKernelCLM, curvatureRefoldMonomialFib_zero_weight,
    curvatureRefoldMonomialFib_zero_weight, curvatureRefoldMonomialFib_zero_weight,
    curvatureRefoldMonomialFib_zero_weight]
  simp

section FrameSum

private def innerPairBilin (x : M) (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (L X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_smul] }

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma innerPairBilin_apply (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    innerPairBilin (I := I) x K L X Y Y' = K X Y * L X Y' := by
  rw [innerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private def outerPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l * K X (chartModelBasis E k)) •
          (ContinuousLinearMap.flip L (chartModelBasis E l))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma outerPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilin (I := I) g x K L X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (chartModelBasis E k) * L X' (chartModelBasis E l)) := by
  rw [outerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private theorem double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (chartModelBasis E m) (chartModelBasis E k) *
            L (chartModelBasis E n) (chartModelBasis E l))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      outerPairBilin (I := I) g x K L (B a) (B a) := by
    intro a
    rw [outerPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (innerPairBilin (I := I) x K L (B a)) B hB
    simp only [innerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (outerPairBilin (I := I) g x K L) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilin_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private theorem double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K L : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * L (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * L (C a) (C b) := by
  rw [double_frame_bilin_trace_eq_fixed (I := I) g x K L B hB,
    double_frame_bilin_trace_eq_fixed (I := I) g x K L C hC]

private def toModelEvalCLM (s : ℕ) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma toModelEvalCLM_apply (s : ℕ) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    toModelEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

private def pairFeedScalarCLM (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (toModelEvalCLM (I := I) (M := M) s x v).comp
        (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x
          ((tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          map_smul] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma pairFeedScalarCLM_apply (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) (p q : TangentSpace I x) :
    pairFeedScalarCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel (𝕜 := ℝ) G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [pairFeedScalarCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, toModelEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p) (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := G) (v0 := p) (vs := Fin.cons (q : E) v)]

def curvatureActionMonomialFrameTrace (W : Π b : M, Tensor0SSpace 2 I b)
    (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    curvatureActionMonomialCLM (I := I) (M := M) x
      (Tensor0SSpace.toModel (𝕜 := ℝ) (W x) ![(B a x : E), (B b x : E)]) σ (B a x) (B b x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem curvatureRefoldMonomialFibFixedFrame_toModel (W : Π b : M, Tensor0SSpace 2 I b)
    (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (G : Tensor0SSpace 4 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (curvatureActionMonomialFrameTrace (I := I) (M := M) W σ B x G) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) (W x) ![(B a x : E), (B b x : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ) G
            (fun i => (Fin.cons ((B a x : E)) (Fin.cons ((B b x : E)) v) : Fin 4 → E)
              (σ i)) := by
  classical
  rw [curvatureActionMonomialFrameTrace, ContinuousLinearMap.sum_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, curvatureRefoldMonomialFib_toModel]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem curvatureRefoldMonomialFibFixedFrame_apply_section_contMDiff
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σ : Equiv.Perm (Fin 4))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (curvatureActionMonomialFrameTrace (I := I) (M := M) W σ B x (Y x))) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  set Yσ : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun z : M => Tensor0SSpace 4 I z⟯ :=
    { toFun := fun x : M => tensorRank4PermuteCLM (I := I) (M := M) x σ (Y x)
      contMDiff_toFun := slotPerm4Fib_apply_section_contMDiff (I := I) (M := M) σ Y }
    with hYσ_def
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (curvatureActionMonomialCLM (I := I) (M := M) x
            (Tensor0SSpace.toModel (𝕜 := ℝ) (W x) ![(B a x : E), (B b x : E)]) σ
            (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (𝕜 := ℝ) (W x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => W b) hW
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hfeed1 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
          (E := fun z : M => Tensor0SSpace 3 I z) x
          (Tensor0SPartialEval.tensor0SPartialEval I M (s := 3)
            (fun z => Yσ z) (fun z => B a z) x)) :=
      Tensor0SPartialEval.contMDiff_tensor0SPartialEval I M (s := 3)
        (fun z => Yσ z) Yσ.contMDiff (fun z => B a z) (hB a)
    set Z3 : Cₛ^∞⟮I; Tensor0SModel 3 ℝ E, fun z : M => Tensor0SSpace 3 I z⟯ :=
      { toFun := fun x : M => Tensor0SPartialEval.tensor0SPartialEval I M (s := 3)
          (fun z => Yσ z) (fun z => B a z) x
        contMDiff_toFun := hfeed1 }
      with hZ3_def
    have hfeed2 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (Tensor0SPartialEval.tensor0SPartialEval I M (s := 2)
            (fun z => Z3 z) (fun z => B b z) x)) :=
      Tensor0SPartialEval.contMDiff_tensor0SPartialEval I M (s := 2)
        (fun z => Z3 z) Z3.contMDiff (fun z => B b z) (hB b)
    have hsmul := ContMDiff.smul_section
      (f := fun x : M => Tensor0SSpace.toModel (𝕜 := ℝ) (W x) ![(B a x : E), (B b x : E)])
      (s := fun x : M => Tensor0SPartialEval.tensor0SPartialEval I M (s := 2)
        (fun z => Z3 z) (fun z => B b z) x)
      hscalar hfeed2
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => curvatureActionMonomialCLM (I := I) (M := M) x
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W x) ![(B a x : E), (B b x : E)]) σ
          (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [curvatureActionMonomialFrameTrace, hStot_def]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

def curvatureActionMonomialTrace (g₁ : SmoothRiemannianMetric I M)
    (W : Π b : M, Tensor0SSpace 2 I b) (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x :=
  curvatureActionMonomialFrameTrace (I := I) (M := M) W σ
    (smoothOrthoFrame (I := I) g₁ x) x

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem curvatureRefoldMonomialBiContrFib_eq_fixedFrame_on_nbhd
    (g₁ : SmoothRiemannianMetric I M) (W : Π b : M, Tensor0SSpace 2 I b)
    (σ : Equiv.Perm (Fin 4)) (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ y =
      curvatureActionMonomialFrameTrace (I := I) (M := M) W σ
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro G
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [curvatureActionMonomialTrace, curvatureRefoldMonomialFibFixedFrame_toModel,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel (𝕜 := ℝ) (W y) ![(Bf a : E), (Bf b : E)] *
          Tensor0SSpace.toModel (𝕜 := ℝ) G
            (fun i => (Fin.cons ((Bf a : E)) (Fin.cons ((Bf b : E)) v) : Fin 4 → E)
              (σ i)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        pairFeedScalarCLM (I := I) (M := M) 0 y (W y) ![] (Bf a) (Bf b) *
          pairFeedScalarCLM (I := I) (M := M) 2 y
            (tensorRank4PermuteCLM (I := I) (M := M) y σ G) v (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [pairFeedScalarCLM_apply, pairFeedScalarCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (pairFeedScalarCLM (I := I) (M := M) 0 y (W y) ![])
    (pairFeedScalarCLM (I := I) (M := M) 2 y (tensorRank4PermuteCLM (I := I) (M := M) y σ G) v)
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem curvatureRefoldMonomialBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σ : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
        (E := fun z : M => TensorRSSpace 4 2 I z) x
        (TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M)
          g₁ W σ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
        (E := fun z : M => TensorRSSpace 4 2 I z) x
        (TensorRSSpace.ofCLM (curvatureActionMonomialFrameTrace (I := I) (M := M) W σ
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ := by
    have h_glob : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 4 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
          (E := fun z : M => TensorRSSpace 4 2 I z) x
          (TensorRSSpace.ofCLM (curvatureActionMonomialFrameTrace (I := I) (M := M) W σ
            (smoothOrthoFrame (I := I) g₁ x₀) x))) := by
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun z : M => Tensor0SSpace 4 I z)
        (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
        (φ := fun x : M => curvatureActionMonomialFrameTrace (I := I) (M := M) W σ
          (smoothOrthoFrame (I := I) g₁ x₀) x)
      intro Y
      exact curvatureRefoldMonomialFibFixedFrame_apply_section_contMDiff (I := I) (M := M)
        W hW σ (smoothOrthoFrame (I := I) g₁ x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) Y
    exact h_glob x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 4 2 ℝ E)
    (E := fun z : M => TensorRSSpace 4 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (curvatureRefoldMonomialBiContrFib_eq_fixedFrame_on_nbhd (I := I) (M := M)
        g₁ W σ x₀ hy))

def curvatureActionMonomialCoeffField (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x))
      contMDiff_toFun := curvatureRefoldMonomialBiContrFib_contMDiff (I := I) (M := M)
        g₁ W hW σ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] theorem curvatureRefoldMonomialCoeffField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁ W hW σ).toSection x =
      (show TensorRSSpace 4 2 I x from
        TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M)
          g₁ W σ x)) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma curvatureRefoldMonomialBiContrFib_zero_weight (g₁ : SmoothRiemannianMetric I M)
    (W : Π b : M, Tensor0SSpace 2 I b) (σ : Equiv.Perm (Fin 4)) {x : M}
    (hx : W x = 0) :
    curvatureActionMonomialTrace (I := I) (M := M) g₁ W σ x = 0 := by
  classical
  rw [curvatureActionMonomialTrace, curvatureActionMonomialFrameTrace]
  refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
  rw [hx]
  rw [show Tensor0SSpace.toModel (𝕜 := ℝ) (0 : Tensor0SSpace 2 I x)
      ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      0 from by rw [Tensor0SSpace.toModel_zero]; rfl]
  exact curvatureRefoldMonomialFib_zero_weight (I := I) (M := M) x σ _ _

def curvatureActionKernelCoeffField (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 4 2 :=
  (1 / 2 : ℝ) •
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁ W hW σ₁
      + curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁ W hW σ₂
      - curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁ W hW σ₃
      - curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁ W hW σ₄)


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem curvatureRefoldKernelCoeffField_toSection_eq_kernelFib_sum
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 4)) (x : M) :
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (curvatureActionKernelCoeffField (I := I) (M := M)
          g₀ g₁ W hW σ₁ σ₂ σ₃ σ₄).toSection x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        curvatureActionKernelCLM (I := I) (M := M) x
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)])
          σ₁ σ₂ σ₃ σ₄
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) := by
  classical
  rw [curvatureActionKernelCoeffField, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_add, Pi.add_apply]
  set F : Equiv.Perm (Fin 4) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x) :=
    fun σ a b => curvatureActionMonomialCLM (I := I) (M := M) x
      (Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
        ![(smoothOrthoFrame (I := I) g₁ x a x : E),
          (smoothOrthoFrame (I := I) g₁ x b x : E)]) σ
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) with hF_def
  have hfib : ∀ σ : Equiv.Perm (Fin 4),
      ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁ W hW σ).toSection x :
        TensorRSSpace 4 2 I x) =
      TensorRSSpace.ofCLM (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        F σ a b) := fun σ => rfl
  rw [hfib σ₁, hfib σ₂, hfib σ₃, hfib σ₄]
  change (1 / 2 : ℝ) •
      ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₁ a b)
        + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₂ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₃ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₄ a b)) =
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      curvatureActionKernelCLM (I := I) (M := M) x
        (Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)])
        σ₁ σ₂ σ₃ σ₄
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
  have hker : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      curvatureActionKernelCLM (I := I) (M := M) x
        (Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)])
        σ₁ σ₂ σ₃ σ₄
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) • (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b) :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => rfl))
  have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) • (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
      (1 / 2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.smul_sum]
  have hdist : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₁ a b)
        + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₂ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₃ a b)
        - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), F σ₄ a b) := by
    have hinner : ∀ a : Fin (Module.finrank ℝ E),
        (∑ b : Fin (Module.finrank ℝ E),
          (F σ₁ a b + F σ₂ a b - F σ₃ a b - F σ₄ a b)) =
        (∑ b : Fin (Module.finrank ℝ E), F σ₁ a b)
          + (∑ b : Fin (Module.finrank ℝ E), F σ₂ a b)
          - (∑ b : Fin (Module.finrank ℝ E), F σ₃ a b)
          - (∑ b : Fin (Module.finrank ℝ E), F σ₄ a b) := by
      intro a
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hker, hsplit, hdist]

end FrameSum

end Connection
end Integral
end DifferentialGeometry

end
