import DifferentialGeometry.Geometry.Connection.TensorNabla.FullHomCovariantCalculusRS
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculus
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_eq_of_toModel_eq {s : ℕ} {x : M} {T T' : Tensor0SSpace s I x}
    (h : ∀ v : Fin s → E, Tensor0SSpace.toModel T v = Tensor0SSpace.toModel T' v) : T = T' := by
  have hM : Tensor0SSpace.toModel T = Tensor0SSpace.toModel T' :=
    ContinuousMultilinearMap.ext h
  exact Tensor0SSpace.toModel_injective hM


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_toModel_sum {s : ℕ} {x : M} {ι : Type*} (t : Finset ι)
    (f : ι → Tensor0SSpace s I x) :
    Tensor0SSpace.toModel (∑ i ∈ t, f i) = ∑ i ∈ t, Tensor0SSpace.toModel (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Tensor0SSpace.toModel_add, ih]

set_option backward.isDefEq.respectTransparency false in

def slotInsertEndoFib (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    Tensor0SSpace s I x →L[ℝ] Tensor0SSpace s I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin s => if i = k then Λ else ContinuousLinearMap.id ℝ E))
      map_add' := fun A A' => by
        apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
        intro v
        simp
      map_smul' := fun c A => by
        apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
        intro v
        simp }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma slotInsertEndoFib_apply (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace s I x) :
    slotInsertEndoFib (I := I) (M := M) s k x Λ A =
      Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin s => if i = k then Λ else ContinuousLinearMap.id ℝ E)) := by
  rw [slotInsertEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertEndoFib_apply_eval (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace s I x)
    (m : Fin s → E) :
    Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) s k x Λ A) m =
      Tensor0SSpace.toModel A (Function.update m k (Λ (m k))) := by
  rw [slotInsertEndoFib_apply, Tensor0SSpace.toModel_ofModel]
  have hfam : (fun i : Fin s =>
      (if i = k then Λ else ContinuousLinearMap.id ℝ E) (m i)) =
      Function.update m k (Λ (m k)) := by
    funext i
    by_cases h : i = k
    · subst h
      simp
    · rw [if_neg h, Function.update_of_ne h]
      rfl
  exact congrArg (fun t => Tensor0SSpace.toModel A t) hfam

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertEndoFib_add_left (s : ℕ) (k : Fin s) (x : M)
    (Λ₁ Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (Λ₁ + Λ₂) =
      slotInsertEndoFib (I := I) (M := M) s k x Λ₁ +
        slotInsertEndoFib (I := I) (M := M) s k x Λ₂ := by
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.add_apply]
  apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
  intro v
  rw [slotInsertEndoFib_apply_eval, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, ContinuousLinearMap.add_apply,
    ContinuousMultilinearMap.map_update_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertEndoFib_smul_left (s : ℕ) (k : Fin s) (x : M) (c : ℝ)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (c • Λ) =
      c • slotInsertEndoFib (I := I) (M := M) s k x Λ := by
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.smul_apply]
  apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
  intro v
  rw [slotInsertEndoFib_apply_eval, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, slotInsertEndoFib_apply_eval,
    ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.map_update_smul]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertEndoFib_zero (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace (s + 1) I x) :
    slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x Λ A =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A).comp Λ) := by
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x Λ A) =
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A).comp Λ := by
    apply ContinuousLinearMap.ext
    intro v0
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro vt
    rw [tensor0S_curry_apply_eval, slotInsertEndoFib_apply_eval,
      ContinuousLinearMap.comp_apply, tensor0S_curry_apply_eval]
    congr 1
    rw [Fin.cons_zero, Fin.update_cons_zero]
  rw [← hcurry, ContinuousLinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertEndoFib_succ (g : SmoothRiemannianMetric I M) (s : ℕ) (j : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) (s + 1) j.succ x Λ =
      slotExtendPointwise (I := I) (M := M) g s s x
        (slotInsertEndoFib (I := I) (M := M) s j x Λ) := by
  apply ContinuousLinearMap.ext
  intro A
  have hcurry : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotInsertEndoFib (I := I) (M := M) (s + 1) j.succ x Λ A) =
      (slotInsertEndoFib (I := I) (M := M) s j x Λ).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) A) := by
    apply ContinuousLinearMap.ext
    intro v0
    apply tensor0S_eq_of_toModel_eq (I := I) (M := M)
    intro vt
    rw [tensor0S_curry_apply_eval, slotInsertEndoFib_apply_eval,
      ContinuousLinearMap.comp_apply, slotInsertEndoFib_apply_eval,
      tensor0S_curry_apply_eval]
    congr 1
    rw [Fin.cons_succ, ← Fin.cons_update]
  rw [slotExtendFib_apply (I := I) (M := M) g s s x, ← hcurry,
    ContinuousLinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotInsertEndoFib_contMDiff (g : SmoothRiemannianMetric I M) :
    ∀ (s : ℕ) (k : Fin s) (φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x),
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x (φ x)) →
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel s s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel s s ℝ E)
          (E := fun z : M => TensorRSSpace s s I z) x
          (TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x (φ x)))) := by
  intro s
  induction s with
  | zero => exact fun k => k.elim0
  | succ s ih =>
      intro k φ hφ
      induction k using Fin.cases with
      | zero =>
          apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
            (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun z : M => Tensor0SSpace (s + 1) I z)
            (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 1) I z)
            (φ := fun x => slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (φ x))
          intro Y
          have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
              (E := fun z : M => Tensor0SSpace (s + 1) I z) x
              (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (φ x) (Y x))) =
              (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
              (E := fun z : M => Tensor0SSpace (s + 1) I z) x
              ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
                (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x)))) := by
            funext x
            rw [slotInsertEndoFib_zero]
          rw [heq]
          have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
              (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
                (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
                ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x))) :=
            fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
              (fun y : M => Y y) x (Y.contMDiff x)
          have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
              (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
                (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
                (((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x))) := by
            apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
              (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
              (F₂ := Tensor0SModel s ℝ E) (V₂ := fun z : M => Tensor0SSpace s I z)
              (φ := fun x => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x))
            intro Z
            have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
                (E := fun z : M => Tensor0SSpace s I z) x
                ((((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x)) (Z x))) =
                (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
                (E := fun z : M => Tensor0SSpace s I z) x
                ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x) (φ x (Z x)))) := by
              funext x; rfl
            rw [heqZ]
            have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
                (fun x : M => TotalSpace.mk' E
                  (E := fun z : M => TangentSpace I z) x (φ x (Z x))) :=
              ContMDiff.clm_bundle_apply (b := id) hφ Z.contMDiff
            exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
          exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
            (fun x : M => ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) (Y x)).comp (φ x)) hG
      | succ j =>
          have hIH := ih j φ hφ
          set Φ : SmoothCcTensor g s s :=
            { toSection :=
                { toFun := fun x : M =>
                    TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s j x (φ x))
                  contMDiff_toFun := hIH }
              hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hΦ_def
          have hext := slotExtendFib_contMDiff (I := I) (M := M) g s s Φ
          refine hext.congr ?_
          intro x
          rw [show TensorRSSpace.ofCLM
                (slotInsertEndoFib (I := I) (M := M) (s + 1) (Fin.succ j) x (φ x)) =
              slotExtendPointwise (I := I) (M := M) g s s x
                (slotInsertEndoFib (I := I) (M := M) s j x (φ x)) from
            slotInsertEndoFib_succ (I := I) (M := M) g s j x (φ x)]
          rfl

set_option backward.isDefEq.respectTransparency false in

def curvatureTensorActionFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u w : TangentSpace I x) :
    Tensor0SSpace s I x →L[ℝ] Tensor0SSpace s I x :=
  -(∑ k : Fin s, slotInsertEndoFib (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma slotCurvSumFib_apply_eval (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u w : TangentSpace I x) (A : Tensor0SSpace s I x) (m : Fin s → E) :
    Tensor0SSpace.toModel (curvatureTensorActionFib (I := I) (M := M) g s x u w A) m =
      - ∑ k : Fin s, Tensor0SSpace.toModel A
          (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))) := by
  rw [curvatureTensorActionFib, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    Tensor0SSpace.toModel_neg, tensor0S_toModel_sum,
    ContinuousMultilinearMap.neg_apply, ContinuousMultilinearMap.sum_apply]
  congr 1
  exact Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_apply_eval (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w) A m

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma slotCurvSumFib_add_left (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u u' w : TangentSpace I x) :
    curvatureTensorActionFib (I := I) (M := M) g s x (u + u') w =
      curvatureTensorActionFib (I := I) (M := M) g s x u w +
        curvatureTensorActionFib (I := I) (M := M) g s x u' w := by
  have hR : riemannOp (LeviCivita (I := I) g) x (u + u') w =
      riemannOp (LeviCivita (I := I) g) x u w +
        riemannOp (LeviCivita (I := I) g) x u' w := by
    rw [map_add (riemannOp (LeviCivita (I := I) g) x), ContinuousLinearMap.add_apply]
  rw [curvatureTensorActionFib, curvatureTensorActionFib, curvatureTensorActionFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_add_left (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w)
      (riemannOp (LeviCivita (I := I) g) x u' w)]
  rw [Finset.sum_add_distrib, neg_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma slotCurvSumFib_smul_left (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (c : ℝ)
    (u w : TangentSpace I x) :
    curvatureTensorActionFib (I := I) (M := M) g s x (c • u) w =
      c • curvatureTensorActionFib (I := I) (M := M) g s x u w := by
  have hR : riemannOp (LeviCivita (I := I) g) x (c • u) w =
      c • riemannOp (LeviCivita (I := I) g) x u w := by
    rw [map_smul (riemannOp (LeviCivita (I := I) g) x), ContinuousLinearMap.smul_apply]
  rw [curvatureTensorActionFib, curvatureTensorActionFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x c
      (riemannOp (LeviCivita (I := I) g) x u w)]
  rw [← Finset.smul_sum, ← smul_neg]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma slotCurvSumFib_add_right (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (u w w' : TangentSpace I x) :
    curvatureTensorActionFib (I := I) (M := M) g s x u (w + w') =
      curvatureTensorActionFib (I := I) (M := M) g s x u w +
        curvatureTensorActionFib (I := I) (M := M) g s x u w' := by
  have hR : riemannOp (LeviCivita (I := I) g) x u (w + w') =
      riemannOp (LeviCivita (I := I) g) x u w +
        riemannOp (LeviCivita (I := I) g) x u w' :=
    map_add (riemannOp (LeviCivita (I := I) g) x u) w w'
  rw [curvatureTensorActionFib, curvatureTensorActionFib, curvatureTensorActionFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_add_left (I := I) (M := M) s k x
      (riemannOp (LeviCivita (I := I) g) x u w)
      (riemannOp (LeviCivita (I := I) g) x u w')]
  rw [Finset.sum_add_distrib, neg_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma slotCurvSumFib_smul_right (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (c : ℝ)
    (u w : TangentSpace I x) :
    curvatureTensorActionFib (I := I) (M := M) g s x u (c • w) =
      c • curvatureTensorActionFib (I := I) (M := M) g s x u w := by
  have hR : riemannOp (LeviCivita (I := I) g) x u (c • w) =
      c • riemannOp (LeviCivita (I := I) g) x u w :=
    map_smul (riemannOp (LeviCivita (I := I) g) x u) c w
  rw [curvatureTensorActionFib, curvatureTensorActionFib, hR]
  rw [Finset.sum_congr rfl fun k _ =>
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x c
      (riemannOp (LeviCivita (I := I) g) x u w)]
  rw [← Finset.smul_sum, ← smul_neg]

set_option backward.isDefEq.respectTransparency false in

def slotFreeCurvWCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u : TangentSpace I x) :
    TangentSpace I x →L[ℝ] Tensor0SSpace s I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  LinearMap.toContinuousLinearMap
    { toFun := fun w => curvatureTensorActionFib (I := I) (M := M) g s x u w A
      map_add' := fun w w' => by
        rw [slotCurvSumFib_add_right (I := I) (M := M) g s x u w w',
          ContinuousLinearMap.add_apply]
      map_smul' := fun c w => by
        rw [slotCurvSumFib_smul_right (I := I) (M := M) g s x c u w,
          ContinuousLinearMap.smul_apply]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] lemma slotFreeCurvWCLM_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u w : TangentSpace I x) :
    slotFreeCurvWCLM (I := I) (M := M) g s x A u w =
      curvatureTensorActionFib (I := I) (M := M) g s x u w A := by
  rw [slotFreeCurvWCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

def slotFreeCurvUCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) :
    TangentSpace I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (slotFreeCurvWCLM (I := I) (M := M) g s x A u)
      map_add' := fun u u' => by
        have hW : slotFreeCurvWCLM (I := I) (M := M) g s x A (u + u') =
            slotFreeCurvWCLM (I := I) (M := M) g s x A u +
              slotFreeCurvWCLM (I := I) (M := M) g s x A u' := by
          apply ContinuousLinearMap.ext
          intro w
          rw [ContinuousLinearMap.add_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
            slotFreeCurvWCLM_apply, slotCurvSumFib_add_left (I := I) (M := M) g s x u u' w,
            ContinuousLinearMap.add_apply]
        rw [hW, map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
      map_smul' := fun c u => by
        have hW : slotFreeCurvWCLM (I := I) (M := M) g s x A (c • u) =
            c • slotFreeCurvWCLM (I := I) (M := M) g s x A u := by
          apply ContinuousLinearMap.ext
          intro w
          rw [ContinuousLinearMap.smul_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
            slotCurvSumFib_smul_left (I := I) (M := M) g s x c u w,
            ContinuousLinearMap.smul_apply]
        rw [hW, map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] lemma slotFreeCurvUCLM_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u : TangentSpace I x) :
    slotFreeCurvUCLM (I := I) (M := M) g s x A u =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (slotFreeCurvWCLM (I := I) (M := M) g s x A u) := by
  rw [slotFreeCurvUCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

def curvatureOperatorOnTensorFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    Tensor0SSpace s I x →L[ℝ] Tensor0SSpace (s + 2) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (slotFreeCurvUCLM (I := I) (M := M) g s x A)
      map_add' := fun A A' => by
        have hU : slotFreeCurvUCLM (I := I) (M := M) g s x (A + A') =
            slotFreeCurvUCLM (I := I) (M := M) g s x A +
              slotFreeCurvUCLM (I := I) (M := M) g s x A' := by
          apply ContinuousLinearMap.ext
          intro u
          have hW : slotFreeCurvWCLM (I := I) (M := M) g s x (A + A') u =
              slotFreeCurvWCLM (I := I) (M := M) g s x A u +
                slotFreeCurvWCLM (I := I) (M := M) g s x A' u := by
            apply ContinuousLinearMap.ext
            intro w
            rw [ContinuousLinearMap.add_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
              slotFreeCurvWCLM_apply,
              map_add (curvatureTensorActionFib (I := I) (M := M) g s x u w)]
          rw [ContinuousLinearMap.add_apply, slotFreeCurvUCLM_apply, slotFreeCurvUCLM_apply,
            slotFreeCurvUCLM_apply, hW,
            map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
        rw [hU, map_add ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm)]
      map_smul' := fun c A => by
        have hU : slotFreeCurvUCLM (I := I) (M := M) g s x (c • A) =
            c • slotFreeCurvUCLM (I := I) (M := M) g s x A := by
          apply ContinuousLinearMap.ext
          intro u
          have hW : slotFreeCurvWCLM (I := I) (M := M) g s x (c • A) u =
              c • slotFreeCurvWCLM (I := I) (M := M) g s x A u := by
            apply ContinuousLinearMap.ext
            intro w
            rw [ContinuousLinearMap.smul_apply, slotFreeCurvWCLM_apply, slotFreeCurvWCLM_apply,
              map_smul (curvatureTensorActionFib (I := I) (M := M) g s x u w)]
          rw [ContinuousLinearMap.smul_apply, slotFreeCurvUCLM_apply, slotFreeCurvUCLM_apply,
            hW, map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm)]
        rw [hU, map_smul ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm)]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] lemma slotFreeCurvOpFib_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) :
    curvatureOperatorOnTensorFib (I := I) (M := M) g s x A =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (slotFreeCurvUCLM (I := I) (M := M) g s x A) := by
  rw [curvatureOperatorOnTensorFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma slotFreeCurvOpFib_apply_eval (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (u w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel (curvatureOperatorOnTensorFib (I := I) (M := M) g s x A)
        (Fin.cons u (Fin.cons w m)) =
      - ∑ k : Fin s, Tensor0SSpace.toModel A
          (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))) := by
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := curvatureOperatorOnTensorFib (I := I) (M := M) g s x A) (v0 := u) (vs := Fin.cons w m)]
  have hcurry1 : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
      (curvatureOperatorOnTensorFib (I := I) (M := M) g s x A) =
      slotFreeCurvUCLM (I := I) (M := M) g s x A := by
    rw [slotFreeCurvOpFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry1, slotFreeCurvUCLM_apply]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
      (slotFreeCurvWCLM (I := I) (M := M) g s x A u)) (v0 := w) (vs := m)]
  rw [ContinuousLinearEquiv.apply_symm_apply, slotFreeCurvWCLM_apply]
  exact slotCurvSumFib_apply_eval (I := I) (M := M) g s x u w A m

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem slotFreeCurvOpFib_contMDiff (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel s (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel s (s + 2) ℝ E)
        (E := fun z : M => TensorRSSpace s (s + 2) I z) x
        (TensorRSSpace.ofCLM (curvatureOperatorOnTensorFib (I := I) (M := M) g s x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel s ℝ E) (V₁ := fun z : M => Tensor0SSpace s I z)
    (F₂ := Tensor0SModel (s + 2) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 2) I z)
    (φ := fun x => curvatureOperatorOnTensorFib (I := I) (M := M) g s x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 2) I z) x
      (curvatureOperatorOnTensorFib (I := I) (M := M) g s x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 2) I z) x
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (slotFreeCurvUCLM (I := I) (M := M) g s x (Y x)))) := by
    funext x
    rw [slotFreeCurvOpFib_apply]
  rw [heq]
  have hU : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace (s + 1) I z) x
        (slotFreeCurvUCLM (I := I) (M := M) g s x (Y x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
      (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 1) I z)
      (φ := fun x => slotFreeCurvUCLM (I := I) (M := M) g s x (Y x))
    intro U
    have heqU : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) x
        (slotFreeCurvUCLM (I := I) (M := M) g s x (Y x) (U x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x)))) := by
      funext x
      rw [slotFreeCurvUCLM_apply]
    rw [heqU]
    have hW : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
          (slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x))) := by
      apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
        (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
        (F₂ := Tensor0SModel s ℝ E) (V₂ := fun z : M => Tensor0SSpace s I z)
        (φ := fun x => slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x))
      intro W
      have hR1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
          (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
            (E := fun z : M =>
              TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) x
            (riemannOp (LeviCivita (I := I) g) x (U x))) :=
        ContMDiff.clm_bundle_apply (b := id)
          (riemannOp_section_contMDiff (I := I) (M := M) g) U.contMDiff
      have hR2 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
          (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
            (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
            (riemannOp (LeviCivita (I := I) g) x (U x) (W x))) :=
        ContMDiff.clm_bundle_apply (b := id) hR1 W.contMDiff
      set T : Fin s → Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯ :=
        fun k =>
          { toFun := fun x : M => slotInsertEndoFib (I := I) (M := M) s k x
              (riemannOp (LeviCivita (I := I) g) x (U x) (W x)) (Y x)
            contMDiff_toFun := ContMDiff.clm_bundle_apply (b := id)
              (slotInsertEndoFib_contMDiff (I := I) (M := M) g s k
                (fun x => riemannOp (LeviCivita (I := I) g) x (U x) (W x)) hR2)
              Y.contMDiff } with hT_def
      have hsum := (-(∑ k : Fin s, T k) :
        Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯).contMDiff
      refine hsum.congr ?_
      intro x
      have hcoe : (-(∑ k : Fin s, T k) :
          Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯) x =
          -(∑ k : Fin s, T k x) := by
        have hs : ((∑ k : Fin s, T k :
            Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun z : M => Tensor0SSpace s I z)⟯) :
              Π z : M, Tensor0SSpace s I z) = ∑ k : Fin s, ⇑(T k) :=
          map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel s ℝ E) ∞
            (fun z : M => Tensor0SSpace s I z)) T Finset.univ
        rw [ContMDiffSection.coe_neg, Pi.neg_apply, hs, Finset.sum_apply]
      rw [hcoe]
      have hval : slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x) (W x) =
          -(∑ k : Fin s, T k x) := by
        rw [slotFreeCurvWCLM_apply, curvatureTensorActionFib, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.sum_apply]
        rfl
      rw [hval]
    exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
      (fun x : M => slotFreeCurvWCLM (I := I) (M := M) g s x (Y x) (U x)) hW
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => slotFreeCurvUCLM (I := I) (M := M) g s x (Y x)) hU

set_option backward.isDefEq.respectTransparency false in

def curvatureOperatorOnTensorHomFib (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 (s + 2) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 s I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  haveI : T2Space (TensorRSSpace 0 s I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun T => (curvatureOperatorOnTensorFib (I := I) (M := M) g s x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
      map_add' := fun T T' => by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T + T') =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) +
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T') from rfl,
          ContinuousLinearMap.comp_add]
      map_smul' := fun c T => by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from c • T) =
            c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) from rfl,
          ContinuousLinearMap.comp_smul]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] lemma slotFreeCurvHomFib_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 s I x) :
    curvatureOperatorOnTensorHomFib (I := I) (M := M) g s x T =
      (curvatureOperatorOnTensorFib (I := I) (M := M) g s x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 s I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  haveI : T2Space (TensorRSSpace 0 s I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  rw [curvatureOperatorOnTensorHomFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem slotFreeCurvHomFib_contMDiff (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 (s + 2) ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z →L[ℝ] TensorRSSpace 0 (s + 2) I z) x
        (curvatureOperatorOnTensorHomFib (I := I) (M := M) g s x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := TensorRSModel 0 s ℝ E) (V₁ := fun z : M => TensorRSSpace 0 s I z)
    (F₂ := TensorRSModel 0 (s + 2) ℝ E) (V₂ := fun z : M => TensorRSSpace 0 (s + 2) I z)
    (φ := fun x => curvatureOperatorOnTensorHomFib (I := I) (M := M) g s x)
  intro Z
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun z : M => Tensor0SSpace 0 I z)
    (F₂ := Tensor0SModel (s + 2) ℝ E) (V₂ := fun z : M => Tensor0SSpace (s + 2) I z)
    (φ := fun x => (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
      curvatureOperatorOnTensorHomFib (I := I) (M := M) g s x (Z x)))
  intro ζ
  have hZζ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Z x) (ζ x))) :=
    ContMDiff.clm_bundle_apply (b := id) Z.contMDiff ζ.contMDiff
  have happ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 2) I z) x
        (curvatureOperatorOnTensorFib (I := I) (M := M) g s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Z x) (ζ x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (slotFreeCurvOpFib_contMDiff (I := I) (M := M) g s) hZζ
  refine happ.congr ?_
  intro x
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
      curvatureOperatorOnTensorHomFib (I := I) (M := M) g s x (Z x)) (ζ x) =
    curvatureOperatorOnTensorFib (I := I) (M := M) g s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Z x) (ζ x)) from by
    rw [slotFreeCurvHomFib_apply, ContinuousLinearMap.comp_apply]]

set_option backward.isDefEq.respectTransparency false in

def curvatureOperatorOnTensorHomField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    HomTensorRSField (E := E) (M := M) 0 s (s + 2) I where
  toFun := fun x : M => curvatureOperatorOnTensorHomFib (I := I) (M := M) g s x
  contMDiff_toFun := slotFreeCurvHomFib_contMDiff (I := I) (M := M) g s

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma slotFreeCurvHomField_apply (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    (show TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 (s + 2) I x from
        curvatureOperatorOnTensorHomField (I := I) (M := M) g s x) =
      curvatureOperatorOnTensorHomFib (I := I) (M := M) g s x := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_slotFreeCurvOpField_baseSlot_eval (g : SmoothRiemannianMetric I M) :
    ∃ Θ : ∀ s : ℕ, HomTensorRSField (E := E) (M := M) 0 s (s + 2) I,
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (u w : TangentSpace I x)
        (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            (homTensorRSFieldApply (I := I) (M := M) g 0 s (s + 2) (Θ s) S).toSection x)
            (unitZeroSec (I := I) (M := M) x))
          (Fin.cons u (Fin.cons w m)) =
        - ∑ k : Fin s, Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              S.toSection x) (unitZeroSec (I := I) (M := M) x))
          (Function.update m k (riemannOp (LeviCivita (I := I) g) x u w (m k))) := by
  refine ⟨fun s => curvatureOperatorOnTensorHomField (I := I) (M := M) g s, fun s S x u w m => ?_⟩
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
      (homTensorRSFieldApply (I := I) (M := M) g 0 s (s + 2)
        (curvatureOperatorOnTensorHomField (I := I) (M := M) g s) S).toSection x)
      (unitZeroSec (I := I) (M := M) x) =
      curvatureOperatorOnTensorFib (I := I) (M := M) g s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [show (homTensorRSFieldApply (I := I) (M := M) g 0 s (s + 2)
        (curvatureOperatorOnTensorHomField (I := I) (M := M) g s) S).toSection x =
      (show TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 (s + 2) I x from
        curvatureOperatorOnTensorHomField (I := I) (M := M) g s x) (S.toSection x) from
      appFullSec_toSection (I := I) (M := M) g 0 s (s + 2)
        (curvatureOperatorOnTensorHomField (I := I) (M := M) g s) S x]
    rw [slotFreeCurvHomField_apply, slotFreeCurvHomFib_apply]
    rfl
  rw [hval, slotFreeCurvOpFib_apply_eval (I := I) (M := M) g s x _ u w m]

end Connection
end Integral
end DifferentialGeometry

end
