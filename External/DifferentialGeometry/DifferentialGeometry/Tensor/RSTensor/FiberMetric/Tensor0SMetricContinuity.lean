import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEvalRealized
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false




























namespace Tensor0SBundle

noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]





theorem tensor0SField_eval_cmdAt_slots {s : ℕ}
    (α : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    {x₀ : M} (v : Fin s -> (∀ y : M, TangentSpace I y))
    (hv : ∀ a : Fin s, ContMDiffAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun y : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) y (v a y)) x₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun a : Fin s => v a y)) x₀ := by
  have hα_top := α.contMDiff x₀
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => α y) hα_top (v := v) (hv := hv)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

section NormSqContinuity

variable (g : DifferentialGeometry.SmoothRiemannianMetric I M)




theorem normSq0S_contAt {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) :
    ContinuousAt (fun y : M => normSq0S (I := I) g y s (T y)) x₀ := by
  classical
  set e := trivializationAt E (TangentSpace I : M -> Type _) x₀ with he
  set b := Module.finBasis ℝ E with hb
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀

  set Gm : M -> Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of fun i j =>
      g.inner y (e.localFrame b i y) (e.localFrame b j y) with hGm

  have hslots : ∀ (s' : ℕ)
      (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s')
      (I0 : Fin s' -> Fin (Module.finrank ℝ E)),
      ContinuousAt (fun y : M => A y (fun a : Fin s' => e.localFrame b (I0 a) y)) x₀ := by
    intro s' A I0
    exact (tensor0SField_eval_cmdAt_slots (I := I) (M := M) (α := A)
      (v := fun a y => e.localFrame b (I0 a) y)
      (hv := fun a => contMDiffAt_localFrame_of_mem (I := I)
        (n := (∞ : WithTop ℕ∞)) (e := e) (b := b) (i := I0 a) hx₀)).continuousAt

  have hGmEnt : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun y : M =>
        g.inner y (e.localFrame b i y) (e.localFrame b j y)) x₀ := by
    intro i j
    have h2 := hslots 2 (metricTensorField (I := I) g)
      (![i, j] : Fin 2 -> Fin (Module.finrank ℝ E))
    have heq : (fun y : M => metricTensorField (I := I) g y
        (fun a : Fin 2 => e.localFrame b ((![i, j] : Fin 2 -> _) a) y)) =
        fun y : M => g.inner y (e.localFrame b i y) (e.localFrame b j y) := by
      funext y
      rw [metricTensorField_apply]
      simp
    rw [heq] at h2
    exact h2
  have hGmc : ContinuousAt Gm x₀ :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => hGmEnt i j

  have hdetne : ∀ y, y ∈ e.baseSet -> (Gm y).det ≠ 0 := by
    intro y hy hdet0
    obtain ⟨c, hc0, hcv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Gm y)).2 hdet0
    set w : TangentSpace I y := ∑ i, c i • e.localFrame b i y with hw
    have hrow0 : ∀ i, (g.inner y (e.localFrame b i y)) w = 0 := by
      intro i
      have h1 : (g.inner y (e.localFrame b i y)) w = ∑ j, Gm y i j * c j := by
        rw [hw, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
        simp only [hGm, Matrix.of_apply]
      have h2 : (∑ j, Gm y i j * c j) = 0 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun hcv i
      rw [h1, h2]
    have hinner : g.inner y w w = 0 := by
      have hout : (g.inner y) w = ∑ i, c i • ((g.inner y) (e.localFrame b i y)) := by
        rw [hw, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      calc g.inner y w w = (∑ i, c i • ((g.inner y) (e.localFrame b i y))) w := by rw [hout]
        _ = ∑ i, c i • ((g.inner y (e.localFrame b i y)) w) := by
            rw [ContinuousLinearMap.sum_apply]
            exact Finset.sum_congr rfl fun i _ => by
              rw [ContinuousLinearMap.smul_apply]
        _ = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            rw [hrow0 i, smul_zero]
    have hwne : w ≠ 0 := by
      intro hw0
      apply hc0
      have hz : ∑ i, c i • e.basisAt b hy i = 0 := by
        rw [← hw0, hw]
        exact Finset.sum_congr rfl fun i _ => by
          rw [e.localFrame_apply_of_mem_baseSet b hy]
      have hall := Fintype.linearIndependent_iff.1 (e.basisAt b hy).linearIndependent c hz
      funext i
      exact hall i
    exact absurd hinner (ne_of_gt (g.pos y w hwne))

  have hGinvc : ContinuousAt (fun y => (Gm y)⁻¹) x₀ := by
    have hdetc : ContinuousAt (fun y => (Gm y).det) x₀ :=
      (continuous_id.matrix_det).continuousAt.comp hGmc
    have hadjc : ContinuousAt (fun y => (Gm y).adjugate) x₀ :=
      (continuous_id.matrix_adjugate).continuousAt.comp hGmc
    have h1 : ContinuousAt (fun y => ((Gm y).det)⁻¹ • (Gm y).adjugate) x₀ :=
      (hdetc.inv₀ (hdetne x₀ hx₀)).smul hadjc
    have hfun : (fun y => (Gm y)⁻¹) =
        fun y => ((Gm y).det)⁻¹ • (Gm y).adjugate := by
      funext y
      rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rw [hfun]
    exact h1
  have hGinvEnt : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun y => (Gm y)⁻¹ i j) x₀ := fun i j =>
    continuousAt_pi.1 (continuousAt_pi.1 hGinvc i) j

  have hinvw : ∀ y (hy : y ∈ e.baseSet),
      MetricInverseInBasis (I := I) g y (e.basisAt b hy) (fun i j => (Gm y)⁻¹ i j) := by
    intro y hy i j
    have hunit : IsUnit (Gm y).det := isUnit_iff_ne_zero.2 (hdetne y hy)
    have hGb : ∀ i' j' : Fin (Module.finrank ℝ E),
        g.inner y (e.basisAt b hy i') (e.basisAt b hy j') = Gm y i' j' := by
      intro i' j'
      rw [hGm]
      simp [e.localFrame_apply_of_mem_baseSet b hy]
    constructor
    · have : (∑ k, (Gm y)⁻¹ i k * Gm y k j) = ((Gm y)⁻¹ * Gm y) i j :=
        (Matrix.mul_apply).symm
      rw [Finset.sum_congr rfl fun k _ => by rw [hGb k j], this,
        Matrix.nonsing_inv_mul (Gm y) hunit, Matrix.one_apply]
    · have : (∑ k, Gm y i k * (Gm y)⁻¹ k j) = (Gm y * (Gm y)⁻¹) i j :=
        (Matrix.mul_apply).symm
      rw [Finset.sum_congr rfl fun k _ => by rw [hGb i k], this,
        Matrix.mul_nonsing_inv (Gm y) hunit, Matrix.one_apply]

  have hF : ContinuousAt (fun y : M =>
      ∑ I0 : Fin s -> Fin (Module.finrank ℝ E),
        ∑ J0 : Fin s -> Fin (Module.finrank ℝ E),
          (∏ a : Fin s, (Gm y)⁻¹ (I0 a) (J0 a)) *
              (T y fun a : Fin s => e.localFrame b (I0 a) y) *
            (T y fun a : Fin s => e.localFrame b (J0 a) y)) x₀ := by
    refine tendsto_finset_sum _ fun I0 _ => tendsto_finset_sum _ fun J0 _ => ?_
    have hprod : ContinuousAt (fun y => ∏ a : Fin s, (Gm y)⁻¹ (I0 a) (J0 a)) x₀ :=
      tendsto_finset_prod _ fun a _ => hGinvEnt (I0 a) (J0 a)
    exact (hprod.mul (hslots s T I0)).mul (hslots s T J0)

  have hev : (fun y : M => normSq0S (I := I) g y s (T y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ I0 : Fin s -> Fin (Module.finrank ℝ E),
          ∑ J0 : Fin s -> Fin (Module.finrank ℝ E),
            (∏ a : Fin s, (Gm y)⁻¹ (I0 a) (J0 a)) *
                (T y fun a : Fin s => e.localFrame b (I0 a) y) *
              (T y fun a : Fin s => e.localFrame b (J0 a) y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy
    rw [normSq0S_eq_coord (I := I) g y s (e.basisAt b hy)
      (fun i j => (Gm y)⁻¹ i j) (hinvw y hy) (T y)]
    unfold coordInner0S
    refine Finset.sum_congr rfl fun I0 _ => Finset.sum_congr rfl fun J0 _ => ?_
    rw [tensor0SComponent_apply, tensor0SComponent_apply]
    have h1 : (T y) (fun a : Fin s => (e.basisAt b hy) (I0 a)) =
        (T y) fun a : Fin s => e.localFrame b (I0 a) y :=
      congrArg (T y) (funext fun a => (e.localFrame_apply_of_mem_baseSet b hy).symm)
    have h2 : (T y) (fun a : Fin s => (e.basisAt b hy) (J0 a)) =
        (T y) fun a : Fin s => e.localFrame b (J0 a) y :=
      congrArg (T y) (funext fun a => (e.localFrame_apply_of_mem_baseSet b hy).symm)
    rw [h1, h2]
  exact hF.congr hev.symm




theorem normSq0S_cont {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Continuous (fun y : M => normSq0S (I := I) g y s (T y)) :=
  continuous_iff_continuousAt.2 fun x₀ => normSq0S_contAt (I := I) g T x₀

end NormSqContinuity

end

end Tensor0SBundle
