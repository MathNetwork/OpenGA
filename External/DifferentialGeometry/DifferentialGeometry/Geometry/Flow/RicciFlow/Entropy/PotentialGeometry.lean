import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.Potential
import DifferentialGeometry.Geometry.Operator.Operators

set_option autoImplicit false








namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]



theorem potential_grad
    (g : SmoothRiemannianMetric I M) (n : Nat) {tau : Real}
    {u : M -> Real} (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (hpos : ∀ y : M, 0 < u y) (htau : 0 < tau) (x : M) :
    gradientFun (I := I) g (perelmanPotential n tau u) x =
      (-(u x)⁻¹) • gradientFun (I := I) g u x := by
  let pref : Real := perelmanDensityPrefactor n tau
  let logu : M -> Real := fun y => Real.log (u y)
  have hpref : 0 < pref := by
    simpa only [pref] using prefactor_pos n htau
  have hudiff (y : M) : MDifferentiableAt I 𝓘(Real, Real) u y :=
    hu.mdifferentiable (by simp) y
  have hlog_smooth : ContMDiff I 𝓘(Real, Real) ∞ logu := by
    intro y
    exact (Real.contDiffAt_log.2 (hpos y).ne').comp_contMDiffAt hu.contMDiffAt
  have hlogdiff (y : M) :
      MDifferentiableAt I 𝓘(Real, Real) logu y :=
    hlog_smooth.mdifferentiable (by simp) y
  have hpot_eq :
      perelmanPotential n tau u =
        fun y : M => ((-1 : Real) • logu) y - (-Real.log pref) := by
    funext y
    simp only [perelmanPotential, logu, Pi.smul_apply, smul_eq_mul]
    rw [Real.log_div (hpos y).ne' hpref.ne']
    dsimp only [pref]
    ring
  rw [hpot_eq]
  rw [gradientFun_sub (I := I) g
    ((hlogdiff x).const_smul (-1)) mdifferentiableAt_const]
  rw [gradientFun_const]
  simp only [sub_zero]
  rw [gradientFun_const_smul (I := I) g (-1) (hlogdiff x)]
  rw [gradientFun_log (I := I) g (hudiff x) (hpos x)]
  simp only [smul_smul]
  congr 1
  ring


theorem potential_grad_sq
    (g : SmoothRiemannianMetric I M) (n : Nat) {tau : Real}
    {u : M -> Real} (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (hpos : ∀ y : M, 0 < u y) (htau : 0 < tau) (x : M) :
    g.inner x
        (gradientFun (I := I) g (perelmanPotential n tau u) x)
        (gradientFun (I := I) g (perelmanPotential n tau u) x) =
      (u x ^ 2)⁻¹ *
        g.inner x
          (gradientFun (I := I) g u x)
          (gradientFun (I := I) g u x) := by
  rw [potential_grad (I := I) g n hu hpos htau x]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [(hpos x).ne']



omit [TopologicalSpace M] in
theorem potential_square
    (n : Nat) {tau : Real} {v : M -> Real}
    (hpos : ∀ y : M, 0 < v y) (htau : 0 < tau) (x : M) :
    perelmanPotential n tau (fun y => v y * v y) x =
      -Real.log (v x * v x) + Real.log (perelmanDensityPrefactor n tau) := by
  unfold perelmanPotential
  rw [Real.log_div
    (mul_ne_zero (hpos x).ne' (hpos x).ne') (prefactor_pos n htau).ne']
  ring



theorem square_pot_energy
    (g : SmoothRiemannianMetric I M) (n : Nat) {tau : Real}
    {v : M -> Real} (hv : ContMDiff I 𝓘(Real, Real) ∞ v)
    (hpos : ∀ y : M, 0 < v y) (htau : 0 < tau) (x : M) :
    (v x * v x) *
        g.inner x
          (gradientFun (I := I) g
            (perelmanPotential n tau (fun y => v y * v y)) x)
          (gradientFun (I := I) g
            (perelmanPotential n tau (fun y => v y * v y)) x) =
      4 * g.inner x
        (gradientFun (I := I) g v x)
        (gradientFun (I := I) g v x) := by
  have hvdiff (y : M) : MDifferentiableAt I 𝓘(Real, Real) v y :=
    hv.mdifferentiable (by simp) y
  have hvsq : ContMDiff I 𝓘(Real, Real) ∞ (fun y => v y * v y) :=
    hv.mul hv
  have hvsq_pos (y : M) : 0 < v y * v y := mul_pos (hpos y) (hpos y)
  rw [potential_grad_sq (I := I) g n hvsq hvsq_pos htau x]
  rw [gradientFun_mul_self (I := I) g (hvdiff x)]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [(hpos x).ne']
  ring

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
