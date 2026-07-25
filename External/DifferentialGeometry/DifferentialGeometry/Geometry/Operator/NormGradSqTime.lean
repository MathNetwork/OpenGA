import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem gradSq_joint
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    {U : Set Real} (hUo : IsOpen U)
    (hG : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (U ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (f : Real -> M -> Real)
    (hf : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => f p.1 p.2) (U ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2)
          (gradientFun (I := I) (G.metric p.1) (f p.1) p.2))
      (U ×ˢ Set.univ) := by
  classical
  intro p hp
  let Idx := Fin (Module.finrank Real E)
  let x₀ : M := p.2
  let e := trivializationAt E (TangentSpace I) x₀
  let b := chartModelBasis E
  let frame : Idx -> (x : M) -> TangentSpace I x :=
    e.localFrame b
  have hframe : IsLocalFrameOn I E ∞ frame e.baseSet := by
    simpa only [frame] using e.isLocalFrameOn_localFrame_baseSet I ∞ b
  have hxe : x₀ ∈ e.baseSet := by
    simpa only [e] using
      mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Gm : (Real × M) -> Matrix Idx Idx Real := fun q =>
    chartGramMatrix (I := I) (G.metric q.1) x₀ q.2
  have hentry (i j : Idx) :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M => Gm q i j) p := by
    simpa only [Gm] using
      (hG x₀ i j).contMDiffAt
        ((hUo.prod e.open_baseSet).mem_nhds ⟨hp.1, hxe⟩)
  have hF :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M => f q.1 q.2) p :=
    hf.contMDiffAt
      ((hUo.prod isOpen_univ).mem_nhds ⟨hp.1, Set.mem_univ _⟩)
  let dF : (Real × M) -> Idx -> Real := fun q i =>
    extDerivFun (I := I) (f q.1) q.2 (frame i q.2)
  have hdF (i : Idx) :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M => dF q i) p := by
    simpa only [dF] using
      DifferentialGeometry.prodExtDerivAt_inf hF
        (hframe.contMDiffAt e.open_baseSet hxe i)
  have det_smooth
      (N : (Real × M) -> Matrix Idx Idx Real)
      (hN : ∀ i j : Idx,
        ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun q : Real × M => N q i j) p) :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M => (N q).det) p := by
    have hexp : (fun q : Real × M => (N q).det) = fun q : Real × M =>
        ∑ σ : Equiv.Perm Idx,
          ((Equiv.Perm.sign σ : ℤ) : Real) * ∏ i : Idx, N q (σ i) i := by
      funext q
      rw [Matrix.det_apply]
      simp [Units.smul_def]
    rw [hexp]
    refine ContMDiffAt.sum fun σ _ => ?_
    exact (contMDiffAt_const
      (c := (((Equiv.Perm.sign σ : ℤ) : Real)))).mul
        (ContMDiffAt.prod fun i _ => hN (σ i) i)
  have hdet :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M => (Gm q).det) p :=
    det_smooth Gm hentry
  have hadj (i j : Idx) :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M => (Gm q).adjugate i j) p := by
    simp_rw [Matrix.adjugate_apply]
    apply det_smooth
    intro a b
    by_cases ha : a = j
    · subst a
      simp only [Matrix.updateRow_self]
      exact contMDiffAt_const
    · simp only [Matrix.updateRow_ne ha]
      exact hentry a b
  have hdetne (q : Real × M) (hq : q.2 ∈ e.baseSet) : (Gm q).det ≠ 0 := by
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (G.metric q.1) x₀ hq)
  have hGinv (i j : Idx) :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M => (Gm q)⁻¹ i j) p := by
    have heq : (fun q : Real × M => (Gm q)⁻¹ i j) =
        fun q : Real × M => ((Gm q).det)⁻¹ * (Gm q).adjugate i j := by
      funext q
      rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
    rw [heq]
    exact (hdet.inv₀ (hdetne p hxe)).mul (hadj i j)
  let rhs : Real × M -> Real := fun q =>
    ∑ i : Idx, ∑ j : Idx, (Gm q)⁻¹ i j * dF q i * dF q j
  have hrhs :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞ rhs p := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact ((hGinv i j).mul (hdF i)).mul (hdF j)
  have hinv (q : Real × M) (hq : q.2 ∈ e.baseSet) :
      MetricInverseInBasis (I := I) (G.metric q.1) q.2
        (hframe.toBasisAt hq) (fun i j => (Gm q)⁻¹ i j) := by
    intro i j
    have hunit : IsUnit (Gm q).det :=
      isUnit_iff_ne_zero.2 (hdetne q hq)
    have hGb (i' j' : Idx) :
        (G.metric q.1).inner q.2
            (hframe.toBasisAt hq i') (hframe.toBasisAt hq j') =
          Gm q i' j' := by
      rw [hframe.toBasisAt_coe, hframe.toBasisAt_coe]
      simp only [Gm, chartGramMatrix_apply]
      change (G.metric q.1).inner q.2
          (e.localFrame b i' q.2) (e.localFrame b j' q.2) = _
      rw [e.localFrame_apply_of_mem_baseSet b hq,
        e.localFrame_apply_of_mem_baseSet b hq]
      rfl
    constructor
    · have hmul : (∑ k, (Gm q)⁻¹ i k * Gm q k j) =
          ((Gm q)⁻¹ * Gm q) i j := (Matrix.mul_apply).symm
      rw [Finset.sum_congr rfl fun k _ => by rw [hGb k j], hmul,
        Matrix.nonsing_inv_mul (Gm q) hunit, Matrix.one_apply]
    · have hmul : (∑ k, Gm q i k * (Gm q)⁻¹ k j) =
          (Gm q * (Gm q)⁻¹) i j := (Matrix.mul_apply).symm
      rw [Finset.sum_congr rfl fun k _ => by rw [hGb i k], hmul,
        Matrix.mul_nonsing_inv (Gm q) hunit, Matrix.one_apply]
  have heq :
      (fun q : Real × M =>
        (G.metric q.1).inner q.2
          (gradientFun (I := I) (G.metric q.1) (f q.1) q.2)
          (gradientFun (I := I) (G.metric q.1) (f q.1) q.2)) =ᶠ[𝓝 p] rhs := by
    filter_upwards [(hUo.prod e.open_baseSet).mem_nhds ⟨hp.1, hxe⟩] with q hq
    let df : Tensor0SSpace 1 I q.2 :=
      differential1FormFun (I := I) (f q.1) q.2
    have hsharp :
        cotangentSharp (I := I) (G.metric q.1) q.2 df =
          gradientFun (I := I) (G.metric q.1) (f q.1) q.2 := by
      apply tangentFlatLinear_injective (I := I) (G.metric q.1) q.2
      ext X
      change (G.metric q.1).inner q.2
          (cotangentSharp (I := I) (G.metric q.1) q.2 df) X =
        (G.metric q.1).inner q.2
          (gradientFun (I := I) (G.metric q.1) (f q.1) q.2) X
      rw [cotangentSharp_inner, cotangentToDual_apply]
      exact differential1FormFun_apply_eq_inner_gradientFun
        (I := I) (G.metric q.1) (f q.1) q.2 X
    calc
      (G.metric q.1).inner q.2
          (gradientFun (I := I) (G.metric q.1) (f q.1) q.2)
          (gradientFun (I := I) (G.metric q.1) (f q.1) q.2) =
          cotangentInner (I := I) (G.metric q.1) q.2 df df := by
            rw [cotangentInner_eq_sharp, hsharp]
      _ = ∑ i : Idx, ∑ j : Idx,
          (Gm q)⁻¹ i j * cotangentToDual (I := I) df (hframe.toBasisAt hq.2 i) *
            cotangentToDual (I := I) df (hframe.toBasisAt hq.2 j) :=
        cotangentInner_eq_coord (I := I) (G.metric q.1) q.2
          (hframe.toBasisAt hq.2) (fun i j => (Gm q)⁻¹ i j) (hinv q hq.2) df df
      _ = rhs q := by
        unfold rhs
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [df, dF, cotangentToDual_apply,
          differential1FormFun_apply_eq_extDerivFun,
          hframe.toBasisAt_coe]
  exact (hrhs.congr_of_eventuallyEq heq).contMDiffWithinAt




theorem normGradSq_time {x : M} {t : Real}
    (g : Real -> SmoothRiemannianMetric I M)
    (f : Real -> M -> Real) (ft : M -> Real)
    (Q : Tensor0SSpace 2 I x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hdf : ∀ X : TangentSpace I x,
      HasDerivAt
        (fun r : Real => extDerivFun (I := I) (f r) x X)
        (extDerivFun (I := I) ft x X) t) :
    HasDerivAt
      (fun r : Real =>
        (g r).inner x
          (gradientFun (I := I) (g r) (f r) x)
          (gradientFun (I := I) (g r) (f r) x))
      (2 * Q (fun a : Fin 2 =>
          if a = 0 then gradientFun (I := I) (g t) (f t) x
          else gradientFun (I := I) (g t) (f t) x) +
        2 * (g t).inner x
          (gradientFun (I := I) (g t) ft x)
          (gradientFun (I := I) (g t) (f t) x)) t := by
  let A : Real -> Tensor0SSpace 1 I x := fun r =>
    differential1FormFun (I := I) (f r) x
  let Adot : Tensor0SSpace 1 I x := differential1FormFun (I := I) ft x
  have hA (X : TangentSpace I x) :
      HasDerivAt
        (fun r : Real => A r (fun _ : Fin 1 => X))
        (Adot (fun _ : Fin 1 => X)) t := by
    simpa only [A, Adot, differential1FormFun_apply_eq_extDerivFun] using hdf X
  have hbase := normSq_one_time (I := I) g Q A Adot hg hA
  have hsharp (m : SmoothRiemannianMetric I M) (u : M -> Real) :
      cotangentSharp (I := I) m x (differential1FormFun (I := I) u x) =
        gradientFun (I := I) m u x := by
    apply tangentFlatLinear_injective (I := I) m x
    ext X
    change m.inner x
        (cotangentSharp (I := I) m x (differential1FormFun (I := I) u x)) X =
      m.inner x (gradientFun (I := I) m u x) X
    rw [cotangentSharp_inner, cotangentToDual_apply]
    exact differential1FormFun_apply_eq_inner_gradientFun (I := I) m u x X
  have hnorm (m : SmoothRiemannianMetric I M) (u : M -> Real) :
      normSq0S (I := I) m x 1 (differential1FormFun (I := I) u x) =
        m.inner x
          (gradientFun (I := I) m u x)
          (gradientFun (I := I) m u x) := by
    rw [normSq0S_eq_inner, inner0S_one_eq_cotangent, cotangentInner_eq_sharp,
      hsharp]
  have hcross :
      inner0S (I := I) (g t) x 1
          (differential1FormFun (I := I) ft x)
          (differential1FormFun (I := I) (f t) x) =
        (g t).inner x
          (gradientFun (I := I) (g t) ft x)
          (gradientFun (I := I) (g t) (f t) x) := by
    rw [inner0S_one_eq_cotangent, cotangentInner_eq_sharp,
      hsharp (g t) ft, hsharp (g t) (f t)]
  dsimp only [A, Adot] at hbase
  rw [hsharp (g t) (f t), hcross] at hbase
  exact hbase.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hnorm (g r) (f r)).symm)

end DifferentialGeometry.Integral.Connection
