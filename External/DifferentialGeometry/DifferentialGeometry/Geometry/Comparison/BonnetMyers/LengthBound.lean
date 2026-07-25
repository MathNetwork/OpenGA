import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic















noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation








omit [SigmaCompactSpace M] in
theorem ricci_eq_sum_sectional_curvature_of_orthonormal_perp_frame
    (g : SmoothRiemannianMetric I M) (x : M) (X : E)
    (hUnit : g.inner x X X = 1)
    (e : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (hPerp : ∀ i, g.inner x (e i) X = 0) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) X X) (e i))
      = ricciTensor (I := I) g x X X := by
  classical
  have hn_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn_eq : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E :=
    Nat.succ_pred_eq_of_pos hn_pos
  let B' : Fin (Module.finrank ℝ E - 1 + 1) → E := Fin.cases X e
  let B : Fin (Module.finrank ℝ E) → E := fun i => B' (Fin.cast hn_eq.symm i)
  have hB_zero : B (⟨0, hn_pos⟩ : Fin (Module.finrank ℝ E)) = X := by
    change B' (Fin.cast hn_eq.symm ⟨0, hn_pos⟩) = X
    have hcast_eq : Fin.cast hn_eq.symm (⟨0, hn_pos⟩ : Fin (Module.finrank ℝ E)) =
        (0 : Fin (Module.finrank ℝ E - 1 + 1)) := by
      apply Fin.ext
      rfl
    rw [hcast_eq]
    rfl
  have hσ_lt : ∀ i : Fin (Module.finrank ℝ E - 1), i.val + 1 < Module.finrank ℝ E := by
    intro i
    have hi : i.val < Module.finrank ℝ E - 1 := i.isLt
    omega
  let σ : Fin (Module.finrank ℝ E - 1) → Fin (Module.finrank ℝ E) :=
    fun i => ⟨i.val + 1, hσ_lt i⟩
  have hB_succ : ∀ i : Fin (Module.finrank ℝ E - 1), B (σ i) = e i := by
    intro i
    change B' (Fin.cast hn_eq.symm (σ i)) = e i
    have hsucc_eq : Fin.cast hn_eq.symm (σ i) = Fin.succ i := by
      apply Fin.ext
      rfl
    rw [hsucc_eq]
    rfl
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    by_cases hi : i.val = 0
    · have hi_eq : i = ⟨0, hn_pos⟩ := Fin.ext hi
      by_cases hj : j.val = 0
      · have hj_eq : j = ⟨0, hn_pos⟩ := Fin.ext hj
        rw [hi_eq, hj_eq, hB_zero, hUnit]
        rw [if_pos rfl]
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        let k : Fin (Module.finrank ℝ E - 1) :=
          ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj_eq : j = σ k := by
          apply Fin.ext
          change j.val = (j.val - 1) + 1
          omega
        rw [hi_eq, hj_eq, hB_zero, hB_succ]
        have h_inner : g.inner x X (e k) = 0 := by
          rw [g.symm x X (e k)]
          exact hPerp k
        rw [h_inner]
        rw [if_neg]
        intro h
        have hval := congrArg Fin.val h
        change 0 = k.val + 1 at hval
        omega
    · have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
      let k : Fin (Module.finrank ℝ E - 1) :=
        ⟨i.val - 1, by have := i.isLt; omega⟩
      have hi_eq : i = σ k := by
        apply Fin.ext
        change i.val = (i.val - 1) + 1
        omega
      by_cases hj : j.val = 0
      · have hj_eq : j = ⟨0, hn_pos⟩ := Fin.ext hj
        rw [hi_eq, hj_eq, hB_succ, hB_zero]
        have h_inner : g.inner x (e k) X = 0 := hPerp k
        rw [h_inner]
        rw [if_neg]
        intro h
        have hval := congrArg Fin.val h
        change k.val + 1 = 0 at hval
        omega
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
        let l : Fin (Module.finrank ℝ E - 1) :=
          ⟨j.val - 1, by have := j.isLt; omega⟩
        have hj_eq : j = σ l := by
          apply Fin.ext
          change j.val = (j.val - 1) + 1
          omega
        rw [hi_eq, hj_eq, hB_succ, hB_succ]
        have h_inner : g.inner x (e k) (e l) = if k = l then (1 : ℝ) else 0 := hON k l
        rw [h_inner]
        by_cases hkl : k = l
        · rw [hkl]
          simp
        · rw [if_neg hkl, if_neg]
          intro hσ_eq
          apply hkl
          apply Fin.ext
          have hval := congrArg Fin.val hσ_eq
          change k.val + 1 = l.val + 1 at hval
          omega
  rw [ricciTensor_eq_orthonormal_trace (I := I) g x X X B hB_orth]
  have hsum_split :
      ∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x X X X) X +
          ∑ i : Fin (Module.finrank ℝ E - 1),
            g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) X X) (e i) := by
    have heq_sum :
        ∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i) =
        ∑ j : Fin (Module.finrank ℝ E - 1 + 1),
          g.inner x (riemannOp (LeviCivita (I := I) g) x (B (finCongr hn_eq j)) X X)
            (B (finCongr hn_eq j)) :=
      (Equiv.sum_comp (finCongr hn_eq)
        (fun i => g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) X X) (B i))).symm
    rw [heq_sum]
    rw [Fin.sum_univ_succ]
    have h0 : (finCongr hn_eq (0 : Fin (Module.finrank ℝ E - 1 + 1)) :
              Fin (Module.finrank ℝ E)) = ⟨0, hn_pos⟩ := by
      apply Fin.ext
      rfl
    rw [h0, hB_zero]
    refine congrArg (fun s : ℝ =>
        g.inner x (riemannOp (LeviCivita (I := I) g) x X X X) X + s)
      (Finset.sum_congr rfl ?_)
    intro i _
    have heq : finCongr hn_eq i.succ = σ i := by
      apply Fin.ext
      rfl
    rw [heq, hB_succ]
  rw [hsum_split]
  have hR_self : riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
    have h := riemannOp_swap (LeviCivita (I := I) g) x X X X
    have hsum : riemannOp (LeviCivita (I := I) g) x X X X +
        riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
      rw [eq_neg_iff_add_eq_zero] at h
      exact h
    have h_two : (2 : ℝ) • riemannOp (LeviCivita (I := I) g) x X X X = 0 := by
      rw [two_smul]; exact hsum
    rcases smul_eq_zero.mp h_two with h2_zero | hv_zero
    · exact absurd h2_zero (by norm_num)
    · exact hv_zero
  rw [hR_self]
  simp only [map_zero, ContinuousLinearMap.zero_apply, zero_add]








omit [SigmaCompactSpace M] in
theorem sum_index_form_integrand_eval
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {L : ℝ} (_hL : 0 < L) (uPrime : ℝ → E)
    (_huPrimeEq : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ)
    (_heDiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t)
    (_hParallel : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ (e i).toFun t = 0)
    (_hON : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
      g.inner (γ t) ((e i).toFun t) ((e j).toFun t) = if i = j then 1 else 0)
    (_hPerp : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
      g.inner (γ t) ((e i).toFun t) (uPrime t) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      (∑ i : Fin (Module.finrank ℝ E - 1),
          indexFormIntegrand (I := I) g γ
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
        = (Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t) := by
  classical
  intro t ht
  set sinπL : ℝ := Real.sin (Real.pi * t / L) with hsinπL
  set cosπL : ℝ := Real.cos (Real.pi * t / L) with hcosπL
  set piOverL : ℝ := Real.pi / L with hpiOverL
  have h_weight_hasDeriv :
      HasDerivAt (fun s : ℝ => Real.sin (Real.pi * s / L))
        (piOverL * cosπL) t := by
    have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h_lin : HasDerivAt (fun s : ℝ => Real.pi * s) (Real.pi * 1) t :=
      hid.const_mul Real.pi
    have h_lin' : HasDerivAt (fun s : ℝ => Real.pi * s) Real.pi t := by
      simpa using h_lin
    have hinner : HasDerivAt (fun s : ℝ => Real.pi * s / L) (Real.pi / L) t := by
      simpa [mul_div_assoc] using h_lin'.div_const L
    have hsin : HasDerivAt
        ((fun u => Real.sin u) ∘ (fun s : ℝ => Real.pi * s / L))
        (Real.cos (Real.pi * t / L) * (Real.pi / L)) t :=
      (Real.hasDerivAt_sin (Real.pi * t / L)).comp t hinner
    have hsin' : HasDerivAt (fun s : ℝ => Real.sin (Real.pi * s / L))
        (Real.cos (Real.pi * t / L) * (Real.pi / L)) t := hsin
    have : Real.cos (Real.pi * t / L) * (Real.pi / L) = piOverL * cosπL := by
      simp [piOverL, cosπL, mul_comm]
    rw [this] at hsin'
    exact hsin'
  have h_gammaPrime : (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t :=
    _huPrimeEq t ht
  have h_nabla_V :
      ∀ i : Fin (Module.finrank ℝ E - 1),
        covDerivAlong (I := I) g γ
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t
          = (piOverL * cosπL) • (e i).toFun t := by
    intro i
    have h_weight_diff : DifferentiableAt ℝ (fun s : ℝ => Real.sin (Real.pi * s / L)) t :=
      h_weight_hasDeriv.differentiableAt
    have h_chartrep_diff :
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t :=
      _heDiff i t ht
    have h_leibniz :=
      covDerivAlong_smulFun (I := I) g γ
        (fun s => Real.sin (Real.pi * s / L)) (e i).toFun t h_weight_diff h_chartrep_diff
    rw [_hParallel i t ht, smul_zero, add_zero, h_weight_hasDeriv.deriv] at h_leibniz
    exact h_leibniz
  have h_integrand_i :
      ∀ i : Fin (Module.finrank ℝ E - 1),
        indexFormIntegrand (I := I) g γ
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t
        = (piOverL * cosπL) ^ 2
          - sinπL ^ 2 *
              g.inner (γ t)
                (riemannOp (LeviCivita (I := I) g) (γ t)
                  ((e i).toFun t) (uPrime t) (uPrime t))
                ((e i).toFun t) := by
    intro i
    have h_ndV := h_nabla_V i
    have h_V_val :
        (SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun t
          = sinπL • (e i).toFun t := by simp [sinπL]
    have h_inner_ND :
        g.inner (γ t)
            ((piOverL * cosπL) • (e i).toFun t)
            ((piOverL * cosπL) • (e i).toFun t)
          = (piOverL * cosπL) ^ 2 := by
      have hpull1 : g.inner (γ t) ((piOverL * cosπL) • (e i).toFun t)
            = (piOverL * cosπL) • g.inner (γ t) ((e i).toFun t) :=
        (g.inner (γ t)).map_smul (piOverL * cosπL) ((e i).toFun t)
      rw [hpull1]
      have : ((piOverL * cosπL) • g.inner (γ t) ((e i).toFun t))
              ((piOverL * cosπL) • (e i).toFun t)
            = (piOverL * cosπL) *
              (g.inner (γ t) ((e i).toFun t))
                ((piOverL * cosπL) • (e i).toFun t) := by
        simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [this]
      have hpull2 :
          (g.inner (γ t) ((e i).toFun t)) ((piOverL * cosπL) • (e i).toFun t)
            = (piOverL * cosπL) *
              (g.inner (γ t) ((e i).toFun t)) ((e i).toFun t) := by
        have hms : (g.inner (γ t) ((e i).toFun t)) ((piOverL * cosπL) • (e i).toFun t)
            = (piOverL * cosπL) • (g.inner (γ t) ((e i).toFun t)) ((e i).toFun t) :=
          (g.inner (γ t) ((e i).toFun t)).map_smul (piOverL * cosπL) ((e i).toFun t)
        rw [hms]
        rw [smul_eq_mul]
      rw [hpull2]
      have hON_ii : g.inner (γ t) ((e i).toFun t) ((e i).toFun t) = 1 := by
        have := _hON t ht i i
        simpa using this
      rw [hON_ii]; ring
    have h_riem_pullout :
        riemannOp (LeviCivita (I := I) g) (γ t)
            (sinπL • (e i).toFun t)
            (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          = sinπL •
            riemannOp (LeviCivita (I := I) g) (γ t)
              ((e i).toFun t)
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) := by
      have hsmul :
          riemannOp (LeviCivita (I := I) g) (γ t)
              (sinπL • (e i).toFun t)
            = sinπL •
              riemannOp (LeviCivita (I := I) g) (γ t) ((e i).toFun t) := by
        exact (riemannOp (LeviCivita (I := I) g) (γ t)).map_smul sinπL
          ((e i).toFun t)
      rw [hsmul]
      simp [ContinuousLinearMap.smul_apply]
    have h_gp : mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) = uPrime t := h_gammaPrime
    have h_inner_R :
        g.inner (γ t)
            (riemannOp (LeviCivita (I := I) g) (γ t)
              (sinπL • (e i).toFun t)
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
            (sinπL • (e i).toFun t)
          = sinπL ^ 2 *
              g.inner (γ t)
                (riemannOp (LeviCivita (I := I) g) (γ t)
                  ((e i).toFun t) (uPrime t) (uPrime t))
                ((e i).toFun t) := by
      rw [h_riem_pullout]
      have hL1 :
          g.inner (γ t)
              (sinπL • riemannOp (LeviCivita (I := I) g) (γ t)
                ((e i).toFun t)
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))
            = sinπL • g.inner (γ t)
              (riemannOp (LeviCivita (I := I) g) (γ t)
                ((e i).toFun t)
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))) :=
        (g.inner (γ t)).map_smul sinπL _
      rw [hL1]
      have hR1 :
          (sinπL • g.inner (γ t)
              (riemannOp (LeviCivita (I := I) g) (γ t)
                ((e i).toFun t)
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))))
            (sinπL • (e i).toFun t)
            = sinπL *
              (g.inner (γ t)
                (riemannOp (LeviCivita (I := I) g) (γ t)
                  ((e i).toFun t)
                  (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
                  (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))))
              (sinπL • (e i).toFun t) := by
        simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hR1]
      have hR2 :
          (g.inner (γ t)
              (riemannOp (LeviCivita (I := I) g) (γ t)
                ((e i).toFun t)
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))))
            (sinπL • (e i).toFun t)
            = sinπL *
              (g.inner (γ t)
                (riemannOp (LeviCivita (I := I) g) (γ t)
                  ((e i).toFun t)
                  (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
                  (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))))
              ((e i).toFun t) := by
        have hms : (g.inner (γ t)
            (riemannOp (LeviCivita (I := I) g) (γ t)
              ((e i).toFun t)
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))))
              (sinπL • (e i).toFun t)
            = sinπL • (g.inner (γ t)
              (riemannOp (LeviCivita (I := I) g) (γ t)
                ((e i).toFun t)
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
                (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))))
              ((e i).toFun t) :=
          (g.inner (γ t)
            (riemannOp (LeviCivita (I := I) g) (γ t)
              ((e i).toFun t)
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)))).map_smul sinπL ((e i).toFun t)
        rw [hms]
        rw [smul_eq_mul]
      rw [hR2, h_gp]
      ring
    simp only [indexFormIntegrand]
    rw [h_ndV, h_V_val, h_inner_ND, h_inner_R]
  have h_sum_split :
      ∑ i : Fin (Module.finrank ℝ E - 1),
        indexFormIntegrand (I := I) g γ
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t
        = (∑ _i : Fin (Module.finrank ℝ E - 1), (piOverL * cosπL) ^ 2)
          - sinπL ^ 2 * ∑ i : Fin (Module.finrank ℝ E - 1),
            g.inner (γ t)
              (riemannOp (LeviCivita (I := I) g) (γ t)
                ((e i).toFun t) (uPrime t) (uPrime t))
              ((e i).toFun t) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E - 1),
            indexFormIntegrand (I := I) g γ
              ((SectionAlongCurve.smulFun
                (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
              ((SectionAlongCurve.smulFun
                (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
          = ∑ i : Fin (Module.finrank ℝ E - 1),
              ((piOverL * cosπL) ^ 2
                - sinπL ^ 2 *
                  g.inner (γ t)
                    (riemannOp (LeviCivita (I := I) g) (γ t)
                      ((e i).toFun t) (uPrime t) (uPrime t))
                    ((e i).toFun t))
        from Finset.sum_congr rfl (fun i _ => h_integrand_i i)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h_unit : g.inner (γ t) (uPrime t) (uPrime t) = 1 := _hUnit t ht
  have h_ON_e : ∀ i j, g.inner (γ t) ((e i).toFun t) ((e j).toFun t)
      = if i = j then 1 else 0 := _hON t ht
  have h_perp_e : ∀ i, g.inner (γ t) ((e i).toFun t) (uPrime t) = 0 :=
    _hPerp t ht
  have h_trace :
      (∑ i : Fin (Module.finrank ℝ E - 1),
          g.inner (γ t)
            (riemannOp (LeviCivita (I := I) g) (γ t)
              ((e i).toFun t) (uPrime t) (uPrime t))
            ((e i).toFun t))
        = ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t) :=
    ricci_eq_sum_sectional_curvature_of_orthonormal_perp_frame (I := I) g (γ t) (uPrime t)
      h_unit (fun i => (e i).toFun t) h_ON_e h_perp_e
  have hn_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have h_n_ge_one : 1 ≤ Module.finrank ℝ E := hn_pos
  have h_const_sum :
      (∑ _i : Fin (Module.finrank ℝ E - 1), (piOverL * cosπL) ^ 2)
        = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (piOverL * cosπL) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [h_sum_split, h_const_sum, h_trace]
  have h_cast : ((Module.finrank ℝ E - 1 : ℕ) : ℝ)
      = (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub h_n_ge_one, Nat.cast_one]
  rw [h_cast]
  ring














omit [SigmaCompactSpace M] in
theorem sum_index_form_frame_evaluation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {L : ℝ} (hL : 0 < L)
    (_hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L))
    (_hgeo : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (uPrime : ℝ → E)
    (huPrimeEq : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ)
    (heDiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t)
    (hParallel : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ (e i).toFun t = 0)
    (hON : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
      g.inner (γ t) ((e i).toFun t) ((e j).toFun t) = if i = j then 1 else 0)
    (hPerp : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
      g.inner (γ t) ((e i).toFun t) (uPrime t) = 0)
    (hIntegrandSum : ∀ i : Fin (Module.finrank ℝ E - 1),
      IntervalIntegrable
        (fun t : ℝ => indexFormIntegrand (I := I) g γ
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
        MeasureTheory.volume 0 L) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
      = ∫ t in (0 : ℝ)..L,
          ((Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)) := by
  classical
  have hIF : ∀ i,
      indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun
            (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun) =
        ∫ t in (0 : ℝ)..L,
          indexFormIntegrand (I := I) g γ
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t := by
    intro i
    exact indexForm_eq_intervalIntegral (I := I) g γ 0 L _ _
  have hSumEq : ∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun
            (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun) =
      ∫ t in (0 : ℝ)..L,
        ∑ i : Fin (Module.finrank ℝ E - 1),
          indexFormIntegrand (I := I) g γ
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t := by
    rw [show (∑ i : Fin (Module.finrank ℝ E - 1),
              indexForm (I := I) g γ 0 L
                ((SectionAlongCurve.smulFun
                  (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
                ((SectionAlongCurve.smulFun
                  (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
            = ∑ i : Fin (Module.finrank ℝ E - 1),
              ∫ t in (0 : ℝ)..L,
                indexFormIntegrand (I := I) g γ
                  ((SectionAlongCurve.smulFun
                    (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
                  ((SectionAlongCurve.smulFun
                    (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t
        from Finset.sum_congr rfl (fun i _ => hIF i)]
    exact (intervalIntegral.integral_finset_sum
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E - 1))))
      (f := fun i t =>
        indexFormIntegrand (I := I) g γ
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
      (fun i _ => hIntegrandSum i)).symm
  have hPointwise :
      Set.EqOn
        (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E - 1),
          indexFormIntegrand (I := I) g γ
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
        (fun t : ℝ =>
          (Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t))
        (Set.Icc (0 : ℝ) L) := by
    intro t ht
    exact sum_index_form_integrand_eval (I := I) g γ hL uPrime huPrimeEq
      hUnit e heDiff hParallel hON hPerp t ht
  rw [hSumEq]
  exact intervalIntegral.integral_congr
    (by
      intro t ht
      have hL_nonneg : (0 : ℝ) ≤ L := le_of_lt hL
      rw [Set.uIcc_of_le hL_nonneg] at ht
      exact hPointwise ht)











omit [SigmaCompactSpace M] in
theorem sum_index_form_bound_by_curvature_hypothesis
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {L : ℝ} (hL : 0 < L)
    (_hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L))
    (_hgeo : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) {K : ℝ}
    (hRic : RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K))
    (uPrime : ℝ → E)
    (huPrimeEq : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ)
    (heDiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t)
    (hParallel : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ (e i).toFun t = 0)
    (hON : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
      g.inner (γ t) ((e i).toFun t) ((e j).toFun t) = if i = j then 1 else 0)
    (hPerp : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
      g.inner (γ t) ((e i).toFun t) (uPrime t) = 0)
    (hIntegrandSum : ∀ i : Fin (Module.finrank ℝ E - 1),
      IntervalIntegrable
        (fun t : ℝ => indexFormIntegrand (I := I) g γ
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
        MeasureTheory.volume 0 L)
    (hRicIntegrable : IntervalIntegrable
      (fun t : ℝ => ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t))
      MeasureTheory.volume 0 L) :
    (∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
      ≤ (Module.finrank ℝ E - 1 : ℝ) * (L / 2) * ((Real.pi / L) ^ 2 - K) := by
  classical
  have hEval :
      (∑ i : Fin (Module.finrank ℝ E - 1),
        indexForm (I := I) g γ 0 L
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
      = ∫ t in (0 : ℝ)..L,
          ((Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)) :=
    sum_index_form_frame_evaluation (I := I) g γ hL _hγ _hgeo uPrime huPrimeEq
      hUnit e heDiff hParallel hON hPerp hIntegrandSum
  rw [hEval]
  have hL_nonneg : (0 : ℝ) ≤ L := le_of_lt hL
  have h_sin_cont : Continuous (fun t : ℝ => Real.sin (Real.pi * t / L)) := by
    have hcont : Continuous (fun t : ℝ => Real.pi * t / L) := by fun_prop
    exact Real.continuous_sin.comp hcont
  have h_cos_cont : Continuous (fun t : ℝ => Real.cos (Real.pi * t / L)) := by
    have hcont : Continuous (fun t : ℝ => Real.pi * t / L) := by fun_prop
    exact Real.continuous_cos.comp hcont
  have h_sinSq_cont : Continuous (fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2) :=
    h_sin_cont.pow 2
  have h_cosSq_cont : Continuous (fun t : ℝ => Real.cos (Real.pi * t / L) ^ 2) :=
    h_cos_cont.pow 2
  have hPtwise : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
            * Real.cos (Real.pi * t / L) ^ 2
        - Real.sin (Real.pi * t / L) ^ 2
            * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)
      ≤ (Module.finrank ℝ E - 1 : ℝ) *
          ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
            - K * Real.sin (Real.pi * t / L) ^ 2) := by
    intro t ht
    have hRicAt : (Module.finrank ℝ E - 1 : ℝ) * K * (g.inner (γ t) (uPrime t) (uPrime t))
        ≤ ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t) :=
      hRic (γ t) (uPrime t)
    have hUnit_t : g.inner (γ t) (uPrime t) (uPrime t) = 1 := hUnit t ht
    rw [hUnit_t, mul_one] at hRicAt
    have hsin_sq_nn : 0 ≤ Real.sin (Real.pi * t / L) ^ 2 := sq_nonneg _
    have h_mul : Real.sin (Real.pi * t / L) ^ 2 * ((Module.finrank ℝ E - 1 : ℝ) * K)
        ≤ Real.sin (Real.pi * t / L) ^ 2
            * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t) :=
      mul_le_mul_of_nonneg_left hRicAt hsin_sq_nn
    nlinarith [h_mul]
  have h_LHS_integrable :
      IntervalIntegrable
        (fun t : ℝ =>
          (Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t))
        MeasureTheory.volume 0 L := by
    refine IntervalIntegrable.sub ?_ ?_
    · have : Continuous (fun t : ℝ =>
          (Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
            * Real.cos (Real.pi * t / L) ^ 2) :=
        h_cosSq_cont.const_mul _
      exact this.intervalIntegrable 0 L
    · exact hRicIntegrable.continuousOn_mul h_sinSq_cont.continuousOn
  have h_RHS_integrable :
      IntervalIntegrable
        (fun t : ℝ =>
          (Module.finrank ℝ E - 1 : ℝ) *
            ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
              - K * Real.sin (Real.pi * t / L) ^ 2))
        MeasureTheory.volume 0 L := by
    have h_cont : Continuous (fun t : ℝ =>
        (Module.finrank ℝ E - 1 : ℝ) *
          ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
            - K * Real.sin (Real.pi * t / L) ^ 2)) := by
      refine Continuous.mul continuous_const ?_
      exact (h_cosSq_cont.const_mul _).sub (h_sinSq_cont.const_mul _)
    exact h_cont.intervalIntegrable 0 L
  have h_mono :
      (∫ t in (0 : ℝ)..L,
          ((Module.finrank ℝ E - 1 : ℝ) * (Real.pi / L) ^ 2
              * Real.cos (Real.pi * t / L) ^ 2
            - Real.sin (Real.pi * t / L) ^ 2
                * ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t)))
        ≤ ∫ t in (0 : ℝ)..L,
            (Module.finrank ℝ E - 1 : ℝ) *
              ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
                - K * Real.sin (Real.pi * t / L) ^ 2) :=
    intervalIntegral.integral_mono_on hL_nonneg h_LHS_integrable h_RHS_integrable
      hPtwise
  refine h_mono.trans ?_
  have h_pull_const :
      (∫ t in (0 : ℝ)..L,
        (Module.finrank ℝ E - 1 : ℝ) *
          ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
            - K * Real.sin (Real.pi * t / L) ^ 2))
      = (Module.finrank ℝ E - 1 : ℝ) *
          ∫ t in (0 : ℝ)..L,
            ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
              - K * Real.sin (Real.pi * t / L) ^ 2) :=
    intervalIntegral.integral_const_mul _ _
  rw [h_pull_const]
  have h_pi_div_L_ne : (Real.pi / L) ≠ 0 :=
    ne_of_gt (div_pos Real.pi_pos hL)
  have h_L_ne : L ≠ 0 := ne_of_gt hL
  have h_sinSq_fun :
      (fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2)
      = (fun t : ℝ => (fun x : ℝ => Real.sin x ^ 2) ((Real.pi / L) * t)) := by
    funext t
    congr 1
    congr 1
    field_simp
  have h_cosSq_fun :
      (fun t : ℝ => Real.cos (Real.pi * t / L) ^ 2)
      = (fun t : ℝ => (fun x : ℝ => Real.cos x ^ 2) ((Real.pi / L) * t)) := by
    funext t
    congr 1
    congr 1
    field_simp
  have h_intsinSq : ∫ t in (0 : ℝ)..L, Real.sin (Real.pi * t / L) ^ 2 = L / 2 := by
    rw [h_sinSq_fun,
        intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) h_pi_div_L_ne]
    have h_bndL : (Real.pi / L) * L = Real.pi := by field_simp
    have h_bnd0 : (Real.pi / L) * 0 = 0 := mul_zero _
    rw [h_bnd0, h_bndL, integral_sin_sq]
    rw [Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi, smul_eq_mul]
    field_simp
    ring
  have h_intcosSq : ∫ t in (0 : ℝ)..L, Real.cos (Real.pi * t / L) ^ 2 = L / 2 := by
    rw [h_cosSq_fun,
        intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) h_pi_div_L_ne]
    have h_bndL : (Real.pi / L) * L = Real.pi := by field_simp
    have h_bnd0 : (Real.pi / L) * 0 = 0 := mul_zero _
    rw [h_bnd0, h_bndL, integral_cos_sq]
    rw [Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi, smul_eq_mul]
    field_simp
    ring
  have h_cosSq_intInteg : IntervalIntegrable
      (fun t : ℝ => Real.cos (Real.pi * t / L) ^ 2) MeasureTheory.volume 0 L :=
    h_cosSq_cont.intervalIntegrable 0 L
  have h_sinSq_intInteg : IntervalIntegrable
      (fun t : ℝ => Real.sin (Real.pi * t / L) ^ 2) MeasureTheory.volume 0 L :=
    h_sinSq_cont.intervalIntegrable 0 L
  have h_split :
      (∫ t in (0 : ℝ)..L,
        ((Real.pi / L) ^ 2 * Real.cos (Real.pi * t / L) ^ 2
          - K * Real.sin (Real.pi * t / L) ^ 2))
      = (Real.pi / L) ^ 2 * (L / 2) - K * (L / 2) := by
    rw [intervalIntegral.integral_sub
        (h_cosSq_intInteg.const_mul ((Real.pi / L) ^ 2))
        (h_sinSq_intInteg.const_mul K),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      h_intsinSq, h_intcosSq]
  rw [h_split]
  apply le_of_eq
  ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in















theorem bonnet_myers_length_le_of_ricci_bound
    [T2Space (TangentBundle I M)] [ConnectedSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [CompleteSpace E]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {L : ℝ} (_hL : 0 < L)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (_hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ)
    (_hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L))
    (_hgeo : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) {K : ℝ}
    (_hK : 0 < K)
    (_hdim : 2 ≤ Module.finrank ℝ E)
    (_hRic : RicciBoundedBelow (I := I) g ((Module.finrank ℝ E - 1 : ℝ) * K))
    (uPrime : ℝ → E)
    (_huPrimeEq : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E) = uPrime t)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, g.inner (γ t) (uPrime t) (uPrime t) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ)
    (_heDiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (e i).toFun t) t)
    (_hParallel : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ (e i).toFun t = 0)
    (_hON : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
      g.inner (γ t) ((e i).toFun t) ((e j).toFun t) = if i = j then 1 else 0)
    (_hPerp : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
      g.inner (γ t) ((e i).toFun t) (uPrime t) = 0)
    (_hIntegrandSum : ∀ i : Fin (Module.finrank ℝ E - 1),
      IntervalIntegrable
        (fun t : ℝ => indexFormIntegrand (I := I) g γ
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
        MeasureTheory.volume 0 L)
    (_hRicIntegrable : IntervalIntegrable
      (fun t : ℝ => ricciTensor (I := I) g (γ t) (uPrime t) (uPrime t))
      MeasureTheory.volume 0 L)
    (_hmin : ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) →
      η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L)
    (_hVbundle : ∀ i : Fin (Module.finrank ℝ E - 1),
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t)
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun t)))) :
    L ≤ Real.pi / Real.sqrt K := by
  classical
  by_contra hcontra
  rw [not_le] at hcontra
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_sqrtK_pos : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr _hK
  have h_piOverL_pos : (0 : ℝ) < Real.pi / L := div_pos h_pi_pos _hL
  have h_nm1_ge_one : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast _hdim
    linarith
  have h_nm1_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) - 1 := by linarith
  have h_piOverL_lt_sqrtK : Real.pi / L < Real.sqrt K := by
    rw [div_lt_iff₀ h_sqrtK_pos] at hcontra
    rw [div_lt_iff₀ _hL]
    linarith
  have h_sq_lt_K : (Real.pi / L) ^ 2 < K := by
    have h_nonneg : (0 : ℝ) ≤ Real.pi / L := le_of_lt h_piOverL_pos
    have h_sqrtK_nonneg : (0 : ℝ) ≤ Real.sqrt K := le_of_lt h_sqrtK_pos
    have h_sq : (Real.pi / L) ^ 2 < (Real.sqrt K) ^ 2 := by
      have := mul_self_lt_mul_self h_nonneg h_piOverL_lt_sqrtK
      simpa [sq] using this
    rw [Real.sq_sqrt (le_of_lt _hK)] at h_sq
    exact h_sq
  have h_upper :
      (∑ i : Fin (Module.finrank ℝ E - 1),
          indexForm (I := I) g γ 0 L
            ((SectionAlongCurve.smulFun
              (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun))
        ≤ (Module.finrank ℝ E - 1 : ℝ) * (L / 2)
            * ((Real.pi / L) ^ 2 - K) :=
    sum_index_form_bound_by_curvature_hypothesis (I := I) g γ _hL _hγ _hgeo
      _hRic uPrime _huPrimeEq _hUnit e _heDiff _hParallel _hON _hPerp
      _hIntegrandSum _hRicIntegrable
  have h_each_nonneg : ∀ i : Fin (Module.finrank ℝ E - 1),
      0 ≤ indexForm (I := I) g γ 0 L
        ((SectionAlongCurve.smulFun
          (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
        ((SectionAlongCurve.smulFun
          (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun) := by
    intro i
    have hUnit_mfd : ∀ t ∈ Set.Icc (0 : ℝ) L,
        g.inner (γ t)
            (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1 := by
      intro t ht
      rw [_huPrimeEq t ht]
      exact _hUnit t ht
    have hVperp : ∀ t ∈ Set.Icc (0 : ℝ) L,
        g.inner (γ t)
            ((SectionAlongCurve.smulFun
              (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun t)
            (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0 := by
      intro t ht
      rw [_huPrimeEq t ht, SectionAlongCurve.smulFun_toFun]
      rw [show (g.inner (γ t)) (Real.sin (Real.pi * t / L) • (e i).toFun t)
            = Real.sin (Real.pi * t / L) • (g.inner (γ t)) ((e i).toFun t) from
          map_smul (g.inner (γ t)) _ _]
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, _hPerp t ht i, mul_zero]
    refine indexForm_nonneg_of_minimising_geodesic
      (I := I) g hEnorm γ L
      (fun t => (SectionAlongCurve.smulFun
        (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun t)
      _hL _hγ_smooth (_hVbundle i) _hgeo _hmin hUnit_mfd hVperp ?_ ?_
    · simp [SectionAlongCurve.smulFun_toFun, Real.sin_zero]
    · have hL_ne : L ≠ 0 := ne_of_gt _hL
      have h_arg : Real.pi * L / L = Real.pi := by field_simp
      simp [SectionAlongCurve.smulFun_toFun, h_arg, Real.sin_pi]
  have h_sum_nonneg :
      (0 : ℝ) ≤ ∑ i : Fin (Module.finrank ℝ E - 1),
          indexForm (I := I) g γ 0 L
            ((SectionAlongCurve.smulFun
              (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun)
            ((SectionAlongCurve.smulFun
              (fun t => Real.sin (Real.pi * t / L)) (e i)).toFun) :=
    Finset.sum_nonneg (fun i _ => h_each_nonneg i)
  have h_L_half_pos : (0 : ℝ) < L / 2 := by linarith
  have h_diff_neg : (Real.pi / L) ^ 2 - K < 0 := by linarith
  have h_upper_strict_neg :
      (Module.finrank ℝ E - 1 : ℝ) * (L / 2) * ((Real.pi / L) ^ 2 - K) < 0 := by
    have h_prod1_pos : (0 : ℝ) < (Module.finrank ℝ E - 1 : ℝ) * (L / 2) :=
      mul_pos h_nm1_pos h_L_half_pos
    exact mul_neg_of_pos_of_neg h_prod1_pos h_diff_neg
  linarith [h_sum_nonneg, h_upper, h_upper_strict_neg]

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
