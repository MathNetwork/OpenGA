import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import Mathlib.Analysis.InnerProductSpace.Orthogonal



















noncomputable section

open Bundle Manifold Set Metric Module VectorField
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

omit [FiniteDimensional ℝ E] in


theorem ambDeriv_inner_normal {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ⟪ambDeriv (n := n) Y x v, (↑x : E)⟫ = - roundInner (n := n) x (Y x) v := by
  have hYd := dInclField_mdifferentiableAt (n := n) hY
  have hcoeC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hcoe : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hcoeC.mdifferentiableAt (by simp)

  have hf0 : (fun b => ⟪dInclField (n := n) Y b, (↑b : E)⟫) = fun _ => (0 : ℝ) := by
    funext b
    refine Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self (↑b : E)) ?_
    rw [dInclField_apply, ← range_mfderiv_coe_sphere (n := n) b]
    exact ⟨Y b, rfl⟩

  have hmf := mfderiv_inner (n := n) hYd hcoe v
  have hf0' : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun b => ⟪dInclField (n := n) Y b, (↑b : E)⟫) x v = 0 := by
    rw [hf0]; simp only [mfderiv_const]; rfl
  have hmf2 := hf0'.symm.trans hmf

  have hcoeval : mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v = dIncl (n := n) x v := rfl
  have hroundeq : ⟪dInclField (n := n) Y x,
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v⟫ = roundInner (n := n) x (Y x) v := by
    rw [hcoeval, dInclField_apply, roundInner_apply]
  rw [hroundeq] at hmf2
  exact eq_neg_of_add_eq_zero_left hmf2.symm

omit [FiniteDimensional ℝ E] in



theorem ambDeriv_gauss {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x}
    {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    ambDeriv (n := n) Y x v
      = dIncl (n := n) x (projConn (n := n) Y x v) - roundInner (n := n) x (Y x) v • (↑x : E) := by
  have hnorm : ‖(↑x : E)‖ = 1 := norm_eq_of_mem_sphere x

  have hsing : (ℝ ∙ (↑x : E)).starProjection (ambDeriv (n := n) Y x v)
      = ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ • (↑x : E) := by
    rw [Submodule.starProjection_singleton, hnorm]; norm_num

  have hproj : dIncl (n := n) x (projConn (n := n) Y x v)
      = ambDeriv (n := n) Y x v - ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ • (↑x : E) := by
    rw [dIncl_projConn, Submodule.coe_orthogonalProjection_apply]
    have hsplit := (ℝ ∙ (↑x : E)).starProjection_add_starProjection_orthogonal
      (ambDeriv (n := n) Y x v)
    rw [hsing] at hsplit
    exact eq_sub_of_add_eq (by rw [add_comm]; exact hsplit)

  have hcomm : ⟪(↑x : E), ambDeriv (n := n) Y x v⟫ = - roundInner (n := n) x (Y x) v := by
    rw [real_inner_comm]; exact ambDeriv_inner_normal (n := n) hY v
  rw [hproj, hcomm]
  module



noncomputable def ambDeriv2
    (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x →L[ℝ] E :=
  (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x :
    TangentSpace (𝓡 n) x →L[ℝ] E)

omit [FiniteDimensional ℝ E] in
@[simp] theorem ambDeriv2_apply
    (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ambDeriv2 (n := n) Z W x v
      = mfderiv (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x v := rfl







omit [FiniteDimensional ℝ E] in
theorem ambDeriv_bracket_symm
    (Z X Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1)
    (hDY : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (Y p)) x)
    (hDX : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (X p)) x) :
    ambDeriv2 (n := n) Z Y x (X x) - ambDeriv2 (n := n) Z X x (Y x)
      = ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) := by
  simp only [ambDeriv2_apply]
  refine ext_inner_left ℝ fun w => ?_

  have hZdiff : ∀ p : sphere (0 : E) 1,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Z)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))

  set gw := embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun (E := E) (n := n) w) with hgwdef
  have hgw : (⇑gw : sphere (0 : E) 1 → ℝ) = fun p => ⟪w, dInclField (n := n) (⇑Z) p⟫ := by
    funext p
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w) p = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (innerCoordFun w) p (Z p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) w) p (Z p) from rfl,
      mfderiv_innerCoordFun, dInclField_apply]

  have hWlevel : ∀ (W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯),
      (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) : sphere (0 : E) 1 → ℝ)
        = fun p => ⟪w, ambDeriv (n := n) (⇑Z) p (W p)⟫ := by
    intro W
    funext p
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) W gw p = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) gw p (W p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (⇑gw) p (W p) from rfl,
      hgw, mfderiv_inner_left w (hZdiff p) (W p), ambDeriv_apply]

  have hsecond : ∀ (V W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯),
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x →
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) V
          (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) : sphere (0 : E) 1 → ℝ) x
        = ⟪w, mfderiv (𝓡 n) 𝓘(ℝ, E)
            (fun p => ambDeriv (n := n) (⇑Z) p (W p)) x (V x)⟫ := by
    intro V W hD
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) V
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) x = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw) x (V x)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
              (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) W gw)) x (V x) from rfl,
      hWlevel W, mfderiv_inner_left w hD (V x)]

  have hbr := embedDeriv_mlieBracket (I := 𝓡 n) (M := sphere (0 : E) 1) X Y gw
  have hbrx : (embedDeriv (𝓡 n) (sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) gw : sphere (0 : E) 1 → ℝ) x
      = (embedDeriv (𝓡 n) (sphere (0 : E) 1) X
          (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y gw) : sphere (0 : E) 1 → ℝ) x
        - (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y
            (embedDeriv (𝓡 n) (sphere (0 : E) 1) X gw) : sphere (0 : E) 1 → ℝ) x := by
    have h := DFunLike.congr_fun hbr x
    simpa using h

  have hbrlevel : (embedDeriv (𝓡 n) (sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) gw : sphere (0 : E) 1 → ℝ) x
      = ⟪w, ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x)⟫ := by
    rw [hWlevel (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y)]
    rfl
  rw [hbrlevel, hsecond X Y hDY, hsecond Y X hDX] at hbrx
  rw [inner_sub_right]
  exact hbrx.symm





omit [FiniteDimensional ℝ E] in
theorem inner_dIncl_metricCov
    {S : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : sphere (0 : E) 1}
    (hS : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (S y))) x)
    (v W : TangentSpace (𝓡 n) x) :
    ⟪dIncl (n := n) x (Integral.Connection.metricCov (roundMetric (E := E) (n := n)) S x v),
        dIncl (n := n) x W⟫
      = ⟪ambDeriv (n := n) S x v, dIncl (n := n) x W⟫ := by
  rw [← projConn_eq_metricCov hS v, dIncl_projConn, ← Submodule.starProjection_apply]
  have hmem : dIncl (n := n) x W ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨W, rfl⟩
  have h0 := Submodule.starProjection_inner_eq_zero (K := (ℝ ∙ (↑x : E))ᗮ)
    (ambDeriv (n := n) S x v) (dIncl (n := n) x W) hmem
  rw [inner_sub_left, sub_eq_zero] at h0
  exact h0.symm

omit [FiniteDimensional ℝ E] in



theorem mdiffAt_inner_left (w : E) {F : sphere (0 : E) 1 → E} {x : sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun p => ⟪w, F p⟫) x := by
  haveI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (F x)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  exact ((innerSL ℝ w).hasFDerivAt.hasMFDerivAt.comp x hF.hasMFDerivAt).mdifferentiableAt

omit [FiniteDimensional ℝ E] in




theorem mfderiv_mul_innerCoordFun_of_inner_eq_zero
    (w : E) {φ : sphere (0 : E) 1 → ℝ} {x : sphere (0 : E) 1}
    (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ x) (horth : ⟪w, (↑x : E)⟫ = 0)
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => φ p * (innerCoordFun (E := E) (n := n) w) p) x v
      = φ x * ⟪w, dIncl (n := n) x v⟫ := by
  set ψ : sphere (0 : E) 1 → ℝ := ⇑(innerCoordFun (E := E) (n := n) w) with hψdef
  have hψ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) ψ x :=
    (innerCoordFun (E := E) (n := n) w).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hψx : ψ x = 0 := by rw [hψdef]; simpa [innerCoordFun] using horth


  have hψCLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) ψ x = (innerSL ℝ w).comp (dIncl (n := n) x) := by
    ext u
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) ψ x u = ⟪w, dIncl (n := n) x u⟫
    exact mfderiv_innerCoordFun (E := E) (n := n) w x u
  show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (φ * ψ) x v = φ x * ⟪w, dIncl (n := n) x v⟫
  rw [(hφ.hasMFDerivAt.mul hψ.hasMFDerivAt).mfderiv]
  simp only [hψx, hψCLM, zero_smul, add_zero]
  change φ x • (((innerSL ℝ w).comp (dIncl (n := n) x)) v) = φ x * ⟪w, dIncl (n := n) x v⟫
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]

set_option maxHeartbeats 800000 in




omit [FiniteDimensional ℝ E] in
theorem inner_ambDeriv_nested
    (Z Yf : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) (v W : TangentSpace (𝓡 n) x)
    (hD : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (Yf p)) x) :
    ⟪ambDeriv (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p)) x v,
        dIncl (n := n) x W⟫
      = ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z Yf x v⟫
        + roundInner (n := n) x (Z x) (Yf x) * ⟪dIncl (n := n) x W, dIncl (n := n) x v⟫ := by
  have hZp : ∀ p, MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y ((⇑Z) y))) p := fun p =>
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Z)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (hZp p)
  have hYfd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Yf)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (Yf.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hcoeC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hcoeM : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hcoeC.mdifferentiableAt (by simp)

  have hAfun : dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))
      = fun p => ambDeriv (n := n) (⇑Z) p (Yf p)
          + roundInner (n := n) p (Z p) (Yf p) • (↑p : E) := by
    funext p
    rw [dInclField_apply, ← projConn_eq_metricCov (hZp p) (Yf p),
      ambDeriv_gauss (n := n) (hZp p) (Yf p)]
    module

  have hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)) x := by
    have hb : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫) x _ :=
      ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).hasFDerivAt
        (dInclField (n := n) (⇑Z) x, dInclField (n := n) (⇑Yf) x)).hasMFDerivAt.comp x
        ((hZd x).hasMFDerivAt.prodMk (hYfd x).hasMFDerivAt)
    have heq : (fun p => roundInner (n := n) p (Z p) (Yf p))
        = fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫ := by
      funext p; rw [roundInner_apply]; rfl
    rw [heq]; exact hb.mdifferentiableAt

  have hAd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))) x := by
    rw [hAfun]; exact hD.add (hφ.smul hcoeM)
  have hψ0 : ⟪dIncl (n := n) x W, (↑x : E)⟫ = (0 : ℝ) :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _)
      (by rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨W, rfl⟩)


  rw [ambDeriv_apply, real_inner_comm, ← mfderiv_inner_left (dIncl (n := n) x W) hAd v]
  have hscal : (fun p => ⟪dIncl (n := n) x W, dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p)) p⟫)
      = (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫)
          + (fun p => roundInner (n := n) p (Z p) (Yf p)
              * (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) p) := by
    funext p
    simp only [Pi.add_apply, hAfun, inner_add_right, inner_smul_right]
    rfl
  have hMh1 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫) x :=
    mdiffAt_inner_left (dIncl (n := n) x W) hD
  have hMh2 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)
        * (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) p) x :=
    hφ.mul ((innerCoordFun (E := E) (n := n)
      (dIncl (n := n) x W)).contMDiff.contMDiffAt.mdifferentiableAt (by simp))


  have h1CLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫) x
        = (innerSL ℝ (dIncl (n := n) x W)).comp (ambDeriv2 (n := n) Z Yf x) := by
    ext u
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => ⟪dIncl (n := n) x W, ambDeriv (n := n) (⇑Z) p (Yf p)⟫) x u
          = ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z Yf x u⟫
    rw [mfderiv_inner_left (dIncl (n := n) x W) hD u, ← ambDeriv2_apply]
  have hψ0' : (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) x = 0 := by
    simpa [innerCoordFun] using hψ0
  have hψCLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) x
      = (innerSL ℝ (dIncl (n := n) x W)).comp (dIncl (n := n) x) := by
    ext u
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) x u
        = ⟪dIncl (n := n) x W, dIncl (n := n) x u⟫
    exact mfderiv_innerCoordFun (E := E) (n := n) (dIncl (n := n) x W) x u
  have h2CLM : mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)
        * (innerCoordFun (E := E) (n := n) (dIncl (n := n) x W)) p) x
        = (roundInner (n := n) x (Z x) (Yf x))
          • (innerSL ℝ (dIncl (n := n) x W)).comp (dIncl (n := n) x) := by
    show mfderiv (𝓡 n) 𝓘(ℝ, ℝ) ((fun p => roundInner (n := n) p (Z p) (Yf p))
        * ⇑(innerCoordFun (E := E) (n := n) (dIncl (n := n) x W))) x = _
    rw [(hφ.hasMFDerivAt.mul ((innerCoordFun (E := E) (n := n)
      (dIncl (n := n) x W)).contMDiff.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt).mfderiv,
      hψCLM, hψ0', zero_smul, add_zero]
  rw [hscal, mfderiv_add hMh1 hMh2, h1CLM, h2CLM]
  rfl




omit [FiniteDimensional ℝ E] in
theorem ambDeriv_section_mdiffAt
    (Z Yf : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (fun p => ambDeriv (n := n) (⇑Z) p (Yf p)) x := by
  have hZp : ∀ p, MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y ((⇑Z) y))) p := fun p =>
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Z)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (hZp p)
  have hYfd : ∀ p, MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n) (⇑Yf)) p := fun p =>
    dInclField_mdifferentiableAt (n := n) (Yf.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hcoeC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) x :=
    contMDiff_coe_sphere.contMDiffAt
  have hcoeM : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    hcoeC.mdifferentiableAt (by simp)
  have hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun p => roundInner (n := n) p (Z p) (Yf p)) x := by
    have hb : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫) x _ :=
      ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).hasFDerivAt
        (dInclField (n := n) (⇑Z) x, dInclField (n := n) (⇑Yf) x)).hasMFDerivAt.comp x
        ((hZd x).hasMFDerivAt.prodMk (hYfd x).hasMFDerivAt)
    have heq : (fun p => roundInner (n := n) p (Z p) (Yf p))
        = fun p => ⟪dInclField (n := n) (⇑Z) p, dInclField (n := n) (⇑Yf) p⟫ := by
      funext p; rw [roundInner_apply]; rfl
    rw [heq]; exact hb.mdifferentiableAt
  have hAd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) (dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))) x :=
    dInclField_mdifferentiableAt (n := n)
      ((Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (Integral.Connection.metricCov (roundMetric (E := E) (n := n)))
        (Integral.Connection.metricCov_smooth (roundMetric (E := E) (n := n))) Yf Z x).mdifferentiableAt
        (by simp))
  have hAfun : dInclField (n := n)
        (fun p => Integral.Connection.metricCov (roundMetric (E := E) (n := n)) (⇑Z) p (Yf p))
      = fun p => ambDeriv (n := n) (⇑Z) p (Yf p)
          + roundInner (n := n) p (Z p) (Yf p) • (↑p : E) := by
    funext p
    rw [dInclField_apply, ← projConn_eq_metricCov (hZp p) (Yf p),
      ambDeriv_gauss (n := n) (hZp p) (Yf p)]
    module
  rw [eq_sub_of_add_eq hAfun.symm]
  exact hAd.sub (hφ.smul hcoeM)

set_option maxHeartbeats 800000 in





omit [FiniteDimensional ℝ E] in
theorem dIncl_curv_inner
    (Z X Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) (W : TangentSpace (𝓡 n) x)
    (hDY : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (Y p)) x)
    (hDX : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      (fun p => ambDeriv (n := n) (⇑Z) p (X p)) x) :
    ⟪dIncl (n := n) x (Integral.Connection.CovariantDerivative.riemannCurvatureAux
        (Integral.Connection.metricCov (roundMetric (E := E) (n := n))) (⇑X) (⇑Y) (⇑Z) x),
        dIncl (n := n) x W⟫
      = roundInner (n := n) x (Z x) (Y x) * ⟪dIncl (n := n) x (X x), dIncl (n := n) x W⟫
        - roundInner (n := n) x (Z x) (X x) * ⟪dIncl (n := n) x (Y x), dIncl (n := n) x W⟫ := by
  set g := roundMetric (E := E) (n := n) with hg

  have hZb : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y ((⇑Z) y))) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        ((fun p => Integral.Connection.metricCov g (⇑Z) p (Y p)) y))) x :=
    (Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
      (Integral.Connection.metricCov g) (Integral.Connection.metricCov_smooth g) Y Z x).mdifferentiableAt (by simp)
  have hB : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        ((fun p => Integral.Connection.metricCov g (⇑Z) p (X p)) y))) x :=
    (Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
      (Integral.Connection.metricCov g) (Integral.Connection.metricCov_smooth g) X Z x).mdifferentiableAt (by simp)

  rw [show Integral.Connection.CovariantDerivative.riemannCurvatureAux
        (Integral.Connection.metricCov g) (⇑X) (⇑Y) (⇑Z) x
      = Integral.Connection.metricCov g (fun p => Integral.Connection.metricCov g (⇑Z) p (Y p)) x (X x)
        - Integral.Connection.metricCov g (fun p => Integral.Connection.metricCov g (⇑Z) p (X p)) x (Y x)
        - Integral.Connection.metricCov g (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) from rfl,
    map_sub, map_sub, inner_sub_left, inner_sub_left,
    inner_dIncl_metricCov hA (X x) W, inner_dIncl_metricCov hB (Y x) W,
    inner_dIncl_metricCov hZb (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) W,
    inner_ambDeriv_nested Z Y x (X x) W hDY, inner_ambDeriv_nested Z X x (Y x) W hDX]

  have hflat := ambDeriv_bracket_symm Z X Y x hDY hDX
  have hbr : ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z Y x (X x)⟫
      - ⟪dIncl (n := n) x W, ambDeriv2 (n := n) Z X x (Y x)⟫
        = ⟪ambDeriv (n := n) (⇑Z) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x), dIncl (n := n) x W⟫ := by
    rw [← inner_sub_right, hflat, real_inner_comm]
  rw [real_inner_comm (dIncl (n := n) x W) (dIncl (n := n) x (X x)),
    real_inner_comm (dIncl (n := n) x W) (dIncl (n := n) x (Y x))]
  linarith [hbr]

end Geometry
end DifferentialGeometry
