import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConn
import DifferentialGeometry.Geometry.Connection.Realization.Embedding
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul
import DifferentialGeometry.Geometry.Curvature.Metric
import Mathlib.Analysis.InnerProductSpace.Calculus

















noncomputable section

open Bundle Manifold Set Metric Module VectorField
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]


noncomputable def innerCoordFun (w : E) : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯ :=
  ⟨fun p => ⟪w, (↑p : E)⟫, ((innerSL ℝ w).contMDiff).comp contMDiff_coe_sphere⟩

omit [FiniteDimensional ℝ E] in

theorem mfderiv_innerCoordFun (w : E) (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) w) p v = ⟪w, dIncl (n := n) p v⟫ := by
  haveI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (↑p : E)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  have hιC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) p :=
    contMDiff_coe_sphere.contMDiffAt
  have hι : HasMFDerivAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p (dIncl (n := n) p) :=
    (hιC.mdifferentiableAt (by simp)).hasMFDerivAt
  have hL : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (innerSL ℝ w) ((↑p : E)) (innerSL ℝ w) :=
    (innerSL ℝ w).hasFDerivAt.hasMFDerivAt
  have hfun : (⇑(innerCoordFun (E := E) (n := n) w)) = (innerSL ℝ w) ∘ ((↑) : sphere (0 : E) 1 → E) := by
    funext q; simp [innerCoordFun]
  have hcomp : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) ((innerSL ℝ w) ∘ ((↑) : sphere (0 : E) 1 → E)) p
      ((innerSL ℝ w).comp (dIncl (n := n) p)) := hL.comp p hι
  rw [hfun, hcomp.mfderiv]
  rfl

omit [FiniteDimensional ℝ E] in


theorem mfderiv_inner_left (w : E) {F : sphere (0 : E) 1 → E} {x : sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun p => ⟪w, F p⟫) x v
      = ⟪w, mfderiv (𝓡 n) 𝓘(ℝ, E) F x v⟫ := by
  haveI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) (F x)) :=
    inferInstanceAs (InnerProductSpace ℝ E)
  have hL : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (innerSL ℝ w) (F x) (innerSL ℝ w) :=
    (innerSL ℝ w).hasFDerivAt.hasMFDerivAt
  have hcomp : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) ((innerSL ℝ w) ∘ F) x
      ((innerSL ℝ w).comp (mfderiv (𝓡 n) 𝓘(ℝ, E) F x)) := hL.comp x hF.hasMFDerivAt
  have hfun : (fun p => ⟪w, F p⟫) = (innerSL ℝ w) ∘ F := by
    funext q; simp
  rw [hfun, hcomp.mfderiv]
  rfl

omit [FiniteDimensional ℝ E] in

theorem mfderiv_inner {F G : sphere (0 : E) 1 → E} {x : sphere (0 : E) 1}
    (hF : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) F x) (hG : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) G x)
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun b => ⟪F b, G b⟫) x v
      = ⟪mfderiv (𝓡 n) 𝓘(ℝ, E) F x v, G x⟫ + ⟪F x, mfderiv (𝓡 n) 𝓘(ℝ, E) G x v⟫ := by
  have hB : HasMFDerivAt 𝓘(ℝ, E × E) 𝓘(ℝ, ℝ) (fun p : E × E => ⟪p.1, p.2⟫) (F x, G x)
      (fderivInnerCLM ℝ (F x, G x)) :=
    (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E) |>.hasFDerivAt (F x, G x)).hasMFDerivAt
  have hpair : HasMFDerivAt (𝓡 n) 𝓘(ℝ, E × E) (fun b => (F b, G b)) x
      ((mfderiv (𝓡 n) 𝓘(ℝ, E) F x).prod (mfderiv (𝓡 n) 𝓘(ℝ, E) G x)) :=
    hF.hasMFDerivAt.prodMk hG.hasMFDerivAt
  have hcomp := (hB.comp x hpair).mfderiv
  rw [show (fun b => ⟪F b, G b⟫) = (fun p : E × E => ⟪p.1, p.2⟫) ∘ (fun b => (F b, G b)) from rfl,
    hcomp]
  change ⟪F x, mfderiv (𝓡 n) 𝓘(ℝ, E) G x v⟫ + ⟪mfderiv (𝓡 n) 𝓘(ℝ, E) F x v, G x⟫
    = ⟪mfderiv (𝓡 n) 𝓘(ℝ, E) F x v, G x⟫ + ⟪F x, mfderiv (𝓡 n) 𝓘(ℝ, E) G x v⟫
  ring





omit [FiniteDimensional ℝ E] in
theorem dIncl_mlieBracket
    (X Y : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
    (x : sphere (0 : E) 1) :
    dIncl (n := n) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x)
      = ambDeriv (n := n) (⇑Y) x (X x) - ambDeriv (n := n) (⇑X) x (Y x) := by
  refine ext_inner_left ℝ fun w => ?_

  have hbr := embedDeriv_mlieBracket (I := 𝓡 n) (M := sphere (0 : E) 1) X Y (innerCoordFun w)

  have hact : ∀ (Z : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯)
      (p : sphere (0 : E) 1),
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w) : sphere (0 : E) 1 → ℝ) p
        = ⟪w, dIncl (n := n) p (Z p)⟫ := by
    intro Z p
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w) p = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (innerCoordFun w) p (Z p)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (innerCoordFun (E := E) (n := n) w) p (Z p) from rfl,
      mfderiv_innerCoordFun]

  have hsecond : ∀ (Z W : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n), (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯),
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) W (embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w))
        : sphere (0 : E) 1 → ℝ) x = ⟪w, ambDeriv (n := n) (⇑Z) x (W x)⟫ := by
    intro Z W
    have hZC : ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞
        (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Z y))) x := Z.contMDiff.contMDiffAt
    have hZdiff := hZC.mdifferentiableAt (by simp)
    have hg : (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w)) : sphere (0 : E) 1 → ℝ)
        = fun p => ⟪w, dInclField (n := n) (⇑Z) p⟫ := by
      funext p; rw [hact Z p]; rfl
    change vectorFieldAction (𝓡 n) (sphere (0 : E) 1) W
      (embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w)) x = _
    simp only [vectorFieldAction]
    rw [show extDerivFun (I := 𝓡 n) (embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w)) x (W x)
          = mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
              (⇑(embedDeriv (𝓡 n) (sphere (0 : E) 1) Z (innerCoordFun w))) x (W x) from rfl,
      hg, mfderiv_inner_left w (dInclField_mdifferentiableAt (n := n) hZdiff) (W x), ambDeriv_apply]

  have hbrx : (embedDeriv (𝓡 n) (sphere (0 : E) 1)
        (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) (innerCoordFun w) : sphere (0 : E) 1 → ℝ) x
      = (embedDeriv (𝓡 n) (sphere (0 : E) 1) X
          (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y (innerCoordFun w)) : sphere (0 : E) 1 → ℝ) x
        - (embedDeriv (𝓡 n) (sphere (0 : E) 1) Y
            (embedDeriv (𝓡 n) (sphere (0 : E) 1) X (innerCoordFun w)) : sphere (0 : E) 1 → ℝ) x := by
    have h := DFunLike.congr_fun hbr x
    simpa using h
  rw [hact (mlieBracketSection (𝓡 n) (sphere (0 : E) 1) X Y) x, hsecond Y X, hsecond X Y] at hbrx
  rw [inner_sub_right]
  exact hbrx


omit [FiniteDimensional ℝ E] in
theorem projConn_torsion :
    (projConnCD (E := E) (n := n)).torsion = 0 := by
  haveI : IsManifold (𝓡 n) ∞ (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  funext x
  ext u v
  obtain ⟨X, hX⟩ : ∃ σ : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯, σ x = u :=
    ContMDiffSection.exists_eq_at x u
  obtain ⟨Y, hY⟩ : ∃ σ : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯, σ x = v :=
    ContMDiffSection.exists_eq_at x v
  have hXd : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (X y))) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYd : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply]
  rw [← hX, ← hY, (projConnCD (E := E) (n := n)).torsion_apply hXd hYd, sub_eq_zero]
  refine mfderiv_coe_sphere_injective x ?_
  change dIncl (n := n) x (projConn (n := n) (⇑Y) x (X x) - projConn (n := n) (⇑X) x (Y x))
    = dIncl (n := n) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x)
  rw [map_sub, dIncl_projConn, dIncl_projConn]
  have hmem : dIncl (n := n) x (mlieBracket (𝓡 n) (⇑X) (⇑Y) x) ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨_, rfl⟩
  rw [← Submodule.coe_sub, ← map_sub, ← dIncl_mlieBracket X Y x,
    ← Submodule.starProjection_apply, Submodule.starProjection_eq_self_iff.mpr hmem]

omit [FiniteDimensional ℝ E] in

theorem projConn_metricCompat :
    Integral.Connection.IsMetricCompatible (projConnCD (E := E) (n := n))
      (roundMetric (E := E) (n := n)) := by
  intro Y Z x hY hZ _ v
  have hYd := dInclField_mdifferentiableAt (n := n) hY
  have hZd := dInclField_mdifferentiableAt (n := n) hZ
  have hmemZ : dIncl (n := n) x (Z x) ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨Z x, rfl⟩
  have hmemY : dIncl (n := n) x (Y x) ∈ (ℝ ∙ (↑x : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) x]; exact ⟨Y x, rfl⟩
  have horth : ∀ (w u : E), u ∈ (ℝ ∙ (↑x : E))ᗮ →
      ⟪w, u⟫ = ⟪(↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjection w) : E), u⟫ := by
    intro w u hu
    rw [← Submodule.starProjection_apply]
    have h0 := Submodule.starProjection_inner_eq_zero (K := (ℝ ∙ (↑x : E))ᗮ) w u hu
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have horth_right : ∀ (w u : E), u ∈ (ℝ ∙ (↑x : E))ᗮ →
      ⟪u, w⟫ = ⟪u, (↑(((ℝ ∙ (↑x : E))ᗮ).orthogonalProjection w) : E)⟫ := by
    intro w u hu
    rw [← Submodule.starProjection_apply]
    have h0 := Submodule.starProjection_inner_eq_zero (K := (ℝ ∙ (↑x : E))ᗮ) w u hu
    rw [real_inner_comm, inner_sub_right, sub_eq_zero] at h0
    exact h0
  have hfun : (fun b => (roundMetric (E := E) (n := n)).inner b (Y b) (Z b))
      = fun b => ⟪dInclField (n := n) Y b, dInclField (n := n) Z b⟫ := by
    funext b; rw [roundMetric_inner]; rfl
  have hmf := mfderiv_inner (n := n) hYd hZd v
  rw [hfun]
  erw [hmf]
  simp only [roundMetric_inner]
  erw [dIncl_projConn, dIncl_projConn]
  simp only [ambDeriv_apply, dInclField_apply]
  congr 1
  · exact horth _ _ hmemZ
  · exact horth_right _ _ hmemY


omit [FiniteDimensional ℝ E] in
theorem projConn_eq_metricCov
    {Y : ∀ x : sphere (0 : E) 1, TangentSpace (𝓡 n) x} {x : sphere (0 : E) 1}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y => (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (Y y))) x)
    (v : TangentSpace (𝓡 n) x) :
    projConn (n := n) Y x v
      = Integral.Connection.metricCov (roundMetric (E := E) (n := n)) Y x v := by
  haveI : IsManifold (𝓡 n) ∞ (sphere (0 : E) 1) :=
    EuclideanSpace.instIsManifoldSphere.of_le le_top
  have htor₂ : (Integral.Connection.metricCov (roundMetric (E := E) (n := n))).torsion = 0 :=
    funext fun y =>
      Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree
        (roundMetric (E := E) (n := n)) y
  have hMC₂ : Integral.Connection.IsMetricCompatible
      (Integral.Connection.metricCov (roundMetric (E := E) (n := n)))
      (roundMetric (E := E) (n := n)) := by
    intro W₁ W₂ y hW₁ hW₂ _ vv
    obtain ⟨W, hWy⟩ : ∃ σ : Cₛ^∞⟮𝓡 n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)⟯, σ y = vv :=
      ContMDiffSection.exists_eq_at y vv
    have hgen := Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (roundMetric (E := E) (n := n)) y W W₁ W₂ W.mdifferentiableAt hW₁ hW₂
    rw [hWy] at hgen
    exact hgen
  exact Integral.Connection.koszul_levi_civita_unique_of_torsionFree_metricCompatible
    (projConnCD (E := E) (n := n)) (Integral.Connection.metricCov (roundMetric (E := E) (n := n)))
    projConn_torsion htor₂ projConn_metricCompat hMC₂ hY v

end Geometry
end DifferentialGeometry
