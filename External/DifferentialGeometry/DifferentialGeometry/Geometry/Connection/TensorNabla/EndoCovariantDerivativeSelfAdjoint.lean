import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [CompleteSpace E] in
omit [SigmaCompactSpace M] in
theorem endoCovariantDerivative_g0_self_adjoint
    (g₀ : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (hΛ : ∀ (y : M) (a b : TangentSpace I y),
      g₀.inner y (Λ y a) b = g₀.inner y a (Λ y b))
    (x : M) (v : TangentSpace I x) (a b : TangentSpace I x) :
    g₀.inner x ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v a) b =
      g₀.inner x a ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v b) := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x a
  obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x b
  have hlamY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((Λ y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) Λ Y
  have hlamZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((Λ y) (Z y))) :=
    endoApplySection_contMDiff (I := I) (M := M) Λ Z
  let lamY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (Λ y) (Y y), hlamY⟩
  let lamZ : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (Λ y) (Z y), hlamZ⟩
  have hY_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) x :=
    Y.mdifferentiableAt
  have hZ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Z y)) x :=
    Z.mdifferentiableAt
  have hlamY_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (lamY y)) x :=
    lamY.mdifferentiableAt
  have hlamZ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (lamZ y)) x :=
    lamZ.mdifferentiableAt
  set cov := (LeviCivita (I := I) g₀).toFun with hcov_def
  have hMC := LeviCivita_isMetricCompatible (I := I) g₀
  have hfun_eq : (fun y : M => g₀.inner y (lamY y) (Z y)) =
      (fun y : M => g₀.inner y (Y y) (lamZ y)) := by
    funext y
    exact hΛ y (Y y) (Z y)
  have hmfderiv_eq :
      (mfderiv I 𝓘(ℝ) (fun y : M => g₀.inner y (lamY y) (Z y)) x) v =
        (mfderiv I 𝓘(ℝ) (fun y : M => g₀.inner y (Y y) (lamZ y)) x) v :=
    hfun_eq ▸ rfl
  have hleft := hMC.apply (Y := fun y => lamY y) (Z := fun y => Z y) hlamY_at hZ_at v
  have hright := hMC.apply (Y := fun y => Y y) (Z := fun y => lamZ y) hY_at hlamZ_at v
  rw [hleft, hright] at hmfderiv_eq
  have hendoY := endoCovariantDerivative_apply (I := I) (M := M) g₀ Λ Y x v
  have hendoZ := endoCovariantDerivative_apply (I := I) (M := M) g₀ Λ Z x v
  have hcovLamY : cov (fun y => lamY y) x v =
      (endoCovariantDerivative (I := I) (M := M) g₀) Λ x v (Y x) + (Λ x) (cov (fun y => Y y) x v) := by
    have heq : ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) (Y x) =
        cov (fun y => lamY y) x v - (Λ x) (cov (fun y => Y y) x v) := hendoY
    rw [eq_sub_iff_add_eq] at heq
    exact heq.symm
  have hcovLamZ : cov (fun y => lamZ y) x v =
      (endoCovariantDerivative (I := I) (M := M) g₀) Λ x v (Z x) + (Λ x) (cov (fun y => Z y) x v) := by
    have heq : ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) (Z x) =
        cov (fun y => lamZ y) x v - (Λ x) (cov (fun y => Z y) x v) := hendoZ
    rw [eq_sub_iff_add_eq] at heq
    exact heq.symm
  rw [hcovLamY, hcovLamZ] at hmfderiv_eq
  have hYx' : Y x = a := hYx
  have hZx' : Z x = b := hZx
  have hlamYx : (lamY : ∀ y, TangentSpace I y) x = (Λ x) a := by
    change (Λ x) (Y x) = (Λ x) a; rw [hYx']
  have hlamZx : (lamZ : ∀ y, TangentSpace I y) x = (Λ x) b := by
    change (Λ x) (Z x) = (Λ x) b; rw [hZx']
  have hcoeY : (LeviCivita (I := I) g₀ : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) (fun y => Y y) =
      cov (fun y => Y y) := rfl
  have hcoeZ : (LeviCivita (I := I) g₀ : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) (fun y => Z y) =
      cov (fun y => Z y) := rfl
  simp only [map_add, ContinuousLinearMap.add_apply, hYx', hZx', hlamYx, hlamZx,
    hcoeY, hcoeZ] at hmfderiv_eq
  have hcancel1 : g₀.inner x ((Λ x) (cov (fun y => Y y) x v)) b =
      g₀.inner x (cov (fun y => Y y) x v) ((Λ x) b) := hΛ x (cov (fun y => Y y) x v) b
  have hcancel2 : g₀.inner x ((Λ x) a) (cov (fun y => Z y) x v) =
      g₀.inner x a ((Λ x) (cov (fun y => Z y) x v)) :=
    hΛ x a (cov (fun y => Z y) x v)
  rw [hcancel1, hcancel2] at hmfderiv_eq
  have hreal :
      (g₀.inner x ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v a) b
          + g₀.inner x (cov (fun y => Y y) x v) ((Λ x) b)
          + g₀.inner x a ((Λ x) (cov (fun y => Z y) x v)) : ℝ) =
        (g₀.inner x (cov (fun y => Y y) x v) ((Λ x) b)
          + (g₀.inner x a ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v b)
            + g₀.inner x a ((Λ x) (cov (fun y => Z y) x v))) : ℝ) := hmfderiv_eq
  clear hmfderiv_eq hcancel1 hcancel2 hleft hright hcovLamY hcovLamZ hendoY hendoZ
    hlamYx hlamZx hcoeY hcoeZ hfun_eq
  generalize (g₀.inner x ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v a) b : ℝ) = A at hreal ⊢
  generalize (g₀.inner x (cov (fun y => Y y) x v) ((Λ x) b) : ℝ) = B at hreal
  generalize (g₀.inner x a ((Λ x) (cov (fun y => Z y) x v)) : ℝ) = C at hreal
  generalize (g₀.inner x a ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v b) : ℝ) = D at hreal ⊢
  linarith [hreal]

end Connection
end Integral
end DifferentialGeometry

end
