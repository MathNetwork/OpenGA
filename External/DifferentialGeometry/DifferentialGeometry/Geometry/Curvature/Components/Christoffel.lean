import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}







section CoordinateChristoffelCurvature

open DifferentialGeometry.Tensor.Coordinates





def christoffelCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j k : CoordinateIdx (𝕜 := Real) E) : Real :=
  christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ i j k


def christoffelCoordFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j k : CoordinateIdx (𝕜 := Real) E) (x : M) : Real :=
  christoffelSymbolInFrame cov (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x i j k


def christoffelCoordDerivAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (dir i j k : CoordinateIdx (𝕜 := Real) E) : Real :=
  extDerivFun (I := I) (christoffelCoordFun (I := I) cov x₀ i j k) x₀
    (coordinateFrameAt (I := I) x₀ dir x₀)







def christoffelCurvCoeffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i k j m : CoordinateIdx (𝕜 := Real) E) : Real :=
  christoffelCoordDerivAt (I := I) cov x₀ i k j m -
    christoffelCoordDerivAt (I := I) cov x₀ k i j m +
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelCoordAt (I := I) cov x₀ k j a *
        christoffelCoordAt (I := I) cov x₀ i a m) -
    (∑ a : CoordinateIdx (𝕜 := Real) E,
      christoffelCoordAt (I := I) cov x₀ i j a *
        christoffelCoordAt (I := I) cov x₀ k a m)








def christoffelRicciCoeffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  ∑ k : CoordinateIdx (𝕜 := Real) E,
    christoffelCurvCoeffAt (I := I) cov x₀ k i j k







theorem christoffelRicciCoeffAt_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    christoffelRicciCoeffAt (I := I) cov x₀ i j =
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        christoffelCoordDerivAt (I := I) cov x₀ k i j k) -
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        christoffelCoordDerivAt (I := I) cov x₀ i k j k) +
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelCoordAt (I := I) cov x₀ i j a *
            christoffelCoordAt (I := I) cov x₀ k a k) -
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          christoffelCoordAt (I := I) cov x₀ k j a *
            christoffelCoordAt (I := I) cov x₀ i a k) := by
  classical
  simp [christoffelRicciCoeffAt, christoffelCurvCoeffAt,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]







def ConnectionCurvatureCoordAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) : Prop :=
  ∀ i k j : CoordinateIdx (𝕜 := Real) E,
    (connectionRiemannCurvatureField (I := I) cov
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ k)
      (coordinateFrameAt (I := I) x₀ j)) x₀ =
        ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m •
            coordinateFrameAt (I := I) x₀ m x₀


omit [FiniteDimensional ℝ E] in
private theorem covariantDerivative_finset_sum
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Finset ι) (σ : ι -> (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov ((insert i t).sum σ) x) v
            = (cov (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov (σ i) x + cov (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov (σ i) x) v + (cov (t.sum σ) x) v := by
              simp
        _ = (insert i t).sum (fun j => (cov (σ j) x) v) := by
              rw [ih]
              simp [Finset.sum_insert, hit]






private theorem covariantDerivative_coordFrame_coeff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x₀ : M) (V : (x : M) -> TangentSpace I x)
    (i m : CoordinateIdx (𝕜 := Real) E)
    (hV : MDiffAt (T% V) x₀)
    (hcoeff : ∀ a : CoordinateIdx (𝕜 := Real) E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff a p (V p)) x₀) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff m x₀
        ((cov V x₀) (coordinateFrameAt (I := I) x₀ i x₀)) =
      extDerivFun (I := I)
        (fun p : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff m p (V p)) x₀
        (coordinateFrameAt (I := I) x₀ i x₀) +
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff a x₀ (V x₀) *
            christoffelCoordAt (I := I) cov x₀ i a m := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let z : CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun a p => hframe.coeff a p (V p)
  let term : CoordinateIdx (𝕜 := Real) E -> (p : M) -> TangentSpace I p :=
    fun a => z a • frame a
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hframe_mdiff (a : CoordinateIdx (𝕜 := Real) E) :
      MDiffAt (T% (frame a)) x₀ :=
    coordinateFrameAt_mdifferentiableAt (I := I) x₀ a
  have hterm_diff (a : CoordinateIdx (𝕜 := Real) E) : MDiffAt (T% (term a)) x₀ := by
    exact (hcoeff a).smul_section (hframe_mdiff a)
  have hsum_diff : MDiffAt
      (T% ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum term)) x₀ := by
    simpa using MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E))) (t := term) hterm_diff
  have hV_ev :
      V =ᶠ[nhds x₀]
        fun p : M => ∑ a : CoordinateIdx (𝕜 := Real) E, z a p • frame a p := by
    filter_upwards
      [(coordinateFrameSet_open (I := I) x₀).mem_nhds hx₀] with p hp
    simpa [z, frame, hframe] using (hframe.coeff_sum_eq V hp)
  have hcov_congr :
      cov V x₀ = cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum term) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hV hsum_diff
      (by simp) (by simpa [term] using hV_ev)
  have hcov_sum :
      (cov V x₀) (frame i x₀) =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          (extDerivFun (I := I) (z a) x₀ (frame i x₀) • frame a x₀ +
            z a x₀ • (cov (frame a) x₀) (frame i x₀)) := by
    calc
      (cov V x₀) (frame i x₀)
          = (cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)).sum term) x₀)
              (frame i x₀) := by
            rw [hcov_congr]
      _ = ∑ a : CoordinateIdx (𝕜 := Real) E, (cov (term a) x₀) (frame i x₀) := by
            exact covariantDerivative_finset_sum (I := I) cov
              (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)) term (frame i x₀) hterm_diff
      _ = ∑ a : CoordinateIdx (𝕜 := Real) E,
            (extDerivFun (I := I) (z a) x₀ (frame i x₀) • frame a x₀ +
              z a x₀ • (cov (frame a) x₀) (frame i x₀)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame a) (g := z a) (x := x₀)
              (hframe_mdiff a) (hcoeff a)) (frame i x₀))
            simpa [term, z, Pi.smul_apply, add_comm] using hleib
  rw [hcov_sum]
  rw [map_sum]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  have hdiag :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I) (z a) x₀ (frame i x₀) *
            hframe.coeff m x₀ (frame a x₀)) =
        extDerivFun (I := I) (z m) x₀ (frame i x₀) := by
    have hcoeff_frame (a : CoordinateIdx (𝕜 := Real) E) :
        hframe.coeff m x₀ (frame a x₀) = if a = m then 1 else 0 := by
      rw [coordinateFrameAt_coeff_eq_toBasis_coord (I := I) x₀ (frame a x₀) m]
      rw [show frame a x₀ = coordinateFrameAt_toBasis (I := I) x₀ a by
        simp [frame]]
      change ((coordinateFrameAt_toBasis (I := I) x₀).repr
          ((coordinateFrameAt_toBasis (I := I) x₀) a)) m =
        if a = m then 1 else 0
      by_cases ham : a = m
      · subst ham
        have hb := congrArg (fun f => f a)
          (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) a)
        simpa [coordinateFrameAt_toBasis_apply] using hb
      · have hb := congrArg (fun f => f m)
          (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) a)
        simpa [coordinateFrameAt_toBasis_apply, Finsupp.single_apply, ham] using hb
    rw [show
      (∑ a : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I) (z a) x₀ (frame i x₀) *
            hframe.coeff m x₀ (frame a x₀)) =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          (if a = m then extDerivFun (I := I) (z m) x₀ (frame i x₀) else 0) by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hcoeff_frame a]
        by_cases ham : a = m
        · subst ham
          simp
        · simp [ham]]
    simp
  have hconn :
      (∑ a : CoordinateIdx (𝕜 := Real) E,
          z a x₀ * hframe.coeff m x₀ ((cov (frame a) x₀) (frame i x₀))) =
        ∑ a : CoordinateIdx (𝕜 := Real) E,
          hframe.coeff a x₀ (V x₀) * christoffelCoordAt (I := I) cov x₀ i a m := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [z, christoffelCoordAt, frame]
  rw [hdiag, hconn]


private theorem coordinateFrame_covariantDeriv_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (x₀ : M) (k j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (coordinateFrameAt (I := I) x₀ j) p)
          (coordinateFrameAt (I := I) x₀ k p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let u := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hframe_j :
      CMDiff[u] ((∞ : WithTop ℕ∞) + 1) (T% (frame j)) := by
    exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn j).of_le
      (by simp)
  have hcov_j :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (frame j) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
        u := by
    simpa [u, frame] using (hcov hu).contMDiff hframe_j
  have hframe_k :
      CMDiff[u] (∞ : WithTop ℕ∞) (T% (frame k)) :=
    ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn k).of_le
      (by simp)
  have hW_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, (cov (frame j) p) (frame k p)⟩ :
            TotalSpace E (TangentSpace I : M -> Type _)))
        u := by
    simpa [frame] using hcov_j.clm_bundle_apply hframe_k
  simpa [u, frame] using (hW_on x₀ hx₀).contMDiffAt (hu.mem_nhds hx₀)

private theorem coordinateFrame_covariantDeriv_mdiffAt_one
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (x₀ : M) (k j : CoordinateIdx (𝕜 := Real) E) :
    MDiffAt
      (T% (fun p : M =>
        (cov (coordinateFrameAt (I := I) x₀ j) p)
          (coordinateFrameAt (I := I) x₀ k p))) x₀ := by
  let u := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hframe_j :
      CMDiff[u] ((1 : WithTop ℕ∞) + 1) (T% (frame j)) := by
    exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn j).of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcov_j :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (frame j) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
        u := by
    simpa [u, frame] using (hcov hu).contMDiff hframe_j
  have hframe_k :
      CMDiff[u] (1 : WithTop ℕ∞) (T% (frame k)) :=
    ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn k).of_le
      (by norm_num)
  have hW_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, (cov (frame j) p) (frame k p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _)))
        u := by
    simpa [frame] using hcov_j.clm_bundle_apply hframe_k
  exact ((hW_on x₀ hx₀).contMDiffAt (hu.mem_nhds hx₀)).mdifferentiableAt
    (by norm_num)



theorem christoffelCoordFun_mdiffAt_one
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (x₀ : M) (i j k : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (christoffelCoordFun (I := I) cov x₀ i j k) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  let b := Module.finBasis Real E
  let frame := coordinateFrameAt (I := I) x₀
  let Z : (x : M) -> TangentSpace I x :=
    fun p => (cov (frame j) p) (frame i p)
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hZ : MDiffAt (T% Z) x₀ := by
    simpa [Z, frame] using
      coordinateFrame_covariantDeriv_mdiffAt_one (I := I) cov hcov x₀ i j
  have hcoeff :=
    mdifferentiableAt_localFrame_coeff
      (I := I) (e := e) (b := b) hx hZ k
  simpa [christoffelCoordFun, christoffelSymbolInFrame, e, b, frame, Z,
    coordinateFrameAt, coordinateFrameAt_isLocalFrame_one,
    coordinateTrivializationAt] using hcoeff



private theorem coordinateFrame_coeff_contMDiffAt_of_contMDiffAt
    (Z : (x : M) -> TangentSpace I x) {x₀ : M}
    (hZ : ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (fun y : M => (⟨y, Z y⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (j : CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M =>
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀ := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hx : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hcoeff :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e)
      (b := Module.finBasis Real E) (s := Z)
      (k := (∞ : WithTop ℕ∞)) hx hZ j
  simpa [e, coordinateTrivializationAt, coordinateFrameAt_isLocalFrame_one,
    coordinateFrameAt] using hcoeff







theorem connection_curvature_coord_of_christoffel
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (x₀ : M) :
    ConnectionCurvatureCoordAt (I := I) cov x₀ := by
  classical
  intro i k j
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let Vkj : (x : M) -> TangentSpace I x :=
    fun p => (cov (frame j) p) (frame k p)
  let Vij : (x : M) -> TangentSpace I x :=
    fun p => (cov (frame j) p) (frame i p)
  have hVkj_smooth :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, Vkj p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    simpa [Vkj, frame] using
      coordinateFrame_covariantDeriv_contMDiffAt (I := I) cov hcov x₀ k j
  have hVij_smooth :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, Vij p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    simpa [Vij, frame] using
      coordinateFrame_covariantDeriv_contMDiffAt (I := I) cov hcov x₀ i j
  have hVkj : MDiffAt (T% Vkj) x₀ :=
    hVkj_smooth.mdifferentiableAt (by simp)
  have hVij : MDiffAt (T% Vij) x₀ :=
    hVij_smooth.mdifferentiableAt (by simp)
  have hcoeff_kj (a : CoordinateIdx (𝕜 := Real) E) :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => hframe.coeff a p (Vkj p)) x₀ :=
    (coordinateFrame_coeff_contMDiffAt_of_contMDiffAt (I := I) Vkj
      hVkj_smooth a).mdifferentiableAt (by simp)
  have hcoeff_ij (a : CoordinateIdx (𝕜 := Real) E) :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M => hframe.coeff a p (Vij p)) x₀ :=
    (coordinateFrame_coeff_contMDiffAt_of_contMDiffAt (I := I) Vij
      hVij_smooth a).mdifferentiableAt (by simp)
  have hcov_i (m : CoordinateIdx (𝕜 := Real) E) :=
    covariantDerivative_coordFrame_coeff (I := I) cov x₀ Vkj i m hVkj
      hcoeff_kj
  have hcov_k (m : CoordinateIdx (𝕜 := Real) E) :=
    covariantDerivative_coordFrame_coeff (I := I) cov x₀ Vij k m hVij
      hcoeff_ij
  have hbracket :
      (cov (frame j) x₀) (VectorField.mlieBracket I (frame i) (frame k) x₀) = 0 := by
    rw [coordinateFrameAt_bracket_zero (I := I) x₀ i k]
    simp
  calc
    (connectionRiemannCurvatureField (I := I) cov (frame i) (frame k) (frame j)) x₀
        = (cov Vkj x₀) (frame i x₀) - (cov Vij x₀) (frame k x₀) := by
          simp [connectionRiemannCurvatureField,
            DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField, Vkj, Vij, frame, hbracket]
    _ = ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ i k j m • frame m x₀ := by
          have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
            coordinateFrameAt_mem (I := I) x₀
          rw [show
            (cov Vkj x₀) (frame i x₀) - (cov Vij x₀) (frame k x₀) =
              ∑ m : CoordinateIdx (𝕜 := Real) E,
                hframe.coeff m x₀
                  ((cov Vkj x₀) (frame i x₀) - (cov Vij x₀) (frame k x₀)) •
                  frame m x₀ by
            simpa [frame, hframe] using
              (hframe.coeff_sum_eq
                (fun _ : M => (cov Vkj x₀) (frame i x₀) -
                  (cov Vij x₀) (frame k x₀)) hx₀)]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [map_sub]
          rw [hcov_i m, hcov_k m]
          unfold christoffelCurvCoeffAt
          unfold christoffelCoordDerivAt
          unfold christoffelCoordFun
          unfold christoffelSymbolInFrame
          congr 1
          have hVkj_coeff (a : CoordinateIdx (𝕜 := Real) E) :
              hframe.coeff a x₀ (Vkj x₀) =
                christoffelCoordAt (I := I) cov x₀ k j a := by
            simp [Vkj, christoffelCoordAt, frame]

          have hVij_coeff (a : CoordinateIdx (𝕜 := Real) E) :
              hframe.coeff a x₀ (Vij x₀) =
                christoffelCoordAt (I := I) cov x₀ i j a := by
            simp [Vij, christoffelCoordAt, frame]

          simp_rw [hVkj_coeff, hVij_coeff]
          simp
          ring

omit [FiniteDimensional ℝ E] in
private theorem smoothSections_cov_apply_mdiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (X Y : SmoothTangentSection (I := I) (M := M)) (x : M) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  exact (CovariantDerivative.smoothSections_cov_contMDiffAt_one
    (𝕜 := Real) (I := I) cov hcov X Y x).mdifferentiableAt
      (by norm_num)

private theorem connectionRiemannCurvatureField_eq_smooth_of_coordFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    {x₀ : M} (i k j : CoordinateIdx (𝕜 := Real) E)
    (Xs Ys Zs : SmoothTangentSection (I := I) (M := M))
    (hX : (fun p : M => Xs p) =ᶠ[nhds x₀] coordinateFrameAt (I := I) x₀ i)
    (hY : (fun p : M => Ys p) =ᶠ[nhds x₀] coordinateFrameAt (I := I) x₀ k)
    (hZ : (fun p : M => Zs p) =ᶠ[nhds x₀] coordinateFrameAt (I := I) x₀ j) :
    connectionRiemannCurvatureField (I := I) cov
        (coordinateFrameAt (I := I) x₀ i)
        (coordinateFrameAt (I := I) x₀ k)
        (coordinateFrameAt (I := I) x₀ j) x₀ =
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x₀ := by
  classical
  let Xc : (p : M) -> TangentSpace I p := coordinateFrameAt (I := I) x₀ i
  let Yc : (p : M) -> TangentSpace I p := coordinateFrameAt (I := I) x₀ k
  let Zc : (p : M) -> TangentSpace I p := coordinateFrameAt (I := I) x₀ j
  have hX' : Xc =ᶠ[nhds x₀] fun p : M => Xs p := by
    simpa [Xc] using hX.symm
  have hY' : Yc =ᶠ[nhds x₀] fun p : M => Ys p := by
    simpa [Yc] using hY.symm
  have hZ' : Zc =ᶠ[nhds x₀] fun p : M => Zs p := by
    simpa [Zc] using hZ.symm
  have hXx : Xc x₀ = Xs x₀ := hX'.self_of_nhds
  have hYx : Yc x₀ = Ys x₀ := hY'.self_of_nhds
  have hbr :
      VectorField.mlieBracket I Xc Yc x₀ =
        VectorField.mlieBracket I (fun p : M => Xs p) (fun p : M => Ys p) x₀ := by
    exact hX'.mlieBracket_vectorField_eq (I := I) hY'
  have hZ_at :
      cov Zc x₀ = cov (fun p : M => Zs p) x₀ := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by simpa [Zc] using coordinateFrameAt_mdifferentiableAt (I := I) x₀ j)
      (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (by simp) hZ'
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hinnerY :
      (fun p : M => (cov Zc p) (Yc p)) =ᶠ[nhds x₀]
        (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ nhds x₀) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hY',
      (coordinateFrameSet_open (I := I) x₀).mem_nhds hx₀] with p hpU hYp hpFrame
    have hZp : Zc =ᶠ[nhds p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hpFrame j).mdifferentiableAt (by simp)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hYp]
  have hinnerX :
      (fun p : M => (cov Zc p) (Xc p)) =ᶠ[nhds x₀]
        (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) := by
    rcases mem_nhds_iff.mp (hZ' : {p : M | Zc p = Zs p} ∈ nhds x₀) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hX',
      (coordinateFrameSet_open (I := I) x₀).mem_nhds hx₀] with p hpU hXp hpFrame
    have hZp : Zc =ᶠ[nhds p] fun q : M => Zs q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hZc_md : MDiffAt (T% Zc) p := by
      exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hpFrame j).mdifferentiableAt (by simp)
    have hcovp :
        cov Zc p = cov (fun q : M => Zs q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        hZc_md (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hXp]
  have hcovZY :
      cov (fun p : M => (cov Zc p) (Yc p)) x₀ =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Ys p)) x₀ := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Yc] using
          coordinateFrame_covariantDeriv_mdiffAt_one (I := I) cov hcov x₀ k j)
      (smoothSections_cov_apply_mdiffAt (I := I) cov hcov Ys Zs x₀)
      (by simp) hinnerY
  have hcovZX :
      cov (fun p : M => (cov Zc p) (Xc p)) x₀ =
        cov (fun p : M => (cov (fun q : M => Zs q) p) (Xs p)) x₀ := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (by
        simpa [Zc, Xc] using
          coordinateFrame_covariantDeriv_mdiffAt_one (I := I) cov hcov x₀ i j)
      (smoothSections_cov_apply_mdiffAt (I := I) cov hcov Xs Zs x₀)
      (by simp) hinnerX
  have hXval : coordinateFrameAt (I := I) x₀ i x₀ = Xs x₀ := by
    simpa [Xc] using hXx
  have hYval : coordinateFrameAt (I := I) x₀ k x₀ = Ys x₀ := by
    simpa [Yc] using hYx
  simp only [connectionRiemannCurvatureField, DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
  rw [hcovZY, hcovZX, hZ_at, hbr]
  rw [hXval, hYval]




theorem rm13_eval_eq_christoffelCurvCoord
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (i k j : CoordinateIdx (𝕜 := Real) E) :
    Rm13 x₀ alpha
        (vec3 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ k x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
      ∑ m : CoordinateIdx (𝕜 := Real) E,
        christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
          alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀) := by
  classical
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame (I := I) x₀
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd
    (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀)
  let Xs : SmoothTangentSection (I := I) (M := M) := s' i
  let Ys : SmoothTangentSection (I := I) (M := M) := s' k
  let Zs : SmoothTangentSection (I := I) (M := M) := s' j
  have hXnear : (fun p : M => Xs p) =ᶠ[nhds x₀] frame i := by
    filter_upwards [hs'] with p hp
    exact hp i
  have hYnear : (fun p : M => Ys p) =ᶠ[nhds x₀] frame k := by
    filter_upwards [hs'] with p hp
    exact hp k
  have hZnear : (fun p : M => Zs p) =ᶠ[nhds x₀] frame j := by
    filter_upwards [hs'] with p hp
    exact hp j
  have hXx : Xs x₀ = frame i x₀ := hXnear.self_of_nhds
  have hYx : Ys x₀ = frame k x₀ := hYnear.self_of_nhds
  have hZx : Zs x₀ = frame j x₀ := hZnear.self_of_nhds
  have hcurv_smooth :
      connectionRiemannCurvatureField (I := I) cov
          (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p) x₀ =
        connectionRiemannCurvatureField (I := I) cov
          (frame i) (frame k) (frame j) x₀ := by
    exact (connectionRiemannCurvatureField_eq_smooth_of_coordFrame
      (I := I) cov hcov i k j Xs Ys Zs hXnear hYnear hZnear).symm
  have hRm_eval := hRm Xs Ys Zs x₀ alpha
  have hcurv_raw := hcurv i k j
  calc
    Rm13 x₀ alpha (vec3 (frame i x₀) (frame k x₀) (frame j x₀))
        = Rm13 x₀ alpha (vec3 (Xs x₀) (Ys x₀) (Zs x₀)) := by
          simp [hXx, hYx, hZx]
    _ = cotangentToDual_gen (I := I) alpha
        ((connectionRiemannCurvatureField (I := I) cov
          (fun p : M => Xs p) (fun p : M => Ys p) (fun p : M => Zs p)) x₀) := hRm_eval
    _ = cotangentToDual_gen (I := I) alpha
        ((connectionRiemannCurvatureField (I := I) cov
          (frame i) (frame k) (frame j)) x₀) := by
          rw [hcurv_smooth]
    _ = ∑ m : CoordinateIdx (𝕜 := Real) E,
        christoffelCurvCoeffAt (I := I) cov x₀ i k j m *
          alpha (fun _ : Fin 1 => frame m x₀) := by
          rw [hcurv_raw]
          simp [cotangentToDual_apply_gen, map_sum, frame]







theorem rm13_coord_expand
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x₀)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (X Y Z : TangentSpace I x₀) :
    Rm13 x₀ alpha (vec3 X Y Z) =
      ∑ r : Fin 3 -> CoordinateIdx (𝕜 := Real) E,
        (∏ q : Fin 3,
          (coordinateFrameAt_toBasis (I := I) x₀).repr
            (vec3 X Y Z q) (r q)) *
          (∑ m : CoordinateIdx (𝕜 := Real) E,
            christoffelCurvCoeffAt (I := I) cov x₀ (r 0) (r 1) (r 2) m *
              alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀)) := by
  classical
  let basis := coordinateFrameAt_toBasis (I := I) x₀
  let slot : Fin 3 -> TangentSpace I x₀ := vec3 X Y Z
  let g : (q : Fin 3) -> CoordinateIdx (𝕜 := Real) E -> TangentSpace I x₀ :=
    fun q i => basis.repr (slot q) i • basis i
  have hslot : (fun q : Fin 3 => ∑ i : CoordinateIdx (𝕜 := Real) E, g q i) = slot := by
    funext q
    simp [g]
  calc
    Rm13 x₀ alpha (vec3 X Y Z) =
        Rm13 x₀ alpha (fun q : Fin 3 => ∑ i : CoordinateIdx (𝕜 := Real) E, g q i) := by
          rw [hslot]
    _ = ∑ r : Fin 3 -> CoordinateIdx (𝕜 := Real) E,
        Rm13 x₀ alpha (fun q : Fin 3 => g q (r q)) := by
          rw [Tensor0SSpace.map_sum (Rm13 x₀ alpha) g]
    _ =
      ∑ r : Fin 3 -> CoordinateIdx (𝕜 := Real) E,
        (∏ q : Fin 3,
          (coordinateFrameAt_toBasis (I := I) x₀).repr
            (vec3 X Y Z q) (r q)) *
          (∑ m : CoordinateIdx (𝕜 := Real) E,
            christoffelCurvCoeffAt (I := I) cov x₀ (r 0) (r 1) (r 2) m *
              alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          have hsmul :
              Rm13 x₀ alpha (fun q : Fin 3 => g q (r q)) =
                (∏ q : Fin 3, basis.repr (slot q) (r q)) *
                  Rm13 x₀ alpha (fun q : Fin 3 => basis (r q)) := by
            rw [(Rm13 x₀ alpha).map_smul_univ]
            simp [smul_eq_mul]
          have hbasisSlots :
              (fun q : Fin 3 => basis (r q)) =
                vec3 (basis (r 0)) (basis (r 1)) (basis (r 2)) := by
            funext q
            fin_cases q <;> simp [DifferentialGeometry.Integral.Connection.vec3]
          have hbasisEval :
              Rm13 x₀ alpha (fun q : Fin 3 => basis (r q)) =
                ∑ m : CoordinateIdx (𝕜 := Real) E,
                  christoffelCurvCoeffAt (I := I) cov x₀ (r 0) (r 1) (r 2) m *
                    alpha (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ m x₀) := by
            rw [hbasisSlots]
            simpa [basis, coordinateFrameAt_toBasis_apply] using
              rm13_eval_eq_christoffelCurvCoord
                (I := I) cov hcov Rm13 x₀ alpha hRm hcurv (r 0) (r 1) (r 2)
          rw [hsmul, hbasisEval]



theorem ricciFromRm13At_coordFrame_eq_christoffelRicciCoeffAt
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x₀ : M)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ricciFromRm13At (I := I) (M := M) (Rm13 x₀)
        (vec2 (coordinateFrameAt (I := I) x₀ i x₀)
          (coordinateFrameAt (I := I) x₀ j x₀)) =
      christoffelRicciCoeffAt (I := I) cov x₀ i j := by
  classical
  let basis := coordinateFrameAt_toBasis (I := I) x₀
  rw [show coordinateFrameAt (I := I) x₀ i x₀ = basis i by
    simp [basis, coordinateFrameAt_toBasis_apply]]
  rw [show coordinateFrameAt (I := I) x₀ j x₀ = basis j by
    simp [basis, coordinateFrameAt_toBasis_apply]]
  rw [ricciFromRm13At_apply_basis_trace (I := I) basis (Rm13 x₀) (basis i) (basis j)]
  unfold christoffelRicciCoeffAt
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := rm13_eval_eq_christoffelCurvCoord (I := I) cov hcov Rm13 x₀
    (dualToCotangent_gen (I := I) (basis.coord a)) hRm hcurv a i j
  have hcoord (m : CoordinateIdx (𝕜 := Real) E) :
      ((coordinateFrameAt_toBasis (I := I) x₀).repr
          (coordinateFrameAt (I := I) x₀ m x₀)) a =
        if m = a then 1 else 0 := by
    rw [show coordinateFrameAt (I := I) x₀ m x₀ =
        (coordinateFrameAt_toBasis (I := I) x₀) m by
      simp [coordinateFrameAt_toBasis_apply]]
    by_cases hma : m = a
    · rw [hma]
      have hb := congrArg (fun f => f a)
        (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) a)
      simpa [coordinateFrameAt_toBasis_apply] using hb
    · have hb := congrArg (fun f => f a)
        (Module.Basis.repr_self (coordinateFrameAt_toBasis (I := I) x₀) m)
      simpa [coordinateFrameAt_toBasis_apply, Finsupp.single_apply, hma] using hb
  have hsum :
      (∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ a i j m *
            ((coordinateFrameAt_toBasis (I := I) x₀).repr
              (coordinateFrameAt (I := I) x₀ m x₀)) a) =
        christoffelCurvCoeffAt (I := I) cov x₀ a i j a := by
    rw [show
        (∑ m : CoordinateIdx (𝕜 := Real) E,
            christoffelCurvCoeffAt (I := I) cov x₀ a i j m *
              ((coordinateFrameAt_toBasis (I := I) x₀).repr
                (coordinateFrameAt (I := I) x₀ m x₀)) a) =
          ∑ m : CoordinateIdx (𝕜 := Real) E,
            (if m = a then christoffelCurvCoeffAt (I := I) cov x₀ a i j a
              else 0) by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hcoord m]
      by_cases hma : m = a
      · subst hma
        simp
      · simp [hma]]
    simp
  have h' :
      ((Rm13 x₀) (dualToCotangent_gen (I := I) (basis.coord a)))
          (vec3 (basis a) (basis i) (basis j)) =
        ∑ m : CoordinateIdx (𝕜 := Real) E,
          christoffelCurvCoeffAt (I := I) cov x₀ a i j m *
            ((coordinateFrameAt_toBasis (I := I) x₀).repr
              (coordinateFrameAt (I := I) x₀ m x₀)) a := by
    simpa [basis, coordinateFrameAt_toBasis_apply, dualToCotangent_apply_gen] using h
  rw [h']
  exact hsum

end CoordinateChristoffelCurvature
end DifferentialGeometry.Integral.Connection
