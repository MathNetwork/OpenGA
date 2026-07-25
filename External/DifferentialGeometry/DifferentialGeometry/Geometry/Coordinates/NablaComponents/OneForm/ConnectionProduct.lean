import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Pairing







set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]


omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem oneForm_covariantDerivative_coordFrame_product_rule
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) (z dz : CoordinateIdx (𝕜 := 𝕜) E -> 𝕜)
    (hz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      z j = (coordinateFrameAt_toBasis (I := I) x₀).coord j (Z x₀))
    (hdz : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      dz j =
        extDerivFun (I := I)
          (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y))
          x₀ (X x₀))
    (hdiff_z : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M =>
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y)) x₀)
    (hZ_diff : MDiffAt (T% Z) x₀) :
    α x₀ (fun _ : Fin 1 => (cov (fun y : M => Z y) x₀) (X x₀)) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
          z j *
            (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k))) := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  let zfun : CoordinateIdx (𝕜 := 𝕜) E -> M -> 𝕜 :=
    fun j y => hframe.coeff j y (Z y)
  let term : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x :=
    fun j => zfun j • frame j
  have hframe_diff (j : CoordinateIdx (𝕜 := 𝕜) E) : MDiffAt (T% (frame j)) x₀ :=
    (hframe.contMDiffAt (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j).mdifferentiableAt one_ne_zero
  have hterm_diff : ∀ j ∈ (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)),
      MDiffAt (T% (term j)) x₀ := by
    intro j _
    exact (hdiff_z j).smul_section (hframe_diff j)
  have hsum_diff :
      MDiffAt (T% ((Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)).sum term)) x₀ := by
    classical
    exact (by
      have hterm_all : ∀ j : CoordinateIdx (𝕜 := 𝕜) E, MDiffAt (T% (term j)) x₀ := by
        intro j
        exact hterm_diff j (by simp)
      simpa using MDifferentiableAt.sum_section
        (s := (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E))) (t := term) hterm_all)
  have hZ_ev : (fun y : M => Z y) =ᶠ[𝓝 x₀]
      (fun y : M => ∑ j : CoordinateIdx (𝕜 := 𝕜) E, term j y) := by
    exact hframe.eventually_eq_sum_coeff_smul (fun y => Z y)
      ((coordinateFrameSet_open (I := I) x₀).mem_nhds
        (coordinateFrameAt_mem (I := I) x₀))
  have hcov_congr :
      cov (fun y : M => Z y) x₀ =
        cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)).sum term) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZ_diff hsum_diff
      (by simp)
      (by simpa [term] using hZ_ev)
  have hcov_sum :
      (cov (fun y : M => Z y) x₀) (X x₀) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
    calc
      (cov (fun y : M => Z y) x₀) (X x₀)
          = (cov ((Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)).sum term) x₀) (X x₀) := by
            rw [hcov_congr]
      _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E, (cov (term j) x₀) (X x₀) := by
            rw [oneForm_covariantDerivative_finset_sum (I := I) cov
              (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) term (X x₀) (by
                intro j
                exact hterm_diff j (by simp))]
      _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
            (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame j) (g := zfun j) (x := x₀)
              (hframe_diff j) (hdiff_z j)) (X x₀))
            have hzj : zfun j x₀ = z j := by
              rw [hz j]
              exact oneForm_coordinateFrame_coeff_at_base_eq_coord (I := I) x₀ (Z x₀) j
            have hdzj : extDerivFun (I := I) (zfun j) x₀ (X x₀) = dz j := by
              exact (hdz j).symm
            simpa [term, zfun, hzj, hdzj, add_comm] using hleib
  rw [hcov_sum]
  rw [tensor0S_one_eval_finset_sum (I := I)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcov_frame :
      (cov (frame j) x₀) (X x₀) =
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀ := by
    exact hframe.coeff_sum_eq
      (fun y => (cov (frame j) y) (X y))
      (coordinateFrameAt_mem (I := I) x₀)
  have h_eval_cov :
      α x₀ (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀)) =
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
    rw [hcov_frame]
    rw [tensor0S_one_eval_finset_sum (I := I)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hupdate :
        (fun _ : Fin 1 =>
            christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀) =
          Function.update (fun _ : Fin 1 => frame k x₀) (0 : Fin 1)
            (christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k • frame k x₀) := by
      funext q
      fin_cases q
      simp
    rw [hupdate, (α x₀).map_update_smul]
    have hframe_eval :
        α x₀ (fun _ : Fin 1 => frame k x₀) =
          coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k) := by
      simp [frame, coordComponent0SAt, component0S]
    have hupdate0 :
        Function.update (fun _ : Fin 1 => frame k x₀) (0 : Fin 1) (frame k x₀) =
          fun _ : Fin 1 => frame k x₀ := by
      funext q
      fin_cases q
      simp
    rw [hupdate0, hframe_eval]
    simp [smul_eq_mul]
  have h_eval_frame :
      α x₀ (fun _ : Fin 1 => frame j x₀) =
        coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) := by
    simp [frame, coordComponent0SAt, component0S]
  change α x₀ (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) =
      dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
        z j *
          (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
            christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
              coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k))
  have hconst_add :
      (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) =
        Function.update
          (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
          (0 : Fin 1)
          (dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀)) := by
    funext q
    fin_cases q
    simp
  rw [hconst_add]
  rw [(α x₀).map_update_add]
  have h_up1 :
      Function.update
        (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
        (0 : Fin 1) (dz j • frame j x₀) =
        fun _ : Fin 1 => dz j • frame j x₀ := by
    funext q
    fin_cases q
    simp
  have h_up2 :
      Function.update
        (fun _ : Fin 1 => dz j • frame j x₀ + z j • (cov (frame j) x₀) (X x₀))
        (0 : Fin 1) (z j • (cov (frame j) x₀) (X x₀)) =
        fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀) := by
    funext q
    fin_cases q
    simp
  rw [h_up1, h_up2]
  rw [show α x₀ (fun _ : Fin 1 => dz j • frame j x₀) =
      dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) by
    have hupdate :
        (fun _ : Fin 1 => dz j • frame j x₀) =
          Function.update (fun _ : Fin 1 => frame j x₀) (0 : Fin 1)
            (dz j • frame j x₀) := by
      funext q
      fin_cases q
      simp
    rw [hupdate, (α x₀).map_update_smul]
    simp [h_eval_frame, smul_eq_mul]]
  rw [show α x₀ (fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀)) =
      z j * (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov frame hframe x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => k)) by
    have hupdate :
        (fun _ : Fin 1 => z j • (cov (frame j) x₀) (X x₀)) =
          Function.update
            (fun _ : Fin 1 => (cov (frame j) x₀) (X x₀))
            (0 : Fin 1)
            (z j • (cov (frame j) x₀) (X x₀)) := by
      funext q
      fin_cases q
      simp
    rw [hupdate, (α x₀).map_update_smul]
    simp [h_eval_cov, smul_eq_mul]]

end DifferentialGeometry.Tensor.Coordinates
