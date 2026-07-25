import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Basic







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
theorem oneForm_pair_coordFrame_eventually
    (Z : (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (x₀ : M) :
    (fun y : M => α y (fun _ : Fin 1 => Z y)) =ᶠ[𝓝 x₀]
      (fun y : M =>
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j y (Z y) *
            α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) := by
  classical
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with y hy
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hZ :
      Z y = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y := by
    exact hframe.coeff_sum_eq (fun y => Z y) hy
  have hupdate (w : TangentSpace I y) :
      Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have hmap := (α y).toMultilinearMap.map_update_sum
    (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) (0 : Fin 1)
    (fun j : CoordinateIdx (𝕜 := 𝕜) E =>
      hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)
    (fun _ : Fin 1 => Z y)
  calc
    α y (fun _ : Fin 1 => Z y)
        = α y (Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1)
            (∑ j : CoordinateIdx (𝕜 := 𝕜) E,
              hframe.coeff j y (Z y) • coordinateFrameAt (I := I) x₀ j y)) := by
          congr 1
          funext q
          fin_cases q
          exact hZ
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          hframe.coeff j y (Z y) *
            α y (Function.update (fun _ : Fin 1 => Z y) (0 : Fin 1)
              (coordinateFrameAt (I := I) x₀ j y)) := by
          simpa using hmap
    _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          hframe.coeff j y (Z y) *
            α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hupdate]







omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem oneForm_pair_coordFrame_product_rule
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
    (hdiff_α : ∀ j : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun y : M => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)) x₀) :
    extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
        (dz j * coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) +
          z j *
            coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
              (fun _ : Fin 1 => j)) := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let zfun : CoordinateIdx (𝕜 := 𝕜) E -> M -> 𝕜 :=
    fun j y => hframe.coeff j y (Z y)
  let afun : CoordinateIdx (𝕜 := 𝕜) E -> M -> 𝕜 :=
    fun j y => α y (fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j y)
  have hpair_ev := oneForm_pair_coordFrame_eventually (I := I) Z α x₀
  have hderiv_congr :
      extDerivFun (I := I) (fun y : M => α y (fun _ : Fin 1 => Z y)) x₀ (X x₀) =
        extDerivFun (I := I)
          (fun y : M => ∑ j : CoordinateIdx (𝕜 := 𝕜) E, zfun j y * afun j y) x₀ (X x₀) := by
    exact oneForm_extDerivFun_congr_eventually (I := I) (X x₀) (by
      simpa [zfun, afun] using hpair_ev)
  rw [hderiv_congr]
  have hsum_fun :
      (fun y : M => ∑ j : CoordinateIdx (𝕜 := 𝕜) E, zfun j y * afun j y) =
        Finset.univ.sum (fun j : CoordinateIdx (𝕜 := 𝕜) E =>
          fun y : M => zfun j y * afun j y) := by
    funext y
    simp
  rw [hsum_fun]
  rw [oneForm_extDerivFun_finset_sum (I := I) (t := Finset.univ)
    (f := fun j y => zfun j y * afun j y) (x := x₀) (v := X x₀)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [oneForm_extDerivFun_mul (I := I) (f := zfun j) (g := afun j) (x := x₀)
      (v := X x₀) (hdiff_z j) (hdiff_α j)]
    have hzj : zfun j x₀ = z j := by
      rw [hz j]
      exact oneForm_coordinateFrame_coeff_at_base_eq_coord (I := I) x₀ (Z x₀) j
    have hdzj : extDerivFun (I := I) (zfun j) x₀ (X x₀) = dz j := by
      exact (hdz j).symm
    have haj :
        afun j x₀ = coordComponent0SAt (I := I) (α x₀) (fun _ : Fin 1 => j) := by
      simp [afun, coordComponent0SAt, component0S]
    have hdaj :
        extDerivFun (I := I) (afun j) x₀ (X x₀) =
          coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
            (fun _ : Fin 1 => j) := by
      change (mfderiv I 𝓘(𝕜, 𝕜) (afun j) x₀) (X x₀) =
          coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x)
            (fun _ : Fin 1 => j)
      simp [afun, coordDeriv0SAt]
    rw [hzj, hdzj, haj, hdaj]
    ring
  · intro j _
    exact (hdiff_z j).mul (hdiff_α j)

end DifferentialGeometry.Tensor.Coordinates
