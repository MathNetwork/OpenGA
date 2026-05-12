import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Gradient

/-!
# Tensoriality of the Riemann curvature tensor — Z-slot Leibniz

`R(X, Y)(f · Z)(x) = f(x) · R(X, Y) Z(x)` for smooth scalar `f` and smooth
vector fields `X, Y, Z`. The cross-derivative residual cancels by the
manifold scalar Hessian-Lie identity.

This is the cornerstone of full 3-slot tensoriality (used by the
heart-of-Bochner outer assembly). -/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle VectorField
open scoped ContDiff Manifold Bundle Riemannian Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Smoothness of `y ↦ mfderiv f y (V y)` as a scalar function** for
smooth scalar `f` and smooth tangent section `V`. The directional
derivative `V(f)` is C∞.

OpenGALib analog of external `extDerivFun_apply_contMDiff`. Proof routes
through the manifold-gradient duality `mfderiv f y v = ⟨∇^M f, v⟩_g`,
which is `metricInner ∘ manifoldGradient ∘ ·`, smooth as a composition. -/
theorem mfderiv_apply_smoothVF_contMDiff
    (f : M → ℝ) (V : SmoothVectorField I M)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (V.toFun y))) := by
  -- Identify with `y ↦ metricInner y (manifoldGradient f y) (V y)` via grad duality.
  -- Then smoothness follows from manifoldGradient smoothness + V smoothness +
  -- bilinearity of the metric (encoded in `HasMetric` smoothness).
  have h_eq : (fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (V.toFun y)))
      = (fun y => metricInner y (manifoldGradient (I := I) f y) (V.toFun y)) := by
    funext y
    exact (manifoldGradient_inner_eq (I := I) f y (V.toFun y)).symm
  rw [h_eq]
  exact fun y => hm.metric.metricInner_contMDiffAt
    (n := ∞) (manifoldGradient_smooth_of_smooth (I := I) f hf y) (V.smooth y)

/-- **3rd-slot (Z-slot) C∞-linearity of `riemannCurvature`**:
$$R(X, Y)(f \cdot Z)(x) = f(x) \cdot R(X, Y)\,Z(x).$$

External reference: `riemannSec_smul_third` in
`differential-geometry/.../Curvature.lean:521`. -/
theorem riemannCurvature_smul_third_scalar_field
    [IsManifold I 2 M]
    (f : M → ℝ) (X Y Z : SmoothVectorField I M) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    riemannCurvature X.toFun Y.toFun (f • Z.toFun) x
      = f x • riemannCurvature X.toFun Y.toFun Z.toFun x := by
  classical
  have hf_at : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    fun y => (hf y).mdifferentiableAt (by simp)
  have hf_C2_at : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
    (hf x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hX1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) x :=
    (X.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hY1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) x :=
    (Y.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  -- Directional-derivative scalar functions.
  set Yf : M → ℝ :=
    fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (Y.toFun y)) with hYf_def
  set Xf : M → ℝ :=
    fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (X.toFun y)) with hXf_def
  -- Smoothness of Yf, Xf as C∞ scalar functions.
  have hYf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Yf :=
    mfderiv_apply_smoothVF_contMDiff (I := I) f Y hf
  have hXf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Xf :=
    mfderiv_apply_smoothVF_contMDiff (I := I) f X hf
  have hYf_at : MDifferentiableAt I 𝓘(ℝ, ℝ) Yf x :=
    (hYf_smooth x).mdifferentiableAt (by simp)
  have hXf_at : MDifferentiableAt I 𝓘(ℝ, ℝ) Xf x :=
    (hXf_smooth x).mdifferentiableAt (by simp)
  -- ∇_V (f Z) section identity at every y (V ∈ {X, Y}).
  -- We state as Π-pointwise functions (not lambda-form) to match `covDeriv` shape.
  have h_inner_Y :
      covDeriv Y.toFun (f • Z.toFun)
        = (fun y : M => f y • covDeriv Y.toFun Z.toFun y + Yf y • Z.toFun y) := by
    funext y
    exact covDeriv_smul_scalar_field Y.toFun f Z.toFun y (hf_at y) (Z.smoothAt y)
  have h_inner_X :
      covDeriv X.toFun (f • Z.toFun)
        = (fun y : M => f y • covDeriv X.toFun Z.toFun y + Xf y • Z.toFun y) := by
    funext y
    exact covDeriv_smul_scalar_field X.toFun f Z.toFun y (hf_at y) (Z.smoothAt y)
  -- Riemann curvature unfold via def.
  rw [riemannCurvature_def, riemannCurvature_def, h_inner_Y, h_inner_X]
  -- Pointwise sums need to be split into Π-add form for `covDeriv_add_field`.
  -- The two summands as separate Π-sections.
  set g1Y : Π y : M, TangentSpace I y :=
    fun y => f y • covDeriv Y.toFun Z.toFun y with hg1Y_def
  set g2Y : Π y : M, TangentSpace I y :=
    fun y => Yf y • Z.toFun y with hg2Y_def
  set g1X : Π y : M, TangentSpace I y :=
    fun y => f y • covDeriv X.toFun Z.toFun y with hg1X_def
  set g2X : Π y : M, TangentSpace I y :=
    fun y => Xf y • Z.toFun y with hg2X_def
  -- Convert `fun y => g1Y y + g2Y y` to Π-add `g1Y + g2Y` definitionally.
  have h_pi_addY : (fun y : M => g1Y y + g2Y y) = g1Y + g2Y := rfl
  have h_pi_addX : (fun y : M => g1X y + g2X y) = g1X + g2X := rfl
  rw [h_pi_addY, h_pi_addX]
  -- Smoothness witnesses for the summands at x.
  have h_dY_Z_smooth : TangentSmoothAt (fun y => covDeriv Y.toFun Z.toFun y) x :=
    covDeriv_smoothVF_smoothAt Y Z x
  have h_dX_Z_smooth : TangentSmoothAt (fun y => covDeriv X.toFun Z.toFun y) x :=
    covDeriv_smoothVF_smoothAt X Z x
  have hg1Y_smooth : TangentSmoothAt g1Y x :=
    (hf_at x).smul_section h_dY_Z_smooth
  have hg2Y_smooth : TangentSmoothAt g2Y x :=
    hYf_at.smul_section (Z.smoothAt x)
  have hg1X_smooth : TangentSmoothAt g1X x :=
    (hf_at x).smul_section h_dX_Z_smooth
  have hg2X_smooth : TangentSmoothAt g2X x :=
    hXf_at.smul_section (Z.smoothAt x)
  -- Apply outer additivity (covDeriv_add_field).
  rw [covDeriv_add_field X.toFun g1Y g2Y x hg1Y_smooth hg2Y_smooth,
      covDeriv_add_field Y.toFun g1X g2X x hg1X_smooth hg2X_smooth]
  -- Apply Leibniz to each summand at x.
  -- g1Y = f • (∇_Y Z), g2Y = Yf • Z, g1X = f • (∇_X Z), g2X = Xf • Z.
  -- ∇_X (f • ∇_Y Z) x = f x • ∇_X (∇_Y Z) x + (Xf x) • (∇_Y Z) x.
  have hT1_g1Y : covDeriv X.toFun g1Y x
      = f x • covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (X.toFun x))
            • covDeriv Y.toFun Z.toFun x :=
    covDeriv_smul_scalar_field X.toFun f
      (fun y => covDeriv Y.toFun Z.toFun y) x (hf_at x) h_dY_Z_smooth
  have hT1_g2Y : covDeriv X.toFun g2Y x
      = Yf x • covDeriv X.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x)) • Z.toFun x :=
    covDeriv_smul_scalar_field X.toFun Yf Z.toFun x hYf_at (Z.smoothAt x)
  have hT2_g1X : covDeriv Y.toFun g1X x
      = f x • covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (Y.toFun x))
            • covDeriv X.toFun Z.toFun x :=
    covDeriv_smul_scalar_field Y.toFun f
      (fun y => covDeriv X.toFun Z.toFun y) x (hf_at x) h_dX_Z_smooth
  have hT2_g2X : covDeriv Y.toFun g2X x
      = Xf x • covDeriv Y.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x)) • Z.toFun x :=
    covDeriv_smul_scalar_field Y.toFun Xf Z.toFun x hXf_at (Z.smoothAt x)
  -- Third term: ∇_{[X,Y]} (f Z) x = f x • ∇_{[X,Y]} Z x + (mfderiv f x ([X,Y] x)) • Z x.
  have hT3 : covDeriv (mlieBracket I X.toFun Y.toFun) (f • Z.toFun) x
      = f x • covDeriv (mlieBracket I X.toFun Y.toFun) Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x
            (mlieBracket I X.toFun Y.toFun x)) • Z.toFun x :=
    covDeriv_smul_scalar_field (mlieBracket I X.toFun Y.toFun) f Z.toFun x
      (hf_at x) (Z.smoothAt x)
  rw [hT1_g1Y, hT1_g2Y, hT2_g1X, hT2_g2X, hT3]
  -- Apply Hessian-Lie identity: X(Yf) x - Y(Xf) x = mfderiv f x ([X,Y] x).
  have h_HL : (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x))
              - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x))
            = (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x
                (mlieBracket I X.toFun Y.toFun x)) :=
    mfderiv_iterate_sub_eq_mlieBracket_apply
      f X.toFun Y.toFun x h_interior hf_C2_at hX1 hY1
  -- Rewrite the `mfderiv f x ([X,Y] x) • Z x` term using h_HL to make
  -- the `(Yf' x - Xf' x) • Z x` cancellation explicit.
  rw [← h_HL, sub_smul]
  -- Identify `Xf x = mfderiv f x (X x)` and `Yf x = mfderiv f x (Y x)` definitionally
  -- (both sides reduce by `set ... with` unfolding).
  show f x • covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x
      + Xf x • covDeriv Y.toFun Z.toFun x
      + (Yf x • covDeriv X.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x)) • Z.toFun x)
    - (f x • covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x
      + Yf x • covDeriv X.toFun Z.toFun x
      + (Xf x • covDeriv Y.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x)) • Z.toFun x))
    - (f x • covDeriv (mlieBracket I X.toFun Y.toFun) Z.toFun x
      + ((show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x)) • Z.toFun x
        - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x)) • Z.toFun x))
    = f x • (covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x
        - covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x
        - covDeriv (mlieBracket I X.toFun Y.toFun) Z.toFun x)
  -- Pure AddCommGroup arithmetic — cross-cancellation + f x • distributes.
  rw [smul_sub, smul_sub]
  abel

/-! ## Z-slot locality

`riemannCurvature` is local in the Z-slot: if `Z =ᶠ[𝓝 x] Z'`, then
`R(X, Y) Z(x) = R(X, Y) Z'(x)`. Each of the three terms in `riemannCurvature_def`
satisfies a covariant-derivative locality identity in `Z`:

* `covDeriv X (covDeriv Y Z) x` and `covDeriv Y (covDeriv X Z) x` use the
  fact that the inner section `covDeriv U Z` is locally constant in `Z`
  (apply `covDeriv_congr_eventuallyEq_field` at every nearby `b`), then
  evaluate the outer `covDeriv` via the same field-locality lemma.
* `covDeriv [X, Y] Z x` reduces directly. -/

/-- **Z-slot locality of `riemannCurvature`**: if `Z =ᶠ[𝓝 x] Z'`, then
`R(X, Y) Z(x) = R(X, Y) Z'(x)`. External reference: `riemannSec_eq_of_Z_eventuallyEq`
(`differential-geometry/.../CurvatureBundling.lean:227`). -/
theorem riemannCurvature_eq_of_Z_eventuallyEq
    (X Y Z Z' : SmoothVectorField I M) (x : M)
    (hZZ' : ∀ᶠ y in 𝓝 x, Z.toFun y = Z'.toFun y) :
    riemannCurvature X.toFun Y.toFun Z.toFun x
      = riemannCurvature X.toFun Y.toFun Z'.toFun x := by
  classical
  -- Convert eventual equality to an open nbhd `V'` on which `Z = Z'`.
  rw [Filter.eventually_iff_exists_mem] at hZZ'
  obtain ⟨U, hU, hZeqZ'⟩ := hZZ'
  obtain ⟨V', hV'U, hV'_open, hpV'⟩ := mem_nhds_iff.mp hU
  -- `Z =ᶠ[𝓝 b] Z'` for any `b ∈ V'` (V' open, V' ⊆ U).
  have hZZ'_at : ∀ b ∈ V', ∀ᶠ b' in 𝓝 b, Z.toFun b' = Z'.toFun b' := by
    intro b hbV'
    exact Filter.eventually_of_mem (hV'_open.mem_nhds hbV')
      (fun b' hb'V' => hZeqZ' b' (hV'U hb'V'))
  -- Inner section pointwise equality on `V'` (Y- and X-flavored).
  have h_inner_Y_pt : ∀ b ∈ V',
      (fun y => covDeriv Y.toFun Z.toFun y) b
        = (fun y => covDeriv Y.toFun Z'.toFun y) b := by
    intro b hbV'
    exact covDeriv_congr_eventuallyEq_field Y.toFun Z.toFun Z'.toFun b
      (Z.smoothAt b) (Z'.smoothAt b) (hZZ'_at b hbV')
  have h_inner_X_pt : ∀ b ∈ V',
      (fun y => covDeriv X.toFun Z.toFun y) b
        = (fun y => covDeriv X.toFun Z'.toFun y) b := by
    intro b hbV'
    exact covDeriv_congr_eventuallyEq_field X.toFun Z.toFun Z'.toFun b
      (Z.smoothAt b) (Z'.smoothAt b) (hZZ'_at b hbV')
  -- Lift to eventual equality on a nbhd of `x`.
  have h_inner_Y_ev : ∀ᶠ b in 𝓝 x,
      (fun y => covDeriv Y.toFun Z.toFun y) b
        = (fun y => covDeriv Y.toFun Z'.toFun y) b :=
    Filter.eventually_of_mem (hV'_open.mem_nhds hpV') h_inner_Y_pt
  have h_inner_X_ev : ∀ᶠ b in 𝓝 x,
      (fun y => covDeriv X.toFun Z.toFun y) b
        = (fun y => covDeriv X.toFun Z'.toFun y) b :=
    Filter.eventually_of_mem (hV'_open.mem_nhds hpV') h_inner_X_pt
  -- T1: outer `covDeriv X ·` field-locality, with `covDeriv_smoothVF_smoothAt`
  -- discharging the inner-section smoothness witnesses.
  have hT1 : covDeriv X.toFun (fun y => covDeriv Y.toFun Z.toFun y) x
      = covDeriv X.toFun (fun y => covDeriv Y.toFun Z'.toFun y) x :=
    covDeriv_congr_eventuallyEq_field X.toFun
      (fun y => covDeriv Y.toFun Z.toFun y)
      (fun y => covDeriv Y.toFun Z'.toFun y) x
      (covDeriv_smoothVF_smoothAt Y Z x)
      (covDeriv_smoothVF_smoothAt Y Z' x) h_inner_Y_ev
  -- T2: outer `covDeriv Y ·` field-locality.
  have hT2 : covDeriv Y.toFun (fun y => covDeriv X.toFun Z.toFun y) x
      = covDeriv Y.toFun (fun y => covDeriv X.toFun Z'.toFun y) x :=
    covDeriv_congr_eventuallyEq_field Y.toFun
      (fun y => covDeriv X.toFun Z.toFun y)
      (fun y => covDeriv X.toFun Z'.toFun y) x
      (covDeriv_smoothVF_smoothAt X Z x)
      (covDeriv_smoothVF_smoothAt X Z' x) h_inner_X_ev
  -- T3: `covDeriv [X, Y] Z x = covDeriv [X, Y] Z' x` direct.
  have hZZ'_x : ∀ᶠ y in 𝓝 x, Z.toFun y = Z'.toFun y :=
    Filter.eventually_of_mem (hV'_open.mem_nhds hpV')
      (fun b hbV' => hZeqZ' b (hV'U hbV'))
  have hT3 : covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x
      = covDeriv (VectorField.mlieBracket I X.toFun Y.toFun) Z'.toFun x :=
    covDeriv_congr_eventuallyEq_field
      (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun Z'.toFun x
      (Z.smoothAt x) (Z'.smoothAt x) hZZ'_x
  -- Combine via `riemannCurvature_def`.
  rw [riemannCurvature_def, riemannCurvature_def, hT1, hT2, hT3]

end Riemannian
