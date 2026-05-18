import OpenGALib.Riemannian.Curvature.RiemannCurvature

/-!
# Ricci tensor / Ricci endomorphism / scalar curvature bundles

Bilinear / linear-map packaging of the Ricci tensor at a point. The
mathematical content (Ricci as a bilinear form, Ricci endomorphism via
metric raising, scalar curvature as trace) is a thin wrapper around the
primitive `ricci` and `riemannCurvature` from `Curvature.lean`; the
engineering tax is the four `map_add'` / `map_smul'` proofs needed by
the Mathlib `LinearMap` structure.

* `ricciTensor g x : T_xM →ₗ[ℝ] T_xM →ₗ[ℝ] ℝ` — the Ricci tensor as a
  bilinear form, with bilinearity proved from `curvatureEndo`'s
  `LinearMap.trace` plus `riemannCurvature`'s tensoriality on
  constant lifts.
* `ricciSharp x : T_xM →ₗ[ℝ] T_xM` — metric-raised Ricci endomorphism
  via `metricToDualEquiv`.
* `scalarCurvature x : ℝ` — `LinearMap.trace` of `ricciSharp x`.

Scoped notations `Ric_g(v, w) x` and `scal_g[I]` ship with this
file. Downstream consumers (`Operators/Bochner/*`) import this
Foundation directly to access the bundle and notation.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle VectorField
open scoped ContDiff Manifold Riemannian InnerProductSpace

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Eng.** Constant smooth vector field at a tangent vector. Hides
`SmoothVectorField.const (I := I) (M := M) V` boilerplate inside this file. -/
local notation "cF[" V "]" => SmoothVectorField.const (I := I) (M := M) V

/-- **Math.** The **Ricci tensor** at $x$ as a bilinear form $T_xM \times T_xM \to \mathbb{R}$,
$(V, W) \mapsto \mathrm{Ric}(V, W)(x)$ with $V, W$ extended to constant sections.
Bundled as a `LinearMap → LinearMap → ℝ` for downstream metric raising. -/
noncomputable def ricciTensor
    (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ where
  toFun V :=
    { toFun := fun W =>
        ricci g (cF[V])
              (cF[W]) x
      map_add' := fun W₁ W₂ => by
        -- Route via `curvatureEndo` LinearMap-additivity, then trace.
        show ricci g (cF[V])
              (cF[W₁ + W₂]) x
            = ricci g (cF[V])
                (cF[W₁]) x
              + ricci g (cF[V])
                (cF[W₂]) x
        unfold ricci
        rw [show curvatureEndo g (cF[V])
                  (cF[W₁ + W₂]) x
              = curvatureEndo g (cF[V])
                  (cF[W₁]) x
                + curvatureEndo g (cF[V])
                  (cF[W₂]) x from ?_]
        · exact (LinearMap.trace ℝ _).map_add _ _
        -- Pointwise LinearMap equality.
        refine LinearMap.ext fun z => ?_
        show riemannCurvature g (fun _ => z)
              (cF[V]).toFun
              (cF[W₁ + W₂]).toFun x
            = riemannCurvature g (fun _ => z)
                (cF[V]).toFun
                (cF[W₁]).toFun x
              + riemannCurvature g (fun _ => z)
                (cF[V]).toFun
                (cF[W₂]).toFun x
        -- Π-equality: const(W₁+W₂) = const W₁ + const W₂.
        have h_const_add : ((fun _ : M => W₁ + W₂) : (y : M) → TangentSpace I y)
            = (fun _ => W₁) + (fun _ => W₂) := by funext y; rfl
        have h_const_W₁_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => W₁) y :=
          fun y => (cF[W₁]).smoothAt y
        have h_const_W₂_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => W₂) y :=
          fun y => (cF[W₂]).smoothAt y
        have h_const_z_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => z) y :=
          fun y => (cF[z]).smoothAt y
        have h_const_V_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => V) y :=
          fun y => (cF[V]).smoothAt y
        show covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V)
                  (fun _ : M => W₁ + W₂) y) x
              - covDeriv g (fun _ : M => V) (fun y => covDeriv g (fun _ => z)
                  (fun _ : M => W₁ + W₂) y) x
              - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                  (fun _ : M => W₁ + W₂) x
            = (covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V)
                    (fun _ : M => W₁) y) x
                - covDeriv g (fun _ : M => V) (fun y => covDeriv g (fun _ => z)
                    (fun _ : M => W₁) y) x
                - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                    (fun _ : M => W₁) x)
              + (covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V)
                    (fun _ : M => W₂) y) x
                - covDeriv g (fun _ : M => V) (fun y => covDeriv g (fun _ => z)
                    (fun _ : M => W₂) y) x
                - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                    (fun _ : M => W₂) x)
        -- Π-equality for the sum-of-constant-sections form.
        have h_const_W_sum : ((fun _ : M => W₁ + W₂) : (y : M) → TangentSpace I y)
            = (fun _ => W₁) + (fun _ => W₂) := by funext y; rfl
        -- Term1 inner: rewrite W₁+W₂ as Π-sum, apply covDeriv_add_field.
        have h_inner_T1 :
            ((fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₁ + W₂) y) :
              (y : M) → TangentSpace I y)
            = (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₁) y)
              + (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₂) y) := by
          funext y
          rw [show ((fun _ : M => W₁ + W₂) : (z : M) → TangentSpace I z)
                = (fun _ => W₁) + (fun _ => W₂) from h_const_W_sum]
          exact covDeriv_add_field g (fun _ => V) (fun _ => W₁) (fun _ => W₂) y
            (h_const_W₁_smooth y) (h_const_W₂_smooth y)
        rw [h_inner_T1]
        have h_inner_T2 :
            ((fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₁ + W₂) y) :
              (y : M) → TangentSpace I y)
            = (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₁) y)
              + (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₂) y) := by
          funext y
          rw [show ((fun _ : M => W₁ + W₂) : (z : M) → TangentSpace I z)
                = (fun _ => W₁) + (fun _ => W₂) from h_const_W_sum]
          exact covDeriv_add_field g (fun _ => z) (fun _ => W₁) (fun _ => W₂) y
            (h_const_W₁_smooth y) (h_const_W₂_smooth y)
        rw [h_inner_T2]
        -- Term3: convert `(fun _ => W₁+W₂)` to Π-add, then split.
        have hT3 : covDeriv g
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W₁ + W₂) x
            = covDeriv g
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W₁) x
            + covDeriv g
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W₂) x := by
          rw [show ((fun _ : M => W₁ + W₂) : (z : M) → TangentSpace I z)
                = (fun _ => W₁) + (fun _ => W₂) from h_const_W_sum]
          exact covDeriv_add_field g
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ => W₁) (fun _ => W₂) x
              (h_const_W₁_smooth x) (h_const_W₂_smooth x)
        rw [hT3]
        -- Outer T1: direction `(fun _ => z)` via covDeriv_add_field g on the
        -- differentiated section sum.
        have hT1 :
            covDeriv g (fun _ : M => z)
              (((fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₁) y) :
                  (y : M) → TangentSpace I y)
                + (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₂) y)) x
            = covDeriv g (fun _ : M => z)
                (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₁) y) x
              + covDeriv g (fun _ : M => z)
                (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₂) y) x :=
          covDeriv_add_field g (fun _ => z)
            (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₁) y)
            (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W₂) y) x
            (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) V
              (cF[W₁]) x)
            (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) V
              (cF[W₂]) x)
        rw [hT1]
        -- Outer T2: direction `(fun _ => V)` of inner T2 sum.
        have hT2 :
            covDeriv g (fun _ : M => V)
              (((fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₁) y) :
                  (y : M) → TangentSpace I y)
                + (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₂) y)) x
            = covDeriv g (fun _ : M => V)
                (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₁) y) x
              + covDeriv g (fun _ : M => V)
                (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₂) y) x :=
          covDeriv_add_field g (fun _ => V)
            (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₁) y)
            (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W₂) y) x
            (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z
              (cF[W₁]) x)
            (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z
              (cF[W₂]) x)
        rw [hT2]
        abel
      map_smul' := fun c W => by
        show ricci g (cF[V])
              (cF[c • W]) x
            = (RingHom.id ℝ) c • ricci g
                (cF[V])
                (cF[W]) x
        unfold ricci
        rw [show curvatureEndo g (cF[V])
                  (cF[c • W]) x
              = c • curvatureEndo g (cF[V])
                  (cF[W]) x from ?_]
        · simp
        refine LinearMap.ext fun z => ?_
        show riemannCurvature g (fun _ => z)
              (cF[V]).toFun
              (cF[c • W]).toFun x
            = c • riemannCurvature g (fun _ => z)
                (cF[V]).toFun
                (cF[W]).toFun x
        have h_const_smul : ((fun _ : M => c • W) : (y : M) → TangentSpace I y)
            = c • (fun _ => W) := by funext y; rfl
        have h_const_W_smooth : ∀ y, TangentSmoothAt
            (fun _ : M => W) y :=
          fun y => (cF[W]).smoothAt y
        show covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V)
                  (fun _ : M => c • W) y) x
              - covDeriv g (fun _ : M => V) (fun y => covDeriv g (fun _ => z)
                  (fun _ : M => c • W) y) x
              - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                  (fun _ : M => c • W) x
            = c • (covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V)
                    (fun _ : M => W) y) x
                - covDeriv g (fun _ : M => V) (fun y => covDeriv g (fun _ => z)
                    (fun _ : M => W) y) x
                - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                    (fun _ : M => W) x)
        -- Term 1 inner.
        have h_inner_T1 :
            ((fun y => covDeriv g (fun _ : M => V) (fun _ : M => c • W) y) :
              (y : M) → TangentSpace I y)
            = c • (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y) := by
          funext y
          rw [show ((fun _ : M => c • W) : (z : M) → TangentSpace I z)
                = c • (fun _ => W) from h_const_smul]
          exact covDeriv_smul_const_field g (fun _ => V) (fun _ => W) y c
            (h_const_W_smooth y)
        rw [h_inner_T1]
        have h_inner_T2 :
            ((fun y => covDeriv g (fun _ : M => z) (fun _ : M => c • W) y) :
              (y : M) → TangentSpace I y)
            = c • (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W) y) := by
          funext y
          rw [show ((fun _ : M => c • W) : (z : M) → TangentSpace I z)
                = c • (fun _ => W) from h_const_smul]
          exact covDeriv_smul_const_field g (fun _ => z) (fun _ => W) y c
            (h_const_W_smooth y)
        rw [h_inner_T2]
        -- Term 3: covDeriv g (...) (c • const W) x = c • covDeriv g (...) (const W) x.
        have hT3 : covDeriv g
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => c • W) x
            = c • covDeriv g
              (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
              (fun _ : M => W) x := by
          rw [show ((fun _ : M => c • W) : (z : M) → TangentSpace I z)
                = c • (fun _ => W) from h_const_smul]
          exact covDeriv_smul_const_field g
            (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y)
            (fun _ => W) x c (h_const_W_smooth x)
        rw [hT3]
        -- Outer T1: direction `(fun _ => z)`, differentiated `c • F`.
        have hT1 :
            covDeriv g (fun _ : M => z)
              ((c • (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y)) :
                  (y : M) → TangentSpace I y) x
            = c • covDeriv g (fun _ : M => z)
                (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y) x :=
          covDeriv_smul_const_field g (fun _ => z)
            (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y) x c
            (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) V
              (cF[W]) x)
        rw [hT1]
        have hT2 :
            covDeriv g (fun _ : M => V)
              ((c • (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W) y)) :
                  (y : M) → TangentSpace I y) x
            = c • covDeriv g (fun _ : M => V)
                (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W) y) x :=
          covDeriv_smul_const_field g (fun _ => V)
            (fun y => covDeriv g (fun _ : M => z) (fun _ : M => W) y) x c
            (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z
              (cF[W]) x)
        rw [hT2]
        rw [smul_sub, smul_sub] }
  map_add' V₁ V₂ := by
    -- LinearMap-level additivity in V slot.
    refine LinearMap.ext fun W => ?_
    show ricci g (cF[V₁ + V₂])
            (cF[W]) x
        = ricci g (cF[V₁])
            (cF[W]) x
          + ricci g (cF[V₂])
            (cF[W]) x
    unfold ricci
    rw [show curvatureEndo g (cF[V₁ + V₂])
              (cF[W]) x
          = curvatureEndo g (cF[V₁])
              (cF[W]) x
            + curvatureEndo g (cF[V₂])
              (cF[W]) x from ?_]
    · exact (LinearMap.trace ℝ _).map_add _ _
    refine LinearMap.ext fun z => ?_
    show riemannCurvature g (fun _ => z)
          (cF[V₁ + V₂]).toFun
          (cF[W]).toFun x
        = riemannCurvature g (fun _ => z)
            (cF[V₁]).toFun
            (cF[W]).toFun x
          + riemannCurvature g (fun _ => z)
            (cF[V₂]).toFun
            (cF[W]).toFun x
    have h_const_add : ((fun _ : M => V₁ + V₂) : (y : M) → TangentSpace I y)
        = (fun _ => V₁) + (fun _ => V₂) := by funext y; rfl
    have h_const_V₁_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => V₁) y :=
      fun y => (cF[V₁]).smoothAt y
    have h_const_V₂_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => V₂) y :=
      fun y => (cF[V₂]).smoothAt y
    show covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V₁ + V₂)
              (fun _ : M => W) y) x
          - covDeriv g (fun _ : M => V₁ + V₂)
              (fun y => covDeriv g (fun _ => z) (fun _ : M => W) y) x
          - covDeriv g (fun y => mlieBracket I (fun _ => z)
              (fun _ : M => V₁ + V₂) y) (fun _ : M => W) x
        = (covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V₁)
                (fun _ : M => W) y) x
            - covDeriv g (fun _ : M => V₁) (fun y => covDeriv g (fun _ => z)
                (fun _ : M => W) y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₁) y)
                (fun _ : M => W) x)
          + (covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V₂)
                (fun _ : M => W) y) x
            - covDeriv g (fun _ : M => V₂) (fun y => covDeriv g (fun _ => z)
                (fun _ : M => W) y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₂) y)
                (fun _ : M => W) x)
    -- Term 1 inner: direction-continuous linear map-linearity of covDeriv g.
    have h_inner_T1 :
        ((fun y => covDeriv g (fun _ : M => V₁ + V₂) (fun _ : M => W) y) :
          (y : M) → TangentSpace I y)
        = (fun y => covDeriv g (fun _ : M => V₁) (fun _ : M => W) y)
          + (fun y => covDeriv g (fun _ : M => V₂) (fun _ : M => W) y) := by
      funext y
      show ((leviCivitaConnection g).toFun (fun _ : M => W) y) (V₁ + V₂)
          = ((leviCivitaConnection g).toFun (fun _ : M => W) y) V₁
            + ((leviCivitaConnection g).toFun (fun _ : M => W) y) V₂
      exact map_add _ _ _
    rw [h_inner_T1]
    -- Term 2: outer covDeriv g direction (V₁+V₂) at section-level via continuous linear map.
    -- Stash the differentiated section so its type is fully determined.
    set Fz : (y : M) → TangentSpace I y :=
      fun y => covDeriv g (fun _ : M => z) (fun _ : M => W) y with hFz
    have hT2 : covDeriv g (fun _ : M => V₁ + V₂) Fz x
        = covDeriv g (fun _ : M => V₁) Fz x + covDeriv g (fun _ : M => V₂) Fz x := by
      show ((leviCivitaConnection g).toFun Fz x) (V₁ + V₂)
          = ((leviCivitaConnection g).toFun Fz x) V₁
            + ((leviCivitaConnection g).toFun Fz x) V₂
      exact map_add _ _ _
    rw [hT2]
    -- Term 3: mlieBracket additivity in right argument.
    have h_lieBr_add :
        ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₁ + V₂) y) :
          (y : M) → TangentSpace I y)
        = (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₁) y)
          + (fun y => mlieBracket I (fun _ => z) (fun _ : M => V₂) y) := by
      funext y
      rw [show ((fun _ : M => V₁ + V₂) : (z : M) → TangentSpace I z)
            = (fun _ => V₁) + (fun _ => V₂) from h_const_add]
      exact VectorField.mlieBracket_add_right (h_const_V₁_smooth y) (h_const_V₂_smooth y)
    rw [h_lieBr_add]
    -- Outer covDeriv g on T3: direction is the sum, differentiated is `const W`.
    have hT3 : covDeriv g ((fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₁) y)
            + (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₂) y))
              (fun _ : M => W) x
        = covDeriv g (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₁) y) (fun _ : M => W) x
          + covDeriv g (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V₂) y) (fun _ : M => W) x := by
      show ((leviCivitaConnection g).toFun (fun _ : M => W) x)
            ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₁) y) x
              + (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₂) y) x)
          = ((leviCivitaConnection g).toFun (fun _ : M => W) x)
              ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₁) y) x)
            + ((leviCivitaConnection g).toFun (fun _ : M => W) x)
              ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V₂) y) x)
      exact map_add _ _ _
    -- Outer covDeriv g on T1: direction `(fun _ => z)`, differentiated sum.
    have hT1 :
        covDeriv g (fun _ : M => z)
            (((fun y => covDeriv g (fun _ : M => V₁) (fun _ : M => W) y) :
                (y : M) → TangentSpace I y)
              + (fun y => covDeriv g (fun _ : M => V₂) (fun _ : M => W) y)) x
        = covDeriv g (fun _ : M => z)
              (fun y => covDeriv g (fun _ : M => V₁) (fun _ : M => W) y) x
          + covDeriv g (fun _ : M => z)
              (fun y => covDeriv g (fun _ : M => V₂) (fun _ : M => W) y) x :=
      covDeriv_add_field g (fun _ => z)
        (fun y => covDeriv g (fun _ : M => V₁) (fun _ : M => W) y)
        (fun y => covDeriv g (fun _ : M => V₂) (fun _ : M => W) y) x
        (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) V₁
          (cF[W]) x)
        (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) V₂
          (cF[W]) x)
    rw [hT1, hT3]
    abel
  map_smul' c V := by
    refine LinearMap.ext fun W => ?_
    show ricci g (cF[c • V])
            (cF[W]) x
        = ((RingHom.id ℝ) c • ricci g (cF[V])
            (cF[W]) x : ℝ)
    unfold ricci
    rw [show curvatureEndo g (cF[c • V])
              (cF[W]) x
          = c • curvatureEndo g (cF[V])
              (cF[W]) x from ?_]
    · simp
    refine LinearMap.ext fun z => ?_
    show riemannCurvature g (fun _ => z)
          (cF[c • V]).toFun
          (cF[W]).toFun x
        = c • riemannCurvature g (fun _ => z)
            (cF[V]).toFun
            (cF[W]).toFun x
    have h_const_smul : ((fun _ : M => c • V) : (y : M) → TangentSpace I y)
        = c • (fun _ => V) := by funext y; rfl
    have h_const_V_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => V) y :=
      fun y => (cF[V]).smoothAt y
    show covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => c • V)
              (fun _ : M => W) y) x
          - covDeriv g (fun _ : M => c • V)
              (fun y => covDeriv g (fun _ => z) (fun _ : M => W) y) x
          - covDeriv g (fun y => mlieBracket I (fun _ => z)
              (fun _ : M => c • V) y) (fun _ : M => W) x
        = c • (covDeriv g (fun _ => z) (fun y => covDeriv g (fun _ : M => V)
                (fun _ : M => W) y) x
            - covDeriv g (fun _ : M => V) (fun y => covDeriv g (fun _ => z)
                (fun _ : M => W) y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z) (fun _ : M => V) y)
                (fun _ : M => W) x)
    -- Term 1 inner.
    have h_inner_T1 :
        ((fun y => covDeriv g (fun _ : M => c • V) (fun _ : M => W) y) :
          (y : M) → TangentSpace I y)
        = c • (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y) := by
      funext y
      show ((leviCivitaConnection g).toFun (fun _ : M => W) y) (c • V)
          = c • ((leviCivitaConnection g).toFun (fun _ : M => W) y) V
      exact ContinuousLinearMap.map_smul _ _ _
    rw [h_inner_T1]
    -- Term 2: outer covDeriv g direction is c • V at section level.
    set Fz : (y : M) → TangentSpace I y :=
      fun y => covDeriv g (fun _ : M => z) (fun _ : M => W) y with hFz
    have hT2 : covDeriv g (fun _ : M => c • V) Fz x
        = c • covDeriv g (fun _ : M => V) Fz x := by
      show ((leviCivitaConnection g).toFun Fz x) (c • V)
          = c • ((leviCivitaConnection g).toFun Fz x) V
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hT2]
    -- Term 3: mlieBracket scalar in right arg.
    have h_lieBr_smul :
        ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => c • V) y) :
          (y : M) → TangentSpace I y)
        = c • (fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y) := by
      funext y
      rw [show ((fun _ : M => c • V) : (z : M) → TangentSpace I z)
            = c • (fun _ => V) from h_const_smul]
      exact VectorField.mlieBracket_const_smul_right (h_const_V_smooth y)
    rw [h_lieBr_smul]
    have hT3 : covDeriv g (c • (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V) y)) (fun _ : M => W) x
        = c • covDeriv g (fun y => mlieBracket I (fun _ : M => z)
              (fun _ : M => V) y) (fun _ : M => W) x := by
      show ((leviCivitaConnection g).toFun (fun _ : M => W) x)
            ((c • fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y) x)
          = c • ((leviCivitaConnection g).toFun (fun _ : M => W) x)
              ((fun y => mlieBracket I (fun _ : M => z) (fun _ : M => V) y) x)
      show ((leviCivitaConnection g).toFun (fun _ : M => W) x)
            (c • mlieBracket I (fun _ : M => z) (fun _ : M => V) x)
          = c • ((leviCivitaConnection g).toFun (fun _ : M => W) x)
              (mlieBracket I (fun _ : M => z) (fun _ : M => V) x)
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hT3]
    -- Outer T1: direction `(fun _ => z)`, differentiated `c • F`.
    have hT1 :
        covDeriv g (fun _ : M => z)
            ((c • (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y)) :
                (y : M) → TangentSpace I y) x
        = c • covDeriv g (fun _ : M => z)
              (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y) x :=
      covDeriv_smul_const_field g (fun _ => z)
        (fun y => covDeriv g (fun _ : M => V) (fun _ : M => W) y) x c
        (covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) V
          (cF[W]) x)
    rw [hT1]
    rw [smul_sub, smul_sub]

/-- **Math.** The **Ricci endomorphism** $\mathrm{Ric}^{\sharp}_x : T_xM \to T_xM$ defined
by metric raising of the Ricci tensor:
$\langle \mathrm{Ric}^{\sharp}_x V, W \rangle_g = \mathrm{Ric}(V, W)(x)$. -/
noncomputable def ricciSharp
    (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun V :=
    (g.metricToDualEquiv x).symm (ricciTensor (I := I) (M := M) g x V).toContinuousLinearMap
  map_add' V₁ V₂ := by
    show (g.metricToDualEquiv x).symm ((ricciTensor g x (V₁ + V₂)).toContinuousLinearMap)
        = (g.metricToDualEquiv x).symm ((ricciTensor g x V₁).toContinuousLinearMap)
        + (g.metricToDualEquiv x).symm ((ricciTensor g x V₂).toContinuousLinearMap)
    rw [show ricciTensor (I := I) (M := M) g x (V₁ + V₂)
          = ricciTensor g x V₁ + ricciTensor g x V₂ from
        (ricciTensor (I := I) (M := M) g x).map_add V₁ V₂]
    show (g.metricToDualEquiv x).symm
          ((ricciTensor g x V₁ + ricciTensor g x V₂).toContinuousLinearMap)
        = (g.metricToDualEquiv x).symm ((ricciTensor g x V₁).toContinuousLinearMap)
        + (g.metricToDualEquiv x).symm ((ricciTensor g x V₂).toContinuousLinearMap)
    rw [show (ricciTensor (I := I) (M := M) g x V₁
                + ricciTensor g x V₂).toContinuousLinearMap
          = (ricciTensor g x V₁).toContinuousLinearMap
            + (ricciTensor g x V₂).toContinuousLinearMap from
        LinearMap.toContinuousLinearMap.map_add _ _]
    exact (g.metricToDualEquiv x).symm.map_add _ _
  map_smul' c V := by
    show (g.metricToDualEquiv x).symm ((ricciTensor g x (c • V)).toContinuousLinearMap)
        = c • (g.metricToDualEquiv x).symm ((ricciTensor g x V).toContinuousLinearMap)
    rw [show ricciTensor (I := I) (M := M) g x (c • V)
          = c • ricciTensor g x V from
        (ricciTensor (I := I) (M := M) g x).map_smul c V]
    show (g.metricToDualEquiv x).symm ((c • ricciTensor g x V).toContinuousLinearMap)
        = c • (g.metricToDualEquiv x).symm ((ricciTensor g x V).toContinuousLinearMap)
    rw [show (c • ricciTensor (I := I) (M := M) g x V).toContinuousLinearMap
          = c • (ricciTensor g x V).toContinuousLinearMap from
        LinearMap.toContinuousLinearMap.map_smul _ _]
    exact (g.metricToDualEquiv x).symm.map_smul c _

/-- **Math.** The **scalar curvature** $\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x)
= \mathrm{tr}(\mathrm{Ric}^{\sharp}_x)$.

Basis-free definition: trace of the Ricci endomorphism. Equals $\sum_i \mathrm{Ric}(e_i, e_i)$
for any $g$-orthonormal basis $\{e_i\}$ of $T_xM$. -/
noncomputable def scalarCurvature
    (g : RiemannianMetric I M) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (ricciSharp (I := I) (M := M) g x)



/-! ## Ricci-flat and Einstein metric predicates

These predicates describe properties of the ambient Riemannian metric
(via `[hm : HasMetric I M]` in scope); they do not take the metric as an
explicit argument because the underlying notations (`Ric_g`,
`metricInner`) already consume the metric through the typeclass. -/

/-- **Math.** The ambient Riemannian metric is **Ricci-flat** if its
Ricci tensor vanishes pointwise. -/
def IsRicciFlat : Prop :=
  ∀ (x : M) (V W : TangentSpace I x), ricciTensor HasMetric.metric x V W = 0

/-- **Math.** The ambient Riemannian metric is **Einstein** if its Ricci
tensor is a constant scalar multiple of the metric:
$\mathrm{Ric}_g(V, W)(x) = c \cdot g_x(V, W)$ for all $x, V, W$ and a
fixed real constant $c$ (the *Einstein constant*).

Reference: do Carmo §4 Ex. 6; Petersen Ch. 3 §6. -/
def IsEinstein : Prop :=
  ∃ c : ℝ, ∀ (x : M) (V W : TangentSpace I x),
    ricciTensor HasMetric.metric x V W = c * HasMetric.metric.metricInner x V W

end Riemannian

end
