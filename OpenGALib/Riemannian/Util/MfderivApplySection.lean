import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame.ChartBasis

/-!
# Smoothness of `mfderiv f` applied to a tangent-bundle section

Chart-pullback machinery: for smooth scalar `f : M → ℝ` and a smooth
tangent-bundle section `Y`, the scalar map $y \mapsto (\mathrm{d}f)_y(Y(y))$
is `ContMDiff`. The proof uses the chart-pullback identity
$\mathrm{d}f(e_j(x)) = \partial_j (f \circ \varphi^{-1})(\varphi(x))$
on the chart base set, with `[I.Boundaryless]` ensuring the chart target
is open and hence equals its interior.

Three public results:

* `mfderiv_apply_section_contMDiffOn` — chart-local version on the
  trivialization base set at `α`.
* `mfderiv_apply_section_contMDiff` — global lift via local charts.
* `mfderiv_chartBasisVec_apply_contMDiffOn` — specialised to
  $Y = \mathrm{chartBasisVec}\,\alpha\,j$, the form expected by
  `metricRiesz_section_contMDiffAt_of_within`.

Consumed by `Connection/CovDerivSmoothness.lean` (via
`mfderiv_apply_section_contMDiff` in the smoothness clause for the
six Koszul terms) and `Gradient.lean`
(`manifoldGradient_smooth_of_smooth`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** The pullback of `f : M → ℝ` through the inverse extended chart at `α`,
viewed as a scalar function on `E`. -/
private def scalarOnE (α : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I α).symm y)

/-- **Eng.** The directional derivative of `u : E → ℝ` at `y` along the `i`-th
model-basis vector. -/
private def partialDerivE (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((Module.finBasis ℝ E) i)

/-- **Eng.** The chart-pullback `scalarOnE α f` of a smooth function `f` is $C^\infty$
on the extended-chart target. -/
private lemma scalarOnE_contDiffOn (α : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hf_on : ContMDiffOn I 𝓘(ℝ) ∞ f Set.univ := hf.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f ∘ (extChartAt I α).symm)
      (extChartAt I α).target :=
    hf_on.comp hsymm (fun _ _ => Set.mem_univ _)
  exact hcomp.contDiffOn

/-- **Eng.** The partial derivative of the chart-pullback is $C^\infty$ on the interior
of the extended-chart target. -/
private lemma partialDerivE_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDerivE (E := E) i (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  have hbase : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hbase.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (Module.finBasis ℝ E) i)
      (interior (extChartAt I α).target) := contDiffOn_const
  exact hfderiv.clm_apply hconst

/-- **Eng.** The partial derivative of the chart-pullback, composed with the extended
chart, is `ContMDiffOn` on the chart base set under `[I.Boundaryless]` (where
the chart target is open and hence equals its interior). -/
private lemma partialDerivE_scalarOnE_comp_extChartAt_contMDiffOn
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDerivE (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have htgt_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have htgt_int : interior (extChartAt I α).target = (extChartAt I α).target :=
    htgt_open.interior_eq
  have hpartial : ContDiffOn ℝ ∞
      (partialDerivE (E := E) i (scalarOnE (I := I) α f))
      (extChartAt I α).target := by
    rw [← htgt_int]
    exact partialDerivE_scalarOnE_contDiffOn_interior (I := I) α hf i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (partialDerivE (E := E) i (scalarOnE (I := I) α f))
      (extChartAt I α).target := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet
      = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
  rw [hbase_eq]
  refine hpartialM.comp hchart ?_
  intro x hx
  -- `extChartAt I α x ∈ target` for `x ∈ chartSource`.
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx
  exact (extChartAt I α).map_source hxsrc

/-- **Mixed.** Chart-basis evaluation of `mfderiv`: under `[I.Boundaryless]`, the
directional derivative of a smooth scalar `f` along the `i`-th chart-basis
vector equals the `i`-th partial derivative of the chart pullback, evaluated
at the chart image of the base point.

For $x \in (\mathrm{chartAt}\,H\,\alpha).\mathrm{source}$:
$$\mathrm{d}f_x(e_i^\alpha(x)) = \partial_i (f \circ \varphi_\alpha^{-1})(\varphi_\alpha(x)).$$ -/
private lemma mfderiv_chartBasisVecFiber_eq_partialDerivE
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x (chartBasisVecFiber (I := I) α i x)
      = partialDerivE (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]; exact hx
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  -- Set up: `f = scalarOnE α f ∘ φ` near `x` on `φ.source`.
  have hcomp_eq : ∀ᶠ y in nhds x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ nhds x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    change f y = f (φ.symm (φ y))
    rw [φ.left_inv hy]
  have hcong : f =ᶠ[nhds x] (scalarOnE (I := I) α f) ∘ φ := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f x =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  -- Differentiability of `scalarOnE α f` at `φ x`. We go through
  -- `scalarOnE α f = f ∘ φ.symm` definitionally, plus `φ.symm` smooth at `φ x`.
  have htgt_open : IsOpen φ.target := isOpen_extChartAt_target (I := I) α
  have hxtgt : φ x ∈ φ.target := φ.map_source hxsrc
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) φ x :=
    mdifferentiableAt_extChartAt (I := I) hx
  have hphi_symm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ x) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm (φ x) :=
      (hcontMDiffOn (φ x) hxtgt).contMDiffAt (htgt_open.mem_nhds hxtgt)
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_x : φ.symm (φ x) = x := φ.left_inv hxsrc
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ) f (φ.symm (φ x)) := by
    rw [hsymm_at_x]; exact hf_mdiff
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ φ.symm) (φ x) :=
    hf_at_symm.comp (φ x) hphi_symm_mdiff
  have hscalar_eq : (scalarOnE (I := I) α f) = f ∘ φ.symm := by
    funext y; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x) := by
    rw [hscalar_eq]; exact hf_comp_symm
  -- Apply chain rule for the composition `(scalarOnE α f) ∘ φ`.
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hg_mdiff hphi_mdiff
  rw [hchain]
  -- `mfderiv (E → ℝ) (scalarOnE α f) = fderiv ℝ (scalarOnE α f)` (model space).
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  -- Identify `mfderiv φ x (chartBasisVecFiber α i x) = Module.finBasis ℝ E i`
  -- via the tangent-bundle trivialization at α applied to chartBasisVec.
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) φ x (chartBasisVecFiber (I := I) α i x)
        = (Module.finBasis ℝ E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx]
    set T : Bundle.Trivialization E
        (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I : M → Type _)
          → M) := trivializationAt E (TangentSpace I) α
    -- chartBasisVecFiber α i x = T.symm x (basis i) = (T.symmL ℝ x) (basis i).
    have heq : chartBasisVecFiber (I := I) α i x =
        (T.symmL ℝ x) ((Module.finBasis ℝ E) i) := by
      show T.symm x ((Module.finBasis ℝ E) i) = (T.symmL ℝ x) ((Module.finBasis ℝ E) i)
      rfl
    rw [heq]
    exact T.continuousLinearMapAt_symmL (R := ℝ) hbase ((Module.finBasis ℝ E) i)
  -- Conclude via `mfderiv (scalarOnE α f)(φ x) = fderiv` + identification of
  -- composition value with the partial derivative.
  show (fderiv ℝ (scalarOnE (I := I) α f) (φ x))
        ((mfderiv I 𝓘(ℝ, E) φ x) (chartBasisVecFiber (I := I) α i x)) =
    partialDerivE (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

/-- **Eng.** Smoothness of the directional derivative `y ↦ mfderiv f y (V y)` on the
trivialization base set at $\alpha$, for a smooth scalar function $f$ and a
smooth tangent-bundle section $V$, under `[I.Boundaryless]`.

Chart-pullback decomposition: on the base set,
$$\mathrm{d}f_y(V(y)) = \mathrm{d}(f\circ\varphi_\alpha^{-1})_{\varphi_\alpha(y)}
    \bigl(V^{\mathrm{chart}}(y)\bigr),$$
where $V^{\mathrm{chart}}(y) := \mathrm{triv}_\alpha\langle y, V(y)\rangle_2 \in E$
is the chart-frame coordinate of $V(y)$. The RHS is smooth in $y$ on the base
set because (i) $f\circ\varphi_\alpha^{-1}$ is $C^\infty$ on the chart target
(`scalarOnE_contDiffOn`), (ii) `fderiv` of a $C^\infty$ function on an open set
is $C^\infty$, (iii) `extChartAt I α` is smooth on its source, and (iv)
$V^{\mathrm{chart}}$ is smooth on the base set by
`Trivialization.contMDiffOn_section_baseSet_iff`. -/
lemma mfderiv_apply_section_contMDiffOn
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (V y) :
        TotalSpace E (TangentSpace I : M → Type _)))) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun y => mfderiv I 𝓘(ℝ) f y (V y))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set triv := trivializationAt E (TangentSpace I) α with htriv_def
  set s := triv.baseSet
  -- `V` evaluated in chart coords at α: smooth on `s`.
  have hVchart_total :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => (TotalSpace.mk' E y (V y) :
          TotalSpace E (TangentSpace I : M → Type _))) s :=
    hV.contMDiffOn
  have hVchart_snd :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun y => (triv ⟨y, V y⟩).2) s :=
    (triv.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)).mp hVchart_total
  -- `fderiv (scalarOnE α f)` smooth on the (open under Boundaryless) chart target.
  have htgt_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have hsmooth : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hfderiv_smooth : ContDiffOn ℝ ∞
      (fderiv ℝ (scalarOnE (I := I) α f)) (extChartAt I α).target :=
    hsmooth.fderiv_of_isOpen htgt_open (by rw [ENat.coe_top_add_one])
  have hfderivM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fderiv ℝ (scalarOnE (I := I) α f)) (extChartAt I α).target :=
    hfderiv_smooth.contMDiffOn
  -- Compose with `extChartAt I α` (smooth on its source = `s`).
  have hbase_eq : s = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E) s := by
    rw [hbase_eq]; exact contMDiffOn_extChartAt
  have hfderivComp :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
        (fun y => fderiv ℝ (scalarOnE (I := I) α f) (extChartAt I α y)) s := by
    refine hfderivM.comp hchart ?_
    intro y hy
    have hysrc : y ∈ (extChartAt I α).source := by
      rw [extChartAt_source, ← hbase_eq]; exact hy
    exact (extChartAt I α).map_source hysrc
  -- Combine via `ContMDiffOn.clm_apply`.
  have happly :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => fderiv ℝ (scalarOnE (I := I) α f) (extChartAt I α y)
          ((triv ⟨y, V y⟩).2)) s := hfderivComp.clm_apply hVchart_snd
  refine happly.congr ?_
  intro y hy
  -- Identify the RHS with mfderiv via the chain rule (analog of
  -- `mfderiv_chartBasisVecFiber_eq_partialDerivE`).
  have hy_chart : y ∈ (chartAt H α).source := by rw [← hbase_eq]; exact hy
  -- mfderiv f y (V y) = fderiv (scalarOnE α f) (extChartAt α y) (mfderiv (extChartAt α) y (V y)).
  set φ := extChartAt I α
  have hysrc : y ∈ φ.source := by
    rw [extChartAt_source]; exact hy_chart
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ) f y := hf.mdifferentiableAt (by simp)
  have hcomp_eq : ∀ᶠ z in nhds y, f z = (scalarOnE (I := I) α f) (φ z) := by
    have hsrc_nhd : φ.source ∈ nhds y :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hysrc
    filter_upwards [hsrc_nhd] with z hz
    change f z = f (φ.symm (φ z))
    rw [φ.left_inv hz]
  have hcong : f =ᶠ[nhds y] (scalarOnE (I := I) α f) ∘ φ := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ) f y =
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) y :=
    Filter.EventuallyEq.mfderiv_eq hcong
  have hytgt : φ y ∈ φ.target := φ.map_source hysrc
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) φ y :=
    mdifferentiableAt_extChartAt (I := I) hy_chart
  have hphi_symm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ y) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) α
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm (φ y) :=
      (hcontMDiffOn (φ y) hytgt).contMDiffAt (htgt_open.mem_nhds hytgt)
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_y : φ.symm (φ y) = y := φ.left_inv hysrc
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ) f (φ.symm (φ y)) := by
    rw [hsymm_at_y]; exact hf_mdiff
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ φ.symm) (φ y) :=
    hf_at_symm.comp (φ y) hphi_symm_mdiff
  have hscalar_eq : (scalarOnE (I := I) α f) = f ∘ φ.symm := by funext z; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ y) := by
    rw [hscalar_eq]; exact hf_comp_symm
  have hchain :
      mfderiv I 𝓘(ℝ) ((scalarOnE (I := I) α f) ∘ φ) y =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ y)).comp
          (mfderiv I 𝓘(ℝ, E) φ y) :=
    mfderiv_comp y hg_mdiff hphi_mdiff
  rw [hmfderiv_cong, hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f) (φ y)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ y) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  -- Identify the action of `mfderiv (extChartAt I α) y` on `V y` with
  -- `triv.continuousLinearMapAt ℝ y (V y) = (triv ⟨y, V y⟩).2`.
  have hcLMAt :
      (triv.continuousLinearMapAt ℝ y) (V y) = (triv ⟨y, V y⟩).2 := by
    have hLEq := Bundle.Trivialization.coe_continuousLinearEquivAt_eq
      (R := ℝ) (e := triv) hy
    have h1 : (triv.continuousLinearEquivAt ℝ y hy) (V y) = (triv ⟨y, V y⟩).2 :=
      congrArg Prod.snd (triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy (V y))
    have h2 : (triv.continuousLinearEquivAt ℝ y hy : TangentSpace I y → E)
        = triv.continuousLinearMapAt ℝ y := hLEq
    have h3 := congrFun h2 (V y)
    rw [h3] at h1
    exact h1
  have hmfderiv_eq : (mfderiv I 𝓘(ℝ, E) φ y) (V y) = (triv ⟨y, V y⟩).2 := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
        (x₀ := α) (x := y) hy_chart]
    exact hcLMAt
  show (fderiv ℝ (scalarOnE (I := I) α f) (φ y))
        ((mfderiv I 𝓘(ℝ, E) φ y) (V y)) =
      (fderiv ℝ (scalarOnE (I := I) α f) (φ y)) ((triv ⟨y, V y⟩).2)
  rw [hmfderiv_eq]

/-- **Eng.** Global version of `mfderiv_apply_section_contMDiffOn`: under `[I.Boundaryless]`,
the directional derivative of a smooth scalar along a smooth tangent section is
smooth on all of $M$. -/
lemma mfderiv_apply_section_contMDiff
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (V y) :
        TotalSpace E (TangentSpace I : M → Type _)))) :
    ContMDiff I 𝓘(ℝ) ∞
      (fun y => mfderiv I 𝓘(ℝ) f y (V y)) := by
  intro y
  have hy_base : y ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) y]
    exact mem_chart_source H y
  have hOn := mfderiv_apply_section_contMDiffOn (I := I) y hf hV
  have hopen : IsOpen (trivializationAt E (TangentSpace I) y).baseSet :=
    (trivializationAt E (TangentSpace I) y).open_baseSet
  exact (hOn y hy_base).contMDiffAt (hopen.mem_nhds hy_base)

/-- **Eng.** Smoothness of the directional derivative `y ↦ mfderiv f y (chartBasisVecFiber α j y)`
on the trivialization base set, under `[I.Boundaryless]`. Used to discharge the
covector-section hypothesis of `metricRiesz_section_contMDiffAt` for the
gradient consumer. -/
lemma mfderiv_chartBasisVec_apply_contMDiffOn
    [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun y => mfderiv I 𝓘(ℝ) f y (chartBasisVecFiber (I := I) α j y))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hpartial :=
    partialDerivE_scalarOnE_comp_extChartAt_contMDiffOn (I := I) α hf j
  refine hpartial.congr ?_
  intro y hy
  have hy_chart : y ∈ (chartAt H α).source := by
    rw [← TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hy
  exact mfderiv_chartBasisVecFiber_eq_partialDerivE (I := I) α hf hy_chart j


end Tensor
end Riemannian

end
