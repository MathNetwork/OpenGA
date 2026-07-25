import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import DifferentialGeometry.Geometry.Connection.LeviCivita.Uniqueness
import DifferentialGeometry.Bundle.LocalFrameRegularity
import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]







omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isLeviCivita_smoothFile
    (g : SmoothRiemannianMetric I M) :
    IsLeviCivita (I := I) (leviCivitaConnectionOfMetric (I := I) g) g :=
  leviCivitaConnectionOfMetric_isLeviCivita (I := I) g









private def localMetricCoeff
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E) (g : SmoothRiemannianMetric I M)
    (i j : ι) (y : M) : Real :=
  g.inner y (e.localFrame b i y) (e.localFrame b j y)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localFrame_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% (e.localFrame b i)) x :=
  (e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
    e.open_baseSet hx i

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricCoeff_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localMetricCoeff (I := I) e b g i j y) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun y : M =>
                TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have hi := localFrame_contMDiffAt (I := I) e b hx i
  have hj := localFrame_contMDiffAt (I := I) e b hx j
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun y : M =>
          (⟨y, localMetricCoeff (I := I) e b g i j y⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x := by
    simpa [localMetricCoeff] using
      ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hj
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricCoeff_deriv_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (a i j : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        extDerivFun (I := I)
          (fun q : M => localMetricCoeff (I := I) e b g i j q)
          y (e.localFrame b a y)) x := by
  exact extDerivFun_apply_contMDiffAt_of_section
    (I := I)
    (f := fun q : M => localMetricCoeff (I := I) e b g i j q)
    (X := e.localFrame b a)
    (localMetricCoeff_contMDiffAt (I := I) e b g hx i j)
    (localFrame_contMDiffAt (I := I) e b hx a)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricBracket_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        g.inner y (e.localFrame b i y)
          (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k) y)) x := by
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have hi := localFrame_contMDiffAt (I := I) e b hx i
  have hj := localFrame_contMDiffAt (I := I) e b hx j
  have hk := localFrame_contMDiffAt (I := I) e b hx k
  have hbr :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k))) x := by
    simpa using
      (ContMDiffAt.mlieBracket_vectorField
        (I := I) (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
        hj hk (by simp))
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun y : M =>
                TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)))
        x :=
    (g.contMDiff.contMDiffAt (x := x)).of_le (by simp)
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) ∞
        (fun y : M =>
          (⟨y,
            g.inner y (e.localFrame b i y)
              (VectorField.mlieBracket I (e.localFrame b j) (e.localFrame b k) y)⟩ :
            TotalSpace Real (Bundle.Trivial M Real))) x := by
    exact ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hg hi hbr
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_localFrame_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
          (e.localFrame b k) y) x := by
  have h1 := localMetricCoeff_deriv_contMDiffAt (I := I) e b g hx i j k
  have h2 := localMetricCoeff_deriv_contMDiffAt (I := I) e b g hx j k i
  have h3 := localMetricCoeff_deriv_contMDiffAt (I := I) e b g hx k i j
  have h4 := localMetricBracket_contMDiffAt (I := I) e b g hx i j k
  have h5 := localMetricBracket_contMDiffAt (I := I) e b g hx j k i
  have h6 := localMetricBracket_contMDiffAt (I := I) e b g hx k i j
  simpa [koszulScalar, directionalDeriv, localMetricCoeff] using
    (((h1.add h2).sub h3).sub h4).add h5 |>.add h6


private noncomputable def coordCLM {ι : Type*} (b : Module.Basis ι Real E) (i : ι) :
    E →L[Real] Real :=
  LinearMap.toContinuousLinearMap (b.coord i)


private noncomputable def basisBilin {ι : Type*} (b : Module.Basis ι Real E) (i j : ι) :
    E →L[Real] E →L[Real] Real :=
  (coordCLM (E := E) b i).smulRight (coordCLM (E := E) b j)

omit [CompleteSpace E] in
private theorem basisBilin_apply {ι : Type*} (b : Module.Basis ι Real E) (i j : ι)
    (v w : E) :
    basisBilin (E := E) b i j v w = b.coord i v * b.coord j w := by
  simp [basisBilin, coordCLM]




noncomputable def localMetricFlatBasis {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) :
    E →L[Real] E →L[Real] Real :=
  ∑ i : ι, ∑ j : ι,
    localMetricCoeff (I := I) e b g i j y • basisBilin (E := E) b i j

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
private theorem localMetricFlatBasis_apply {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (y : M) (v w : E) :
    localMetricFlatBasis (I := I) e b g y v w =
      ∑ i : ι, ∑ j : ι,
        localMetricCoeff (I := I) e b g i j y * b.coord i v * b.coord j w := by
  simp [localMetricFlatBasis, basisBilin_apply, mul_assoc]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localFrame_sum_coord_smul
    {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet) (v : E) :
    (∑ i : ι, b.coord i v • e.localFrame b i x) = e.symmL Real x v := by
  calc
    (∑ i : ι, b.coord i v • e.localFrame b i x)
        = ∑ i : ι, b.coord i v • e.symmL Real x (b i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [e.localFrame_apply_of_mem_baseSet (b := b) hx,
            Bundle.Trivialization.basisAt]
    _ = e.symmL Real x (∑ i : ι, b.coord i v • b i) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp [map_smul]
    _ = e.symmL Real x v := by
          have hsum : (∑ i : ι, b.coord i v • b i) = v := by
            simp [b.sum_repr v]
          rw [hsum]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
theorem localMetricFlatBasis_eq_inner {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (v w : E) :
    localMetricFlatBasis (I := I) e b g x v w =
      g.inner x (e.symmL Real x v) (e.symmL Real x w) := by
  have hv := localFrame_sum_coord_smul (I := I) e b hx v
  have hw := localFrame_sum_coord_smul (I := I) e b hx w
  calc
    localMetricFlatBasis (I := I) e b g x v w
        = g.inner x
            (∑ i : ι, b.coord i v • e.localFrame b i x)
            (∑ j : ι, b.coord j w • e.localFrame b j x) := by
          simp [localMetricFlatBasis_apply, localMetricCoeff, map_sum, map_smul,
            smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_comm]
          conv_rhs => rw [Finset.sum_comm]
    _ = g.inner x (e.symmL Real x v) (e.symmL Real x w) := by
          rw [hv, hw]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
theorem localMetricFlatBasis_isInvertible {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    (localMetricFlatBasis (I := I) e b g x).IsInvertible := by
  haveI : CompleteSpace (E →L[Real] Real) := inferInstance
  let A : E →ₗ[Real] (E →L[Real] Real) :=
    (localMetricFlatBasis (I := I) e b g x).toLinearMap
  have hker : LinearMap.ker A = ⊥ := by
    ext v
    constructor
    · intro hv
      change A v = 0 at hv
      have hself :
          localMetricFlatBasis (I := I) e b g x v v = 0 := by
        exact congrArg (fun L : E →L[Real] Real => L v) hv
      have hinner :
          g.inner x (e.symmL Real x v) (e.symmL Real x v) = 0 := by
        simpa [localMetricFlatBasis_eq_inner (I := I) e b g hx v v] using hself
      by_contra hvne
      have hsymm_ne : e.symmL Real x v ≠ 0 := by
        intro hzero
        have hmap := congrArg (e.continuousLinearMapAt Real x) hzero
        have hcancel :
            e.continuousLinearMapAt Real x (e.symmL Real x v) = v :=
          e.continuousLinearMapAt_symmL (R := Real) hx v
        rw [hcancel] at hmap
        exact hvne (by simpa using hmap)
      exact False.elim ((ne_of_gt (g.pos x (e.symmL Real x v) hsymm_ne)) hinner)
    · intro hv
      have hv0 : v = 0 := by simpa using hv
      simp [A, hv0]
  have hdim :
      Module.finrank Real E = Module.finrank Real (E →L[Real] Real) := by
    calc
      Module.finrank Real E = Module.finrank Real (Module.Dual Real E) :=
        Subspace.dual_finrank_eq.symm
      _ = Module.finrank Real (E →L[Real] Real) :=
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[Real] Real) ≃ₗ[Real] (E →L[Real] Real)).finrank_eq
  let Aequiv : E ≃ₗ[Real] (E →L[Real] Real) :=
    A.linearEquivOfInjective (LinearMap.ker_eq_bot.mp hker) hdim
  let Acle : E ≃L[Real] (E →L[Real] Real) :=
    Aequiv.toContinuousLinearEquiv
  have hA : (Acle : E →L[Real] E →L[Real] Real) =
      localMetricFlatBasis (I := I) e b g x := by
    ext v w
    change Aequiv v w = localMetricFlatBasis (I := I) e b g x v w
    rw [LinearMap.linearEquivOfInjective_apply]
    rfl
  rw [← hA]
  exact ContinuousLinearMap.isInvertible_equiv



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem localMetricFlatBasis_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
      (fun y => localMetricFlatBasis (I := I) e b g y) x := by
  unfold localMetricFlatBasis
  refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
  exact (localMetricCoeff_contMDiffAt (I := I) e b g hx i j).smul contMDiffAt_const



private noncomputable def localInvMetricCoeff {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (k l : ι) (y : M) : Real :=
  b.coord k
    ((ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y))
      (coordCLM (E := E) b l))

omit [CompleteSpace E] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem localInvMetricCoeff_contMDiffAt_of_isInvertible {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (hInv : (localMetricFlatBasis (I := I) e b g x).IsInvertible) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localInvMetricCoeff (I := I) e b g k l y) x := by
  haveI : CompleteSpace E := FiniteDimensional.complete Real E
  let εl : E →L[Real] Real := coordCLM (E := E) b l
  let εk : E →L[Real] Real := coordCLM (E := E) b k
  have hflat :=
    localMetricFlatBasis_contMDiffAt (I := I) e b g hx
  have hinv :
      ContMDiffAt I 𝓘(Real, (E →L[Real] Real) →L[Real] E) ∞
        (fun y : M =>
          ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y)) x := by
    simpa [Function.comp_def] using
      (hInv.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp x hflat
  have happ :
      ContMDiffAt I 𝓘(Real, E) ∞
        (fun y : M =>
          ContinuousLinearMap.inverse (localMetricFlatBasis (I := I) e b g y) εl) x := by
    simpa [εl] using hinv.clm_apply contMDiffAt_const
  simpa [localInvMetricCoeff, εk, εl, coordCLM] using
    (contMDiffAt_const (c := εk)).clm_apply happ

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localInvMetricCoeff_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet) (k l : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localInvMetricCoeff (I := I) e b g k l y) x :=
  localInvMetricCoeff_contMDiffAt_of_isInvertible (I := I) e b g hx
    (localMetricFlatBasis_isInvertible (I := I) e b g hx) k l



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem coordGInvMdiff
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ y)) x := by
  let e := coordinateTrivializationAt (I := I) x₀
  let b := Module.finBasis Real E
  have hxE : x ∈ e.baseSet := by
    simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hx
  have hlocal :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => localInvMetricCoeff (I := I) e b g k l y) x :=
    (localInvMetricCoeff_contMDiffAt (I := I) e b g hxE k l).mdifferentiableAt
      (by simp)
  have heq :
      (fun y : M =>
        inverseMetricFlatModelInChart_component (I := I) g x₀ k l
          (extChartAt I x₀ y))
        =ᶠ[nhds x]
      fun y : M => localInvMetricCoeff (I := I) e b g k l y := by
    filter_upwards [e.open_baseSet.mem_nhds hxE] with y hy
    have hyCoord : y ∈ coordinateFrameSet (I := I) x₀ := by
      simpa [e, coordinateFrameSet, coordinateTrivializationAt] using hy
    have hflat :
        metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ y) =
          localMetricFlatBasis (I := I) e b g y := by
      ext v w
      rw [flatChart_apply (I := I) g x₀ hyCoord v w]
      rw [localMetricFlatBasis_eq_inner (I := I) e b g hy v w]
    unfold inverseMetricFlatModelInChart_component localInvMetricCoeff
    rw [hflat]
    simp [e, b, coordCLM]
  exact hlocal.congr_of_eventuallyEq heq

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem localMetricFlatBasis_eq_dual_sum {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    localMetricFlatBasis (I := I) e b g x v =
      ∑ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) • coordCLM (E := E) b l := by
  ext w
  calc
    localMetricFlatBasis (I := I) e b g x v w
        = localMetricFlatBasis (I := I) e b g x v
            (∑ l : ι, b.coord l w • b l) := by
          rw [show (∑ l : ι, b.coord l w • b l) = w by
            exact b.sum_repr w]
    _ = ∑ l : ι,
          localMetricFlatBasis (I := I) e b g x v (b l) *
            b.coord l w := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro l _
          simp [smul_eq_mul, mul_comm]
    _ = (∑ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) • coordCLM (E := E) b l) w := by
          simp [coordCLM, smul_eq_mul]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
private theorem basis_coord_eq_sum_localInvMetric_flat {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (v : E) :
    b.coord k v =
      ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          localMetricFlatBasis (I := I) e b g x v (b l) := by
  let A := localMetricFlatBasis (I := I) e b g x
  have hInv := localMetricFlatBasis_isInvertible (I := I) e b g hx
  calc
    b.coord k v = b.coord k (A.inverse (A v)) := by
      rw [hInv.inverse_apply_self]
    _ = b.coord k
        (A.inverse
          (∑ l : ι, A v (b l) • coordCLM (E := E) b l)) := by
          rw [← localMetricFlatBasis_eq_dual_sum (I := I) e b g x v]
    _ = ∑ l : ι, A v (b l) *
          b.coord k (A.inverse (coordCLM (E := E) b l)) := by
          simp [map_sum, map_smul, smul_eq_mul]
    _ = ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          localMetricFlatBasis (I := I) e b g x v (b l) := by
          apply Finset.sum_congr rfl
          intro l _
          simp [A, localInvMetricCoeff, mul_comm]

omit [SigmaCompactSpace M] [T2Space M] in
omit [CompleteSpace E] in
private theorem localFrame_coeff_eq_sum_localInvMetric_inner {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (k : ι) (V : TangentSpace I x) :
    e.localFrame_coeff I b k x V =
      ∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x *
          g.inner x (e.localFrame b l x) V := by
  let v : E := e.continuousLinearMapAt Real x V
  have hcoeff :
      e.localFrame_coeff I b k x V = b.coord k v := by
    classical
    let σ : (y : M) → TangentSpace I y := fun y => if h : x = y then h ▸ V else 0
    have hσx : σ x = V := by
      simp [σ]
    have hσ := Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
      (𝕜 := Real) (F := E) (V := (TangentSpace I : M → Type _)) (I := I)
      (e := e) (b := b) hx σ k
    rw [hσx] at hσ
    rw [hσ]
    simp [v, Bundle.Trivialization.basisAt, Bundle.Trivialization.continuousLinearMapAt_apply,
      e.coe_linearMapAt_of_mem hx]
  have hflat :
      ∀ l : ι,
        localMetricFlatBasis (I := I) e b g x v (b l) =
          g.inner x V (e.localFrame b l x) := by
    intro l
    have hv : e.symmL Real x v = V := by
      exact e.symmL_continuousLinearMapAt (R := Real) hx V
    have hl : e.symmL Real x (b l) = e.localFrame b l x := by
      rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
      simp [Bundle.Trivialization.basisAt]
    rw [localMetricFlatBasis_eq_inner (I := I) e b g hx v (b l), hv, hl]
  rw [hcoeff, basis_coord_eq_sum_localInvMetric_flat (I := I) e b g hx]
  apply Finset.sum_congr rfl
  intro l _
  rw [hflat l, g.symm x V (e.localFrame b l x)]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem lc_christoffel_eq_koszul_sum {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    e.localFrame_coeff I b k x
        ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) x)
          (e.localFrame b i x)) =
      (1 / 2 : Real) *
        ∑ l : ι,
          localInvMetricCoeff (I := I) e b g k l x *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
  let A : TangentSpace I x :=
    (leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) x)
      (e.localFrame b i x)
  have hcoeff := localFrame_coeff_eq_sum_localInvMetric_inner
    (I := I) e b g hx k A
  have hinner :
      ∀ l : ι,
        g.inner x (e.localFrame b l x) A =
          (1 / 2 : Real) *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
    intro l
    have hi := (localFrame_contMDiffAt (I := I) e b hx i).mdifferentiableAt (by simp)
    have hj := (localFrame_contMDiffAt (I := I) e b hx j).mdifferentiableAt (by simp)
    have hl := (localFrame_contMDiffAt (I := I) e b hx l).mdifferentiableAt (by simp)
    have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      (I := I) g (e.localFrame b i) (e.localFrame b j)
      (e.localFrame b l) x hi hj hl
    calc
      g.inner x (e.localFrame b l x) A = g.inner x A (e.localFrame b l x) := by
        exact g.symm x (e.localFrame b l x) A
      _ = (1 / 2 : Real) *
          koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
            (e.localFrame b l) x := by
          simpa [A] using hKos
  rw [hcoeff]
  calc
    (∑ l : ι,
        localInvMetricCoeff (I := I) e b g k l x * g.inner x (e.localFrame b l x) A)
        = ∑ l : ι,
            localInvMetricCoeff (I := I) e b g k l x *
              ((1 / 2 : Real) *
                koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                  (e.localFrame b l) x) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hinner l]
    _ = (1 / 2 : Real) *
        ∑ l : ι,
          localInvMetricCoeff (I := I) e b g k l x *
            koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
              (e.localFrame b l) x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring

omit [SigmaCompactSpace M] [T2Space M] in
theorem lc_christoffel_contMDiffAt {ι : Type*} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    (g : SmoothRiemannianMetric I M) {x : M} (hx : x ∈ e.baseSet)
    (i j k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) y)
            (e.localFrame b i y))) x := by
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M =>
          (1 / 2 : Real) *
            ∑ l : ι,
              localInvMetricCoeff (I := I) e b g k l y *
                koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                  (e.localFrame b l) y) x := by
    refine contMDiffAt_const.mul (ContMDiffAt.sum fun l _ => ?_)
    exact (localInvMetricCoeff_contMDiffAt (I := I) e b g hx k l).mul
      (koszulScalar_localFrame_contMDiffAt (I := I) e b g hx i j l)
  have heq :
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((leviCivitaConnectionOfMetric (I := I) g (e.localFrame b j) y)
            (e.localFrame b i y))) =ᶠ[𝓝 x]
      fun y : M =>
        (1 / 2 : Real) *
          ∑ l : ι,
            localInvMetricCoeff (I := I) e b g k l y *
              koszulScalar (I := I) g (e.localFrame b i) (e.localFrame b j)
                (e.localFrame b l) y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact lc_christoffel_eq_koszul_sum (I := I) e b g hy i j k
  exact hRhs.congr_of_eventuallyEq heq

end DifferentialGeometry.Integral.Connection
