import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import Mathlib.Analysis.Calculus.Deriv.Slope


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 2400000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section NormedLinearizedKoszulCovector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def ccTensorRetagMetric (g' : SmoothRiemannianMetric I M) {g : SmoothRiemannianMetric I M}
    (S : SmoothCcTensor g 0 2) : SmoothCcTensor g' 0 2 :=
  { toSection := S.toSection
    hasCompactSupport := S.hasCompactSupport }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_ccTensorRetagMetric (g' : SmoothRiemannianMetric I M)
    {g : SmoothRiemannianMetric I M} (S : SmoothCcTensor g 0 2) (b : M)
    (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g' (ccTensorRetagMetric (I := I) g' S) b u w =
      smoothCcTensorBilinForm (I := I) g S b u w := rfl

def linearizedKoszulCovec (g' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g' 0 2)
    (x : M) (u ζ : TangentSpace I x) : TangentSpace I x →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    (((unitModel (I := I) (M := M) g' 3
          (covGrad (I := I) (M := M) g' 0 2 S) x).toContinuousLinearMap ![ζ, u, 0] 2).toLinearMap
      + ((unitModel (I := I) (M := M) g' 3
          (covGrad (I := I) (M := M) g' 0 2 S) x).toContinuousLinearMap ![u, ζ, 0] 2).toLinearMap
      - ((unitModel (I := I) (M := M) g' 3
          (covGrad (I := I) (M := M) g' 0 2 S) x).toContinuousLinearMap ![0, ζ, u] 0).toLinearMap)

private lemma vec3_update_zero {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 0 z = ![z, b, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_update_one {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 1 z = ![a, z, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_update_two {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 2 z = ![a, b, z] := by
  funext k
  fin_cases k <;> simp [Function.update]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma linearizedKoszulCovec_apply (g' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g' 0 2)
    (x : M) (u ζ z : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x u ζ z =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x ![ζ, u, z]
          + unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x ![u, ζ, z]
          - unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x ![z, ζ, u]) := by
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : ((G.toContinuousLinearMap ![ζ, u, 0] 2).toLinearMap) z =
      G ![ζ, u, z] := by
    change G (Function.update ![ζ, u, 0] 2 z) = G ![ζ, u, z]
    rw [vec3_update_two]
  have h2 : ((G.toContinuousLinearMap ![u, ζ, 0] 2).toLinearMap) z =
      G ![u, ζ, z] := by
    change G (Function.update ![u, ζ, 0] 2 z) = G ![u, ζ, z]
    rw [vec3_update_two]
  have h3 : ((G.toContinuousLinearMap ![0, ζ, u] 0).toLinearMap) z =
      G ![z, ζ, u] := by
    change G (Function.update ![0, ζ, u] 0 z) = G ![z, ζ, u]
    rw [vec3_update_zero]
  change ((1 / 2 : ℝ) •
      ((G.toContinuousLinearMap ![ζ, u, 0] 2).toLinearMap
        + (G.toContinuousLinearMap ![u, ζ, 0] 2).toLinearMap
        - (G.toContinuousLinearMap ![0, ζ, u] 0).toLinearMap)) z = _
  rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, h1, h2, h3]
  rw [smul_eq_mul]

end NormedLinearizedKoszulCovector

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_linearizedKoszulCovec_fst (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (ζ z : TangentSpace I x) :
    Continuous (fun u : TangentSpace I x =>
      linearizedKoszulCovec (I := I) g' S x u ζ z) := by
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have heq : (fun u : TangentSpace I x => linearizedKoszulCovec (I := I) g' S x u ζ z) =
      fun u : TangentSpace I x => (1 / 2 : ℝ) *
        ((G.toContinuousLinearMap ![ζ, ζ, z] 1) u
          + (G.toContinuousLinearMap ![ζ, ζ, z] 0) u
          - (G.toContinuousLinearMap ![z, ζ, ζ] 2) u) := by
    funext u
    rw [linearizedKoszulCovec_apply]
    have e1 : (G.toContinuousLinearMap ![ζ, ζ, z] 1) u = G ![ζ, u, z] := by
      change G (Function.update ![ζ, ζ, z] 1 u) = _
      rw [vec3_update_one]
    have e2 : (G.toContinuousLinearMap ![ζ, ζ, z] 0) u = G ![u, ζ, z] := by
      change G (Function.update ![ζ, ζ, z] 0 u) = _
      rw [vec3_update_zero]
    have e3 : (G.toContinuousLinearMap ![z, ζ, ζ] 2) u = G ![z, ζ, u] := by
      change G (Function.update ![z, ζ, ζ] 2 u) = _
      rw [vec3_update_two]
    rw [← e1, ← e2, ← e3]
  rw [heq]
  exact continuous_const.mul
    (((G.toContinuousLinearMap ![ζ, ζ, z] 1).continuous.add
      (G.toContinuousLinearMap ![ζ, ζ, z] 0).continuous).sub
      (G.toContinuousLinearMap ![z, ζ, ζ] 2).continuous)

def linearizedConnSharp (g' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g' 0 2)
    (x : M) (u ζ : TangentSpace I x) : TangentSpace I x :=
  DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g' x (linearizedKoszulCovec (I := I) g' S x u ζ)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inner_linearizedConnSharp (g' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g' 0 2)
    (x : M) (u ζ z : TangentSpace I x) :
    g'.inner x (linearizedConnSharp (I := I) g' S x u ζ) z =
      linearizedKoszulCovec (I := I) g' S x u ζ z :=
  DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp (I := I) g' x (linearizedKoszulCovec (I := I) g' S x u ζ) z

def covDerivLinearizedConn (g' : SmoothRiemannianMetric I M) (S : SmoothCcTensor g' 0 2)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g').toFun
      (fun b : M => linearizedConnSharp (I := I) g' S b (Z b) (Y b)) x (X x)
    - linearizedConnSharp (I := I) g' S x (Z x)
        (covApply (LeviCivita (I := I) g') X Y x)
    - linearizedConnSharp (I := I) g' S x
        (covApply (LeviCivita (I := I) g') X Z x) (Y x)

section NormedRealizedVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)

def realizedVelocityCc
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s₀ : ℝ) : SmoothCcTensor (realizedFam (I := I) g₀ T T' hδ hδ' s₀) 0 2 :=
  ccTensorRetagMetric (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))

end NormedRealizedVelocity

variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)

omit [BoundarylessManifold I M] in
lemma realizedVelocityCc_bilin
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s₀ : ℝ) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u w =
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ).inner b u w
        - (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ').inner b u w := by
  have htrans : smoothCcTensorBilinForm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u w =
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) b u w := rfl
  have hsub : ∀ (p q : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ (T - T') b p q =
        smoothCcTensorBilinForm (I := I) g₀ T b p q - smoothCcTensorBilinForm (I := I) g₀ T' b p q := by
    intro p q
    rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
    have hmulti : (ccTensorMultilinear (I := I) g₀ (T - T') b : Tensor0SSpace 2 I b) =
        (ccTensorMultilinear (I := I) g₀ T b : Tensor0SSpace 2 I b)
          - (ccTensorMultilinear (I := I) g₀ T' b : Tensor0SSpace 2 I b) := by
      unfold ccTensorMultilinear
      rw [SmoothCcTensor.toSection_sub]
      rfl
    have hmodel : ccTensorModel (I := I) g₀ (T - T') b =
        ccTensorModel (I := I) g₀ T b - ccTensorModel (I := I) g₀ T' b := by
      unfold ccTensorModel
      rw [hmulti, Tensor0SSpace.toModel_sub]
    rw [hmodel, ContinuousMultilinearMap.sub_apply]
  rw [htrans, ccTensorBilin_symmS (I := I) (M := M) g₀ (T - T') b u w,
    tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner]
  simp only [ccTensorBilinSymm_apply]
  rw [hsub u w, hsub w u]
  ring

lemma one_mem_realizedSmallSet {δ δ' : ℝ} (hδ_lt : δ < 1) :
    (1 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') := by
  change |1 - (1 : ℝ)| * δ' + |(1 : ℝ)| * δ < 1
  rw [sub_self, abs_zero, abs_one, zero_mul, one_mul, zero_add]
  exact hδ_lt

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
lemma realizedFam_inner_affine
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ s : ℝ} (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (b : M) (u w : TangentSpace I b) :
    (realizedFam (I := I) g₀ T T' hδ hδ' s).inner b u w =
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀).inner b u w
        + (s - s₀) *
          ((tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ).inner b u w
            - (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ').inner b u w) := by
  rw [realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs₀,
    ccTensorBilinSymm_convexPerturbation, ccTensorBilinSymm_convexPerturbation,
    tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner]
  ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma metricDiffCovDeriv_realizedFam_affine
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ s : ℝ} (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    metricDiffCovDeriv (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      (s - s₀) *
        (metricDiffCovDeriv (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
            (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (fun b => X b) (fun b => Y b) (fun b => Z b) x
          - metricDiffCovDeriv (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
              (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
              (fun b => X b) (fun b => Y b) (fun b => Z b) x) := by
  classical
  set gsf := realizedFam (I := I) g₀ T T' hδ hδ' s with hgsf
  set gs0 := realizedFam (I := I) g₀ T T' hδ hδ' s₀ with hgs0
  set gT := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hgT
  set gT' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hgT'
  set F0 : M → ℝ := fun b : M => gs0.inner b (Y b) (Z b) with hF0
  set FT : M → ℝ := fun b : M => gT.inner b (Y b) (Z b) with hFT
  set FT' : M → ℝ := fun b : M => gT'.inner b (Y b) (Z b) with hFT'
  have hd0 : MDifferentiableAt I 𝓘(ℝ) F0 x :=
    (contMDiff_g_inner_of_smooth_sections (I := I) (M := M) gs0 Y Z x).mdifferentiableAt
      (by simp)
  have hdT : MDifferentiableAt I 𝓘(ℝ) FT x :=
    (contMDiff_g_inner_of_smooth_sections (I := I) (M := M) gT Y Z x).mdifferentiableAt
      (by simp)
  have hdT' : MDifferentiableAt I 𝓘(ℝ) FT' x :=
    (contMDiff_g_inner_of_smooth_sections (I := I) (M := M) gT' Y Z x).mdifferentiableAt
      (by simp)
  have hdSub := hdT.sub hdT'
  have hdSmul := hdSub.const_smul (s - s₀)
  have hfun : (fun b : M => gsf.inner b (Y b) (Z b)) = F0 + (s - s₀) • (FT - FT') := by
    funext b
    have h := realizedFam_inner_affine (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀ hs b (Y b) (Z b)
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hF0, hFT, hFT']
    exact h
  have hval : ∀ (p q : TangentSpace I x),
      gsf.inner x p q = gs0.inner x p q + (s - s₀) * (gT.inner x p q - gT'.inner x p q) :=
    fun p q => realizedFam_inner_affine (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀ hs x p q
  have hmfapp : directionalDeriv (I := I) (fun b : M => gsf.inner b (Y b) (Z b)) x (X x) =
      directionalDeriv (I := I) F0 x (X x)
        + (s - s₀) *
          (directionalDeriv (I := I) FT x (X x) - directionalDeriv (I := I) FT' x (X x)) := by
    simp only [directionalDeriv_eq]
    rw [hfun, mfderiv_add hd0 hdSmul, const_smul_mfderiv hdSub, mfderiv_sub hdT hdT']
    rfl
  simp only [metricDiffCovDeriv, metricCovDeriv]
  rw [show (fun b : M => gs0.inner b (Y b) (Z b)) = F0 from hF0.symm,
    show (fun b : M => gT.inner b (Y b) (Z b)) = FT from hFT.symm,
    show (fun b : M => gT'.inner b (Y b) (Z b)) = FT' from hFT'.symm]
  rw [hmfapp]
  rw [hval ((LeviCivita (I := I) gs0).toFun (fun b => Y b) x (X x)) (Z x),
    hval (Y x) ((LeviCivita (I := I) gs0).toFun (fun b => Z b) x (X x))]
  ring

private lemma connDiff_realizedFam_inner_koszul
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ s : ℝ} (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    2 * (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x (Y x) (X x)) (Z x) =
      (s - s₀) *
        (2 * linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x (Y x) (X x) (Z x)) := by
  classical
  have hbil : ∀ (b : M) (u' w' : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u' w' =
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ).inner b u' w'
          - (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ').inner b u' w' :=
    fun b u' w' => realizedVelocityCc_bilin (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s₀ b u' w'
  have hUM : ∀ (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      unitModel (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) 3
          (covGrad (I := I) (M := M) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) 0 2
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀)) x ![A x, B x, C x] =
        metricDiffCovDeriv (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
            (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (fun b => A b) (fun b => B b) (fun b => C b) x
          - metricDiffCovDeriv (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
              (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
              (fun b => A b) (fun b => B b) (fun b => C b) x := by
    intro A B C
    have h := covGrad02_unitModel_eval_eq_metricDiffCovDeriv' (I := I) (M := M)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
      (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) hbil A B C x
    exact h
  have hkos := connDiff_koszul_metricDiff (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
    (X := fun b => X b) (Y := fun b => Y b) (Z := fun b => Z b) (x := x)
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt
  rw [hkos]
  rw [metricDiffCovDeriv_realizedFam_affine (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀ hs X Y Z x,
    metricDiffCovDeriv_realizedFam_affine (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀ hs Y X Z x,
    metricDiffCovDeriv_realizedFam_affine (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀ hs Z X Y x]
  rw [linearizedKoszulCovec_apply]
  rw [← hUM X Y Z, ← hUM Y X Z, ← hUM Z X Y]
  ring

theorem connDiff_realizedFam_eq_smul_sharp
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ s : ℝ} (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (b : M) (u ζ : TangentSpace I b) :
    PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b u ζ =
      (s - s₀) •
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u ζ) := by
  classical
  refine SmoothRiemannianMetric.eq_of_inner_eq (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (fun z => ?_)
  set Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) b ζ, smoothExtensionTangent_contMDiff (I := I) b ζ⟩
    with hXf
  set Yf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) b u, smoothExtensionTangent_contMDiff (I := I) b u⟩
    with hYf
  set Zf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) b z, smoothExtensionTangent_contMDiff (I := I) b z⟩
    with hZf
  have hXfb : (Xf b : TangentSpace I b) = ζ := smoothExtensionTangent_eq (I := I) b ζ
  have hYfb : (Yf b : TangentSpace I b) = u := smoothExtensionTangent_eq (I := I) b u
  have hZfb : (Zf b : TangentSpace I b) = z := smoothExtensionTangent_eq (I := I) b z
  have hkos := connDiff_realizedFam_inner_koszul (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    hs₀ hs Xf Yf Zf b
  rw [hXfb, hYfb, hZfb] at hkos
  have hR : (realizedFam (I := I) g₀ T T' hδ hδ' s).inner b
      ((s - s₀) •
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u ζ)) z =
      (s - s₀) *
        linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u ζ z := by
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp]
  rw [hR]
  linarith [hkos]

private lemma linearizedKoszulCovec_eq_endpoint_flat
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    (b : M) (u ζ : TangentSpace I b) :
    linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u ζ =
      (1 - s₀)⁻¹ •
        ((realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
            (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b u ζ)).toLinearMap := by
  classical
  have h1mem : (1 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    one_mem_realizedSmallSet hδ_lt
  have hs₀mem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs₀)
  have hne : (1 : ℝ) - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs₀.2)
  ext z
  have hkey := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    hs₀mem h1mem b u ζ
  have hinner : (realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b u ζ) z =
      (1 - s₀) *
        linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b u ζ z := by
    rw [hkey, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp]
  rw [LinearMap.smul_apply]
  rw [show (((realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b u ζ)).toLinearMap) z =
      (realizedFam (I := I) g₀ T T' hδ hδ' 1).inner b
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
          (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b u ζ) z from rfl]
  rw [hinner, smul_eq_mul]
  field_simp

private lemma linearizedKoszulCovec_basis_contMDiffOn
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  have hΛ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
          (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' 1) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
      Z.contMDiff Y.contMDiff
  have hflat : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) b
        (g0FlatCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1) b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
            (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)) hΛ
  set Kf : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun z : M => Tensor0SSpace 1 I z)⟯ :=
    ⟨fun b : M => g0FlatCLM (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1) b
      (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' 1)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b)), hflat⟩ with hKf
  have hbase := cotangentSection_chartComponent_contMDiffOn (I := I) Kf α j
  have heq : ∀ b ∈ (chartAt H α).source,
      linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b) =
        (1 - s₀)⁻¹ *
          Tensor0SSpace.toModel (Kf b)
            (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b) := by
    intro b _
    rw [linearizedKoszulCovec_eq_endpoint_flat (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀
      b (Z b) (Y b)]
    rw [LinearMap.smul_apply, smul_eq_mul]
    congr 1
  have hcomb : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (1 - s₀)⁻¹ *
        Tensor0SSpace.toModel (Kf b)
          (fun _ : Fin 1 => chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source :=
    contMDiffOn_const.mul hbase
  exact hcomb.congr heq

private def linearizedKoszulSharpField
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s₀ s : ℝ) (Y Z : Π b : M, TangentSpace I b) : Π b : M, TangentSpace I b :=
  fun b =>
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) b
      (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b))

private lemma sharpPsiField_contMDiff
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) (s : ℝ)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s (fun b' => Y b') (fun b' => Z b') b)) := by
  apply metricSharp_contMDiff_total (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (cv := fun b : M =>
      linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b))
  intro α j
  exact linearizedKoszulCovec_basis_contMDiffOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
    hs₀ Y Z α j

private lemma sharpPsiField_jointContMDiffOn
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ p.2 (fun b' => Y b') (fun b' => Z b') p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun α i j => realizedFam_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ =>
          linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) p.1 (Z p.1) (Y p.1)
            (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro α j
    exact (linearizedKoszulCovec_basis_contMDiffOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      hs₀ Y Z α j).comp contMDiffOn_fst (fun p hp => hp.1)
  exact metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s : ℝ => realizedFam (I := I) g₀ T T' hδ hδ' s)
    (cv := fun _ : ℝ => fun b : M =>
      linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) b (Z b) (Y b))
    realizedSmallSet_isOpen hinv hcv

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma continuousAt_leviCivita_toFun_slice
    (g' : SmoothRiemannianMetric I M) {S : Set ℝ} (hSopen : IsOpen S) {s₀ : ℝ} (hs₀S : s₀ ∈ S)
    (Φ : ∀ p : M × ℝ, TangentSpace I p.1)
    (hΦ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Φ p))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (e : TangentSpace I x) :
    ContinuousAt (fun s : ℝ =>
      (LeviCivita (I := I) g').toFun (fun b : M => Φ (b, s)) x e) s₀ := by
  classical
  set xhat : E := extChartAt I x x with hxhat
  set F : ℝ × E → E := fun q =>
    chartE_section_repr (I := I) x (fun b : M => Φ (b, q.1)) ((extChartAt I x).symm q.2)
    with hF
  have hgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hxsrc : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have h_projx : (extChartAt I x).symm xhat = x := (extChartAt I x).left_inv hxsrc
  have hxhatint : xhat ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x
      ((extChartAt I x).map_source hxsrc)
  set U : Set (ℝ × E) := S ×ˢ interior (extChartAt I x).target with hU
  have hUopen : IsOpen U := hSopen.prod isOpen_interior
  have hq₀U : ((s₀, xhat) : ℝ × E) ∈ U := ⟨hs₀S, hxhatint⟩
  have hσMD : ∀ {s : ℝ}, s ∈ S → MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Φ (b, s))) x := by
    intro s hs
    have h2 : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Φ p))
        (x, s) :=
      (hΦ (x, s) ⟨Set.mem_univ x, hs⟩).contMDiffAt
        ((isOpen_univ.prod hSopen).mem_nhds ⟨Set.mem_univ x, hs⟩)
    have hmap : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun b : M => ((b, s) : M × ℝ)) x :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact ((h2.comp x hmap).mdifferentiableAt (by simp))
  have hJ : ContDiffAt ℝ ∞ F (s₀, xhat) := by
    have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × E => (((extChartAt I x).symm q.2), q.1)) U := by
      refine ContMDiffOn.prodMk ?_ contMDiffOn_fst
      have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
          (Prod.snd : ℝ × E → E) U := contMDiffOn_snd
      have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
          (extChartAt I x).target := contMDiffOn_extChartAt_symm (I := I) x
      have hmaps : Set.MapsTo (Prod.snd : ℝ × E → E) U (extChartAt I x).target :=
        fun q hq => interior_subset hq.2
      exact hsymm.comp hsnd hmaps
    have hcomp := hΦ.comp hmap
      (fun q hq => ⟨Set.mem_univ _, hq.1⟩)
    have hcompAt : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × E => TotalSpace.mk' E (E := fun z : M => TangentSpace I z)
          ((extChartAt I x).symm q.2) (Φ (((extChartAt I x).symm q.2), q.1)))
        (s₀, xhat) :=
      (hcomp (s₀, xhat) hq₀U).contMDiffAt (hUopen.mem_nhds hq₀U)
    rw [Bundle.contMDiffAt_totalSpace] at hcompAt
    have hfib : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × E =>
          (trivializationAt E (TangentSpace I) ((extChartAt I x).symm xhat)
            (TotalSpace.mk' E (E := fun z : M => TangentSpace I z)
              ((extChartAt I x).symm q.2) (Φ (((extChartAt I x).symm q.2), q.1)))).2)
        (s₀, xhat) := hcompAt.2
    rw [h_projx] at hfib
    have hfib' : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ F (s₀, xhat) := by
      refine hfib.congr_of_eventuallyEq ?_
      filter_upwards [hUopen.mem_nhds hq₀U] with q hq
      have hbsrc : (extChartAt I x).symm q.2 ∈ (chartAt H x).source := by
        have : (extChartAt I x).symm q.2 ∈ (extChartAt I x).source :=
          (extChartAt I x).map_target (interior_subset hq.2)
        rw [extChartAt_source_eq_chartAt_source (I := I)] at this
        exact this
      have hbbase : (extChartAt I x).symm q.2 ∈
          (trivializationAt E (TangentSpace I) x).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
        exact hbsrc
      exact chartE_section_repr_eq_trivialization_snd (I := I) x
        (fun b : M => Φ (b, q.1)) hbbase
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hfib'
    exact contMDiffAt_iff_contDiffAt.mp hfib'
  set u₀ : E := trivToE (I := I) x x e with hu₀
  have hkey : ∀ᶠ s in 𝓝 s₀,
      (LeviCivita (I := I) g').toFun (fun b : M => Φ (b, s)) x e =
        trivFromE (I := I) x x
          ((fderiv ℝ (fun y : E => F (s, y)) xhat) u₀
            + christoffelCorrection (I := I) g' x x (F (s, xhat)) e) := by
    filter_upwards [hSopen.mem_nhds hs₀S] with s hs
    rw [LeviCivita_chart_apply (I := I) g' x hgood (hσMD hs) e]
    rw [chartLeviCivita_apply (I := I) g' x (fun b : M => Φ (b, s)) hgood e]
    have hfun_eq : (chartE_section_repr (I := I) x (fun b : M => Φ (b, s)) ∘
        (extChartAt I x).symm) = fun y : E => F (s, y) := rfl
    have hval_eq : chartE_section_repr (I := I) x (fun b : M => Φ (b, s)) x = F (s, xhat) :=
      (congrArg (chartE_section_repr (I := I) x (fun b : M => Φ (b, s))) h_projx).symm
    rw [hfun_eq, hval_eq]
  have hFslice : ContinuousAt (fun s : ℝ => F (s, xhat)) s₀ := by
    have h1 : Filter.Tendsto (fun s : ℝ => ((s, xhat) : ℝ × E)) (𝓝 s₀) (𝓝 ((s₀, xhat) : ℝ × E)) :=
      (continuous_id.prodMk continuous_const).tendsto (s₀ : ℝ)
    exact hJ.continuousAt.tendsto.comp h1
  have hchrisY : Continuous (fun Yv : E => christoffelCorrection (I := I) g' x x Yv e) := by
    have heq : (fun Yv : E => christoffelCorrection (I := I) g' x x Yv e) =
        fun Yv : E =>
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (((chartModelBasis E).repr (trivToE (I := I) x x e)) i *
                  ((chartModelBasis E).repr Yv) j *
                  chartChristoffel (I := I) g' x i j k (extChartAt I x x)) •
                (chartModelBasis E) k := by
      funext Yv
      exact christoffelCorrection_apply (I := I) g' x x Yv e
    rw [heq]
    refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
      continuous_finset_sum _ (fun k _ => ?_)))
    have hcoord : Continuous (fun Yv : E => ((chartModelBasis E).repr Yv) j) :=
      LinearMap.continuous_of_finiteDimensional ((chartModelBasis E).coord j)
    exact (((continuous_const.mul hcoord).mul continuous_const).smul continuous_const)
  have hfd : ContDiffAt ℝ ∞ (fun s : ℝ => fderiv ℝ (fun y : E => F (s, y)) xhat) s₀ := by
    have hf : ContDiffAt ℝ ∞
        (Function.uncurry (fun (s : ℝ) (y : E) => F (s, y)))
        (s₀, (fun _ : ℝ => xhat) s₀) := hJ
    exact ContDiffAt.fderiv hf contDiffAt_const (by simp)
  have hRHS : ContinuousAt (fun s : ℝ =>
      trivFromE (I := I) x x
        ((fderiv ℝ (fun y : E => F (s, y)) xhat) u₀
          + christoffelCorrection (I := I) g' x x (F (s, xhat)) e)) s₀ := by
    have tfd : Filter.Tendsto
        (fun s : ℝ => (fderiv ℝ (fun y : E => F (s, y)) xhat) u₀) (𝓝 s₀)
        (𝓝 ((fderiv ℝ (fun y : E => F (s₀, y)) xhat) u₀)) :=
      ((ContinuousLinearMap.apply ℝ E u₀).continuous.tendsto
        (fderiv ℝ (fun y : E => F (s₀, y)) xhat)).comp hfd.continuousAt.tendsto
    have tch : Filter.Tendsto
        (fun s : ℝ => christoffelCorrection (I := I) g' x x (F (s, xhat)) e) (𝓝 s₀)
        (𝓝 (christoffelCorrection (I := I) g' x x (F (s₀, xhat)) e)) :=
      (hchrisY.tendsto (F (s₀, xhat))).comp hFslice.tendsto
    exact ((trivFromE (I := I) x x).continuous.tendsto _).comp (tfd.add tch)
  exact hRHS.congr (Filter.EventuallyEq.symm hkey)

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma continuousOn_realizedFam_invGram_slice
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun s : ℝ => chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i j)
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := realizedFam_chartInvGramMatrix_jointContMDiffOn_free
    (I := I) g₀ T T' hδ hδ' x i j
  have hmap : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (x, s)) :=
    contMDiff_const.prodMk contMDiff_id
  have hcomp := hjoint.comp hmap.contMDiffOn
    (fun s hs => ⟨mem_chart_source H x, hs⟩)
  exact hcomp.continuousOn

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma metricSharp_realizedFam_eq_invGram_sum
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (α₀ : TangentSpace I x →ₗ[ℝ] ℝ) :
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x α₀ =
      ∑ i : Fin (Module.finrank ℝ E),
        (∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i j *
              α₀ (chartBasisVecFiber (I := I) x j x)) •
          chartBasisVecFiber (I := I) x i x := by
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  have h := metricSharpChartLocal_eq_metricSharp (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) x (fun _ : M => α₀) hxbase
  rw [← h, metricSharpChartLocal]
  rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma tendsto_metricSharp_realizedFam_fixed
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (x : M) (α₀ : TangentSpace I x →ₗ[ℝ] ℝ) :
    Filter.Tendsto
      (fun s : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x α₀)
      (𝓝 s₀)
      (𝓝 (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x α₀)) := by
  have heq : ∀ s : ℝ, DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x α₀ =
      ∑ i : Fin (Module.finrank ℝ E),
        (∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i j *
              α₀ (chartBasisVecFiber (I := I) x j x)) •
          chartBasisVecFiber (I := I) x i x :=
    fun s => metricSharp_realizedFam_eq_invGram_sum (I := I) g₀ T T' hδ hδ' s x α₀
  rw [heq s₀]
  refine Filter.Tendsto.congr (fun s => (heq s).symm) ?_
  refine tendsto_finset_sum _ (fun i _ => ?_)
  refine Filter.Tendsto.smul ?_ tendsto_const_nhds
  refine tendsto_finset_sum _ (fun j _ => ?_)
  have hinv : Filter.Tendsto
      (fun s : ℝ => chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i j)
      (𝓝 s₀)
      (𝓝 (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x x i j)) := by
    have hcont := (continuousOn_realizedFam_invGram_slice (I := I) g₀ T T' hδ hδ' x i j)
    exact (hcont.continuousAt (realizedSmallSet_isOpen.mem_nhds hs₀)).tendsto
  exact hinv.mul tendsto_const_nhds

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma tendsto_metricSharp_realizedFam_varying
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (x : M) {κ : ℝ → TangentSpace I x →ₗ[ℝ] ℝ}
    (hκ : ∀ j : Fin (Module.finrank ℝ E),
      Filter.Tendsto (fun s : ℝ => κ s (chartBasisVecFiber (I := I) x j x)) (𝓝 s₀)
        (𝓝 (κ s₀ (chartBasisVecFiber (I := I) x j x)))) :
    Filter.Tendsto
      (fun s : ℝ => DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x (κ s))
      (𝓝 s₀)
      (𝓝 (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x (κ s₀))) := by
  have heq : ∀ s : ℝ,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x (κ s) =
      ∑ i : Fin (Module.finrank ℝ E),
        (∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i j *
              κ s (chartBasisVecFiber (I := I) x j x)) •
          chartBasisVecFiber (I := I) x i x :=
    fun s => metricSharp_realizedFam_eq_invGram_sum (I := I) g₀ T T' hδ hδ' s x (κ s)
  rw [heq s₀]
  refine Filter.Tendsto.congr (fun s => (heq s).symm) ?_
  refine tendsto_finset_sum _ (fun i _ => ?_)
  refine Filter.Tendsto.smul ?_ tendsto_const_nhds
  refine tendsto_finset_sum _ (fun j _ => ?_)
  have hinv : Filter.Tendsto
      (fun s : ℝ => chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i j)
      (𝓝 s₀)
      (𝓝 (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x x i j)) := by
    have hcont := (continuousOn_realizedFam_invGram_slice (I := I) g₀ T T' hδ hδ' x i j)
    exact (hcont.continuousAt (realizedSmallSet_isOpen.mem_nhds hs₀)).tendsto
  exact hinv.mul (hκ j)

variable (x : M) (v w : TangentSpace I x)

private def covDerivSharp
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s₀ s : ℝ) (X Y Z : Π b : M, TangentSpace I b) : TangentSpace I x :=
  (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)).toFun
      (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s Y Z) x (X x)
    - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x (Z x)
          (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)) X Y x))
    - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
          (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)) X Z x) (Y x))

private def slopeCore
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s₀ s : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (covDerivSharp (I := I) g₀ T T' x hδ hδ' s₀ s
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
        - covDerivSharp (I := I) g₀ T T' x hδ hδ' s₀ s
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x w)
        + (s - s₀) •
            DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
              (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
                (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
                  (smoothExtensionTangent (I := I) x v)
                  (smoothExtensionTangent (I := I) x w) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
        - (s - s₀) •
            DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
              (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
                (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x w) x)
                (smoothExtensionTangent (I := I) x v x))) i

omit [CompactSpace M] in
private lemma realizedRicciPathValue_eq_ricciTensor_realizedFam
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      ricciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x v w := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : max 0 (min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le (zero_le_one) (le_trans (min_le_right s 1) (le_refl 1))) =
        realizedFam (I := I) g₀ T T' hδ hδ' s := by
    refine riemannianMetric_eq_of_inner _ _ (fun b' u' z' => ?_)
    rw [realizedMetricPath_inner, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem,
      hclamp]
  rw [hmetric]

private lemma covDerivConnDiff_realizedFam_eq_smul_covDerivSharp
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      (s - s₀) •
        covDerivSharp (I := I) g₀ T T' x hδ hδ' s₀ s
          (fun b => X b) (fun b => Y b) (fun b => Z b) := by
  classical
  have hs₀mem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs₀)
  have hexpand : covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
      (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)).toFun
          (diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
            (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
            (fun b => Y b) (fun b => Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x (Z x)
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
              (fun b => X b) (fun b => Y b) x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
              (fun b => X b) (fun b => Z b) x) (Y x) := rfl
  rw [hexpand]
  have hdiffSec : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
      (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
      (fun b => Y b) (fun b => Z b) =
      (s - s₀) • linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
        (fun b => Y b) (fun b => Z b) := by
    funext b
    rw [Pi.smul_apply]
    exact connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      hs₀mem hs b (Z b) (Y b)
  rw [hdiffSec]
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s (fun b' => Y b') (fun b' => Z b') b)) x :=
    ((sharpPsiField_contMDiff (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀ s Y Z)
      x).mdifferentiableAt (by simp)
  have hsmul := (LeviCivita (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s₀)).isCovariantDerivativeOnUniv.smul_const
    (σ := linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s (fun b => Y b) (fun b => Z b))
    (x := x) (s - s₀) hσ (Set.mem_univ x)
  rw [hsmul, ContinuousLinearMap.smul_apply]
  rw [connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      hs₀mem hs x (Z x)
      (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
        (fun b => X b) (fun b => Y b) x),
    connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      hs₀mem hs x
      (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
        (fun b => X b) (fun b => Z b) x) (Y x)]
  rw [covDerivSharp]
  module

private lemma pathValue_sub_eq_mul_slopeCore
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s
        - realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s₀ =
      (s - s₀) * slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀ s := by
  classical
  have hs₀Icc : s₀ ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioo hs₀
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs
  rw [realizedRicciPathValue_eq_ricciTensor_realizedFam (I := I) g₀ T T' x v w
      hδ_lt hδ hδ'_lt hδ' hs,
    realizedRicciPathValue_eq_ricciTensor_realizedFam (I := I) g₀ T T' x v w
      hδ_lt hδ hδ'_lt hδ' hs₀Icc]
  rw [ricciTensor_sub_eq_connDiff_palatini (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s₀) (realizedFam (I := I) g₀ T T' hδ hδ' s) x v w]
  rw [slopeCore, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set Bi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hBi
  set Vf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v,
      smoothExtensionTangent_contMDiff (I := I) x v⟩ with hVf
  set Wf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w,
      smoothExtensionTangent_contMDiff (I := I) x w⟩ with hWf
  have hs₀mem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs₀Icc
  have hA : covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
      (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w) x =
      (s - s₀) • covDerivSharp (I := I) g₀ T T' x hδ hδ' s₀ s
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) :=
    covDerivConnDiff_realizedFam_eq_smul_covDerivSharp (I := I) g₀ T T' x
      hδ_lt hδ hδ'_lt hδ' hs₀ hsmem Bi Vf Wf
  have hB : covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
      (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
      (smoothExtensionTangent (I := I) x w) x =
      (s - s₀) • covDerivSharp (I := I) g₀ T T' x hδ hδ' s₀ s
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) :=
    covDerivConnDiff_realizedFam_eq_smul_covDerivSharp (I := I) g₀ T T' x
      hδ_lt hδ hδ'_lt hδ' hs₀ hsmem Vf Bi Wf
  have hQ1 : PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x
      (diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x)
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x) =
      (s - s₀) • ((s - s₀) •
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
            (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w) x)
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) := by
    have h1 : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x =
        (s - s₀) • linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) x :=
      connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        hs₀mem hsmem x (smoothExtensionTangent (I := I) x w x)
        (smoothExtensionTangent (I := I) x v x)
    rw [h1, map_smul, ContinuousLinearMap.smul_apply]
    congr 1
    exact connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      hs₀mem hsmem x
      (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x)
      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
  have hQ2 : PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x
      (diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x)
      (smoothExtensionTangent (I := I) x v x) =
      (s - s₀) • ((s - s₀) •
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
            (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
              (smoothExtensionTangent (I := I) x w) x)
            (smoothExtensionTangent (I := I) x v x))) := by
    have h1 : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x =
        (s - s₀) • linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
          (smoothExtensionTangent (I := I) x w) x :=
      connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        hs₀mem hsmem x (smoothExtensionTangent (I := I) x w x)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
    rw [h1, map_smul, ContinuousLinearMap.smul_apply]
    congr 1
    exact connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      hs₀mem hsmem x
      (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x)
      (smoothExtensionTangent (I := I) x v x)
  rw [hA, hB, hQ1, hQ2]
  rw [show ∀ (A B qa qb : TangentSpace I x),
      ((s - s₀) • A - (s - s₀) • B) + ((s - s₀) • ((s - s₀) • qa) - (s - s₀) • ((s - s₀) • qb))
        = (s - s₀) • (A - B + (s - s₀) • qa - (s - s₀) • qb) from
    fun A B qa qb => by module]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

private lemma slopeCore_tendsto
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    Filter.Tendsto (slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀) (𝓝 s₀)
      (𝓝 (slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀ s₀)) := by
  classical
  have hs₀mem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs₀)
  set Vf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v,
      smoothExtensionTangent_contMDiff (I := I) x v⟩ with hVf
  set Wf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x w,
      smoothExtensionTangent_contMDiff (I := I) x w⟩ with hWf
  have hterm1 : ∀ (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (e : TangentSpace I x),
      Filter.Tendsto (fun s : ℝ =>
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)).toFun
          (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s (fun b => Y b) (fun b => Z b)) x e)
        (𝓝 s₀)
        (𝓝 ((LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)).toFun
          (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s₀ (fun b => Y b) (fun b => Z b)) x e)) := by
    intro Y Z e
    have hC := continuousAt_leviCivita_toFun_slice (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) realizedSmallSet_isOpen hs₀mem
      (fun p : M × ℝ => linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ p.2
        (fun b => Y b) (fun b => Z b) p.1)
      (sharpPsiField_jointContMDiffOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs₀ Y Z)
      x e
    exact hC.tendsto
  have hfixed : ∀ (α₀ : TangentSpace I x →ₗ[ℝ] ℝ),
      Filter.Tendsto (fun s : ℝ =>
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x α₀) (𝓝 s₀)
        (𝓝 (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x α₀)) :=
    fun α₀ => tendsto_metricSharp_realizedFam_fixed (I := I) g₀ T T' hδ hδ' hs₀mem x α₀
  have hcovSharp : ∀ (Xf Yf Zf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      Filter.Tendsto (fun s : ℝ =>
        covDerivSharp (I := I) g₀ T T' x hδ hδ' s₀ s
          (fun b => Xf b) (fun b => Yf b) (fun b => Zf b)) (𝓝 s₀)
        (𝓝 (covDerivSharp (I := I) g₀ T T' x hδ hδ' s₀ s₀
          (fun b => Xf b) (fun b => Yf b) (fun b => Zf b))) := by
    intro Xf Yf Zf
    refine Filter.Tendsto.sub (Filter.Tendsto.sub ?_ ?_) ?_
    · exact hterm1 Yf Zf (Xf x)
    · exact hfixed _
    · exact hfixed _
  have hquad : ∀ (Yf Zf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (e : TangentSpace I x),
      Filter.Tendsto (fun s : ℝ =>
        (s - s₀) •
          DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
              (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
                (fun b => Yf b) (fun b => Zf b) x) e)) (𝓝 s₀)
        (𝓝 ((s₀ - s₀) •
          DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
              (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s₀
                (fun b => Yf b) (fun b => Zf b) x) e))) := by
    intro Yf Zf e
    refine Filter.Tendsto.smul ?_ ?_
    · exact ((continuous_id.sub continuous_const).tendsto s₀)
    · refine tendsto_metricSharp_realizedFam_varying (I := I) g₀ T T' hδ hδ' hs₀mem x
        (κ := fun s : ℝ =>
          linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
            (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x
            (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s
              (fun b => Yf b) (fun b => Zf b) x) e) ?_
      intro j
      have hucont := continuous_linearizedKoszulCovec_fst (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
        (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x e
        (chartBasisVecFiber (I := I) x j x)
      have hΨ : Filter.Tendsto (fun s : ℝ =>
          linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s (fun b => Yf b) (fun b => Zf b) x)
          (𝓝 s₀)
          (𝓝 (linearizedKoszulSharpField (I := I) g₀ T T' hδ hδ' s₀ s₀
            (fun b => Yf b) (fun b => Zf b) x)) :=
        hfixed (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
          (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀) x (Zf x) (Yf x))
      exact (hucont.tendsto _).comp hΨ
  simp only [slopeCore]
  refine tendsto_finset_sum _ (fun i _ => ?_)
  set Bi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hBi
  have hcoord : Continuous (fun u : E => ((chartModelBasis E).repr u) i) :=
    LinearMap.continuous_of_finiteDimensional ((chartModelBasis E).coord i)
  refine (hcoord.tendsto _).comp ?_
  refine Filter.Tendsto.sub (Filter.Tendsto.add (Filter.Tendsto.sub ?_ ?_) ?_) ?_
  · exact hcovSharp Bi Vf Wf
  · exact hcovSharp Vf Bi Wf
  · exact hquad Vf Wf (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
  · exact hquad Bi Wf (smoothExtensionTangent (I := I) x v x)

omit [BoundarylessManifold I M] in
private lemma slopeCore_at_base
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s₀ : ℝ) :
    slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀ s₀ =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀)
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w) x
            - covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀)
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x) i := by
  simp only [slopeCore, sub_self, zero_smul, add_zero, sub_zero]
  rfl

theorem linearizedRicciAt_eq_palatini_covDeriv
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s₀ =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
              (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀)
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w) x
            - covDerivLinearizedConn (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀)
                (realizedVelocityCc (I := I) g₀ T T' hδ hδ' s₀)
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x) i := by
  classical
  have hEv : (fun s : ℝ =>
      slope (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ s)
      =ᶠ[𝓝[≠] s₀] (fun s : ℝ => slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀ s) := by
    have hIoo : ∀ᶠ s in 𝓝 s₀, s ∈ Set.Ioo (0 : ℝ) 1 := isOpen_Ioo.mem_nhds hs₀
    filter_upwards [hIoo.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hsIoo hsne
    have hne : s ≠ s₀ := hsne
    rw [slope_def_field]
    rw [pathValue_sub_eq_mul_slopeCore (I := I) g₀ T T' x v w hδ_lt hδ hδ'_lt hδ' hs₀
      (Set.mem_Icc_of_Ioo hsIoo)]
    rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr hne)]
  have hT : Filter.Tendsto (slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀) (𝓝[≠] s₀)
      (𝓝 (slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀ s₀)) :=
    (slopeCore_tendsto (I := I) g₀ T T' x v w hδ_lt hδ hδ'_lt hδ' hs₀).mono_left
      nhdsWithin_le_nhds
  have hHas : HasDerivAt (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀ s₀) s₀ :=
    hasDerivAt_iff_tendsto_slope.mpr (Filter.Tendsto.congr' hEv.symm hT)
  have hderiv : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s₀ =
      slopeCore (I := I) g₀ T T' x v w hδ hδ' s₀ s₀ := hHas.deriv
  rw [hderiv]
  exact slopeCore_at_base (I := I) g₀ T T' x v w hδ hδ' s₀

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
