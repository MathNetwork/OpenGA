import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedDiffOpProportionalBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldDifferentiatedTowerNormalForm


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

section RankCast


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_heq_congr_lg (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_covGrad_comm_heq_lg (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_lg g r (by omega : (s + 1) + k = s + (k + 1)) ih


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private theorem rfns_toSection_heq_congr_lg (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rfns_iteratedCovGrad_covGrad_comm_lg (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + m) x
        ((iteratedCovGrad g r (s + 1) m (covGrad g r s W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (m + 1)) x
        ((iteratedCovGrad g r s (m + 1) W).toSection x) :=
  rfns_toSection_heq_congr_lg g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq_lg g r s m W) x

private def castRankCc_lg (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ W


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rfns_iteratedCovGrad_castRankCc_lg (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (W : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (b + j) x
        ((iteratedCovGrad g r b j (castRankCc_lg g r h W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (a + j) x
        ((iteratedCovGrad g r a j W).toSection x) := by
  subst h
  rfl

end RankCast

variable (g : SmoothRiemannianMetric I M)
  {X Y : Π b : M, TangentSpace I b}
  (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
  (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))

def diffCurvOp : ∀ (p r : ℕ) (_ : SmoothCcTensor g 0 r), SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => curvatureContraction (I := I) (M := M) g r W hX hY
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p) (diffCurvOp p r W) -
        castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
          (diffCurvOp p (r + 1) (covGrad (I := I) (M := M) g 0 r W))


omit [NeZero (Module.finrank ℝ E)] in
theorem diffCurvOp_zero (r : ℕ) (W : SmoothCcTensor g 0 r) :
    diffCurvOp (I := I) (M := M) g hX hY 0 r W =
      curvatureContraction (I := I) (M := M) g r W hX hY := rfl


omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_diffCurvOp_eq (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p) (diffCurvOp (I := I) (M := M) g hX hY p r W) =
      diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W +
        castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
          (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p) (diffCurvOp (I := I) (M := M) g hX hY p r W) -
      castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
        (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

omit [NeZero (Module.finrank ℝ E)] in
theorem diffCurvOp_isOrderZeroCurvFactor :
    IsPointwiseLinearLocalOperator (I := I) (M := M) g (diffCurvOp (I := I) (M := M) g hX hY) where
  linear := by
    intro r c₁ c₂ W₁ W₂ x
    rw [show (diffCurvOp (I := I) (M := M) g hX hY 0 r (c₁ • W₁ + c₂ • W₂)).toSection x =
          (curvatureContraction (I := I) (M := M) g r (c₁ • W₁ + c₂ • W₂) hX hY).toSection x from rfl,
      show (diffCurvOp (I := I) (M := M) g hX hY 0 r W₁).toSection x =
          (curvatureContraction (I := I) (M := M) g r W₁ hX hY).toSection x from rfl,
      show (diffCurvOp (I := I) (M := M) g hX hY 0 r W₂).toSection x =
          (curvatureContraction (I := I) (M := M) g r W₂ hX hY).toSection x from rfl,
      curvatureContraction_toSection_apply (I := I) (M := M) g r (c₁ • W₁ + c₂ • W₂) hX hY x,
      curvatureContraction_toSection_apply (I := I) (M := M) g r W₁ hX hY x,
      curvatureContraction_toSection_apply (I := I) (M := M) g r W₂ hX hY x]
    rw [show (c₁ • W₁ + c₂ • W₂).toSection x = c₁ • W₁.toSection x + c₂ • W₂.toSection x from by
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
        SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]]
    rw [map_add, map_smul, map_smul]
  local' := by
    intro r W₁ W₂ x hx
    rw [show (diffCurvOp (I := I) (M := M) g hX hY 0 r W₁).toSection x =
          (curvatureContraction (I := I) (M := M) g r W₁ hX hY).toSection x from rfl,
      show (diffCurvOp (I := I) (M := M) g hX hY 0 r W₂).toSection x =
          (curvatureContraction (I := I) (M := M) g r W₂ hX hY).toSection x from rfl,
      curvatureContraction_toSection_apply (I := I) (M := M) g r W₁ hX hY x,
      curvatureContraction_toSection_apply (I := I) (M := M) g r W₂ hX hY x, hx]

set_option backward.isDefEq.respectTransparency false in

noncomputable def diffCurvPhi0Fib (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (r : ℕ) (x : M) : TensorRSSpace r r I x :=
  (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace r I x from
    riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) x (X x) (Y x) :
    TensorRSSpace r r I x)

set_option backward.isDefEq.respectTransparency false in

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem diffCurvPhi0Fib_contMDiff (g : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (r : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r r ℝ E)
        (E := fun z : M => TensorRSSpace r r I z)
        x (diffCurvPhi0Fib (I := I) (M := M) g X Y r x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel r ℝ E) (V₂ := fun x : M => Tensor0SSpace r I x)
    (φ := fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace r I x from
      diffCurvPhi0Fib (I := I) (M := M) g X Y r x))
  intro Z
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
      (E := fun z : M => Tensor0SSpace r I z) x
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace r I x from
        diffCurvPhi0Fib (I := I) (M := M) g X Y r x) (Z x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
      (E := fun z : M => Tensor0SSpace r I z) x
      (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Y b) (fun b => Z b) x)) := by
    funext x
    rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace r I x from
        diffCurvPhi0Fib (I := I) (M := M) g X Y r x) =
      riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
        x (X x) (Y x) from rfl]
    rw [riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
      hX hY Z.contMDiff]
  rw [heq]
  exact riemannSec_contMDiff
    (cov := Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
    hX hY Z.contMDiff

set_option backward.isDefEq.respectTransparency false in

noncomputable def diffCurvPhi0 (g : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (r : ℕ) : SmoothCcTensor g r r where
  toSection :=
    { toFun := fun x : M => diffCurvPhi0Fib (I := I) (M := M) g X Y r x
      contMDiff_toFun := diffCurvPhi0Fib_contMDiff (I := I) (M := M) g hX hY r }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem diffCurvOp_zero_eq_appCc (g : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (r : ℕ) (W : SmoothCcTensor g 0 r) :
    diffCurvOp (I := I) (M := M) g hX hY 0 r W =
      operatorFieldApply (I := I) (M := M) g r r (diffCurvPhi0 (I := I) (M := M) g hX hY r) W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x

  apply ContinuousLinearMap.ext
  intro d

  change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
      (diffCurvOp (I := I) (M := M) g hX hY 0 r W).toSection x) d =
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace r I x from
        riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
          x (X x) (Y x))
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d)
  rw [show (diffCurvOp (I := I) (M := M) g hX hY 0 r W).toSection x =
      (curvatureContraction (I := I) (M := M) g r W hX hY).toSection x from rfl,
    curvatureContraction_toSection_apply (I := I) (M := M) g r W hX hY x]

  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 0 ℝ E) (V := fun y : M => Tensor0SSpace 0 I y) (n := (⊤ : ℕ∞)) x d
  have hWd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace r I y from W.toSection y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff dSec.contMDiff

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        riemannOp (tensorCov (I := I) g 0 r) x (X x) (Y x) (W.toSection x)) d =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        riemannSec (tensorCov (I := I) g 0 r) (fun b => X b) (fun b => Y b)
          (fun b => W.toSection b) x) (dSec x) from by
    rw [riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 r) hX hY W.toSection.contMDiff]
    rw [show d = dSec x from hdSec.symm]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        riemannSec (tensorCov (I := I) g 0 r) (fun b => X b) (fun b => Y b)
          (fun b => W.toSection b) x) (dSec x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Y b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace r I z) (fun b => W.toSection b) (fun b => dSec b)) x -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
          (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun b => X b) (fun b => Y b) (fun b => dSec b) x) from
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M
      (Tensor0SModel 0 ℝ E) (fun z : M => Tensor0SSpace 0 I z)
      (Tensor0SModel r ℝ E) (fun z : M => Tensor0SSpace r I z)
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
      ⟨fun b => X b, hX⟩ ⟨fun b => Y b, hY⟩ W.toSection dSec x]
  rw [show riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Y b) (fun b => dSec b) x = 0 from
    riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g ⟨fun b => X b, hX⟩ ⟨fun b => Y b, hY⟩
      (fun b => dSec b) dSec.contMDiff x]
  rw [map_zero, sub_zero]

  rw [show (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace r I x from
        riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
          x (X x) (Y x))
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Y b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace r I z) (fun b => W.toSection b) (fun b => dSec b)) x from by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d =
        HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
          (V := fun z : M => Tensor0SSpace r I z) (fun b => W.toSection b) (fun b => dSec b) x from by
      rw [HomConnectionGen.pairedSection_apply, show d = dSec x from hdSec.symm]]
    rw [riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)) hX hY
      (show ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) y
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace r I z) (fun b => W.toSection b) (fun b => dSec b) y))
        from hWd_smooth)]]

theorem exists_proportional_diffCurvOp_highOrder :
    ∃ kappaHigh : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappaHigh p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (p + 1)) x
            ((diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W).toSection x) ≤
          kappaHigh p r * ∑ q ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical

  have hcovGrad_op : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r),
      covGrad g 0 (r + p) (diffCurvOp (I := I) (M := M) g hX hY p r W) =
        diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W +
          castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
            (diffCurvOp (I := I) (M := M) g hX hY p (r + 1) (covGrad g 0 r W)) := by
    intro p r W
    rw [covGrad_diffCurvOp_eq (I := I) (M := M) g hX hY p r W]
    rfl

  have hNF : ∀ (p r : ℕ),
      IsIteratedCovGradNormalForm (I := I) (M := M) g (diffCurvOp (I := I) (M := M) g hX hY) p r :=
    fun p => normalForm_of_base (I := I) (M := M) g
      (diffCurvOp (I := I) (M := M) g hX hY) hcovGrad_op
      (fun r => diffCurvPhi0 (I := I) (M := M) g hX hY r)
      (fun r W => diffCurvOp_zero_eq_appCc (I := I) (M := M) g hX hY r W) p

  choose kap hkap_nn hkap using fun p r =>
    exists_jet_bound_of_normalForm (I := I) (M := M) g
      (diffCurvOp (I := I) (M := M) g hX hY) p r (hNF p r)
  refine ⟨fun p r => kap (p + 1) r, fun p r => hkap_nn (p + 1) r, fun p r W x => ?_⟩

  have h := hkap (p + 1) r W x
  rw [show (p + 1) + 1 = p + 2 from rfl] at h
  exact h

theorem exists_continuous_proportional_diffCurvOp (p : ℕ) :
    ∃ Cp : ℕ → M → ℝ, (∀ r, Continuous (Cp r)) ∧ (∀ r x, 0 ≤ Cp r x) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x) ≤
          Cp r x * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical

  have hgnn : ∀ (x : M) (v : TangentSpace I x), 0 ≤ g.inner x v v := by
    intro x v
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g.pos x v hv0).le

  have hgcont : ∀ (Z : Π b : M, TangentSpace I b),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) → Continuous (fun x : M => g.inner x (Z x) (Z x)) := by
    intro Z hZ
    have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b (g.inner b)) :=
      g.contMDiff
    have hgZ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] ℝ) b (g.inner b (Z b))) :=
      ContMDiff.clm_bundle_apply (E₁ := fun y : M => TangentSpace I y)
        (E₂ := fun y : M => TangentSpace I y →L[ℝ] ℝ) (b := fun b : M => b)
        (ϕ := fun b => g.inner b) (v := fun b => Z b) hg hZ
    exact (cotangentCov_pairing_contMDiff hgZ hZ).continuous
  have hXcont : Continuous (fun x : M => g.inner x (X x) (X x)) := hgcont X hX
  have hYcont : Continuous (fun x : M => g.inner x (Y x) (Y x)) := hgcont Y hY
  cases p with
  | zero =>

      choose Ccurv hCcurv_cont hCcurv_nn hCcurv using
        fun r => exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional
          (I := I) (M := M) g r
      refine ⟨fun r x => Ccurv r x * g.inner x (X x) (X x) * g.inner x (Y x) (Y x),
        fun r => ((hCcurv_cont r).mul hXcont).mul hYcont, fun r x => ?_, fun r W x => ?_⟩
      · exact mul_nonneg (mul_nonneg (hCcurv_nn r x) (hgnn x (X x))) (hgnn x (Y x))
      · rw [Finset.sum_range_one]

        rw [show (diffCurvOp (I := I) (M := M) g hX hY 0 r W).toSection x =
            riemannOp (tensorCov (I := I) g 0 r) x (X x) (Y x) (W.toSection x) from
          curvatureContraction_toSection_apply (I := I) (M := M) g r W hX hY x]
        exact hCcurv r x (X x) (Y x) (W.toSection x)
  | succ p' =>

      obtain ⟨kappaHigh, hkappaHigh_nn, hkappaHigh⟩ :=
        exists_proportional_diffCurvOp_highOrder (I := I) (M := M) g hX hY
      refine ⟨fun r _ => kappaHigh p' r, fun r => continuous_const,
        fun r _ => hkappaHigh_nn p' r, fun r W x => ?_⟩
      rw [show (p' + 1) + 1 = p' + 2 from rfl]
      exact hkappaHigh p' r W x


theorem exists_proportional_diffCurvOp :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x) ≤
          kappa p r * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  choose Cp hCp_cont hCp_nn hCp_bound using
    fun p => exists_continuous_proportional_diffCurvOp (I := I) (M := M) g hX hY p
  refine ⟨fun p r => sSup (Set.range (Cp p r)), fun p r => ?_, fun p r W x => ?_⟩
  · have hbdd : BddAbove (Set.range (Cp p r)) := (isCompact_range (hCp_cont p r)).bddAbove
    rcases isEmpty_or_nonempty M with hM | hM
    · simp [Set.range_eq_empty (f := Cp p r)]
    · obtain ⟨x₀⟩ := hM
      exact le_trans (hCp_nn p r x₀) (le_csSup hbdd ⟨x₀, rfl⟩)
  · have hbdd : BddAbove (Set.range (Cp p r)) := (isCompact_range (hCp_cont p r)).bddAbove
    have hCp_le : Cp p r x ≤ sSup (Set.range (Cp p r)) := le_csSup hbdd ⟨x, rfl⟩
    refine (hCp_bound p r W x).trans ?_
    refine mul_le_mul_of_nonneg_right hCp_le ?_
    exact Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _

private lemma sum_range_le_succ_of_nonneg (n : ℕ) (f : ℕ → ℝ) (hf : 0 ≤ f n) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right hf

private lemma sum_range_shift_le (n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ Finset.range (n + 1), 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f (i + 1) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.sum_range_succ' f n]
  exact le_add_of_nonneg_right (hf 0 (Finset.mem_range.2 (Nat.succ_pos n)))

section GridInduction

variable {kappa : ℕ → ℕ → ℝ} (hkappa_nn : ∀ p r, 0 ≤ kappa p r)
  (hkappa : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
        ((diffCurvOp (I := I) (M := M) g hX hY p r W).toSection x) ≤
      kappa p r * ∑ q ∈ Finset.range (p + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x))

include hkappa_nn hkappa in

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_diffCurvOp_grid (j : ℕ) :
    ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + j) x
          ((iteratedCovGrad g 0 (r + p) j
            (diffCurvOp (I := I) (M := M) g hX hY p r W)).toSection x) ≤
        (4 : ℝ) ^ j * gridWindowSum kappa p r j *
          ∑ q ∈ Finset.range (p + j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  induction j with
  | zero =>
      intro p r W x
      have hrhs : (4 : ℝ) ^ 0 * gridWindowSum kappa p r 0 *
            ∑ q ∈ Finset.range (p + 0 + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) =
          kappa p r * ∑ q ∈ Finset.range (p + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [pow_zero, one_mul, gridWindowSum_zero, Nat.add_zero]
      rw [iteratedCovGrad_zero, hrhs]
      exact hkappa p r W x
  | succ j ih =>
      intro p r W x

      set K : ℝ := gridWindowSum kappa p r (j + 1) with hK_def
      set S : ℝ := ∑ q ∈ Finset.range (p + (j + 1) + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hS_def
      have hK_nn : 0 ≤ K := gridWindowSum_nonneg hkappa_nn p r (j + 1)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg fun q _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hpow_nn : (0 : ℝ) ≤ (4 : ℝ) ^ j := by positivity

      rw [show riemannianFiberNormSq (I := I) (M := M) g 0 ((r + p) + (j + 1)) x
            ((iteratedCovGrad g 0 (r + p) (j + 1)
              (diffCurvOp (I := I) (M := M) g hX hY p r W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (covGrad (I := I) (M := M) g 0 (r + p)
                (diffCurvOp (I := I) (M := M) g hX hY p r W))).toSection x) from
        (rfns_iteratedCovGrad_covGrad_comm_lg g 0 (r + p) j
          (diffCurvOp (I := I) (M := M) g hX hY p r W) x).symm]
      rw [covGrad_diffCurvOp_eq g hX hY p r W, iteratedCovGrad_add]
      refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 (((r + p) + 1) + j) x
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W)).toSection x)
          ((iteratedCovGrad g 0 ((r + p) + 1) j
            (castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
              (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                (covGrad (I := I) (M := M) g 0 r W)))).toSection x)).trans ?_

      set kA : ℝ := gridWindowSum kappa (p + 1) r j with hkA_def
      set kB : ℝ := gridWindowSum kappa p (r + 1) j with hkB_def

      set sA : ℝ := ∑ q ∈ Finset.range ((p + 1) + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
          ((iteratedCovGrad g 0 r q W).toSection x) with hsA_def

      set sB : ℝ := ∑ q ∈ Finset.range (p + j + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (q + 1)) x
          ((iteratedCovGrad g 0 r (q + 1) W).toSection x) with hsB_def

      have hA : riemannianFiberNormSq (I := I) (M := M) g 0 ((r + (p + 1)) + j) x
            ((iteratedCovGrad g 0 (r + (p + 1)) j
              (diffCurvOp (I := I) (M := M) g hX hY (p + 1) r W)).toSection x) ≤
          (4 : ℝ) ^ j * (kA * sA) := by
        refine (ih (p + 1) r W x).trans_eq ?_
        rw [hkA_def, hsA_def, mul_assoc]
      have hB0 := ih p (r + 1) (covGrad (I := I) (M := M) g 0 r W) x

      have hBshift : gridWindowSum kappa p (r + 1) j *
            ∑ q ∈ Finset.range (p + j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 ((r + 1) + q) x
                ((iteratedCovGrad g 0 (r + 1) q (covGrad (I := I) (M := M) g 0 r W)).toSection x) =
          kB * sB := by
        rw [hkB_def, hsB_def]
        congr 1
        exact Finset.sum_congr rfl fun q _ => rfns_iteratedCovGrad_covGrad_comm_lg g 0 r q W x
      have hB : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                (covGrad (I := I) (M := M) g 0 r W))).toSection x) ≤
          (4 : ℝ) ^ j * (kB * sB) := by
        refine hB0.trans_eq ?_
        rw [mul_assoc, ← hBshift]

      have hkA_le : kA ≤ K := by
        rw [hkA_def, hK_def]
        exact gridWindowSum_shift_le hkappa_nn p r j 1 0 le_rfl (Nat.zero_le _)
      have hkB_le : kB ≤ K := by
        rw [hkB_def, hK_def]
        exact gridWindowSum_shift_le hkappa_nn p r j 0 1 (Nat.zero_le _) le_rfl

      have hsA_le : sA ≤ S := by
        rw [hsA_def, hS_def]
        exact le_of_eq (Finset.sum_congr (by rw [show (p + 1) + j + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))

      have hsB_le : sB ≤ S := by
        rw [hsB_def, hS_def]
        refine le_trans (sum_range_shift_le (p + j + 1)
          (fun q => riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x))
          (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _)) ?_
        exact le_of_eq (Finset.sum_congr (by rw [show (p + j + 1) + 1 = p + (j + 1) + 1 from by omega])
          (fun _ _ => rfl))
      have hkA_nn : 0 ≤ kA := gridWindowSum_nonneg hkappa_nn (p + 1) r j
      have hkB_nn : 0 ≤ kB := gridWindowSum_nonneg hkappa_nn p (r + 1) j
      have hsA_nn : 0 ≤ sA :=
        Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + q) x _
      have hsB_nn : 0 ≤ sB :=
        Finset.sum_nonneg fun q _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (r + (q + 1)) x _

      have hprodA : kA * sA ≤ K * S := mul_le_mul hkA_le hsA_le hsA_nn hK_nn
      have hprodB : kB * sB ≤ K * S := mul_le_mul hkB_le hsB_le hsB_nn hK_nn
      have hgoal : (2 : ℝ) * ((4 : ℝ) ^ j * (kA * sA)) +
            (2 : ℝ) * ((4 : ℝ) ^ j * (kB * sB)) ≤
          (4 : ℝ) ^ (j + 1) * (K * S) := by
        have h4 : (4 : ℝ) ^ (j + 1) = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
        rw [h4]
        nlinarith [hprodA, hprodB, hpow_nn,
          mul_le_mul_of_nonneg_left hprodA hpow_nn,
          mul_le_mul_of_nonneg_left hprodB hpow_nn]
      have htarget : (4 : ℝ) ^ (j + 1) * (K * S) =
          (4 : ℝ) ^ (j + 1) * gridWindowSum kappa p r (j + 1) *
            ∑ q ∈ Finset.range (p + (j + 1) + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
                ((iteratedCovGrad g 0 r q W).toSection x) := by
        rw [hK_def, hS_def, mul_assoc]
      rw [htarget] at hgoal
      refine le_trans ?_ hgoal

      have hb_eq : riemannianFiberNormSq (I := I) (M := M) g 0 (((r + p) + 1) + j) x
            ((iteratedCovGrad g 0 ((r + p) + 1) j
              (castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
                (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                  (covGrad (I := I) (M := M) g 0 r W)))).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g 0 (((r + 1) + p) + j) x
            ((iteratedCovGrad g 0 ((r + 1) + p) j
              (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
                (covGrad (I := I) (M := M) g 0 r W))).toSection x) :=
        rfns_iteratedCovGrad_castRankCc_lg g 0 (by omega : (r + 1) + p = r + (p + 1))
          (diffCurvOp (I := I) (M := M) g hX hY p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) j x
      rw [hb_eq]
      exact add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))

end GridInduction


theorem exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le_of_construction
    (s : ℕ) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (Z : SmoothCcTensor g 0 s) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((iteratedCovGrad g 0 s j (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection
              x) ≤
          (4 : ℝ) ^ j * gridWindowSum kappa 0 s j *
            ∑ q ∈ Finset.range (j + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
                ((iteratedCovGrad g 0 s q Z).toSection x) := by
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_diffCurvOp (I := I) (M := M) g hX hY
  refine ⟨kappa, hkappa_nn, fun Z j x => ?_⟩
  have hgrid := riemannianFiberNormSq_iteratedCovGrad_diffCurvOp_grid (I := I) (M := M) g hX hY
    hkappa_nn hkappa j 0 s Z x

  rw [diffCurvOp_zero g hX hY s Z] at hgrid
  simpa only [Nat.add_zero, Nat.zero_add] using hgrid

end Connection
end Integral
end DifferentialGeometry

end
