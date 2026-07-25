import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma vec3_upd_zero {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 0 z = ![z, b, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_upd_one {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 1 z = ![a, z, c] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma vec3_upd_two {F : Type*} (a b c z : F) :
    Function.update ![a, b, c] 2 z = ![a, b, z] := by
  funext k
  fin_cases k <;> simp [Function.update]


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma linearizedKoszulCovec_add_fst (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (u u' ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x (u + u') ζ =
      linearizedKoszulCovec (I := I) g' S x u ζ +
        linearizedKoszulCovec (I := I) g' S x u' ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.add_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply,
    linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ, u + u', z] = G ![ζ, u, z] + G ![ζ, u', z] := by
    have h := G.map_update_add ![ζ, u, z] 1 u u'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  have h2 : G ![u + u', ζ, z] = G ![u, ζ, z] + G ![u', ζ, z] := by
    have h := G.map_update_add ![u, ζ, z] 0 u u'
    rwa [vec3_upd_zero, vec3_upd_zero, vec3_upd_zero] at h
  have h3 : G ![z, ζ, u + u'] = G ![z, ζ, u] + G ![z, ζ, u'] := by
    have h := G.map_update_add ![z, ζ, u] 2 u u'
    rwa [vec3_upd_two, vec3_upd_two, vec3_upd_two] at h
  rw [h1, h2, h3]
  ring


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma linearizedKoszulCovec_smul_fst (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x (c • u) ζ =
      c • linearizedKoszulCovec (I := I) g' S x u ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ, c • u, z] = c • G ![ζ, u, z] := by
    have h := G.map_update_smul ![ζ, u, z] 1 c u
    rwa [vec3_upd_one, vec3_upd_one] at h
  have h2 : G ![c • u, ζ, z] = c • G ![u, ζ, z] := by
    have h := G.map_update_smul ![u, ζ, z] 0 c u
    rwa [vec3_upd_zero, vec3_upd_zero] at h
  have h3 : G ![z, ζ, c • u] = c • G ![z, ζ, u] := by
    have h := G.map_update_smul ![z, ζ, u] 2 c u
    rwa [vec3_upd_two, vec3_upd_two] at h
  rw [h1, h2, h3]
  simp only [smul_eq_mul]
  ring


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma linearizedKoszulCovec_add_snd (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (u ζ ζ' : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x u (ζ + ζ') =
      linearizedKoszulCovec (I := I) g' S x u ζ +
        linearizedKoszulCovec (I := I) g' S x u ζ' := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.add_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply,
    linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![ζ + ζ', u, z] = G ![ζ, u, z] + G ![ζ', u, z] := by
    have h := G.map_update_add ![ζ, u, z] 0 ζ ζ'
    rwa [vec3_upd_zero, vec3_upd_zero, vec3_upd_zero] at h
  have h2 : G ![u, ζ + ζ', z] = G ![u, ζ, z] + G ![u, ζ', z] := by
    have h := G.map_update_add ![u, ζ, z] 1 ζ ζ'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  have h3 : G ![z, ζ + ζ', u] = G ![z, ζ, u] + G ![z, ζ', u] := by
    have h := G.map_update_add ![z, ζ, u] 1 ζ ζ'
    rwa [vec3_upd_one, vec3_upd_one, vec3_upd_one] at h
  rw [h1, h2, h3]
  ring


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma linearizedKoszulCovec_smul_snd (g' : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g' 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' S x u (c • ζ) =
      c • linearizedKoszulCovec (I := I) g' S x u ζ := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, linearizedKoszulCovec_apply, linearizedKoszulCovec_apply]
  set G := unitModel (I := I) (M := M) g' 3 (covGrad (I := I) (M := M) g' 0 2 S) x with hG
  have h1 : G ![c • ζ, u, z] = c • G ![ζ, u, z] := by
    have h := G.map_update_smul ![ζ, u, z] 0 c ζ
    rwa [vec3_upd_zero, vec3_upd_zero] at h
  have h2 : G ![u, c • ζ, z] = c • G ![u, ζ, z] := by
    have h := G.map_update_smul ![u, ζ, z] 1 c ζ
    rwa [vec3_upd_one, vec3_upd_one] at h
  have h3 : G ![z, c • ζ, u] = c • G ![z, ζ, u] := by
    have h := G.map_update_smul ![z, ζ, u] 1 c ζ
    rwa [vec3_upd_one, vec3_upd_one] at h
  rw [h1, h2, h3]
  simp only [smul_eq_mul]
  ring


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma linearizedKoszulCovec_zero_weight (g' : SmoothRiemannianMetric I M) (x : M)
    (u ζ : TangentSpace I x) :
    linearizedKoszulCovec (I := I) g' (0 : SmoothCcTensor g' 0 2) x u ζ = 0 := by
  apply LinearMap.ext
  intro z
  rw [linearizedKoszulCovec_apply, LinearMap.zero_apply]
  have hzero : covGrad (I := I) (M := M) g' 0 2 (0 : SmoothCcTensor g' 0 2) = 0 :=
    covGrad_zero (I := I) (M := M) g' 0 2
  rw [hzero]
  have hunit : ∀ v : Fin 3 → TangentSpace I x,
      unitModel (I := I) (M := M) g' 3 (0 : SmoothCcTensor g' 0 3) x v = 0 := by
    intro v
    rw [unitModel]
    have h0 : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (0 : SmoothCcTensor g' 0 3).toSection x) = 0 := rfl
    rw [h0, ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero]
    rfl
  rw [hunit ![ζ, u, z], hunit ![u, ζ, z], hunit ![z, ζ, u]]
  ring

def sharpRaisedKoszulVec (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (u ζ : TangentSpace I x) : TangentSpace I x :=
  DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
    (linearizedKoszulCovec (I := I) g₀ S x u ζ)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpRaisedKoszulVec_add_fst (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u u' ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x (u + u') ζ =
      sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ +
        sharpRaisedKoszulVec (I := I) g₀ g₁ S x u' ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, sharpRaisedKoszulVec,
    linearizedKoszulCovec_add_fst,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_add]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpRaisedKoszulVec_smul_fst (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x (c • u) ζ =
      c • sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, linearizedKoszulCovec_smul_fst,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpRaisedKoszulVec_add_snd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (u ζ ζ' : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x u (ζ + ζ') =
      sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ +
        sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ' := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, sharpRaisedKoszulVec,
    linearizedKoszulCovec_add_snd,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_add]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpRaisedKoszulVec_smul_snd (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (c : ℝ) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ S x u (c • ζ) =
      c • sharpRaisedKoszulVec (I := I) g₀ g₁ S x u ζ := by
  rw [sharpRaisedKoszulVec, sharpRaisedKoszulVec, linearizedKoszulCovec_smul_snd,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_smul]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpRaisedKoszulVec_zero_weight (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x u ζ = 0 := by
  rw [sharpRaisedKoszulVec, linearizedKoszulCovec_zero_weight,
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_zero]

def sharpGradKoszulKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 =>
        (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0))
          + (g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)).comp
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p))
        - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p))
          + (g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)).comp
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0))
      map_add' := fun v0 v0' => by
        rw [sharpRaisedKoszulVec_add_snd, map_add, map_add, map_add,
          ContinuousLinearMap.add_comp,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v0 + v0') =
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 +
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0' from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_add v0 v0',
          ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.comp_add]
        abel
      map_smul' := fun c v0 => by
        rw [RingHom.id_apply, sharpRaisedKoszulVec_smul_snd, map_smul, map_smul, map_smul,
          ContinuousLinearMap.smul_comp,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • v0) =
            c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_smul c v0,
          ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.comp_smul]
        rw [smul_sub, smul_add, smul_add] }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sharpGradKoszulKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q v0 v1 : TangentSpace I x) :
    sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1 =
      (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)) v1
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1))
      - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)) v1
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x q p)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1)) := by
  rw [sharpGradKoszulKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]

def frameSharpGradKoszulKernel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        haveI : FiniteDimensional ℝ (TangentSpace I x) :=
          inferInstanceAs (FiniteDimensional ℝ E)
        LinearMap.toContinuousLinearMap
          { toFun := fun q => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1
            map_add' := fun q q' => by
              rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
                sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_add_fst,
                sharpRaisedKoszulVec_add_fst]
              simp only [map_add, ContinuousLinearMap.add_apply]
              ring
            map_smul' := fun c q => by
              rw [RingHom.id_apply, sharpGradKoszulKernelBilin_apply,
                sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_smul_fst,
                sharpRaisedKoszulVec_smul_fst]
              simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
              ring }
      map_add' := fun p p' => by
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
          sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_add_snd,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p + p') =
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x p +
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x p' from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_add p p']
        simp only [map_add, ContinuousLinearMap.add_apply]
        ring
      map_smul' := fun c p => by
        rw [RingHom.id_apply]
        apply ContinuousLinearMap.ext
        intro q
        rw [ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_toContinuousLinearMap']
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [sharpGradKoszulKernelBilin_apply, sharpGradKoszulKernelBilin_apply,
          sharpRaisedKoszulVec_smul_snd,
          show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • p) =
            c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x p from
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).map_smul c p]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma frameSharpGradKoszulKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v0 v1 p q : TangentSpace I x) :
    frameSharpGradKoszulKernel (I := I) g₀ g₁ S x v0 v1 p q =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q v0 v1 := by
  rw [frameSharpGradKoszulKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def sharpGradKoszulSummandFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sharpGradKoszulSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (p q : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (sharpGradKoszulSummandFib (I := I) g₀ g₁ S x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x p q (v 0) (v 1) := by
  rw [sharpGradKoszulSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def sharpGradKoszulBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpGradKoszulBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x D) v =
      (2 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (B a x) (B b x) (v 0) (v 1) := by
  classical
  rw [sharpGradKoszulBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply,
    ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, sharpGradKoszulSummandFib_toModel]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma unitValueCovGrad3_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g₀ 0 2 S).toSection y)
          (unitZeroSec (I := I) (M := M) y))) := by
  exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel 3 ℝ E)
    (E₁ := fun z : M => Tensor0SSpace 0 I z)
    (E₂ := fun z : M => Tensor0SSpace 3 I z)
    (IM := I) (IB := I) (b := id)
    (ϕ := fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g₀ 0 2 S).toSection y))
    (v := fun y : M => unitZeroSec (I := I) (M := M) y)
    (covGrad (I := I) (M := M) g₀ 0 2 S).toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma linearizedKoszulCovec_basis_contMDiffOn_generic
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        linearizedKoszulCovec (I := I) g₀ S b (Z b) (Y b)
          (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  set W₃ : ∀ b : M, Tensor0SSpace 3 I b := fun b =>
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 3 I b from
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection b)
      (unitZeroSec (I := I) (M := M) b) with hW₃def
  have hW₃ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SSpace 3 I z) y (W₃ y)) :=
    unitValueCovGrad3_contMDiff (I := I) (M := M) g₀ S
  intro b hb
  have hb_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb
  have hbasisAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y => chartBasisVecFiber (I := I) α j y)) b := by
    have h := chartBasisVec_contMDiffOn (I := I) α j
    have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
      (trivializationAt E (TangentSpace I) α).open_baseSet
    exact (h b hb_base).contMDiffAt (hopen.mem_nhds hb_base)
  have hEval : ∀ (v : Fin 3 → ∀ y : M, TangentSpace I y)
      (_ : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% (v i)) b),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => Tensor0SSpace.toModel (W₃ y) (fun i : Fin 3 => v i y)) b :=
    fun v hv => TensorMultilinear.contMDiffAt_section_apply (n := 3) W₃
      (hW₃.contMDiffAt) v hv
  have h1 := hEval ![fun y => Y y, fun y => Z y, fun y => chartBasisVecFiber (I := I) α j y]
    (by
      intro i
      fin_cases i
      · exact Y.contMDiff.contMDiffAt
      · exact Z.contMDiff.contMDiffAt
      · exact hbasisAt)
  have h2 := hEval ![fun y => Z y, fun y => Y y, fun y => chartBasisVecFiber (I := I) α j y]
    (by
      intro i
      fin_cases i
      · exact Z.contMDiff.contMDiffAt
      · exact Y.contMDiff.contMDiffAt
      · exact hbasisAt)
  have h3 := hEval ![fun y => chartBasisVecFiber (I := I) α j y, fun y => Y y, fun y => Z y]
    (by
      intro i
      fin_cases i
      · exact hbasisAt
      · exact Y.contMDiff.contMDiffAt
      · exact Z.contMDiff.contMDiffAt)
  have hcomb : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => (1 / 2 : ℝ) *
        (Tensor0SSpace.toModel (W₃ y)
            (fun i : Fin 3 => (![fun y' => Y y', fun y' => Z y',
              fun y' => chartBasisVecFiber (I := I) α j y'] : Fin 3 → ∀ y' : M,
                TangentSpace I y') i y)
          + Tensor0SSpace.toModel (W₃ y)
              (fun i : Fin 3 => (![fun y' => Z y', fun y' => Y y',
                fun y' => chartBasisVecFiber (I := I) α j y'] : Fin 3 → ∀ y' : M,
                  TangentSpace I y') i y)
          - Tensor0SSpace.toModel (W₃ y)
              (fun i : Fin 3 => (![fun y' => chartBasisVecFiber (I := I) α j y',
                fun y' => Y y', fun y' => Z y'] : Fin 3 → ∀ y' : M,
                  TangentSpace I y') i y))) b :=
    ContMDiffAt.mul contMDiffAt_const ((h1.add h2).sub h3)
  refine (hcomb.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards with y
  rw [linearizedKoszulCovec_apply]
  have hUM : ∀ v : Fin 3 → TangentSpace I y,
      unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) y v =
        Tensor0SSpace.toModel (W₃ y) v := fun _ => rfl
  rw [hUM, hUM, hUM]
  congr 1
  congr 1
  · congr 1
    · congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  · congr 1
    funext i
    fin_cases i <;> rfl


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sharpRaisedKoszulVec_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (U Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (U b) (Z b))) := by
  apply DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_contMDiff_total (I := I) g₁
    (cv := fun b : M => linearizedKoszulCovec (I := I) g₀ S b (U b) (Z b))
  intro α j
  exact linearizedKoszulCovec_basis_contMDiffOn_generic (I := I) (M := M) g₀ S Z U α j

omit [NeZero (Module.finrank ℝ E)] in
theorem sharpGradKoszulKernelBilin_homSection_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x
        (sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (p x) (q x) (V0 x))
  intro W
  have hΨqV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b))) := by
    have h := sharpRaisedKoszulVec_section_contMDiff (I := I) (M := M) g₀ g₁ S
      ⟨fun b => q b, hq⟩ ⟨fun b => V0 b, V0.contMDiff⟩
    exact h
  have hΨqp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b))) := by
    have h := sharpRaisedKoszulVec_section_contMDiff (I := I) (M := M) g₀ g₁ S
      ⟨fun b => q b, hq⟩ ⟨fun b => p b, hp⟩
    exact h
  have hApΨ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b)))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hp hΨqV
  have hApW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b) (W b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ hp W.contMDiff
  have hAVΨ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b)))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff hΨqp
  have hAVW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b) (W b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff W.contMDiff
  have hs1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b)), hApΨ⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x) (W x))) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (V0 b), hΨqV⟩
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (p b) (W b), hApW⟩
  have hs3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b)
        (sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b)), hAVΨ⟩
      ⟨fun b => W b, W.contMDiff⟩
  have hs4 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (W x))) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₁
      ⟨fun b => sharpRaisedKoszulVec (I := I) g₀ g₁ S b (q b) (p b), hΨqp⟩
      ⟨fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (V0 b) (W b), hAVW⟩
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x)
          (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))) (W x)
        + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (V0 x))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (p x) (W x)))
        - (g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x)
            (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))) (W x)
          + g₁.inner x (sharpRaisedKoszulVec (I := I) g₀ g₁ S x (q x) (p x))
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (V0 x) (W x)))) :=
    (hs1.add hs2).sub (hs3.add hs4)
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change sharpGradKoszulKernelBilin (I := I) g₀ g₁ S y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [sharpGradKoszulKernelBilin_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem sharpGradKoszulBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b' => Y b') Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => sharpGradKoszulKernelBilin (I := I) g₀ g₁ S x (B a x) (B b x))
      (sharpGradKoszulKernelBilin_homSection_contMDiff (I := I) g₀ g₁ S (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x : M =>
        Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set T2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hT2_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b with hStot_def
  have hfinal := ContMDiff.smul_section (f := fun _ : M => (2 : ℝ))
    contMDiff_const Stot.contMDiff
  refine hfinal.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  have hcoe1 : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), T2 a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
            Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), T2 a b) Finset.univ
  have hcoe2 : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), T2 a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((T2 a b : Π z : M, Tensor0SSpace 2 I z)) :=
    fun a => map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => T2 a b) Finset.univ
  have hval : Stot x = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      sharpGradKoszulSummandFib (I := I) g₀ g₁ S x (B a x) (B b x) (Y x) := by
    have h1 : Stot x = ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        T2 a b : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) x := rfl
    rw [h1, hcoe1, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoe2 a, Finset.sum_apply]
    rfl
  have hgoal : sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x (Y x) =
      (2 : ℝ) • Stot x := by
    rw [hval, sharpGradKoszulBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact ContinuousLinearMap.sum_apply _ _ _
  rw [hgoal]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem sharpGradKoszulBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S B x)
  intro Y
  exact sharpGradKoszulBiContrFibFixedFrame_apply_section_contMDiff
    (I := I) g₀ g₁ S B hB Y

def sharpGradKoszulBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S (smoothOrthoFrame (I := I) g₁ x) x

omit [BoundarylessManifold I M] in
theorem sharpGradKoszulBiContrFib_eq_fixedFrame_on_nbhd
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    sharpGradKoszulBiContrFib (I := I) g₀ g₁ S y =
      sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S
        (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel,
    sharpGradKoszulBiContrFibFixedFrame_toModel]
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ S y (Bf a) (Bf b) (v 0) (v 1) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameSharpGradKoszulKernel (I := I) g₀ g₁ S y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameSharpGradKoszulKernel_apply,
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rw [mul_comm]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameSharpGradKoszulKernel (I := I) g₀ g₁ S y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem sharpGradKoszulBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ S
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    sharpGradKoszulBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁ S
      (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (sharpGradKoszulBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ S x₀ hy))

def ricciArmSharpGradKoszulResidualField (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x))
      contMDiff_toFun := sharpGradKoszulBiContrFib_contMDiff (I := I) g₀ g₁ S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem ricciArmSharpGradKoszulResidualField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (sharpGradKoszulBiContrFib (I := I) g₀ g₁ S x)) := rfl


theorem ricciArmSharpGradKoszulResidualField_zero_weight
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
      (0 : SmoothCcTensor g₀ 0 2) = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [ricciArmSharpGradKoszulResidualField_toSection]
  have hzero : sharpGradKoszulBiContrFib (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x = 0 := by
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [sharpGradKoszulBiContrFib, sharpGradKoszulBiContrFibFixedFrame_toModel]
    have hker : ∀ p q : TangentSpace I x,
        sharpGradKoszulKernelBilin (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x p q
          (v 0) (v 1) = 0 := by
      intro p q
      rw [sharpGradKoszulKernelBilin_apply, sharpRaisedKoszulVec_zero_weight,
        sharpRaisedKoszulVec_zero_weight]
      simp only [map_zero, ContinuousLinearMap.zero_apply]
      ring
    rw [show (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)]) *
          sharpGradKoszulKernelBilin (I := I) g₀ g₁ (0 : SmoothCcTensor g₀ 0 2) x
            (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
            (v 0) (v 1)) = 0 from
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => by
        rw [hker]
        ring))]
    rw [mul_zero]
    simp only [ContinuousLinearMap.zero_apply, Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply]
  rw [hzero]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
