import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Connection.ChartBridge.Gradient
import DifferentialGeometry.Bundle.SmoothScalarGerm
import Mathlib.Analysis.Calculus.FDeriv.Congr


noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

def abstractHessianLin (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  let L : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    abstractHessian (I := I) g f x
  { toFun := fun v =>
      { toFun := fun w => L v w
        map_add' := fun w₁ w₂ => by simp
        map_smul' := fun c w => by simp }
    map_add' := fun v₁ v₂ => by
      ext w
      change L (v₁ + v₂) w = L v₁ w + L v₂ w
      rw [map_add]; rfl
    map_smul' := fun c v => by
      ext w
      change L (c • v) w = c * L v w
      rw [map_smul]; rfl }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma abstractHessianLin_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    abstractHessianLin (I := I) g f x v w =
      abstractHessian (I := I) g f x v w := rfl

def abstractHessianBilin (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    pointwiseBilin (M := M) I :=
  fun x => abstractHessianLin (I := I) g f x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma abstractHessianBilin_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    abstractHessianBilin (I := I) g f x v w =
      abstractHessian (I := I) g f x v w := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractHessianLin_symm
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v w : TangentSpace I x) :
    abstractHessianLin (I := I) g f x v w =
      abstractHessianLin (I := I) g f x w v :=
  abstractHessian_symm (I := I) g hf v w

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractHessianBilin_isPointwiseSymm
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    IsPointwiseSymm (abstractHessianBilin (I := I) (M := M) g f) := by
  intro x v w
  apply abstractHessianLin_symm (I := I) g
  exact (hf.contMDiffAt).of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractHessian_eq_inner_cov_gradFun_extend [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) (v w : TangentSpace I x) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x v) w =
      abstractHessian (I := I) g f x v w := by
  classical
  set V : Π b : M, TangentSpace I b := FiberBundle.extend E v with hV_def
  set W : Π b : M, TangentSpace I b := FiberBundle.extend E w with hW_def
  have hVx : V x = v := by simp [V]
  have hWx : W x = w := by simp [W]
  have hV_at : MDiffAt (T% V) x := mdifferentiableAt_extend ..
  have hW_at : MDiffAt (T% W) x := mdifferentiableAt_extend ..
  set cov := LeviCivita (I := I) g with hcov
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        (gradFun (I := I) g f y)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have h_grad_at : MDiffAt (T% (fun b => gradFun (I := I) g f b)) x :=
    (h_grad_smooth x).mdifferentiableAt (by simp)
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth :=
      cotangentCov_extDerivFun_smooth (I := I) hf
    exact (hext_smooth x).mdifferentiableAt (by simp)
  have hpair_W := cotangentCov_dualPairing cov hθ_at hW_at v
  have h_eq_fn : (fun b : M => extDerivFun (I := I) f b (W b)) =
      (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) := by
    funext b
    exact (gradFun_metricDual_extDerivFun (I := I) g f b (W b)).symm
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply h_grad_at hW_at v
  have hmc' : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (W b)) x v =
      g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x v) (W x) +
        g.inner x (gradFun (I := I) g f x) (cov.toFun W x v) := by
    have hext_eq : extDerivFun (I := I)
        (fun b => g.inner b (gradFun (I := I) g f b) (W b)) x v =
          (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) x) v := rfl
    rw [hext_eq, hmc]
  have h_lhs_eq : extDerivFun (I := I) (fun b : M => θ b (W b)) x v =
      extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) x v := by
    have h_eq : (fun b : M => θ b (W b)) =
        (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) := h_eq_fn
    rw [h_eq]
  rw [h_lhs_eq] at hpair_W
  have h_grad_inner :
      g.inner x (gradFun (I := I) g f x) (cov.toFun W x v) =
        θ x (cov.toFun W x v) := by
    rw [gradFun_metricDual_extDerivFun (I := I) g f x (cov.toFun W x v)]
  have hkey :
      g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x v) (W x) =
        ((cotangentCov cov).toFun θ x v) (W x) := by
    have hlhs := hmc'
    rw [h_grad_inner] at hlhs
    have h := hlhs.symm.trans hpair_W
    linarith [h]
  rw [hWx] at hkey
  rw [hkey]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractHessian_eq_inner_cov_gradFun_smooth [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      abstractHessian (I := I) g f x (X x) (Y x) :=
  inner_cov_gradFun_eq_abstractHessian (I := I) g hf hX hY

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma traceFun_abstractHessianBilin_def
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f x
          ((chartModelBasis E) i) ((chartModelBasis E) i) := by
  unfold traceFun
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma frobeniusSqFun_abstractHessianBilin_def
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (abstractHessian (I := I) g f x
            ((chartModelBasis E) i) ((chartModelBasis E) j))^2 := by
  unfold frobeniusSqFun
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem traceFun_abstractHessianBilin_sq_le_dim_mul_frobeniusSqFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
  traceFun_sq_le_dim_mul_frobeniusSqFun
    (I := I) (M := M) (abstractHessianBilin (I := I) g f) x

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem traceFun_abstractHessianBilin_sq_div_dim_le_frobeniusSqFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x)^2 /
      (Module.finrank ℝ E : ℝ) ≤
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
  traceFun_sq_div_dim_le_frobeniusSqFun
    (I := I) (M := M) (abstractHessianBilin (I := I) g f) x

def chartHessianMatrixIdentity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) : Prop :=
  ∀ i j : Fin (Module.finrank ℝ E),
    abstractHessian (I := I) g f x
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      chartHessianTensor (I := I) g x f i j x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem hessFun_eq_abstractHessianBilin_of_matrix_identity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      abstractHessianBilin (I := I) g f x v w := by
  classical
  rw [hessFun_apply]
  rw [abstractHessianBilin_apply]
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  have h_abs : abstractHessian (I := I) g f x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (b.repr v i * b.repr w j) *
            abstractHessian (I := I) g f x (b i) (b j) := by
    have hv_decomp : v = ∑ i : Fin (Module.finrank ℝ E), b.repr v i • b i :=
      (Module.Basis.sum_repr b v).symm
    have hw_decomp : w = ∑ j : Fin (Module.finrank ℝ E), b.repr w j • b j :=
      (Module.Basis.sum_repr b w).symm
    have h1 : abstractHessian (I := I) g f x v =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr v i • abstractHessian (I := I) g f x (b i) := by
      have happ_eq : abstractHessian (I := I) g f x v =
          abstractHessian (I := I) g f x
            (∑ i : Fin (Module.finrank ℝ E), b.repr v i • b i) :=
        congrArg (abstractHessian (I := I) g f x) hv_decomp
      rw [happ_eq, map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      exact (abstractHessian (I := I) g f x).map_smul (b.repr v i) (b i)
    have h2 : abstractHessian (I := I) g f x v w =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr v i • abstractHessian (I := I) g f x (b i) w := by
      rw [h1]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rfl
    have h3 : ∀ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f x (b i) w =
          ∑ j : Fin (Module.finrank ℝ E),
            b.repr w j • abstractHessian (I := I) g f x (b i) (b j) := by
      intro i
      have happ_eq : abstractHessian (I := I) g f x (b i) w =
          abstractHessian (I := I) g f x (b i)
            (∑ j : Fin (Module.finrank ℝ E), b.repr w j • b j) :=
        congrArg (abstractHessian (I := I) g f x (b i)) hw_decomp
      rw [happ_eq, map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      exact (abstractHessian (I := I) g f x (b i)).map_smul (b.repr w j) (b j)
    rw [h2]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [h3 i]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [h_abs]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hM i j, mul_assoc]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x) :
    traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x := by
  classical
  unfold traceFun
  refine Finset.sum_congr rfl ?_
  intro i _
  exact hessFun_eq_abstractHessianBilin_of_matrix_identity (I := I) g f x hM
    ((chartModelBasis E) i) ((chartModelBasis E) i)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x) :
    frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x := by
  classical
  unfold frobeniusSqFun
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hessFun_eq_abstractHessianBilin_of_matrix_identity (I := I) g f x hM
    ((chartModelBasis E) i) ((chartModelBasis E) j)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartHessianTensor_eq_inner_cov_gradFun_basis_of_matrix_identity
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x)
    (i j : Fin (Module.finrank ℝ E)) :
    chartHessianTensor (I := I) g x f i j x =
      g.inner x ((LeviCivita (I := I) g).toFun
                    (fun b => gradFun (I := I) g f b) x ((chartModelBasis E) i))
        ((chartModelBasis E) j) := by
  rw [← hM i j]
  exact (abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x
    ((chartModelBasis E) i) ((chartModelBasis E) j)).symm

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma trivToE_self_eq_id (x : M) :
    (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  classical
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
    (x₀ := x) (x := x) (mem_chart_source H x)
  rw [show (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x from rfl]
  rw [h]
  exact mfderiv_extChartAt_self (I := I) (x := x)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma trivToE_self_apply (x : M) (v : TangentSpace I x) :
    trivToE (I := I) x x v = v := by
  rw [trivToE_self_eq_id (I := I) x]
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma trivFromE_self_apply (x : M) (w : E) :
    trivFromE (I := I) x x w = w := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have h := trivToE_trivFromE (I := I) x hbase w
  rwa [trivToE_self_apply (I := I) x (trivFromE (I := I) x x w)] at h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartBasisVecFiber_self
    (x : M) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x i x = (chartModelBasis E) i := by
  unfold chartBasisVecFiber
  change trivFromE (I := I) x x ((chartModelBasis E) i) = (chartModelBasis E) i
  exact trivFromE_self_apply (I := I) x ((chartModelBasis E) i)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartE_section_repr_chartBasisVec_apply
    (x : M) (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    chartE_section_repr (I := I) x
        (fun y : M => chartBasisVecFiber (I := I) x j y) b =
      (chartModelBasis E) j := by
  classical
  unfold chartE_section_repr
  change trivToE (I := I) x b (chartBasisVecFiber (I := I) x j b) =
    (chartModelBasis E) j
  have h := trivToE_trivFromE (I := I) x hb ((chartModelBasis E) j)
  have heq : chartBasisVecFiber (I := I) x j b =
      trivFromE (I := I) x b ((chartModelBasis E) j) := rfl
  rw [heq]
  exact h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartE_section_repr_chartBasisVec_pullback_constOn
    (x : M) (j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : (extChartAt I x).symm y ∈
        (trivializationAt E (TangentSpace I) x).baseSet) :
    (chartE_section_repr (I := I) x
        (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) y =
      (chartModelBasis E) j := by
  classical
  change chartE_section_repr (I := I) x
      (fun b : M => chartBasisVecFiber (I := I) x j b) ((extChartAt I x).symm y) =
    (chartModelBasis E) j
  exact chartE_section_repr_chartBasisVec_apply (I := I) x j hy

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartBasisVec_mdifferentiableAt_self
    (x : M) (j : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) x j b)) x := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hcontMDiff_on :=
    chartBasisVec_contMDiffOn (I := I) x j
  have hopen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hcontMDiff_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) x j) x :=
    (hcontMDiff_on x hbase).contMDiffAt (hopen.mem_nhds hbase)
  exact hcontMDiff_at.mdifferentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma extDerivFun_chartBasisVec_apply_of_mem
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb_chart : b ∈ (chartAt H x).source)
    (hb_int : extChartAt I x b ∈ interior ((extChartAt I x).target : Set E)) :
    extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) x j b) =
      partialDeriv (E := E) j (scalarOnE (I := I) x f) (extChartAt I x b) := by
  classical
  have hf_at : MDiffAt f b := (hf b).mdifferentiableAt (by simp)
  change (mfderiv I 𝓘(ℝ, ℝ) f b) (chartBasisVecFiber (I := I) x j b) = _
  exact mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) x hf_at
    hb_chart hb_int j

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma extDerivFun_chartBasisVec_eventuallyEq
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (j : Fin (Module.finrank ℝ E)) :
    (fun b : M => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) x j b)) =ᶠ[𝓝 x]
      (fun b : M =>
        partialDeriv (E := E) j (scalarOnE (I := I) x f) (extChartAt I x b)) := by
  classical
  set S : Set M :=
    (chartAt H x).source ∩
      ((extChartAt I x) ⁻¹' interior ((extChartAt I x).target : Set E)) with hS_def
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hxS : x ∈ S := ⟨hxsrc, hxint⟩
  have hS_open : IsOpen S := by
    have hcont : ContinuousOn (extChartAt I x) (chartAt H x).source := by
      have h := continuousOn_extChartAt (I := I) (x := x)
      have heq : (extChartAt I x).source = (chartAt H x).source :=
        extChartAt_source (I := I) x
      rw [heq] at h
      exact h
    have hpre : IsOpen ((chartAt H x).source ∩
        (extChartAt I x) ⁻¹' interior ((extChartAt I x).target : Set E)) :=
      hcont.isOpen_inter_preimage ((chartAt H x).open_source) isOpen_interior
    convert hpre using 1
  have hS_nhds : S ∈ 𝓝 x := hS_open.mem_nhds hxS
  filter_upwards [hS_nhds] with b hb
  obtain ⟨hb_chart, hb_int⟩ := hb
  exact extDerivFun_chartBasisVec_apply_of_mem (I := I) hf x j hb_chart hb_int

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma extDerivFun_pairing_chartBasisVec_apply_basis
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    extDerivFun (I := I) (fun b => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) x j b)) x ((chartModelBasis E) i) =
      chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) := by
  classical
  have hev := extDerivFun_chartBasisVec_eventuallyEq (I := I) hf x j
  have hf_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) x f)
      (extChartAt I x).target :=
    scalarOnE_contDiffOn (I := I) x hf
  have hf_smooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) x f)
      (interior ((extChartAt I x).target : Set E)) :=
    hf_smooth_target.mono interior_subset
  have hopen_int : IsOpen (interior ((extChartAt I x).target : Set E)) := isOpen_interior
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  set g : M → ℝ :=
    fun b => partialDeriv (E := E) j (scalarOnE (I := I) x f) (extChartAt I x b) with hg_def
  have hu_smooth_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) x f) (extChartAt I x x) :=
    hf_smooth_int.contDiffAt (hopen_int.mem_nhds hxint)
  have hfd_contDiffOn : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) x f))
      (interior ((extChartAt I x).target : Set E)) :=
    hf_smooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hfd_contDiffAt : ContDiffAt ℝ ∞ (fderiv ℝ (scalarOnE (I := I) x f))
      (extChartAt I x x) :=
    hfd_contDiffOn.contDiffAt (hopen_int.mem_nhds hxint)
  have hPD_contDiffAt : ContDiffAt ℝ ∞
      (partialDeriv (E := E) j (scalarOnE (I := I) x f)) (extChartAt I x x) := by
    have hcomp_eq :
        partialDeriv (E := E) j (scalarOnE (I := I) x f) =
          (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j) :
            (E →L[ℝ] ℝ) →L[ℝ] ℝ) ∘
          (fderiv ℝ (scalarOnE (I := I) x f)) := by
      funext y
      rfl
    rw [hcomp_eq]
    exact (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j)).contDiff.contDiffAt.comp
      (extChartAt I x x) hfd_contDiffAt
  have hphi_mdiff : MDiffAt (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (I := I) (x := x) hxsrc
  have hPD_mdiff_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (partialDeriv (E := E) j (scalarOnE (I := I) x f)) (extChartAt I x x) := by
    have hd : DifferentiableAt ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) x f)) (extChartAt I x x) :=
      hPD_contDiffAt.differentiableAt (by simp)
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hd
  have hg_mdiff : MDiffAt g x :=
    hPD_mdiff_at.comp x hphi_mdiff
  have htgt_nhds : ((extChartAt I x).target : Set E) ∈ 𝓝 (extChartAt I x x) := by
    refine mem_nhds_iff.mpr ?_
    refine ⟨interior ((extChartAt I x).target : Set E),
      interior_subset, hopen_int, hxint⟩
  have hcompose_eq : (g ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
      (partialDeriv (E := E) j (scalarOnE (I := I) x f)) := by
    filter_upwards [htgt_nhds] with y hy
    change partialDeriv (E := E) j (scalarOnE (I := I) x f)
        (extChartAt I x ((extChartAt I x).symm y)) =
      partialDeriv (E := E) j (scalarOnE (I := I) x f) y
    rw [(extChartAt I x).right_inv hy]
  have hg_value :
      (mfderiv I 𝓘(ℝ) g x : TangentSpace I x →L[ℝ] _)
          ((chartModelBasis E) i) =
        chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) := by
    rw [mfderiv_scalar_eq_chart_fderiv (I := I) x g hxsrc hxint hg_mdiff
      ((chartModelBasis E) i)]
    rw [hcompose_eq.fderiv_eq]
    rw [trivToE_self_apply (I := I) x ((chartModelBasis E) i)]
    rw [chartIteratedPartialDeriv_def]
    rfl
  have hed_to_mfderiv : ∀ (h : M → ℝ) (v : TangentSpace I x),
      extDerivFun (I := I) h x v = (mfderiv I 𝓘(ℝ) h x : TangentSpace I x →L[ℝ] _) v := by
    intro h v; rfl
  rw [hed_to_mfderiv]
  rw [Filter.EventuallyEq.mfderiv_eq hev]
  exact hg_value

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma fderiv_chartE_chartBasisVec_self_eq_zero
    [I.Boundaryless]
    (x : M) (j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartE_section_repr (I := I) x
        (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm)
        (extChartAt I x x) = 0 := by
  classical
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  set U : Set E :=
    (extChartAt I x) '' ((extChartAt I x).source ∩
      (trivializationAt E (TangentSpace I) x).baseSet) with hU_def
  set V : Set E :=
    (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (trivializationAt E (TangentSpace I) x).baseSet with hV_def
  have hxV : extChartAt I x x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage]
    rw [(extChartAt I x).left_inv hxsrc_ext]
    exact hbase
  have hcont_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
    continuousOn_extChartAt_symm x
  have hopen_V : IsOpen V := by
    refine ContinuousOn.isOpen_inter_preimage hcont_symm
      (isOpen_extChartAt_target (I := I) x) ?_
    exact (trivializationAt E (TangentSpace I) x).open_baseSet
  have hconstOn : ∀ y ∈ V,
      (chartE_section_repr (I := I) x
          (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) y =
        (chartModelBasis E) j := by
    intro y hy
    obtain ⟨_hy_target, hy_pre⟩ := hy
    rw [Set.mem_preimage] at hy_pre
    exact chartE_section_repr_chartBasisVec_pullback_constOn (I := I) x j hy_pre
  have hev : (chartE_section_repr (I := I) x
      (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) =ᶠ[𝓝
        (extChartAt I x x)]
      (fun _ : E => ((chartModelBasis E) j : E)) := by
    filter_upwards [hopen_V.mem_nhds hxV] with y hy
    exact hconstOn y hy
  rw [hev.fderiv_eq]
  exact fderiv_const_apply ((chartModelBasis E) j)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma christoffelCorrection_self_basis_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    christoffelCorrection (I := I) g x x ((chartModelBasis E) j)
        ((chartModelBasis E) i) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) •
          (chartModelBasis E) k := by
  classical
  rw [christoffelCorrection_apply (I := I) g x x ((chartModelBasis E) j)
        ((chartModelBasis E) i)]
  rw [trivToE_self_apply (I := I) x ((chartModelBasis E) i)]
  rw [show (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
                ((chartModelBasis E).repr ((chartModelBasis E) j)) j' *
                chartChristoffel (I := I) g x i' j' k (extChartAt I x x)) •
              (chartModelBasis E) k) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) •
          (chartModelBasis E) k from ?_]
  classical
  have hrepr_basis : ∀ (r s : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr ((chartModelBasis E) r)) s =
        if r = s then (1 : ℝ) else 0 := by
    intro r s
    rw [Module.Basis.repr_self]
    by_cases h : r = s
    · subst h; simp
    · simp [h]
  rw [Finset.sum_eq_single i (fun i' _ hi'_ne_i => ?_) (fun hi_mem => ?_)]
  · rw [Finset.sum_eq_single j (fun j' _ hj'_ne_j => ?_) (fun hj_mem => ?_)]
    · have hrepr_ii : ((chartModelBasis E).repr ((chartModelBasis E) i)) i = 1 := by
        rw [hrepr_basis i i, if_pos rfl]
      have hrepr_jj : ((chartModelBasis E).repr ((chartModelBasis E) j)) j = 1 := by
        rw [hrepr_basis j j, if_pos rfl]
      rw [hrepr_ii, hrepr_jj]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring_nf
    · have hrepr_jj' : ((chartModelBasis E).repr ((chartModelBasis E) j)) j' = 0 := by
        rw [hrepr_basis j j', if_neg (fun h => hj'_ne_j h.symm)]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [hrepr_jj']
      simp
    · exact (hj_mem (Finset.mem_univ j)).elim
  · refine Finset.sum_eq_zero (fun j' _ => ?_)
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hrepr_ii' : ((chartModelBasis E).repr ((chartModelBasis E) i)) i' = 0 := by
      rw [hrepr_basis i i', if_neg (fun h => hi'_ne_i h.symm)]
    rw [hrepr_ii']
    simp
  · exact (hi_mem (Finset.mem_univ i)).elim

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma LeviCivita_chartBasisVec_self_basis_apply
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => chartBasisVecFiber (I := I) x j b) x
        ((chartModelBasis E) i) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) •
          (chartModelBasis E) k := by
  classical
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hY_at : MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) x j b)) x :=
    chartBasisVec_mdifferentiableAt_self (I := I) x j
  rw [LeviCivita_chart_apply (I := I) g x hx_good hY_at ((chartModelBasis E) i)]
  rw [chartLeviCivita_apply (I := I) g x
        (fun b : M => chartBasisVecFiber (I := I) x j b) hx_good
        ((chartModelBasis E) i)]
  rw [fderiv_chartE_chartBasisVec_self_eq_zero (I := I) x j]
  rw [show
        chartE_section_repr (I := I) x
          (fun b : M => chartBasisVecFiber (I := I) x j b) x =
        (chartModelBasis E) j from
      chartE_section_repr_chartBasisVec_apply (I := I) x j
        (FiberBundle.mem_baseSet_trivializationAt' x)]
  rw [christoffelCorrection_self_basis_apply (I := I) g x i j]
  simp only [ContinuousLinearMap.zero_apply, zero_add]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [(trivFromE (I := I) x x).map_smul]
  rw [trivFromE_self_apply (I := I) x ((chartModelBasis E) k)]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma extDerivFun_LeviCivita_chartBasisVec_self_basis
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    extDerivFun (I := I) f x
        ((LeviCivita (I := I) g).toFun
          (fun b : M => chartBasisVecFiber (I := I) x j b) x
          ((chartModelBasis E) i)) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) *
          partialDeriv (E := E) k (scalarOnE (I := I) x f) (extChartAt I x x) := by
  classical
  rw [LeviCivita_chartBasisVec_self_basis_apply (I := I) g x i j]
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hf_at : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  have h_distribute :
      extDerivFun (I := I) f x
          (∑ k : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x i j k (extChartAt I x x) •
              (chartModelBasis E) k) =
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x i j k (extChartAt I x x) *
            extDerivFun (I := I) f x ((chartModelBasis E) k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (extDerivFun (I := I) f x)
            (chartChristoffel (I := I) g x i j k (extChartAt I x x) •
              (chartModelBasis E) k) =
          chartChristoffel (I := I) g x i j k (extChartAt I x x) •
            (extDerivFun (I := I) f x) ((chartModelBasis E) k) from
        (extDerivFun (I := I) f x).map_smul
          (chartChristoffel (I := I) g x i j k (extChartAt I x x))
          ((chartModelBasis E) k)]
    rw [smul_eq_mul]
  have h_summand : ∀ (k : Fin (Module.finrank ℝ E)),
      extDerivFun (I := I) f x ((chartModelBasis E) k) =
        partialDeriv (E := E) k (scalarOnE (I := I) x f) (extChartAt I x x) := by
    intro k
    change (mfderiv I 𝓘(ℝ, ℝ) f x : TangentSpace I x →L[ℝ] _) ((chartModelBasis E) k) = _
    rw [mfderiv_scalar_eq_chart_fderiv (I := I) x f hxsrc hxint hf_at
      ((chartModelBasis E) k)]
    rw [trivToE_self_apply (I := I) x ((chartModelBasis E) k)]
    rfl
  refine h_distribute.trans ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [h_summand k]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartHessianMatrixIdentity_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    chartHessianMatrixIdentity (I := I) g f x := by
  classical
  intro i j
  rw [abstractHessian_apply]
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  set Y : Π b : M, TangentSpace I b :=
    fun b : M => chartBasisVecFiber (I := I) x j b with hY_def
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth := cotangentCov_extDerivFun_smooth (I := I) hf
    exact (hext_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := chartBasisVec_mdifferentiableAt_self (I := I) x j
  have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g) hθ_at hY_at
    ((chartModelBasis E) i)
  have hYx : Y x = (chartModelBasis E) j := by
    exact chartBasisVecFiber_self (I := I) x j
  rw [hYx] at hpair
  have hLHS := extDerivFun_pairing_chartBasisVec_apply_basis (I := I) hf x i j
  have hRHS_2 := extDerivFun_LeviCivita_chartBasisVec_self_basis (I := I) g hf x i j
  have hkey :
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x ((chartModelBasis E) i))
          ((chartModelBasis E) j) =
        extDerivFun (I := I) (fun b => θ b (Y b)) x ((chartModelBasis E) i) -
          θ x ((LeviCivita (I := I) g).toFun Y x ((chartModelBasis E) i)) := by
    linarith [hpair]
  rw [hkey]
  rw [hLHS, hRHS_2]
  rw [chartHessianTensor_def]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hessFun_eq_abstract [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      abstractHessian (I := I) g f x v w := by
  simpa only [abstractHessianBilin_apply] using
    hessFun_eq_abstractHessianBilin_of_matrix_identity (I := I) g f x
      (chartHessianMatrixIdentity_holds (I := I) g hf x) v w


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hessFun_eq_cov_grad [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x v) w := by
  rw [hessFun_eq_abstract (I := I) g hf x v w]
  exact (abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x v w).symm


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem hessFun_congr
    (g : SmoothRiemannianMetric I M) {f f' : M → ℝ} {x : M}
    (h : f =ᶠ[𝓝 x] f') :
    hessFun (I := I) g f x = hessFun (I := I) g f' x := by
  classical
  let y₀ : E := extChartAt I x x
  have hleft : (extChartAt I x).symm y₀ = x := by
    exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have htend : Filter.Tendsto (fun y : E => (extChartAt I x).symm y)
      (𝓝 y₀) (𝓝 x) := by
    have hcont : ContinuousAt (fun y : E => (extChartAt I x).symm y) y₀ := by
      simpa only [y₀] using continuousAt_extChartAt_symm (I := I) x
    simpa only [ContinuousAt, hleft, Function.comp_def] using hcont
  have hscalar : scalarOnE (I := I) x f =ᶠ[𝓝 y₀]
      scalarOnE (I := I) x f' := by
    simpa only [scalarOnE_def, Function.comp_apply] using htend.eventually h
  have hpartial (j : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) j (scalarOnE (I := I) x f) =ᶠ[𝓝 y₀]
        partialDeriv (E := E) j (scalarOnE (I := I) x f') := by
    filter_upwards [hscalar.fderiv (𝕜 := ℝ)] with y hy
    unfold partialDeriv
    rw [hy]
  have hfirst (j : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) j (scalarOnE (I := I) x f) y₀ =
        partialDeriv (E := E) j (scalarOnE (I := I) x f') y₀ := by
    unfold partialDeriv
    rw [hscalar.fderiv_eq (𝕜 := ℝ)]
  have hiter (i j : Fin (Module.finrank ℝ E)) :
      chartIteratedPartialDeriv (I := I) x f i j y₀ =
        chartIteratedPartialDeriv (I := I) x f' i j y₀ := by
    change (fderiv ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) x f)) y₀)
          ((chartModelBasis E) i) =
      (fderiv ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) x f')) y₀)
          ((chartModelBasis E) i)
    rw [(hpartial j).fderiv_eq (𝕜 := ℝ)]
  have htensor (i j : Fin (Module.finrank ℝ E)) :
      chartHessianTensor (I := I) g x f i j x =
        chartHessianTensor (I := I) g x f' i j x := by
    simp only [chartHessianTensor_def]
    change chartIteratedPartialDeriv (I := I) x f i j y₀ - _ =
      chartIteratedPartialDeriv (I := I) x f' i j y₀ - _
    rw [hiter i j]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hfirst k]
  ext v w
  rw [hessFun_apply, hessFun_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [htensor i j]


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hessFun_eq_cov_local [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {U : Set M} {x : M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ) ∞ f U) (hx : x ∈ U)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x v) w := by
  obtain ⟨F, hF, hFf⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  have hgrad : (fun b => gradFun (I := I) g F b) =ᶠ[𝓝 x]
      (fun b => gradFun (I := I) g f b) := by
    filter_upwards [hFf.eventuallyEq_nhds] with y hy
    unfold gradFun
    rw [hy.mfderiv_eq]
  have hgrad_total :
      (T% fun b => gradFun (I := I) g F b) =ᶠ[𝓝 x]
        (T% fun b => gradFun (I := I) g f b) := by
    filter_upwards [hgrad] with y hy
    change TotalSpace.mk' E y (gradFun (I := I) g F y) =
      TotalSpace.mk' E y (gradFun (I := I) g f y)
    rw [hy]
  have hgradF_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% fun b => gradFun (I := I) g F b) := by
    exact gradFun_contMDiff_total_section (I := I) g hF
  have hgradF_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% fun b => gradFun (I := I) g F b) x := hgradF_smooth x
  have hgradf_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% fun b => gradFun (I := I) g f b) x :=
    hgradF_at.congr_of_eventuallyEq hgrad_total.symm
  have hcov :
      (LeviCivita (I := I) g).toFun
          (fun b => gradFun (I := I) g F b) x =
        (LeviCivita (I := I) g).toFun
          (fun b => gradFun (I := I) g f b) x :=
    (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hgradF_at.mdifferentiableAt (by simp))
      (hgradf_at.mdifferentiableAt (by simp)) Filter.univ_mem hgrad
  calc
    hessFun (I := I) g f x v w = hessFun (I := I) g F x v w := by
      exact congrArg (fun B => B v w) (hessFun_congr (I := I) g hFf.symm)
    _ = g.inner x ((LeviCivita (I := I) g).toFun
          (fun b => gradFun (I := I) g F b) x v) w :=
      hessFun_eq_cov_grad (I := I) g hF x v w
    _ = g.inner x ((LeviCivita (I := I) g).toFun
          (fun b => gradFun (I := I) g f b) x v) w := by rw [hcov]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma extDerivFun_chartBasisVec_alpha_apply_of_mem
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) α j b) =
      partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α b) := by
  classical
  have hf_at : MDiffAt f b := (hf b).mdifferentiableAt (by simp)
  have hb_chart : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  change (mfderiv I 𝓘(ℝ, ℝ) f b) (chartBasisVecFiber (I := I) α j b) = _
  exact mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α hf_at
    hb_chart hb_int j

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma extDerivFun_chartBasisVec_alpha_eventuallyEq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun b : M => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) α j b)) =ᶠ[𝓝 x]
      (fun b : M =>
        partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α b)) := by
  classical
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hnhd : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 x := hopen.mem_nhds hx
  filter_upwards [hnhd] with b hb
  exact extDerivFun_chartBasisVec_alpha_apply_of_mem (I := I) hf α j hb

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma extDerivFun_pairing_chartBasisVec_alpha_apply
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    extDerivFun (I := I) (fun b => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) α j b)) x
        (chartBasisVecFiber (I := I) α i x) =
      chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) := by
  classical
  have hev := extDerivFun_chartBasisVec_alpha_eventuallyEq (I := I) hf α j hx
  have hf_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hf_smooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf_smooth_target.mono interior_subset
  have hopen_int : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxchart
  have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  set g : M → ℝ :=
    fun b => partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α b) with hg_def
  have hu_smooth_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α x) :=
    hf_smooth_int.contDiffAt (hopen_int.mem_nhds hxint)
  have hfd_contDiffOn : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior ((extChartAt I α).target : Set E)) :=
    hf_smooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hfd_contDiffAt : ContDiffAt ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (extChartAt I α x) :=
    hfd_contDiffOn.contDiffAt (hopen_int.mem_nhds hxint)
  have hPD_contDiffAt : ContDiffAt ℝ ∞
      (partialDeriv (E := E) j (scalarOnE (I := I) α f)) (extChartAt I α x) := by
    have hcomp_eq :
        partialDeriv (E := E) j (scalarOnE (I := I) α f) =
          (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j) :
            (E →L[ℝ] ℝ) →L[ℝ] ℝ) ∘
          (fderiv ℝ (scalarOnE (I := I) α f)) := by
      funext y; rfl
    rw [hcomp_eq]
    exact (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j)).contDiff.contDiffAt.comp
      (extChartAt I α x) hfd_contDiffAt
  have hphi_mdiff : MDiffAt (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  have hPD_mdiff_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (partialDeriv (E := E) j (scalarOnE (I := I) α f)) (extChartAt I α x) := by
    have hd : DifferentiableAt ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) (extChartAt I α x) :=
      hPD_contDiffAt.differentiableAt (by simp)
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hd
  have hg_mdiff : MDiffAt g x :=
    hPD_mdiff_at.comp x hphi_mdiff
  have htgt_nhds : ((extChartAt I α).target : Set E) ∈ 𝓝 (extChartAt I α x) := by
    refine mem_nhds_iff.mpr ?_
    refine ⟨interior ((extChartAt I α).target : Set E),
      interior_subset, hopen_int, hxint⟩
  have hg_value :
      (mfderiv I 𝓘(ℝ) g x : TangentSpace I x →L[ℝ] _)
          (chartBasisVecFiber (I := I) α i x) =
        chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) := by
    rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α
        hg_mdiff hxchart hxint i]
    have hscalar_eq : (scalarOnE (I := I) α g) =ᶠ[𝓝 (extChartAt I α x)]
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) := by
      filter_upwards [htgt_nhds] with y hy
      change g ((extChartAt I α).symm y) =
        partialDeriv (E := E) j (scalarOnE (I := I) α f) y
      change partialDeriv (E := E) j (scalarOnE (I := I) α f)
          (extChartAt I α ((extChartAt I α).symm y)) =
        partialDeriv (E := E) j (scalarOnE (I := I) α f) y
      rw [(extChartAt I α).right_inv hy]
    change partialDeriv (E := E) i (scalarOnE (I := I) α g) (extChartAt I α x) =
        chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x)
    have h_pd : partialDeriv (E := E) i (scalarOnE (I := I) α g) (extChartAt I α x) =
        partialDeriv (E := E) i
          (partialDeriv (E := E) j (scalarOnE (I := I) α f))
          (extChartAt I α x) := by
      change (fderiv ℝ (scalarOnE (I := I) α g) (extChartAt I α x))
          ((chartModelBasis E) i) =
        (fderiv ℝ (partialDeriv (E := E) j (scalarOnE (I := I) α f))
            (extChartAt I α x))
          ((chartModelBasis E) i)
      congr 1
      exact Filter.EventuallyEq.fderiv_eq hscalar_eq
    rw [h_pd]
    rw [chartIteratedPartialDeriv_def]
  have hed_to_mfderiv : ∀ (h : M → ℝ) (v : TangentSpace I x),
      extDerivFun (I := I) h x v = (mfderiv I 𝓘(ℝ) h x : TangentSpace I x →L[ℝ] _) v := by
    intro h v; rfl
  rw [hed_to_mfderiv]
  rw [Filter.EventuallyEq.mfderiv_eq hev]
  exact hg_value

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartBasisVec_alpha_mdifferentiableAt
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) α j b)) x := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hcontMDiff_on := chartBasisVec_contMDiffOn (I := I) α j
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hcontMDiff_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α j) x :=
    (hcontMDiff_on x hbase).contMDiffAt (hopen.mem_nhds hbase)
  exact hcontMDiff_at.mdifferentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma fderiv_chartE_chartBasisVec_alpha_eq_zero [I.Boundaryless]
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    fderiv ℝ (chartE_section_repr (I := I) α
        (fun b : M => chartBasisVecFiber (I := I) α j b) ∘ (extChartAt I α).symm)
        (extChartAt I α x) = 0 := by
  classical
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxchart
  have hxtgt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc_ext
  have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  set V : Set E :=
    (extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet with hV_def
  have hxV : extChartAt I α x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage]
    rw [(extChartAt I α).left_inv hxsrc_ext]
    exact hbase
  have hcont_symm : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have hopen_V : IsOpen V := by
    refine ContinuousOn.isOpen_inter_preimage hcont_symm
      (isOpen_extChartAt_target (I := I) α) ?_
    exact (trivializationAt E (TangentSpace I) α).open_baseSet
  have hconstOn : ∀ y ∈ V,
      (chartE_section_repr (I := I) α
          (fun b : M => chartBasisVecFiber (I := I) α j b) ∘ (extChartAt I α).symm) y =
        (chartModelBasis E) j := by
    intro y hy
    obtain ⟨_hy_target, hy_pre⟩ := hy
    rw [Set.mem_preimage] at hy_pre
    change trivToE (I := I) α ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)) =
      (chartModelBasis E) j
    have heq : chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y) =
        trivFromE (I := I) α ((extChartAt I α).symm y) ((chartModelBasis E) j) := rfl
    rw [heq]
    exact trivToE_trivFromE (I := I) α hy_pre ((chartModelBasis E) j)
  have hev : (chartE_section_repr (I := I) α
      (fun b : M => chartBasisVecFiber (I := I) α j b) ∘ (extChartAt I α).symm) =ᶠ[𝓝
        (extChartAt I α x)]
      (fun _ : E => ((chartModelBasis E) j : E)) := by
    filter_upwards [hopen_V.mem_nhds hxV] with y hy
    exact hconstOn y hy
  rw [hev.fderiv_eq]
  exact fderiv_const_apply ((chartModelBasis E) j)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartE_section_repr_chartBasisVec_alpha_apply
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartE_section_repr (I := I) α
        (fun b : M => chartBasisVecFiber (I := I) α j b) x =
      (chartModelBasis E) j := by
  classical
  unfold chartE_section_repr
  change trivToE (I := I) α x (chartBasisVecFiber (I := I) α j x) =
    (chartModelBasis E) j
  have heq : chartBasisVecFiber (I := I) α j x =
      trivFromE (I := I) α x ((chartModelBasis E) j) := rfl
  rw [heq]
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  exact trivToE_trivFromE (I := I) α hbase ((chartModelBasis E) j)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma christoffelCorrection_alpha_basis_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
        (chartBasisVecFiber (I := I) α i x) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k (extChartAt I α x) •
          (chartModelBasis E) k := by
  classical
  rw [christoffelCorrection_apply (I := I) g α x ((chartModelBasis E) j)
        (chartBasisVecFiber (I := I) α i x)]
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have h_round : trivToE (I := I) α x (chartBasisVecFiber (I := I) α i x) =
      (chartModelBasis E) i := by
    have heq : chartBasisVecFiber (I := I) α i x =
        trivFromE (I := I) α x ((chartModelBasis E) i) := rfl
    rw [heq]
    exact trivToE_trivFromE (I := I) α hbase ((chartModelBasis E) i)
  rw [h_round]
  have hrepr_basis : ∀ (r s : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr ((chartModelBasis E) r)) s =
        if r = s then (1 : ℝ) else 0 := by
    intro r s
    rw [Module.Basis.repr_self]
    by_cases h : r = s
    · subst h; simp
    · simp [h]
  rw [Finset.sum_eq_single i (fun i' _ hi'_ne_i => ?_) (fun hi_mem => ?_)]
  · rw [Finset.sum_eq_single j (fun j' _ hj'_ne_j => ?_) (fun hj_mem => ?_)]
    · have hrepr_ii : ((chartModelBasis E).repr ((chartModelBasis E) i)) i = 1 := by
        rw [hrepr_basis i i, if_pos rfl]
      have hrepr_jj : ((chartModelBasis E).repr ((chartModelBasis E) j)) j = 1 := by
        rw [hrepr_basis j j, if_pos rfl]
      rw [hrepr_ii, hrepr_jj]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring_nf
    · have hrepr_jj' : ((chartModelBasis E).repr ((chartModelBasis E) j)) j' = 0 := by
        rw [hrepr_basis j j', if_neg (fun h => hj'_ne_j h.symm)]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [hrepr_jj']
      simp
    · exact (hj_mem (Finset.mem_univ j)).elim
  · refine Finset.sum_eq_zero (fun j' _ => ?_)
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hrepr_ii' : ((chartModelBasis E).repr ((chartModelBasis E) i)) i' = 0 := by
      rw [hrepr_basis i i', if_neg (fun h => hi'_ne_i h.symm)]
    rw [hrepr_ii']
    simp
  · exact (hi_mem (Finset.mem_univ i)).elim

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma LeviCivita_chartBasisVec_alpha_basis_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => chartBasisVecFiber (I := I) α j b) x
        (chartBasisVecFiber (I := I) α i x) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k (extChartAt I α x) •
          chartBasisVecFiber (I := I) α k x := by
  classical
  have hY_at : MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) α j b)) x :=
    chartBasisVec_alpha_mdifferentiableAt (I := I) α j hx
  rw [LeviCivita_chart_apply (I := I) g α hx hY_at
        (chartBasisVecFiber (I := I) α i x)]
  rw [chartLeviCivita_apply (I := I) g α
        (fun b : M => chartBasisVecFiber (I := I) α j b) hx
        (chartBasisVecFiber (I := I) α i x)]
  rw [fderiv_chartE_chartBasisVec_alpha_eq_zero (I := I) α j hx]
  rw [show
        chartE_section_repr (I := I) α
          (fun b : M => chartBasisVecFiber (I := I) α j b) x =
        (chartModelBasis E) j from
      chartE_section_repr_chartBasisVec_alpha_apply (I := I) α j hx]
  simp only [ContinuousLinearMap.zero_apply, zero_add]
  rw [christoffelCorrection_alpha_basis_apply (I := I) g α i j hx]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [(trivFromE (I := I) α x).map_smul]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma extDerivFun_LeviCivita_chartBasisVec_alpha_basis [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    extDerivFun (I := I) f x
        ((LeviCivita (I := I) g).toFun
          (fun b : M => chartBasisVecFiber (I := I) α j b) x
          (chartBasisVecFiber (I := I) α i x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k (extChartAt I α x) *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α i j hx]
  have h_distribute :
      extDerivFun (I := I) f x
          (∑ k : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i j k (extChartAt I α x) •
              chartBasisVecFiber (I := I) α k x) =
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k (extChartAt I α x) *
            extDerivFun (I := I) f x (chartBasisVecFiber (I := I) α k x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (extDerivFun (I := I) f x)
            (chartChristoffel (I := I) g α i j k (extChartAt I α x) •
              chartBasisVecFiber (I := I) α k x) =
          chartChristoffel (I := I) g α i j k (extChartAt I α x) •
            (extDerivFun (I := I) f x) (chartBasisVecFiber (I := I) α k x) from
        (extDerivFun (I := I) f x).map_smul
          (chartChristoffel (I := I) g α i j k (extChartAt I α x))
          (chartBasisVecFiber (I := I) α k x)]
    rw [smul_eq_mul]
  have h_summand : ∀ (k : Fin (Module.finrank ℝ E)),
      extDerivFun (I := I) f x (chartBasisVecFiber (I := I) α k x) =
        partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro k
    exact extDerivFun_chartBasisVec_alpha_apply_of_mem (I := I) hf α k hx
  refine h_distribute.trans ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [h_summand k]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartAlphaMatrixIdentity_holds_on_goodSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      chartHessianTensor (I := I) g α f i j x := by
  classical
  rw [abstractHessian_apply]
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  set Y : Π b : M, TangentSpace I b :=
    fun b : M => chartBasisVecFiber (I := I) α j b with hY_def
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth := cotangentCov_extDerivFun_smooth (I := I) hf
    exact (hext_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x :=
    chartBasisVec_alpha_mdifferentiableAt (I := I) α j hx
  have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g) hθ_at hY_at
    (chartBasisVecFiber (I := I) α i x)
  have hYx : Y x = chartBasisVecFiber (I := I) α j x := rfl
  have hkey :
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x
            (chartBasisVecFiber (I := I) α i x))
          (chartBasisVecFiber (I := I) α j x) =
        extDerivFun (I := I) (fun b => θ b (Y b)) x
            (chartBasisVecFiber (I := I) α i x) -
          θ x ((LeviCivita (I := I) g).toFun Y x
            (chartBasisVecFiber (I := I) α i x)) := by
    rw [← hYx]
    linarith [hpair]
  rw [hkey]
  have hLHS := extDerivFun_pairing_chartBasisVec_alpha_apply (I := I) hf α i j hx
  have hRHS_2 := extDerivFun_LeviCivita_chartBasisVec_alpha_basis (I := I) g hf α i j hx
  rw [hLHS, hRHS_2]
  rw [chartHessianTensor_def]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartAlphaMatrixIdentity_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      chartHessianTensor (I := I) g α f i j x := by
  classical
  have hx_src_ext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hx_tgt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_src_ext
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_tgt
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨hx_src_ext, hbase, hx_int⟩
  exact chartAlphaMatrixIdentity_holds_on_goodSet
    (I := I) (M := M) g α hf hx_good i j

end Connection
end Integral
end DifferentialGeometry
