import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Operator.HessianTrace


noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

def connLaplacian_function [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  Δ_g (I := I) g hf

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp] lemma connLaplacian_function_def [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = Δ_g (I := I) g hf x := rfl

def connLaplacian_vector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x) V x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma connLaplacian_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    connLaplacian_vector (I := I) g V x =
      localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        V x := rfl

def connLaplacian_oneForm
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((cotangentCov (LeviCivita (I := I) g)).toFun
      (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
        (smoothOrthoFrame (I := I) g x i b)) x
        (smoothOrthoFrame (I := I) g x i x) -
      (cotangentCov (LeviCivita (I := I) g)).toFun θ x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma connLaplacian_oneForm_def
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    connLaplacian_oneForm (I := I) g θ x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((cotangentCov (LeviCivita (I := I) g)).toFun
          (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
            (smoothOrthoFrame (I := I) g x i b)) x
            (smoothOrthoFrame (I := I) g x i x) -
          (cotangentCov (LeviCivita (I := I) g)).toFun θ x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem connLaplacian_function_eq_laplaceBeltrami [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    connLaplacian_function (I := I) g hf = Δ_g (I := I) g hf := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connLaplacian_function_eq_chartHessTrace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = chartHessTrace (I := I) g f x := by
  rw [connLaplacian_function_def]
  exact (chartHessTrace_eq_laplacian_pointwise_of_boundaryless
    (I := I) g hf x).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem connLaplacian_function_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (connLaplacian_function (I := I) g hf) :=
  Δ_g_contMDiff (I := I) g hf

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem connLaplacian_function_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    connLaplacian_function (I := I) g (hf.add hh) x =
      connLaplacian_function (I := I) g hf x +
        connLaplacian_function (I := I) g hh x := by
  rw [connLaplacian_function_def, connLaplacian_function_def,
      connLaplacian_function_def]
  exact Δ_g_add (I := I) g hf hh x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp] theorem connLaplacian_function_const [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    connLaplacian_function (I := I) g
      (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c)) x = 0 := by
  rw [connLaplacian_function_def]
  exact Δ_g_const (I := I) g c x

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) := by
  rw [connLaplacian_vector_def]
  exact localConnLap_vector_grad_inner_eq_hessian_diff (I := I) g hf hw
    (smoothOrthoFrame (I := I) g x)
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) x

omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) := by
  unfold connLaplacian_vector
  exact heart_of_bochner_smoothOrthoFrame (I := I) g hf x hInner

omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    (I := I) g hf x hInner

omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_iff_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) ↔
      ∀ w : TangentSpace I x,
        g.inner x (connLaplacian_vector (I := I) g
                    (fun b => gradFun (I := I) g f b) x) w =
          g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
            g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w := by
  classical
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · rw [h]
    rw [show g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
      by rw [map_add, ContinuousLinearMap.add_apply]]
  · exact connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
      (I := I) g hf x h

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_inner_hessian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) :=
  connLaplacian_grad_inner (I := I) g hf hw x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_hessian_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (Y x)) (X x) :=
  inner_cov_gradFun_symm (I := I) g hf hX hY

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_grad_curvature_term [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {B w : Π b : M, TangentSpace I b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    g.inner x (riemannSec (LeviCivita (I := I) g) B w
                (fun b => gradFun (I := I) g f b) x) (B x) =
      - g.inner x (gradFun (I := I) g f x)
          (riemannSec (LeviCivita (I := I) g) B w B x) :=
  inner_riemannSec_gradFun_skew_symm (I := I) g hf hB hw

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_orthonormal_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal_at_center (I := I) g x i j

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem smoothOrthoFrame_isSmooth
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x i)) :=
  smoothOrthoFrame_smooth (I := I) g x i

def frobeniusSq_grad_vector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    g.inner x
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma frobeniusSq_grad_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    frobeniusSq_grad_vector (I := I) g V x =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x))
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x)) := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
lemma frobeniusSq_grad_vector_nonneg
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    0 ≤ frobeniusSq_grad_vector (I := I) g V x := by
  unfold frobeniusSq_grad_vector
  refine Finset.sum_nonneg ?_
  intro i _
  set v : TangentSpace I x :=
    (LeviCivita (I := I) g).toFun V x
      (smoothOrthoFrame (I := I) g x i x) with hv_def
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt (g.pos x v hv)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem connLaplacian_inner_self_of_trace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (_hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
          2 * frobeniusSq_grad_vector (I := I) g V x) :
    connLaplacian_function (I := I) g hgVV x =
      2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
        2 * frobeniusSq_grad_vector (I := I) g V x := by
  rw [connLaplacian_function_def]
  exact hLeibniz

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma extDerivFun_inner_self [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) (x : M)
    (X : TangentSpace I x) :
    extDerivFun (I := I) (fun b => g.inner b (V b) (V b)) x X =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x X) (V x) := by
  classical
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hV_at hV_at X
  have hext_eq : extDerivFun (I := I) (fun b => g.inner b (V b) (V b)) x X =
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (V b) (V b)) x) X := rfl
  rw [hext_eq, hmc]
  rw [g.symm x (V x) ((LeviCivita (I := I) g).toFun V x X)]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma extDerivFun_inner_self_eq_globally [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (X : Π b : M, TangentSpace I b) :
    (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (V b') (V b')) b
        (X b)) =
      (fun b : M => 2 * g.inner b
        ((LeviCivita (I := I) g).toFun V b (X b)) (V b)) := by
  funext b
  exact extDerivFun_inner_self (I := I) g hV b (X b)

end Connection
end Integral
end DifferentialGeometry
