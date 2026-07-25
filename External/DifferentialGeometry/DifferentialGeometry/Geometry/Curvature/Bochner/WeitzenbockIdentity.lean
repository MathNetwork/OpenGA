import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.HessFrobenius
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace


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

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leibniz_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V W : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    {x : M} (X : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (V b) (W b)) x) X =
      g.inner x ((LeviCivita (I := I) g).toFun V x X) (W x) +
        g.inner x (V x) ((LeviCivita (I := I) g).toFun W x X) := by
  classical
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  exact (LeviCivita_isMetricCompatible (I := I) g).apply hV_at hW_at X

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leibniz_inner_globally [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V W : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (X : Π b : M, TangentSpace I b) :
    (fun b : M => (mfderiv I 𝓘(ℝ) (fun b' : M => g.inner b' (V b') (W b')) b)
        (X b)) =
      (fun b : M =>
        g.inner b ((LeviCivita (I := I) g).toFun V b (X b)) (W b) +
          g.inner b (V b) ((LeviCivita (I := I) g).toFun W b (X b))) := by
  funext b
  exact leibniz_inner (I := I) g hV hW (X b)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem laplacian_inner_self_half [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (_hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
          2 * frobeniusSq_grad_vector (I := I) g V x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g hgVV x =
      g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
        frobeniusSq_grad_vector (I := I) g V x := by
  rw [hLeibniz]
  ring

omit [SigmaCompactSpace M] in
theorem laplacian_grad_eq_grad_laplacian_plus_ricciSharp [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
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

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem laplacian_grad_inner_eq_grad_laplacian_plus_ricci [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w)
    (w : TangentSpace I x) :
    g.inner x (connLaplacian_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x) w =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
        ricciTensor (I := I) g x (gradFun (I := I) g f x) w := by
  rw [hInner w, inner_ricciSharp (I := I) g x (gradFun (I := I) g f x) w]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem bochner_abstract [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    (1 / 2 : ℝ) * Δ_g (I := I) g hgVV x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x := by
  classical
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g f b)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB2 :=
    laplacian_inner_self_half (I := I) g h_grad_smooth hgVV x hLeibniz
  rw [hB2]
  have hB3 :=
    laplacian_grad_inner_eq_grad_laplacian_plus_ricci (I := I) g hf x hInner
      (gradFun (I := I) g f x)
  rw [hB3]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem bochner_abstract_of_heart_of_bochner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hHeart :
      connLaplacian_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) :
    (1 / 2 : ℝ) * Δ_g (I := I) g hgVV x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x := by
  classical
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g f b)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB2 :=
    laplacian_inner_self_half (I := I) g h_grad_smooth hgVV x hLeibniz
  rw [hB2]
  rw [hHeart]
  rw [show g.inner x
        (gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x))
        (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
      g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x))
        (gradFun (I := I) g f x) from by
    rw [map_add, ContinuousLinearMap.add_apply]]
  rw [inner_ricciSharp (I := I) g x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x)]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normGradSq_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (gradFun (I := I) g f b)
        (gradFun (I := I) g f b)) := by
  exact normGradSqFun_contMDiff (I := I) g hf

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem bochner_abstract_packaged [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hLeibniz :
      Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_abstract (I := I) g hf (normGradSq_contMDiff (I := I) g hf) x
    hLeibniz hInner

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem bochner_abstract_of_heart_of_bochner_packaged [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hLeibniz :
      Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hHeart :
      connLaplacian_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_abstract_of_heart_of_bochner (I := I) g hf
    (normGradSq_contMDiff (I := I) g hf) x hLeibniz hHeart

def IsChartOrthonormalAt
    (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  ∀ i j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0

@[reducible] def IsLeibnizTraceAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b)
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M) : Prop :=
  Δ_g (I := I) g hgVV x =
    2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
      2 * frobeniusSq_grad_vector (I := I) g V x

@[reducible] def IsHeartOfBochnerInnerAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) : Prop :=
  ∀ w : TangentSpace I x,
    g.inner x (connLaplacian_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x) w =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
        g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w

structure BochnerReductionAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) : Prop where
  leibniz : IsLeibnizTraceAt (I := I) g
    (fun b => gradFun (I := I) g f b) (normGradSq_contMDiff (I := I) g hf) x
  heart : IsHeartOfBochnerInnerAt (I := I) g hf x

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem bochner_pointwise_abstract_of_reduction [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hRed : BochnerReductionAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_abstract_packaged (I := I) g hf x hRed.leibniz hRed.heart

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem bochner_pointwise_abstract [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hLeibniz :
      IsLeibnizTraceAt (I := I) g
        (fun b => gradFun (I := I) g f b)
        (normGradSq_contMDiff (I := I) g hf) x)
    (hInner : IsHeartOfBochnerInnerAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_pointwise_abstract_of_reduction (I := I) g hf x ⟨hLeibniz, hInner⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem sum_abstractHessian_orthonormal_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E),
      abstractHessian (I := I) g f x (B i) (B i) =
      Δ_g (I := I) g hf x := by
  classical
  have htrace := orthonormal_basis_bilin_trace (I := I) g x
    (abstractHessian (I := I) g f x) B hB
  rw [htrace]
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          abstractHessian (I := I) g f x ((chartModelBasis E) k)
            ((chartModelBasis E) l)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartHessianTensor (I := I) g x f k l x from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [hM k l]]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartHessianTensor (I := I) g x f k l x) =
      chartHessTrace (I := I) g f x from rfl]
  exact chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x

theorem sum_abstractHessian_smoothOrthoFrame_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
      abstractHessian (I := I) g f x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x i x) =
      Δ_g (I := I) g hf x :=
  sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf x
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractHessian_innerSelf_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    {Y : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (V b) (V b)))
    (x : M) :
    abstractHessian (I := I) g
        (fun b : M => g.inner b (V b) (V b)) x (Y x) (Y x) =
      2 * (g.inner x ((LeviCivita (I := I) g).toFun
              (covApply (LeviCivita (I := I) g) Y V) x (Y x)) (V x) -
            g.inner x ((LeviCivita (I := I) g).toFun V x
              ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x)) +
        2 * g.inner x
          ((LeviCivita (I := I) g).toFun V x (Y x))
          ((LeviCivita (I := I) g).toFun V x (Y x)) := by
  classical
  set f' : M → ℝ := fun b => g.inner b (V b) (V b) with hf'_def
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f' with hθ_def
  have hθ_at : MDiffAtCotangent θ x := by
    have hθ_smooth := cotangentCov_extDerivFun_smooth (I := I) hgVV
    exact (hθ_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hdual := cotangentCov_dualPairing (LeviCivita (I := I) g) hθ_at hY_at (Y x)
  have habsH : abstractHessian (I := I) g f' x (Y x) (Y x) =
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x (Y x)) (Y x) := rfl
  rw [habsH]
  have h_isolate :
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x (Y x)) (Y x) =
        extDerivFun (I := I) (fun b : M => θ b (Y b)) x (Y x) -
          θ x ((LeviCivita (I := I) g).toFun Y x (Y x)) := by
    linarith [hdual]
  rw [h_isolate]
  have hθY_eq : ∀ b : M, θ b (Y b) =
      2 * g.inner b ((LeviCivita (I := I) g).toFun V b (Y b)) (V b) := by
    intro b
    exact extDerivFun_inner_self (I := I) g hV b (Y b)
  have h_func_eq : (fun b : M => θ b (Y b)) =
      (fun b : M => 2 * g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) := by
    funext b
    exact hθY_eq b
  rw [h_func_eq]
  have h_2_factor :
      extDerivFun (I := I)
        (fun b : M => 2 * g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) =
      2 * extDerivFun (I := I)
        (fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) := by
    have hP_smooth0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (covApply (LeviCivita (I := I) g) Y V)) :=
      contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hY hV)
    have h_inner_at : MDiffAt
        (fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x := by
      have hsmooth :
          ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun b : M => g.inner b (covApply (LeviCivita (I := I) g) Y V b) (V b)) := by
        have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
            (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
              b (g.inner b)) :=
          g.contMDiff
        have happ :
            ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
              (fun m : M => (⟨m,
                  g.inner m (covApply (LeviCivita (I := I) g) Y V m) (V m)⟩ :
                    TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
          ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
            (b := id) hg hP_smooth0 hV
        intro m
        have hpm := happ m
        rw [Bundle.contMDiffAt_totalSpace] at hpm
        exact hpm.2
      have hsmooth_eq : (fun b : M => g.inner b
            ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) =
          (fun b : M => g.inner b (covApply (LeviCivita (I := I) g) Y V b) (V b)) := rfl
      rw [hsmooth_eq]
      exact (hsmooth x).mdifferentiableAt (by simp)
    have h_mul : (fun b : M => 2 * g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) =
        ((2 : ℝ) • fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) := by
      funext b
      change (2 : ℝ) * _ = (2 : ℝ) • _
      rw [smul_eq_mul]
    rw [h_mul]
    change (mfderiv I 𝓘(ℝ, ℝ) ((2 : ℝ) • fun b : M => g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x) (Y x) = _
    rw [const_smul_mfderiv h_inner_at (2 : ℝ)]
    simp [smul_eq_mul]
    rfl
  rw [h_2_factor]
  set P : Π b : M, TangentSpace I b :=
    fun b : M => (LeviCivita (I := I) g).toFun V b (Y b) with hP_def
  have hP_eq_covApply : P = covApply (LeviCivita (I := I) g) Y V := rfl
  have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P) := by
    rw [hP_eq_covApply]
    exact contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hY hV)
  have hP_at : MDiffAt (T% P) x := (hP_smooth x).mdifferentiableAt (by simp)
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hV_at (Y x)
  have h_extDerivFun_eq :
      extDerivFun (I := I) (fun b : M => g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun P x (Y x)) (V x) +
        g.inner x (P x) ((LeviCivita (I := I) g).toFun V x (Y x)) := hmc
  have hPx : P x = (LeviCivita (I := I) g).toFun V x (Y x) := rfl
  rw [hPx] at h_extDerivFun_eq
  rw [h_extDerivFun_eq]
  have hLCP : (LeviCivita (I := I) g).toFun P x (Y x) =
      (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y V) x (Y x) :=
    by rw [hP_eq_covApply]
  rw [hLCP]
  have hθ_x_LC : θ x ((LeviCivita (I := I) g).toFun Y x (Y x)) =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x
        ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x) := by
    change extDerivFun (I := I) f' x ((LeviCivita (I := I) g).toFun Y x (Y x)) =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x
        ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x)
    exact extDerivFun_inner_self (I := I) g hV x
      ((LeviCivita (I := I) g).toFun Y x (Y x))
  rw [hθ_x_LC]
  ring

theorem leibnizTraceIdentity_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    IsLeibnizTraceAt (I := I) g
      (fun b => gradFun (I := I) g f b)
      (normGradSq_contMDiff (I := I) g hf) x := by
  classical
  change Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
    2 * g.inner x (connLaplacian_vector (I := I) g
                    (fun b => gradFun (I := I) g f b) x)
                   (gradFun (I := I) g f x) +
      2 * frobeniusSq_grad_vector (I := I) g
            (fun b => gradFun (I := I) g f b) x
  set V : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hV_def
  set hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
    (fun b : M => g.inner b (V b) (V b)) := normGradSq_contMDiff (I := I) g hf with hgVV_def
  have hV_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have h_trace := sum_abstractHessian_smoothOrthoFrame_eq_laplacian (I := I) g hgVV x
  rw [← h_trace]
  rw [show ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g
          (fun b : M => g.inner b (V b) (V b)) x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (2 * (g.inner x ((LeviCivita (I := I) g).toFun
                (covApply (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) V) x
                  (smoothOrthoFrame (I := I) g x i x)) (V x) -
              g.inner x ((LeviCivita (I := I) g).toFun V x
                ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g x i) x
                  (smoothOrthoFrame (I := I) g x i x))) (V x)) +
          2 * g.inner x
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x))
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact abstractHessian_innerSelf_apply (I := I) g hV_smooth
      (smoothOrthoFrame_smooth (I := I) g x i) hgVV x]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h_frob : ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x))
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x)) =
      frobeniusSq_grad_vector (I := I) g V x := rfl
  rw [h_frob]
  have h_LCV : ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) V) x
                (smoothOrthoFrame (I := I) g x i x)) (V x) -
            g.inner x ((LeviCivita (I := I) g).toFun V x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x))) (V x)) =
      g.inner x (connLaplacian_vector (I := I) g V x) (V x) := by
    rw [show g.inner x (connLaplacian_vector (I := I) g V x) (V x) =
      g.inner x (∑ i : Fin (Module.finrank ℝ E),
        ((LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g)
              (smoothOrthoFrame (I := I) g x i) V) x
              (smoothOrthoFrame (I := I) g x i x) -
          (LeviCivita (I := I) g).toFun V x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x)))) (V x) from rfl]
    rw [map_sum]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_sub]
    rw [ContinuousLinearMap.sub_apply]
  rw [h_LCV]

theorem bochner_pointwise_abstract_via_orthonormalTrace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hPerSummand_Leibniz :
      ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g
          (fun b : M => g.inner b
            (gradFun (I := I) g f b) (gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hInner : IsHeartOfBochnerInnerAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x := by
  classical
  have hLeibniz : IsLeibnizTraceAt (I := I) g
      (fun b => gradFun (I := I) g f b)
      (normGradSq_contMDiff (I := I) g hf) x := by
    change Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      2 * g.inner x (connLaplacian_vector (I := I) g
                      (fun b => gradFun (I := I) g f b) x)
                     (gradFun (I := I) g f x) +
        2 * frobeniusSq_grad_vector (I := I) g
              (fun b => gradFun (I := I) g f b) x
    have h1 := sum_abstractHessian_smoothOrthoFrame_eq_laplacian (I := I) g
      (normGradSq_contMDiff (I := I) g hf) x
    rw [← h1]
    exact hPerSummand_Leibniz
  exact bochner_pointwise_abstract (I := I) g hf x hLeibniz hInner

theorem bochner_pointwise_abstract_hLeibniz_discharged [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hInner : IsHeartOfBochnerInnerAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_pointwise_abstract (I := I) g hf x
    (leibnizTraceIdentity_holds (I := I) g hf x) hInner

section HessianSkewVanishing

variable (g : SmoothRiemannianMetric I M)

omit [SigmaCompactSpace M] in
private theorem sum_abstractHessian_smoothOrthoFrame_cov_eq_zero
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (v : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
      abstractHessian (I := I) g f x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x v) = 0 := by
  classical
  have hRiesz : ∀ i : Fin (Module.finrank ℝ E),
      (LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x v =
      ∑ j : Fin (Module.finrank ℝ E),
        g.inner x ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x i) x v)
          (smoothOrthoFrame (I := I) g x j x) •
          (smoothOrthoFrame (I := I) g x j x) := by
    intro i
    apply (vector_eq_iff_inner_eq (I := I) g x _ _).mpr
    intro w
    rw [show g.inner x (∑ j : Fin (Module.finrank ℝ E),
            g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) •
              (smoothOrthoFrame (I := I) g x j x)) w =
          ∑ j : Fin (Module.finrank ℝ E),
            g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) *
              g.inner x (smoothOrthoFrame (I := I) g x j x) w from by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [show ((g.inner x)
                (g.inner x ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g x i) x v)
                  (smoothOrthoFrame (I := I) g x j x) •
                  smoothOrthoFrame (I := I) g x j x)) w =
            g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) •
              ((g.inner x) (smoothOrthoFrame (I := I) g x j x)) w from by
        rw [ContinuousLinearMap.map_smul]; rfl]
      rw [smul_eq_mul]]
    exact g_inner_eq_orthonormal_parseval_sum (I := I) g x
      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v) w
      (fun j => smoothOrthoFrame (I := I) g x j x)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
  have h_expand : (∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f x
          (smoothOrthoFrame (I := I) g x i x)
          ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x i) x v)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x j x) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    conv_lhs => rw [hRiesz i]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [show ((abstractHessian (I := I) g f x (smoothOrthoFrame (I := I) g x i x))
              (g.inner x ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g x i) x v)
                (smoothOrthoFrame (I := I) g x j x) •
                smoothOrthoFrame (I := I) g x j x)) =
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x) •
            (abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x))
              (smoothOrthoFrame (I := I) g x j x) from
      ContinuousLinearMap.map_smul
        (abstractHessian (I := I) g f x (smoothOrthoFrame (I := I) g x i x))
        _ _]
    rw [smul_eq_mul]
  rw [h_expand]
  have h_skew_pair : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x j) x v)
        (smoothOrthoFrame (I := I) g x i x) =
      - g.inner x ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x v)
        (smoothOrthoFrame (I := I) g x j x) := by
    intro i j
    rw [smoothOrthoFrame_cov_skew (I := I) g x j i v]
    rw [g.symm x (smoothOrthoFrame (I := I) g x j x)
      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)]
  have h_hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) (2 : ℕ∞) f x := hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)
  have h_hess_symm : ∀ a b : TangentSpace I x,
      abstractHessian (I := I) g f x a b =
      abstractHessian (I := I) g f x b a := fun a b =>
    abstractHessian_symm (I := I) g h_hf_2 a b
  set S : ℝ := ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        g.inner x ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x i) x v)
          (smoothOrthoFrame (I := I) g x j x) *
          abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) with hS_def
  change S = 0
  have h_step1 : S =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x j) x v)
            (smoothOrthoFrame (I := I) g x i x) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x j x)
              (smoothOrthoFrame (I := I) g x i x) := by
    rw [hS_def, Finset.sum_comm]
  have h_step2 : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x j) x v)
            (smoothOrthoFrame (I := I) g x i x) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x j x)
              (smoothOrthoFrame (I := I) g x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (- g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x)) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x j x) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_skew_pair i j, h_hess_symm
      (smoothOrthoFrame (I := I) g x j x)
      (smoothOrthoFrame (I := I) g x i x)]
  have h_step3 : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (- g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x)) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x j x)) = -S := by
    rw [hS_def]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (- g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x)) *
              abstractHessian (I := I) g f x
                (smoothOrthoFrame (I := I) g x i x)
                (smoothOrthoFrame (I := I) g x j x)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            -(g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) *
              abstractHessian (I := I) g f x
                (smoothOrthoFrame (I := I) g x i x)
                (smoothOrthoFrame (I := I) g x j x)) from by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      ring]
    simp_rw [← Finset.sum_neg_distrib]
  have h_S_eq_neg_S : S = -S := h_step1.trans (h_step2.trans h_step3)
  linarith

end HessianSkewVanishing

section LaplacianTraceOnNbhd

variable (g : SmoothRiemannianMetric I M)

private lemma sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f b
          (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x i b)) =ᶠ[𝓝 x]
      (fun b : M => Δ_g (I := I) g hf b) := by
  classical
  have h_open : smoothOrthoFrameNbhd (I := I) (M := M) x ∈ 𝓝 x :=
    smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x
  filter_upwards [h_open] with b hb
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x j b) =
        if i = j then 1 else 0 := fun i j =>
    smoothOrthoFrame_orthonormal (I := I) g x hb i j
  exact sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf b
    (fun i => smoothOrthoFrame (I := I) g x i b) hB_orth

end LaplacianTraceOnNbhd

omit [SigmaCompactSpace M] in
private lemma heart_per_summand_swap [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (W : Π b : M, TangentSpace I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (i : Fin (Module.finrank ℝ E)) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i)
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x)) (W x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) (W x) =
      g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) W
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x))
        (smoothOrthoFrame (I := I) g x i x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun W x
          (smoothOrthoFrame (I := I) g x i x)))
        (smoothOrthoFrame (I := I) g x i x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set B : Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x i with hB_def
  set Gf : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hGf_def
  set Q : Π b : M, TangentSpace I b := covApply cov B Gf with hQ_def
  set P : Π b : M, TangentSpace I b := covApply cov W Gf with hP_def
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Gf) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hGf_at : MDiffAt (T% Gf) x := (hGf_smooth x).mdifferentiableAt (by simp)
  have hQ_at : MDiffAt (T% Q) x :=
    covApply_mdifferentiableAt_local (cov := cov) hB_at
      (by simpa using hGf_smooth)
  have hP_at : MDiffAt (T% P) x :=
    covApply_mdifferentiableAt_local (cov := cov) hW_at
      (by simpa using hGf_smooth)
  have hmc_QW :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hQ_at hW_at (B x)
  have hmc_PB :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hB_at (B x)
  have hHess_section : (fun b : M => g.inner b (Q b) (W b)) =
      (fun b : M => g.inner b (P b) (B b)) := by
    have h := inner_cov_gradFun_symm_globally (I := I) g hf
      (X := B) (Y := W) hB_smooth hW
    funext b
    have hQb : Q b = cov.toFun Gf b (B b) := rfl
    have hPb : P b = cov.toFun Gf b (W b) := rfl
    rw [hQb, hPb]
    exact congrFun h b
  have h_mfderiv_eq :
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Q b) (W b)) x) (B x) =
        (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (P b) (B b)) x) (B x) := by
    rw [hHess_section]
    rfl
  have h_combined :
      g.inner x (cov.toFun Q x (B x)) (W x) + g.inner x (Q x) (cov.toFun W x (B x)) =
        g.inner x (cov.toFun P x (B x)) (B x) +
          g.inner x (P x) (cov.toFun B x (B x)) := by
    rw [← hmc_QW, h_mfderiv_eq, hmc_PB]
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) (2 : ℕ∞) f x := hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)
  have hQx_inner : g.inner x (Q x) (cov.toFun W x (B x)) =
      g.inner x (cov.toFun Gf x (cov.toFun W x (B x))) (B x) := by
    have hQx_eq : Q x = cov.toFun Gf x (B x) := rfl
    rw [hQx_eq]
    set v : TangentSpace I x := cov.toFun W x (B x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := B) (Y := Xv) (x := x) hB_smooth hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    exact h_sym
  have hPx_inner : g.inner x (P x) (cov.toFun B x (B x)) =
      g.inner x (cov.toFun Gf x (cov.toFun B x (B x))) (W x) := by
    have hPx_eq : P x = cov.toFun Gf x (W x) := rfl
    rw [hPx_eq]
    set v : TangentSpace I x := cov.toFun B x (B x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := W) (Y := Xv) (x := x) hW hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    exact h_sym
  rw [hQx_inner, hPx_inner] at h_combined
  linarith

omit [SigmaCompactSpace M] in
private lemma heart_per_summand_riemann_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (W : Π b : M, TangentSpace I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (i : Fin (Module.finrank ℝ E)) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) W
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x))
        (smoothOrthoFrame (I := I) g x i x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun W x
          (smoothOrthoFrame (I := I) g x i x)))
        (smoothOrthoFrame (I := I) g x i x) =
      g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      g.inner x ((LeviCivita (I := I) g).toFun
                  (covApply (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i)
                    (fun b => gradFun (I := I) g f b)) x (W x))
        (smoothOrthoFrame (I := I) g x i x) -
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g x i) x (W x)))
        (smoothOrthoFrame (I := I) g x i x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set B : Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x i with hB_def
  set Gf : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hGf_def
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hriem :=
    LeviCivita_riemannSec_torsionFree_form (I := I) g
      (X := B) (Y := W) (Z := Gf) (x := x) hB_at hW_at
  have hriem' :
      riemannSec cov B W Gf x =
        cov.toFun (covApply cov W Gf) x (B x) -
          cov.toFun (covApply cov B Gf) x (W x) -
          (cov.toFun Gf x (cov.toFun W x (B x)) -
            cov.toFun Gf x (cov.toFun B x (W x))) := by
    change riemannSec (LeviCivita (I := I) g) B W Gf x =
      (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) W Gf) x (B x) -
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) B Gf) x (W x) -
        ((LeviCivita (I := I) g).toFun Gf x ((LeviCivita (I := I) g).toFun W x (B x)) -
          (LeviCivita (I := I) g).toFun Gf x ((LeviCivita (I := I) g).toFun B x (W x)))
    exact hriem
  have hP_split :
      cov.toFun (covApply cov W Gf) x (B x) =
        riemannSec cov B W Gf x +
          cov.toFun (covApply cov B Gf) x (W x) +
          (cov.toFun Gf x (cov.toFun W x (B x)) -
            cov.toFun Gf x (cov.toFun B x (W x))) := by
    rw [hriem']; abel
  have h_inner_split :
      g.inner x (cov.toFun (covApply cov W Gf) x (B x)) (B x) =
        g.inner x (riemannSec cov B W Gf x) (B x) +
          g.inner x (cov.toFun (covApply cov B Gf) x (W x)) (B x) +
          g.inner x (cov.toFun Gf x (cov.toFun W x (B x))) (B x) -
          g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    rw [hP_split]
    rw [map_add, ContinuousLinearMap.add_apply]
    rw [map_add, ContinuousLinearMap.add_apply]
    rw [map_sub, ContinuousLinearMap.sub_apply]
    ring
  linarith

omit [SigmaCompactSpace M] in
private lemma heart_per_summand_assembled [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (W : Π b : M, TangentSpace I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (i : Fin (Module.finrank ℝ E)) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i)
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x)) (W x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) (W x) =
      g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      extDerivFun (I := I) (fun b : M =>
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) -
      2 * abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x)) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set B : Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x i with hB_def
  set Gf : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hGf_def
  set Q : Π b : M, TangentSpace I b := covApply cov B Gf with hQ_def
  have h_swap := heart_per_summand_swap (I := I) g hf x W hW i
  have h_riem := heart_per_summand_riemann_form (I := I) g hf x W hW i
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Gf) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hQ_at : MDiffAt (T% Q) x :=
    covApply_mdifferentiableAt_local (cov := cov) hB_at
      (by simpa using hGf_smooth)
  have hmc_QB :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hQ_at hB_at (W x)
  have h_QB_section : (fun b : M => g.inner b (Q b) (B b)) =
      (fun b : M => abstractHessian (I := I) g f b (B b) (B b)) := by
    funext b
    have hQb : Q b = cov.toFun Gf b (B b) := rfl
    rw [hQb]
    exact inner_cov_gradFun_eq_abstractHessian (I := I) g hf
      (X := B) (Y := B) (x := b) hB_smooth hB_smooth
  rw [show (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Q b) (B b)) x) (W x) =
      (mfderiv I 𝓘(ℝ) (fun b : M =>
          abstractHessian (I := I) g f b (B b) (B b)) x) (W x) from by
    rw [h_QB_section]; rfl] at hmc_QB
  have h_QcovBW : g.inner x (Q x) (cov.toFun B x (W x)) =
      g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    have hQx_eq : Q x = cov.toFun Gf x (B x) := rfl
    rw [hQx_eq]
    set v : TangentSpace I x := cov.toFun B x (W x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := B) (Y := Xv) (x := x) hB_smooth hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    exact h_sym
  have h_LCQW_B :
      g.inner x (cov.toFun Q x (W x)) (B x) =
        extDerivFun (I := I) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x (W x) -
          g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    have hext : extDerivFun (I := I) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x (W x) =
        (mfderiv I 𝓘(ℝ, ℝ) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x) (W x) := rfl
    rw [hext]
    rw [show (mfderiv I 𝓘(ℝ, ℝ) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x) (W x) =
        g.inner x (cov.toFun Q x (W x)) (B x) +
          g.inner x (Q x) (cov.toFun B x (W x)) from hmc_QB]
    rw [h_QcovBW]
    ring
  have h_Hess_BcovBW :
      g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) =
        abstractHessian (I := I) g f x (B x) (cov.toFun B x (W x)) := by
    set v : TangentSpace I x := cov.toFun B x (W x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    rw [show v = Xv x from hXv_eq.symm]
    rw [inner_cov_gradFun_eq_abstractHessian (I := I) g hf
        (X := Xv) (Y := B) (x := x) hXv_smooth hB_smooth]
    exact (abstractHessian_symm (I := I) g (hf.contMDiffAt.of_le (by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1)) (Xv x) (B x))
  rw [h_Hess_BcovBW] at h_LCQW_B
  rw [h_swap, h_riem, h_LCQW_B, h_Hess_BcovBW]
  ring

theorem heartOfBochnerInner_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    IsHeartOfBochnerInnerAt (I := I) g hf x := by
  classical
  intro w
  set W : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hW_def
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) :=
    smoothExtensionTangent_contMDiff x w
  have hW_eq : W x = w := smoothExtensionTangent_eq x w
  rw [show w = W x from hW_eq.symm]
  rw [connLaplacian_grad_inner (I := I) g hf hW_smooth x]
  rw [show ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (W x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (W x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      extDerivFun (I := I) (fun b : M =>
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) -
      2 * abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x))) from by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact heart_per_summand_assembled (I := I) g hf x W hW_smooth i]
  rw [show ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      extDerivFun (I := I) (fun b : M =>
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) -
      2 * abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x))) =
      (∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
          (smoothOrthoFrame (I := I) g x i x)) +
      (∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (fun b : M =>
                    abstractHessian (I := I) g f b
                      (smoothOrthoFrame (I := I) g x i b)
                      (smoothOrthoFrame (I := I) g x i b)) x (W x)) -
      2 * ∑ i : Fin (Module.finrank ℝ E),
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x (W x)) from by
    rw [Finset.mul_sum]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
            (smoothOrthoFrame (I := I) g x i x) +
            extDerivFun (I := I) (fun b : M =>
                      abstractHessian (I := I) g f b
                        (smoothOrthoFrame (I := I) g x i b)
                        (smoothOrthoFrame (I := I) g x i b)) x (W x) -
            2 * abstractHessian (I := I) g f x
                  (smoothOrthoFrame (I := I) g x i x)
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g x i) x (W x)))) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
            (smoothOrthoFrame (I := I) g x i x) +
            extDerivFun (I := I) (fun b : M =>
                      abstractHessian (I := I) g f b
                        (smoothOrthoFrame (I := I) g x i b)
                        (smoothOrthoFrame (I := I) g x i b)) x (W x)) -
            2 * abstractHessian (I := I) g f x
                  (smoothOrthoFrame (I := I) g x i x)
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g x i) x (W x))) from by
      refine Finset.sum_congr rfl ?_
      intro i _
      ring]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]]
  have h_curv_sum_eq :
      (∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
          (smoothOrthoFrame (I := I) g x i x)) =
      ricciTensor (I := I) g x (gradFun (I := I) g f x) w := by
    have h_per_summand : ∀ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
          (smoothOrthoFrame (I := I) g x i x) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x
            (smoothOrthoFrame (I := I) g x i x) w
            (gradFun (I := I) g f x))
          (smoothOrthoFrame (I := I) g x i x) := by
      intro i
      have h_riemOp :=
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g)
          (X := smoothOrthoFrame (I := I) g x i) (Y := W)
          (Z := fun b => gradFun (I := I) g f b) (x := x)
          (smoothOrthoFrame_smooth (I := I) g x i) hW_smooth
          (gradFun_contMDiff_total_section (I := I) g hf)
      rw [show (smoothOrthoFrame (I := I) g x i x) =
              (smoothOrthoFrame (I := I) g x i) x from rfl,
          show w = W x from hW_eq.symm,
          show gradFun (I := I) g f x =
              (fun b => gradFun (I := I) g f b) x from rfl,
          h_riemOp]
    rw [Finset.sum_congr rfl (fun i _ => h_per_summand i)]
    exact heart_curvature_orthonormal_sum_eq_ricci (I := I) g hf x w
  rw [h_curv_sum_eq]
  have h_hess_sum_eventuallyEq :=
    sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian (I := I) g hf x
  have h_extDerivFun_sum_eq :
      (∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (fun b : M =>
                    abstractHessian (I := I) g f b
                      (smoothOrthoFrame (I := I) g x i b)
                      (smoothOrthoFrame (I := I) g x i b)) x (W x)) =
      extDerivFun (I := I) (Δ_g (I := I) g hf) x w := by
    have hB_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (smoothOrthoFrame (I := I) g x i)) :=
      fun i => smoothOrthoFrame_smooth (I := I) g x i
    have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b => gradFun (I := I) g f b)) :=
      gradFun_contMDiff_total_section (I := I) g hf
    have h_each_diff : ∀ i : Fin (Module.finrank ℝ E),
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M =>
          abstractHessian (I := I) g f b
            (smoothOrthoFrame (I := I) g x i b)
            (smoothOrthoFrame (I := I) g x i b)) x := by
      intro i
      have h_conv : (fun b : M =>
            abstractHessian (I := I) g f b
              (smoothOrthoFrame (I := I) g x i b)
              (smoothOrthoFrame (I := I) g x i b)) =
          (fun b : M => g.inner b (covApply (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i)
            (fun b' => gradFun (I := I) g f b') b)
          (smoothOrthoFrame (I := I) g x i b)) := by
        funext b
        exact (inner_cov_gradFun_eq_abstractHessian (I := I) g hf
          (X := smoothOrthoFrame (I := I) g x i)
          (Y := smoothOrthoFrame (I := I) g x i) (x := b)
          (hB_smooth i) (hB_smooth i)).symm
      rw [h_conv]
      have hQ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (covApply (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i)
            (fun b' => gradFun (I := I) g f b'))) x :=
        covApply_mdifferentiableAt_local
          (cov := LeviCivita (I := I) g)
          ((hB_smooth i x).mdifferentiableAt (by simp))
          (by simpa using hGf_smooth)
      have hg_contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
            b (g.inner b)) := g.contMDiff
      have hg_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
          (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
            b (g.inner b)) x :=
        (hg_contMDiff x).mdifferentiableAt (by simp)
      have hB_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (smoothOrthoFrame (I := I) g x i)) x :=
        ((hB_smooth i) x).mdifferentiableAt (by simp)
      have happ : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
          (fun m : M => (⟨m,
              g.inner m (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i)
                (fun b' => gradFun (I := I) g f b') m)
                (smoothOrthoFrame (I := I) g x i m)⟩ :
                TotalSpace ℝ (Bundle.Trivial M ℝ))) x :=
        MDifferentiableAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
          (b := id)
          hg_at hQ_at hB_at
      rw [mdifferentiableAt_totalSpace] at happ
      exact happ.2
    have h_sum_mfderiv :
        extDerivFun (I := I) (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) =
          ∑ i : Fin (Module.finrank ℝ E),
            extDerivFun (I := I) (fun b : M =>
                    abstractHessian (I := I) g f b
                      (smoothOrthoFrame (I := I) g x i b)
                      (smoothOrthoFrame (I := I) g x i b)) x (W x) := by
      induction (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        using Finset.induction_on with
      | empty => simp
      | @insert a s ha IH =>
        rw [Finset.sum_insert ha]
        have hsplit : (fun b : M => ∑ i ∈ insert a s,
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x i b)
                (smoothOrthoFrame (I := I) g x i b)) =
            (fun b : M =>
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x a b)
                (smoothOrthoFrame (I := I) g x a b) +
              ∑ i ∈ s,
                abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x i b)
                  (smoothOrthoFrame (I := I) g x i b)) := by
          funext b
          rw [Finset.sum_insert ha]
        rw [hsplit]
        have h_sum_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => ∑ i ∈ s,
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x i b)
                (smoothOrthoFrame (I := I) g x i b)) x := by
          have h := MDifferentiableAt.sum (z := x) (t := s)
            (f := fun i b => abstractHessian (I := I) g f b
              (smoothOrthoFrame (I := I) g x i b)
              (smoothOrthoFrame (I := I) g x i b))
            (fun i _ => h_each_diff i)
          have heq : (∑ i ∈ s, fun b : M => abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x i b)
                  (smoothOrthoFrame (I := I) g x i b)) =
              (fun b : M => ∑ i ∈ s,
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) := by
            funext b
            simp [Finset.sum_apply]
          rw [heq] at h
          exact h
        rw [show (fun b : M =>
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x a b)
                (smoothOrthoFrame (I := I) g x a b) +
              ∑ i ∈ s,
                abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x i b)
                  (smoothOrthoFrame (I := I) g x i b)) =
            ((fun b : M => abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x a b)
                  (smoothOrthoFrame (I := I) g x a b)) +
              (fun b : M => ∑ i ∈ s,
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b))) from rfl]
        rw [extDerivFun_add (h_each_diff a) h_sum_diff,
            ContinuousLinearMap.add_apply, IH]
    rw [← h_sum_mfderiv]
    have h_extDerivFun_eq :
        extDerivFun (I := I) (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x =
        extDerivFun (I := I) (Δ_g (I := I) g hf) x := by
      change (NormedSpace.fromTangentSpace _).toContinuousLinearMap ∘L
            (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                      abstractHessian (I := I) g f b
                        (smoothOrthoFrame (I := I) g x i b)
                        (smoothOrthoFrame (I := I) g x i b)) x) =
            (NormedSpace.fromTangentSpace _).toContinuousLinearMap ∘L
            (mfderiv I 𝓘(ℝ, ℝ) (Δ_g (I := I) g hf) x)
      have h_mf_eq : (mfderiv I 𝓘(ℝ, ℝ) (fun b : M =>
                  ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x) =
          mfderiv I 𝓘(ℝ, ℝ) (Δ_g (I := I) g hf) x :=
        Filter.EventuallyEq.mfderiv_eq h_hess_sum_eventuallyEq
      have h_base_eq : (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x =
          Δ_g (I := I) g hf x := by
        exact h_hess_sum_eventuallyEq.self_of_nhds
      rw [h_mf_eq]
      congr 1
    rw [h_extDerivFun_eq, hW_eq]
  rw [h_extDerivFun_sum_eq]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x))) = 0 from by
    rw [hW_eq]
    exact sum_abstractHessian_smoothOrthoFrame_cov_eq_zero (I := I) g hf x w]
  rw [show extDerivFun (I := I) (Δ_g (I := I) g hf) x w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w from
    (gradFun_metricDual_extDerivFun (I := I) g (Δ_g (I := I) g hf) x w).symm]
  rw [show ricciTensor (I := I) g x (gradFun (I := I) g f x) w =
        g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
    (inner_ricciSharp (I := I) g x (gradFun (I := I) g f x) w).symm]
  rw [hW_eq]
  ring

theorem bochner_pointwise_abstract_of_smooth [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_pointwise_abstract (I := I) g hf x
    (leibnizTraceIdentity_holds (I := I) g hf x)
    (heartOfBochnerInner_holds (I := I) g hf x)
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem laplacian_inner_self [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
          2 * frobeniusSq_grad_vector (I := I) g V x) :
    Δ_g (I := I) g hgVV x =
      2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
        2 * frobeniusSq_grad_vector (I := I) g V x := by
  have h := connLaplacian_inner_self_of_trace (I := I) g hV hgVV x hLeibniz
  rw [connLaplacian_function_def] at h
  exact h


end Connection
end Integral
end DifferentialGeometry
