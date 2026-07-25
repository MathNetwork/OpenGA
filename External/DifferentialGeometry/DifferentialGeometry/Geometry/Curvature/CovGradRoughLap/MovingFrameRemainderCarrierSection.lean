import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem orthonormalFrame_parseval_expand
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    u = ∑ a : Fin n, g.inner x (e a) u • e a := by
  classical
  have hfinrank_eq : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  haveI : Nonempty (Fin n) := by
    refine ⟨⟨0, ?_⟩⟩
    rw [hn, hfinrank_eq]
    exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; exact hn
  set bse : Module.Basis (Fin n) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  congr 1
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin n, bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin n,
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
        bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  have hexp : ∀ u : TangentSpace I x, u = ∑ a : Fin n,
      g.inner x (e a) u • e a := fun u =>
    orthonormalFrame_parseval_expand (I := I) (M := M) g x e hn horth u
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) e hexp w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

noncomputable def genuineCurvPureRSubtracted
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S - genuineCurvatureOnlySection (I := I) (M := M) g s S

@[simp] lemma genuineCurvPureRSubtracted_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection := by
  rw [genuineCurvPureRSubtracted, SmoothCcTensor.toSection_sub]

theorem genuineCurvPureRSubtracted_toSection_eq_covDeriv_add_bracket
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m +
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hGcurv⟩ :=
    GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩

  have hsub : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (genuineCurvPureRSubtracted (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) := by
    rw [genuineCurvPureRSubtracted_toSection]
    rw [show ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection) x =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
        (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x from rfl]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x -
            (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x) from
      ContinuousLinearMap.sub_apply _ _ _]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hsub]

  rw [pointwiseTensorCurv_toSection_eq_genuine_add_bracket_ofOrthonormal
    (I := I) (M := M) g s S x e hn horth w m]
  rw [genuineThirdCurvFieldFib_eq_pureR_add_covDeriv (I := I) (M := M) g s S x e w m]
  rw [hGcurv w m]
  ring

noncomputable def movingFrameRemainderSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  pointwiseTensorCurv (I := I) (M := M) g s S - genuineCurvatureOnlySection (I := I) (M := M) g s S -
    genuineDiffCurvSection (I := I) (M := M) g s S - ricTraceSection (I := I) (M := M) g s S

@[simp] lemma movingFrameRemainderSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (movingFrameRemainderSection (I := I) (M := M) g s S).toSection =
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection -
          (genuineCurvatureOnlySection (I := I) (M := M) g s S).toSection -
          (genuineDiffCurvSection (I := I) (M := M) g s S).toSection -
        (ricTraceSection (I := I) (M := M) g s S).toSection := by
  rw [movingFrameRemainderSection, SmoothCcTensor.toSection_sub,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]

theorem movingFrameRemainderSection_eq_pureRSubtracted_sub_genuineDiff_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    movingFrameRemainderSection (I := I) (M := M) g s S =
      genuineCurvPureRSubtracted (I := I) (M := M) g s S -
        (genuineDiffCurvSection (I := I) (M := M) g s S +
          ricTraceSection (I := I) (M := M) g s S) := by
  rw [movingFrameRemainderSection, genuineCurvPureRSubtracted]
  abel

end Connection
end Integral
end DifferentialGeometry
