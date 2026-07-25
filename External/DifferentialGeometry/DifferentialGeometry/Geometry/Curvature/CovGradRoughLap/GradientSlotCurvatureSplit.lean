import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance
import DifferentialGeometry.Geometry.Curvature.Bochner.TensorWeitzenbockIdentity
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 6400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla TensorRSNabla TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem baseSlotCurv_eq_riemannOp
    (g : SmoothRiemannianMetric I M)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    baseSlotCurv (I := I) g X W x u =
      riemannOp (LeviCivita (I := I) g) x (X x) (W x) u := by
  rw [baseSlotCurv]
  rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g) X.contMDiff W.contMDiff
    (smoothExtensionTangent_contMDiff (I := I) x u)]
  rw [smoothExtensionTangent_eq (I := I) x u]

def gradSlotCurv (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace (s + 1) I x :=
  riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
    (fun b => X b) (fun b => W b) (unitGradFieldGen (I := I) (M := M) g s S) x

omit [NeZero (Module.finrank ℝ E)] in
theorem gradSlotCurv_toModel_eq_baseSlot_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x) u =
      - ∑ k : Fin (s + 1),
          Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
            (Function.update u k (baseSlotCurv (I := I) g X W x (u k))) := by
  rw [gradSlotCurv]
  exact riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g (s + 1) X W
    (unitGradFieldGen (I := I) (M := M) g s S)
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S) x u

omit [NeZero (Module.finrank ℝ E)] in
theorem gradSlotCurv_toModel_eq_leading_add_tail
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x) u =
      - (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
            (Function.update u 0 (baseSlotCurv (I := I) g X W x (u 0))) +
          ∑ k : Fin s,
            Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
              (Function.update u k.succ
                (baseSlotCurv (I := I) g X W x (u k.succ)))) := by
  rw [gradSlotCurv_toModel_eq_baseSlot_sum, Fin.sum_univ_succ]

def orthoFrameSec (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
    (smoothOrthoFrame_smooth (I := I) g x i)

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma orthoFrameSec_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    orthoFrameSec (I := I) (M := M) g x i b = smoothOrthoFrame (I := I) g x i b := rfl

theorem gradSlotCurv_frameSum_toModel_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (u : Fin (s + 1) → TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (gradSlotCurv (I := I) (M := M) g s S (orthoFrameSec (I := I) (M := M) g x i) W x) u) =
      ∑ i : Fin (Module.finrank ℝ E),
        - (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
              (Function.update u 0
                (riemannOp (LeviCivita (I := I) g) x
                  (smoothOrthoFrame (I := I) g x i x) (W x) (u 0))) +
            ∑ k : Fin s,
              Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)
                (Function.update u k.succ
                  (riemannOp (LeviCivita (I := I) g) x
                    (smoothOrthoFrame (I := I) g x i x) (W x) (u k.succ)))) := by
  simp only [gradSlotCurv_toModel_eq_leading_add_tail,
    baseSlotCurv_eq_riemannOp, orthoFrameSec_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricEndoRaisedFib_inner_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x (ricEndoRaisedFib (I := I) g x v) w =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x
          (smoothOrthoFrame (I := I) g x i x) v w)
          (smoothOrthoFrame (I := I) g x i x) := by
  rw [inner_ricEndoRaisedFib (I := I) (M := M) g x v w,
    smoothOrthoFrame_riemannOp_trace_eq_ricci (I := I) (M := M) g x v w]

omit [NeZero (Module.finrank ℝ E)] in
theorem ricTraceSection_apply_leadingSlot
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v0 : E) (vs : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (ricTraceSection (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (ricEndoRaisedFib (I := I) g x v0) vs) := by
  classical
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (ricTraceSection (I := I) (M := M) g s S).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      ricSlotOpFib (I := I) (M := M) g s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [ricTraceSection_toSection, ricSlotOpField_toSection]
    rfl
  rw [hval]
  rw [ricSlotOpFib_apply_eval (I := I) (M := M) g s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) v0 vs]
  rw [tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (ricEndoRaisedFib (I := I) g x v0) vs]

private lemma slot_skew_cancel {n s : ℕ} (k : Fin (s + 1)) (Rmat : Fin n → Fin n → ℝ)
    (hskew : ∀ a c, Rmat a c + Rmat c a = 0)
    (P Q : (Fin (s + 1) → Fin n) → ℝ) :
    (∑ φ : Fin (s + 1) → Fin n, ∑ c : Fin n, Rmat (φ k) c * (P (Function.update φ k c) * Q φ))
      + (∑ φ : Fin (s + 1) → Fin n, ∑ c : Fin n,
          Rmat (φ k) c * (P φ * Q (Function.update φ k c))) = 0 := by
  classical
  rw [Fintype.sum_prod_type
        (f := fun p : (Fin (s + 1) → Fin n) × Fin n =>
          Rmat (p.1 k) p.2 * (P (Function.update p.1 k p.2) * Q p.1)) |>.symm,
      Fintype.sum_prod_type
        (f := fun p : (Fin (s + 1) → Fin n) × Fin n =>
          Rmat (p.1 k) p.2 * (P p.1 * Q (Function.update p.1 k p.2))) |>.symm]
  rw [show (∑ p : (Fin (s + 1) → Fin n) × Fin n,
        Rmat (p.1 k) p.2 * (P (Function.update p.1 k p.2) * Q p.1))
      = (∑ p : (Fin (s + 1) → Fin n) × Fin n,
          Rmat p.2 (p.1 k) * (P p.1 * Q (Function.update p.1 k p.2)))
    from by
      apply Finset.sum_nbij' (fun p => (Function.update p.1 k p.2, p.1 k))
        (fun p => (Function.update p.1 k p.2, p.1 k))
      · intro p _; exact Finset.mem_univ _
      · intro p _; exact Finset.mem_univ _
      · rintro ⟨φ, c⟩ _; simp [Function.update_idem]
      · rintro ⟨φ, c⟩ _; simp [Function.update_idem]
      · rintro ⟨φ, c⟩ _
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  rintro ⟨φ, c⟩ _
  simp only
  have hs := hskew (φ k) c
  have hrw : Rmat c (φ k) * (P φ * Q (Function.update φ k c))
      + Rmat (φ k) c * (P φ * Q (Function.update φ k c))
      = (Rmat (φ k) c + Rmat c (φ k)) * (P φ * Q (Function.update φ k c)) := by ring
  rw [hrw, hs, zero_mul]

omit [CompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma curv_inner_left_reduce
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T U : Π b : M, Tensor0SSpace (s + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (T b)))
    (x : M)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then 1 else 0)
    (hbse_exp : ∀ v : TangentSpace I x, v = ∑ c, g.inner x (bse c) v • bse c) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) T x))
        (Tensor0SSpace.toModel (U x)) =
      - ∑ k : Fin (s + 1), ∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E),
          ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (U x) (fun j => bse (φ j))) := by
  classical
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (s + 1) bse hbse_orth]
  have hslot : ∀ φ : Fin (s + 1) → Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) T x) (fun k => bse (φ k)) =
        - ∑ k : Fin (s + 1),
            Tensor0SSpace.toModel (T x)
              (Function.update (fun j => bse (φ j)) k
                (baseSlotCurv (I := I) g X W x ((fun j => bse (φ j)) k))) := by
    intro φ
    exact riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g (s + 1) X W T hT x
      (fun j => bse (φ j))
  rw [Finset.sum_congr rfl (fun φ _ => by rw [hslot φ])]
  have hexp_slot : ∀ (φ : Fin (s + 1) → Fin (Module.finrank ℝ E)) (k : Fin (s + 1)),
      Tensor0SSpace.toModel (T x)
          (Function.update (fun j => bse (φ j)) k
            (baseSlotCurv (I := I) g X W x ((fun j => bse (φ j)) k))) =
        ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) := by
    intro φ k
    have harg : baseSlotCurv (I := I) g X W x ((fun j => bse (φ j)) k)
        = baseSlotCurv (I := I) g X W x (bse (φ k)) := by simp
    have hv : baseSlotCurv (I := I) g X W x (bse (φ k))
        = ∑ c, g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c :=
      hbse_exp (baseSlotCurv (I := I) g X W x (bse (φ k)))
    conv_lhs => rw [harg, hv]
    have hsum := (Tensor0SSpace.toModel (T x)).toMultilinearMap.map_update_sum
      (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (i := k)
      (g := fun c => g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)
      (m := fun j => bse (φ j))
    have hsum' :
        Tensor0SSpace.toModel (T x)
            (Function.update (fun j => bse (φ j)) k
              (∑ c, g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)) =
          ∑ c, Tensor0SSpace.toModel (T x)
              (Function.update (fun j => bse (φ j)) k
                (g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)) := hsum
    rw [hsum']
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hsmul := (Tensor0SSpace.toModel (T x)).toMultilinearMap.map_update_smul
      (m := fun j => bse (φ j)) (i := k)
      (c := g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k)))) (x := bse c)
    have hsmul' :
        Tensor0SSpace.toModel (T x)
            (Function.update (fun j => bse (φ j)) k
              (g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) • bse c)) =
          g.inner x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k))) •
            Tensor0SSpace.toModel (T x)
              (Function.update (fun j => bse (φ j)) k (bse c)) := hsmul
    rw [hsmul', smul_eq_mul, g.symm x (bse c) (baseSlotCurv (I := I) g X W x (bse (φ k)))]
    congr 1
    have hupd : Function.update (fun j => bse (φ j)) k (bse c)
        = fun j => bse ((Function.update φ k c) j) := by
      funext j
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
    rw [hupd]
  rw [Finset.sum_congr rfl (fun φ _ => by
    rw [Finset.sum_congr rfl (fun k _ => hexp_slot φ k)])]
  have hdist : ∀ φ : Fin (s + 1) → Fin (Module.finrank ℝ E),
      (-∑ k : Fin (s + 1), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)))
        * Tensor0SSpace.toModel (U x) (fun k => bse (φ k))
      = -∑ k : Fin (s + 1), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (U x) (fun j => bse (φ j))) := by
    intro φ
    rw [neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [mul_assoc]
  rw [Finset.sum_congr rfl (fun φ _ => hdist φ)]
  simp only [Finset.sum_neg_distrib]
  rw [neg_inj]
  rw [Finset.sum_comm]

omit [CompactSpace M] in

theorem tensor0SCov_riemannSec_metric_skew_section
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T U : Π b : M, Tensor0SSpace (s + 1) I b)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (T b)))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (U b)))
    (x : M) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) T x))
        (Tensor0SSpace.toModel (U x))
      + covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel (T x))
        (Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b) U x)) = 0 := by
  classical
  obtain ⟨n, e, hn, horth, _hpar, hexp, _⟩ := tangent_frame_expansion (I := I) (M := M) g x
  have hn' : n = Module.finrank ℝ E := hn
  subst hn'
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := fun i => by
    rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then 1 else 0 := fun a b => by
    rw [hbse_eq a, hbse_eq b]; exact horth a b
  have hbse_exp : ∀ v : TangentSpace I x, v = ∑ c, g.inner x (bse c) v • bse c := fun v => by
    conv_lhs => rw [hexp v]
    exact Finset.sum_congr rfl (fun c _ => by rw [hbse_eq c])
  have hL := curv_inner_left_reduce (I := I) (M := M) g s X W T U hT x bse hbse_orth hbse_exp
  have hsymm := tensorInnerPointwise_0s_symm (I := I) (M := M) g x (s + 1)
    (Tensor0SSpace.toModel (T x))
    (Tensor0SSpace.toModel
      (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b) U x))
  have hR := curv_inner_left_reduce (I := I) (M := M) g s X W U T hU x bse hbse_orth hbse_exp
  rw [hL, hsymm, hR]
  rw [← neg_add, neg_eq_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k _
  have hRmat_skew : ∀ a c : Fin (Module.finrank ℝ E),
      g.inner x (baseSlotCurv (I := I) g X W x (bse a)) (bse c)
        + g.inner x (baseSlotCurv (I := I) g X W x (bse c)) (bse a) = 0 := by
    intro a c
    rw [baseSlotCurv_eq_riemannOp (I := I) g X W x (bse a),
        baseSlotCurv_eq_riemannOp (I := I) g X W x (bse c)]
    have hsk := riemannOp_metric_skew (I := I) g x (X x) (W x) (bse a) (bse c)
    have hcomm : g.inner x (riemannOp (LeviCivita (I := I) g) x (X x) (W x) (bse c)) (bse a)
        = g.inner x (bse a) (riemannOp (LeviCivita (I := I) g) x (X x) (W x) (bse c)) :=
      g.symm x (riemannOp (LeviCivita (I := I) g) x (X x) (W x) (bse c)) (bse a)
    rw [hcomm]
    linarith [hsk]
  have hcore := slot_skew_cancel (n := Module.finrank ℝ E) (s := s) k
    (fun a c => g.inner x (baseSlotCurv (I := I) g X W x (bse a)) (bse c))
    (fun a c => hRmat_skew a c)
    (fun φ => Tensor0SSpace.toModel (T x) (fun j => bse (φ j)))
    (fun φ => Tensor0SSpace.toModel (U x) (fun j => bse (φ j)))
  have hgoal_eq :
      (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (T x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (U x) (fun j => bse (φ j))))
        + (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
            g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
              (Tensor0SSpace.toModel (U x) (fun j => bse ((Function.update φ k c) j)) *
                Tensor0SSpace.toModel (T x) (fun j => bse (φ j)))) = 0 := by
    rw [show (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
            (Tensor0SSpace.toModel (U x) (fun j => bse ((Function.update φ k c) j)) *
              Tensor0SSpace.toModel (T x) (fun j => bse (φ j))))
        = (∑ φ : Fin (s + 1) → Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
            g.inner x (baseSlotCurv (I := I) g X W x (bse (φ k))) (bse c) *
              (Tensor0SSpace.toModel (T x) (fun j => bse (φ j)) *
                Tensor0SSpace.toModel (U x) (fun j => bse ((Function.update φ k c) j))))
      from by
        refine Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun c _ => ?_))
        ring]
    exact hcore
  exact hgoal_eq

omit [CompactSpace M] in

theorem tensor0SCov_riemannOp_metric_skew
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (v w : TangentSpace I x) (T U : Tensor0SSpace (s + 1) I x) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel
          (riemannOp (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)) x v w T))
        (Tensor0SSpace.toModel U)
      + covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel T)
        (Tensor0SSpace.toModel
          (riemannOp (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)) x v w U)) =
      0 := by
  classical
  set cov := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) with hcov
  set Xext : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b => smoothExtensionTangent (I := I) x v b)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXext
  set Wext : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b => smoothExtensionTangent (I := I) x w b)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hWext
  set Text : Π b : M, Tensor0SSpace (s + 1) I b :=
    fun b => smoothExtensionFiber (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x T b with hText
  set Uext : Π b : M, Tensor0SSpace (s + 1) I b :=
    fun b => smoothExtensionFiber (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x U b with hUext
  have hXc : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun b => TotalSpace.mk' E
      (E := fun z : M => TangentSpace I z) b (Xext b)) := Xext.contMDiff
  have hWc : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun b => TotalSpace.mk' E
      (E := fun z : M => TangentSpace I z) b (Wext b)) := Wext.contMDiff
  have hTc : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (Text b)) :=
    smoothExtensionFiber_contMDiff (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x T
  have hUc : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (Uext b)) :=
    smoothExtensionFiber_contMDiff (I := I) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun b : M => Tensor0SSpace (s + 1) I b) x U
  have hXx : Xext x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : Wext x = w := smoothExtensionTangent_eq (I := I) x w
  have hTx : Text x = T := smoothExtensionFiber_eq (I := I) (F := Tensor0SModel (s + 1) ℝ E)
    (V := fun b : M => Tensor0SSpace (s + 1) I b) x T
  have hUx : Uext x = U := smoothExtensionFiber_eq (I := I) (F := Tensor0SModel (s + 1) ℝ E)
    (V := fun b : M => Tensor0SSpace (s + 1) I b) x U
  have hRT : riemannOp cov x v w T = riemannSec cov (fun b => Xext b) (fun b => Wext b) Text x := by
    rw [← hXx, ← hWx, ← hTx]
    exact (riemannSec_eq_riemannOp_smooth (cov := cov) hXc hWc hTc).symm
  have hRU : riemannOp cov x v w U = riemannSec cov (fun b => Xext b) (fun b => Wext b) Uext x := by
    rw [← hXx, ← hWx, ← hUx]
    exact (riemannSec_eq_riemannOp_smooth (cov := cov) hXc hWc hUc).symm
  rw [hRT, hRU]
  rw [show T = Text x from hTx.symm, show U = Uext x from hUx.symm]
  exact tensor0SCov_riemannSec_metric_skew_section (I := I) (M := M) g s Xext Wext Text Uext
    hTc hUc x

theorem gradSlotCurv_pairing_covGrad_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x
        (Tensor0SSpace.toModel (gradSlotCurv (I := I) (M := M) g s S X W x))
        (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x)) = 0 := by
  classical
  have hskew := tensor0SCov_riemannSec_metric_skew_section (I := I) (M := M) g s X W
    (unitGradFieldGen (I := I) (M := M) g s S) (unitGradFieldGen (I := I) (M := M) g s S)
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S)
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S) x
  rw [gradSlotCurv]
  have hsymm := tensorInnerPointwise_0s_symm (I := I) (M := M) g x (s + 1)
    (Tensor0SSpace.toModel
      (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b) (unitGradFieldGen (I := I) (M := M) g s S) x))
    (Tensor0SSpace.toModel (unitGradFieldGen (I := I) (M := M) g s S x))
  rw [← hsymm] at hskew
  linarith [hskew]

end Connection
end Integral
end DifferentialGeometry

end
