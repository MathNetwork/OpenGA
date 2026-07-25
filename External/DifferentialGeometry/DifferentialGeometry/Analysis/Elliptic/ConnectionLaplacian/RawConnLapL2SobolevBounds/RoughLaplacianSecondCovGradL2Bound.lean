import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma coframeS_zero_eq_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) :
    coframeS (I := I) (M := M) g x 0 e K₀ = unitZeroSec (I := I) (M := M) x := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
      (coframeS (I := I) (M := M) g x 0 e K₀) m = 1 := by
    have h1 : Tensor0SBundle.Tensor0SSpace.toModel
        (coframeS (I := I) (M := M) g x 0 e K₀) m =
        coframeS (I := I) (M := M) g x 0 e K₀ (fun k : Fin 0 => k.elim0) := by
      apply congrArg
      funext k; exact k.elim0
    rw [h1, coframeS_apply (I := I) (M := M) g x 0 e K₀ (fun k : Fin 0 => k.elim0)]
    simp
  have hR : Tensor0SBundle.Tensor0SSpace.toModel
      (unitZeroSec (I := I) (M := M) x) m = 1 := by
    rw [unitZeroSec_apply (I := I) (M := M) x,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hL, hR]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_twoSlotUnitEval_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : Tensor0SBundle.TensorRSSpace 0 (s + 1 + 1) I x)
    (w : TangentSpace I x) (hw : g.inner x w w ≤ 1)
    (U : Tensor0SBundle.TensorRSSpace 0 s I x)
    (hU : ∀ m : Fin s → TangentSpace I x,
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from U)
            (unitZeroSec (I := I) (M := M) x)) m =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
              Tensor0SBundle.Tensor0SSpace (s + 1 + 1) I x from T)
            (unitZeroSec (I := I) (M := M) x))
          (Fin.cons w (Fin.cons w m))) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x U ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x T := by
  classical

  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _ with heob_def
  set e : Fin n → TangentSpace I x := fun i => eob i with he_def
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl

  have hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g.inner x (e i) v ^ 2 = g.inner x v v := by
    intro v
    have h := OrthonormalBasis.sum_sq_inner_right eob v
    have hns : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    calc ∑ i : Fin n, g.inner x (e i) v ^ 2
        = ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (eob i) v]
      _ = ‖v‖ ^ 2 := h
      _ = g.inner x v v := by rw [← hns, hinner_eq v v]
  have hexp : ∀ v : TangentSpace I x, v = ∑ i : Fin n, g.inner x (e i) v • e i := by
    intro v
    have hrepr : ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i = v :=
      OrthonormalBasis.sum_repr' eob v
    have hcongr : (∑ i : Fin n, g.inner x (e i) v • e i) =
        ∑ i : Fin n, (inner ℝ (eob i) v : ℝ) • eob i := by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [hinner_eq (eob i) v]
    rw [hcongr, hrepr]
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := fun S => rfl
  have hreprT : ∀ S : TensorRSSpace 0 (s + 1 + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1 + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1 + 1) S n e K J := fun S => rfl

  set Uu : Tensor0SSpace s I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from U)
      (unitZeroSec (I := I) (M := M) x) with hUu_def
  set Tu : Tensor0SSpace (s + 1 + 1) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from T)
      (unitZeroSec (I := I) (M := M) x) with hTu_def

  set D : Fin n → Fin n → (Fin s → Fin n) → ℝ :=
    fun a b J => Tensor0SSpace.toModel Tu
      (Fin.cons (e a) (Fin.cons (e b) (fun k : Fin s => e (J k)))) with hD_def

  have hcomp : ∀ J : Fin s → Fin n,
      fiberNormSqComponent (I := I) (M := M) g x 0 s U n e K₀ J =
        ∑ a : Fin n, ∑ b : Fin n,
          (g.inner x (e a) w * g.inner x (e b) w) • D a b J := by
    intro J

    have hUcomp : fiberNormSqComponent (I := I) (M := M) g x 0 s U n e K₀ J =
        Tensor0SSpace.toModel Uu (fun k : Fin s => e (J k)) := by
      have hco : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
          unitZeroSec (I := I) (M := M) x := by
        rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
            coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
        exact coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀
      unfold fiberNormSqComponent
      rw [hco, hUu_def]
      rfl
    rw [hUcomp]

    have hUT : Tensor0SSpace.toModel Uu (fun k : Fin s => e (J k)) =
        Tensor0SSpace.toModel Tu
          (Fin.cons w (Fin.cons w (fun k : Fin s => e (J k)))) := hU _
    rw [hUT]

    have hstep1 : Tensor0SSpace.toModel Tu
          (Fin.cons w (Fin.cons w (fun k : Fin s => e (J k)))) =
        ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (s + 1) x Tu (e a))
          (Fin.cons w (fun k : Fin s => e (J k))) :=
      tensor0S_uncurry_cons_eval_of_expansion (I := I) (M := M) Tu
        (fun a => g.inner x (e a) w) e w (hexp w)
        (Fin.cons w (fun k : Fin s => e (J k)))
    rw [hstep1]
    refine Finset.sum_congr rfl (fun a _ => ?_)

    have hstep2 : Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (s + 1) x Tu (e a))
          (Fin.cons w (fun k : Fin s => e (J k))) =
        ∑ b : Fin n, g.inner x (e b) w • Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) s x
            (tensor0S_curry (I := I) (M := M) (s + 1) x Tu (e a)) (e b))
          (fun k : Fin s => e (J k)) :=
      tensor0S_uncurry_cons_eval_of_expansion (I := I) (M := M)
        (tensor0S_curry (I := I) (M := M) (s + 1) x Tu (e a))
        (fun b => g.inner x (e b) w) e w (hexp w) (fun k : Fin s => e (J k))
    rw [hstep2, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)

    have hcurry2 : Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x
          (tensor0S_curry (I := I) (M := M) (s + 1) x Tu (e a)) (e b))
        (fun k : Fin s => e (J k)) = D a b J := by
      rw [hD_def]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (tensor0S_curry (I := I) (M := M) (s + 1) x Tu (e a)) (e b)
        (fun k : Fin s => e (J k))]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        Tu (e a) (Fin.cons (e b) (fun k : Fin s => e (J k)))]
    rw [hcurry2]
    exact (mul_smul (g.inner x (e a) w) (g.inner x (e b) w) (D a b J)).symm

  have hDcomp : ∀ (a b : Fin n) (J : Fin s → Fin n),
      fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
          (Fin.cons a (Fin.cons b J)) = D a b J := by
    intro a b J
    have hco : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
        unitZeroSec (I := I) (M := M) x := by
      rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
      exact coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀
    have htuple : (fun k : Fin (s + 1 + 1) =>
          e ((Fin.cons a (Fin.cons b J) : Fin (s + 1 + 1) → Fin n) k)) =
        Fin.cons (e a) (Fin.cons (e b) (fun k : Fin s => e (J k))) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · simp
      · intro j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i; simp
    rw [hD_def]
    unfold fiberNormSqComponent
    rw [hco, htuple]
    rfl

  have hCS : ∀ J : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x 0 s U n e K₀ J) ^ 2 ≤
        ∑ a : Fin n, ∑ b : Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
            (Fin.cons a (Fin.cons b J))) ^ 2 := by
    intro J

    have hflat : fiberNormSqComponent (I := I) (M := M) g x 0 s U n e K₀ J =
        ∑ p : Fin n × Fin n,
          (g.inner x (e p.1) w * g.inner x (e p.2) w) * D p.1 p.2 J := by
      rw [hcomp J, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [smul_eq_mul]
    rw [hflat]

    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
      (fun p => g.inner x (e p.1) w * g.inner x (e p.2) w) (fun p => D p.1 p.2 J)
    have hcoeff : ∑ p : Fin n × Fin n,
        (g.inner x (e p.1) w * g.inner x (e p.2) w) ^ 2 = (g.inner x w w) ^ 2 := by
      rw [Fintype.sum_prod_type]
      have : ∀ a : Fin n, ∑ b : Fin n,
          (g.inner x (e a) w * g.inner x (e b) w) ^ 2 =
            (g.inner x (e a) w) ^ 2 * ∑ b : Fin n, (g.inner x (e b) w) ^ 2 := by
        intro a
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [mul_pow]
      simp_rw [this]
      rw [← Finset.sum_mul, hpars w, ← sq]
    have hle1 : (g.inner x w w) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ g.inner x w w := by
        rw [← hpars w]; positivity
      nlinarith [hw, h0]
    calc (∑ p : Fin n × Fin n,
            (g.inner x (e p.1) w * g.inner x (e p.2) w) * D p.1 p.2 J) ^ 2
        ≤ (∑ p : Fin n × Fin n,
              (g.inner x (e p.1) w * g.inner x (e p.2) w) ^ 2) *
            ∑ p : Fin n × Fin n, (D p.1 p.2 J) ^ 2 := hcs
      _ = (g.inner x w w) ^ 2 * ∑ p : Fin n × Fin n, (D p.1 p.2 J) ^ 2 := by rw [hcoeff]
      _ ≤ 1 * ∑ p : Fin n × Fin n, (D p.1 p.2 J) ^ 2 := by
          refine mul_le_mul_of_nonneg_right hle1 ?_
          exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
      _ = ∑ a : Fin n, ∑ b : Fin n, (D a b J) ^ 2 := by
          rw [one_mul, Fintype.sum_prod_type]
      _ = ∑ a : Fin n, ∑ b : Fin n,
            (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
              (Fin.cons a (Fin.cons b J))) ^ 2 := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [hDcomp a b J]

  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS U K₀]
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x (s + 1 + 1) e hreprT T K₀]

  have hexpandT : ∑ J'' : Fin (s + 1 + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀ J'') ^ 2 =
      ∑ a : Fin n, ∑ b : Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
          (Fin.cons a (Fin.cons b J))) ^ 2 := by
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1 + 1) => Fin n))
          (fun pr : Fin n × (Fin (s + 1) → Fin n) =>
            (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
              (Fin.cons pr.1 pr.2)) ^ 2)
          (fun J'' : Fin (s + 1 + 1) → Fin n =>
            (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀ J'') ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun pr : Fin n × (Fin s → Fin n) =>
            (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
              (Fin.cons a (Fin.cons pr.1 pr.2))) ^ 2)
          (fun J' : Fin (s + 1) → Fin n =>
            (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
              (Fin.cons a J')) ^ 2)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
  rw [hexpandT]

  calc ∑ J : Fin s → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x 0 s U n e K₀ J) ^ 2
      ≤ ∑ J : Fin s → Fin n, ∑ a : Fin n, ∑ b : Fin n,
            (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
              (Fin.cons a (Fin.cons b J))) ^ 2 :=
        Finset.sum_le_sum (fun J _ => hCS J)
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ J : Fin s → Fin n,
            (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1 + 1) T n e K₀
              (Fin.cons a (Fin.cons b J))) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_comm]

private theorem secondCovDeriv_unit_frame_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : Integral.L2.SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (tensorSecondCovDeriv (I := I) g 0 s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => S.toSection y) x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  classical
  have hunit : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    simpa using smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
  refine riemannianFiberNormSq_twoSlotUnitEval_le (I := I) (M := M) g s x
    ((covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x)
    (smoothOrthoFrame (I := I) g x i x) (le_of_eq hunit)
    (tensorSecondCovDeriv (I := I) g 0 s
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => S.toSection y) x) (fun m => ?_)
  exact (DifferentialGeometry.Integral.Connection.tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
    (I := I) (M := M) g s S (X := smoothOrthoFrame (I := I) g x i)
    (Y := smoothOrthoFrame (I := I) g x i)
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i) x m).symm

theorem rawConnLap_fiberNormSq_le_secondCovGrad
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : Integral.L2.SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((rawTensorConnLapSmooth (I := I) g 0 s S).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
          ((covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set rhs : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x) with hrhs_def

  have hsum :
      (rawTensorConnLapSmooth (I := I) g 0 s S).toSection x =
        ∑ i : Fin n,
          tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x := by
    rw [rawTensorConnLapSmooth_toSection_apply (I := I) (M := M) g 0 s S x]
    rw [rawTensorConnLap_eq_metricTraceHessian (I := I) g 0 s
      (fun y : M => S.toSection y) x]
    rw [metricTraceHessian_def (I := I) g 0 s (fun y : M => S.toSection y) x]
  rw [hsum]

  have hsub :
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (∑ i : Fin n,
            tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y) x) ≤
        ((Finset.univ : Finset (Fin n)).card : ℝ) *
          ∑ i : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => S.toSection y) x) :=
    riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 s x Finset.univ _
  have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard] at hsub

  have hterm : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x) ≤ rhs := by
    intro i
    rw [hrhs_def]
    exact secondCovDeriv_unit_frame_fiberNormSq_le (I := I) (M := M) g s S x i
  have hsum_le :
      (∑ i : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y) x)) ≤ (n : ℝ) * rhs := by
    calc (∑ i : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => S.toSection y) x))
          ≤ ∑ _i : Fin n, rhs := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (n : ℝ) * rhs := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (∑ i : Fin n,
            tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y) x)
      ≤ (n : ℝ) * ∑ i : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => S.toSection y) x) := hsub
    _ ≤ (n : ℝ) * ((n : ℝ) * rhs) := mul_le_mul_of_nonneg_left hsum_le hn_nn
    _ = (n : ℝ) ^ 2 * rhs := by ring

theorem exists_rawConnLap_l2Norm_le_secondCovGrad_l2Norm_gen
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (s : ℕ) (S : Integral.L2.SmoothCcTensor g 0 s),
        Integral.L2.tensorL2Norm (I := I) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ≤
          K * Integral.L2.tensorL2Norm (I := I) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := by
    rw [hn_def]; exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hK1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  refine ⟨(n : ℝ), hK1, ?_⟩
  intro s S

  set HH : Integral.L2.SmoothCcTensor g 0 (s + 1 + 1) :=
    covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) with hHH_def

  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          ((rawTensorConnLapSmooth (I := I) g 0 s S).toSection x) ≤
        (n : ℝ) ^ 2 * ∑ _i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x (HH.toSection x) := by
    intro x
    rw [Finset.sum_const, Finset.card_range, one_nsmul]
    rw [hHH_def]
    exact rawConnLap_fiberNormSq_le_secondCovGrad (I := I) (M := M) g s S x

  have hpack :
      ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ≤
        (n : ℝ) * ∑ _i ∈ Finset.range 1, ‖HH‖ :=
    tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g 1
      (fun _ => s + 1 + 1) (fun _ => HH)
      (rawTensorConnLapSmooth (I := I) g 0 s S)
      (n : ℝ) (Nat.cast_nonneg n) hpt
  rw [Finset.sum_const, Finset.card_range, one_nsmul] at hpack
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M)
    (rawTensorConnLapSmooth (I := I) g 0 s S)] at hpack
  rw [Integral.L2.SmoothCcTensor.norm_def (I := I) (M := M) HH] at hpack
  rw [hHH_def] at hpack
  exact hpack

end Connection
end Integral
end DifferentialGeometry

end
