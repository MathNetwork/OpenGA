import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.ChartRiemannDataUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorCurvatureUnitEvalBridge
import Mathlib.Topology.Order.Compact


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma finrank_tensor0SModel_eq_cfec (t : ℕ) :
    Module.finrank ℝ (Tensor0SModel t ℝ E) = (Module.finrank ℝ E) ^ t := by
  induction t with
  | zero =>
      rw [pow_zero, (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ t ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (t + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel t ℝ E) ≃ₗ[ℝ] (E →ₗ[ℝ] Tensor0SModel t ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma finrank_tensorRSSpace_zero_eq (t : ℕ) (x : M) :
    Module.finrank ℝ (TensorRSSpace 0 t I x) = (Module.finrank ℝ E) ^ t := by
  rw [(tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M)
    0 t x).toLinearEquiv.finrank_eq]
  change Module.finrank ℝ (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel t ℝ E) = _
  let φ : (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel t ℝ E) ≃ₗ[ℝ]
      (Tensor0SModel 0 ℝ E →ₗ[ℝ] Tensor0SModel t ℝ E) :=
    { toFun := fun f => f.toLinearMap
      invFun := fun f => LinearMap.toContinuousLinearMap f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [φ.finrank_eq, Module.finrank_linearMap, finrank_tensor0SModel_eq_cfec,
    finrank_tensor0SModel_eq_cfec, pow_zero, one_mul]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma orthonormal_rfns_exists_basis
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M) (ht : 1 ≤ t)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 0 t I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J) :
    ∃ bse : Module.Basis (Fin n) ℝ (TangentSpace I x), ∀ i : Fin n, bse i = e i := by
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
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  set d : ℕ := Module.finrank ℝ (TangentSpace I x) with hd_def
  have hdE : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl

  have horthonormal : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j; rw [hinner_eq (e i) (e j)]; exact horth i j
  have hli : LinearIndependent ℝ e := horthonormal.linearIndependent
  have hn_le_d : n ≤ d := by
    have := hli.fintype_card_le_finrank
    simpa using this

  set Φ : TensorRSSpace 0 t I x →ₗ[ℝ] ((Fin t → Fin n) → ℝ) :=
    { toFun := fun T J => fiberNormSqComponent (I := I) (M := M) g x 0 t T n e
        (fun k => k.elim0) J
      map_add' := by
        intro T T'; funext J
        exact fiberNormSqComponent_add (I := I) (M := M) g x 0 t T T' n e _ J
      map_smul' := by
        intro c T; funext J
        rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact fiberNormSqComponent_smul (I := I) (M := M) g x 0 t c T n e _ J } with hΦ_def
  have hΦ_inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    intro T hT

    have hcomp0 : ∀ J : Fin t → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x 0 t T n e (fun k => k.elim0) J = 0 := by
      intro J; exact congrFun hT J
    have hrfns0 : riemannianFiberNormSq (I := I) (M := M) g 0 t x T = 0 := by
      rw [hrepr T]
      refine Finset.sum_eq_zero (fun K _ => Finset.sum_eq_zero (fun J _ => ?_))
      rw [fiberNormSqSummand_eq_component_sq]
      rw [show K = (fun k : Fin 0 => k.elim0) from funext (fun k => k.elim0)]
      rw [hcomp0 J]; ring

    have hpd := riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x T
    rw [hrfns0] at hpd
    have hTm0 : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := t) (x := x) T = 0 :=
      (L2.tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g 0 t x _).mp hpd.symm
    have hT0model : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := t) (x := x) T =
      TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := t) (x := x) (0 : TensorRSSpace 0 t I x) := by
      rw [hTm0]
      exact (map_zero (tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M)
        0 t x)).symm
    exact TensorRSSpace.toModel_injective (𝕜 := ℝ) (E := E) (I := I) (M := M) hT0model
  have hdt_le_nt : (d : ℕ) ^ t ≤ n ^ t := by
    have hle := LinearMap.finrank_le_finrank_of_injective hΦ_inj
    rw [finrank_tensorRSSpace_zero_eq (I := I) (M := M) t x, hdE.symm] at hle
    rw [Module.finrank_pi, Fintype.card_pi] at hle
    simp only [Fintype.card_fin] at hle
    calc (d : ℕ) ^ t = Module.finrank ℝ (TangentSpace I x) ^ t := by rw [hd_def]
      _ ≤ n ^ t := by
            convert hle using 2
            simp [Fintype.card_fin]
  have hd_pos : 0 < d := by
    rw [hd_def, hdE]; exact Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hd_le_n : d ≤ n := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hdt_le_nt (not_le.mpr (Nat.pow_lt_pow_left hlt (by omega)))
  have hcard : Fintype.card (Fin n) = d := by
    rw [Fintype.card_fin]; omega

  haveI : Nonempty (Fin n) := by
    rw [← Fintype.card_pos_iff, hcard]; exact hd_pos
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [hcard, hd_def]), ?_⟩
  intro i
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

theorem exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        ∀ (i j : Fin n) (J : Fin t → Fin n),
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x t e J)) ≤ K :=
  exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound_of_leviCivitaGNormBound (I := I) (M := M) g t

theorem exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 t x
              (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
                (dualTensorFrameS (I := I) (M := M) g x t e J))) ≤ C := by
  classical

  obtain ⟨K, hK_nonneg, hK_term⟩ :=
    exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_single_term_bound (I := I) (M := M) g t
  set d : ℕ := Module.finrank ℝ E with hd_def
  refine ⟨(d : ℝ) ^ (t + 2) * K, ?_, ?_⟩
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _) hK_nonneg
  intro x n e horth

  have hn_le_d : n ≤ d := by
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
    have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
      fun u v => rfl
    have horthonormal : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j; rw [hinner_eq (e i) (e j)]; exact horth i j
    have hcard := horthonormal.linearIndependent.fintype_card_le_finrank
    have hcardE : Module.finrank ℝ (TangentSpace I x) = d := rfl
    rw [hcardE] at hcard
    simpa using hcard

  have hsum_le_const :
      (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x t e J))) ≤
        ∑ _i : Fin n, ∑ _j : Fin n, ∑ _J : Fin t → Fin n, K := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun J _ => ?_)
    exact hK_term x e horth i j J
  refine le_trans hsum_le_const ?_

  have hconst_eq :
      (∑ _i : Fin n, ∑ _j : Fin n, ∑ _J : Fin t → Fin n, K) = (n : ℝ) ^ (t + 2) * K := by
    rw [Finset.sum_const, Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hconst_eq]

  refine mul_le_mul_of_nonneg_right ?_ hK_nonneg
  exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hn_le_d) (t + 2)

theorem exists_continuous_riemannOp_tensorCovS_frameEnergy_bound
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ Ccurv : M → ℝ, Continuous Ccurv ∧ (∀ x : M, 0 ≤ Ccurv x) ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        (∀ S : TensorRSSpace 0 t I x,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J) →
        ∀ T : TensorRSSpace 0 t I x,
          (∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 t x
                (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T)) ≤
            Ccurv x * riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by
  classical
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const (I := I) (M := M) g t
  refine ⟨fun _ => C, continuous_const, fun _ => hC_nonneg, ?_⟩
  intro x n e horth hrepr T

  have hCx_le_C :
      (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
              (dualTensorFrameS (I := I) (M := M) g x t e J))) ≤ C :=
    hC_bound x e horth
  have hrfns_nonneg : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 t x T
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0
    set J₀ : Fin 0 → Fin n := fun k => k.elim0 with hJ₀

    set φ : TensorRSSpace 0 0 I x → ℝ :=
      fun S => fiberNormSqComponent (I := I) (M := M) g x 0 0 S n e J₀ J₀ with hφ_def

    have hrfns_sq : ∀ S : TensorRSSpace 0 0 I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 0 x S = φ S ^ 2 := by
      intro S
      rw [hrepr S]
      rw [Finset.sum_eq_single J₀ (fun K _ hK => absurd (Subsingleton.elim K J₀) hK)
        (fun h => absurd (Finset.mem_univ J₀) h)]
      rw [Finset.sum_eq_single J₀ (fun J _ hJ => absurd (Subsingleton.elim J J₀) hJ)
        (fun h => absurd (Finset.mem_univ J₀) h)]
      simp only [hφ_def]
      rw [fiberNormSqSummand_eq_component_sq]

    have hφ_unit : φ (dualTensorFrameS (I := I) (M := M) g x 0 e J₀) = 1 := by
      simp only [hφ_def]
      rw [fiberNormSqComponent_dualTensorFrameS (I := I) (M := M) g x 0 e horth J₀ J₀ J₀]
      simp

    have hφ_smul : ∀ (a : ℝ) (S : TensorRSSpace 0 0 I x), φ (a • S) = a * φ S := by
      intro a S; simp only [hφ_def]; rw [fiberNormSqComponent_smul]

    have hφ_inj : ∀ S : TensorRSSpace 0 0 I x, φ S = 0 → S = 0 := by
      intro S hS
      have hrfns0 : riemannianFiberNormSq (I := I) (M := M) g 0 0 x S = 0 := by
        rw [hrfns_sq S, hS]; ring
      have hpd := riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 0 x S
      rw [hrfns0] at hpd
      have hSm0 : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := 0) (s := 0) (x := x) S = 0 :=
        (L2.tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g 0 0 x _).mp hpd.symm
      have : TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := 0) (s := 0) (x := x) S =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := 0) (s := 0) (x := x) (0 : TensorRSSpace 0 0 I x) := by
        rw [hSm0]; exact (map_zero _).symm
      exact TensorRSSpace.toModel_injective (𝕜 := ℝ) (E := E) (I := I) (M := M) this

    set D := dualTensorFrameS (I := I) (M := M) g x 0 e J₀ with hD_def
    have hT_eq : T = φ T • D := by
      have hdiff : φ (T - φ T • D) = 0 := by
        simp only [hφ_def]
        rw [show (T - φ T • D : TensorRSSpace 0 0 I x) = T + (-(φ T)) • D from by
          rw [neg_smul]; abel]
        rw [fiberNormSqComponent_add, fiberNormSqComponent_smul]
        have hφD : fiberNormSqComponent (I := I) (M := M) g x 0 0 D n e J₀ J₀ = 1 := hφ_unit
        rw [hφD]; ring
      have hTD : T - φ T • D = 0 := hφ_inj _ hdiff
      exact sub_eq_zero.mp hTD

    have hLHS_eq :
        (∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 0 x
              (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) T)) =
          φ T ^ 2 *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 0 x
                (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      conv_lhs => rw [hT_eq, (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j)).map_smul (φ T) D]

      rw [hrfns_sq, hrfns_sq]
      have : φ (φ T • riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D) =
          φ T * φ (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D) := hφ_smul _ _
      rw [this]; ring
    rw [hLHS_eq, hrfns_sq T]
    rw [show (fun _ : M => C) x = C from rfl]

    have hsq_nonneg : (0 : ℝ) ≤ φ T ^ 2 := sq_nonneg _
    have henergy0_le_C :
        (∑ i : Fin n, ∑ j : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 0 x
              (riemannOp (tensorCov (I := I) g 0 0) x (e i) (e j) D)) ≤ C := by
      refine le_trans (le_of_eq ?_) hCx_le_C
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [Finset.sum_eq_single J₀ (fun J _ hJ => absurd (Subsingleton.elim J J₀) hJ)
        (fun h => absurd (Finset.mem_univ J₀) h)]
    rw [mul_comm C (φ T ^ 2)]
    exact mul_le_mul_of_nonneg_left henergy0_le_C hsq_nonneg
  · obtain ⟨bse, hbse⟩ :=
      orthonormal_rfns_exists_basis (I := I) (M := M) g t x htpos e horth hrepr
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T))
          ≤ (∑ i : Fin n, ∑ j : Fin n, ∑ J : Fin t → Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 t x
                (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j)
                  (dualTensorFrameS (I := I) (M := M) g x t e J))) *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
            sum_riemannianFiberNormSq_riemannOpS_le_Cx
              (I := I) (M := M) g x t e bse hbse horth hrepr T
      _ ≤ C * riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
            mul_le_mul_of_nonneg_right hCx_le_C hrfns_nonneg

end Connection
end Integral
end DifferentialGeometry

end
