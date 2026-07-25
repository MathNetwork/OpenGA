import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradCrossBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RankRReadingDominationUniformSup
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormDiscreteLogConvex
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNormHolderIntegrability


noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section GeneralValenceRS

open Bundle Tensor0SBundle Tensor0SNabla TensorRSNabla TensorMultilinear

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_covGradBundleEquiv_symm_apply_eq_finCons
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : Tensor0SBundle.TensorRSSpace r (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) (a : Fin n) :
    Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r s
        ((Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) r s x).symm T (e a)) n e K J =
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T n e K
        (Fin.cons a J) := by
  unfold Integral.Connection.fiberNormSqComponent
  set ωK : Tensor0SBundle.Tensor0SSpace r I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K k))) with hωK
  rw [show (((Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) r s x).symm T (e a)) ωK
        (fun k => e (J k)) : ℝ) =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
          ((Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) r s x).symm T) (e a)) ωK)
        (fun k => e (J k)) from rfl]
  rw [Tensor0SBundle.covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r s x T (e a) ωK
    (fun k => e (J k))]
  congr 1
  exact (Fin.comp_cons e a J).symm

set_option maxHeartbeats 1600000 in

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_orthonormalFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : Tensor0SBundle.TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r s S n e K J) ^ 2 := by
  classical
  subst hn
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin (Module.finrank ℝ E), bse i = e i := fun i => by
    rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x S]
  rw [Integral.Connection.tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g r s x e bse
    rfl hbse horth S S]
  refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
  rw [pow_two]

set_option maxHeartbeats 1600000 in

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] Tensor0SBundle.TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        (Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) r s x Φ) =
      ∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g r s x (Φ (e a)) := by
  classical
  set T : Tensor0SBundle.TensorRSSpace r (s + 1) I x :=
    Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) r s x Φ with hT_def

  rw [riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_orthonormalFrame (I := I) (M := M) g r (s + 1) x T e hn
    horth]

  have hΦeq : ∀ a : Fin n,
      Φ (e a) = (Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) r s x).symm T (e a) := by
    intro a
    rw [hT_def]
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ (e a)) =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
            n e K (Fin.cons a J)) ^ 2 := by
    intro a
    rw [hΦeq a]
    rw [riemannianFiberNormSq_eq_sum_fiberNormSqComponent_sq_of_orthonormalFrame (I := I) (M := M) g r s x _ e hn horth]
    refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
    rw [fiberNormSqComponent_covGradBundleEquiv_symm_apply_eq_finCons (I := I) (M := M) g r s x T e K J a]
  rw [Finset.sum_congr rfl (fun a _ => hper a)]

  have hcons_bij : Function.Bijective
      (fun p : Fin n × (Fin s → Fin n) => Fin.cons p.1 p.2 : _ → (Fin (s + 1) → Fin n)) := by
    refine ⟨fun p₁ p₂ hp => ?_, fun J'' => ⟨(J'' 0, Fin.tail J''), ?_⟩⟩
    · have h0 := congrFun hp 0
      have ht := congrArg Fin.tail hp
      simp only [Fin.cons_zero, Fin.tail_cons] at h0 ht
      exact Prod.ext h0 ht
    · exact Fin.cons_self_tail J''

  have hperK : ∀ K : Fin r → Fin n,
      (∑ a : Fin n, ∑ J : Fin s → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
            n e K (Fin.cons a J)) ^ 2) =
        ∑ J'' : Fin (s + 1) → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
            n e K J'') ^ 2 := by
    intro K
    rw [show (∑ a : Fin n, ∑ J : Fin s → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
            n e K (Fin.cons a J)) ^ 2) =
        ∑ p : Fin n × (Fin s → Fin n),
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
            n e K (Fin.cons p.1 p.2)) ^ 2 from
      (Fintype.sum_prod_type (fun p : Fin n × (Fin s → Fin n) =>
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
          n e K (Fin.cons p.1 p.2)) ^ 2)).symm]
    exact Fintype.sum_bijective _ hcons_bij
      (fun p : Fin n × (Fin s → Fin n) =>
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
          n e K (Fin.cons p.1 p.2)) ^ 2)
      (fun J'' : Fin (s + 1) → Fin n =>
        (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
          n e K J'') ^ 2)
      (fun p => rfl)

  conv_rhs => rw [Finset.sum_comm]
  exact (Finset.sum_congr rfl (fun K _ => hperK K)).symm

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φ : TangentSpace I x →L[ℝ] Tensor0SBundle.TensorRSSpace r s I x) (b : ℝ)
    (hbound : ∀ v : TangentSpace I x, g.inner x v v = 1 →
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ v) ≤ b) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        (Tensor0SBundle.covGradBundleEquiv (I := I) (M := M) r s x Φ) ≤
      (Module.finrank ℝ E : ℝ) * b := by
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
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  set e : Fin n → TangentSpace I x := fun i => eob i with he_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have horth : ∀ a c : Fin n, g.inner x (e a) (e c) = if a = c then (1 : ℝ) else 0 := by
    intro a c
    have horthb : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horthb a c
    rw [he_def, ← hinner_eq (eob a) (eob c)]
    exact hite
  have hfr : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hn : n = Module.finrank ℝ E := by rw [hn_def, hfr]
  rw [riemannianFiberNormSq_covGradBundleEquiv_eq_sum_frame_rs (I := I) (M := M) g r s x Φ e hn
    horth]
  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g r s x (Φ (e a)) ≤ b := by
    intro a
    refine hbound (e a) ?_
    have := horth a a; rwa [if_pos rfl] at this
  refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hn_def, hfr]

end GeneralValenceRS

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
