import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.CometricDifferenceRaisedGreenPairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Connection.ParsevalFrameField
import DifferentialGeometry.Geometry.Operator.Gradient


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [FiniteDimensional ℝ E] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem g0_polarized_parseval
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (v w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E), g₀.inner x (e i) v * g₀.inner x (e i) w =
      g₀.inner x v w := by
  have hexp : (∑ i : Fin (Module.finrank ℝ E), g₀.inner x (e i) w • e i) = w :=
    orthonormal_tangent_expansion (I := I) (M := M) g₀ x e horth w
  calc ∑ i : Fin (Module.finrank ℝ E), g₀.inner x (e i) v * g₀.inner x (e i) w
      = ∑ i : Fin (Module.finrank ℝ E), g₀.inner x v (g₀.inner x (e i) w • e i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, smul_eq_mul, g₀.symm x v (e i)]; ring
    _ = g₀.inner x v (∑ i : Fin (Module.finrank ℝ E), g₀.inner x (e i) w • e i) := by
        rw [map_sum]
    _ = g₀.inner x v w := by rw [hexp]


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem multilinear_firstSlot_pairing_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) {s : ℕ}
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (Wm : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ)
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    (∑ a : Fin (Module.finrank ℝ E),
        Wm (Fin.cons (e a) (fun k => e (J' k))) *
          Wm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
      ≤ κ * ∑ a : Fin (Module.finrank ℝ E),
          Wm (Fin.cons (e a) (fun k => e (J' k))) ^ 2 := by
  classical
  set φ : TangentSpace I x →L[ℝ] ℝ :=
    (Wm.toContinuousLinearMap (Fin.cons (0 : TangentSpace I x) (fun k => e (J' k))) 0).comp
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) with hφ_def
  have hφ_apply : ∀ u : TangentSpace I x,
      φ u = Wm (Fin.cons u (fun k => e (J' k))) := by
    intro u
    rw [hφ_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  set w : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
      (I := I) g₀ x φ.toLinearMap with hw_def
  have hw_inner : ∀ u : TangentSpace I x, g₀.inner x w u = φ u := by
    intro u
    rw [hw_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp
      (I := I) g₀ x φ.toLinearMap u
  have hcomp_eq : ∀ a : Fin (Module.finrank ℝ E),
      Wm (Fin.cons (e a) (fun k => e (J' k))) = g₀.inner x w (e a) := by
    intro a; rw [hw_inner, hφ_apply]
  have hcompΛ_eq : ∀ a : Fin (Module.finrank ℝ E),
      Wm (Fin.cons (Λ (e a)) (fun k => e (J' k))) = g₀.inner x w (Λ (e a)) := by
    intro a; rw [hw_inner, hφ_apply]
  have hkey : (∑ a : Fin (Module.finrank ℝ E),
        Wm (Fin.cons (e a) (fun k => e (J' k))) *
          Wm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
      = g₀.inner x (Λ w) w := by
    have hsum_eq : (∑ a : Fin (Module.finrank ℝ E),
          Wm (Fin.cons (e a) (fun k => e (J' k))) *
            Wm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) (Λ w) * g₀.inner x (e a) w := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hcomp_eq a, hcompΛ_eq a]
      rw [g₀.symm x w (e a)]
      have hadj' : g₀.inner x w (Λ (e a)) = g₀.inner x (Λ w) (e a) := by
        rw [g₀.symm x w (Λ (e a)), hadj (e a) w, g₀.symm x (e a) (Λ w)]
      rw [hadj', g₀.symm x (Λ w) (e a)]
      ring
    rw [hsum_eq, g0_polarized_parseval (I := I) g₀ x e horth (Λ w) w]
  have hself : (∑ a : Fin (Module.finrank ℝ E),
        Wm (Fin.cons (e a) (fun k => e (J' k))) ^ 2)
      = g₀.inner x w w := by
    have hsum_eq : (∑ a : Fin (Module.finrank ℝ E),
          Wm (Fin.cons (e a) (fun k => e (J' k))) ^ 2)
        = ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) w * g₀.inner x (e a) w := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hcomp_eq a, g₀.symm x w (e a), sq]
    rw [hsum_eq, g0_polarized_parseval (I := I) g₀ x e horth w w]
  rw [hkey, hself]
  exact hbound w


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem slotInsertEndoFib_bundle_eval (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (A : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1) → TangentSpace I x) :
    (slotInsertEndoFib (s + 1) 0 x Λ A) v = A (Function.update v 0 (Λ (v 0))) := by
  have h := slotInsertEndoFib_apply_eval (I := I) (M := M) (s + 1) 0 x Λ A
    (fun k => ((v k : TangentSpace I x) : E))
  rw [show (slotInsertEndoFib (s + 1) 0 x Λ A) v
      = Tensor0SSpace.toModel (slotInsertEndoFib (s + 1) 0 x Λ A)
        (fun k => ((v k : TangentSpace I x) : E)) from rfl]
  rw [h]
  rfl


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_orthoFrame_basis_E (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
      (∀ i : Fin (Module.finrank ℝ E), bse i = e i) ∧
      (∀ a b : Fin (Module.finrank ℝ E),
        g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) := by
  classical
  obtain ⟨n, e0, hn, horth0, _hpars, _hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g 0 0 x
  subst hn
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := e0 with he_def
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := horth0
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1:ℝ) else 0) := by
      intro j _; rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  refine ⟨e, basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_, horth⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorInnerPointwise_slotΛ_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (W : TensorRSSpace 0 (s+1) I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g₀.inner x (e a) (e b) = if a = b then (1:ℝ) else 0) :
    tensorInnerPointwise g₀ 0 (s+1) x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel
          (show TensorRSSpace 0 (s+1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s+1) 0 x Λ).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W))))
      ≤ κ * tensorInnerPointwise g₀ 0 (s+1) x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  classical
  set slotW : TensorRSSpace 0 (s+1) I x :=
    TensorRSSpace.ofCLM ((slotInsertEndoFib (s+1) 0 x Λ).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W)) with hslotW
  set Wm : ContinuousMultilinearMap ℝ (fun _ : Fin (s+1) => TangentSpace I x) ℝ :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e ((Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) k))))) with hWm
  have hcompW : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E)) (J : Fin (s+1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s+1) W (Module.finrank ℝ E) e K J
        = Wm (fun k => e (J k)) := by
    intro K J; rw [hWm]; rfl
  have hcompSlot : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E)) (J : Fin (s+1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s+1) slotW (Module.finrank ℝ E) e K J
        = Wm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro K J
    rw [hWm, hslotW]
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s+1)
          (TensorRSSpace.ofCLM ((slotInsertEndoFib (s+1) 0 x Λ).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W))) (Module.finrank ℝ E) e K J
        = (slotInsertEndoFib (s+1) 0 x Λ
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K k)))))) (fun k => e (J k)) from rfl,
      slotInsertEndoFib_bundle_eval]
    rfl
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 (s+1) x e bse rfl hbse horth W slotW]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 (s+1) x e bse rfl hbse horth W W]
  have hKcollapse : ∀ (F : (Fin 0 → Fin (Module.finrank ℝ E)) → ℝ),
      (∑ K : Fin 0 → Fin (Module.finrank ℝ E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro b _ hb; exact absurd (Subsingleton.elim b Fin.elim0) hb
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hKcollapse, hKcollapse]
  have hLHS : ∀ J : Fin (s+1) → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s+1) W (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s+1) slotW (Module.finrank ℝ E) e Fin.elim0 J
      = Wm (fun k => e (J k)) * Wm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro J; rw [hcompW, hcompSlot]
  have hRHS : ∀ J : Fin (s+1) → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s+1) W (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s+1) W (Module.finrank ℝ E) e Fin.elim0 J
      = Wm (fun k => e (J k)) ^ 2 := by
    intro J; rw [hcompW]; ring
  rw [Finset.sum_congr rfl (fun J _ => hLHS J), Finset.sum_congr rfl (fun J _ => hRHS J)]
  have hsplit : ∀ g : (Fin (s+1) → Fin (Module.finrank ℝ E)) → ℝ,
      (∑ J : Fin (s+1) → Fin (Module.finrank ℝ E), g J)
        = ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E), g (Fin.cons a J') := by
    intro g
    rw [← (Fin.consEquiv (fun _ : Fin (s+1) => Fin (Module.finrank ℝ E))).sum_comp g,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  rw [hsplit (fun J => Wm (fun k => e (J k)) * Wm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0))))),
    hsplit (fun J => Wm (fun k => e (J k)) ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum (fun J' _ => ?_)
  have hpertail := multilinear_firstSlot_pairing_le (I := I) (M := M) g₀ x Λ hadj hbound e horth Wm J'
  have hLHSeq : (∑ a : Fin (Module.finrank ℝ E),
        Wm (fun k => e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) k)) *
          Wm (Function.update (fun k => e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) k)) 0
            (Λ (e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) 0)))))
      = ∑ a : Fin (Module.finrank ℝ E),
          Wm (Fin.cons (e a) (fun k => e (J' k))) *
            Wm (Fin.cons (Λ (e a)) (fun k => e (J' k))) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (fun k => e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) k))
        = Fin.cons (e a) (fun k => e (J' k)) := by
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    have h2 : Function.update (fun k => e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) k)) 0
          (Λ (e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) 0)))
        = Fin.cons (Λ (e a)) (fun k => e (J' k)) := by
      rw [show ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) 0) = a from rfl]
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    rw [h2, h1]
  have hRHSeq : (∑ a : Fin (Module.finrank ℝ E),
        Wm (fun k => e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) k)) ^ 2)
      = ∑ a : Fin (Module.finrank ℝ E),
          Wm (Fin.cons (e a) (fun k => e (J' k))) ^ 2 := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (fun k => e ((Fin.cons a J' : Fin (s+1) → Fin (Module.finrank ℝ E)) k))
        = Fin.cons (e a) (fun k => e (J' k)) := by
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    rw [h1]
  rw [hLHSeq, hRHSeq]
  exact hpertail

def gInvDiffSlotApplied (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s+1) I x) : TensorRSSpace 0 (s+1) I x :=
  TensorRSSpace.ofCLM ((slotInsertEndoFib (s+1) 0 x (metricComparisonDiffEndo (I := I) g₀ g₁ x)).comp
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W))

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorInnerPointwise_gInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (x : M) (W : TensorRSSpace 0 (s+1) I x) :
    tensorInnerPointwise g₀ 0 (s+1) x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x W))
      ≤ (δ / (1 - δ)) * tensorInnerPointwise g₀ 0 (s+1) x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_E (I := I) (M := M) g₀ x
  exact tensorInnerPointwise_slotΛ_le g₀ s x (metricComparisonDiffEndo (I := I) g₀ g₁ x)
    (gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x)
    (fun v => gInvDiffRaisedEndo_inner_self_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorL2Inner_slotΛ_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {κ : ℝ}
    (Wfield Sfield : M → TensorRSModel 0 (s+1) ℝ E)
    (hptwise : ∀ x : M,
      tensorInnerPointwise g₀ 0 (s+1) x (Wfield x) (Sfield x)
        ≤ κ * tensorInnerPointwise g₀ 0 (s+1) x (Wfield x) (Wfield x))
    (hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x (Wfield x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x (Wfield x) (Wfield x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 (s+1) Wfield Sfield
      ≤ κ * tensorL2Inner g₀ 0 (s+1) Wfield Wfield := by
  unfold tensorL2Inner
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono hWS_int (hWW_int.const_mul κ) ?_
  intro x; exact hptwise x

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorL2Inner_gInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (W : ∀ x, TensorRSSpace 0 (s+1) I x)
    (hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x
        (TensorRSSpace.toModel (W x))
        (TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x))))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x
        (TensorRSSpace.toModel (W x)) (TensorRSSpace.toModel (W x)))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 (s+1)
        (fun x => TensorRSSpace.toModel (W x))
        (fun x => TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x)))
      ≤ (δ / (1 - δ)) * tensorL2Inner g₀ 0 (s+1)
          (fun x => TensorRSSpace.toModel (W x)) (fun x => TensorRSSpace.toModel (W x)) := by
  refine tensorL2Inner_slotΛ_le g₀ s
    (fun x => TensorRSSpace.toModel (W x))
    (fun x => TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x)))
    (fun x => ?_) hWS_int hWW_int
  exact tensorInnerPointwise_gInvDiffSlot_le g₀ g₁ h htie hδ_lt hδ_nn hδ s x (W x)

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem multi_slotAt_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) {r : ℕ} (j : Fin r)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i k, g₀.inner x (e i) (e k) = if i = k then (1 : ℝ) else 0)
    (Wm : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ TangentSpace I x) ℝ)
    (z : Fin r → TangentSpace I x) :
    (∑ a : Fin (Module.finrank ℝ E),
        Wm (Function.update z j (e a)) *
          Wm (Function.update z j (Λ (e a))))
      ≤ κ * ∑ a : Fin (Module.finrank ℝ E),
          Wm (Function.update z j (e a)) ^ 2 := by
  classical
  set φ : TangentSpace I x →L[ℝ] ℝ :=
    (Wm.toContinuousLinearMap z j).comp
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) with hφ_def
  have hφ_apply : ∀ u : TangentSpace I x,
      φ u = Wm (Function.update z j u) := by
    intro u
    rw [hφ_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply]
  set w : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
      (I := I) g₀ x φ.toLinearMap with hw_def
  have hw_inner : ∀ u : TangentSpace I x, g₀.inner x w u = φ u := by
    intro u
    rw [hw_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp
      (I := I) g₀ x φ.toLinearMap u
  have hcomp : ∀ a : Fin (Module.finrank ℝ E),
      Wm (Function.update z j (e a)) = g₀.inner x w (e a) := by
    intro a
    rw [hw_inner, hφ_apply]
  have hcompΛ : ∀ a : Fin (Module.finrank ℝ E),
      Wm (Function.update z j (Λ (e a))) = g₀.inner x w (Λ (e a)) := by
    intro a
    rw [hw_inner, hφ_apply]
  have hkey : (∑ a : Fin (Module.finrank ℝ E),
        Wm (Function.update z j (e a)) *
          Wm (Function.update z j (Λ (e a)))) = g₀.inner x (Λ w) w := by
    calc
      (∑ a : Fin (Module.finrank ℝ E),
          Wm (Function.update z j (e a)) *
            Wm (Function.update z j (Λ (e a)))) =
          ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) (Λ w) * g₀.inner x (e a) w := by
              refine Finset.sum_congr rfl (fun a _ ↦ ?_)
              rw [hcomp a, hcompΛ a, g₀.symm x w (e a)]
              have ha : g₀.inner x w (Λ (e a)) = g₀.inner x (Λ w) (e a) := by
                rw [g₀.symm x w (Λ (e a)), hadj (e a) w,
                  g₀.symm x (e a) (Λ w)]
              rw [ha, g₀.symm x (Λ w) (e a)]
              ring
      _ = g₀.inner x (Λ w) w :=
        g0_polarized_parseval (I := I) g₀ x e horth (Λ w) w
  have hself : (∑ a : Fin (Module.finrank ℝ E),
        Wm (Function.update z j (e a)) ^ 2) = g₀.inner x w w := by
    calc
      (∑ a : Fin (Module.finrank ℝ E),
          Wm (Function.update z j (e a)) ^ 2) =
          ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) w * g₀.inner x (e a) w := by
              refine Finset.sum_congr rfl (fun a _ ↦ ?_)
              rw [hcomp a, g₀.symm x w (e a), sq]
      _ = g₀.inner x w w :=
        g0_polarized_parseval (I := I) g₀ x e horth w w
  rw [hkey, hself]
  exact hbound w


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem slotFib_eval_at (r : ℕ) (j : Fin r) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (A : Tensor0SSpace r I x) (v : Fin r → TangentSpace I x) :
    (slotInsertEndoFib r j x Λ A) v = A (Function.update v j (Λ (v j))) := by
  have h := slotInsertEndoFib_apply_eval (I := I) (M := M) r j x Λ A
    (fun k ↦ ((v k : TangentSpace I x) : E))
  rw [show (slotInsertEndoFib r j x Λ A) v =
      Tensor0SSpace.toModel (slotInsertEndoFib r j x Λ A)
        (fun k ↦ ((v k : TangentSpace I x) : E)) from rfl]
  rw [h]
  rfl


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem inner_slotAt_le
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    {κ : ℝ}
    (hbound : ∀ v : TangentSpace I x, g₀.inner x (Λ v) v ≤ κ * g₀.inner x v v)
    (W : TensorRSSpace 0 r I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    tensorInnerPointwise g₀ 0 r x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel
          (show TensorRSSpace 0 r I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib r j x Λ).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))))
      ≤ κ * tensorInnerPointwise g₀ 0 r x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  classical
  set slotW : TensorRSSpace 0 r I x :=
    TensorRSSpace.ofCLM ((slotInsertEndoFib r j x Λ).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) with hslotW
  set Wm : ContinuousMultilinearMap ℝ (fun _ : Fin r ↦ TangentSpace I x) ℝ :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k ↦ g₀.inner x (e ((Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) k)))))
      with hWm
  have hcompW : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
      (J : Fin r → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e K J = Wm (fun k ↦ e (J k)) := by
    intro K J
    rw [hWm]
    rfl
  have hcompSlot : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E))
      (J : Fin r → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r slotW
          (Module.finrank ℝ E) e K J =
        Wm (Function.update (fun k ↦ e (J k)) j (Λ (e (J j)))) := by
    intro K J
    rw [hWm, hslotW]
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 r
          (TensorRSSpace.ofCLM ((slotInsertEndoFib r j x Λ).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)))
          (Module.finrank ℝ E) e K J =
        (slotInsertEndoFib r j x Λ
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k ↦ g₀.inner x (e (K k)))))) (fun k ↦ e (J k)) from rfl,
      slotFib_eval_at]
    rfl
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 r x
    e bse rfl hbse horth W slotW]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 r x
    e bse rfl hbse horth W W]
  have hKcollapse : ∀ (F : (Fin 0 → Fin (Module.finrank ℝ E)) → ℝ),
      (∑ K : Fin 0 → Fin (Module.finrank ℝ E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro b _ hb
      exact absurd (Subsingleton.elim b Fin.elim0) hb
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hKcollapse, hKcollapse]
  have hLHS : ∀ J : Fin r → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 r slotW
          (Module.finrank ℝ E) e Fin.elim0 J =
        Wm (fun k ↦ e (J k)) *
          Wm (Function.update (fun k ↦ e (J k)) j (Λ (e (J j)))) := by
    intro J
    rw [hcompW, hcompSlot]
  have hRHS : ∀ J : Fin r → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 r W
          (Module.finrank ℝ E) e Fin.elim0 J = Wm (fun k ↦ e (J k)) ^ 2 := by
    intro J
    rw [hcompW]
    ring
  rw [Finset.sum_congr rfl (fun J _ ↦ hLHS J),
    Finset.sum_congr rfl (fun J _ ↦ hRHS J)]
  set ee := Equiv.funSplitAt j (Fin (Module.finrank ℝ E)) with hee
  have hsplit : ∀ q : (Fin r → Fin (Module.finrank ℝ E)) → ℝ,
      (∑ J : Fin r → Fin (Module.finrank ℝ E), q J) =
        ∑ ρ : {i : Fin r // i ≠ j} → Fin (Module.finrank ℝ E),
          ∑ a : Fin (Module.finrank ℝ E), q (ee.symm (a, ρ)) := by
    intro q
    rw [← (Equiv.sum_comp ee.symm q), Fintype.sum_prod_type, Finset.sum_comm]
  rw [hsplit, hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum (fun ρ _ ↦ ?_)
  let z : Fin r → TangentSpace I x := fun k ↦
    if hkj : k = j then 0 else e (ρ ⟨k, hkj⟩)
  have hkval : ∀ a : Fin (Module.finrank ℝ E), (ee.symm (a, ρ)) j = a := by
    intro a
    rw [hee]
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hcoe : ∀ (a : Fin (Module.finrank ℝ E)) (k : Fin r) (hkj : k ≠ j),
      (ee.symm (a, ρ)) k = ρ ⟨k, hkj⟩ := by
    intro a k hkj
    rw [hee]
    simp [Equiv.funSplitAt, Equiv.piSplitAt, hkj]
  have harg : ∀ a : Fin (Module.finrank ℝ E),
      (fun k ↦ e ((ee.symm (a, ρ)) k)) = Function.update z j (e a) := by
    intro a
    funext k
    by_cases hkj : k = j
    · subst k
      rw [Function.update_self, hkval]
    · rw [Function.update_of_ne hkj, hcoe a k hkj]
      simp [z, hkj]
  simpa only [harg, hkval, Function.update_idem] using
    (multi_slotAt_le (I := I) (M := M) g₀ x j Λ hadj hbound e horth Wm z)

def gInvDiffSlotAt (g₀ g₁ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (W : TensorRSSpace 0 r I x) : TensorRSSpace 0 r I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib r j x (metricComparisonDiffEndo (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))

private noncomputable def negDiffSlotApplied
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) : TensorRSSpace 0 (s + 1) I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (-metricComparisonDiffEndo (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffSlot_eq_neg
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    negDiffSlotApplied (I := I) g₀ g₁ s x W =
      -gInvDiffSlotApplied (I := I) g₀ g₁ s x W := by
  rw [negDiffSlotApplied, gInvDiffSlotApplied,
    show (-metricComparisonDiffEndo (I := I) g₀ g₁ x) =
        (-1 : ℝ) • metricComparisonDiffEndo (I := I) g₀ g₁ x from
      (neg_one_smul ℝ _).symm,
    slotInsertEndoFib_smul_left (I := I) (M := M) (s + 1) 0 x,
    neg_one_smul, ContinuousLinearMap.neg_comp]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffSlot_model
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    TensorRSSpace.toModel
        (negDiffSlotApplied (I := I) g₀ g₁ s x W) =
      -TensorRSSpace.toModel
        (gInvDiffSlotApplied (I := I) g₀ g₁ s x W) := by
  rw [negDiffSlot_eq_neg (I := I) g₀ g₁ s x W, TensorRSSpace.toModel_neg]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffEndo_adjoint
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g₀.inner x ((-metricComparisonDiffEndo (I := I) g₀ g₁ x) a) b =
      g₀.inner x a ((-metricComparisonDiffEndo (I := I) g₀ g₁ x) b) := by
  simp only [ContinuousLinearMap.neg_apply, map_neg]
  rw [gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x a b]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    g₀.inner x ((-metricComparisonDiffEndo (I := I) g₀ g₁ x) v) v ≤
      (δ / (1 - δ)) * g₀.inner x v v := by
  rw [ContinuousLinearMap.neg_apply, map_neg]
  have hbnd := abs_inner_gInvDiffRaisedEndo_le
    (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v v
  have hv_nn : 0 ≤ g₀.inner x v v :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) =
      g₀.inner x v v := by
    rw [← Real.sqrt_mul hv_nn, Real.sqrt_mul_self hv_nn]
  calc
    -g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) v
        ≤ |g₀.inner x (metricComparisonDiffEndo (I := I) g₀ g₁ x v) v| := neg_le_abs _
    _ ≤ (δ / (1 - δ)) *
        (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := hbnd
    _ = (δ / (1 - δ)) * g₀.inner x v v := by rw [hsq]



omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem negDiffSlot_point_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (x : M) (W : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise g₀ 0 (s + 1) x
        (TensorRSSpace.toModel W)
        (-TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x W)) ≤
      (δ / (1 - δ)) * tensorInnerPointwise g₀ 0 (s + 1) x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_E (I := I) (M := M) g₀ x
  have hslot := tensorInnerPointwise_slotΛ_le g₀ s x
    (-metricComparisonDiffEndo (I := I) g₀ g₁ x)
    (negDiffEndo_adjoint (I := I) g₀ g₁ x)
    (fun v => negDiffEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth
  rw [← negDiffSlot_model (I := I) g₀ g₁ s x W]
  exact hslot



omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem neg_gInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (W : ∀ x, TensorRSSpace 0 (s + 1) I x)
    (hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
        (TensorRSSpace.toModel (W x))
        (-TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x))))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
        (TensorRSSpace.toModel (W x)) (TensorRSSpace.toModel (W x)))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 (s + 1)
        (fun x => TensorRSSpace.toModel (W x))
        (fun x => -TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x))) ≤
      (δ / (1 - δ)) * tensorL2Inner g₀ 0 (s + 1)
        (fun x => TensorRSSpace.toModel (W x)) (fun x => TensorRSSpace.toModel (W x)) := by
  refine tensorL2Inner_slotΛ_le g₀ s
    (fun x => TensorRSSpace.toModel (W x))
    (fun x => -TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x)))
    (fun x => ?_) hWS_int hWW_int
  exact negDiffSlot_point_le g₀ g₁ h htie hδ_lt hδ_nn hδ s x (W x)

private noncomputable def negDiffSlotAt
    (g₀ g₁ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (W : TensorRSSpace 0 r I x) : TensorRSSpace 0 r I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib (I := I) (M := M) r j x
        (-metricComparisonDiffEndo (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem negSlotAt_model
    (g₀ g₁ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (W : TensorRSSpace 0 r I x) :
    TensorRSSpace.toModel (negDiffSlotAt (I := I) g₀ g₁ r j x W) =
      -TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x W) := by
  rw [negDiffSlotAt, gInvDiffSlotAt,
    show (-metricComparisonDiffEndo (I := I) g₀ g₁ x) =
        (-1 : ℝ) • metricComparisonDiffEndo (I := I) g₀ g₁ x from
      (neg_one_smul ℝ _).symm,
    slotInsertEndoFib_smul_left (I := I) (M := M) r j x,
    neg_one_smul, ContinuousLinearMap.neg_comp]
  rfl



omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem negDiffSlotAt_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (r : ℕ) (j : Fin r) (x : M) (W : TensorRSSpace 0 r I x) :
    tensorInnerPointwise g₀ 0 r x
        (TensorRSSpace.toModel W)
        (-TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x W)) ≤
      (δ / (1 - δ)) * tensorInnerPointwise g₀ 0 r x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_E (I := I) (M := M) g₀ x
  have hslot := inner_slotAt_le (I := I) (M := M) g₀ r j x
    (-metricComparisonDiffEndo (I := I) g₀ g₁ x)
    (negDiffEndo_adjoint (I := I) g₀ g₁ x)
    (fun v ↦ negDiffEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth
  rw [← negSlotAt_model (I := I) g₀ g₁ r j x W]
  exact hslot


omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem negSlotAtL2_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (r : ℕ) (j : Fin r) (W : ∀ x, TensorRSSpace 0 r I x)
    (hWS_int : Integrable
      (fun x ↦ tensorInnerPointwise (I := I) (M := M) g₀ 0 r x
        (TensorRSSpace.toModel (W x))
        (-TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x (W x))))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x ↦ tensorInnerPointwise (I := I) (M := M) g₀ 0 r x
        (TensorRSSpace.toModel (W x)) (TensorRSSpace.toModel (W x)))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 r
        (fun x ↦ TensorRSSpace.toModel (W x))
        (fun x ↦ -TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x (W x))) ≤
      (δ / (1 - δ)) * tensorL2Inner g₀ 0 r
        (fun x ↦ TensorRSSpace.toModel (W x))
        (fun x ↦ TensorRSSpace.toModel (W x)) := by
  unfold tensorL2Inner
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono hWS_int (hWW_int.const_mul (δ / (1 - δ))) ?_
  intro x
  exact negDiffSlotAt_le g₀ g₁ h htie hδ_lt hδ_nn hδ r j x (W x)


end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
