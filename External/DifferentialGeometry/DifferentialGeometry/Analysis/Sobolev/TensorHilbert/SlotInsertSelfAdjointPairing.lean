import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs

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
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem multilinear_slot0_pairing_self_adjoint
    (g₀ : SmoothRiemannianMetric I M) (x : M) {s : ℕ}
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (Am Bm : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ)
    (J' : Fin s → Fin (Module.finrank ℝ E)) :
    (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (e a) (fun k => e (J' k))) *
          Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))) := by
  classical
  set φA : TangentSpace I x →L[ℝ] ℝ :=
    (Am.toContinuousLinearMap (Fin.cons (0 : TangentSpace I x) (fun k => e (J' k))) 0).comp
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) with hφA_def
  have hφA_apply : ∀ u : TangentSpace I x,
      φA u = Am (Fin.cons u (fun k => e (J' k))) := by
    intro u
    rw [hφA_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  set φB : TangentSpace I x →L[ℝ] ℝ :=
    (Bm.toContinuousLinearMap (Fin.cons (0 : TangentSpace I x) (fun k => e (J' k))) 0).comp
      (ContinuousLinearMap.id ℝ (TangentSpace I x)) with hφB_def
  have hφB_apply : ∀ u : TangentSpace I x,
      φB u = Bm (Fin.cons u (fun k => e (J' k))) := by
    intro u
    rw [hφB_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  set wA : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
      (I := I) g₀ x φA.toLinearMap with hwA_def
  set wB : TangentSpace I x :=
    DifferentialGeometry.Integral.DivergenceTheorem.metricSharp
      (I := I) g₀ x φB.toLinearMap with hwB_def
  have hwA_inner : ∀ u : TangentSpace I x, g₀.inner x wA u = φA u := by
    intro u
    rw [hwA_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp
      (I := I) g₀ x φA.toLinearMap u
  have hwB_inner : ∀ u : TangentSpace I x, g₀.inner x wB u = φB u := by
    intro u
    rw [hwB_def]
    exact DifferentialGeometry.Integral.DivergenceTheorem.inner_metricSharp
      (I := I) g₀ x φB.toLinearMap u
  have hAe : ∀ a : Fin (Module.finrank ℝ E),
      Am (Fin.cons (e a) (fun k => e (J' k))) = g₀.inner x wA (e a) := by
    intro a; rw [hwA_inner, hφA_apply]
  have hAΛe : ∀ a : Fin (Module.finrank ℝ E),
      Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) = g₀.inner x wA (Λ (e a)) := by
    intro a; rw [hwA_inner, hφA_apply]
  have hBe : ∀ a : Fin (Module.finrank ℝ E),
      Bm (Fin.cons (e a) (fun k => e (J' k))) = g₀.inner x wB (e a) := by
    intro a; rw [hwB_inner, hφB_apply]
  have hBΛe : ∀ a : Fin (Module.finrank ℝ E),
      Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) = g₀.inner x wB (Λ (e a)) := by
    intro a; rw [hwB_inner, hφB_apply]
  have hLHS : (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (e a) (fun k => e (J' k))) *
          Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
      = g₀.inner x (Λ wB) wA := by
    have hsum_eq : (∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (e a) (fun k => e (J' k))) *
            Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) (Λ wB) * g₀.inner x (e a) wA := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hAe a, hBΛe a]
      rw [g₀.symm x wA (e a)]
      have hadj' : g₀.inner x wB (Λ (e a)) = g₀.inner x (Λ wB) (e a) := by
        rw [g₀.symm x wB (Λ (e a)), hadj (e a) wB, g₀.symm x (e a) (Λ wB)]
      rw [hadj', g₀.symm x (Λ wB) (e a)]
      ring
    rw [hsum_eq, g0_polarized_parseval (I := I) g₀ x e horth (Λ wB) wA]
  have hRHS : (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
          Bm (Fin.cons (e a) (fun k => e (J' k))))
      = g₀.inner x (Λ wA) wB := by
    have hsum_eq : (∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (e a) (Λ wA) * g₀.inner x (e a) wB := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hAΛe a, hBe a]
      rw [g₀.symm x wB (e a)]
      have hadj' : g₀.inner x wA (Λ (e a)) = g₀.inner x (Λ wA) (e a) := by
        rw [g₀.symm x wA (Λ (e a)), hadj (e a) wA, g₀.symm x (e a) (Λ wA)]
      rw [hadj', g₀.symm x (Λ wA) (e a)]
    rw [hsum_eq, g0_polarized_parseval (I := I) g₀ x e horth (Λ wA) wB]
  rw [hLHS, hRHS]
  rw [hadj wB wA, g₀.symm x wB (Λ wA)]

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorInnerPointwise_slotΛ_self_adjoint
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (hadj : ∀ a b : TangentSpace I x, g₀.inner x (Λ a) b = g₀.inner x a (Λ b))
    (A B : TensorRSSpace 0 (s + 1) I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    tensorInnerPointwise g₀ 0 (s + 1) x
        (TensorRSSpace.toModel
          (show TensorRSSpace 0 (s + 1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A))))
        (TensorRSSpace.toModel B)
      = tensorInnerPointwise g₀ 0 (s + 1) x
          (TensorRSSpace.toModel A)
          (TensorRSSpace.toModel
            (show TensorRSSpace 0 (s + 1) I x from
              TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)))) := by
  classical
  set slotA : TensorRSSpace 0 (s + 1) I x :=
    TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)) with hslotA
  set slotB : TensorRSSpace 0 (s + 1) I x :=
    TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)) with hslotB
  set Am : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e ((Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) k))))) with hAm
  set Bm : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I x) ℝ :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g₀.inner x (e ((Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) k))))) with hBm
  have hcompA : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E)) (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) A (Module.finrank ℝ E) e K J
        = Am (fun k => e (J k)) := by
    intro K J; rw [hAm]; rfl
  have hcompB : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E)) (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) B (Module.finrank ℝ E) e K J
        = Bm (fun k => e (J k)) := by
    intro K J; rw [hBm]; rfl
  have hcompSlotA : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E)) (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotA (Module.finrank ℝ E) e K J
        = Am (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro K J
    rw [hAm, hslotA]
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1)
          (TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A))) (Module.finrank ℝ E) e K J
        = (slotInsertEndoFib (s + 1) 0 x Λ
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K k)))))) (fun k => e (J k)) from rfl,
      slotInsertEndoFib_bundle_eval]
    rfl
  have hcompSlotB : ∀ (K : Fin 0 → Fin (Module.finrank ℝ E)) (J : Fin (s + 1) → Fin (Module.finrank ℝ E)),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotB (Module.finrank ℝ E) e K J
        = Bm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro K J
    rw [hBm, hslotB]
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1)
          (TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x Λ).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B))) (Module.finrank ℝ E) e K J
        = (slotInsertEndoFib (s + 1) 0 x Λ
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from B)
              ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
                (fun k => g₀.inner x (e (K k)))))) (fun k => e (J k)) from rfl,
      slotInsertEndoFib_bundle_eval]
    rfl
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 (s + 1) x e bse rfl hbse horth slotA B]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g₀ 0 (s + 1) x e bse rfl hbse horth A slotB]
  have hKcollapse : ∀ (F : (Fin 0 → Fin (Module.finrank ℝ E)) → ℝ),
      (∑ K : Fin 0 → Fin (Module.finrank ℝ E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro b _ hb; exact absurd (Subsingleton.elim b Fin.elim0) hb
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hKcollapse, hKcollapse]
  have hLHS : ∀ J : Fin (s + 1) → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotA (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) B (Module.finrank ℝ E) e Fin.elim0 J
      = Am (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) * Bm (fun k => e (J k)) := by
    intro J; rw [hcompSlotA, hcompB]
  have hRHS : ∀ J : Fin (s + 1) → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) A (Module.finrank ℝ E) e Fin.elim0 J *
        fiberNormSqComponent (I := I) (M := M) g₀ x 0 (s + 1) slotB (Module.finrank ℝ E) e Fin.elim0 J
      = Am (fun k => e (J k)) * Bm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) := by
    intro J; rw [hcompSlotB, hcompA]
  rw [Finset.sum_congr rfl (fun J _ => hLHS J), Finset.sum_congr rfl (fun J _ => hRHS J)]
  have hsplit : ∀ G : (Fin (s + 1) → Fin (Module.finrank ℝ E)) → ℝ,
      (∑ J : Fin (s + 1) → Fin (Module.finrank ℝ E), G J)
        = ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E), G (Fin.cons a J') := by
    intro G
    rw [← (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E))).sum_comp G,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  rw [hsplit (fun J => Am (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) * Bm (fun k => e (J k))),
    hsplit (fun J => Am (fun k => e (J k)) * Bm (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))))]
  refine Finset.sum_congr rfl (fun J' _ => ?_)
  have hkey := multilinear_slot0_pairing_self_adjoint (I := I) (M := M) g₀ x Λ hadj e horth Bm Am J'
  have hLHSeq : (∑ a : Fin (Module.finrank ℝ E),
        Am (Function.update (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
            (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))) *
          Bm (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k))
        = Fin.cons (e a) (fun k => e (J' k)) := by
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    have h2 : Function.update (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
          (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))
        = Fin.cons (Λ (e a)) (fun k => e (J' k)) := by
      rw [show ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0) = a from rfl]
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    rw [h2, h1]
  have hRHSeq : (∑ a : Fin (Module.finrank ℝ E),
        Am (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) *
          Bm (Function.update (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
            (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (e a) (fun k => e (J' k))) *
            Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k))
        = Fin.cons (e a) (fun k => e (J' k)) := by
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    have h2 : Function.update (fun k => e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) 0
          (Λ (e ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0)))
        = Fin.cons (Λ (e a)) (fun k => e (J' k)) := by
      rw [show ((Fin.cons a J' : Fin (s + 1) → Fin (Module.finrank ℝ E)) 0) = a from rfl]
      funext i; rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,rfl⟩
      · subst hi; simp
      · simp
    rw [h2, h1]
  rw [hLHSeq, hRHSeq]
  have hkey' : (∑ a : Fin (Module.finrank ℝ E),
        Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
          Bm (Fin.cons (e a) (fun k => e (J' k))))
      = ∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (e a) (fun k => e (J' k))) *
            Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) := by
    have hkeyL : (∑ a : Fin (Module.finrank ℝ E),
          Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Bm (Fin.cons (e a) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            Bm (Fin.cons (e a) (fun k => e (J' k))) *
              Am (Fin.cons (Λ (e a)) (fun k => e (J' k))) :=
      Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hkeyR : (∑ a : Fin (Module.finrank ℝ E),
          Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) *
            Am (Fin.cons (e a) (fun k => e (J' k))))
        = ∑ a : Fin (Module.finrank ℝ E),
            Am (Fin.cons (e a) (fun k => e (J' k))) *
              Bm (Fin.cons (Λ (e a)) (fun k => e (J' k))) :=
      Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [hkeyL, hkey, hkeyR]
  rw [hkey']

omit [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorL2Inner_appCc_slotInsertEndoCc_self_adjoint
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (hadj : ∀ (x : M) (a b : TangentSpace I x),
      g₀.inner x (Λ x a) b = g₀.inner x a (Λ x b))
    (A B : SmoothCcTensor g₀ 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g₀ 0 (s + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) A).toFun
        B.toFun =
      tensorL2Inner (I := I) (M := M) g₀ 0 (s + 1)
        A.toFun
        (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) B).toFun := by
  classical
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only []
  obtain ⟨e, bse, hbse, horth⟩ :=
    exists_orthoFrame_basis_E (I := I) (M := M) g₀ x
  have hslotA :
      (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) A).toFun x =
        TensorRSSpace.toModel
          (show TensorRSSpace 0 (s + 1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x (Λ x)).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                A.toSection x))) := rfl
  have hslotB :
      (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) B).toFun x =
        TensorRSSpace.toModel
          (show TensorRSSpace 0 (s + 1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x (Λ x)).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                B.toSection x))) := rfl
  rw [hslotA, hslotB, SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply]
  exact tensorInnerPointwise_slotΛ_self_adjoint (I := I) (M := M) g₀ s x (Λ x)
    (hadj x) (A.toSection x) (B.toSection x) e bse hbse horth

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
