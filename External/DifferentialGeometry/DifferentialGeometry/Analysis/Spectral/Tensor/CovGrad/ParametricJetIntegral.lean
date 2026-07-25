import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition








noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.L2

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (jointContMDiff_toModel_continuous_slice)

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

theorem joint_rs_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun z : M => TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in

theorem joint_rs_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun z : M => TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem rfns_joint_cont
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hSI : Set.Icc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r s p.2 ((Φ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
  have hIccprod : (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ _, hSI ht⟩
  have hswapCont : Continuous (fun p : ℝ × M => (p.2, p.1)) := by fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.2 ((Φ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswapCont.continuousOn hIccprod).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hψ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ)
        (E := fun x : M => TensorRSSpace r s I x →L[ℝ] TensorRSSpace r s I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ((tensorRSRiemannianInnerCLM_continuous (I := I) (M := M) g₀ r s).comp
      continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2 ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂ (F₁ := TensorRSModel r s ℝ E)
      (F₂ := TensorRSModel r s ℝ E) (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hψ hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2 ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    intro p hp
    have hp2 := ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r s p.2
          ((Φ p.1).toSection p.2) ((Φ p.1).toSection p.2)))).mp (happ p hp)).2
    exact hp2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r s x
      ((Φ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem path_field_congr
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hj₁ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ₁ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hj₂ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ₂ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hΦ : Φ₁ = Φ₂) :
    pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ₁ S hS hSI hj₁ =
      pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ₂ S hS hSI hj₂ := by
  subst hΦ
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private theorem icg_joint_smooth
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r s i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
    exact covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (s + j)
      (fun t => iteratedCovGrad (I := I) g₀ r s j (Φ t)) S ih

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private theorem icg_rfns_cont
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
        ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
  rfns_joint_cont (I := I) g₀ r (s + i)
    (fun t => iteratedCovGrad (I := I) g₀ r s i (Φ t)) S
    (by rw [Set.uIcc_of_le (zero_le_one (α := ℝ))] at hSI; exact hSI)
    (icg_joint_smooth (I := I) g₀ r s i Φ S hjoint)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] in
private theorem icg_norm_sq_int
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    IntervalIntegrable
      (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r s i (Φ t)‖ ^ 2) volume 0 1 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set F : ℝ × M → ℝ := fun p : ℝ × M =>
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
      ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2) with hF
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    icg_rfns_cont (I := I) g₀ r s i Φ S hSI hjoint
  have hnormsq : ∀ t : ℝ,
      ‖iteratedCovGrad (I := I) g₀ r s i (Φ t)‖ ^ 2 = ∫ x, F (t, x) ∂μ := by
    intro t
    rw [SmoothCcTensor.norm_def]
    have hsec : (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s + i) (x := x)
          ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x)) =
        (iteratedCovGrad (I := I) g₀ r s i (Φ t)).toFun := by
      funext x
      rw [SmoothCcTensor.toFun_apply]
    rw [← hsec,
      tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i)
        (fun x => (iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x)]
  have hcontInt : ContinuousOn (fun t : ℝ => ∫ x, F (t, x) ∂μ) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_of_compact_support (μ := μ) isCompact_univ hFcont
      (fun _ x _ hx => absurd (Set.mem_univ x) hx)
  have heq : (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r s i (Φ t)‖ ^ 2) =
      fun t : ℝ => ∫ x, F (t, x) ∂μ := funext hnormsq
  rw [heq]
  exact hcontInt.intervalIntegrable_of_Icc (by norm_num)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in


omit [NeZero (Module.finrank ℝ E)] in
theorem icg_path_comm
    (g₀ : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r s i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    iteratedCovGrad (I := I) g₀ r s i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (s + i)
        (fun t => iteratedCovGrad (I := I) g₀ r s i (Φ t)) S hS hSI hji := by
  induction i with
  | zero =>
    rw [iteratedCovGrad_zero]
    exact path_field_congr (I := I) g₀ r s Φ
      (fun t => iteratedCovGrad (I := I) g₀ r s 0 (Φ t)) S hS hSI hjoint hji
      (by funext t; rw [iteratedCovGrad_zero])
  | succ j ih =>
    have hjg_j := icg_joint_smooth (I := I) g₀ r s j Φ S hjoint
    have hjgsucc := covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (s + j)
      (fun t => iteratedCovGrad (I := I) g₀ r s j (Φ t)) S hjg_j
    rw [iteratedCovGrad_succ, ih hjg_j]
    rw [covGrad_pathIntegral_comm (I := I) (M := M) g₀ r (s + j)
      (fun t => iteratedCovGrad (I := I) g₀ r s j (Φ t)) S hS hSI hjg_j hjgsucc]
    exact path_field_congr (I := I) g₀ r (s + j + 1)
      (fun t => covGrad (I := I) (M := M) g₀ r (s + j)
        (iteratedCovGrad (I := I) g₀ r s j (Φ t)))
      (fun t => iteratedCovGrad (I := I) g₀ r s (j + 1) (Φ t)) S hS hSI hjgsucc hji
      (by funext t; rw [iteratedCovGrad_succ])

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in


omit [NeZero (Module.finrank ℝ E)] in
theorem path_jetL2_le
    (g₀ : SmoothRiemannianMetric I M) (r s a : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    {B : ℝ} (hB : 0 ≤ B)
    (hΦjet : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ r s i (Φ t)‖ ^ 2) ≤ B ^ 2) :
    (∑ i ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ r s i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint)‖ ^ 2) ≤ B ^ 2 := by
  have hji : ∀ i ∈ Finset.range (a + 1),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (s + i) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (s + i) ℝ E)
          (E := fun z : M => TensorRSSpace r (s + i) I z) q.1
          ((iteratedCovGrad (I := I) g₀ r s i (Φ q.2)).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
    fun i _ => icg_joint_smooth (I := I) g₀ r s i Φ S hjoint
  have hci : ∀ i ∈ Finset.range (a + 1), ∀ x : M,
      ContinuousOn (fun t : ℝ =>
        TensorRSSpace.toModel ((iteratedCovGrad (I := I) g₀ r s i (Φ t)).toSection x))
        (Set.Icc (0 : ℝ) 1) := by
    intro i hi x
    exact (jointContMDiff_toModel_continuous_slice (I := I) g₀ r (s + i)
      (fun t => iteratedCovGrad (I := I) g₀ r s i (Φ t)) S (hji i hi) x).mono
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI)
  have hri : ∀ i ∈ Finset.range (a + 1),
      ContinuousOn (fun p : ℝ × M =>
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) p.2
          ((iteratedCovGrad (I := I) g₀ r s i (Φ p.1)).toSection p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    fun i _ => icg_rfns_cont (I := I) g₀ r s i Φ S hSI hjoint
  have hii : ∀ i ∈ Finset.range (a + 1),
      IntervalIntegrable
        (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r s i (Φ t)‖ ^ 2) volume 0 1 :=
    fun i _ => icg_norm_sq_int (I := I) g₀ r s i Φ S hSI hjoint
  have hcomm : ∀ (i : ℕ) (hi : i ∈ Finset.range (a + 1)),
      iteratedCovGrad (I := I) g₀ r s i
          (pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint) =
        pathIntegralCoeffField (I := I) (M := M) g₀ r (s + i)
          (fun t => iteratedCovGrad (I := I) g₀ r s i (Φ t)) S hS hSI (hji i hi) :=
    fun i hi => icg_path_comm (I := I) g₀ r s i Φ S hS hSI hjoint (hji i hi)
  exact iteratedCovGrad_pathIntegralCoeffField_jetL2_le (I := I) (M := M)
    g₀ r s a Φ B hB S hS hSI hjoint hΦjet hji hci hri hii hcomm

end DifferentialGeometry.Integral.L2
