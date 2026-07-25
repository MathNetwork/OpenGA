import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ParametricAppCcJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantLeibniz
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Tensor.RSTensor.RankZero










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem rank_zero_one (x : M) (c : Tensor0SSpace 0 I x) :
    tensor0SSpace_evalScalar x c •
        Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) ∞ x = c := by
  apply (tensor0SSpace_continuousLinearEquiv 0 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel
      (tensor0SSpace_evalScalar x c •
        Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) ∞ x) v = Tensor0SSpace.toModel c v
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SField.one0_apply, smul_eq_mul, mul_one,
    Tensor0SSpace.evalScalar_apply]
  exact congrArg (Tensor0SSpace.toModel c) (Subsingleton.elim Fin.elim0 v)


noncomputable def scalarCc (g : SmoothRiemannianMetric I M)
    (zeta : C^∞⟮I, M; ℝ⟯) : SmoothCcTensor g 0 0 where
  toSection := tensorRSField_smulByFun ∞ (zeta : M → ℝ) zeta.contMDiff
    ((Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) ∞).toTensorRSField ∞)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in


@[simp] theorem scalar0_scalarCc (g : SmoothRiemannianMetric I M)
    (zeta : C^∞⟮I, M; ℝ⟯) :
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (scalarCc (I := I) (M := M) g zeta).toSection =
      (zeta : M → ℝ) := by
  funext x
  simp only [scalarCc, TensorRSField.scalar0,
    Tensor0SField.toScalarField, TensorRSField.rs0_apply,
    tensorRSField_smulByFun_apply]
  change Tensor0SSpace.toModel
    ((((zeta : M → ℝ) x) •
      ((Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) ∞).toTensorRSField ∞ x))
      (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) ∞ x)) Fin.elim0 = (zeta : M → ℝ) x
  rw [ContinuousLinearMap.smul_apply, Tensor0SField.toRS0_apply,
    rank_zero_one, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, Tensor0SField.one0_apply,
    smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] in


theorem unit_init_or_empty (g : SmoothRiemannianMetric I M) :
    IsEmpty M ∨
      ∃ u0 : SmoothCcTensor g 0 0,
        (∀ x : M, 0 <
          TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
            u0.toSection x) ∧
        (∫ x,
            TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
              u0.toSection x
          ∂(Measure.riemannianVolumeMeasure (I := I) (M := M) g)) = 1 := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact Or.inl hM
  · letI : Nonempty M := hM
    let μ := Measure.riemannianVolumeMeasure (I := I) (M := M) g
    letI : IsFiniteMeasure μ :=
      Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
        (I := I) (M := M) g
    letI : μ.IsOpenPosMeasure :=
      Measure.riemannianVolumeMeasure_isOpenPosMeasure
        (I := I) (M := M) g
    let vol : ℝ := (μ Set.univ).toReal
    have hvol : 0 < vol := by
      exact ENNReal.toReal_pos
        (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
        (measure_ne_top μ Set.univ)
    let zeta : C^∞⟮I, M; ℝ⟯ :=
      ⟨fun _ => vol⁻¹, contMDiff_const⟩
    refine Or.inr ⟨scalarCc (I := I) (M := M) g zeta, ?_, ?_⟩
    · intro x
      rw [scalar0_scalarCc]
      exact inv_pos.mpr hvol
    · rw [scalar0_scalarCc]
      change (∫ _x : M, vol⁻¹ ∂μ) = 1
      rw [MeasureTheory.integral_const, smul_eq_mul,
        MeasureTheory.measureReal_def]
      exact mul_inv_cancel₀ hvol.ne'


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem app_scalarCc (g : SmoothRiemannianMetric I M)
    (zeta : C^∞⟮I, M; ℝ⟯) (U : SmoothCcTensor g 0 0) :
    operatorFieldApply (I := I) (M := M) g 0 0 (scalarCc (I := I) (M := M) g zeta) U =
      scalarSmul (I := I) (M := M) g 0 0 zeta U := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, scalarSmul_toSection_apply]
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.comp_apply]
  change (((zeta : M → ℝ) x) •
      ((Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) ∞).toTensorRSField ∞ x))
        (U.toSection x c) = ((zeta : M → ℝ) x) • U.toSection x c
  rw [ContinuousLinearMap.smul_apply, Tensor0SField.toRS0_apply,
    rank_zero_one]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] in


theorem scalar0_smul_cc (g : SmoothRiemannianMetric I M)
    (zeta : C^∞⟮I, M; ℝ⟯) (U : SmoothCcTensor g 0 0) (x : M) :
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (scalarSmul (I := I) (M := M) g 0 0 zeta U).toSection x =
      (zeta : M → ℝ) x *
        TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection x := by
  simp only [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply]
  change ((((zeta : M → ℝ) x) • U.toSection x) _).toModel Fin.elim0 = _
  rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_rs_smul {r s : ℕ} {S : Set ℝ}
    (f : M × ℝ → ℝ)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f
      ((Set.univ : Set M) ×ˢ S))
    (A : ∀ p : M × ℝ, TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun x : M => TensorRSSpace r s I x) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun x : M => TensorRSSpace r s I x) p.1 (f p • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun x : M => TensorRSSpace r s I x) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r s ℝ E)
    (E := fun x : M => TensorRSSpace r s I x)).mp (hA p₀ hp₀)
  refine ((hf p₀ hp₀).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hp
    exact (e.linear ℝ hp).map_smul (f p) (A p)
  · exact (e.linear ℝ (by
      rw [he, ← hx₀]
      exact mem_baseSet_trivializationAt _ _ x₀)).map_smul (f p₀) (A p₀)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in


theorem scalarCc_joint (g : SmoothRiemannianMetric I M)
    (zeta : ℝ → C^∞⟮I, M; ℝ⟯) {S : Set ℝ}
    (hzeta : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => (zeta p.2 : M → ℝ) p.1)
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 0 ℝ E)
        (E := fun x : M => TensorRSSpace 0 0 I x) p.1
        ((scalarCc (I := I) (M := M) g (zeta p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  let A : TensorRSField ∞ 0 0 (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) :=
    (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) ∞).toTensorRSField ∞
  have hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 0 ℝ E)
        (E := fun x : M => TensorRSSpace 0 0 I x) p.1 (A p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    A.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hsmul := joint_rs_smul (I := I) (M := M)
    (fun p : M × ℝ => (zeta p.2 : M → ℝ) p.1) hzeta
    (fun p : M × ℝ => A p.1) hA
  exact hsmul.congr fun p _ => rfl




theorem smul_jet_unif (g : SmoothRiemannianMetric I M)
    (zeta : ℝ → C^∞⟮I, M; ℝ⟯) {S K : Set ℝ}
    (hK : IsCompact K) (hKS : K ⊆ S)
    (hzeta : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => (zeta p.2 : M → ℝ) p.1)
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t, t ∈ K → ∀ (U : SmoothCcTensor g 0 0) (j : ℕ),
        ‖iteratedCovGrad (I := I) g 0 0 j
          (scalarSmul (I := I) (M := M) g 0 0 (zeta t) U)‖ ≤
            C j * ∑ l ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g 0 0 l U‖ := by
  obtain ⟨C, hC, hbound⟩ := param_app_jet (I := I) (M := M) g 0 0
    (fun t => scalarCc (I := I) (M := M) g (zeta t)) hK hKS
    (scalarCc_joint (I := I) (M := M) g zeta hzeta)
  refine ⟨C, hC, ?_⟩
  intro t ht U j
  simpa only [app_scalarCc] using hbound t ht U j

end Connection
end Integral
end DifferentialGeometry

end
