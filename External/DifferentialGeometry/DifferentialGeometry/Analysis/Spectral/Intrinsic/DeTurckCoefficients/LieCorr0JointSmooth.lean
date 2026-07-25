import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Core









noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff Matrix

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff
    deTurckVFCovDeriv connDiffOp_homSection_contMDiff metricConnDiffLoweredFib
    metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank
    domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

open LieCorr0Core

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckVF_realizedFam_jointContMDiffOn metricConnDiffLowered_selfFam_jointContMDiffOn metricConnDiffLowered_bgFam_jointContMDiffOn jointTensor0SProd_local deTurckLieWEndo_realizedFam_jointContMDiffOn deTurckLieCoeffField deTurckLieCoeffField_realizedFam_jointSmooth linearizedRicciThreeArmHjoint)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (interiorProductField_jointContMDiffOn_vecJoint inverseMetricSharpField_realizedFam_jointContMDiffOn domDomCongrField_jointContMDiffOn cometricDoubleTraceFib_realizedFam_jointContMDiffOn slotInsertEndo0Field_apply_jointContMDiffOn slotInsertEndo1Field_apply_jointContMDiffOn contMDiffOn_clm_section_of_pointwise_joint_manifold_time)
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

section LieCorr0Joint

variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lieCorr0_jhom_sub_local {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (E →L[ℝ] E)
    (fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] E)
    (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] E)
    (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lieCorr0_jhom_smulConst_local {S : Set ℝ} (c : ℝ)
    (A : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (c • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (E →L[ℝ] E)
    (fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] E)
    (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul c (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      c (A p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lieCorr0_j0S_add_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lieCorr0_j0S_smulConst_local {d : ℕ} {S : Set ℝ} (c : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (c • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul c (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      c (A p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lieCorr0_toModel_g0Flat (g : SmoothRiemannianMetric I M) (x : M)
    (w t : TangentSpace I x) :
    Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (Fin.cons t (fun i => Fin.elim0 i)) = g.inner x w t := by
  have h1 : Tensor0SSpace.toModel
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) =
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (fun _ : Fin 1 => t) := by
    change (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) = _
    congr 1
    funext j
    refine Fin.cases rfl (fun j => j.elim0) j
  rw [h1, ← Tensor0SBundle.cotangentToDual_apply (I := I) (x := x) _ t]
  exact DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g x w t

private theorem lieCorr0_connDiffVF_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gP : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1) (Z p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hM := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hW := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' gP
  have hι1 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP : Π b : M, TangentSpace I b) p.1) hW
    (α := fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1) hM
  have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hι2 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => Z p.1) hZjoint
    (α := fun p : M × ℝ => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
      ((PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP : Π b : M, TangentSpace I b) p.1)
      (metricConnDiffLoweredFib (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) hι1
  have hsharp := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hι2
  refine hsharp.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hform : Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP : Π b : M, TangentSpace I b) p.1)
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1) (Z p.1)) := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hm : m = Fin.cons (m 0) (fun i => Fin.elim0 i) := by
      funext j
      refine Fin.cases rfl (fun j => j.elim0) j
    have e1 : Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1)
            (metricConnDiffLoweredFib (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      change Tensor0SSpace.toModel
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
        (Fin.cons ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1)
          (Fin.cons (Z p.1) m)) = _
      rw [metricConnDiffLoweredFib_toModel]
      rfl
    have e2 : Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      refine Eq.trans (congrArg (Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1)))) hm) ?_
      exact lieCorr0_toModel_g0Flat (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 _ (m 0)
    exact e1.trans e2.symm
  rw [hform, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]

private theorem lieCorr0_connDiffVFEndo_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gP : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ =>
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
            Π b : M, TangentSpace I b) p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Z
  exact lieCorr0_connDiffVF_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' gP Z

private theorem lieCorr0NEndo_realizedFam_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (lieCorr0NEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hBV := lieCorr0_connDiffVFEndo_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hBW := lieCorr0_connDiffVFEndo_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hW := deTurckLieWEndo_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hsub1 := lieCorr0_jhom_sub_local (I := I)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hBV hBW
  have hsub2 := lieCorr0_jhom_sub_local (I := I)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hsub1 hW
  refine hsub2.congr (fun p _ => ?_)
  rfl

omit [CompactSpace M] in
private theorem lieCorr0TraceStepFam_jointContMDiffOn (p : ℕ) (σ : Equiv.Perm (Fin (p + 2)))
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ pp : M × ℝ, Tensor0SSpace (p + 2) I pp.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) pp.1 (Z pp))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) pp.1
        (lieCorr0TraceStep (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) p σ pp.1 (Z pp)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hddc := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Z hZ
  have htr := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := p)
    g₀ T T' hδ hδ' _ hddc
  refine htr.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) pp.1 t) ?_
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem lieCorr0TraceStepFixed_jointContMDiffOn (g : SmoothRiemannianMetric I M)
    (p : ℕ) (σ : Equiv.Perm (Fin (p + 2))) {S : Set ℝ}
    (Z : ∀ pp : M × ℝ, Tensor0SSpace (p + 2) I pp.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) pp.1 (Z pp))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) pp.1
        (lieCorr0TraceStep (I := I) g p σ pp.1 (Z pp)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hddcJ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) pp.1
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := pp.1)
          (ContinuousMultilinearMap.domDomCongr σ (Tensor0SSpace.toModel (Z pp)))))
      ((Set.univ : Set M) ×ˢ S) :=
    domDomCongrField_jointContMDiffOn (I := I) σ (S := S) Z hZ
  have hhom : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel (p + 2) p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (TensorRSModel (p + 2) p ℝ E)
        (E := fun z : M => TensorRSSpace (p + 2) p I z) pp.1
        (cometricDoubleTraceFib (I := I) g p pp.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (cometricDoubleTraceFib_contMDiff (I := I) g p).comp_contMDiffOn contMDiffOn_fst
  have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hhom hddcJ
  refine happ.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) pp.1 t) ?_
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

private theorem lieCorr0InsertFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0InsertFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hΛ := lieCorr0NEndo_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have h0 := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun pp : M × ℝ =>
      lieCorr0NEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1) hΛ
    (A := fun pp : M × ℝ => Y pp.1) hY
  have h1 := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀
    (Λ := fun pp : M × ℝ =>
      lieCorr0NEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1) hΛ
    (A := fun pp : M × ℝ => Y pp.1) hY
  have hsum := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h0 h1
  refine hsum.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0InsertFib, ContinuousLinearMap.add_apply]

private theorem lieCorr0VBFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0VBFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) pp.1 (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hVF := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hip := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun pp : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ : Π b : M, TangentSpace I b) pp.1) hVF
    (α := fun pp : M × ℝ => Y pp.1) hY
  have hLB := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hprod := jointTensor0SProd_local (I := I) (p := 1) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 pp.1
      ((PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ : Π b : M, TangentSpace I b) pp.1)
      (Y pp.1))
    (fun pp : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1)
    hip hLB
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1
          (metricConnDiffLoweredFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 pp.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ :
                Π b : M, TangentSpace I b) pp.1) (Y pp.1))))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
      (E := fun z : M => Tensor0SSpace 4 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 2 lieCorr0VBPerm hδ hδ' _
    hprod'
  have hs := lieCorr0_j0S_smulConst_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (2 : ℝ) _ htr
  refine hs.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0VBFib]
  rfl

private theorem lieCorr0AMixHalfFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0AMixHalfFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hLB := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hLA := metricConnDiffLowered_bgFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hprod1 := jointTensor0SProd_local (I := I) (p := 2) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => Y pp.1)
    (fun pp : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1)
    hY hLB
  have hprod1' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 5 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 5 ℝ E)
        (E := fun z : M => Tensor0SSpace 5 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1
          (metricConnDiffLoweredFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1) (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod1.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 5 ℝ E)
      (E := fun z : M => Tensor0SSpace 5 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr1 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 3 lieCorr0AMixPermQ
    hδ hδ' _ hprod1'
  have hprod2 := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => lieCorr0TraceStep (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) 3 lieCorr0AMixPermQ pp.1
      (tensor0SProdKappaFib (I := I) pp.1
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1) (Y pp.1)))
    (fun pp : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1)
    htr1 hLA
  have hprod2' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun z : M => Tensor0SSpace 6 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1
          (metricConnDiffLoweredFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1)
          (lieCorr0TraceStep (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) 3 lieCorr0AMixPermQ pp.1
            (tensor0SProdKappaFib (I := I) pp.1
              (metricConnDiffLoweredFib (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
                (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1) (Y pp.1)))))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod2.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun z : M => Tensor0SSpace 6 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr2 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 4 lieCorr0AMixPerm1
    hδ hδ' _ hprod2'
  have htr3 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 2 lieCorr0AMixPerm2
    hδ hδ' _ htr2
  refine htr3.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0AMixHalfFib]
  rfl

private theorem lieCorr0AMixFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0AMixFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hhalf := lieCorr0AMixHalfFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have hswapRaw := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap 0 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => lieCorr0AMixHalfFib (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1 (Y pp.1)) hhalf
  have hswap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) pp.1
          (lieCorr0AMixHalfFib (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1 (Y pp.1))))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hswapRaw.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
    rw [domDomCongrFibRank_apply]
  have hadd := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hhalf hswap
  have hs := lieCorr0_j0S_smulConst_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (2 : ℝ) _ hadd
  refine hs.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0AMixFib]
  rfl

omit [CompactSpace M] in
private theorem lieCorr0RiemFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0RiemFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) pp.1 (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) pp.1
        (lieCorr0RiemLoweredFib (I := I) g₀ pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  have hprod := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => Y pp.1)
    (fun pp : M × ℝ => lieCorr0RiemLoweredFib (I := I) g₀ pp.1)
    hY hR
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun z : M => Tensor0SSpace 6 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1 (lieCorr0RiemLoweredFib (I := I) g₀ pp.1) (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun z : M => Tensor0SSpace 6 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr1 := lieCorr0TraceStepFixed_jointContMDiffOn (I := I) g₀ 4 lieCorr0RiemPerm1
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprod'
  have htr2 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 2 lieCorr0RiemPerm2
    hδ hδ' _ htr1
  have hs := lieCorr0_j0S_smulConst_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (-1 : ℝ) _ htr2
  refine hs.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0RiemFib]
  rfl

private theorem lieCorr0TotalFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0TotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have h1 := lieCorr0InsertFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have h2 := lieCorr0VBFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' Y
  have h3 := lieCorr0AMixFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have h4 := lieCorr0RiemFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' Y
  have h12 := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h1 h2
  have h123 := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h12 h3
  have h1234 := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h123 h4
  refine h1234.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0TotalFib]
  rfl



theorem lieCorr0_path_joint
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => lieCorr0Field (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint]
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun pp : M × ℝ =>
      lieCorr0TotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => lieCorr0TotalFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) pp.1 t) ?_
  rw [lieCorr0Field_apply]
  rfl

end LieCorr0Joint

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
