import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSubstitutionFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricConnDiffLoweredTrilinear


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpace0S_add_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpace0S_sub_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTotalSpace0S_smulFun_local {d : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointTensor0SProd_local {p q : ℕ} {S : Set ℝ}
    (A : ∀ pp : M × ℝ, Tensor0SBundle.Tensor0SSpace p I pp.1)
    (B : ∀ pp : M × ℝ, Tensor0SBundle.Tensor0SSpace q I pp.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z) pp.1 (A pp))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel q ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z) pp.1 (B pp))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace (p + q) I z) pp.1
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := pp.1)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
            (Tensor0SBundle.Tensor0SSpace.toModel (B pp)))))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) p
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) q
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (p + q)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace p I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel q ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace q I z)).mp (hB p₀ hp₀)
  have h_combine : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.Tensor0SModel (p + q) ℝ E) ∞
      (fun pp : M × ℝ => modelProdCLM (E := E) p q
        ((trivializationAt (Tensor0SBundle.Tensor0SModel p ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace p I z) x₀ ⟨pp.1, A pp⟩).2)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel q ℝ E)
          (fun z : M => Tensor0SBundle.Tensor0SSpace q I z) x₀ ⟨pp.1, B pp⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    ((contMDiffWithinAt_const (c := modelProdCLM (E := E) p q)).clm_apply
      hA'.2).clm_apply hB'.2
  refine h_combine.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Filter.univ_mem] with pp _
    apply ContinuousMultilinearMap.ext
    intro v
    rw [modelProdCLM_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
    change (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1
            ((v ∘ Fin.castAdd q) i)) *
        (Tensor0SBundle.Tensor0SSpace.toModel (B pp))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1
            ((v ∘ Fin.natAdd p) i)) =
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SBundle.Tensor0SSpace.toModel (A pp))
        (Tensor0SBundle.Tensor0SSpace.toModel (B pp)))
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ pp.1 (v i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  · apply ContinuousMultilinearMap.ext
    intro v
    rw [modelProdCLM_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
    change (Tensor0SBundle.Tensor0SSpace.toModel (A p₀))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1
            ((v ∘ Fin.castAdd q) i)) *
        (Tensor0SBundle.Tensor0SSpace.toModel (B p₀))
          (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1
            ((v ∘ Fin.natAdd p) i)) =
      (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SBundle.Tensor0SSpace.toModel (A p₀))
        (Tensor0SBundle.Tensor0SSpace.toModel (B p₀)))
        (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p₀.1 (v i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem realizedFam_chartDeTurckVFComp_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_chartDeTurckVFComp (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG g_bg k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg α k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem deTurckVFChartLocal_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1) •
            chartBasisVecFiber (I := I) α k p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hcoeff : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α k (extChartAt I α p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun k => realizedFam_chartDeTurckVFComp_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg α k
  set e := trivializationAt E (TangentSpace I) α with he
  have hcoord_eq : ∀ q ∈ (chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      (e ⟨q.1, ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            chartBasisVecFiber (I := I) α k q.1⟩).2 =
        ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            (chartModelBasis E) k := by
    rintro q ⟨hqx, _⟩
    have hqbase : q.1 ∈ e.baseSet := by
      rw [he, trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hqx
    have hclm : ∀ w : TangentSpace I q.1,
        (e ⟨q.1, w⟩).2 = e.continuousLinearMapAt ℝ q.1 w := fun w => by
      rw [Trivialization.continuousLinearMapAt_apply]
      exact (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) w).symm
    rw [hclm, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ← hclm]
    congr 1
    rw [trivializationAt_chartBasisVec_snd (I := I) α k hqbase]
  have hcoordSmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => (e ⟨q.1, ∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg α k (extChartAt I α q.1) •
            chartBasisVecFiber (I := I) α k q.1⟩).2)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.congr ?_ hcoord_eq
    refine contMDiffOn_finset_sum (fun k _ => ?_)
    exact (hcoeff k).smul contMDiffOn_const
  haveI : MemTrivializationAtlas e := by rw [he]; infer_instance
  rw [Bundle.Trivialization.contMDiffOn_iff (e := e) ?_]
  · exact ⟨contMDiffOn_fst, hcoordSmooth⟩
  · rintro q ⟨hqx, _⟩
    rw [Trivialization.mem_source, he, trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hqx

omit [CompactSpace M] in
theorem deTurckVF_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        ((PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg :
          Π b : M, TangentSpace I b) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  intro p hp
  obtain ⟨_, hps⟩ := hp
  have hlocal := deTurckVFChartLocal_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg p.1
  have heqOn : ∀ q ∈ (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          (∑ k : Fin (Module.finrank ℝ E),
            PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 k (extChartAt I p.1 q.1) •
              chartBasisVecFiber (I := I) p.1 k q.1) =
        TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
          ((PDE.DeTurck.deTurckVF (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg :
            Π b : M, TangentSpace I b) q.1) := by
    rintro q ⟨hqx, _⟩
    have hqgood : q.1 ∈ chartLeviCivitaGoodSet (I := I) p.1 := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I), extChartAt_source (I := I)]
      exact hqx
    rw [PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 hqgood]
  have hpmem : p ∈ (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') :=
    ⟨mem_chart_source H p.1, hps⟩
  have hnhd : (chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ') ∈
      nhdsWithin p ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H p.1).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ'),
      (chartAt H p.1).open_source.prod realizedSmallSet_isOpen, hpmem, fun q hq => hq.1⟩
  have hlocalAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (∑ k : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' q.2) g_bg p.1 k (extChartAt I p.1 q.1) •
            chartBasisVecFiber (I := I) p.1 k q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p :=
    (hlocal p hpmem).mono_of_mem_nhdsWithin hnhd
  refine hlocalAt.congr_of_eventuallyEq ?_ (heqOn p hpmem).symm
  filter_upwards [hnhd] with q hq using (heqOn q hq).symm

private def arm1LowerSwapPermA : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def arm1LowerSwapPermC : Equiv.Perm (Fin 3) :=
  ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩

private noncomputable def covGradSymmSValue (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) (x : M) : Tensor0SBundle.Tensor0SSpace 3 I x :=
  (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
    (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ V)).toSection x)
    (unitTensor (I := I) (M := M) x)


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGradSymmSValue_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) x
        (covGradSymmSValue (I := I) g₀ V x)) := by
  have h := ContMDiff.clm_bundle_apply (b := id)
    (covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ V)).toSection.contMDiff
    (unitZeroSec (I := I) (M := M)).contMDiff
  refine h.congr (fun x => ?_)
  rfl


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGradSymmSValue_convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (x : M) :
    covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x =
      (1 - s) • covGradSymmSValue (I := I) g₀ T' x +
        s • covGradSymmSValue (I := I) g₀ T x := by
  have hsplit : covGrad (I := I) (M := M) g₀ 0 2
      (ccTensor02Symm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) =
      (1 - s) • covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T')
        + s • covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T) := by
    rw [convexPerturbation, symmS_add, symmS_smul, symmS_smul, covGrad_add,
      covGrad_smul, covGrad_smul]
  rw [covGradSymmSValue, hsplit, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_smul]
  rfl


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGradSymmSValueFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (_hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hP' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ T' p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (covGradSymmSValue_contMDiff (I := I) g₀ T').comp_contMDiffOn contMDiffOn_fst
  have hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (covGradSymmSValue (I := I) g₀ T p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (covGradSymmSValue_contMDiff (I := I) g₀ T).comp_contMDiffOn contMDiffOn_fst
  have hone : ContDiff ℝ ∞ (fun s : ℝ => 1 - s) := contDiff_const.sub contDiff_id
  have hids : ContDiff ℝ ∞ (fun s : ℝ => s) := contDiff_id
  have h1 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hone
    (fun p : M × ℝ => covGradSymmSValue (I := I) g₀ T' p.1) hP'
  have h2 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hids
    (fun p : M × ℝ => covGradSymmSValue (I := I) g₀ T p.1) hP
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (1 - p.2) • covGradSymmSValue (I := I) g₀ T' p.1)
    (fun p : M × ℝ => p.2 • covGradSymmSValue (I := I) g₀ T p.1) h1 h2
  refine hsum.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  rw [covGradSymmSValue_convexPerturbation]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem connDiff_split_middle (gA gC gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v =
      PDE.DeTurck.connDiff (I := I) gA gC x u v +
        PDE.DeTurck.connDiff (I := I) gC gB x u v := by
  classical
  set σ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x u, smoothExtensionTangent_contMDiff (I := I) x u⟩ with hσdef
  have hσx : σ x = u := smoothExtensionTangent_eq (I := I) x u
  have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (σ y)) x :=
    (σ.contMDiff x).mdifferentiableAt (by simp)
  have h1 := PDE.DeTurck.connDiff_apply (I := I) gA gB (σ := fun y => σ y) hmd v
  have h2 := PDE.DeTurck.connDiff_apply (I := I) gA gC (σ := fun y => σ y) hmd v
  have h3 := PDE.DeTurck.connDiff_apply (I := I) gC gB (σ := fun y => σ y) hmd v
  rw [hσx] at h1 h2 h3
  rw [h1, h2, h3]
  exact (sub_add_sub_cancel _ _ _).symm


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private theorem metricConnDiffLoweredFib_split (gm gA gC gB : SmoothRiemannianMetric I M)
    (x : M) :
    metricConnDiffLoweredFib (I := I) gm gA gB x =
      metricConnDiffLoweredFib (I := I) gm gA gC x +
        metricConnDiffLoweredFib (I := I) gm gC gB x := by
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, metricConnDiffLoweredFib_toModel,
    metricConnDiffLoweredFib_toModel, metricConnDiffLoweredFib_toModel,
    connDiff_split_middle (I := I) gA gC gB, map_add, ContinuousLinearMap.add_apply]


omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem metricConnDiffLowered_fixedPair_affine (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gB : SmoothRiemannianMetric I M) {s : ℝ}
    (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) (x : M) :
    metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ gB x =
      metricConnDiffLoweredFib (I := I) g₀ g₀ gB x
        + (1 - s) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ gB x
        + s • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ gB x := by
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  rw [Tensor0SBundle.Tensor0SSpace.toModel_add, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
    metricConnDiffLoweredFib_toModel, metricConnDiffLoweredFib_toModel,
    ccBilinConnDiffLoweredFib_toModel, ccBilinConnDiffLoweredFib_toModel]
  rw [realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    ccTensorBilinSymm_convexPerturbation]
  simp only [smul_eq_mul]
  ring

theorem metricConnDiffLowered_selfFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set Vfam : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 3 I p.1 :=
    fun p => covGradSymmSValue (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) p.1
    with hVfamdef
  have hV : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 (Vfam p))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    covGradSymmSValueFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hU1 := domDomCongrField_jointContMDiffOn (I := I) arm1LowerSwapPermA
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Vfam hV
  have hU3 := domDomCongrField_jointContMDiffOn (I := I) arm1LowerSwapPermC
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Vfam hV
  have hsum := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
        (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    Vfam hU1 hV
  have hsub := jointTotalSpace0S_sub_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
        (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
          (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))) + Vfam p)
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermC
        (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    hsum hU3
  have hhalf := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (f := fun _ : ℝ => (1 / 2 : ℝ)) contDiff_const
    (fun p : M × ℝ =>
      (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermA
            (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))) + Vfam p) -
        Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
          (ContinuousMultilinearMap.domDomCongr arm1LowerSwapPermC
            (Tensor0SBundle.Tensor0SSpace.toModel (Vfam p))))
    hsub
  refine hhalf.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  beta_reduce
  apply ContinuousMultilinearMap.ext
  intro v
  rw [metricConnDiffLoweredFib_toModel, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    Tensor0SBundle.Tensor0SSpace.toModel_sub, Tensor0SBundle.Tensor0SSpace.toModel_add,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner b u w =
        g₀.inner b u w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2) b u w :=
    fun b u w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hp.2 b u w
  have hid := connDiffInner_g1_eq_half_covGradSymmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
    (convexPerturbation (I := I) g₀ T T' p.2) hg₁ p.1 (v 0) (v 1) (v 2)
  rw [hid]
  have h1 : (fun j => v (arm1LowerSwapPermA j)) = ![v 1, v 0, v 2] := by
    funext j; fin_cases j <;> rfl
  have h3 : (fun j => v (arm1LowerSwapPermC j)) = ![v 2, v 1, v 0] := by
    funext j; fin_cases j <;> rfl
  rw [h1, h3]
  have huM : ∀ vv : Fin 3 → TangentSpace I p.1,
      unitModel (I := I) (M := M) g₀ 3
        (covGrad (I := I) (M := M) g₀ 0 2
          (ccTensor02Symm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' p.2))) p.1 vv =
      Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) vv := fun vv => rfl
  rw [huM ![v 1, v 0, v 2], huM ![v 0, v 1, v 2], huM ![v 2, v 1, v 0]]
  have hv012 : Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) v =
      Tensor0SBundle.Tensor0SSpace.toModel (Vfam p) ![v 0, v 1, v 2] := by
    congr 1
    funext j; fin_cases j <;> rfl
  rw [hv012]
  simp only [smul_eq_mul]

theorem metricConnDiffLowered_bgFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hself := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hfix0 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hfixT' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ T' g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hfixT : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 3 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1
        (ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ T g₀ g_bg).comp_contMDiffOn contMDiffOn_fst
  have hone : ContDiff ℝ ∞ (fun s : ℝ => 1 - s) := contDiff_const.sub contDiff_id
  have hids : ContDiff ℝ ∞ (fun s : ℝ => s) := contDiff_id
  have h1 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hone
    (fun p : M × ℝ => ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1) hfixT'
  have h2 := jointTotalSpace0S_smulFun_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) hids
    (fun p : M × ℝ => ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1) hfixT
  have hsum1 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1)
    (fun p : M × ℝ => (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1)
    hfix0 h1
  have hsum2 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1 +
      (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1)
    (fun p : M × ℝ => p.2 • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1)
    hsum1 h2
  have hsum3 := jointTotalSpace0S_add_local (I := I) (d := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
    (fun p : M × ℝ => metricConnDiffLoweredFib (I := I) g₀ g₀ g_bg p.1 +
        (1 - p.2) • ccBilinConnDiffLoweredFib (I := I) g₀ T' g₀ g_bg p.1 +
      p.2 • ccBilinConnDiffLoweredFib (I := I) g₀ T g₀ g_bg p.1)
    hself hsum2
  refine hsum3.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z) p.1 t) ?_
  rw [metricConnDiffLoweredFib_split (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
    (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ g_bg p.1]
  congr 1
  exact metricConnDiffLowered_fixedPair_affine (I := I) g₀ T T' hδ hδ' g_bg hp.2 p.1

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
