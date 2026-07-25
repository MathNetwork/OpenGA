import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Calculus.ContDiffExtendInterval
import DifferentialGeometry.Analysis.Integration.L2.ForcingFiniteOrderTimeRegularityParametricIntegral


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance tensorRSModelNormedAddCommGroup_local :
    NormedAddCommGroup (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2

private local instance tensorRSModelNormedSpace_local :
    NormedSpace ℝ (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace 0 2


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem smoothCcTensor_path_toFun_contDiffWithinAt
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} {N : WithTop ℕ∞}
    (Sfam : ℝ → SmoothCcTensor g₀ 0 2)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    (x : M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContDiffWithinAt ℝ N (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 2
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) N (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun s : ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) x ((Sfam s).toSection x))
      (Set.Icc (0 : ℝ) T) :=
    hSfam.comp harg hmaps
  have h2 := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.TensorRSModel 0 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)
    (IB := I) (IM := 𝓘(ℝ, ℝ))).mp (h1 t ht) |>.2
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at h2
  set e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) x with he
  have hxbase : x ∈ e.baseSet := by
    rw [he]
    change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) x).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) x).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change x ∈ (trivializationAt E (TangentSpace I) x).baseSet
        rw [show (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source from
          TangentBundle.trivializationAt_baseSet (I := I) x]
        exact mem_chart_source H x
  set L : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    (Tensor0SBundle.TensorRSSpace.toModelL (𝕜 := ℝ) 0 2 x).comp (e.symmL ℝ x) with hL
  have hLeq : ∀ s : ℝ, L ((e ⟨x, (Sfam s).toSection x⟩).2) = (Sfam s).toFun x := by
    intro s
    have h3 : e.continuousLinearMapAt ℝ x ((Sfam s).toSection x)
        = (e ⟨x, (Sfam s).toSection x⟩).2 := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Trivialization.coe_linearMapAt_of_mem _ hxbase]
    rw [hL, ContinuousLinearMap.comp_apply, ← h3,
      Bundle.Trivialization.symmL_continuousLinearMapAt _ hxbase]
    rfl
  have h4 : ContDiffWithinAt ℝ N (fun s : ℝ => L ((e ⟨x, (Sfam s).toSection x⟩).2))
      (Set.Icc (0 : ℝ) T) t :=
    L.contDiff.comp_contDiffWithinAt h2
  exact h4.congr (fun s _ => (hLeq s).symm) (hLeq t).symm


section FiniteOrderReconJetEnergy

open Tensor0SBundle TensorMultilinear
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Integral.Connection

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem partialSnd_set_contMDiffOn_Icc_finiteOrder
    (f : M → ℝ → ℝ) {T : ℝ} (U : Set M) (N : ℕ)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((N : WithTop ℕ∞) + 1)
      (fun p : M × ℝ => f p.1 p.2) (U ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (N : WithTop ℕ∞)
      (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  rcases le_or_gt T 0 with hT0 | hT0
  · have hzero : Set.EqOn
        (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
        (fun _ : M × ℝ => (0 : ℝ)) (U ×ˢ Set.Icc (0 : ℝ) T) := by
      intro p hp
      have hnacc : ¬ AccPt p.2 (Filter.principal (Set.Icc (0 : ℝ) T)) := by
        rw [accPt_principal_iff_nhdsWithin]
        have hempty : Set.Icc (0 : ℝ) T \ {p.2} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro y hy
          exact hy.2 (Set.mem_singleton_iff.mpr
            ((Set.subsingleton_Icc_of_ge hT0) hy.1 hp.2))
        rw [hempty, nhdsWithin_empty]
        exact not_neBot.mpr rfl
      exact derivWithin_zero_of_not_accPt hnacc
    exact (contMDiffOn_const (c := (0 : ℝ))).congr hzero
  have hUM : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) T) :=
    (uniqueDiffOn_Icc hT0).uniqueMDiffOn
  have hrw : (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) =
      fun p : M × ℝ =>
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) (1 : ℝ) := by
    funext p
    rw [mfderivWithin_eq_fderivWithin]
    exact (fderivWithin_derivWithin (𝕜 := ℝ) (f := fun s => f p.1 s)
      (s := Set.Icc (0 : ℝ) T) (x := p.2)).symm
  rw [hrw]
  intro p₀ hp₀
  have hf' : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      ((N : WithTop ℕ∞) + 1)
      (Function.uncurry (fun (p : M × ℝ) (s : ℝ) => f p.1 s))
      ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) := by
    have harg : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        ((N : WithTop ℕ∞) + 1)
        (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        ((U ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T)
        (U ×ˢ Set.Icc (0 : ℝ) T) :=
      fun q hq => ⟨hq.1.1, hq.2⟩
    exact (hf (p₀.1, p₀.2) ⟨hp₀.1, hp₀.2⟩).comp (p₀, p₀.2) harg hmaps
  have h_apply :=
    ContMDiffWithinAt.mfderivWithin_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : M × ℝ) (s : ℝ) => f p.1 s)
      (g := fun p : M × ℝ => p.2) (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ))
      (t := U ×ˢ Set.Icc (0 : ℝ) T)
      (u := Set.Icc (0 : ℝ) T)
      (v := U ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p₀) (n := (N : WithTop ℕ∞) + 1) (m := (N : WithTop ℕ∞))
      hf'
      contMDiffWithinAt_snd contMDiffWithinAt_id contMDiffWithinAt_const le_rfl
      (Set.mapsTo_id _) hp₀
      (fun q hq => hq.2) hUM
  simpa [inTangentCoordinates_model_space] using h_apply

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem iteratedPartialSnd_set_contMDiffOn_Icc_finiteOrder
    {T : ℝ} (U : Set M) :
    ∀ (j : ℕ) (f : M → ℝ → ℝ) (N : ℕ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((N + j : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ => f p.1 p.2) (U ×ˢ Set.Icc (0 : ℝ) T) →
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (N : WithTop ℕ∞)
        (fun p : M × ℝ => iteratedDerivWithin j (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
        (U ×ˢ Set.Icc (0 : ℝ) T) := by
  intro j
  induction j with
  | zero =>
      intro f N hf
      rw [Nat.add_zero] at hf
      refine hf.congr ?_
      intro p _
      rw [iteratedDerivWithin_zero]
  | succ n ih =>
      intro f N hf
      have hf1 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (((N + n : ℕ) : WithTop ℕ∞) + 1)
          (fun p : M × ℝ => f p.1 p.2) (U ×ˢ Set.Icc (0 : ℝ) T) := by
        rw [show N + (n + 1) = (N + n) + 1 from rfl, Nat.cast_succ] at hf
        exact hf
      have hderiv : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((N + n : ℕ) : WithTop ℕ∞)
          (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
          (U ×ˢ Set.Icc (0 : ℝ) T) :=
        partialSnd_set_contMDiffOn_Icc_finiteOrder f U (N + n) hf1
      have hih := ih (fun x s => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) s) N hderiv
      refine hih.congr ?_
      intro p _
      rw [iteratedDerivWithin_succ']

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem vec_iteratedPartialSnd_set_contMDiffOn_Icc_finiteOrder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {T : ℝ} (U : Set M) (hT : 0 < T) (Vf : M → ℝ → V) (j N : ℕ)
    (hVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) ((N + j : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => Vf p.1 p.2) (U ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) (N : WithTop ℕ∞)
      (fun p : M × ℝ => iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  set A : V ≃L[ℝ] (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) :=
    (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv with hA
  have hAVf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ))
      ((N + j : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => A (Vf p.1 p.2)) (U ×ˢ Set.Icc (0 : ℝ) T) :=
    (A.toContinuousLinearMap.contMDiff.comp_contMDiffOn hVf)
  have hcoord : ∀ i : Module.Basis.ofVectorSpaceIndex ℝ V,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (N : WithTop ℕ∞)
        (fun p : M × ℝ => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)
        (U ×ˢ Set.Icc (0 : ℝ) T) := by
    intro i
    have hfi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((N + j : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ => A (Vf p.1 p.2) i) (U ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.1 hAVf i
    exact iteratedPartialSnd_set_contMDiffOn_Icc_finiteOrder U j
      (fun x s => A (Vf x s) i) N hfi
  have hkey : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) (N : WithTop ℕ∞)
      (fun p : M × ℝ => A.symm
        (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2))
      (U ×ˢ Set.Icc (0 : ℝ) T) := by
    have hpi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ))
        (N : WithTop ℕ∞)
        (fun p : M × ℝ => (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i)
          (Set.Icc (0 : ℝ) T) p.2)) (U ×ˢ Set.Icc (0 : ℝ) T) :=
      contMDiffOn_pi_space.2 hcoord
    exact A.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hpi
  refine hkey.congr ?_
  intro p hp
  obtain ⟨hpU, hs⟩ := hp
  have hfiber0 : ContDiffWithinAt ℝ ((N + j : ℕ) : WithTop ℕ∞) (fun s => Vf p.1 s)
      (Set.Icc (0 : ℝ) T) p.2 := by
    have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ((N + j : ℕ) : WithTop ℕ∞)
        (fun u : ℝ => (p.1, u)) (Set.Icc (0 : ℝ) T) :=
      (contMDiffOn_const (c := p.1)).prodMk contMDiffOn_id
    have hmaps : Set.MapsTo (fun u : ℝ => (p.1, u)) (Set.Icc (0 : ℝ) T)
        (U ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨hpU, hu⟩
    have hcomp := hVf.comp harg hmaps
    rw [contMDiffOn_iff_contDiffOn] at hcomp
    exact hcomp p.2 hs
  have hfiber : ContDiffWithinAt ℝ ((j : ℕ) : WithTop ℕ∞) (fun s => Vf p.1 s)
      (Set.Icc (0 : ℝ) T) p.2 :=
    hfiber0.of_le (by exact_mod_cast Nat.le_add_left j N)
  have hcomm : (fun i => iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2)
      = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) := by
    have hAcomm : iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2
        = A (iteratedDerivWithin j (fun s => Vf p.1 s) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin_finiteOrder A.toContinuousLinearMap
        (fun s => Vf p.1 s) hT hs j hfiber
    funext i
    have hfiberA : ContDiffWithinAt ℝ ((j : ℕ) : WithTop ℕ∞) (fun s => A (Vf p.1 s))
        (Set.Icc (0 : ℝ) T) p.2 :=
      A.toContinuousLinearMap.contDiff.comp_contDiffWithinAt hfiber
    have hproj : iteratedDerivWithin j (fun s => A (Vf p.1 s) i) (Set.Icc (0 : ℝ) T) p.2
        = (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
            (iteratedDerivWithin j (fun s => A (Vf p.1 s)) (Set.Icc (0 : ℝ) T) p.2) :=
      clm_comm_iteratedDerivWithin_finiteOrder (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Module.Basis.ofVectorSpaceIndex ℝ V => ℝ) i)
        (fun s => A (Vf p.1 s)) hT hs j hfiberA
    rw [hproj, hAcomm]
    rfl
  rw [hcomm]
  exact (A.symm_apply_apply _).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem contMDiff_constOfIsEmpty_tensor0S_section_local :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffAt_fst, ?_⟩
  have hconst : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) ∞
      (fun _ : M × ℝ =>
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) :
          Tensor0SBundle.Tensor0SModel 0 ℝ E)) p₀ :=
    contMDiffAt_const
  refine hconst.congr_of_eventuallyEq ?_
  filter_upwards with p
  rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M)
    (fun _ : M => Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) p₀.1 p.1]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.constOfIsEmpty_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [show ((Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) :
        Tensor0SBundle.Tensor0SSpace 0 I p.1) 0) =
        Tensor0SBundle.Tensor0SSpace.toModel
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) :
              Tensor0SBundle.Tensor0SSpace 0 I p.1) 0 from rfl,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem contMDiffWithinAt_curriedSection_prod_ofOrder_local {N : WithTop ℕ∞} {n : ℕ}
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (n + 1) I p.1)
    (hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace (n + 1) I x) p.1 (T p)) s p₀) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p.1
        (tensor0S_curry (I := I) (M := M) n p.1 (T p))) s p₀ := by
  letI : TopologicalSpace (TotalSpace (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundle_topology (n + 1)
  rw [Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hT_at := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E) N
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbase : {p : M × ℝ | p.1 ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).baseSet} ∈ nhdsWithin p₀ s := by
      apply nhdsWithin_le_nhds
      apply (continuous_fst.continuousAt).preimage_mem_nhds
      exact (trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt _ _ _)
    filter_upwards [hbase] with p hb
    have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p) p₀.1 p.1 hb
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p.1, tensor0S_curry (I := I) (M := M) n p.1 (T p)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p.1, T p⟩).2)
    exact hpt
  · have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p₀) p₀.1 p₀.1 (mem_baseSet_trivializationAt _ _ _)
    change (trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p₀.1, tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p₀.1, T p₀⟩).2)
    exact hpt

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem contMDiffWithinAt_section_apply_prod_ofOrder_local {N : WithTop ℕ∞} : ∀ (n : ℕ)
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace n I p.1)
    (_hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1 (T p)) s p₀)
    (v : Fin n → ∀ p : M × ℝ, TangentSpace I p.1)
    (_hv : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) N
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p)) s p₀),
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (T p) (fun i => v i p)) s p₀
  | 0, s, p₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffWithinAt_totalSpace
      (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y)
      (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) N
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
          (fun p : M × ℝ =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) p₀.1 ⟨p.1, T p⟩).2)) s p₀ :=
      hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p) p₀.1 p.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p) 0)) = (T p) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p) 0)) 0 = (T p) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
    · rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p₀) p₀.1 p₀.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p₀) 0)) = (T p₀) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p₀) 0)) 0 = (T p₀) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq : (fun i : Fin 0 => v i p₀) = (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
  | n + 1, s, p₀, T, hT, v, hv => by
    have hCurry := contMDiffWithinAt_curriedSection_prod_ofOrder_local (I := I) (M := M) T hT
    have hApplied : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) N
        (fun p : M × ℝ =>
          TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1
            ((tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))) s p₀ :=
      ContMDiffWithinAt.clm_bundle_apply (𝕜 := ℝ) (n := N)
        (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace n I x)
        (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
        (b := Prod.fst) (ϕ := fun p : M × ℝ => tensor0S_curry (I := I) (M := M) n p.1 (T p))
        (v := fun p : M × ℝ => v 0 p)
        hCurry (hv 0)
    have hRec := contMDiffWithinAt_section_apply_prod_ofOrder_local n
      (s := s) (p₀ := p₀)
      (fun p : M × ℝ => (tensor0S_curry (I := I) (M := M) n p.1 (T p)) (v 0 p))
      hApplied
      (fun (i : Fin n) (p : M × ℝ) => v i.succ p)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]
    · change Tensor0SBundle.Tensor0SSpace.toModel (T p₀) (fun i : Fin (n + 1) => v i p₀) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((tensor0S_curry (I := I) (M := M) n p₀.1 (T p₀)) (v 0 p₀))
          (fun i : Fin n => v i.succ p₀)
      rw [tensor0S_curry_apply_eval]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder_local
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ} :
    ∀ (n : ℕ)
    (TT SS : M × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (_hT : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ => (TT p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (_hS : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ => (SS p) (fun k : Fin n => (chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1 (TT p) (SS p))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  intro n
  induction n with
  | zero =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ((TT p) (fun i => Fin.elim0 i)) * ((SS p) (fun i => Fin.elim0 i)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      have hempty :
          (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i; exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
            (fun p : M × ℝ => (TT p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (TT p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (TT p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hT0
      have hS_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
            (fun p : M × ℝ => (SS p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (SS p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (SS p)
              (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hS0
      exact hT_smooth.mul hS_smooth
  | succ n ih =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (n + 1) g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix (I := I) g α p.1)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) n g α p.1
                    ((TT p).curryLeft ((chartModelBasis E) i))
                    ((SS p).curryLeft ((chartModelBasis E) j)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · have hinv := chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
        have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
          trivializationAt_baseSet_eq_chartAt_source (I := I) α
        rw [hbase_eq] at hinv
        exact (hinv.of_le hN).comp contMDiffOn_fst (fun p hp => hp.1)
      · refine ih
            (fun p : M × ℝ => (TT p).curryLeft ((chartModelBasis E) i))
            (fun p : M × ℝ => (SS p).curryLeft ((chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((TT p).curryLeft ((chartModelBasis E) i))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (TT p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((SS p).curryLeft ((chartModelBasis E) j))
                  (fun k : Fin n => (chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (SS p) (fun k : Fin (n + 1) => (chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hS ψ'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder_local
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (Tval : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 2 I p.1)
    (arm : M × ℝ → Tensor0SBundle.TensorRSModel 0 2 ℝ E)
    (harm : ∀ p : M × ℝ,
      arm p (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p))
    (hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Tval p))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (φ : Fin (0 + 2) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ =>
        (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  have heval : ∀ p : M × ℝ,
      (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (chartModelBasis E) (φ k)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p)
          (fun j : Fin 2 => chartBasisVecFiber (I := I) α
            (φ (Fin.natAdd 0 j)) p.1) := by
    intro p
    rw [loweredCompose_apply, lowerAllUpperIndices_apply, separableFormAt_zero, harm p]
    congr 1
  refine ContMDiffOn.congr ?_ (fun p _ => heval p)
  have hv : ∀ j : Fin 2, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro j
    have h := DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartBasisVec_jointContMDiffOn
      (I := I) α (φ (Fin.natAdd 0 j))
    exact h.mono (Set.prod_mono (subset_refl _) (Set.subset_univ _))
  intro p hp
  exact contMDiffWithinAt_section_apply_prod_ofOrder_local 2
    (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
    (p₀ := p) Tval (hTval p hp)
    (fun j p => chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1)
    (fun j => (hv j p hp).of_le hN)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma tensorInnerPointwise_abs_le_half_selfInner_add
    (g : SmoothRiemannianMetric I M) (x : M)
    (V W : Tensor0SBundle.TensorRSModel 0 2 ℝ E) :
    |DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 2 x V W| ≤
      (DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 2 x V V +
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 2 x W W)
        / 2 := by
  have hexp : ∀ c : ℝ,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 2 x
          (V + c • W) (V + c • W) =
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 2 x V V +
          c * DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 2 x V W +
          (c * DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g 0 2 x W V +
            c * (c * DifferentialGeometry.Integral.L2.tensorInnerPointwise
              (I := I) (M := M) g 0 2 x W W)) := by
    intro c
    rw [DifferentialGeometry.Integral.L2.tensorInnerPointwise_add_left,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise_add_right,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise_add_right,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise_smul_right,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise_smul_left,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise_smul_left,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise_smul_right]
  have hsymm := DifferentialGeometry.Integral.L2.tensorInnerPointwise_symm
    (I := I) (M := M) g 0 2 x V W
  have hplus := DifferentialGeometry.Integral.L2.tensorInnerPointwise_nonneg
    (I := I) (M := M) g 0 2 x (V + (1 : ℝ) • W)
  have hminus := DifferentialGeometry.Integral.L2.tensorInnerPointwise_nonneg
    (I := I) (M := M) g 0 2 x (V + (-1 : ℝ) • W)
  rw [hexp 1] at hplus
  rw [hexp (-1)] at hminus
  rw [← hsymm] at hplus hminus
  refine abs_le.mpr ⟨by linarith, by linarith⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma eigenvectorSmooth_selfInner_integral_eq_one
    (g₀ : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    (∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
          (I := I) (M := M) g₀ 0 2 i).toFun x)
        ((Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
          (I := I) (M := M) g₀ 0 2 i).toFun x)
      ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀))
      = 1 := by
  classical
  set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
    with heig
  have h1 : (∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x (eig.toFun x) (eig.toFun x)
      ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀))
      = ⟪eig, eig⟫_ℝ := by
    rw [SmoothCcTensor.inner_def]
    rfl
  rw [h1, ← SmoothCcTensor.inner_toL2 (g := g₀) (r := 0) (s := 2) eig eig,
    real_inner_self_eq_norm_sq]
  have h4 : SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) eig =
      Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2) i := by
    rw [SmoothCcTensor.toL2_apply (g := g₀) (r := 0) (s := 2) eig]
    exact Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i
  rw [h4,
    (Analysis.Parabolic.TensorSpectral.tensorResolventEigenbasisVec_orthonormal
      (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)).1 i]
  norm_num

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem smoothCcTensorPath_timeJet_selfPairing_continuousOn
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk j : ℕ) (hj : j ≤ kk)
    (Sfam : ℝ → SmoothCcTensor g₀ 0 2)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContinuousOn
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          (iteratedDerivWithin j (fun s => (Sfam s).toFun p.1) (Set.Icc (0 : ℝ) T) p.2)
          (iteratedDerivWithin j (fun s => (Sfam s).toFun p.1) (Set.Icc (0 : ℝ) T) p.2))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) 0 2
  set jetD : M → ℝ → Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    fun x t => iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t
    with hjetD
  have hbaseRS : ∀ (α : M) (x : M), x ∈ (chartAt H α).source →
      x ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
    intro α x hx
    change x ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        exact hx
  have hfiberSec : ∀ x : M, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ContDiffWithinAt ℝ ((kk : ℕ) : WithTop ℕ∞) (fun s => (Sfam s).toFun x)
        (Set.Icc (0 : ℝ) T) t :=
    fun x t ht => smoothCcTensor_path_toFun_contDiffWithinAt (I := I) (M := M) g₀ Sfam hSfam x ht
  have hCR : ∀ α : M, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M => (Sfam p.2).toSection z) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro α p hp
    have hpbase := hbaseRS α p.1 hp.1
    have hsub : ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) ⊆
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun q hq => ⟨Set.mem_univ _, hq.2⟩
    have hFwithin : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ((kk : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ => (⟨p.1, (Sfam p.2).toSection p.1⟩ :
          TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p :=
      (hSfam p (hsub hp)).mono hsub
    have hsource : (⟨p.1, (Sfam p.2).toSection p.1⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
      rw [Bundle.Trivialization.mem_source]; exact hpbase
    have hrepr := ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ((kk : ℕ) : WithTop ℕ∞))
      (f := fun p : M × ℝ => (⟨p.1, (Sfam p.2).toSection p.1⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p)
      (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mp hFwithin).2
    refine hrepr.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ (hbaseRS α q.1 hq.1)]
    · rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
  have hChartCommute : ∀ (α : M) (x : M), x ∈ (chartAt H α).source → ∀ t ∈ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z t)) x =
        iteratedDerivWithin j
          (fun s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
            (I := I) 0 2 α (fun z : M => (Sfam s).toSection z) x)
          (Set.Icc (0 : ℝ) T) t := by
    intro α x hx t ht
    have hxRSbase := hbaseRS α x hx
    set Φ : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt ℝ x).comp
        ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
          : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSSpace 0 2 I x)
      with hΦ
    have hΦeq : ∀ s : ℝ, Φ ((Sfam s).toFun x) =
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => (Sfam s).toSection z) x := by
      intro s
      rw [hΦ, ContinuousLinearMap.comp_apply,
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply]
      have hsymm : ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
          : Tensor0SBundle.TensorRSModel 0 2 ℝ E →L[ℝ] Tensor0SBundle.TensorRSSpace 0 2 I x)
          ((Sfam s).toFun x) = (Sfam s).toSection x := by
        change (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x).symm
            ((Tensor0SBundle.tensorRSSpace_continuousLinearEquiv (I := I) 0 2 x)
              ((Sfam s).toSection x)) = (Sfam s).toSection x
        exact (Tensor0SBundle.tensorRSSpace_continuousLinearEquiv
          (I := I) 0 2 x).symm_apply_apply _
      rw [hsymm]
    have hΦLHS : DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
          (I := I) 0 2 α (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z t)) x =
        Φ (jetD x t) := by
      rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply, hΦ,
        ContinuousLinearMap.comp_apply]
      rfl
    have hcomm := clm_comm_iteratedDerivWithin_finiteOrder Φ
      (fun s => (Sfam s).toFun x) hT ht j
      ((hfiberSec x t ht).of_le (by exact_mod_cast hj))
    rw [hΦLHS, show jetD x t =
        iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t from rfl,
      ← hcomm]
    exact iteratedDerivWithin_congr (fun s _ => hΦeq s) ht
  have hChartJet : ∀ α : M, ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ((0 : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
          (fun z : M => Tensor0SBundle.TensorRSSpace.ofModel (jetD z p.2)) p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro α
    have hCRj : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        ((0 + j : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ =>
          DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr (I := I) 0 2 α
            (fun z : M => (Sfam p.2).toSection z) p.1)
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
      (hCR α).of_le (by exact_mod_cast (by omega : 0 + j ≤ kk))
    have hvecjet := vec_iteratedPartialSnd_set_contMDiffOn_Icc_finiteOrder
      (V := Tensor0SBundle.TensorRSModel 0 2 ℝ E) (U := (chartAt H α).source) hT
      (fun x s => DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr
        (I := I) 0 2 α (fun z : M => (Sfam s).toSection z) x) j 0 hCRj
    refine hvecjet.congr ?_
    intro p hp
    exact hChartCommute α p.1 hp.1 p.2 hp.2
  have hJet : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((0 : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    refine contMDiffOn_of_locally_contMDiffOn ?_
    rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
    refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
      (chartAt H x₀).open_source.prod isOpen_univ,
      ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
    set α : M := x₀ with hα
    have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
        ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
        (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
      ext ⟨y, u⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
      tauto
    rw [hsub_eq]
    intro p₀ hp₀
    obtain ⟨hx₀src, hs₀'⟩ := hp₀
    have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := hbaseRS α p₀.1 hx₀src
    have hsource : (⟨p₀.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p₀.1 p₀.2)⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
      rw [Bundle.Trivialization.mem_source]; exact hbaseSet
    have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ((0 : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ =>
          ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
            ⟨p.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)⟩).2)
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p₀ := by
      refine ((hChartJet α) p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with p hp
        rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
          Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.coe_linearMapAt_of_mem _ (hbaseRS α p.1 hp.1)]
      · rw [DifferentialGeometry.Integral.Connection.tensorRSChartE_section_repr_apply,
          Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.coe_linearMapAt_of_mem _ hbaseSet]
    exact ((Bundle.Trivialization.contMDiffWithinAt_iff
      (IM := I.prod 𝓘(ℝ, ℝ)) (n := ((0 : ℕ) : WithTop ℕ∞))
      (f := fun p : M × ℝ => (⟨p.1, Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)⟩ :
        TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p₀)
      (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
      ⟨contMDiffWithinAt_fst, hfib⟩)
  have h0inf : (((0 : ℕ) : WithTop ℕ∞)) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hpair : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((0 : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          (jetD p.1 p.2) (jetD p.1 p.2))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
    refine contMDiffOn_of_locally_contMDiffOn ?_
    rintro ⟨x₀, t₀⟩ ⟨_, ht₀⟩
    refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
      (chartAt H x₀).open_source.prod isOpen_univ,
      ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
    have hinter : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
        ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
        (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
      rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
    rw [hinter]
    set α : M := x₀ with hα
    have hbridge : ∀ p ∈ (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T,
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            (jetD p.1 p.2) (jetD p.1 p.2) =
          chartTensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g₀ α p.1
            (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (jetD p.1 p.2))
            (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (jetD p.1 p.2)) := by
      rintro ⟨y, u⟩ ⟨hy, _⟩
      have hb : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hy
      rw [tensorInnerPointwise_bridge_identity (I := I) (M := M) g₀ α 0 2 hb,
        chartTensorInnerPointwise_apply]
    refine ContMDiffOn.congr ?_ hbridge
    have hWjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
          Tensor0SBundle.Tensor0SModel 2 ℝ E)) ((0 : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
            Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
          (Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
      hJet.mono (Set.prod_mono (fun y _ => Set.mem_univ y) (subset_refl _))
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) :=
      contMDiff_constOfIsEmpty_tensor0S_section_local
    have hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ((0 : ℕ) : WithTop ℕ∞)
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
          ((Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2) :
              Tensor0SBundle.TensorRSSpace 0 2 I p.1)
            (Tensor0SBundle.Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
      have happ := ContMDiffOn.clm_bundle_apply (𝕜 := ℝ) (n := ((0 : ℕ) : WithTop ℕ∞))
        (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
        (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
        (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
        (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
        (b := Prod.fst)
        (ϕ := fun p : M × ℝ => (Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2) :
          Tensor0SBundle.TensorRSSpace 0 2 I p.1))
        (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
        hWjoint ((hconst.contMDiffOn).of_le h0inf)
      exact happ
    have harm : ∀ p : M × ℝ,
        (jetD p.1 p.2) (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
          Tensor0SBundle.Tensor0SSpace.toModel
            ((Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2) :
                Tensor0SBundle.TensorRSSpace 0 2 I p.1)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) := by
      intro p
      conv_lhs => rw [← Tensor0SBundle.TensorRSSpace.toModel_ofModel (I := I)
        (r := 0) (s := 2) (x := p.1) (jetD p.1 p.2)]
      rfl
    have hcoeff_W : ∀ ψ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((0 : ℕ) : WithTop ℕ∞)
          (fun p : M × ℝ =>
            (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (jetD p.1 p.2))
              (fun k : Fin (0 + 2) => (chartModelBasis E) (ψ k)))
          ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
      fun ψ => loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder_local
        (I := I) (M := M) h0inf g₀ α
        (fun p => (Tensor0SBundle.TensorRSSpace.ofModel (jetD p.1 p.2) :
            Tensor0SBundle.TensorRSSpace 0 2 I p.1)
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))))
        (fun p => jetD p.1 p.2) harm hTval ψ
    exact chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder_local
      (I := I) (M := M) h0inf g₀ α (0 + 2)
      (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (jetD p.1 p.2))
      (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 (jetD p.1 p.2))
      hcoeff_W hcoeff_W
  exact hpair.continuousOn

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem smoothCcTensorPath_eigenPairing_timeJet_uniform_bound
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk j : ℕ) (hj : j ≤ kk)
    (Sfam : ℝ → SmoothCcTensor g₀ 0 2)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ∃ C : ℝ, ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
      |iteratedDerivWithin j
          (fun s => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam s)) i)
          (Set.Icc (0 : ℝ) T) t| ≤ C := by
  classical
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2 with hhc
  have hdiag := smoothCcTensorPath_timeJet_selfPairing_continuousOn (I := I) (M := M)
    g₀ hT kk j hj Sfam hSfam
  obtain ⟨K, hK⟩ := (isCompact_univ.prod isCompact_Icc).exists_bound_of_continuousOn hdiag
  refine ⟨(1 + (K * μ.real Set.univ)) / 2, ?_⟩
  intro i t ht
  have hkinf : ((kk : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hjW : ((j : ℕ) : WithTop ℕ∞) ≤ ((kk : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
  set eig := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i
    with heig
  have heigM := Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_contMDiff
    (I := I) (M := M) g₀ 0 2 i
  have heigP : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        (eig.toSection p.1)) :=
    heigM.comp contMDiff_fst
  have hpairing : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          (eig.toFun p.1) ((Sfam p.2).toFun p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
    tensorInnerPointwise_pair_section_jointContMDiffOn (I := I) (M := M) hkinf g₀
      (fun _ : ℝ => eig) Sfam ((heigP.contMDiffOn).of_le hkinf) hSfam
  have hcoeffInt : ∀ S : SmoothCcTensor g₀ 0 2,
      tensorL2Coeff (I := I) (M := M) hc
          (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) S) i =
        ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (eig.toFun x) (S.toFun x) ∂μ := by
    intro S
    rw [tensorL2Coeff_eq_inner,
      Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma_apply,
      ← Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2 (I := I) (M := M) g₀ 0 2 i,
      ← SmoothCcTensor.toL2_apply
        (Analysis.Parabolic.TensorSpectral.eigenvectorSmooth (I := I) (M := M) g₀ 0 2 i),
      SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_def]
    rfl
  have hLHSfun : (fun s : ℝ => tensorL2Coeff (I := I) (M := M) hc
        (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam s)) i)
      = (fun s : ℝ => ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
          (I := I) (M := M) g₀ 0 2 x (eig.toFun x) ((Sfam s).toFun x) ∂μ) :=
    funext fun s => hcoeffInt (Sfam s)
  have hinter := iteratedDerivWithin_integral_param_Icc_finiteOrder μ hT j
    (fun x s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
      (I := I) (M := M) g₀ 0 2 x (eig.toFun x) ((Sfam s).toFun x))
    (hpairing.of_le hjW) t ht
  have hγfam : ∀ x : M, ContDiffWithinAt ℝ ((j : ℕ) : WithTop ℕ∞)
      (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t := fun x =>
    (smoothCcTensor_path_toFun_contDiffWithinAt (I := I) (M := M) g₀ Sfam hSfam x ht).of_le hjW
  have hfib : ∀ x : M,
      iteratedDerivWithin j
          (fun s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x (eig.toFun x) ((Sfam s).toFun x))
          (Set.Icc (0 : ℝ) T) t
        = DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x)
            (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t) := by
    intro x
    have hL := clm_comm_iteratedDerivWithin_finiteOrder
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
        (I := I) (M := M) g₀ 0 2 x (eig.toFun x))
      (fun s => (Sfam s).toFun x) hT ht j (hγfam x)
    simpa only [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS_apply]
      using hL
  have hjet_slice_cont : Continuous (fun x : M =>
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
        (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)) := by
    have harg : ContinuousOn (fun x : M => ((x, t) : M × ℝ)) (Set.univ : Set M) := by fun_prop
    have hmaps : Set.MapsTo (fun x : M => ((x, t) : M × ℝ)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun x _ => ⟨Set.mem_univ _, ht⟩
    have hcomp := hdiag.comp harg hmaps
    rw [continuousOn_univ] at hcomp
    exact hcomp
  have hjet_int : MeasureTheory.Integrable (fun x : M =>
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
        (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)) μ :=
    integrableOn_univ.mp (hjet_slice_cont.continuousOn.integrableOn_compact isCompact_univ)
  have heig_int : MeasureTheory.Integrable (fun x : M =>
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (eig.toFun x) (eig.toFun x)) μ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) eig eig
  have hmaj_int : MeasureTheory.Integrable (fun x : M =>
      (DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (eig.toFun x) (eig.toFun x) +
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)) / 2) μ :=
    (heig_int.add hjet_int).div_const 2
  have hbound_pt : ∀ x : M,
      ‖iteratedDerivWithin j
          (fun s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x (eig.toFun x) ((Sfam s).toFun x))
          (Set.Icc (0 : ℝ) T) t‖ ≤
        (DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (eig.toFun x) (eig.toFun x) +
          DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
            (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
            (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)) / 2 := by
    intro x
    rw [hfib x, Real.norm_eq_abs]
    exact tensorInnerPointwise_abs_le_half_selfInner_add (I := I) (M := M) g₀ x _ _
  have h1 : ‖∫ x, iteratedDerivWithin j
        (fun s => DifferentialGeometry.Integral.L2.tensorInnerPointwise
          (I := I) (M := M) g₀ 0 2 x (eig.toFun x) ((Sfam s).toFun x))
        (Set.Icc (0 : ℝ) T) t ∂μ‖ ≤
      ∫ x, (DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (eig.toFun x) (eig.toFun x) +
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)) / 2 ∂μ :=
    MeasureTheory.norm_integral_le_of_norm_le hmaj_int
      (Filter.Eventually.of_forall hbound_pt)
  have h2 : (∫ x, (DifferentialGeometry.Integral.L2.tensorInnerPointwise
          (I := I) (M := M) g₀ 0 2 x (eig.toFun x) (eig.toFun x) +
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)) / 2 ∂μ)
      = ((∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x (eig.toFun x) (eig.toFun x) ∂μ) +
          (∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
            (I := I) (M := M) g₀ 0 2 x
            (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
            (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t) ∂μ)) / 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add heig_int hjet_int]
  have h3 : (∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x (eig.toFun x) (eig.toFun x) ∂μ) = 1 :=
    eigenvectorSmooth_selfInner_integral_eq_one (I := I) (M := M) g₀ i
  have h4 : (∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
        (I := I) (M := M) g₀ 0 2 x
        (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
        (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t) ∂μ)
      ≤ K * μ.real Set.univ := by
    have hle : (∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
          (I := I) (M := M) g₀ 0 2 x
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t)
          (iteratedDerivWithin j (fun s => (Sfam s).toFun x) (Set.Icc (0 : ℝ) T) t) ∂μ)
        ≤ ∫ _x, K ∂μ := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const K) ?_
      · exact Filter.Eventually.of_forall (fun x =>
          DifferentialGeometry.Integral.L2.tensorInnerPointwise_nonneg
            (I := I) (M := M) g₀ 0 2 x _)
      · refine Filter.Eventually.of_forall (fun x => ?_)
        have hKx := hK (x, t) ⟨Set.mem_univ _, ht⟩
        rw [Real.norm_eq_abs] at hKx
        exact le_trans (le_abs_self _) hKx
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_comm] at hle
    exact hle
  rw [hLHSfun, hinter]
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2, h3, h4]

end FiniteOrderReconJetEnergy

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
