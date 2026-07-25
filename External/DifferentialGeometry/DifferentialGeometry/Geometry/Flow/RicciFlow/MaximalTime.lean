import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.ExtendShiInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BBSLimitProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]





def SolutionAgreesOn
    {D Dhat : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Shat : SolutionOn (I := I) (M := M) Dhat)
    (U : Set Real) : Prop :=
  forall t : Real, t ∈ U ->
    S.family.metric t = Shat.family.metric t ∧
      S.family.connection t = Shat.family.connection t ∧
        S.ricci t = Shat.ricci t


def ExtendsPastEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ∃ eps : Real, 0 < eps ∧
    ∃ hwide : alpha < omega + eps,
      ∃ Shat : SolutionOn (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha (omega + eps) hwide),
        IsSolutionOn (I := I) Shat ∧
          SolutionAgreesOn (I := I) S Shat (Set.Ico alpha omega)


def IsMaximalAtEndpoint
    {alpha omega : Real} (hαω : alpha < omega)
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ¬ ExtendsPastEndpoint (I := I) hαω S



def Rm04RealizesSolutionConnectionOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) : Prop :=
  forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D,
    DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I)
      (S.family.metric (t : Real)) (S.family.connection (t : Real))
      (Rm04 (t : Real))



omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem rm04Realizes_metric
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    Rm04RealizesSolutionConnectionOn (I := I) S S.base.rm04 := by
  intro t
  simpa [SolutionOn.family, SolutionFamily.rm04, SolutionFamily.connection,
    metricCov] using
    (DifferentialGeometry.Integral.Connection.rm04Section_realizes (I := I) (M := M)
      (S.base.metric (t : Real))
      (metricCov (I := I) (M := M) (S.base.metric (t : Real)))
      (metricCov_smooth (I := I) (M := M) (S.base.metric (t : Real))))


def curvatureNormSq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
@[simp] theorem curvatureNormSq_apply
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (t : Real) (x : M) :
    curvatureNormSq (I := I) S Rm04 t x =
      Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4 ((Rm04 t) x) := by
  rfl



def Rm04NormSqUnboundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) : Prop :=
  forall K : Real, ∃ t : Real, ∃ x : M,
    alpha <= t ∧ t < omega ∧ K < curvatureNormSq (I := I) S Rm04 t x



def Rm04NormSqBoundedAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)) : Prop :=
  ∃ K : Real, forall t : Real, forall x : M,
    alpha <= t -> t < omega ->
      curvatureNormSq (I := I) S Rm04 t x <= K



omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem rmBounded_of_not_unbounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)}
    (hnot : ¬ Rm04NormSqUnboundedAt (I := I) S Rm04) :
    Rm04NormSqBoundedAt (I := I) S Rm04 := by
  classical
  unfold Rm04NormSqUnboundedAt at hnot
  simp only [not_forall, not_exists, not_and, not_lt] at hnot
  rcases hnot with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro t x ht hT
  exact hK t x ht hT

set_option maxHeartbeats 1000000 in



theorem extends_of_rmBounded
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank ℝ E = 3)
    (_hS : IsSolutionOn (I := I) S)
    (_hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04)
    (_hbound : Rm04NormSqBoundedAt (I := I) S Rm04) :
    ExtendsPastEndpoint (I := I) hαω S := by
  let g_fam := S.base.metric

  have hleft := ricciFlowPDE_Ici_of_soln (I := I) _hS

  obtain ⟨K', hK'bound⟩ := _hbound
  have hbound_raw : ∀ t : ℝ, ∀ x : M, alpha ≤ t → t < omega →
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 ((Rm04 t) x) ≤ K' := by
    intro t x ht1 ht2
    have h := hK'bound t x ht1 ht2
    simpa [curvatureNormSq, SolutionOn.family] using h

  have hRmRaw : ∀ t ∈ Set.Ico alpha omega,
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t) := by
    intro t ht
    have h := _hRm ⟨t, ht⟩
    simpa [SolutionOn.family, SolutionFamily.connection, metricCov] using h
  have hric := ric_quad_le_of_soln (I := I) hRmRaw hbound_raw
  have hbound_can := rm04_bound_can (I := I) Rm04 hRmRaw ⟨K', hbound_raw⟩

  obtain ⟨hell, hcov⟩ := extendInputs_of_soln (I := I) hdim _hS
    (K := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K') (by positivity) hric hbound_can

  obtain ⟨t_star, ht_star, TT, hreach, rr, hrr0, hrr_smooth, hrr_cont, hrr_pde⟩ :=
    ricci_flow_interior_restart (I := I) g_fam hαω hell hcov
  have ht1 : alpha ≤ t_star := ht_star.1
  have ht2 : t_star < omega := ht_star.2

  have hsmooth_left := fun (x₀ : M) (i j : Fin (Module.finrank ℝ E)) =>
    chartGram_smooth_of_soln (I := I) _hS x₀ i j
  have hcont_left := fun (x₀ : M) (i j : Fin (Module.finrank ℝ E)) =>
    chartGram_cont_of_soln (I := I) _hS x₀ i j

  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => ((p.1 - t_star, p.2) : ℝ × M)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  have h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (rr (p.1 - t_star)) x₀ p.2 i j)
        (Set.Ioo t_star omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun q : ℝ × M => ((q.1 - t_star, q.2) : ℝ × M))
        (Set.Ioo t_star omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ioo (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
      fun q hq => ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2, hreach]⟩, hq.2⟩
    exact (hrr_smooth x₀ i j).comp hshift.contMDiffOn hmaps
  have h2cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (rr (p.1 - t_star)) x₀ p.2 i j)
        (Set.Ico t_star omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hmaps : Set.MapsTo (fun q : ℝ × M => ((q.1 - t_star, q.2) : ℝ × M))
        (Set.Ico t_star omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
        (Set.Ico (0 : ℝ) TT ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
      fun q hq => ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2, hreach]⟩, hq.2⟩
    exact (hrr_cont x₀ i j).comp hshift.continuous.continuousOn hmaps
  have h2pde : ∀ t ∈ Set.Ico t_star omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (rr (s - t_star)).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (rr (t - t_star)) x v w) (Set.Ici t_star) t := by
    intro t ht x v w
    have hmem : t - t_star ∈ Set.Ico (0 : ℝ) TT :=
      ⟨by linarith [ht.1], by linarith [ht.2, hreach]⟩
    have hd := hrr_pde (t - t_star) hmem x v w
    have hφ : HasDerivWithinAt (fun s : ℝ => s - t_star) 1 (Set.Ici t_star) t :=
      (hasDerivWithinAt_id t (Set.Ici t_star)).sub_const t_star
    have hmapsφ : Set.MapsTo (fun s : ℝ => s - t_star) (Set.Ici t_star) (Set.Ici 0) :=
      fun s hs => by simp only [Set.mem_Ici] at hs ⊢; linarith
    have hchain := hd.comp t hφ hmapsφ
    simpa using hchain
  have h1pde : ∀ t ∈ Set.Ico t_star omega, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici t_star) t :=
    fun t ht x v w =>
      (hleft t ⟨le_trans ht1 ht.1, ht.2⟩ x v w).mono (Set.Ici_subset_Ici.mpr ht1)
  have h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ioo t_star omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hsmooth_left x₀ i j).mono
      (Set.prod_mono (Set.Ioo_subset_Ioo ht1 le_rfl) (le_refl _))
  have h1cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.Ico t_star omega ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hcont_left x₀ i j).mono
      (Set.prod_mono (Set.Ico_subset_Ico ht1 le_rfl) (le_refl _))
  have h0 : g_fam t_star = (fun t : ℝ => rr (t - t_star)) t_star := by
    simp only [sub_self]; exact hrr0.symm
  have hagree_overlap : ∀ s ∈ Set.Ico t_star omega, rr (s - t_star) = g_fam s :=
    fun s hs =>
      (ricci_flow_forward_unique (I := I) g_fam (fun t => rr (t - t_star)) ht2
        h1smooth h1cont h2smooth h2cont h1pde h2pde h0 s hs).symm

  obtain ⟨ε, hε, g_ext, hagree, _hsmooth, _hcont, hpde⟩ :=
    extend_construction_of_restart (I := I) g_fam hαω hleft hsmooth_left hcont_left
      ht1 ht2 hreach rr hrr_smooth hrr_cont hrr_pde hagree_overlap

  have hwide : alpha < omega + ε := by linarith
  let Shat : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha (omega + ε) hwide) :=
    { base := { metric := g_ext } }
  refine ⟨ε, hε, hwide, Shat, ?_, ?_⟩
  ·
    exact DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_extendData
      hwide hαω g_ext S _hS hagree _hsmooth _hcont hpde
  ·
    intro t ht
    have htlt : t < omega := ht.2
    have hteq : g_ext t = g_fam t := hagree t htlt
    refine ⟨?_, ?_, ?_⟩
    ·
      show S.family.metric t = Shat.family.metric t
      change S.base.metric t = g_ext t
      exact hteq.symm
    ·
      show S.family.connection t = Shat.family.connection t
      change S.base.connection t = (SolutionFamily.connection { metric := g_ext }) t
      simp only [SolutionFamily.connection]
      congr 1; exact hteq.symm
    ·
      show S.ricci t = Shat.ricci t
      change S.base.ricci t = SolutionFamily.ricci { metric := g_ext } t
      simp only [SolutionFamily.ricci]
      congr 1; exact hteq.symm






theorem rmUnbounded_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    {Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRm : Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    Rm04NormSqUnboundedAt (I := I) S Rm04 := by
  by_contra hnot
  exact hmax (extends_of_rmBounded (I := I) hdim hS hRm
    (rmBounded_of_not_unbounded (I := I) hnot))




def FormsSingularityAt
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  ∃ Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M),
    Rm04RealizesSolutionConnectionOn (I := I) S Rm04 ∧
      Rm04NormSqUnboundedAt (I := I) S Rm04



theorem formsSing_of_maximal
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S)
    (hRmEx :
      ∃ Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M),
        Rm04RealizesSolutionConnectionOn (I := I) S Rm04) :
    FormsSingularityAt (I := I) S := by
  rcases hRmEx with ⟨Rm04, hRm⟩
  exact ⟨Rm04, hRm, rmUnbounded_of_maximal (I := I) hdim hS hmax hRm⟩


theorem formsSing_of_maximal_metric
    {alpha omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    (hdim : Module.finrank ℝ E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hmax : IsMaximalAtEndpoint (I := I) hαω S) :
    FormsSingularityAt (I := I) S := by
  exact formsSing_of_maximal (I := I) hdim hS hmax
    ⟨S.base.rm04, rm04Realizes_metric (I := I) S⟩




def SingularIffMaximalAtEndpoint
    {alpha omega : Real} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)) : Prop :=
  FormsSingularityAt (I := I) S ↔
    IsMaximalAtEndpoint (I := I) hαω S

end DifferentialGeometry.PDE.RicciFlow
