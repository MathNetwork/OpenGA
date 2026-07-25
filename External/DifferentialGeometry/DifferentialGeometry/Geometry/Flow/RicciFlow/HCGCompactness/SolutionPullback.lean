import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity










noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private lemma infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide





omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem _root_.IsLocalFrameOn.pushforward
    {ι : Type*} {frame : ι → (x : M) → TangentSpace I x} {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (Φ : M ≃ₘ⟮I, I⟯ N) :
    IsLocalFrameOn (V := (TangentSpace I : N → Type _)) I E (∞ : WithTop ℕ∞)
      (fun i (y : N) => mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y))) (Φ '' u) where
  linearIndependent {y} hy := by
    have hsymm : Φ.symm y ∈ u := by
      obtain ⟨x, hx, hxy⟩ := hy; rw [← hxy, Φ.symm_apply_apply]; exact hx
    have hb : (fun i => mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
        = ⇑((hframe.toBasisAt hsymm).map
            (Φ.mfderivToContinuousLinearEquiv infty_ne_zero (Φ.symm y)).toLinearEquiv) := by
      funext i
      rw [Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
        Φ.mfderivToContinuousLinearEquiv_coe]
    show LinearIndependent ℝ (fun i => mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
    rw [hb]
    exact Module.Basis.linearIndependent _
  generating {y} hy := by
    have hsymm : Φ.symm y ∈ u := by
      obtain ⟨x, hx, hxy⟩ := hy; rw [← hxy, Φ.symm_apply_apply]; exact hx
    have hb : (fun i => mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
        = ⇑((hframe.toBasisAt hsymm).map
            (Φ.mfderivToContinuousLinearEquiv infty_ne_zero (Φ.symm y)).toLinearEquiv) := by
      funext i
      rw [Module.Basis.map_apply, IsLocalFrameOn.toBasisAt_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, ← ContinuousLinearEquiv.coe_coe,
        Φ.mfderivToContinuousLinearEquiv_coe]
    show ⊤ ≤ Submodule.span ℝ (Set.range
      (fun i => mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y))))
    rw [hb]
    exact (Module.Basis.span_eq _).ge
  contMDiffOn i := by
    have hmaps : Set.MapsTo (Φ.symm : N → M) (Φ '' u) u := by
      rintro y ⟨x, hx, rfl⟩; rw [Φ.symm_apply_apply]; exact hx
    have h1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (fun y : N => TotalSpace.mk' E (Φ.symm y) (frame i (Φ.symm y))) (Φ '' u) :=
      (hframe.contMDiffOn i).comp (Φ.symm.contMDiff.contMDiffOn) hmaps
    have h2 := (Φ.contMDiff.contMDiff_tangentMap (by simp)).comp_contMDiffOn h1
    refine h2.congr ?_
    intro y _hy
    change TotalSpace.mk' E y (mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y)))
       = tangentMap I I (Φ : M → N) (TotalSpace.mk' E (Φ.symm y) (frame i (Φ.symm y)))
    exact (congrArg
      (fun b : N => TotalSpace.mk' E (E := fun z : N => TangentSpace I z) b
        (mfderiv I I (Φ : M → N) (Φ.symm y) (frame i (Φ.symm y))))
      (Φ.apply_symm_apply y)).symm





omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem gradientFun_pullback
    [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (f : N → ℝ) (y : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ y)) :
    gradientFun (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) (f ∘ (Φ : M → N)) y
      = (Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm
          (gradientFun (I := I) g f (Φ y)) := by
  have he : mfderiv I I (Φ : M → N) y
      = ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y :
          TangentSpace I y →L[ℝ] TangentSpace I (Φ y))) :=
    (Φ.mfderivToContinuousLinearEquiv_coe infty_ne_zero (x := y)).symm
  apply (metricFlatEquiv (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) y).injective
  ext w
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, gradientFun_eq, inner_metricSharp,
    Diffeomorph.pullbackMetric_inner, he, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, gradientFun_eq, inner_metricSharp,
    mfderiv_comp y hf (Φ.contMDiff.mdifferentiableAt infty_ne_zero)]
  simp only [ContinuousLinearMap.coe_comp, he]
  rfl





omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem mfderiv_symm_apply
    (Φ : M ≃ₘ⟮I, I⟯ N) (y : M) (v : TangentSpace I (Φ y)) :
    (Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v
      = mfderiv I I (Φ.symm : N → M) (Φ y) v := by
  have he : mfderiv I I (Φ : M → N) y
      = ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y :
          TangentSpace I y →L[ℝ] TangentSpace I (Φ y))) :=
    (Φ.mfderivToContinuousLinearEquiv_coe infty_ne_zero (x := y)).symm
  have heq : ((Φ.symm : N → M) ∘ (Φ : M → N)) =ᶠ[nhds y] id :=
    Filter.Eventually.of_forall (fun z => Φ.symm_apply_apply z)
  have hli : (mfderiv I I (Φ.symm : N → M) (Φ y)
      (mfderiv I I (Φ : M → N) y ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v))
        : TangentSpace I y)
      = (Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp y (Φ.symm.contMDiff.mdifferentiableAt infty_ne_zero)
        (Φ.contMDiff.mdifferentiableAt infty_ne_zero),
      heq.mfderiv_eq, mfderiv_id]
    exact ContinuousLinearMap.id_apply
      ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v)
  have h2 : mfderiv I I (Φ : M → N) y
      ((Φ.mfderivToContinuousLinearEquiv infty_ne_zero y).symm v) = v := by
    rw [he, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [h2] at hli
  exact hli.symm


def solutionOn_pullback [SigmaCompactSpace M] [T2Space M]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) :
    SolutionOn (I := I) (M := M) D where
  base := { metric := fun t => Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ }



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem pullback_coeff_eq
    [SigmaCompactSpace M] [T2Space M] [SigmaCompactSpace N] [T2Space N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N)
    (x : M) (X Y : TangentSpace I x) :
    (fun t : ℝ => ((solutionOn_pullback (I := I) S Φ).family.metric t).inner x X Y)
      = fun t : ℝ => (S.family.metric t).inner (Φ x)
          (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y) := by
  funext t
  exact Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric t) Φ x X Y





omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricFamilySmoothOn_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    MetricFamilySmoothOn (I := I) D (solutionOn_pullback (I := I) S Φ).family where
  coeff x X Y := by
    rw [pullback_coeff_eq (I := I) S Φ x X Y]
    exact hS.smoothMetric.coeff (Φ x)
      (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y)
  coeff_cont x X Y := by
    rw [pullback_coeff_eq (I := I) S Φ x X Y]
    exact hS.smoothMetric.coeff_cont (Φ x)
      (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y)
  metricTensor_cont := by
    apply Tensor0SFamilyContinuousOnSet.congr
      (Tensor0SFamilyContinuousOnSet.pullback (I := I)
        (fun t x => Tensor0SBundle.metricTensorField (I := I) (S.family.metric t) x)
        hS.smoothMetric.metricTensor_cont Φ)
    intro t _ht x
    have hm : (solutionOn_pullback (I := I) S Φ).family.metric t
        = Diffeomorph.pullbackMetric (I := I) (S.family.metric t) Φ := rfl
    ext slots
    rw [hm]
    change (S.family.metric t).inner (Φ x)
        (mfderiv I I (Φ : M → N) x (slots 0))
        (mfderiv I I (Φ : M → N) x (slots 1)) =
      (Diffeomorph.pullbackMetric (I := I) (S.family.metric t) Φ).inner x
        (slots 0) (slots 1)
    exact (Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric t) Φ x
      (slots 0) (slots 1)).symm
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    have heq : (fun p : ℝ × M =>
          ((solutionOn_pullback (I := I) S Φ).family.metric p.1).inner p.2
            (frame i p.2) (frame j p.2))
        = fun p : ℝ × M => (S.family.metric p.1).inner (Φ p.2)
            (mfderiv I I (Φ : M → N) p.2 (frame i p.2))
            (mfderiv I I (Φ : M → N) p.2 (frame j p.2)) := by
      funext p
      exact Diffeomorph.pullbackMetric_inner (I := I) (S.family.metric p.1) Φ p.2
        (frame i p.2) (frame j p.2)
    rw [heq]

    have hpf := hS.smoothMetric.frameCompSmooth
      (fun k (y : N) => mfderiv I I (Φ : M → N) (Φ.symm y) (frame k (Φ.symm y)))
      (hframe.pushforward Φ) i j
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (∞ : WithTop ℕ∞)
        (fun p : ℝ × M => (p.1, (Φ : M → N) p.2)) :=
      contMDiff_fst.prodMk (Φ.contMDiff.comp contMDiff_snd)
    have hmaps : Set.MapsTo (fun p : ℝ × M => (p.1, (Φ : M → N) p.2))
        (D.regular ×ˢ u) (D.regular ×ˢ (Φ '' u)) :=
      fun p hp => ⟨hp.1, Set.mem_image_of_mem _ hp.2⟩
    have hcomp := hpf.comp hmap.contMDiffOn hmaps

    have hN : ∀ (k : Idx) (x : M),
        (mfderiv I I (Φ : M → N) (Φ.symm (Φ x)) (frame k (Φ.symm (Φ x))) : E)
          = (mfderiv I I (Φ : M → N) x (frame k x) : E) :=
      fun k x => congrArg
        (fun a : M => (mfderiv I I (Φ : M → N) a (frame k a) : E)) (Φ.symm_apply_apply x)
    refine hcomp.congr ?_
    intro p _hp
    simp only [Function.comp_apply, hN]




omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricVariationEquation_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    MetricVariationEquationOn (I := I) (solutionOn_pullback (I := I) S Φ) := by
  intro t x X Y
  have hcoeff := pullback_coeff_eq (I := I) S Φ x X Y
  have hric :
      RicciAtFamily.toTensorField (I := I)
          (solutionOn_pullback (I := I) S Φ).ricciAt (t : ℝ) x X Y
        = RicciAtFamily.toTensorField (I := I) S.ricciAt (t : ℝ) (Φ x)
            (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y) := by
    simp only [RicciAtFamily.toTensorField_apply]
    change metricRicciAt (I := I)
          (Diffeomorph.pullbackMetric (I := I) (S.base.metric (t : ℝ)) Φ) x (vec2 X Y)
        = metricRicciAt (I := I) (S.base.metric (t : ℝ)) (Φ x)
            (vec2 (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y))
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact DifferentialGeometry.HCGCompactness.ricciTensor_pullback (I := I)
      (S.base.metric (t : ℝ)) Φ x X Y
  rw [hcoeff, hric]
  exact hS.equation t (Φ x)
    (mfderiv I I (Φ : M → N) x X) (mfderiv I I (Φ : M → N) x Y)

set_option maxHeartbeats 1000000 in


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (x : M) :
    (solutionOn_pullback (I := I) S Φ).scalar t x = S.scalar t (Φ x) := by
  simp only [SolutionOn.scalar, SolutionFamily.scalar, solutionOn_pullback]
  exact DifferentialGeometry.HCGCompactness.metricScalarAt_pullback (I := I)
    (S.base.metric t) Φ x



omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarCont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    ContinuousOn (fun q : ℝ × M => (solutionOn_pullback (I := I) S Φ).scalar q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set M)) := by
  have heq : (fun q : ℝ × M => (solutionOn_pullback (I := I) S Φ).scalar q.1 q.2)
      = (fun p : ℝ × N => S.scalar p.1 p.2)
          ∘ (fun q : ℝ × M => ((q.1, Φ q.2) : ℝ × N)) := by
    funext q; exact scalar_pullback (I := I) S Φ q.1 q.2
  rw [heq]
  exact hS.scalarCont.comp
    (continuous_fst.prodMk ((Φ.continuous).comp continuous_snd)).continuousOn
    (fun q hq => ⟨hq.1, Set.mem_univ _⟩)




omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarTime_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) {K : Set ℝ} {t : ℝ} (htK : t ∈ K) (hKsub : K ⊆ D.carrier)
    (x : M) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => (solutionOn_pullback (I := I) S Φ).scalar s x) K t := by
  have heq : (fun s : ℝ => (solutionOn_pullback (I := I) S Φ).scalar s x)
      = fun s : ℝ => S.scalar s (Φ x) := by
    funext s; exact scalar_pullback (I := I) S Φ s x
  rw [heq]
  exact hS.scalarTime htK hKsub (Φ x)




omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricRicci_pullback_eval
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M)
    (slots : Fin 2 → TangentSpace I x) :
    metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x slots
      = metricRicci (I := I) g (Φ x)
          (fun q : Fin 2 => mfderiv I I (Φ : M → N) x (slots q)) := by
  have hLHS : metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x
        (vec2 (slots 0) (slots 1))
      = ricciTensor (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x (slots 0) (slots 1) := by
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  have hRHS : metricRicci (I := I) g (Φ x)
        (vec2 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1)))
      = ricciTensor (I := I) g (Φ x)
          (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1)) := by
    rw [metricRicci_apply, metricRicciAt_apply_eq_ricciTensor]
  have hpb := DifferentialGeometry.HCGCompactness.ricciTensor_pullback (I := I) g Φ x
    (slots 0) (slots 1)
  rw [show vec2 (slots 0) (slots 1) = slots from by funext i; fin_cases i <;> rfl] at hLHS
  rw [show vec2 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
        = (fun q : Fin 2 => mfderiv I I (Φ : M → N) x (slots q)) from by
      funext i; fin_cases i <;> rfl] at hRHS
  rw [hLHS, hpb, ← hRHS]

set_option maxHeartbeats 1000000 in



omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciNorm_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (x : M) :
    ricciNorm (I := I) (solutionOn_pullback (I := I) S Φ) t x = ricciNorm (I := I) S t (Φ x) := by
  obtain ⟨B, hB⟩ :=
    exists_gOrthonormalBasis (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x
  change Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x 2
        (metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x)
      = Tensor0SBundle.normSq0S (I := I) (S.base.metric t) (Φ x) 2
          (metricRicci (I := I) (S.base.metric t) (Φ x))
  exact DifferentialGeometry.HCGCompactness.normSq0S_pullback_eval_of_orthonormal (I := I)
    (g := S.base.metric t) Φ x 2 B hB
    (metricRicci (I := I) (Diffeomorph.pullbackMetric (I := I) (S.base.metric t) Φ) x)
    (metricRicci (I := I) (S.base.metric t) (Φ x))
    (fun slots => metricRicci_pullback_eval (I := I) (S.base.metric t) Φ x slots)




omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciNormSpace_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) (t : ℝ) (ht : t ∈ D.carrier) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (ricciNorm (I := I) (solutionOn_pullback (I := I) S Φ) t) x := by
  have heq : ricciNorm (I := I) (solutionOn_pullback (I := I) S Φ) t
      = (ricciNorm (I := I) S t) ∘ (Φ : M → N) := by
    funext y; exact ricciNorm_pullback (I := I) S Φ t y
  rw [heq]
  exact (hS.ricciNormSpace t ht (Φ x)).comp x
    (Φ.contMDiff.mdifferentiableAt (by simp))




omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciCont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 D.carrier
      (fun t x => (solutionOn_pullback (I := I) S Φ).ricci t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.pullback (I := I)
      (fun t x => S.ricci t x) hS.ricciCont Φ)
  intro t _ht x
  ext slots
  exact (metricRicci_pullback_eval (I := I) (S.base.metric t) Φ x slots).symm





omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricRm04_pullback_eval
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) (x : M)
    (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x slots
      = metricRm04 (I := I) g (Φ x)
          (fun q : Fin 4 => mfderiv I I (Φ : M → N) x (slots q)) := by
  have hLHS : metricRm04 (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x
        (vec4 (slots 0) (slots 1) (slots 2) (slots 3))
      = metricRm04StdAt (I := I) (Diffeomorph.pullbackMetric (I := I) g Φ) x
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    rw [metricRm04_apply, metricRm04StdAt_apply]
  have hRHS : metricRm04 (I := I) g (Φ x)
        (vec4 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
          (mfderiv I I (Φ : M → N) x (slots 2)) (mfderiv I I (Φ : M → N) x (slots 3)))
      = metricRm04StdAt (I := I) g (Φ x)
          (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
          (mfderiv I I (Φ : M → N) x (slots 2)) (mfderiv I I (Φ : M → N) x (slots 3)) := by
    rw [metricRm04_apply, metricRm04StdAt_apply]
  have hpb := metricRm04Std_pullback (I := I) g Φ x (slots 0) (slots 1) (slots 2) (slots 3)
  rw [show vec4 (slots 0) (slots 1) (slots 2) (slots 3) = slots from by
      funext i; fin_cases i <;> rfl] at hLHS
  rw [show vec4 (mfderiv I I (Φ : M → N) x (slots 0)) (mfderiv I I (Φ : M → N) x (slots 1))
          (mfderiv I I (Φ : M → N) x (slots 2)) (mfderiv I I (Φ : M → N) x (slots 3))
        = (fun q : Fin 4 => mfderiv I I (Φ : M → N) x (slots q)) from by
      funext i; fin_cases i <;> rfl] at hRHS
  rw [hLHS, hpb, ← hRHS]




omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem rm04Cont_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    Tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.carrier
      (fun t x => (solutionOn_pullback (I := I) S Φ).base.rm04 t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.pullback (I := I)
      (fun t x => S.base.rm04 t x) hS.rm04Cont Φ)
  intro t _ht x
  ext slots
  exact (metricRm04_pullback_eval (I := I) (S.base.metric t) Φ x slots).symm




omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothConnection_pullback
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (Φ : M ≃ₘ⟮I, I⟯ N) :
    ConnectionFamilySmoothOn (I := I) (solutionOn_pullback (I := I) S Φ).family := by
  intro t
  exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I)
    ((solutionOn_pullback (I := I) S Φ).base.metric (t : ℝ))










omit [FiniteDimensional ℝ E] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem isSolutionOn_pullback
    [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold I N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn (I := I) S)
    (Φ : M ≃ₘ⟮I, I⟯ N) :
    IsSolutionOn (I := I) (solutionOn_pullback (I := I) S Φ) where
  smoothMetric := metricFamilySmoothOn_pullback (I := I) S hS Φ
  smoothConnection := smoothConnection_pullback (I := I) S Φ
  equation := metricVariationEquation_pullback (I := I) S hS Φ
  scalarCont := scalarCont_pullback (I := I) S hS Φ
  scalarTime := scalarTime_pullback (I := I) S hS Φ
  ricciCont := ricciCont_pullback (I := I) S hS Φ
  rm04Cont := rm04Cont_pullback (I := I) S hS Φ
  ricciNormSpace := ricciNormSpace_pullback (I := I) S hS Φ
  ricciNormGrad := by
    intro t _ht x
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        (ricciNorm (I := I) (solutionOn_pullback (I := I) S Φ) t) := by
      refine (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := M)
        ((solutionOn_pullback (I := I) S Φ).family.metric t)
        (metricRicci (I := I) (M := M)
          ((solutionOn_pullback (I := I) S Φ).family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I)
      ((solutionOn_pullback (I := I) S Φ).family.metric t) hsmooth x


end RicciFlow
end PDE
end DifferentialGeometry

end
