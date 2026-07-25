import DifferentialGeometry.Geometry.Comparison.InjectivityRadius
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false






















open Set Function Manifold
open scoped Topology Manifold ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

section GenericGlue

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞}





theorem exists_diffeo_of_injOn [Nonempty M]
    {f : M → N} {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) :
    ∃ Φ : PartialDiffeomorph I J M N n,
      Φ.source = s ∧ Φ.target = f '' s ∧ EqOn Φ f s := by
  classical

  have htgt : IsOpen (f '' s) := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨φ, hxφ, hEq⟩ := hf ⟨x, hx⟩
    refine ⟨φ '' (s ∩ φ.source), ?_, ?_, ⟨x, ⟨hx, hxφ⟩, (hEq hxφ).symm⟩⟩
    · rintro z ⟨x', ⟨hx's, hx'φ⟩, rfl⟩
      exact ⟨x', hx's, hEq hx'φ⟩
    · exact φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hs.inter φ.open_source) inter_subset_right


  have hinv : ContMDiffOn J I n (invFunOn f s) (f '' s) := by
    apply contMDiffOn_of_locally_contMDiffOn
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨φ, hxφ, hEq⟩ := hf ⟨x, hx⟩
    refine ⟨φ '' (s ∩ φ.source),
      φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hs.inter φ.open_source) inter_subset_right,
      ⟨x, ⟨hx, hxφ⟩, (hEq hxφ).symm⟩, ?_⟩
    have hsub : φ '' (s ∩ φ.source) ⊆ φ.target := by
      rintro z ⟨x', ⟨_, hx'φ⟩, rfl⟩
      exact φ.toPartialEquiv.map_source hx'φ
    refine ((φ.symm.contMDiffOn.mono hsub).mono inter_subset_right).congr ?_
    rintro z ⟨-, x', ⟨hx's, hx'φ⟩, rfl⟩
    have h2 : f x' = φ x' := hEq hx'φ
    have hmem : invFunOn f s (φ x') ∈ s := invFunOn_mem ⟨x', hx's, h2⟩
    have happ : f (invFunOn f s (φ x')) = φ x' := invFunOn_eq ⟨x', hx's, h2⟩
    have h1 : φ.toPartialEquiv.symm (φ x') = x' := φ.toPartialEquiv.left_inv hx'φ
    show invFunOn f s (φ x') = φ.toPartialEquiv.symm (φ x')
    rw [h1]
    exact hinj hmem hx's (by rw [happ, h2])
  refine ⟨{
    toFun := f
    invFun := invFunOn f s
    source := s
    target := f '' s
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := fun y ⟨x', hx', hxy⟩ => invFunOn_mem ⟨x', hx', hxy⟩
    left_inv' := fun x hx => hinj.leftInvOn_invFunOn hx
    right_inv' := fun y ⟨x', hx', hxy⟩ => invFunOn_eq ⟨x', hx', hxy⟩
    open_source := hs
    open_target := htgt
    contMDiffOn_toFun := hf.contMDiffOn
    contMDiffOn_invFun := hinv }, rfl, rfl, fun x _ => rfl⟩

end GenericGlue

section ExpBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Exponential






omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem exists_expBall_diffeo
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hr : ENNReal.ofReal r < injRadius (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.ball (0 : E) r)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1,
      Φ.source = Metric.ball (0 : E) r ∧
      Φ.target = (fun v : E =>
        (expMap (I := I) g p (show TangentSpace I p from v) : M)) ''
          Metric.ball (0 : E) r ∧
      EqOn Φ (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r) :=
  exists_diffeo_of_injOn hloc Metric.isOpen_ball
    (injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p hr)







theorem exp_isLocalDiffeomorphOn_ball
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hr : r ≤ expMapC2Radius (I := I) g p) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (Metric.ball (0 : E) r) := by
  haveI : IsManifold I 1 M := by
    have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (by decide : (1 : ℕ∞) ≤ ⊤)
    exact IsManifold.of_le h1
  rintro ⟨x, hx⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  have hxR : ‖x‖ < expMapC2Radius (I := I) g p := lt_of_lt_of_le hx hr
  have hsrc : x ∈ (NormalCoordinates.expMapDiffeo (I := I) g p).source := by
    have h := ball_subset_normalChartAt_target (I := I) g p hxR
    rwa [NormalCoordinates.normalChartAt_target_eq] at h
  exact ⟨NormalCoordinates.expMapDiffeo (I := I) g p, hsrc,
    fun y hy => (NormalCoordinates.expMapDiffeo_apply_eq (I := I) g p hy).symm⟩






theorem exists_expBall_diffeo_of_lt
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hrinj : ENNReal.ofReal r < injRadius (I := I) g p)
    (hrC2 : r ≤ expMapC2Radius (I := I) g p) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1,
      Φ.source = Metric.ball (0 : E) r ∧
      Φ.target = (fun v : E =>
        (expMap (I := I) g p (show TangentSpace I p from v) : M)) ''
          Metric.ball (0 : E) r ∧
      EqOn Φ (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (Metric.ball (0 : E) r) :=
  exists_expBall_diffeo (I := I) g p hrinj (exp_isLocalDiffeomorphOn_ball (I := I) g p hrC2)

end ExpBall

end Riemannian
end Geometry
end DifferentialGeometry
