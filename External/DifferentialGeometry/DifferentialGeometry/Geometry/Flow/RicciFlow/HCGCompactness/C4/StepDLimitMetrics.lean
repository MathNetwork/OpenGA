import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackField
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDDirected
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ComponentConvAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvWindowAll
import DifferentialGeometry.Geometry.Topology.DirectLimitManifold
import DifferentialGeometry.Geometry.Topology.SigmaCompactOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]


def ballOpen (b : ∀ j, M j) (r : ℕ → ℝ) (j : ℕ) : Opens (M j) :=
  ⟨Metric.ball (b j) (r j), Metric.isOpen_ball⟩



def tailBallOpen (b : ∀ j, M j) (j₀ n : ℕ) : Opens (M (j₀ + n)) :=
  ⟨Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ n), Metric.isOpen_ball⟩

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in

theorem ballOpen_nonempty (b : ∀ j, M j) (r : ℕ → ℝ) (j : ℕ) (hr : 0 < r j) :
    Nonempty (ballOpen b r j) := by
  refine ⟨⟨b j, ?_⟩⟩
  exact Metric.mem_ball_self hr

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in

theorem tailBall_nonempty (b : ∀ j, M j) (j₀ n : ℕ) :
    Nonempty (tailBallOpen b j₀ n) :=
  ⟨⟨b (j₀ + n), Metric.mem_ball_self (by positivity)⟩⟩

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in


theorem tailBall_le_large (b : ∀ j, M j) (j₀ n : ℕ) :
    tailBallOpen b j₀ n ≤ ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) := by
  intro x hx
  change x ∈ Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ n) at hx
  change x ∈ Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))
  rw [Metric.mem_ball] at hx ⊢
  exact hx.trans_le (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))


noncomputable def tailMetric
    (b : ∀ j, M j) (j₀ : ℕ)
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (n : ℕ) : SmoothRiemannianMetric I (tailBallOpen b j₀ n) := by
  letI : SigmaCompactSpace (tailBallOpen b j₀ n) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  exact (gInf n).restrictOpenOfSubset (I := I) (tailBall_le_large b j₀ n)


def coreRadius (n : ℕ) : ℝ := (2 : ℝ) ^ n / 2


def tailCenter (b : ∀ j, M j) (j₀ n : ℕ) : tailBallOpen b j₀ n :=
  ⟨b (j₀ + n), Metric.mem_ball_self (by positivity)⟩


def tailCore (b : ∀ j, M j) (j₀ n : ℕ) : Set (tailBallOpen b j₀ n) :=
  {x | dist (b (j₀ + n)) (x : M (j₀ + n)) ≤ coreRadius n}


def limitCore (b : ∀ j, M j) (j₀ : ℕ)
    [∀ n, Nonempty (tailBallOpen b j₀ n)]
    (S : SmoothSeqSystem I (fun n => tailBallOpen b j₀ n)) (n : ℕ) :
    Set S.toSeqSystem.Lim :=
  S.toSeqSystem.incl n '' tailCore b j₀ n

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in

theorem core_subset_tail (b : ∀ j, M j) (j₀ n : ℕ) :
    Metric.closedBall (b (j₀ + n)) (coreRadius n) ⊆
      (tailBallOpen b j₀ n : Set (M (j₀ + n))) := by
  intro x hx
  change dist x (b (j₀ + n)) < (2 : ℝ) ^ n
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hx' : dist x (b (j₀ + n)) ≤ coreRadius n := by
    simpa only [Metric.mem_closedBall, dist_comm] using hx
  dsimp only [coreRadius] at hx'
  nlinarith

omit [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in


theorem tailCore_compact (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))] : IsCompact (tailCore b j₀ n) := by
  rw [Subtype.isCompact_iff]
  have hval : Subtype.val '' tailCore b j₀ n =
      Metric.closedBall (b (j₀ + n)) (coreRadius n) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [tailCore, Set.mem_setOf_eq, Metric.mem_closedBall, dist_comm] using hx
    · intro hy
      refine ⟨⟨y, core_subset_tail b j₀ n hy⟩, ?_, rfl⟩
      simpa only [tailCore, Set.mem_setOf_eq, Metric.mem_closedBall, dist_comm] using hy
  rw [hval]
  exact isCompact_closedBall _ _

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] in

theorem limitCore_closed (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m)) :
    IsClosed (limitCore b j₀ S n) := by
  exact ((tailCore_compact b j₀ n).image
    (S.toSeqSystem.continuous_incl n)).isClosed

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in


theorem incl_mem_coreInt (b : ∀ j, M j) (j₀ n : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    {x : tailBallOpen b j₀ n}
    (hx : dist (b (j₀ + n)) (x : M (j₀ + n)) < coreRadius n) :
    S.toSeqSystem.incl n x ∈ interior (limitCore b j₀ S n) := by
  let W : Set (tailBallOpen b j₀ n) :=
    (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ⁻¹'
      Metric.ball (b (j₀ + n)) (coreRadius n)
  have hWopen : IsOpen W := Metric.isOpen_ball.preimage continuous_subtype_val
  have hxW : x ∈ W := by
    simpa only [W, Set.mem_preimage, Metric.mem_ball, dist_comm] using hx
  have hWsub : S.toSeqSystem.incl n '' W ⊆ limitCore b j₀ S n := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    have hy' : dist (b (j₀ + n)) (y : M (j₀ + n)) < coreRadius n := by
      simpa only [W, Set.mem_preimage, Metric.mem_ball, dist_comm] using hy
    exact hy'.le
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset
    ((S.toSeqSystem.incl_isOpenMap n) W hWopen |>.mem_nhds
      (Set.mem_image_of_mem _ hxW)) hWsub

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)] in

theorem center_mem_coreInt (b : ∀ j, M j) (j₀ n : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m)) :
    S.toSeqSystem.incl n (tailCenter b j₀ n) ∈ interior (limitCore b j₀ S n) := by
  apply incl_mem_coreInt b j₀ n S
  simp only [tailCenter, dist_self, coreRadius]
  positivity

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [∀ j, SigmaCompactSpace (M j)] in


theorem frontier_core_radius (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    {q : S.toSeqSystem.Lim} (hq : q ∈ frontier (limitCore b j₀ S n)) :
    ∃ x : tailBallOpen b j₀ n,
      S.toSeqSystem.incl n x = q ∧
        dist (b (j₀ + n)) (x : M (j₀ + n)) = coreRadius n := by
  have hclosed := limitCore_closed b j₀ n S
  have hqK : q ∈ limitCore b j₀ S n := by
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hq
  have hnotInt : q ∉ interior (limitCore b j₀ S n) :=
    (mem_frontier_iff_notMem_interior hqK).mp hq
  obtain ⟨x, hx, hxeq⟩ := hqK
  refine ⟨x, hxeq, le_antisymm hx ?_⟩
  by_contra hnot
  have hlt : dist (b (j₀ + n)) (x : M (j₀ + n)) < coreRadius n :=
    lt_of_not_ge hnot
  have hint := incl_mem_coreInt b j₀ n S hlt
  exact hnotInt (hxeq ▸ hint)


def ballStep
    (b : ∀ j, M j) (r : ℕ → ℝ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hsrc : ∀ j, (ballOpen b r j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (ballOpen b r j : Set (M j)) ⊆
      (ballOpen b r (j + 1) : Set (M (j + 1))))
    (j : ℕ) : ballOpen b r j → ballOpen b r (j + 1) :=
  PartialDiffeomorph.opensMap (I := I) (M := M j) (N := M (j + 1))
    (Ψ j) (hsrc j) (hmap j)



def ballSystem
    (b : ∀ j, M j) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hsrc : ∀ j, (ballOpen b r j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (ballOpen b r j : Set (M j)) ⊆
      (ballOpen b r (j + 1) : Set (M (j + 1)))) :
    letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
    SmoothSeqSystem I (fun j => ballOpen b r j) := by
  letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
  exact SmoothSeqSystem.ofSucc (fun j => ballStep b r Ψ hsrc hmap j)
    (fun j => PartialDiffeomorph.opensMap_isOpenEmb (I := I) (M := M j) (N := M (j + 1))
      (Ψ j) (hsrc j) (hmap j))
    (fun j => PartialDiffeomorph.opensMap_contMDiff (I := I) (M := M j) (N := M (j + 1))
      (Ψ j) (hsrc j) (hmap j))
    (fun j => PartialDiffeomorph.opensMap_inv_mdiff (I := I) (M := M j) (N := M (j + 1))
      (Ψ j) (hsrc j) (hmap j))


def ballPullbackMetric {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (g : SmoothRiemannianMetric I (M l)) : SmoothRiemannianMetric I U := by
  let W : Opens (M l) :=
    ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  exact Diffeomorph.pullbackMetric (I := I) (g.restrictOpen (I := I) W) F


omit [CompleteSpace E] in
theorem ballPullback_inner {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (g : SmoothRiemannianMetric I (M l)) (x : U) (v w : TangentSpace I x) :
    (ballPullbackMetric Φ U hU g).inner x v w =
      g.inner ((Φ : M j → M l) x)
        (mfderiv I I (Φ : M j → M l) (x : M j) v)
        (mfderiv I I (Φ : M j → M l) (x : M j) w) := by
  let W : Opens (M l) :=
    ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  rw [ballPullbackMetric, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [PartialDiffeomorph.opensDiffeo_mfderiv Φ hU x v,
    PartialDiffeomorph.opensDiffeo_mfderiv Φ hU x w]
  rfl



def ballTransSource {j l m : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I (M l) (M m) (∞ : WithTop ℕ∞))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hnext : (Φ : M j → M l) '' (U : Set (M j)) ⊆ Θ.source) :
    (U : Set (M j)) ⊆ (PartialDiffeomorph.trans (I := I) Φ Θ).source := by
  intro x hx
  exact ⟨hU hx, hnext (Set.mem_image_of_mem _ hx)⟩


def nestedBallPullback {j l m : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I (M l) (M m) (∞ : WithTop ℕ∞))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hnext : (Φ : M j → M l) '' (U : Set (M j)) ⊆ Θ.source)
    (g : SmoothRiemannianMetric I (M m)) : SmoothRiemannianMetric I U := by
  let W : Opens (M l) :=
    ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  exact Diffeomorph.pullbackMetric (I := I) (ballPullbackMetric Θ W hnext g) F


omit [CompleteSpace E] in
theorem ballPullback_trans {j l m : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I (M l) (M m) (∞ : WithTop ℕ∞))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hnext : (Φ : M j → M l) '' (U : Set (M j)) ⊆ Θ.source)
    (g : SmoothRiemannianMetric I (M m)) :
    ballPullbackMetric (PartialDiffeomorph.trans (I := I) Φ Θ) U
        (ballTransSource Φ Θ U hU hnext) g =
      nestedBallPullback Φ Θ U hU hnext g := by
  have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I U),
      (∀ (x : U) (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
    intro g₁ g₂ h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply metric_ext
  intro x v w
  rw [ballPullback_inner]
  let W : Opens (M l) :=
    ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  change _ = (Diffeomorph.pullbackMetric (I := I)
    (ballPullbackMetric Θ W hnext g) F).inner x v w
  rw [Diffeomorph.pullbackMetric_inner, ballPullback_inner,
    PartialDiffeomorph.opensDiffeo_mfderiv,
    PartialDiffeomorph.opensDiffeo_mfderiv]
  have hΦd : MDifferentiableAt I I (Φ : M j → M l) (x : M j) :=
    (Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hU x.2))).mdifferentiableAt (by decide)
  have hΘd : MDifferentiableAt I I (Θ : M l → M m) ((Φ : M j → M l) x) :=
    (Θ.contMDiffOn_toFun.contMDiffAt
      (Θ.open_source.mem_nhds (hnext (Set.mem_image_of_mem _ x.2)))).mdifferentiableAt
        (by decide)
  have hcomp : mfderiv I I
      (PartialDiffeomorph.trans (I := I) Φ Θ : M j → M m) (x : M j) =
      (mfderiv I I (Θ : M l → M m) ((Φ : M j → M l) x)).comp
        (mfderiv I I (Φ : M j → M l) (x : M j)) := by
    exact mfderiv_comp (x : M j) hΘd hΦd
  rw [hcomp]
  rfl


omit [CompleteSpace E] in
theorem ballPullback_congr {j l : ℕ}
    (Φ Ψ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (U : Opens (M j)) (hΦ : (U : Set (M j)) ⊆ Φ.source)
    (hΨ : (U : Set (M j)) ⊆ Ψ.source)
    (g : SmoothRiemannianMetric I (M l))
    (hmap : (Φ : M j → M l) = (Ψ : M j → M l)) :
    ballPullbackMetric Φ U hΦ g = ballPullbackMetric Ψ U hΨ g := by
  have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I U),
      (∀ (x : U) (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
    intro g₁ g₂ h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply metric_ext
  intro x v w
  rw [ballPullback_inner, ballPullback_inner, hmap]



omit [CompleteSpace E] in
theorem ballPullback_cast {j l m : ℕ} (h : l = m)
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (g : ∀ n, SmoothRiemannianMetric I (M n))
    (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hU' : (U : Set (M j)) ⊆ (h ▸ Φ).source) :
    ballPullbackMetric (h ▸ Φ) U hU' (g m) = ballPullbackMetric Φ U hU (g l) := by
  subst h
  rfl


omit [CompleteSpace E] in
theorem ballPullback_assoc
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j a b : ℕ} (U : Opens (M j))
    (hA : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (hU : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j (a + b)).source) :
    ballPullbackMetric (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hA
        (g ((j + a) + b)) =
      ballPullbackMetric (chainComp (I := I) (Mf := M) Ψ j (a + b)) U hU
        (g (j + (a + b))) := by
  simpa only [chainCompAssoc] using
    ballPullback_cast (I := I) (M := M) (Nat.add_assoc j a b).symm
      (chainComp (I := I) (Mf := M) Ψ j (a + b)) g U hU hA


noncomputable def chainPullbackSeq
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ} (U : Opens (M j))
    (hU : ∀ k : ℕ, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j k).source)
    (k : ℕ) : SmoothRiemannianMetric I U :=
  ballPullbackMetric (chainComp (I := I) (Mf := M) Ψ j k) U (hU k) (g (j + k))


omit [CompleteSpace E] in
theorem chainPullback_zero
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ} (U : Opens (M j)) [SigmaCompactSpace U]
    (hU : ∀ k : ℕ, (U : Set (M j)) ⊆
      (chainComp (I := I) (Mf := M) Ψ j k).source) :
    chainPullbackSeq (I := I) Ψ g U hU 0 =
      (g j).restrictOpen (I := I) U := by
  change ballPullbackMetric (I := I) (PartialDiffeomorph.refl (I := I) (M j))
      U (hU 0) (g j) = (g j).restrictOpen (I := I) U
  have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I U),
      (∀ (x : U) (v w : TangentSpace I x), g₁.inner x v w = g₂.inner x v w) →
        g₁ = g₂ := by
    intro g₁ g₂ h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply metric_ext
  intro x v w
  rw [ballPullback_inner, SmoothRiemannianMetric.restrictOpen_inner]
  have hmfd : mfderiv I I
      (PartialDiffeomorph.refl (I := I) (M j) : M j → M j) (x : M j) =
        ContinuousLinearMap.id ℝ (TangentSpace I (x : M j)) := mfderiv_id
  rw [hmfd]
  rfl



omit [CompleteSpace E] in
theorem chainPullback_step
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ} (U : Opens (M j)) (V : Opens (M (j + 1)))
    (hU : ∀ k, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j k).source)
    (hV : ∀ k, (V : Set (M (j + 1))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j + 1) k).source)
    (hmap : (chainComp (I := I) (Mf := M) Ψ j 1 : M j → M (j + 1)) ''
      (U : Set (M j)) ⊆ (V : Set (M (j + 1))) )
    (b : ℕ) (x : U) (v w : TangentSpace I x) :
    (chainPullbackSeq (I := I) Ψ g U hU (1 + b)).inner x v w =
      (chainPullbackSeq (I := I) Ψ g V hV b).inner
        (PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ j 1) (hU 1) hmap x)
        (mfderiv I I (PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ j 1) (hU 1) hmap) x v)
        (mfderiv I I (PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ j 1) (hU 1) hmap) x w) := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let Φ := chainComp (I := I) (Mf := M) Ψ j 1
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + 1) b
  let F : U → V := PartialDiffeomorph.opensMap Φ (hU 1) hmap
  have hnext : (Φ : M j → M (j + 1)) '' (U : Set (M j)) ⊆ Θ.source :=
    hmap.trans (hV b)
  have hA : (U : Set (M j)) ⊆
      (chainCompAssoc (I := I) (Mf := M) Ψ j 1 b).source := by
    rw [chainAssoc_source (I := I) (Mf := M) Ψ j 1 b]
    exact hU (1 + b)
  have htrans : (U : Set (M j)) ⊆
      (PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    ballTransSource Φ Θ U (hU 1) hnext
  have hassoc := ballPullback_assoc (I := I) Ψ g U hA (hU (1 + b))
  have hcongr := ballPullback_congr (I := I)
    (chainCompAssoc (I := I) (Mf := M) Ψ j 1 b)
    (PartialDiffeomorph.trans (I := I) Φ Θ) U hA htrans (g ((j + 1) + b))
    (chainCompAssoc_eq (I := I) (Mf := M) Ψ j 1 b)
  have htransMetric := ballPullback_trans (I := I) Φ Θ U (hU 1) hnext (g ((j + 1) + b))
  calc
    (chainPullbackSeq (I := I) Ψ g U hU (1 + b)).inner x v w =
        (ballPullbackMetric (chainCompAssoc (I := I) (Mf := M) Ψ j 1 b)
          U hA (g ((j + 1) + b))).inner x v w := by
      simpa only [chainPullbackSeq] using congrArg (fun h => h.inner x v w) hassoc.symm
    _ = (ballPullbackMetric (PartialDiffeomorph.trans (I := I) Φ Θ)
          U htrans (g ((j + 1) + b))).inner x v w :=
      congrArg (fun h => h.inner x v w) hcongr
    _ = (nestedBallPullback Φ Θ U (hU 1) hnext (g ((j + 1) + b))).inner x v w :=
      congrArg (fun h => h.inner x v w) htransMetric
    _ = (chainPullbackSeq (I := I) Ψ g V hV b).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w) := by
      change (nestedBallPullback Φ Θ U (hU 1) hnext (g ((j + 1) + b))).inner x v w =
        (ballPullbackMetric Θ V (hV b) (g ((j + 1) + b))).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w)
      unfold nestedBallPullback
      rw [Diffeomorph.pullbackMetric_inner, ballPullback_inner, ballPullback_inner,
        PartialDiffeomorph.opensDiffeo_mfderiv,
        PartialDiffeomorph.opensDiffeo_mfderiv,
        PartialDiffeomorph.opensMap_mfderiv,
        PartialDiffeomorph.opensMap_mfderiv]
      rfl
    _ = _ := rfl



noncomputable def chainBallSystem
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1)))) ) :
    SmoothSeqSystem I (fun n => U n) :=
  SmoothSeqSystem.ofSucc
    (fun n => PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_isOpenEmb
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_contMDiff
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n))
    (fun n => PartialDiffeomorph.opensMap_inv_mdiff
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n))



omit [FiniteDimensional ℝ E] [CompleteSpace E] [∀ (j : ℕ), SigmaCompactSpace (M j)] [∀ (j : ℕ), T2Space (M j)] in
theorem chainMetricCocycle
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    [∀ n, SigmaCompactSpace (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1)))) )
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hstep : ∀ n,
      let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
      ∀ (x : U n) (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w)) :
    (chainBallSystem (I := I) j₀ U Ψ hU hmap).MetricCocycle gInf := by
  apply SmoothSeqSystem.MetricCocycle.ofSucc
  intro n x v w
  have hF : (chainBallSystem (I := I) j₀ U Ψ hU hmap).toSeqSystem.F
      (Nat.le_succ n) = PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n) := by
    unfold chainBallSystem
    apply SmoothSeqSystem.ofSucc_F_succ
  rw [hF]
  exact (hstep n x v w).symm



def chainAmbientSeq
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j)) :
    PointedRiemannianSeq (I := I) where
  obj n :=
    { M := M (j₀ + n)
      basepoint := (S.toSeqSystem.F (Nat.zero_le n) O₀ : M (j₀ + n))
      metric := g (j₀ + n) }



noncomputable def chainAmbientMaps
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    [∀ n, SigmaCompactSpace (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hgInf : S.MetricCocycle gInf) :
    PointedRiemannianCGMaps (I := I)
      (chainAmbientSeq (I := I) j₀ U S O₀ g)
      (limitPointedCoc S O₀ gInf hgInf) id where
  partialDiffeomorph n := by
    change PartialDiffeomorph I I S.toSeqSystem.Lim (M (j₀ + n))
      (∞ : WithTop ℕ∞)
    exact PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl
  source_exhausts := rangeExhausts S
  base_mem n := by
    change S.toSeqSystem.incl 0 O₀ ∈ Set.range (S.toSeqSystem.incl n)
    exact
      ⟨S.toSeqSystem.F (Nat.zero_le n) O₀,
        S.toSeqSystem.incl_comp (Nat.zero_le n) O₀⟩
  basepoint_map n := by
    exact congrArg Subtype.val (S.invIncl_incl_le (Nat.zero_le n) O₀)

section ApproxData

open Bundle

variable [I.Boundaryless]
variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
include I in

omit [FiniteDimensional ℝ E] [CompleteSpace E] [∀ (j : ℕ), IsManifold I ∞ (M j)] [∀ (j : ℕ), SigmaCompactSpace (M j)] [∀ (j : ℕ), T2Space (M j)] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailBall_preconn (b : ∀ j, M j) (j₀ n : ℕ) :
    PreconnectedSpace (tailBallOpen b j₀ n) := by
  have hR : 0 < (2 : ℝ) ^ n := by positivity
  have hpath : IsPathConnected
      (Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ n) : Set (M (j₀ + n))) := by
    refine ⟨b (j₀ + n), Metric.mem_ball_self hR, ?_⟩
    intro y hy
    have hy' : Manifold.riemannianEDist I (b (j₀ + n)) y <
        ENNReal.ofReal ((2 : ℝ) ^ n) := by
      rw [← IsRiemannianManifold.out (I := I) (b (j₀ + n)) y, edist_dist,
        ENNReal.ofReal_lt_ofReal_iff hR]
      simpa only [Metric.mem_ball, dist_comm] using hy
    obtain ⟨γ, hγ0, hγ1, hγC, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hy'
    refine JoinedIn.ofLine hγC.continuousOn hγ0 hγ1 ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, ← ENNReal.ofReal_lt_ofReal_iff hR, ← edist_dist,
      edist_comm, IsRiemannianManifold.out (I := I) (b (j₀ + n)) (γ t)]
    calc
      Manifold.riemannianEDist I (b (j₀ + n)) (γ t) ≤
          Manifold.pathELength I γ 0 t := by
        exact Manifold.riemannianEDist_le_pathELength
          (hγC.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
      _ ≤ Manifold.pathELength I γ 0 1 :=
        Manifold.pathELength_mono le_rfl ht.2
      _ < ENNReal.ofReal ((2 : ℝ) ^ n) := hγlen
  letI : PathConnectedSpace (tailBallOpen b j₀ n) := by
    exact (isPathConnected_iff_pathConnectedSpace
      (F := (tailBallOpen b j₀ n : Set (M (j₀ + n))))).mp
        (by simpa only [tailBallOpen] using hpath)
  infer_instance

omit [I.Boundaryless] [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)]
  [NeZero (Module.finrank ℝ E)] in

omit [CompleteSpace E] [∀ (j : ℕ), SigmaCompactSpace (M j)] [∀ (j : ℕ), T2Space (M j)] in
theorem speed_ge_of_c0 {j : ℕ}
    (P : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M j) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I (M j)) {ε : ℝ} {x : M j}
    (hc0 : metricTensorErrorNorm (I := I) P g x ≤ ε)
    (v : TangentSpace I x) :
    (1 - ε) * g.inner x v v ≤ P x (fun _ => v) := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) g x
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I)
    g x 2 basis (fun i k => hON i k)
    (P x - Tensor0SBundle.metricTensorField (I := I) g x)
    (fun _ => v)
  have hval : (P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v) =
      P x (fun _ => v) - g.inner x v v := by
    simp [Tensor0SBundle.metricTensorField_apply]
  have hnn : 0 ≤ g.inner x v v := metricInner_nonneg (I := I) g x v
  have hprod : (∏ _a : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt hnn]
  have habs : |P x (fun _ => v) - g.inner x v v| ≤ ε * g.inner x v v := by
    unfold metricTensorErrorNorm at hc0
    calc
      |P x (fun _ => v) - g.inner x v v| =
          |(P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)| := by
            rw [hval]
      _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
            (P x - Tensor0SBundle.metricTensorField (I := I) g x)) *
          ∏ _a : Fin 2, Real.sqrt (g.inner x v v) := hCS
      _ ≤ ε * g.inner x v v := by
        rw [hprod]
        exact mul_le_mul_of_nonneg_right hc0 hnn
  nlinarith [abs_le.mp habs]

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


omit [NeZero (Module.finrank ℝ E)] in
theorem ballPullback_covNorm {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (q : ℕ) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q (ballPullbackMetric Φ U hU g)
        (gRef.restrictOpen (I := I) U) x =
      tensor02CovDerivNormWith (I := I) q D.pullback gRef gRef (x : M j) := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let hB := ballPullbackMetric Φ U hU g
  have hbase : ∀ (y : U) (slots : Fin 2 → TangentSpace I y),
      Tensor0SBundle.metricTensorField (I := I) hB y slots =
        D.pullback (y : M j) slots := by
    intro y slots
    rw [Tensor0SBundle.metricTensorField_apply, ballPullback_inner]
    exact (D.pullback_apply (y : M j) (hUK y.2) slots).symm
  have htower := covDerivOfField_restrictOpen (I := I) gRef U
    (Tensor0SBundle.metricTensorField (I := I) hB) D.pullback hbase q x
  have hT : metricCovDeriv (I := I) hB (gRef.restrictOpen (I := I) U) q x =
      covDerivOfField (I := I) gRef D.pullback q (x : M j) := by
    rw [metricCovDeriv_eq_covDerivOfField]
    exact ContinuousMultilinearMap.ext htower
  unfold metricCovDerivNorm tensor02CovDerivNormWith
  rw [tensor02_eq_covDOF, hT]
  congr 1
  exact normSq0S_restrictOpen_apply (I := I) gRef U (q + 2) x _

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


omit [NeZero (Module.finrank ℝ E)] in
theorem ballPullback_cov_le {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p q : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q (ballPullbackMetric Φ U hU g)
      (gRef.restrictOpen (I := I) U) x ≤ ε := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  rw [ballPullback_covNorm Φ U hU hUK gRef g D q x]
  exact D.cov_deriv_small q hq1 hqp (x : M j) (hUK x.2)

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


theorem prefixTail_cov_le {j l m : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I (M l) (M m) (∞ : WithTop ℕ∞))
    {K : Set (M l)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hnext : (Φ : M j → M l) '' (U : Set (M j)) ⊆ Θ.source)
    (hUK : (Φ : M j → M l) '' (U : Set (M j)) ⊆ K)
    (gMid : SmoothRiemannianMetric I (M l)) (g : SmoothRiemannianMetric I (M m))
    {ε : ℝ} {p q : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Θ : M l → M m) gMid g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q
        (ballPullbackMetric (PartialDiffeomorph.trans (I := I) Φ Θ) U
          (ballTransSource Φ Θ U hU hnext) g)
        (ballPullbackMetric Φ U hU gMid) x ≤ ε := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  rw [ballPullback_trans]
  let W : Opens (M l) :=
    ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  change metricCovDerivNorm (I := I) q
      (Diffeomorph.pullbackMetric (I := I) (ballPullbackMetric Θ W hnext g) F)
      (Diffeomorph.pullbackMetric (I := I) (gMid.restrictOpen (I := I) W) F) x ≤ ε
  rw [metricCovDerivNorm_pullback (I := I)]
  exact ballPullback_cov_le Θ W hnext hUK gMid g D hq1 hqp (F x)

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in

theorem chainPrefix_cov_le
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    {j a b : ℕ} {K : Set (M (j + a))} (U : Opens (M j))
    (hpre : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j a).source)
    (hnext : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ (j + a) b).source)
    (hUK : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ K)
    (hfull : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (gMid : SmoothRiemannianMetric I (M (j + a)))
    (g : SmoothRiemannianMetric I (M ((j + a) + b)))
    {ε : ℝ} {p q : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p
      (chainComp (I := I) (Mf := M) Ψ (j + a) b : M (j + a) → M ((j + a) + b))
      gMid g)
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) q
        (ballPullbackMetric (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hfull g)
        (ballPullbackMetric (chainComp (I := I) (Mf := M) Ψ j a) U hpre gMid) x ≤ ε := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let Φ := chainComp (I := I) (Mf := M) Ψ j a
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + a) b
  let A := chainCompAssoc (I := I) (Mf := M) Ψ j a b
  have htrans : (U : Set (M j)) ⊆ (PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    ballTransSource Φ Θ U hpre hnext
  rw [ballPullback_congr A (PartialDiffeomorph.trans (I := I) Φ Θ) U hfull htrans g
    (chainCompAssoc_eq (I := I) (Mf := M) Ψ j a b)]
  exact prefixTail_cov_le Φ Θ U hpre hnext hUK gMid g D hq1 hqp x

omit [I.Boundaryless] [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in

theorem ballPullback_lower {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (x : U) (v : TangentSpace I x) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    (1 - ε) * (gRef.restrictOpen (I := I) U).inner x v v ≤
      (ballPullbackMetric Φ U hU g).inner x v v := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  calc
    (1 - ε) * (gRef.restrictOpen (I := I) U).inner x v v =
        (1 - ε) * gRef.inner (x : M j) v v := rfl
    _ ≤ D.pullback (x : M j) (fun _ => v) :=
      speed_ge_of_c0 D.pullback gRef (D.c0_small (x : M j) (hUK x.2)) v
    _ = (ballPullbackMetric Φ U hU g).inner x v v := by
      rw [D.pullback_apply (x : M j) (hUK x.2), ballPullback_inner]

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem ballPullback_upper {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (x : U) (v : TangentSpace I x) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    (ballPullbackMetric Φ U hU g).inner x v v ≤
      (1 + ε) * (gRef.restrictOpen (I := I) U).inner x v v := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  calc
    (ballPullbackMetric Φ U hU g).inner x v v =
        D.pullback (x : M j) (fun _ => v) := by
      rw [D.pullback_apply (x : M j) (hUK x.2), ballPullback_inner]
    _ ≤ (1 + ε) * gRef.inner (x : M j) v v :=
      speed_le_of_c0 (I := I) D.pullback gRef (D.c0_small (x : M j) (hUK x.2)) v
    _ = (1 + ε) * (gRef.restrictOpen (I := I) U).inner x v v := rfl

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem ballPullback_zero_le {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (hε : ε ≤ 1 / 2) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) 0 (ballPullbackMetric Φ U hU g)
        (gRef.restrictOpen (I := I) U) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  apply covNorm0_le (I := I) (ballPullbackMetric Φ U hU g)
    (gRef.restrictOpen (I := I) U) x (C := 2) (by norm_num)
  intro v
  have hl := ballPullback_lower Φ U hU hUK gRef g D x v
  have hu := ballPullback_upper Φ U hU hUK gRef g D x v
  have hnn : 0 ≤ (gRef.restrictOpen (I := I) U).inner x v v :=
    metricInner_nonneg (I := I) (gRef.restrictOpen (I := I) U) x v
  constructor
  · have hu' : (ballPullbackMetric Φ U hU g).inner x v v ≤
        (3 / 2 : ℝ) * (gRef.restrictOpen (I := I) U).inner x v v := by
      nlinarith
    calc
      (2 : ℝ)⁻¹ * (ballPullbackMetric Φ U hU g).inner x v v =
          (1 / 2 : ℝ) * (ballPullbackMetric Φ U hU g).inner x v v := by norm_num
      _ ≤ (1 / 2 : ℝ) * ((3 / 2 : ℝ) *
          (gRef.restrictOpen (I := I) U).inner x v v) :=
        mul_le_mul_of_nonneg_left hu' (by norm_num)
      _ ≤ (gRef.restrictOpen (I := I) U).inner x v v := by nlinarith
  · nlinarith

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


omit [NeZero (Module.finrank ℝ E)] in
theorem pullbackDiff_le {j l : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    {K : Set (M j)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hUK : (U : Set (M j)) ⊆ K)
    (gRef : SmoothRiemannianMetric I (M j)) (g : SmoothRiemannianMetric I (M l))
    {ε : ℝ} {p q : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Φ : M j → M l) gRef g)
    (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricDerivNorm (I := I) q (ballPullbackMetric Φ U hU g)
      (gRef.restrictOpen (I := I) U) (gRef.restrictOpen (I := I) U) x ≤ ε := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let hB := ballPullbackMetric Φ U hU g
  let gU := gRef.restrictOpen (I := I) U
  by_cases hq0 : q = 0
  · subst q
    have hpb : Tensor0SBundle.metricTensorField (I := I) hB x = D.pullback (x : M j) := by
      apply ContinuousMultilinearMap.ext
      intro slots
      rw [Tensor0SBundle.metricTensorField_apply, ballPullback_inner]
      exact (D.pullback_apply (x : M j) (hUK x.2) slots).symm
    have href : Tensor0SBundle.metricTensorField (I := I) gU x =
        Tensor0SBundle.metricTensorField (I := I) gRef (x : M j) := by
      apply ContinuousMultilinearMap.ext
      intro slots
      change gU.inner x (slots 0) (slots 1) =
        gRef.inner (x : M j) (slots 0) (slots 1)
      rfl
    unfold metricDerivNorm metricDiffCovDerivAt
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) gU x 2
      (Tensor0SBundle.metricTensorField (I := I) hB x -
        Tensor0SBundle.metricTensorField (I := I) gU x)) ≤ ε
    rw [hpb, href, normSq0S_restrictOpen_apply (I := I)]
    exact D.c0_small (x : M j) (hUK x.2)
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hzero : metricCovDeriv (I := I) gU gU q x = 0 := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      rw [metricCovDeriv_eq_covDerivOfField, covDerivOfField_eq_iterCov,
        iterCov_metric_zero]
      exact DFunLike.congr_fun (MultilinearSection.domDomCongr_zero
        (IB := I) (F := E) (n := (∞ : WithTop ℕ∞)) (acEquiv r.succ)) x
    unfold metricDerivNorm metricDiffCovDerivAt
    rw [hzero, sub_zero]
    exact ballPullback_cov_le Φ U hU hUK gRef g D hq1 hqp x

omit [NeZero (Module.finrank ℝ E)] in


omit [I.Boundaryless] in
theorem limitDiff_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (gSeq : ℕ → SmoothRiemannianMetric I N)
    (gInf g₀ gRef : SmoothRiemannianMetric I N)
    (hconv : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef)
    {a : ℕ} {x : N} {δ : ℝ}
    (hbound : ∀ k, metricDerivNorm (I := I) a (gSeq k) g₀ gRef x ≤ δ) :
    metricDerivNorm (I := I) a gInf g₀ gRef x ≤ δ := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨k₀, hk₀⟩ := hconv {x} isCompact_singleton a η hη
  have hpoint : metricDerivNorm (I := I) a (gSeq k₀) gInf gRef x < η :=
    lt_of_le_of_lt
      (derivNorm_le_sup (I := I) isCompact_singleton le_rfl
        (gSeq k₀) gInf gRef (Set.mem_singleton x))
      (hk₀ k₀ le_rfl)
  have hsymm : metricDerivNorm (I := I) a gInf (gSeq k₀) gRef x =
      metricDerivNorm (I := I) a (gSeq k₀) gInf gRef x := by
    have hneg : metricDiffCovDerivAt (I := I) a gInf (gSeq k₀) gRef x =
        -metricDiffCovDerivAt (I := I) a (gSeq k₀) gInf gRef x := by
      simp [metricDiffCovDerivAt]
    rw [metricDerivNorm, metricDerivNorm, hneg, normSq0S_neg]
  calc
    metricDerivNorm (I := I) a gInf g₀ gRef x ≤
        metricDerivNorm (I := I) a gInf (gSeq k₀) gRef x +
          metricDerivNorm (I := I) a (gSeq k₀) g₀ gRef x :=
      metricDerivNorm_triangle (I := I) a gInf (gSeq k₀) g₀ gRef x
    _ ≤ δ + η := by rw [hsymm]; linarith [hbound k₀]

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


omit [NeZero (Module.finrank ℝ E)] in
theorem chainLimit_base_le
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ}
    (U : Opens (M j))
    (hUball : (U : Set (M j)) = Metric.ball (b j) ((2 : ℝ) ^ j))
    (hU : ∀ l, (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j l).source)
    {δ : ℝ} {p : ℕ}
    (D : ∀ l, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
      (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))
    (ρ : ℕ → ℕ)
    (gInf : SmoothRiemannianMetric I U)
    (hconv :
      letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      MetricCInfConvOnCompacts (I := I)
        (fun k => chainPullbackSeq (I := I) Ψ g U hU (ρ k)) gInf
        ((g j).restrictOpen (I := I) U))
    {q : ℕ} (hqp : q ≤ p) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricDerivNorm (I := I) q gInf ((g j).restrictOpen (I := I) U)
      ((g j).restrictOpen (I := I) U) x ≤ δ := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  apply limitDiff_le (I := I)
    (fun k => chainPullbackSeq (I := I) Ψ g U hU (ρ k)) gInf
    ((g j).restrictOpen (I := I) U) ((g j).restrictOpen (I := I) U) hconv
  intro k
  have hUK : (U : Set (M j)) ⊆ Metric.closedBall (b j) ((2 : ℝ) ^ j) := by
    intro y hy
    rw [hUball] at hy
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le
  simpa only [chainPullbackSeq] using
    pullbackDiff_le (I := I)
      (chainComp (I := I) (Mf := M) Ψ j (ρ k)) U (hU (ρ k)) hUK
      (g j) (g (j + ρ k)) (D (ρ k)).forward hqp x

omit [NeZero (Module.finrank ℝ E)] in


omit [I.Boundaryless] in
theorem diffNorm_change_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {u : Set N} (hu : IsOpen u)
    (A B gInf gBase : SmoothRiemannianMetric I N)
    (p r : ℕ) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gBase.inner x v v ≤ gInf.inner x v v ∧
        gInf.inner x v v ≤ (1 + eps) * gBase.inner x v v)
    (hInf : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      metricDerivNorm (I := I) j gInf gBase gBase x ≤ eps)
    (x : N) (hx : x ∈ u) (hr0 : 0 < r) (hrp : r ≤ p) :
    metricDerivNorm (I := I) r A B gInf x ≤
      Real.sqrt ((1 + eps) ^ (2 + r)) *
        (metricDerivNorm (I := I) r A B gBase x +
          eps * lemma45CorConst (E := E) 2 p * ∑ k ∈ Finset.range r,
            metricDerivNorm (I := I) k A B gBase x) := by
  classical
  obtain ⟨bBase, hBaseON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) gBase x
  have hBaseInv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gBase x bBase
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) gBase bBase hBaseON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  obtain ⟨bInf, hInfON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) gInf x
  have hInfInv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gInf x bInf
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) gInf bInf hInfON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  have hInfIter : ∀ y ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase y (2 + j)
        (iterCov (I := I) gBase 2
          (Tensor0SBundle.metricTensorField (I := I) gInf) j y)) ≤ eps := by
    intro y hy j hj1 hjp
    obtain ⟨b, hON⟩ :=
      DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis (I := I) gBase y
    have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gBase y b
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I y)))) := by
      have h := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
        (I := I) gBase b hON
      intro i k
      simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i k
    have heq := metricDerivNorm_eq_iterCov (I := I) gInf gBase gBase j b hinv
    have hiter : iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) gInf -
          Tensor0SBundle.metricTensorField (I := I) gBase) j y =
        iterCov (I := I) gBase 2
          (Tensor0SBundle.metricTensorField (I := I) gInf) j y := by
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj1
      rw [show 1 + j' = j' + 1 by omega, iterCov_sub, iterCov_metric_zero, sub_zero]
    rw [hiter] at heq
    rw [← heq]
    exact hInf y hy j hj1 hjp
  let T : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2 :=
    Tensor0SBundle.metricTensorField (I := I) A -
      Tensor0SBundle.metricTensorField (I := I) B
  have hcor := lemma45_corII_bound (I := I) hu gInf gBase T
    p eps heps0 heps1 hequiv hInfIter x hx r hr0 hrp
  dsimp only [T] at hcor
  have hleft := metricDerivNorm_eq_iterCov (I := I) A B gInf r bInf hInfInv
  have hright : ∀ k, Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (2 + k)
      (iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) A -
          Tensor0SBundle.metricTensorField (I := I) B) k x)) =
      metricDerivNorm (I := I) k A B gBase x :=
    fun k => (metricDerivNorm_eq_iterCov (I := I) A B gBase k bBase hBaseInv).symm
  rw [← hleft] at hcor
  simp_rw [hright] at hcor
  exact hcor



noncomputable def limitRefFactor (p : ℕ) : ℝ :=
  4 + ∑ r ∈ Finset.range (p + 1),
    Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * lemma45CorConst (E := E) 2 p * (r : ℝ))

omit [NeZero (Module.finrank ℝ E)] in

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem limitRefFactor_pos (p : ℕ) : 0 < limitRefFactor (E := E) p := by
  have hterm : ∀ r : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * lemma45CorConst (E := E) 2 p * (r : ℝ)) := by
    intro r
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := corConst_nonneg (E := E) 2 p
    positivity
  have hsum : 0 ≤ ∑ r ∈ Finset.range (p + 1),
      Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * lemma45CorConst (E := E) 2 p * (r : ℝ)) := by
    exact Finset.sum_nonneg fun r _ => hterm r
  unfold limitRefFactor
  linarith

omit [NeZero (Module.finrank ℝ E)] in

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem four_le_refFactor (p : ℕ) : 4 ≤ limitRefFactor (E := E) p := by
  have hterm : ∀ r : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * lemma45CorConst (E := E) 2 p * (r : ℝ)) := by
    intro r
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := corConst_nonneg (E := E) 2 p
    positivity
  have hsum : 0 ≤ ∑ r ∈ Finset.range (p + 1),
      Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * lemma45CorConst (E := E) 2 p * (r : ℝ)) := by
    exact Finset.sum_nonneg fun r _ => hterm r
  unfold limitRefFactor
  linarith

omit [NeZero (Module.finrank ℝ E)] in


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem refTerm_le_factor (p r : ℕ) (hrp : r ≤ p) :
    Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * lemma45CorConst (E := E) 2 p * (r : ℝ)) ≤
      limitRefFactor (E := E) p := by
  have hterm : ∀ q : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + q)) *
      (2 + 2 * lemma45CorConst (E := E) 2 p * (q : ℝ)) := by
    intro q
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := corConst_nonneg (E := E) 2 p
    positivity
  have hmem : r ∈ Finset.range (p + 1) := by simp only [Finset.mem_range]; omega
  have hsum : Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * lemma45CorConst (E := E) 2 p * (r : ℝ)) ≤
      ∑ q ∈ Finset.range (p + 1), Real.sqrt ((2 : ℝ) ^ (2 + q)) *
        (2 + 2 * lemma45CorConst (E := E) 2 p * (q : ℝ)) := by
    exact Finset.single_le_sum (fun q _ => hterm q) hmem
  unfold limitRefFactor
  linarith

omit [NeZero (Module.finrank ℝ E)] in


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem exists_refDelta (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (Module.finrank ℝ E : ℝ) * δ ≤ 1 / 2 ∧
      limitRefFactor (E := E) p * δ ≤ ε := by
  let n : ℝ := Module.finrank ℝ E
  let F : ℝ := limitRefFactor (E := E) p
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hn1 : 0 < n + 1 := by linarith
  have hF : 0 < F := by exact limitRefFactor_pos (E := E) p
  let δ : ℝ := min (1 / (4 * (n + 1))) (ε / (2 * F))
  have hleft : 0 < 1 / (4 * (n + 1)) := by positivity
  have hright : 0 < ε / (2 * F) := by positivity
  have hδpos : 0 < δ := by simpa only [δ] using lt_min hleft hright
  have hδleft : δ ≤ 1 / (4 * (n + 1)) := min_le_left _ _
  have hδright : δ ≤ ε / (2 * F) := min_le_right _ _
  refine ⟨δ, hδpos, ?_, ?_, ?_⟩
  · have hden_ge : (4 : ℝ) ≤ 4 * (n + 1) := by nlinarith
    have hinv : 1 / (4 * (n + 1)) ≤ (1 : ℝ) / 4 :=
      one_div_le_one_div_of_le (by norm_num) hden_ge
    nlinarith
  · change n * δ ≤ 1 / 2
    have hmul := mul_le_mul_of_nonneg_left hδleft hn
    have hden : 0 < 4 * (n + 1) := by positivity
    have hfrac : n * (1 / (4 * (n + 1))) ≤ (1 : ℝ) / 4 := by
      calc
        n * (1 / (4 * (n + 1))) = n / (4 * (n + 1)) := by ring
        _ ≤ (1 : ℝ) / 4 := (div_le_iff₀ hden).2 (by nlinarith)
    linarith
  · change F * δ ≤ ε
    calc
      F * δ ≤ F * (ε / (2 * F)) := mul_le_mul_of_nonneg_left hδright hF.le
      _ = ε / 2 := by field_simp [ne_of_gt hF]
      _ ≤ ε := by linarith

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in



omit [I.Boundaryless] in
theorem diffNorm_limit_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {u : Set N} (hu : IsOpen u)
    (A gInf gBase : SmoothRiemannianMetric I N)
    (p : ℕ) {δ ε : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδdim : (Module.finrank ℝ E : ℝ) * δ ≤ 1 / 2)
    (hδbudget : limitRefFactor (E := E) p * δ ≤ ε)
    (hA : ∀ x ∈ u, ∀ q, q ≤ p →
      metricDerivNorm (I := I) q A gBase gBase x ≤ δ)
    (hInf : ∀ x ∈ u, ∀ q, q ≤ p →
      metricDerivNorm (I := I) q gInf gBase gBase x ≤ δ)
    (x : N) (hx : x ∈ u) (q : ℕ) (hqp : q ≤ p) :
    metricDerivNorm (I := I) q A gInf gInf x ≤ ε := by
  classical
  have hBaseNN (y : N) (v : TangentSpace I y) : 0 ≤ gBase.inner y v v := by
    by_cases hv : v = 0
    · subst hv
      simp
    · exact (gBase.pos y v hv).le
  have hnorm0 (y : N) (hy : y ∈ u) : (Module.finrank ℝ E : ℝ) *
      metricDerivNorm (I := I) 0 gInf gBase gBase y ≤ 1 / 2 := by
    have hn : (0 : ℝ) ≤ Module.finrank ℝ E := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left (hInf y hy 0 (Nat.zero_le p)) hn) hδdim
  have hequiv : ∀ y ∈ u, ∀ v : TangentSpace I y,
      ((2 : ℝ)⁻¹ * gBase.inner y v v ≤ gInf.inner y v v) ∧
        gInf.inner y v v ≤ 2 * gBase.inner y v v := by
    intro y hy v
    have hquad := metricQuadFormDiff_le_metricDerivNorm
      (I := I) gInf gBase gBase y v
    have habs : |gInf.inner y v v - gBase.inner y v v| ≤
        (1 / 2 : ℝ) * gBase.inner y v v :=
      le_trans hquad (mul_le_mul_of_nonneg_right (hnorm0 y hy) (hBaseNN y v))
    rw [abs_le] at habs
    constructor <;> norm_num at habs ⊢ <;> linarith
  have hsymm (a : ℕ) : metricDerivNorm (I := I) a gBase gInf gBase x =
      metricDerivNorm (I := I) a gInf gBase gBase x := by
    have hneg : metricDiffCovDerivAt (I := I) a gBase gInf gBase x =
        -metricDiffCovDerivAt (I := I) a gInf gBase gBase x := by
      simp [metricDiffCovDerivAt]
    rw [metricDerivNorm, metricDerivNorm, hneg, normSq0S_neg]
  have hbase (a : ℕ) (hap : a ≤ p) :
      metricDerivNorm (I := I) a A gInf gBase x ≤ 2 * δ := by
    calc
      metricDerivNorm (I := I) a A gInf gBase x ≤
          metricDerivNorm (I := I) a A gBase gBase x +
            metricDerivNorm (I := I) a gBase gInf gBase x :=
        metricDerivNorm_triangle (I := I) a A gBase gInf gBase x
      _ ≤ δ + δ := by rw [hsymm]; exact add_le_add (hA x hx a hap) (hInf x hx a hap)
      _ = 2 * δ := by ring
  by_cases hq0 : q = 0
  · subst q
    have hzero := diffNorm_zero_change (I := I) A gInf gInf gBase x
      (C := (2 : ℝ)) (by norm_num) (hequiv x hx)
    norm_num at hzero
    calc
      metricDerivNorm (I := I) 0 A gInf gInf x ≤
          2 * metricDerivNorm (I := I) 0 A gInf gBase x := hzero
      _ ≤ 4 * δ := by nlinarith [hbase 0 (Nat.zero_le p)]
      _ ≤ limitRefFactor (E := E) p * δ :=
        mul_le_mul_of_nonneg_right (four_le_refFactor (E := E) p) hδ0
      _ ≤ ε := hδbudget
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hInf1 : ∀ y ∈ u, ∀ j, 1 ≤ j → j ≤ p →
        metricDerivNorm (I := I) j gInf gBase gBase y ≤ 1 := by
      intro y hy j _ hjp
      exact le_trans (hInf y hy j hjp) hδ1
    have hequiv1 : ∀ y ∈ u, ∀ v : TangentSpace I y,
        ((1 : ℝ) + 1)⁻¹ * gBase.inner y v v ≤ gInf.inner y v v ∧
          gInf.inner y v v ≤ ((1 : ℝ) + 1) * gBase.inner y v v := by
      intro y hy v
      norm_num
      simpa only [one_div] using hequiv y hy v
    have hchange := diffNorm_change_le (I := I) hu A gInf gInf gBase p q 1
      (by norm_num) (by norm_num) hequiv1 hInf1 x hx hqpos hqp
    norm_num at hchange
    have hsum : ∑ k ∈ Finset.range q,
        metricDerivNorm (I := I) k A gInf gBase x ≤ (q : ℝ) * (2 * δ) := by
      calc
        (∑ k ∈ Finset.range q, metricDerivNorm (I := I) k A gInf gBase x) ≤
            ∑ _k ∈ Finset.range q, 2 * δ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hbase k (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hqp)
        _ = (q : ℝ) * (2 * δ) := by simp
    have hC : 0 ≤ lemma45CorConst (E := E) 2 p := corConst_nonneg (E := E) 2 p
    have hinside : metricDerivNorm (I := I) q A gInf gBase x +
          lemma45CorConst (E := E) 2 p *
            (∑ k ∈ Finset.range q, metricDerivNorm (I := I) k A gInf gBase x) ≤
        (2 + 2 * lemma45CorConst (E := E) 2 p * (q : ℝ)) * δ := by
      calc
        _ ≤ 2 * δ + lemma45CorConst (E := E) 2 p * ((q : ℝ) * (2 * δ)) :=
          add_le_add (hbase q hqp) (mul_le_mul_of_nonneg_left hsum hC)
        _ = _ := by ring
    calc
      metricDerivNorm (I := I) q A gInf gInf x ≤
          Real.sqrt ((2 : ℝ) ^ (2 + q)) *
            (metricDerivNorm (I := I) q A gInf gBase x +
              lemma45CorConst (E := E) 2 p *
                (∑ k ∈ Finset.range q,
                  metricDerivNorm (I := I) k A gInf gBase x)) := hchange
      _ ≤ Real.sqrt ((2 : ℝ) ^ (2 + q)) *
          ((2 + 2 * lemma45CorConst (E := E) 2 p * (q : ℝ)) * δ) :=
        mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg _)
      _ = (Real.sqrt ((2 : ℝ) ^ (2 + q)) *
          (2 + 2 * lemma45CorConst (E := E) 2 p * (q : ℝ))) * δ := by ring
      _ ≤ limitRefFactor (E := E) p * δ :=
        mul_le_mul_of_nonneg_right (refTerm_le_factor (E := E) p q hqp) hδ0
      _ ≤ ε := hδbudget

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in

theorem prefixTail_zero_le {j l m : ℕ}
    (Φ : PartialDiffeomorph I I (M j) (M l) (∞ : WithTop ℕ∞))
    (Θ : PartialDiffeomorph I I (M l) (M m) (∞ : WithTop ℕ∞))
    {K : Set (M l)} (U : Opens (M j)) (hU : (U : Set (M j)) ⊆ Φ.source)
    (hnext : (Φ : M j → M l) '' (U : Set (M j)) ⊆ Θ.source)
    (hUK : (Φ : M j → M l) '' (U : Set (M j)) ⊆ K)
    (gMid : SmoothRiemannianMetric I (M l)) (g : SmoothRiemannianMetric I (M m))
    {ε : ℝ} {p : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p (Θ : M l → M m) gMid g)
    (hε : ε ≤ 1 / 2) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) 0
        (ballPullbackMetric (PartialDiffeomorph.trans (I := I) Φ Θ) U
          (ballTransSource Φ Θ U hU hnext) g)
        (ballPullbackMetric Φ U hU gMid) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  rw [ballPullback_trans]
  let W : Opens (M l) :=
    ⟨(Φ : M j → M l) '' (U : Set (M j)), image_opens_isOpen Φ hU⟩
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let F : Diffeomorph I I U W (∞ : WithTop ℕ∞) :=
    PartialDiffeomorph.toOpensDiffeo Φ hU
  change metricCovDerivNorm (I := I) 0
      (Diffeomorph.pullbackMetric (I := I) (ballPullbackMetric Θ W hnext g) F)
      (Diffeomorph.pullbackMetric (I := I) (gMid.restrictOpen (I := I) W) F) x ≤ _
  rw [metricCovDerivNorm_pullback (I := I)]
  exact ballPullback_zero_le Θ W hnext hUK gMid g D hε (F x)

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in

theorem chainPrefix_zero_le
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    {j a b : ℕ} {K : Set (M (j + a))} (U : Opens (M j))
    (hpre : (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ j a).source)
    (hnext : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ (chainComp (I := I) (Mf := M) Ψ (j + a) b).source)
    (hUK : (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
      (U : Set (M j)) ⊆ K)
    (hfull : (U : Set (M j)) ⊆ (chainCompAssoc (I := I) (Mf := M) Ψ j a b).source)
    (gMid : SmoothRiemannianMetric I (M (j + a)))
    (g : SmoothRiemannianMetric I (M ((j + a) + b)))
    {ε : ℝ} {p : ℕ}
    (D : PreApproxIsoDataOn (I := I) K ε p
      (chainComp (I := I) (Mf := M) Ψ (j + a) b : M (j + a) → M ((j + a) + b))
      gMid g)
    (hε : ε ≤ 1 / 2) (x : U) :
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    metricCovDerivNorm (I := I) 0
        (ballPullbackMetric (chainCompAssoc (I := I) (Mf := M) Ψ j a b) U hfull g)
        (ballPullbackMetric (chainComp (I := I) (Mf := M) Ψ j a) U hpre gMid) x ≤
      2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let Φ := chainComp (I := I) (Mf := M) Ψ j a
  let Θ := chainComp (I := I) (Mf := M) Ψ (j + a) b
  let A := chainCompAssoc (I := I) (Mf := M) Ψ j a b
  have htrans : (U : Set (M j)) ⊆ (PartialDiffeomorph.trans (I := I) Φ Θ).source :=
    ballTransSource Φ Θ U hpre hnext
  rw [ballPullback_congr A (PartialDiffeomorph.trans (I := I) Φ Θ) U hfull htrans g
    (chainCompAssoc_eq (I := I) (Mf := M) Ψ j a b)]
  exact prefixTail_zero_le Φ Θ U hpre hnext hUK gMid g D hε x

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem chain_image_open
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j a : ℕ} (ha : 1 ≤ a)
    (D : BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a) (g j) (g (j + a))) :
    (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        Metric.ball (b j) ((2 : ℝ) ^ j) ⊆
      Metric.ball (b (j + a)) ((2 : ℝ) ^ (j + a)) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ a := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ j < (2 : ℝ) ^ (j + a) := by
    rw [pow_add]
    calc
      Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ j < 2 * (2 : ℝ) ^ j :=
        mul_lt_mul_of_pos_right hsqrt hr
      _ ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ a := by
        rw [mul_comm 2]
        exact mul_le_mul_of_nonneg_left hpow hr.le
  have hdata : PreApproxIsoDataOn (I := I)
      (Metric.closedEBall (b j) (ENNReal.ofReal ((2 : ℝ) ^ j))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) (g j) (g (j + a)) := by
    rw [Metric.closedEBall_ofReal hr.le]
    exact D.forward
  have hsource : Metric.closedEBall (b j) (ENNReal.ofReal ((2 : ℝ) ^ j)) ⊆
      (chainComp (I := I) (Mf := M) Ψ j a).source := by
    rw [Metric.closedEBall_ofReal hr.le]
    exact D.source_sub
  have himg := data_image_metric_ball (I := I)
    (chainComp (I := I) (Mf := M) Ψ j a) (hnorm j) (hnorm (j + a))
    hr le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hdata hsource
  intro y hy
  have hyball := himg hy
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase j a] at hyball
  exact hyball

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem chain_image_ball
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j a : ℕ} (ha : 1 ≤ a)
    (D : BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a) (g j) (g (j + a))) :
    (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        Metric.ball (b j) ((2 : ℝ) ^ j) ⊆
      Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a)) :=
  (chain_image_open (I := I) b Ψ hbase g hnorm ha D).trans Metric.ball_subset_closedBall

omit [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)]
  [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] in

omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem tailBall_source
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (j₀ n : ℕ)
    (D0 : ∀ k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    ∀ k, (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source := by
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  intro k x hx
  apply (D0 k).source_sub
  exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hx).le.trans hpow)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailBall_image
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ n : ℕ)
    (D : BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
      (g (j₀ + n)) (g ((j₀ + n) + 1))) :
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M ((j₀ + n) + 1)) ''
        (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
      Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1)) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ n < (2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith
  have hK : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
  have hsub : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1).source := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
    exact D.source_sub
  have himg := data_image_metric_ball_of_superset (I := I)
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
    (hnorm (j₀ + n)) (hnorm ((j₀ + n) + 1)) hr hpow
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hK D.forward hsub
  intro y hy
  have hy' := himg hy
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1] at hy'
  exact hy'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailClosed_image
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ n : ℕ) (hj₀ : 1 ≤ j₀)
    (D : BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
      (g (j₀ + n)) (g ((j₀ + n) + 1))) :
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M ((j₀ + n) + 1)) ''
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) ⊆
      Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1)) := by
  let rMid : ℝ := (3 / 2 : ℝ) * (2 : ℝ) ^ n
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hrMid : 0 < rMid := by
    dsimp only [rMid]
    positivity
  have hr_lt : (2 : ℝ) ^ n < rMid := by
    dsimp only [rMid]
    nlinarith
  have hrr₂ : rMid ≤ (2 : ℝ) ^ (j₀ + n) := by
    have hjpow : (2 : ℝ) ≤ (2 : ℝ) ^ j₀ := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj₀
    rw [pow_add]
    dsimp only [rMid]
    nlinarith
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 4 / 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)
    have hs0 := Real.sqrt_nonneg (1 + (1 / 2 : ℝ))
    nlinarith
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * rMid < (2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    dsimp only [rMid]
    nlinarith
  have hclosed : Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) ⊆
      Metric.ball (b (j₀ + n)) rMid := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hr_lt)
  have hK : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
  have hsub : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1).source := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
    exact D.source_sub
  have himg := data_image_metric_ball_of_superset (I := I)
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
    (hnorm (j₀ + n)) (hnorm ((j₀ + n) + 1)) hrMid hrr₂
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hK D.forward hsub
  intro y hy
  have hy' := himg (Set.image_mono hclosed hy)
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1] at hy'
  exact hy'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

noncomputable def tailBallSystem
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
    SmoothSeqSystem I (fun n => tailBallOpen b j₀ n) := by
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let hU := fun n => tailBall_source (I := I) b Ψ g j₀ n (D₀ n)
  let hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
        (tailBallOpen b j₀ (n + 1) : Set (M (j₀ + (n + 1)))) := fun n => by
    simpa only [tailBallOpen, Nat.add_assoc] using
      tailBall_image (I := I) b Ψ hbase g hnorm j₀ n (D₀ n 1)
  exact chainBallSystem (I := I) j₀ (tailBallOpen b j₀) Ψ hU hmap

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailSystem_center
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n : ℕ) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
    (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
        (Nat.le_succ n) (tailCenter b j₀ n) = tailCenter b j₀ (n + 1) := by
  letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
  let hU := fun m => tailBall_source (I := I) b Ψ g j₀ m (D₀ m)
  let hmap : ∀ m,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + m) 1 :
        M (j₀ + m) → M (j₀ + (m + 1))) ''
          (tailBallOpen b j₀ m : Set (M (j₀ + m))) ⊆
        (tailBallOpen b j₀ (m + 1) : Set (M (j₀ + (m + 1)))) := fun m => by
    simpa only [tailBallOpen, Nat.add_assoc] using
      tailBall_image (I := I) b Ψ hbase g hnorm j₀ m (D₀ m 1)
  have hF :
      (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
          (Nat.le_succ n) =
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n) := by
    unfold tailBallSystem
    apply SmoothSeqSystem.ofSucc_F_succ
  rw [hF]
  apply Subtype.ext
  change (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
    M (j₀ + n) → M ((j₀ + n) + 1)) (b (j₀ + n)) = b (j₀ + (n + 1))
  simpa only [Nat.add_assoc] using
    chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailCenter_map
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n : ℕ) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
    (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
        (Nat.zero_le n) (tailCenter b j₀ 0) = tailCenter b j₀ n := by
  letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  induction n with
  | zero =>
      exact S.toSeqSystem.map_self 0 (tailCenter b j₀ 0)
  | succ n ih =>
      calc
        S.toSeqSystem.F (Nat.zero_le (n + 1)) (tailCenter b j₀ 0) =
            S.toSeqSystem.F ((Nat.zero_le n).trans (Nat.le_succ n))
              (tailCenter b j₀ 0) :=
          S.toSeqSystem.F_apply_irrel _ _ _
        _ = S.toSeqSystem.F (Nat.le_succ n)
              (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0)) :=
          (S.toSeqSystem.map_map (Nat.zero_le n) (Nat.le_succ n)
            (tailCenter b j₀ 0)).symm
        _ = S.toSeqSystem.F (Nat.le_succ n) (tailCenter b j₀ n) := by rw [ih]
        _ = tailCenter b j₀ (n + 1) :=
          tailSystem_center (I := I) b Ψ hbase g hnorm j₀ D₀ n

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailCenter_incl
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (n : ℕ) :
    letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    S.toSeqSystem.incl n (tailCenter b j₀ n) =
      S.toSeqSystem.incl 0 (tailCenter b j₀ 0) := by
  letI : ∀ m, Nonempty (tailBallOpen b j₀ m) := fun m => tailBall_nonempty b j₀ m
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        S.toSeqSystem.incl (n + 1) (tailCenter b j₀ (n + 1)) =
            S.toSeqSystem.incl (n + 1)
              (S.toSeqSystem.F (Nat.le_succ n) (tailCenter b j₀ n)) := by
          rw [tailSystem_center (I := I) b Ψ hbase g hnorm j₀ D₀ n]
        _ = S.toSeqSystem.incl n (tailCenter b j₀ n) :=
          S.toSeqSystem.incl_comp (Nat.le_succ n) (tailCenter b j₀ n)
        _ = S.toSeqSystem.incl 0 (tailCenter b j₀ 0) := ih

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailSystem_compact
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ) (hj₀ : 1 ≤ j₀)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
    ∀ n, ∃ K : Set (tailBallOpen b j₀ (n + 1)), IsCompact K ∧
      Set.range ((tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
        (Nat.le_succ n)) ⊆ K := by
  classical
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let hU := fun n => tailBall_source (I := I) b Ψ g j₀ n (D₀ n)
  let hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
        (tailBallOpen b j₀ (n + 1) : Set (M (j₀ + (n + 1)))) := fun n => by
    simpa only [tailBallOpen, Nat.add_assoc] using
      tailBall_image (I := I) b Ψ hbase g hnorm j₀ n (D₀ n 1)
  intro n
  let Φ := chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1
  let C : Set (M (j₀ + n)) := Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n)
  let K : Set (tailBallOpen b j₀ (n + 1)) := Subtype.val ⁻¹' ((Φ : M (j₀ + n) → _) '' C)
  refine ⟨K, ?_, ?_⟩
  · have hC : IsCompact C := isCompact_closedBall _ _
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hCsrc : C ⊆ Φ.source := by
      intro x hx
      apply (D₀ n 1).source_sub
      exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hx).trans hpow)
    have hΦc : ContinuousOn (Φ : M (j₀ + n) → M ((j₀ + n) + 1)) C :=
      Φ.contMDiffOn_toFun.continuousOn.mono hCsrc
    have hImage : IsCompact ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C) :=
      hC.image_of_continuousOn hΦc
    have hImageSub : ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C) ⊆
        (tailBallOpen b j₀ (n + 1) : Set (M (j₀ + (n + 1)))) := by
      simpa only [Φ, C, tailBallOpen, Nat.add_assoc] using
        tailClosed_image (I := I) b Ψ hbase g hnorm j₀ n hj₀ (D₀ n 1)
    dsimp only [K]
    rw [Subtype.isCompact_iff]
    have hval : Subtype.val ''
          (Subtype.val ⁻¹' ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C) :
            Set (tailBallOpen b j₀ (n + 1))) =
        (Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨y, hImageSub hy⟩, hy, rfl⟩
    rw [hval]
    exact hImage
  · have hF :
        (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).toSeqSystem.F
            (Nat.le_succ n) =
          PartialDiffeomorph.opensMap Φ (hU n 1) (hmap n) := by
      unfold tailBallSystem
      apply SmoothSeqSystem.ofSucc_F_succ
    rw [hF]
    rintro _ ⟨x, rfl⟩
    change ((Φ : M (j₀ + n) → M ((j₀ + n) + 1)) x ∈
      (Φ : M (j₀ + n) → M ((j₀ + n) + 1)) '' C)
    exact ⟨x, Metric.mem_closedBall.mpr (Metric.mem_ball.mp x.property).le, rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailMetricCocycle
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w)) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
    (tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀).MetricCocycle
      (tailMetric (I := I) b j₀ gInf) := by
  classical
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  let V : ∀ n, Opens (M (j₀ + n)) := tailBallOpen b j₀
  letI : ∀ n, Nonempty (V n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (V n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (V n).isOpen)
  let hV := fun n => tailBall_source (I := I) b Ψ g j₀ n (D₀ n)
  let hmapV : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (V n : Set (M (j₀ + n))) ⊆
          (V (n + 1) : Set (M (j₀ + (n + 1)))) := fun n => by
    simpa only [V, tailBallOpen, Nat.add_assoc] using
      tailBall_image (I := I) b Ψ hbase g hnorm j₀ n (D₀ n 1)
  let gTail : ∀ n, SmoothRiemannianMetric I (V n) :=
    tailMetric (I := I) b j₀ gInf
  have hstepV : ∀ n,
      let F : V n → V (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hV n 1) (hmapV n)
      ∀ (x : V n) (v w : TangentSpace I x),
        (gTail n).inner x v w =
          (gTail (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w) := by
    intro n
    dsimp only
    let Fbig : U n → U (n + 1) := PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
    let Fsmall : V n → V (n + 1) := PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hV n 1) (hmapV n)
    let inc : V n → U n := Opens.inclusion (tailBall_le_large b j₀ n)
    let incNext : V (n + 1) → U (n + 1) :=
      Opens.inclusion (tailBall_le_large b j₀ (n + 1))
    intro x v w
    have hbig := hstep n (inc x) v w
    have hpoint : Fbig (inc x) = incNext (Fsmall x) := by
      apply Subtype.ext
      rfl
    have hderiv (u : TangentSpace I x) :
        mfderiv I I Fbig (inc x) u = mfderiv I I Fsmall x u := by
      dsimp only [Fbig, Fsmall]
      rw [PartialDiffeomorph.opensMap_mfderiv,
        PartialDiffeomorph.opensMap_mfderiv]
    change (gInf n).inner (inc x) v w =
      (gInf (n + 1)).inner (incNext (Fsmall x))
        (mfderiv I I Fsmall x v) (mfderiv I I Fsmall x w)
    rw [← hpoint, ← hderiv v, ← hderiv w]
    exact hbig
  change (chainBallSystem (I := I) j₀ V Ψ hV hmapV).MetricCocycle gTail
  exact chainMetricCocycle (I := I) j₀ V Ψ hV hmapV gTail hstepV

omit [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)]
  [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] in

omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chainBall_source
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    {j : ℕ}
    (D0 : ∀ k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k))) :
    ∀ k, (ballOpen b (fun n => (2 : ℝ) ^ n) j : Set (M j)) ⊆
      (chainComp (I := I) (Mf := M) Ψ j k).source := by
  intro k x hx
  apply (D0 k).source_sub
  exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem chainPullback_bdd
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j : ℕ}
    (D0 : ∀ k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)))
    (Dhi : ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
      Nonempty (BookApproxIsoPartialData (I := I)
        (Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a))) (1 / 2) p
        (chainComp (I := I) (Mf := M) Ψ (j + a) c)
        (g (j + a)) (g ((j + a) + c)))) :
    let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let hU := chainBall_source (I := I) b Ψ g D0
    let gSeq := chainPullbackSeq (I := I) Ψ g U hU
    ∃ gRef : ℕ → SmoothRiemannianMetric I U,
      (∀ r q : ℕ, q ≤ r → ∀ K : Set U, IsCompact K → ∃ C : Real,
        ∀ k : ℕ, ∀ z ∈ K,
          metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C) ∧
      ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : U) (v : TangentSpace I x),
        c * ((g j).restrictOpen (I := I) U).inner x v v ≤ (gSeq k).inner x v v := by
  classical
  let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let hU := chainBall_source (I := I) b Ψ g D0
  let gSeq := chainPullbackSeq (I := I) Ψ g U hU
  let a : ℕ → ℕ := fun r => (Dhi r).choose
  have ha : ∀ r, 1 ≤ a r := fun r => (Dhi r).choose_spec.1
  have htail : ∀ r c, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j + a r)) ((2 : ℝ) ^ (j + a r))) (1 / 2) r
      (chainComp (I := I) (Mf := M) Ψ (j + a r) c)
      (g (j + a r)) (g ((j + a r) + c)) :=
    fun r c => Classical.choice ((Dhi r).choose_spec.2 c)
  let gRef : ℕ → SmoothRiemannianMetric I U := fun r => gSeq (a r)
  refine ⟨gRef, ?_, ?_⟩
  · intro r q hqr K hK
    apply cov_bdd_of_eventual (I := I) hK q gSeq (gRef r)
    refine ⟨a r, max (2 * Real.sqrt (Module.finrank ℝ E : ℝ)) (1 / 2), ?_⟩
    intro k hk z hz
    let c := k - a r
    have hdecomp : a r + c = k := by
      dsimp only [c]
      omega
    have hpre := hU (a r)
    have himg :
        (chainComp (I := I) (Mf := M) Ψ j (a r) : M j → M (j + a r)) ''
            (U : Set (M j)) ⊆
          Metric.closedBall (b (j + a r)) ((2 : ℝ) ^ (j + a r)) := by
      simpa only [U, ballOpen] using
        chain_image_ball (I := I) b Ψ hbase g hnorm (ha r) (D0 (a r))
    have hnext :
        (chainComp (I := I) (Mf := M) Ψ j (a r) : M j → M (j + a r)) ''
            (U : Set (M j)) ⊆
          (chainComp (I := I) (Mf := M) Ψ (j + a r) c).source :=
      fun y hy => (htail r c).source_sub (himg hy)
    have hfull : (U : Set (M j)) ⊆
        (chainCompAssoc (I := I) (Mf := M) Ψ j (a r) c).source := by
      rw [chainAssoc_source]
      exact hU (a r + c)
    by_cases hq0 : q = 0
    · subst q
      have hb := chainPrefix_zero_le (I := I) Ψ U hpre hnext himg hfull
        (g (j + a r)) (g ((j + a r) + c)) (htail r c).forward (by norm_num) z
      rw [ballPullback_assoc (I := I) Ψ g U hfull (hU (a r + c))] at hb
      rw [hdecomp] at hb
      have hb' : metricCovDerivNorm (I := I) 0 (gSeq k) (gRef r) z ≤
          2 * Real.sqrt (Module.finrank ℝ E : ℝ) := by
        simpa only [gSeq, gRef, chainPullbackSeq] using hb
      exact hb'.trans (le_max_left _ _)
    · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
      have hb := chainPrefix_cov_le (I := I) Ψ U hpre hnext himg hfull
        (g (j + a r)) (g ((j + a r) + c)) (htail r c).forward hq1 hqr z
      rw [ballPullback_assoc (I := I) Ψ g U hfull (hU (a r + c))] at hb
      rw [hdecomp] at hb
      have hb' : metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ 1 / 2 := by
        simpa only [gSeq, gRef, chainPullbackSeq] using hb
      exact hb'.trans (le_max_right _ _)
  · refine ⟨1 / 2, by norm_num, fun k x v => ?_⟩
    have hUK : (U : Set (M j)) ⊆ Metric.closedBall (b j) ((2 : ℝ) ^ j) :=
      fun y hy => Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le
    have hb := ballPullback_lower (I := I)
      (chainComp (I := I) (Mf := M) Ψ j k) U (hU k) hUK
      (g j) (g (j + k)) (D0 k).forward x v
    norm_num at hb
    simpa only [gSeq, chainPullbackSeq] using hb

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_chain_limit
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j : ℕ}
    (D0 : ∀ k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)))
    (Dhi : ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
      Nonempty (BookApproxIsoPartialData (I := I)
        (Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a))) (1 / 2) p
        (chainComp (I := I) (Mf := M) Ψ (j + a) c)
        (g (j + a)) (g ((j + a) + c)))) :
    let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    let hU := chainBall_source (I := I) b Ψ g D0
    let gSeq := chainPullbackSeq (I := I) Ψ g U hU
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I U,
      MetricCInfConvOnCompacts (I := I) (fun k => gSeq (φ k)) gInf
        ((g j).restrictOpen (I := I) U) := by
  classical
  let U := ballOpen b (fun n => (2 : ℝ) ^ n) j
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let hU := chainBall_source (I := I) b Ψ g D0
  let gSeq := chainPullbackSeq (I := I) Ψ g U hU
  obtain ⟨gRef, hbdd, hlow⟩ :=
    chainPullback_bdd (I := I) b Ψ hbase g hnorm D0 Dhi
  exact metricCInf_refs (I := I) (ballOpen_nonempty b (fun n => (2 : ℝ) ^ n) j (by positivity))
    ((g j).restrictOpen (I := I) U) gRef gSeq hbdd hlow

omit [I.Boundaryless] [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in


omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem exists_chain_data
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (BookApproxIsoPartialData (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
          (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j →
      ∃ _D0 : ∀ k, BookApproxIsoPartialData (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)),
        ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
          Nonempty (BookApproxIsoPartialData (I := I)
            (Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a))) (1 / 2) p
            (chainComp (I := I) (Mf := M) Ψ (j + a) c)
            (g (j + a)) (g ((j + a) + c))) := by
  classical
  let hzero := hdata (1 / 2) (by norm_num) (by norm_num) 0
  let jbase := Classical.choose hzero
  have hjbase := Classical.choose_spec hzero
  let j₀ := max 1 jbase
  refine ⟨j₀, le_max_left _ _, fun j hj => ?_⟩
  let D0 : ∀ k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j k) (g j) (g (j + k)) :=
    fun k => Classical.choice (hjbase j (le_trans (le_max_right 1 jbase) hj) k)
  refine ⟨D0, fun p => ?_⟩
  let hp := hdata (1 / 2) (by norm_num) (by norm_num) p
  let jp := Classical.choose hp
  have hjp := Classical.choose_spec hp
  let a := max 1 (jp - j)
  refine ⟨a, le_max_left _ _, fun c => ?_⟩
  apply hjp (j + a) (by
    dsimp only [a]
    omega) c

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



theorem exists_limits_diag
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (BookApproxIsoPartialData (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
          (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧
      let U : ∀ n, Opens (M (j₀ + n)) :=
        fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
      ∃ _D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
          (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
          (g (j₀ + n)) (g ((j₀ + n) + k)),
        ∃ hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source,
        (∀ n,
            (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
              M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
              (U (n + 1) : Set (M (j₀ + (n + 1)))) ) ∧
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ gInf : ∀ n, SmoothRiemannianMetric I (U n),
            ∀ n,
              letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
                (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
              MetricCInfConvOnCompacts (I := I)
                (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
                  (φ k - (j₀ + n)))
                (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n)) := by
  classical
  obtain ⟨j₀, hj₀, hpacks⟩ := exists_chain_data (I := I) b Ψ g hdata
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  have hpacks' : ∀ n,
      ∃ D0 : ∀ k, BookApproxIsoPartialData (I := I)
          (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
          (g (j₀ + n)) (g ((j₀ + n) + k)),
        ∀ p : ℕ, ∃ a : ℕ, 1 ≤ a ∧ ∀ c : ℕ,
          Nonempty (BookApproxIsoPartialData (I := I)
            (Metric.closedBall (b ((j₀ + n) + a)) ((2 : ℝ) ^ ((j₀ + n) + a))) (1 / 2) p
            (chainComp (I := I) (Mf := M) Ψ ((j₀ + n) + a) c)
            (g ((j₀ + n) + a)) (g (((j₀ + n) + a) + c))) :=
    fun n => hpacks (j₀ + n) (Nat.le_add_right j₀ n)
  choose D0 Dhi using hpacks'
  let hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source :=
    fun n => chainBall_source (I := I) b Ψ g (D0 n)
  let hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1))) ) := fun n => by
    simpa only [U, ballOpen, Nat.add_assoc] using
      chain_image_open (I := I) b Ψ hbase g hnorm (j := j₀ + n) (a := 1)
        (by omega) (D0 n 1)
  let gSeq : ∀ n, ℕ → SmoothRiemannianMetric I (U n) :=
    fun n => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
  let P : ℕ → (ℕ → ℕ) → Prop := fun n ξ =>
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    ∃ gInf : SmoothRiemannianMetric I (U n),
      MetricCInfConvOnCompacts (I := I)
        (fun k => gSeq n (ξ k - (j₀ + n))) gInf
        ((g (j₀ + n)).restrictOpen (I := I) (U n))
  have metric_subseq : ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
      [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
      {gS : ℕ → SmoothRiemannianMetric I N} {gLim gBase : SmoothRiemannianMetric I N},
      MetricCInfConvOnCompacts (I := I) gS gLim gBase →
      ∀ {ρ : ℕ → ℕ}, StrictMono ρ →
        MetricCInfConvOnCompacts (I := I) (fun k => gS (ρ k)) gLim gBase := by
    intro N _ _ _ _ _ gS gLim gBase hconv ρ hρ K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hconv K hK p ε hε
    exact ⟨k₀, fun k hk => hk₀ (ρ k) (le_trans hk hρ.le_apply)⟩
  have metric_of_tail : ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
      [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
      {gS : ℕ → SmoothRiemannianMetric I N} {gLim gBase : SmoothRiemannianMetric I N},
      ∀ m : ℕ,
        MetricCInfConvOnCompacts (I := I) (fun k => gS (k + m)) gLim gBase →
        MetricCInfConvOnCompacts (I := I) gS gLim gBase := by
    intro N _ _ _ _ _ gS gLim gBase m hconv K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hconv K hK p ε hε
    refine ⟨k₀ + m, fun k hk => ?_⟩
    have hval := hk₀ (k - m) (by omega)
    simpa only [Nat.sub_add_cancel (show m ≤ k by omega)] using hval
  obtain ⟨φ, hφ, hPφ⟩ := exists_diag_subseq P
    (fun n ξ _ => by
      letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gRef, hbdd, hlow⟩ :=
        chainPullback_bdd (I := I) b Ψ hbase g hnorm (D0 n) (Dhi n)
      have hbdd' : ∀ r q : ℕ, q ≤ r → ∀ K : Set (U n), IsCompact K → ∃ C : Real,
          ∀ k : ℕ, ∀ z ∈ K,
            metricCovDerivNorm (I := I) q
              (gSeq n (ξ k - (j₀ + n))) (gRef r) z ≤ C := by
        intro r q hqr K hK
        obtain ⟨C, hC⟩ := hbdd r q hqr K hK
        exact ⟨C, fun k z hz => hC (ξ k - (j₀ + n)) z hz⟩
      obtain ⟨c, hc, hclow⟩ := hlow
      have hlow' : ∃ c : Real, 0 < c ∧ ∀ (k : ℕ) (x : U n) (v : TangentSpace I x),
          c * ((g (j₀ + n)).restrictOpen (I := I) (U n)).inner x v v ≤
            (gSeq n (ξ k - (j₀ + n))).inner x v v :=
        ⟨c, hc, fun k => hclow (ξ k - (j₀ + n))⟩
      obtain ⟨ψ, hψ, gInf, hconv⟩ := metricCInf_refs (I := I)
        (ballOpen_nonempty b (fun s => (2 : ℝ) ^ s) (j₀ + n) (by positivity))
        ((g (j₀ + n)).restrictOpen (I := I) (U n)) gRef
        (fun k => gSeq n (ξ k - (j₀ + n))) hbdd' hlow'
      exact ⟨ψ, hψ, gInf, by simpa only [Function.comp_apply] using hconv⟩)
    (fun n ξ ρ hρ hP => by
      letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gInf, hconv⟩ := hP
      exact ⟨gInf, metric_subseq hconv hρ⟩)
    (fun n ξ m hP => by
      letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
      obtain ⟨gInf, hconv⟩ := hP
      exact ⟨gInf, metric_of_tail m hconv⟩)
  let gInf : ∀ n, SmoothRiemannianMetric I (U n) := fun n =>
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    (hPφ n).choose
  refine ⟨j₀, hj₀, D0, hU, hmap, φ, hφ, gInf, fun n => ?_⟩
  letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  exact (hPφ n).choose_spec

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



theorem exists_limits_close
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ,
      ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
        Nonempty (BookApproxIsoPartialData (I := I)
          (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
          (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧
      let U : ∀ n, Opens (M (j₀ + n)) :=
        fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
      ∃ _D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
          (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
          (g (j₀ + n)) (g ((j₀ + n) + k)),
        ∃ hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source,
        ∃ hmap : ∀ n,
            (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
              M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
              (U (n + 1) : Set (M (j₀ + (n + 1)))),
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ gInf : ∀ n, SmoothRiemannianMetric I (U n),
            (∀ n,
              letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
                (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
              MetricCInfConvOnCompacts (I := I)
                (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
                  (φ k - (j₀ + n)))
                (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n))) ∧
            (∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
              ∀ n : ℕ, n₀ ≤ n →
                letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
                  (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
                ∀ l q : ℕ, q ≤ p → ∀ x : U n,
                  metricDerivNorm (I := I) q
                    (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
                    (gInf n) (gInf n) x ≤ ε) ∧
            ∀ n,
              let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
                (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
              ∀ (x : U n) (v w : TangentSpace I x),
                (gInf n).inner x v w =
                  (gInf (n + 1)).inner (F x)
                    (mfderiv I I F x v) (mfderiv I I F x w) := by
  classical
  obtain ⟨j₀, hj₀, D₀, hU, hmap, φ, hφ, gInf, hconv⟩ :=
    exists_limits_diag (I := I) b Ψ hbase g hnorm hdata
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  refine ⟨j₀, hj₀, ?_⟩
  dsimp only
  refine ⟨D₀, hU, hmap, φ, hφ, gInf, hconv, ?_, ?_⟩
  · intro ε hε p
    obtain ⟨δ, hδ0, hδ1, hδdim, hδbudget⟩ := exists_refDelta (E := E) p hε
    obtain ⟨jδ, hjδ⟩ := hdata δ hδ0 hδ1 p
    refine ⟨jδ, fun n hn => ?_⟩
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    intro l q hqp x
    have hstage : jδ ≤ j₀ + n := by omega
    let D : ∀ m, BookApproxIsoPartialData (I := I)
        (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) δ p
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) m)
        (g (j₀ + n)) (g ((j₀ + n) + m)) :=
      fun m => Classical.choice (hjδ (j₀ + n) hstage m)
    have hUK : (U n : Set (M (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
      simpa only [U, ballOpen] using
        (Metric.ball_subset_closedBall :
          Metric.ball (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) ⊆
            Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)))
    have htail (m a : ℕ) (hap : a ≤ p) (y : U n) :
        metricDerivNorm (I := I) a
          (chainPullbackSeq (I := I) Ψ g (U n) (hU n) m)
          ((g (j₀ + n)).restrictOpen (I := I) (U n))
          ((g (j₀ + n)).restrictOpen (I := I) (U n)) y ≤ δ := by
      simpa only [chainPullbackSeq] using
        pullbackDiff_le (I := I)
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) m) (U n) (hU n m) hUK
          (g (j₀ + n)) (g ((j₀ + n) + m)) (D m).forward hap y
    have hInfBase : ∀ y ∈ (Set.univ : Set (U n)), ∀ a, a ≤ p →
        metricDerivNorm (I := I) a (gInf n)
          ((g (j₀ + n)).restrictOpen (I := I) (U n))
          ((g (j₀ + n)).restrictOpen (I := I) (U n)) y ≤ δ := by
      intro y _ a hap
      exact limitDiff_le (I := I)
        (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n)
          (φ k - (j₀ + n)))
        (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n))
        ((g (j₀ + n)).restrictOpen (I := I) (U n)) (hconv n)
        (fun k => htail (φ k - (j₀ + n)) a hap y)
    exact diffNorm_limit_le (I := I) isOpen_univ
      (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l) (gInf n)
      ((g (j₀ + n)).restrictOpen (I := I) (U n)) p hδ0.le hδ1.le hδdim hδbudget
      (fun y _ a hap => htail l a hap y) hInfBase x (Set.mem_univ x) q hqp
  · intro n
    letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
    letI : SigmaCompactSpace (U (n + 1)) := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (U (n + 1)).isOpen)
    let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
    intro x v w
    have hleft := metricCInf_inner (I := I)
      (fun k => chainPullbackSeq (I := I) Ψ g (U n) (hU n) (φ k - (j₀ + n)))
      (gInf n) ((g (j₀ + n)).restrictOpen (I := I) (U n)) (hconv n) x v w
    have hright := metricCInf_inner (I := I)
      (fun k => chainPullbackSeq (I := I) Ψ g (U (n + 1)) (hU (n + 1))
        (φ k - (j₀ + (n + 1))))
      (gInf (n + 1)) ((g (j₀ + (n + 1))).restrictOpen (I := I) (U (n + 1)))
      (hconv (n + 1)) (F x) (mfderiv I I F x v) (mfderiv I I F x w)
    have hevent :
        (fun k => (chainPullbackSeq (I := I) Ψ g (U n) (hU n)
          (φ k - (j₀ + n))).inner x v w) =ᶠ[Filter.atTop]
        (fun k => (chainPullbackSeq (I := I) Ψ g (U (n + 1)) (hU (n + 1))
          (φ k - (j₀ + (n + 1)))).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w)) := by
      filter_upwards [Filter.eventually_ge_atTop (j₀ + n + 1)] with k hk
      have hφk : j₀ + n + 1 ≤ φ k := le_trans hk (hφ.id_le k)
      have hlen : φ k - (j₀ + n) = 1 + (φ k - (j₀ + (n + 1))) := by omega
      rw [hlen]
      simpa only [F] using chainPullback_step (I := I) Ψ g (U n) (U (n + 1))
        (hU n) (hU (n + 1)) (hmap n) (φ k - (j₀ + (n + 1))) x v w
    have hleft' := Filter.Tendsto.congr' hevent hleft
    exact tendsto_nhds_unique hleft' hright

omit [I.Boundaryless] [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] [NeZero (Module.finrank ℝ E)] in


theorem half_ambient_le_tail
    (b : ∀ j, M j) (j₀ : ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (tailMetric (I := I) b j₀ gInf n).inner x v v := by
  let U : ∀ n, Opens (M (j₀ + n)) :=
    fun n => ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  let d : ℝ := Module.finrank ℝ E
  let ε₀ : ℝ := 1 / (d + 1)
  have hd₀ : 0 ≤ d := by
    dsimp only [d]
    positivity
  have hden : 0 < d + 1 := by linarith
  have hε₀ : 0 < ε₀ := by
    dsimp only [ε₀]
    positivity
  have hdε : d * ε₀ ≤ 1 := by
    calc
      d * ε₀ = d / (d + 1) := by
        dsimp only [ε₀]
        ring
      _ ≤ 1 := (div_le_one hden).2 (by linarith)
  obtain ⟨n₀, hn₀⟩ := hclose ε₀ hε₀ 0
  refine ⟨n₀, fun n hn x v => ?_⟩
  letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  let inc : tailBallOpen b j₀ n → U n := Opens.inclusion (tailBall_le_large b j₀ n)
  have hnorm₀ := hn₀ n hn 0 0 (by omega) (inc x)
  rw [chainPullback_zero (I := I) Ψ g (U n) (hU n)] at hnorm₀
  have hquad := metricQuadFormDiff_le_metricDerivNorm (I := I)
    ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) v
  have hcoef :
      (Module.finrank ℝ (TangentSpace I (inc x)) : ℝ) *
          metricDerivNorm (I := I) 0
            ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) ≤ 1 := by
    change d * metricDerivNorm (I := I) 0
      ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) ≤ 1
    exact (mul_le_mul_of_nonneg_left hnorm₀ hd₀).trans hdε
  have hinner₀ : 0 ≤ (gInf n).inner (inc x) v v :=
    metricInner_nonneg (I := I) (gInf n) (inc x) v
  have hscaled :
      (Module.finrank ℝ (TangentSpace I (inc x)) : ℝ) *
          metricDerivNorm (I := I) 0
            ((g (j₀ + n)).restrictOpen (I := I) (U n)) (gInf n) (gInf n) (inc x) *
            (gInf n).inner (inc x) v v ≤ (gInf n).inner (inc x) v v := by
    calc
      _ ≤ 1 * (gInf n).inner (inc x) v v :=
        mul_le_mul_of_nonneg_right hcoef hinner₀
      _ = (gInf n).inner (inc x) v v := one_mul _
  have hbound := hquad.trans hscaled
  have hbound' :
      |(g (j₀ + n)).inner (x : M (j₀ + n)) v v -
          (tailMetric (I := I) b j₀ gInf n).inner x v v| ≤
        (tailMetric (I := I) b j₀ gInf n).inner x v v := by
    simpa only [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictSubset_inner] using hbound
  rw [abs_le] at hbound'
  nlinarith [hbound'.2]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
  [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)] in


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem enorm_val_le_two
    (b : ∀ j, M j) (j₀ n : ℕ)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (gTail : SmoothRiemannianMetric I (tailBallOpen b j₀ n))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (x : tailBallOpen b j₀ n) (v : TangentSpace I x)
    (hlow : (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤
      gTail.inner x v v) :
    letI : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
      ⟨gTail.toRiemannianMetric⟩
    ‖mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v‖ₑ ≤
      2 * ‖v‖ₑ := by
  letI : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
    ⟨gTail.toRiemannianMetric⟩
  have hquad : gAmb.inner (x : M (j₀ + n)) v v ≤ 2 * gTail.inner x v v := by
    nlinarith
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  calc
    ‖mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v‖ₑ =
        ENNReal.ofReal (Real.sqrt (gAmb.inner (x : M (j₀ + n))
          (mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v)
          (mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) x v))) :=
      hAmbNorm _ _
    _ = ENNReal.ofReal (Real.sqrt (gAmb.inner (x : M (j₀ + n)) v v)) := by
      rw [mfderiv_subtype_val_apply]
    _ ≤ ENNReal.ofReal (Real.sqrt (2 * gTail.inner x v v)) :=
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hquad)
    _ = ENNReal.ofReal (Real.sqrt 2) *
        ENNReal.ofReal (Real.sqrt (gTail.inner x v v)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    _ = ENNReal.ofReal (Real.sqrt 2) * ‖v‖ₑ := by
      rw [DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        gTail x v]
    _ ≤ 2 * ‖v‖ₑ := mul_le_mul_left
      (by simpa using ENNReal.ofReal_le_ofReal hsqrt2) _

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
  [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)] in


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem pathELength_val_le
    (b : ∀ j, M j) (j₀ n : ℕ)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (gTail : SmoothRiemannianMetric I (tailBallOpen b j₀ n))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (hlow : ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
      (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤ gTail.inner x v v)
    {γ : ℝ → tailBallOpen b j₀ n} {t₀ t₁ : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc t₀ t₁)) :
    letI : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
      ⟨gTail.toRiemannianMetric⟩
    Manifold.pathELength I ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ γ) t₀ t₁ ≤
      2 * Manifold.pathELength I γ t₀ t₁ := by
  letI : RiemannianBundle (fun y : tailBallOpen b j₀ n => TangentSpace I y) :=
    ⟨gTail.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    ← MeasureTheory.lintegral_const_mul' (2 : ENNReal) _ (by norm_num)]
  refine MeasureTheory.lintegral_mono_ae
    (Filter.eventually_of_mem
      (MeasureTheory.self_mem_ae_restrict measurableSet_Ioo) ?_)
  intro t ht
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hval : MDifferentiableAt I I
      (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) (γ t) :=
    (contMDiff_subtype_val (I := I) (U := tailBallOpen b j₀ n)
      (n := (∞ : WithTop ℕ∞))).mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ γ) t =
      (mfderiv I I (Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) (γ t)).comp
        (mfderiv 𝓘(ℝ, ℝ) I γ t) := mfderiv_comp t hval hγt
  rw [hcomp]
  exact enorm_val_le_two b j₀ n gAmb gTail hAmbNorm (γ t)
    (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (hlow _ _)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem path_escape_core
    (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    [∀ m, SigmaCompactSpace (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (hlow : ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
      (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤ (gTail n).inner x v v)
    {γ : ℝ → S.toSeqSystem.Lim}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 1))
    (hγ0 : γ 0 = S.toSeqSystem.incl n (tailCenter b j₀ n))
    (hγ1 : γ 1 ∉ limitCore b j₀ S n) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
    ENNReal.ofReal ((2 : ℝ) ^ n / 4) ≤ Manifold.pathELength I γ 0 1 := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  letI : RiemannianBundle
      (fun x : tailBallOpen b j₀ n => TangentSpace I x) :=
    ⟨(gTail n).toRiemannianMetric⟩
  have hstart : γ 0 ∈ interior (limitCore b j₀ S n) := by
    rw [hγ0]
    exact center_mem_coreInt b j₀ n S
  obtain ⟨t, ht, hstay, hfront⟩ := exists_first_exit
    (limitCore_closed b j₀ n S) hγ.continuousOn hstart hγ1
  obtain ⟨x, hxinc, hxrad⟩ := frontier_core_radius b j₀ n S hfront
  have hγpre : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 t) :=
    hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)
  have hrange : ∀ s ∈ Set.Icc (0 : ℝ) t,
      γ s ∈ Set.range (S.toSeqSystem.incl n) := by
    intro s hs
    have hsK := hstay s hs
    obtain ⟨y, _, hyeq⟩ := hsK
    exact ⟨y, hyeq⟩
  let δ : ℝ → tailBallOpen b j₀ n :=
    Function.invFun (S.toSeqSystem.incl n) ∘ γ
  have hδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 δ (Set.Icc 0 t) := by
    intro s hs
    exact ContMDiffAt.comp_contMDiffWithinAt s
      ((S.contMDiffAt_invIncl n (hrange s hs)).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ∞))
      (hγpre s hs)
  have hvalδ : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) (Set.Icc 0 t) :=
    ((contMDiff_subtype_val (I := I) (U := tailBallOpen b j₀ n)
      (n := (∞ : WithTop ℕ∞))).of_le
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp_contMDiffOn hδ
  have hδ0 : δ 0 = tailCenter b j₀ n := by
    change Function.invFun (S.toSeqSystem.incl n) (γ 0) = tailCenter b j₀ n
    rw [hγ0]
    exact Function.leftInverse_invFun (S.toSeqSystem.incl_injective n) _
  have hδt : δ t = x := by
    change Function.invFun (S.toSeqSystem.incl n) (γ t) = x
    rw [← hxinc]
    exact Function.leftInverse_invFun (S.toSeqSystem.incl_injective n) _
  have hval0 :
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 = b (j₀ + n) := by
    change (δ 0 : M (j₀ + n)) = b (j₀ + n)
    rw [hδ0]
    rfl
  have hvalt :
      ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) t =
        (x : M (j₀ + n)) := by
    change (δ t : M (j₀ + n)) = (x : M (j₀ + n))
    rw [hδt]
  have hamb : Manifold.riemannianEDist I (b (j₀ + n)) (x : M (j₀ + n)) ≤
      Manifold.pathELength I
        ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 t :=
    Manifold.riemannianEDist_le_pathELength hvalδ hval0 hvalt ht.1.le
  have hradius : ENNReal.ofReal (coreRadius n) ≤
      Manifold.pathELength I
        ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 t := by
    calc
      ENNReal.ofReal (coreRadius n) = edist (b (j₀ + n)) (x : M (j₀ + n)) := by
        rw [edist_dist, hxrad]
      _ = Manifold.riemannianEDist I (b (j₀ + n)) (x : M (j₀ + n)) :=
        IsRiemannianManifold.out (I := I) _ _
      _ ≤ _ := hamb
  have hvalLe := pathELength_val_le b j₀ n gAmb (gTail n) hAmbNorm hlow hδ
  have hpull : Manifold.pathELength I δ 0 t = Manifold.pathELength I γ 0 t := by
    simpa only [δ] using pathELength_invIncl S gTail hgTail n hγpre hrange
  have hprefix : Manifold.pathELength I γ 0 t ≤ Manifold.pathELength I γ 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  have hRle : ENNReal.ofReal (coreRadius n) ≤
      2 * Manifold.pathELength I γ 0 1 := by
    calc
      ENNReal.ofReal (coreRadius n) ≤
          Manifold.pathELength I
            ((Subtype.val : tailBallOpen b j₀ n → M (j₀ + n)) ∘ δ) 0 t := hradius
      _ ≤ 2 * Manifold.pathELength I δ 0 t := hvalLe
      _ = 2 * Manifold.pathELength I γ 0 t := by rw [hpull]
      _ ≤ 2 * Manifold.pathELength I γ 0 1 := by
        simpa only [mul_comm] using mul_le_mul_left hprefix (2 : ENNReal)
  have hsplit : (2 : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ n / 4) =
      ENNReal.ofReal (coreRadius n) := by
    calc
      (2 : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ n / 4) =
          ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ((2 : ℝ) ^ n / 4) := by norm_num
      _ = ENNReal.ofReal ((2 : ℝ) * ((2 : ℝ) ^ n / 4)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ENNReal.ofReal (coreRadius n) := by
        congr 1
        simp only [coreRadius]
        ring
  apply (ENNReal.mul_le_mul_iff_right (a := (2 : ENNReal))
    (by norm_num) ENNReal.ofNat_ne_top).mp
  rw [hsplit]
  exact hRle

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem mem_core_of_edist
    (b : ∀ j, M j) (j₀ n : ℕ)
    [ProperSpace (M (j₀ + n))]
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    [∀ m, SigmaCompactSpace (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (gAmb : SmoothRiemannianMetric I (M (j₀ + n)))
    (hAmbNorm : ∀ (y : M (j₀ + n)) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gAmb.inner y w w)))
    (hlow : ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
      (1 / 2 : ℝ) * gAmb.inner (x : M (j₀ + n)) v v ≤ (gTail n).inner x v v)
    {q : S.toSeqSystem.Lim}
    (hq :
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      Manifold.riemannianEDist I
        (S.toSeqSystem.incl n (tailCenter b j₀ n)) q <
          ENNReal.ofReal ((2 : ℝ) ^ n / 4)) :
    q ∈ limitCore b j₀ S n := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  by_contra hqK
  obtain ⟨γ, hγ0, hγ1, hγC, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hq
  have hγout : γ 1 ∉ limitCore b j₀ S n := by
    rw [hγ1]
    exact hqK
  have hesc := path_escape_core b j₀ n S gTail hgTail gAmb hAmbNorm hlow
    hγC hγ0 hγout
  exact (not_lt_of_ge hesc) hγlen

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem baseRange_exhausts
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j) (j₀ : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    [∀ m, SigmaCompactSpace (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (y : M j) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner y w w)))
    (O : S.toSeqSystem.Lim)
    (hcenter : ∀ n, S.toSeqSystem.incl n (tailCenter b j₀ n) = O)
    (hlow : ∃ n₀, ∀ n, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (gTail n).inner x v v)
    (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
    ∃ n, ∀ q : S.toSeqSystem.Lim,
      Manifold.riemannianEDist I O q ≤ r → q ∈ Set.range (S.toSeqSystem.incl n) := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  obtain ⟨n₀, hn₀⟩ := hlow
  have hevPow : ∀ᶠ n : ℕ in Filter.atTop,
      4 * r.toReal < (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).eventually
      (Filter.eventually_gt_atTop (4 * r.toReal))
  obtain ⟨n, hn, hpow⟩ :=
    ((Filter.eventually_ge_atTop n₀).and hevPow).exists
  have hreal : r.toReal < (2 : ℝ) ^ n / 4 := by
    nlinarith
  have hcost : r < ENNReal.ofReal ((2 : ℝ) ^ n / 4) := by
    rw [← ENNReal.ofReal_toReal hr]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hreal
  refine ⟨n, fun q hq => ?_⟩
  have hqcost : Manifold.riemannianEDist I
      (S.toSeqSystem.incl n (tailCenter b j₀ n)) q <
        ENNReal.ofReal ((2 : ℝ) ^ n / 4) := by
    rw [hcenter n]
    exact hq.trans_lt hcost
  have hcore := mem_core_of_edist b j₀ n S gTail hgTail (g (j₀ + n))
    (hnorm (j₀ + n)) (hn₀ n hn) hqcost
  obtain ⟨x, _, hx⟩ := hcore
  exact ⟨x, hx⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [∀ j, SigmaCompactSpace (M j)] [I.Boundaryless] in


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem finiteRange_exhausts
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j) (j₀ : ℕ)
    [∀ m, Nonempty (tailBallOpen b j₀ m)]
    [∀ m, SigmaCompactSpace (tailBallOpen b j₀ m)]
    (S : SmoothSeqSystem I (fun m => tailBallOpen b j₀ m))
    (gTail : ∀ m, SmoothRiemannianMetric I (tailBallOpen b j₀ m))
    (hgTail : S.MetricCocycle gTail)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (y : M j) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner y w w)))
    (O : S.toSeqSystem.Lim)
    (hcenter : ∀ n, S.toSeqSystem.incl n (tailCenter b j₀ n) = O)
    (hlow : ∃ n₀, ∀ n, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (gTail n).inner x v v)
    (hfinite :
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      ∀ z : S.toSeqSystem.Lim, Manifold.riemannianEDist I O z ≠ ⊤)
    (z : S.toSeqSystem.Lim) (r : ENNReal) (hr : r ≠ ⊤) :
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
    ∃ n, ∀ q : S.toSeqSystem.Lim,
      Manifold.riemannianEDist I z q ≤ r → q ∈ Set.range (S.toSeqSystem.incl n) := by
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  have hR : Manifold.riemannianEDist I O z + r ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfinite z, hr⟩
  obtain ⟨n, hn⟩ := baseRange_exhausts b j₀ S gTail hgTail g hnorm O hcenter hlow
    (Manifold.riemannianEDist I O z + r) hR
  refine ⟨n, fun q hq => hn q ?_⟩
  exact (Manifold.riemannianEDist_triangle (I := I) (x := O) (y := z) (z := q)).trans
    (add_le_add le_rfl hq)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tailRangeExhausts
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
    letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    let gTail := tailMetric (I := I) b j₀ gInf
    let hgTail : S.MetricCocycle gTail :=
      tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
    ∀ (z : S.toSeqSystem.Lim) (r : ENNReal), r ≠ ⊤ →
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      ∃ n, ∀ q : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z q ≤ r →
          q ∈ Set.range (S.toSeqSystem.incl n) := by
  letI : ∀ n, PreconnectedSpace (tailBallOpen b j₀ n) := fun n =>
    tailBall_preconn (I := I) b j₀ n
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
  let O : S.toSeqSystem.Lim := S.toSeqSystem.incl 0 (tailCenter b j₀ 0)
  letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
  letI : ConnectedSpace S.toSeqSystem.Lim := inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨(S.limitMetric gTail hgTail).inner,
      (S.limitMetric gTail hgTail).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  have hcenter : ∀ n, S.toSeqSystem.incl n (tailCenter b j₀ n) = O := by
    intro n
    exact tailCenter_incl (I := I) b Ψ hbase g hnorm j₀ D₀ n
  have hlow : ∃ n₀, ∀ n, n₀ ≤ n →
      ∀ (x : tailBallOpen b j₀ n) (v : TangentSpace I x),
        (1 / 2 : ℝ) * (g (j₀ + n)).inner (x : M (j₀ + n)) v v ≤
          (gTail n).inner x v v := by
    simpa only [gTail] using
      half_ambient_le_tail (I := I) b j₀ Ψ g hU gInf hclose
  have hfinite : ∀ z : S.toSeqSystem.Lim,
      Manifold.riemannianEDist I O z ≠ ⊤ := by
    intro z
    exact Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I) O z
  dsimp only
  intro z r hr
  exact finiteRange_exhausts (I := I) (b := b) (j₀ := j₀) (S := S)
    (gTail := gTail) (hgTail := hgTail) (g := g) (hnorm := hnorm) (O := O)
    (hcenter := hcenter) (hlow := hlow) (hfinite := hfinite) (z := z) (r := r) hr

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem tailLimitComplete
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ) (hj₀ : 1 ≤ j₀)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
    letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    let gTail := tailMetric (I := I) b j₀ gInf
    let hgTail : S.MetricCocycle gTail :=
      tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
    MetricComplete (I := I)
      (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail) := by
  letI : ∀ n, PreconnectedSpace (tailBallOpen b j₀ n) := fun n =>
    tailBall_preconn (I := I) b j₀ n
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
  dsimp only
  have hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal), r ≠ ⊤ →
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric gTail hgTail).toRiemannianMetric⟩
      ∃ n, ∀ q : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z q ≤ r →
          q ∈ Set.range (S.toSeqSystem.incl n) := by
    simpa only [S, gTail, hgTail] using
      tailRangeExhausts (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep hclose
  have hcompact : ∀ n, ∃ K : Set (tailBallOpen b j₀ (n + 1)), IsCompact K ∧
      Set.range (S.toSeqSystem.F (Nat.le_succ n)) ⊆ K := by
    simpa only [S] using
      tailSystem_compact (I := I) b Ψ hbase g hnorm j₀ hj₀ D₀
  have hcover : HasCompactBallCover S gTail hgTail :=
    compactCover_of_step S gTail hgTail hexh hcompact
  exact limitComplete_cover S (tailCenter b j₀ 0) gTail hgTail hcover

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)]
  [NeZero (Module.finrank ℝ E)] in


omit [I.Boundaryless] in
theorem tail_derivSup_lt
    (j₀ : ℕ)
    (U : ∀ n, Opens (M (j₀ + n)))
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
        ∀ l q : ℕ, q ≤ p → ∀ x : U n,
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
        ∀ l : ℕ, ∀ K : Set (U n), IsCompact K →
          metricDerivNormSupOn (I := I) K p
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) < ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := hclose (ε / 2) (by linarith) p
  refine ⟨n₀, fun n hn => ?_⟩
  letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  intro l K _hK
  exact lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p
      (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
      (gInf n) (gInf n) (ε / 2) (by linarith)
      (fun q hqp x _ => hn₀ n hn l q hqp x)) (by linarith)

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


omit [NeZero (Module.finrank ℝ E)] in
theorem tailFlatSup_lt
    (b : ∀ j, M j) (j₀ : ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        letI : SigmaCompactSpace (tailBallOpen b j₀ n) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
        ∀ K : Set (tailBallOpen b j₀ n), IsCompact K →
          metricDerivNormSupOn (I := I) K p
            ((g (j₀ + n)).restrictOpen (I := I) (tailBallOpen b j₀ n))
            (tailMetric (I := I) b j₀ gInf n)
            (tailMetric (I := I) b j₀ gInf n) < ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := hclose (ε / 2) (by linarith) p
  refine ⟨n₀, fun n hn => ?_⟩
  let U := ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)
  let V := tailBallOpen b j₀ n
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  intro K _hK
  refine lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall (I := I) K p
      ((g (j₀ + n)).restrictOpen (I := I) V)
      (tailMetric (I := I) b j₀ gInf n)
      (tailMetric (I := I) b j₀ gInf n) (ε / 2) (by linarith) ?_) (by linarith)
  intro q hqp x _hxK
  let inc : V → U := Opens.inclusion (tailBall_le_large b j₀ n)
  have hbig := hn₀ n hn 0 q hqp (inc x)
  rw [chainPullback_zero (I := I) Ψ g U (hU n)] at hbig
  calc
    metricDerivNorm (I := I) q
        ((g (j₀ + n)).restrictOpen (I := I) V)
        (tailMetric (I := I) b j₀ gInf n)
        (tailMetric (I := I) b j₀ gInf n) x =
      metricDerivNorm (I := I) q
        ((g (j₀ + n)).restrictOpen (I := I) U)
        (gInf n) (gInf n) (inc x) := by
          simpa only [U, V, inc, tailMetric,
            SmoothRiemannianMetric.restrictOpen_flat] using
            metricDerivNorm_flat (I := I) (tailBall_le_large b j₀ n)
              ((g (j₀ + n)).restrictOpen (I := I) U) (gInf n) (gInf n) q x
    _ ≤ ε / 2 := hbig

set_option maxHeartbeats 800000 in
omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in


def ambientCGConverges
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n)))
    [∀ n, Nonempty (U n)] [∀ n, SigmaCompactSpace (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hgInf : S.MetricCocycle gInf)
    (hstage : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ K : Set (U k), IsCompact K →
        metricDerivNormSupOn (I := I) K p
          ((g (j₀ + k)).restrictOpen (I := I) (U k))
          (gInf k) (gInf k) < ε) :
    PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ U S O₀ g)
      (limitPointedCoc S O₀ gInf hgInf) id
      (chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf) := by
  let Φ := chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf
  have hσsrc : ∀ k : ℕ,
      letI : TopologicalSpace (limitPointedCoc S O₀ gInf hgInf).M :=
        (limitPointedCoc S O₀ gInf hgInf).topology
      IsSigmaCompact (Φ.source k) := by
    intro k
    letI : TopologicalSpace (limitPointedCoc S O₀ gInf hgInf).M :=
      (limitPointedCoc S O₀ gInf hgInf).topology
    letI : ChartedSpace H (limitPointedCoc S O₀ gInf hgInf).M :=
      (limitPointedCoc S O₀ gInf hgInf).charted
    letI : SigmaCompactSpace (limitPointedCoc S O₀ gInf hgInf).M :=
      (limitPointedCoc S O₀ gInf hgInf).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k)
  have hσtgt : ∀ k : ℕ,
      letI : TopologicalSpace
          ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
      IsSigmaCompact (Φ.target k) := by
    intro k
    letI : TopologicalSpace
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
    letI : ChartedSpace H
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).charted
    letI : SigmaCompactSpace
        ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.target_open k)
  let refMetric : ∀ k : ℕ,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) := fun k => by
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
    letI : T2Space (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomT2 (I := I) Φ k
    let sourceSigma : SigmaCompactSpace (metricSourceOpen (I := I) Φ k) := by
      change SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
      exact metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
    let sourceT2 : T2Space (metricSourceOpen (I := I) Φ k) := by
      change T2Space (MetricSourceDomain (I := I) Φ k)
      exact metricSourceDomT2 (I := I) Φ k
    exact @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
      S.toSeqSystem.Lim inferInstance inferInstance inferInstance inferInstance
      (S.limitMetric gInf hgInf) (metricSourceOpen (I := I) Φ k) sourceSigma sourceT2
  refine PointedRiemannianCGConverges.ofRestrictPullback (I := I)
    Φ hσsrc hσtgt refMetric ?_
  intro K hK p ε hε
  obtain ⟨kSrc, hkSrc⟩ := Φ.source_subset hK
  obtain ⟨kConv, hkConv⟩ := hstage ε hε p
  refine ⟨max kSrc kConv, fun k hk => ?_⟩
  have hkS : kSrc ≤ k := le_trans (Nat.le_max_left kSrc kConv) hk
  have hkC : kConv ≤ k := le_trans (Nat.le_max_right kSrc kConv) hk
  letI : TopologicalSpace (limitPointedCoc S O₀ gInf hgInf).M :=
    (limitPointedCoc S O₀ gInf hgInf).topology
  letI : ChartedSpace H (limitPointedCoc S O₀ gInf hgInf).M :=
    (limitPointedCoc S O₀ gInf hgInf).charted
  letI : TopologicalSpace
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
  letI : ChartedSpace H
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).charted
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  letI : T2Space (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  letI : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSigmaOf (I := I) Φ k (hσtgt k)
  let F := metricSourceTargetDiff (I := I) Φ k
  let sourceSigma : SigmaCompactSpace (metricSourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (MetricSourceDomain (I := I) Φ k)
    exact metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
  let sourceT2 : T2Space (metricSourceOpen (I := I) Φ k) := by
    change T2Space (MetricSourceDomain (I := I) Φ k)
    exact metricSourceDomT2 (I := I) Φ k
  let sourceMetric : SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) :=
    @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
      S.toSeqSystem.Lim inferInstance inferInstance inferInstance inferInstance
      (S.limitMetric gInf hgInf) (metricSourceOpen (I := I) Φ k) sourceSigma sourceT2
  let targetSeq : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) := by
    change SmoothRiemannianMetric I (U k)
    exact (g (j₀ + k)).restrictOpen (I := I) (U k)
  let targetLim : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) := by
    change SmoothRiemannianMetric I (U k)
    exact gInf k
  have hlim : sourceMetric = Diffeomorph.pullbackMetric (I := I) targetLim F := by
    have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I
        (MetricSourceDomain (I := I) Φ k)),
        (∀ (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
          g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
      intro g₁ g₂ h
      obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
      obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
      have hi : i₁ = i₂ :=
        funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
      subst hi
      rfl
    apply metric_ext
    intro x v w
    dsimp only [sourceMetric, targetLim]
    change (S.limitMetric gInf hgInf).inner
        (x : (limitPointedCoc S O₀ gInf hgInf).M) v w =
      (gInf k).inner (F x : U k)
        (mfderiv I I F x v) (mfderiv I I F x w)
    rw [S.limitMetric_of_mem gInf hgInf k x.2]
    rw [metricSourceTargetDiff_mfderiv (I := I) Φ k x v,
      metricSourceTargetDiff_mfderiv (I := I) Φ k x w]
    let z : (limitPointedCoc S O₀ gInf hgInf).M := x
    have hxSource : z ∈ (S.inclPartialDiffeo k).source := by
      change z ∈ Set.range (S.toSeqSystem.incl k)
      exact x.2
    have hFx : (F x : U k) = Function.invFun (S.toSeqSystem.incl k) z := by
      apply Subtype.ext
      have hmapPoint : Φ.map k z =
          ((Function.invFun (S.toSeqSystem.incl k) z : U k) : M (j₀ + k)) := rfl
      exact (metricSourceTargetDiff_apply (I := I) Φ k x).trans hmapPoint
    have hmapv : mfderiv I I (Φ.map k) z v =
        mfderiv I I
          (S.inclPartialDiffeo k : (limitPointedCoc S O₀ gInf hgInf).M → U k)
          z v := by
      change mfderiv I I
        (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
          (limitPointedCoc S O₀ gInf hgInf).M → M (j₀ + k)) z v = _
      exact PartialDiffeomorph.liftOpen_mfderiv
        (S.inclPartialDiffeo k) rfl hxSource v
    have hmapw : mfderiv I I (Φ.map k) z w =
        mfderiv I I
          (S.inclPartialDiffeo k : (limitPointedCoc S O₀ gInf hgInf).M → U k)
          z w := by
      change mfderiv I I
        (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
          (limitPointedCoc S O₀ gInf hgInf).M → M (j₀ + k)) z w = _
      exact PartialDiffeomorph.liftOpen_mfderiv
        (S.inclPartialDiffeo k) rfl hxSource w
    rw [hFx, hmapv, hmapw]
    rfl
  change metricDerivNormSupOn (I := I)
      (metricSourceCompactSet (I := I) Φ k K) p
      (Diffeomorph.pullbackMetric (I := I) targetSeq F)
      sourceMetric sourceMetric < ε
  rw [hlim, metricDerivNormSupOn_pullback_image (I := I)]
  have hKsource : IsCompact (metricSourceCompactSet (I := I) Φ k K) :=
    metricSourceCompactSet_isCompact (I := I) Φ k hK (hkSrc k hkS)
  have hKtarget : IsCompact (F '' metricSourceCompactSet (I := I) Φ k K) :=
    hKsource.image F.continuous
  change metricDerivNormSupOn (I := I)
      (F '' metricSourceCompactSet (I := I) Φ k K) p
      ((g (j₀ + k)).restrictOpen (I := I) (U k))
      (gInf k) (gInf k) < ε
  exact hkConv k hkC _ hKtarget

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in



def chainCGConverges
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n)))
    [∀ n, Nonempty (U n)] [∀ n, SigmaCompactSpace (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hstep : ∀ n,
      let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
      ∀ (x : U n) (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
        ∀ l q : ℕ, q ≤ p → ∀ x : U n,
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) x ≤ ε)
    (O₀ : U 0) :
    let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
    let gSeq : ∀ n, SmoothRiemannianMetric I (U n) := fun n =>
      chainPullbackSeq (I := I) Ψ g (U n) (hU n) 0
    let hgInf : S.MetricCocycle gInf :=
      chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
    PointedRiemannianCGConverges (I := I)
      (factorSeq S O₀ gSeq) (limitPointedCoc S O₀ gInf hgInf) id
      (limitCGMapsOf S O₀ gSeq gInf hgInf) := by
  let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
  let gSeq : ∀ n, SmoothRiemannianMetric I (U n) := fun n =>
    chainPullbackSeq (I := I) Ψ g (U n) (hU n) 0
  let hgInf : S.MetricCocycle gInf :=
    chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
  apply limitCGConverges (I := I) S O₀ gSeq gInf hgInf
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := tail_derivSup_lt (I := I) j₀ U Ψ g hU gInf hclose ε hε p
  refine ⟨n₀, fun n hn K hK => ?_⟩
  simpa only [gSeq] using hn₀ n hn 0 K hK

omit [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [∀ j, IsRiemannianManifold I (M j)] in



def chainAmbientConv
    (j₀ : ℕ) (U : ∀ n, Opens (M (j₀ + n)))
    [∀ n, Nonempty (U n)] [∀ n, SigmaCompactSpace (U n)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hU : ∀ n k, (U n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) '' (U n : Set (M (j₀ + n))) ⊆
        (U (n + 1) : Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hstep : ∀ n,
      let F : U n → U (n + 1) := PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
      ∀ (x : U n) (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace (U n) := isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
        ∀ l q : ℕ, q ≤ p → ∀ x : U n,
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g (U n) (hU n) l)
            (gInf n) (gInf n) x ≤ ε)
    (O₀ : U 0) :
    let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
    let hgInf : S.MetricCocycle gInf :=
      chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
    PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ U S O₀ g)
      (limitPointedCoc S O₀ gInf hgInf) id
      (chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf) := by
  let S := chainBallSystem (I := I) j₀ U Ψ hU hmap
  let hgInf : S.MetricCocycle gInf :=
    chainMetricCocycle (I := I) j₀ U Ψ hU hmap gInf hstep
  apply ambientCGConverges (I := I) j₀ U S O₀ g gInf hgInf
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := tail_derivSup_lt (I := I) j₀ U Ψ g hU gInf hclose ε hε p
  refine ⟨n₀, fun n hn K hK => ?_⟩
  rw [← chainPullback_zero (I := I) Ψ g (U n) (hU n)]
  exact hn₀ n hn 0 K hK

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


def tailAmbientConv
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ : ℕ)
    (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k)))
    (hU : ∀ n k,
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source)
    (hmap : ∀ n,
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M (j₀ + (n + 1))) ''
          (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) : Set (M (j₀ + n))) ⊆
        (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :
          Set (M (j₀ + (n + 1)))))
    (gInf : ∀ n, SmoothRiemannianMetric I
      (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)))
    (hstep : ∀ n,
      let F : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n) →
          ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + (n + 1)) :=
        PartialDiffeomorph.opensMap
          (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1) (hU n 1) (hmap n)
      ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n))
        (v w : TangentSpace I x),
        (gInf n).inner x v w =
          (gInf (n + 1)).inner (F x)
            (mfderiv I I F x v) (mfderiv I I F x w))
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        letI : SigmaCompactSpace
            (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
          isSigmaCompact_iff_sigmaCompactSpace.mp
            (Geometry.isSigmaCompact_of_isOpen I
              (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)).isOpen)
        ∀ l q : ℕ, q ≤ p →
          ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n),
            metricDerivNorm (I := I) q
              (chainPullbackSeq (I := I) Ψ g
                (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) (hU n) l)
              (gInf n) (gInf n) x ≤ ε) :
    letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
    letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
    let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
    let gTail := tailMetric (I := I) b j₀ gInf
    let hgTail : S.MetricCocycle gTail :=
      tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
    PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S (tailCenter b j₀ 0) g)
      (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail) id
      (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail) := by
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g hnorm j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tailMetricCocycle (I := I) b Ψ hbase g hnorm j₀ D₀ hU hmap gInf hstep
  apply ambientCGConverges (I := I) j₀ (tailBallOpen b j₀) S
    (tailCenter b j₀ 0) g gTail hgTail
  exact tailFlatSup_lt (I := I) b j₀ Ψ g hU gInf hclose

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


def ballSystemOfData
    (b : ∀ j, M j) (r ε : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hε : ∀ j, 0 ≤ ε j)
    (p : ℕ → ℕ)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : ∀ j, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b j) (r j)) (ε j) (p j) (Ψ j) (g j) (g (j + 1)))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hgrow : ∀ j, Real.sqrt (1 + ε j) * r j < r (j + 1)) :
    letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
    SmoothSeqSystem I (fun j => ballOpen b r j) := by
  letI : ∀ j, Nonempty (ballOpen b r j) := fun j => ballOpen_nonempty b r j (hr j)
  have hsrc : ∀ j, (ballOpen b r j : Set (M j)) ⊆ (Ψ j).source := by
    intro j x hx
    apply (D j).source_sub
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le
  have hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (ballOpen b r j : Set (M j)) ⊆
      (ballOpen b r (j + 1) : Set (M (j + 1))) := by
    intro j
    have hdata : PreApproxIsoDataOn (I := I)
        (Metric.closedEBall (b j) (ENNReal.ofReal (r j))) (ε j) (p j)
        (Ψ j : M j → M (j + 1)) (g j) (g (j + 1)) := by
      rw [Metric.closedEBall_ofReal (hr j).le]
      exact (D j).forward
    have hsource : Metric.closedEBall (b j) (ENNReal.ofReal (r j)) ⊆ (Ψ j).source := by
      rw [Metric.closedEBall_ofReal (hr j).le]
      exact (D j).source_sub
    simpa only [ballOpen, hbase j] using
      (data_image_metric_ball (I := I) (Ψ j) (hnorm j) (hnorm (j + 1))
        (hr j) le_rfl (hε j) (hgrow j) hdata hsource)
  exact ballSystem b r hr Ψ hsrc hmap

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



noncomputable def directedBallSystem
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (hdata : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
      Nonempty (BookApproxIsoPartialData (I := I)
        (Metric.closedBall (b j) ((2 : ℝ) ^ j)) δ p
        (chainComp (I := I) (Mf := M) Ψ j l) (g j) (g (j + l)))) :
    Σ j₀ : ℕ,
      let b' : ∀ n, M (j₀ + n) := fun n => b (j₀ + n)
      let r' : ℕ → ℝ := fun n => (2 : ℝ) ^ (j₀ + n)
      letI : ∀ n, Nonempty (ballOpen b' r' n) :=
        fun n => ballOpen_nonempty b' r' n (by positivity)
      SmoothSeqSystem I (fun n => ballOpen b' r' n) := by
  classical
  let hex := hdata (1 / 2) (by norm_num) (by norm_num) 0
  let j₀ := Classical.choose hex
  have hj₀ := Classical.choose_spec hex
  refine ⟨j₀, ?_⟩
  let b' : ∀ n, M (j₀ + n) := fun n => b (j₀ + n)
  let r' : ℕ → ℝ := fun n => (2 : ℝ) ^ (j₀ + n)
  let Ψ' : ∀ n, PartialDiffeomorph I I (M (j₀ + n)) (M (j₀ + (n + 1)))
      (∞ : WithTop ℕ∞) := fun n =>
    chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1
  let g' : ∀ n, SmoothRiemannianMetric I (M (j₀ + n)) := fun n => g (j₀ + n)
  letI : ∀ n, Nonempty (ballOpen b' r' n) :=
    fun n => ballOpen_nonempty b' r' n (by dsimp [r']; positivity)
  have hD : ∀ n, Nonempty (BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b' n) (r' n)) (1 / 2) 0 (Ψ' n) (g' n) (g' (n + 1))) := by
    intro n
    simpa only [b', r', Ψ', g', Nat.add_assoc] using
      hj₀ (j₀ + n) (Nat.le_add_right j₀ n) 1
  let D : ∀ n, BookApproxIsoPartialData (I := I)
      (Metric.closedBall (b' n) (r' n)) (1 / 2) 0 (Ψ' n) (g' n) (g' (n + 1)) :=
    fun n => Classical.choice (hD n)
  have hbase' : ∀ n, (Ψ' n : M (j₀ + n) → M (j₀ + (n + 1))) (b' n) = b' (n + 1) := by
    intro n
    simpa only [Ψ', b', Nat.add_assoc] using
      chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1
  have hnorm' : ∀ n (x : M (j₀ + n)) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g' n).inner x v v)) := by
    intro n
    exact hnorm (j₀ + n)
  have hgrow : ∀ n, Real.sqrt (1 + (1 / 2 : ℝ)) * r' n < r' (n + 1) := by
    intro n
    have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
    calc
      Real.sqrt (1 + (1 / 2 : ℝ)) * r' n < 2 * r' n :=
        mul_lt_mul_of_pos_right hsqrt (by dsimp [r']; positivity)
      _ = r' (n + 1) := by
        dsimp [r']
        rw [show j₀ + (n + 1) = (j₀ + n) + 1 by omega]
        rw [pow_succ]
        ring
  exact ballSystemOfData b' r' (fun _ => 1 / 2) (fun n => by dsimp [r']; positivity)
    (fun _ => by norm_num) (fun _ => 0) Ψ' hbase' g' D hnorm' hgrow

end ApproxData

end HCGCompactness
end DifferentialGeometry
