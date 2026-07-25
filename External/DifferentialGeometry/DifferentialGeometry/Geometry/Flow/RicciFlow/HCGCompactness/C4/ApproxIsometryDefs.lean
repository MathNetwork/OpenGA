import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Metric.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder

set_option autoImplicit false
set_option linter.style.longLine false




















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]



section MapLevel

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]







structure PullbackMetricTensorData
    (Phi : M -> N) (h : SmoothRiemannianMetric I N) where
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))


noncomputable def metricTensorErrorNorm
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) g x 2
      (A x - Tensor0SBundle.metricTensorField (I := I) g x))





noncomputable def tensor02CovDeriv
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    A
    (fun a Aprev =>
      metricCovDerivStep (I := I) gRef a Aprev)


noncomputable def tensor02CovDerivNormWith
    (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (cov norm : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) norm x (a + 2)
      (tensor02CovDeriv (I := I) A cov a x))




structure PreApproxIsometryData
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  smooth : ContMDiff I I (∞ : WithTop ℕ∞) Phi
  pullbackData : PullbackMetricTensorData (I := I) Phi h
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullbackData.pullback g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullbackData.pullback g g x <= eps












structure BookApproxIsometryData
    (K : Set M) (L : Set N) (eps : Real) (p : Nat)
    (Phi : M ≃ₘ⟮I, I⟯ N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  forward : PreApproxIsometryData (I := I) K eps p (Phi : M -> N) g h
  reverse : PreApproxIsometryData (I := I) L eps p (Phi.symm : N -> M) h g







structure PreApproxIsoDataOn
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  smoothOn : ContMDiffOn I I (∞ : WithTop ℕ∞) Phi K
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, x ∈ K -> forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullback g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullback g g x <= eps







structure BookApproxIsoPartialData
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  source_sub : K ⊆ Phi.source
  forward : PreApproxIsoDataOn (I := I) K eps p (Phi : M -> N) g h
  reverse : PreApproxIsoDataOn (I := I) ((Phi : M -> N) '' K) eps p (Phi.symm : N -> M) h g







structure PreApproxIsoSep
    (K : Set M) (c0 cov : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  c0_nonneg : 0 <= c0
  cov_nonneg : 0 <= cov
  smoothOn : ContMDiffOn I I (∞ : WithTop ℕ∞) Phi K
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, x ∈ K -> forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullback g x <= c0
  cov_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullback g g x <= cov



def PreApproxIsoSep.toBook
    {K : Set M} {c0 cov eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoSep (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hc0 : c0 <= eps) (hcov : cov <= eps) :
    PreApproxIsoDataOn (I := I) K eps p Phi g h where
  eps_pos := heps0
  eps_lt_one := heps1
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := fun x hx => le_trans (D.c0_small x hx) hc0
  cov_deriv_small := fun a h1 h2 x hx =>
    le_trans (D.cov_small a h1 h2 x hx) hcov


structure BookApproxIsoSep
    (K : Set M) (c0 cov : Real) (p : Nat)
    (Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  source_sub : K ⊆ Phi.source
  forward : PreApproxIsoSep (I := I) K c0 cov p (Phi : M -> N) g h
  reverse : PreApproxIsoSep (I := I) ((Phi : M -> N) '' K) c0 cov p (Phi.symm : N -> M) h g



def BookApproxIsoSep.toBook
    {K : Set M} {c0 cov eps : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoSep (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hc0 : c0 <= eps) (hcov : cov <= eps) :
    BookApproxIsoPartialData (I := I) K eps p Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toBook heps0 heps1 hc0 hcov
  reverse := D.reverse.toBook heps0 heps1 hc0 hcov



def PreApproxIsoDataOn.toSep
    {K : Set M} {eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoDataOn (I := I) K eps p Phi g h) :
    PreApproxIsoSep (I := I) K eps eps p Phi g h where
  c0_nonneg := le_of_lt D.eps_pos
  cov_nonneg := le_of_lt D.eps_pos
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := D.c0_small
  cov_small := D.cov_deriv_small



def BookApproxIsoPartialData.toSep
    {K : Set M} {eps : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoPartialData (I := I) K eps p Phi g h) :
    BookApproxIsoSep (I := I) K eps eps p Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toSep
  reverse := D.reverse.toSep


def PreApproxIsoSep.mono
    {K K' : Set M} {c0 c0' cov cov' : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoSep (I := I) K c0 cov p Phi g h)
    (hK : K' ⊆ K) (hc0 : c0 <= c0') (hcov : cov <= cov') :
    PreApproxIsoSep (I := I) K' c0' cov' p Phi g h where
  c0_nonneg := le_trans D.c0_nonneg hc0
  cov_nonneg := le_trans D.cov_nonneg hcov
  smoothOn := D.smoothOn.mono hK
  pullback := D.pullback
  pullback_apply := fun x hx v => D.pullback_apply x (hK hx) v
  c0_small := fun x hx => le_trans (D.c0_small x (hK hx)) hc0
  cov_small := fun a h1 h2 x hx =>
    le_trans (D.cov_small a h1 h2 x (hK hx)) hcov


def BookApproxIsoSep.mono
    {K K' : Set M} {c0 c0' cov cov' : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoSep (I := I) K c0 cov p Phi g h)
    (hK : K' ⊆ K) (hc0 : c0 <= c0') (hcov : cov <= cov') :
    BookApproxIsoSep (I := I) K' c0' cov' p Phi g h where
  source_sub := fun _ hx => D.source_sub (hK hx)
  forward := D.forward.mono hK hc0 hcov
  reverse := D.reverse.mono (Set.image_mono hK) hc0 hcov

end MapLevel









structure IsApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  uniform_equiv : MetricUniformEquivalentOn (I := I) K g h (1 + eps)
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        metricCovDerivNorm (I := I) a h g x <= eps



structure IsTwoSidedApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  forward : IsApproxIsometryOn (I := I) K eps p g h
  reverse_cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        metricCovDerivNorm (I := I) a g h x <= eps

omit [SigmaCompactSpace M] in
theorem IsTwoSidedApproxIsometryOn.toApprox
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h) :
    IsApproxIsometryOn (I := I) K eps p g h :=
  Happrox.forward



noncomputable def metricCovDerivNormWith
    (a : Nat) (h cov norm : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) norm x (a + 2)
      (metricCovDeriv (I := I) h cov a x))









def ConnDiffFieldRealizes
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M)
    (D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2) : Prop :=
  forall x : M,
    D x =
      Tensor0SBundle.connectionDifferenceTensorAt
        (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h) x



noncomputable def connDiffDerivNorm
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2))
    (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) 1 (k + 2) (Dk x))



def ConnDiffDerivRealizes
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2)) : Prop :=
  exists D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2,
    ConnDiffFieldRealizes (I := I) g h D ∧
      Tensor0SBundle.HigherCovDerivRSRealizes
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h) D k Dk





def ConnDiffDerivBoundOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) :
    Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C



def ConnDiffEpsBoundOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) : Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C * eps


def ConnDiffEpsBoundsBelow
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) : Prop :=
  forall k : Nat, k < m ->
    ConnDiffEpsBoundOn (I := I) K eps g h k (C k)



def connDiffOneConst (Idx : Type*) [Fintype Idx] : Real :=
  let n : Real := Fintype.card Idx
  let q : Real := n * (((n * (n * 8)) * (3 * 8))) + n * (3 * 16)
  Real.sqrt
    ((Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 3 -> Idx) : Real) * q ^ 2))



def connDiffTwoConst (Idx : Type*) [Fintype Idx] : Real :=
  let n : Real := Fintype.card Idx
  let Q0 : Real := n * (n * 8)
  let R0 : Real := n * (n * (16 + Q0 * 8 + Q0 * 8))
  let q : Real :=
    n * (Q0 * (3 * 16) + R0 * (3 * 8)) +
      n * (3 * 32 + Q0 * (3 * 16))
  Real.sqrt
    ((Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 4 -> Idx) : Real) * q ^ 2))



def connDiffEpsConst_two
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace Real E]
    [Module.Finite Real E] : Nat -> Real
  | 0 => 12
  | _ + 1 => connDiffOneConst (Fin (Module.finrank Real E))



def connDiffEpsConst_three
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace Real E]
    [Module.Finite Real E] : Nat -> Real
  | 0 => 12
  | 1 => connDiffOneConst (Fin (Module.finrank Real E))
  | _ => connDiffTwoConst (Fin (Module.finrank Real E))


def connDiffCoeff (eps : Real) : Real :=
  (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)

end FixedDomain

end HCGCompactness
end DifferentialGeometry
