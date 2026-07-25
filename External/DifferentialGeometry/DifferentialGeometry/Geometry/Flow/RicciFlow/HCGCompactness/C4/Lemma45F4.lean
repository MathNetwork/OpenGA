import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.Lemma45Covariant
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.Lemma45Intrinsic
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBoundGoodFrame

set_option autoImplicit false
set_option linter.style.longLine false



















universe u

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open Bundle DifferentialGeometry.Integral.Connection Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]



noncomputable def lemma45CorConst (q₂ p : ℕ) : Real :=
  lemma45Const
    (fun c => claim1MulConst
      (Real.sqrt (Module.finrank Real E) * 2)
      (|(1 / 2 : Real)| + |(1 / 2 : Real)| + |-(1 / 2 : Real)|)
      (4 ^ (2 + p)) c)
    p q₂


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem corConst_nonneg (q₂ p : ℕ) : 0 ≤ lemma45CorConst (E := E) q₂ p := by
  apply lemma45Const_nonneg
  intro c
  exact claim1MulConst_nonneg (by positivity : (0 : Real) ≤ 4 ^ (2 + p)) c



omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lemma45_corII_bound
    {q₂ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q₂)
    (p : ℕ) (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + eps) * gRef.inner x v v)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) :
    ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
          (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt ((1 + eps) ^ (q₂ + r)) *
          (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
              (iterCov (I := I) gRef q₂ T r x)) +
            eps * lemma45CorConst (E := E) q₂ p * ∑ k ∈ Finset.range r,
              Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                (iterCov (I := I) gRef q₂ T k x))) := by
  classical
  intro x hx r hr0 hrp
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x
  obtain ⟨basisE, u', η, hu', hxu', hsub, hη0, hsmall, hnear, hON, hcomp, _⟩ :=
    exists_goodFrame_compBound (I := I) g x
  let frame : Fin (Module.finrank Real E) → (y : M) → TangentSpace I y :=
    fun a y => e₀.localFrame basisE a y
  let w : Set M := u' ∩ u
  have hwopen : IsOpen w := hu'.inter hu
  have hxw : x ∈ w := ⟨hxu', hx⟩
  have hwsub : w ⊆ e₀.baseSet := fun _ hz => hsub hz.1
  let hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame w :=
    (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub
  have hframeS : ∀ d : Fin (Module.finrank Real E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) w :=
    fun d => (frame_e_mdiffOn e₀ basisE d).mono hwsub
  have hchrG : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        frame hframe y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ g basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hchrH : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ gRef basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hgsm := fun k => (gCompField_mdiffOn e₀ g basisE k).mono hwsub
  have hTsm := fun k => (tensorComp_mdiffOn e₀ T basisE k).mono hwsub
  let C0 : Real := Real.sqrt (Module.finrank Real E) * 2
  have hGinv : ∀ z ∈ w, compL2 (ginvCompField (I := I) e₀ g basisE z) ≤ C0 := by
    intro z hz
    have h := movingGinv_le (I := I) e₀ g g basisE 1 zero_lt_one
      (fun v => by simp) η hη0 hsmall (fun i j => hnear z hz.1 i j)
    simpa only [C0, Fintype.card_fin, mul_one] using h
  have hinv : ∀ z ∈ w, ∀ c e : Fin (Module.finrank Real E),
      (∑ l, frameComp0S (I := I) (metricTensorField (I := I) g) frame z
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE z (Fin.snoc (fun _ : Fin 1 => e) l)) =
          if c = e then 1 else 0 :=
    fun z hz c e => ginv_hinv (I := I) e₀ g basisE (hwsub hz) c e
  let L : Real := 4 ^ (2 + p)
  have hL0 : 0 ≤ L := by positivity
  have hgKcomp : ∀ z ∈ w, ∀ j, 1 ≤ j → j ≤ p →
      compL2 (iterCovComp (I := I) frame
        (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y)
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j z) ≤ L * eps := by
    intro z hz j _ hjp
    exact metricComp_mul (I := I) g gRef frame hframe hwopen hz
      (fun s A => hcomp z (hwsub hz) hz.1 s A)
      (1 + eps) (by linarith) (by linarith)
      (hequiv z hz.2) p j hjp heps0 (hgK z hz.2 j (by omega) hjp)
  have hcompF3 := lemma45_F3_bound hwopen g gRef frame hframe hframeS hchrG hchrH
    hgsm (frameComp0S (I := I) T frame) hTsm
    (ginvCompField (I := I) e₀ g basisE) hinv C0 L eps hL0 heps0 heps1 hGinv p hgKcomp
  have hON' : ∀ i j : Fin (Module.finrank Real E),
      g.inner x (hframe.toBasisAt hxw i) (hframe.toBasisAt hxw j) =
        if i = j then 1 else 0 := by
    intro i j
    simpa only [IsLocalFrameOn.toBasisAt_coe] using hON i j
  have hinvON := metricInverseInBasis_of_orthonormal (I := I) g
    (hframe.toBasisAt hxw) hON'
  have hF3 : ∀ s : ℕ, 0 < s → s ≤ p →
      Real.sqrt (normSq0S (I := I) g x (q₂ + s) (iterCov (I := I) g q₂ T s x)) ≤
        Real.sqrt (normSq0S (I := I) g x (q₂ + s) (iterCov (I := I) gRef q₂ T s x)) +
        eps * lemma45CorConst (E := E) q₂ p * ∑ k ∈ Finset.range s,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := by
    intro s hs0 hsp
    apply hF3_term hwopen g gRef T frame hframe hxw hinvON eps
      (lemma45CorConst (E := E) q₂ p) s
    simpa only [lemma45CorConst, C0, L] using hcompF3 x hxw s hs0 hsp
  exact lemma45_cor_II_of_intrinsic g gRef T p (x := x) (C := 1 + eps)
    (by linarith) (hequiv x hx) eps (lemma45CorConst (E := E) q₂ p) heps0
    (corConst_nonneg (E := E) q₂ p) hF3 r hr0 hrp










omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lemma45_corII
    {q₂ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q₂)
    (p : ℕ) (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + eps) * gRef.inner x v v)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) :
    ∃ Cc : Real, 0 ≤ Cc ∧ ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
          (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt ((1 + eps) ^ (q₂ + r)) *
          (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
              (iterCov (I := I) gRef q₂ T r x)) +
            eps * Cc * ∑ k ∈ Finset.range r,
              Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                (iterCov (I := I) gRef q₂ T k x))) := by
  refine ⟨lemma45CorConst (E := E) q₂ p, corConst_nonneg (E := E) q₂ p, ?_⟩
  exact lemma45_corII_bound hu g gRef T p eps heps0 heps1 hequiv hgK








omit [I.Boundaryless] in
theorem lemma45_corII_unif (q₂ p : ℕ) :
    ∃ Cc : Real, 0 ≤ Cc ∧
      ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
        [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
        [IsManifold I 1 M'] [IsManifold I 2 M']
        [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
        {u : Set M'} (_ : IsOpen u)
        (g gRef : SmoothRiemannianMetric I M')
        (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) q₂)
        (eps : Real), 0 ≤ eps → eps ≤ 1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
            g.inner x v v ≤ (1 + eps) * gRef.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
            (iterCov (I := I) gRef 2
              (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) →
        ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
              (iterCov (I := I) g q₂ T r x)) ≤
            Real.sqrt ((1 + eps) ^ (q₂ + r)) *
              (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
                  (iterCov (I := I) gRef q₂ T r x)) +
                eps * Cc * ∑ k ∈ Finset.range r,
                  Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                    (iterCov (I := I) gRef q₂ T k x))) := by
  refine ⟨lemma45CorConst (E := E) q₂ p, corConst_nonneg (E := E) q₂ p, ?_⟩
  intro M' instTop instChart instT2 instMan instSigma instMan1 instMan2 instManSucc
    u hu g gRef T eps heps0 heps1 hequiv hgK
  exact lemma45_corII_bound hu g gRef T p eps heps0 heps1 hequiv hgK

end HCGCompactness
end DifferentialGeometry
