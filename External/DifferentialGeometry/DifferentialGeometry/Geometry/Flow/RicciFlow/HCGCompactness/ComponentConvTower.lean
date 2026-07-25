import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergenceDeriv

set_option autoImplicit false
set_option linter.style.longLine false





















noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle TensorLieDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]



omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem chartRep_towerScalar_contDiffOn
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)))
      (extChartAt I x₀).target := by
  intro z hz
  have hy : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hz
  have hzeq : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hz
  have hcd := contDiffAt_chartRep (I := I)
    (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w))
    (covDerivOfField_eval_contMDiff (I := I) gRef A0 p V) x₀ hy
  rw [hzeq] at hcd
  exact hcd.contDiffWithinAt





omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTowerScalar_contDiff
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target) :
    ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) z) :=
  bumpMul_contDiff (isOpen_extChartAt_target (I := I) x₀) hχ htsupp
    (chartRep_towerScalar_contDiffOn (I := I) gRef A0 p V x₀)







omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpFderiv_eq_chartTowerStep
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) (v : E)
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {Kc : Set M}
    (hσ : ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x)
    (hKchart : Kc ⊆ (chartAt H x₀).source)
    {χ : E → Real} {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {z : E} (hz : z ∈ U) :
    fderiv Real (fun z' : E => χ z' * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) z') z v
      = χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (towerStep (I := I) gRef A0 p V σ) z := by
  set f : E → Real := writtenInExtChartAt I 𝓘(Real, Real) x₀
    (fun w : M => (covDerivOfField (I := I) gRef A0 p) w (fun a => V a w)) with hf
  have hztarget : z ∈ (extChartAt I x₀).target := hUtarget hz
  have hsymm : extChartAt I x₀ ((extChartAt I x₀).symm z) = z :=
    (extChartAt I x₀).right_inv hztarget
  have hbumpeq : (fun z' : E => χ z' * f z') =ᶠ[nhds z] f := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [hχU hw]; simp
  have hfd : fderiv Real (fun z' : E => χ z' * f z') z = fderiv Real f z :=
    hbumpeq.fderiv_eq
  have hgerm := fderiv_chartRep_eq_towerStep (I := I) gRef A0 p V x₀ v σ hσ hKchart
    (hUKc z hz)
  rw [hsymm] at hgerm
  have hval : fderiv Real f z v =
      writtenInExtChartAt I 𝓘(Real, Real) x₀ (towerStep (I := I) gRef A0 p V σ) z :=
    hgerm.eq_of_nhds
  rw [show fderiv Real (fun z' : E => χ z' * f z') z v = fderiv Real f z v from by rw [hfd]]
  rw [hval, hχU hz]
  simp





omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTowerStep_chartConv
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) (v : E)
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {Kc : Set M}
    (hσ : ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x)
    (hKchart : Kc ⊆ (chartAt H x₀).source)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    (hconv : MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef (A0Seq k) p V σ) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef A0inf p V σ) z) := by
  have hB2 := hconv.fderivApply
    (fun k => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p V x₀ hχ htsupp)
    (bumpTowerScalar_contDiff (I := I) gRef A0inf p V x₀ hχ htsupp) v
  refine hB2.congr hU (fun k z hz => ?_) (fun z hz => ?_)
  · exact (bumpFderiv_eq_chartTowerStep (I := I) gRef (A0Seq k) p V x₀ v σ hσ hKchart
      hU hχU hUKc hUtarget hz).symm
  · exact (bumpFderiv_eq_chartTowerStep (I := I) gRef A0inf p V x₀ v σ hσ hKchart
      hU hχU hUKc hUtarget hz).symm





omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem chartRep_contDiffOn (f : M → Real) (x₀ : M)
    (hf : ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f (chartAt H x₀).source) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (extChartAt I x₀).target := by
  have hsymm : ContMDiffOn 𝓘(Real, E) I (∞ : WithTop ℕ∞)
      (extChartAt I x₀).symm (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
  have hmaps : Set.MapsTo (extChartAt I x₀).symm (extChartAt I x₀).target
      (chartAt H x₀).source := by
    intro z hz
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hz
  have hcomp : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target := hf.comp hsymm hmaps
  have hcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target :=
    contMDiffOn_iff_contDiffOn.mp hcomp
  have hwrite : writtenInExtChartAt I 𝓘(Real, Real) x₀ f
      = f ∘ (extChartAt I x₀).symm := by funext z; simp [writtenInExtChartAt]
  rw [hwrite]; exact hcd

set_option linter.unusedVariables false in








omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTower_slotExpand_conv
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ) (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (c : ι → M → Real)
    (hc : ∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
      (chartAt H x₀).source)
    (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (j : Fin (p + 2))
    {S : Set M} (hUS : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ S)
    (hexpand : ∀ w ∈ S, (V j) w = ∑ i ∈ s, c i w • frame i w)
    (hconv : ∀ i, MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w
          (fun a => (Function.update V j (frame i)) a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w
          (fun a => (Function.update V j (frame i)) a w)) z)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z) := by
  classical

  have hg : ∀ i, ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀ (c i) z) :=
    fun i => bumpMul_contDiff (isOpen_extChartAt_target (I := I) x₀) hχ htsupp
      (chartRep_contDiffOn (I := I) (c i) x₀ (hc i))

  have hcarrSeq : ∀ (i : ι) (k : ℕ), ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w
          (fun a => (Function.update V j (frame i)) a w)) z) :=
    fun i k => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p
      (Function.update V j (frame i)) x₀ hχ htsupp
  have hcarrInf : ∀ i : ι, ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w
          (fun a => (Function.update V j (frame i)) a w)) z) :=
    fun i => bumpTowerScalar_contDiff (I := I) gRef A0inf p
      (Function.update V j (frame i)) x₀ hχ htsupp

  have hsum := MapCInfConvOnCompacts.sum s
    (fun i => (hconv i).mulLeft (hg i) (fun k => hcarrSeq i k) (hcarrInf i))
    (fun i k => (hg i).mul (hcarrSeq i k)) (fun i => (hg i).mul (hcarrInf i))

  have hmulti : ∀ (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2),
      ∀ q ∈ S,
      (covDerivOfField (I := I) gRef A0 p) q (fun a => V a q)
        = ∑ i ∈ s, c i q •
            (covDerivOfField (I := I) gRef A0 p) q
              (fun a => (Function.update V j (frame i)) a q) := by
    intro A0 q hq
    have hupd : ∀ i : ι,
        Function.update (fun a => V a q) j (frame i q)
          = fun a => (Function.update V j (frame i)) a q := by
      intro i
      funext a
      by_cases h : a = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    have hstep1 : (fun a => V a q)
        = Function.update (fun a => V a q) j (∑ i ∈ s, c i q • frame i q) := by
      rw [← hexpand q hq]
      exact (Function.update_eq_self j (fun a => V a q)).symm
    calc
      (covDerivOfField (I := I) gRef A0 p) q (fun a => V a q)
          = (covDerivOfField (I := I) gRef A0 p) q
              (Function.update (fun a => V a q) j (∑ i ∈ s, c i q • frame i q)) := by
            rw [← hstep1]
      _ = ∑ i ∈ s, c i q * (covDerivOfField (I := I) gRef A0 p) q
              (Function.update (fun a => V a q) j (frame i q)) := by
            simpa using ((covDerivOfField (I := I) gRef A0 p) q).toMultilinearMap.map_update_sum
              s j (fun i => c i q • frame i q) (fun a => V a q)
      _ = ∑ i ∈ s, c i q • (covDerivOfField (I := I) gRef A0 p) q
              (fun a => (Function.update V j (frame i)) a q) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [smul_eq_mul, hupd i]

  refine hsum.congr hU (fun k z hz => ?_) (fun z hz => ?_)
  · have hχz : χ z = 1 := (hχU hz).trans (Pi.one_apply z)
    simp only [writtenInExtChartAt_real_apply, hχz, one_mul]
    rw [hmulti (A0Seq k) ((extChartAt I x₀).symm z) (hUS z hz)]
    simp only [smul_eq_mul]
  · have hχz : χ z = 1 := (hχU hz).trans (Pi.one_apply z)
    simp only [writtenInExtChartAt_real_apply, hχz, one_mul]
    rw [hmulti A0inf ((extChartAt I x₀).symm z) (hUS z hz)]
    simp only [smul_eq_mul]







omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTowerStep_split
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V' : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x₀ : M) (χ : E → Real) (z : E) :
    χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z
      = χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (towerStep (I := I) gRef A0 p V' σ) z
        - ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
              (fun b => (Function.update V' a
                (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                    (I := I) gRef) σ (V' a))) b w)) z := by
  simp only [writtenInExtChartAt_real_apply, towerStep]
  set q : M := (extChartAt I x₀).symm z with hq
  have hupd : ∀ a : Fin (p + 2),
      (fun b : Fin (p + 2) =>
          (Function.update V' a
            (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                (I := I) gRef) σ (V' a))) b q)
        = Function.update (fun b : Fin (p + 2) => V' b q) a
            (((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun r : M => V' a r) q) (σ q)) := by
    intro a
    funext b
    by_cases h : b = a
    · subst h; simp [covSection_apply]
    · simp [Function.update_of_ne h]
  simp only [hupd]
  rw [mul_add, Finset.mul_sum]
  ring





omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTowerStepScalar_contDiff
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ)
    (V' : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x₀ : M) {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target) :
    ContDiff Real (∞ : WithTop ℕ∞)
      (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef A0 p V' σ) z) := by
  have heq : (fun z : E => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (towerStep (I := I) gRef A0 p V' σ) z)
      = (fun z : E =>
          (χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
              (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
          + ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef A0 p) w
                (fun b => (Function.update V' a
                  (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
                    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
                      (I := I) gRef) σ (V' a))) b w)) z) := by
    funext z
    have h := bumpTowerStep_split (I := I) gRef A0 p V' σ x₀ χ z
    linarith [h]
  rw [heq]
  have hcons :
      (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w)))
        = (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
            (fun a : Fin (p + 3) =>
              (Fin.cons σ V' : Fin (p + 3) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M → Type _)) a w)) := by
    funext w
    congr 1
    funext a
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  refine ContDiff.add ?_ (ContDiff.sum fun a _ => ?_)
  · rw [hcons]
    exact bumpTowerScalar_contDiff (I := I) gRef A0 (p + 1) (Fin.cons σ V') x₀ hχ htsupp
  · exact bumpTowerScalar_contDiff (I := I) gRef A0 p
      (Function.update V' a
        (covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) gRef)
          σ (V' a))) x₀ hχ htsupp








omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTowerCons_conv
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ) (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {Kc : Set M} (hKchart : Kc ⊆ (chartAt H x₀).source)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    (v : E) (σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hσ : ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ v x)
    (V' : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (IH : ∀ (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z) := by
  classical
  set corrSec : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun a => covSection (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) gRef)
      σ (V' a) with hcorrSec
  have hTS := bumpTowerStep_chartConv (I := I) gRef A0Seq A0inf p V' x₀ v σ hσ hKchart
    hχ htsupp hU hχU hUKc hUtarget (IH V')
  have hSumCorr := MapCInfConvOnCompacts.sum (Finset.univ : Finset (Fin (p + 2)))
    (fun a => IH (Function.update V' a (corrSec a)))
    (fun a k => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
    (fun a => bumpTowerScalar_contDiff (I := I) gRef A0inf p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
  have hsub := hTS.sub hSumCorr
    (fun k => bumpTowerStepScalar_contDiff (I := I) gRef (A0Seq k) p V' σ x₀ hχ htsupp)
    (bumpTowerStepScalar_contDiff (I := I) gRef A0inf p V' σ x₀ hχ htsupp)
    (fun k => ContDiff.sum fun a _ => bumpTowerScalar_contDiff (I := I) gRef (A0Seq k) p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
    (ContDiff.sum fun a _ => bumpTowerScalar_contDiff (I := I) gRef A0inf p
      (Function.update V' a (corrSec a)) x₀ hχ htsupp)
  have hfeq_seq : (fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
      = fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (towerStep (I := I) gRef (A0Seq k) p V' σ) z
          - ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w
                (fun b => (Function.update V' a (corrSec a)) b w)) z := by
    funext k z
    exact bumpTowerStep_split (I := I) gRef (A0Seq k) p V' σ x₀ χ z
  have hfeq_inf : (fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
          (Fin.cons (σ w) (fun a : Fin (p + 2) => V' a w))) z)
      = fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (towerStep (I := I) gRef A0inf p V' σ) z
          - ∑ a : Fin (p + 2), χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
              (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w
                (fun b => (Function.update V' a (corrSec a)) b w)) z := by
    funext z
    exact bumpTowerStep_split (I := I) gRef A0inf p V' σ x₀ χ z
  rw [hfeq_seq, hfeq_inf]
  exact hsub






omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTowerCarrier_step
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (p : ℕ) (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {Kc : Set M} (hKchart : Kc ⊆ (chartAt H x₀).source)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (vbasis : ι → E)
    (hframeσ : ∀ i, ∀ᶠ x in 𝓝ˢ Kc,
      frame i x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (vbasis i) x)
    (hspan : ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        ∃ c : ι → M → Real,
          (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
            (chartAt H x₀).source)
          ∧ ∀ w ∈ Kc, W0 w = ∑ i ∈ s, c i w • frame i w)
    (IH : ∀ (V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) p) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf p) w (fun a => V a w)) z))
    (W : Fin (p + 3) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w (fun a => W a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w (fun a => W a w)) z) := by
  classical
  obtain ⟨c, hc, hexpand⟩ := hspan (W 0)
  refine bumpTower_slotExpand_conv (I := I) gRef A0Seq A0inf (p + 1) x₀ hχ htsupp
    hU hχU hUtarget s frame c hc W 0 hUKc hexpand ?_
  intro i
  have hslot : ∀ (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2),
      (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
          (fun a => (Function.update W 0 (frame i)) a w))
        = (fun w : M => (covDerivOfField (I := I) gRef A0 (p + 1)) w
            (Fin.cons (frame i w) (fun a : Fin (p + 2) => (Fin.tail W) a w))) := by
    intro A0
    funext w
    congr 1
    funext a
    refine Fin.cases ?_ (fun j => ?_) a
    · simp
    · simp [Fin.tail]
  have hbr_seq : (fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
          (fun a => (Function.update W 0 (frame i)) a w)) z)
      = fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) (p + 1)) w
            (Fin.cons (frame i w) (fun a : Fin (p + 2) => (Fin.tail W) a w))) z := by
    funext k z
    rw [hslot (A0Seq k)]
  have hbr_inf : (fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
          (fun a => (Function.update W 0 (frame i)) a w)) z)
      = fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef A0inf (p + 1)) w
            (Fin.cons (frame i w) (fun a : Fin (p + 2) => (Fin.tail W) a w))) z := by
    funext z
    rw [hslot A0inf]
  rw [hbr_seq, hbr_inf]
  exact bumpTowerCons_conv (I := I) gRef A0Seq A0inf p x₀ hχ htsupp hU hχU hUtarget
    hKchart hUKc (vbasis i) (frame i) (hframeσ i) (Fin.tail W) IH





omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem bumpTowerCarrier_all
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {Kc : Set M} (hKchart : Kc ⊆ (chartAt H x₀).source)
    (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (vbasis : ι → E)
    (hframeσ : ∀ i, ∀ᶠ x in 𝓝ˢ Kc,
      frame i x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (vbasis i) x)
    (hspan : ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        ∃ c : ι → M → Real,
          (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
            (chartAt H x₀).source)
          ∧ ∀ w ∈ Kc, W0 w = ∑ i ∈ s, c i w • frame i w)
    (hbase : ∀ (V : Fin (0 + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w (fun a => V a w)) z)) :
    ∀ (a : ℕ) (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        MapCInfConvOnCompacts U
          (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) a) w (fun a => V a w)) z)
          (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef A0inf a) w (fun a => V a w)) z) := by
  intro a
  induction a with
  | zero => exact hbase
  | succ p IH =>
    exact bumpTowerCarrier_step (I := I) gRef A0Seq A0inf p x₀ hχ htsupp hU hχU hUtarget
      hKchart hUKc s frame vbasis hframeσ hspan IH









omit [CompleteSpace E] [I.Boundaryless] in
theorem exists_frameData (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) :
    ∃ (frame : Fin (Module.finrank Real E) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _))
      (vbasis : Fin (Module.finrank Real E) → E),
      (∀ i, ∀ᶠ x in 𝓝ˢ Kc,
        frame i x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (vbasis i) x)
      ∧ ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
          ∃ c : Fin (Module.finrank Real E) → M → Real,
            (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
              (chartAt H x₀).source)
            ∧ ∀ w ∈ Kc, W0 w = ∑ i : Fin (Module.finrank Real E), c i w • frame i w := by
  classical
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀ with he
  set b := Module.finBasis Real E with hb
  have hbase : e.baseSet = (chartAt H x₀).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := Real) (I := I) x₀
  have hσex : ∀ i : Fin (Module.finrank Real E),
      ∃ σ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ∀ᶠ x in 𝓝ˢ Kc, σ x = tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) x :=
    fun i => exists_section_eqOn_compact (I := I) x₀ (b i) hKc hKchart
  choose frame hframeσ using hσex
  refine ⟨frame, b, hframeσ, fun W0 => ⟨fun i w => e.localFrame_coeff I b i w (W0 w), ?_, ?_⟩⟩
  · intro i
    rw [← hbase]
    exact contMDiffOn_baseSet_localFrame_coeff b W0.contMDiff.contMDiffOn i
  · intro w hw
    have hwbase : w ∈ e.baseSet := by rw [hbase]; exact hKchart hw
    have hexp := e.eq_sum_localFrame_coeff_smul (I := I) (b := b)
      (s := (W0 : ∀ x : M, TangentSpace I x)) hwbase
    rw [hexp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hframe_eq : frame i w = tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) w :=
      (hframeσ i).self_of_nhdsSet w hw
    have hlf_eq : e.localFrame b i w = tangentConstInChart (𝕜 := Real) (I := I) x₀ (b i) w := by
      rw [e.localFrame_apply_of_mem_baseSet b hwbase]
      simp [Bundle.Trivialization.basisAt, tangentConstInChart_apply, he]
    change e.localFrame_coeff I b i w (W0 w) • e.localFrame b i w
        = e.localFrame_coeff I b i w (W0 w) • frame i w
    rw [hlf_eq, hframe_eq]







omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem hbase_of_framePairs
    (gRef : SmoothRiemannianMetric I M)
    (A0Seq : ℕ → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (A0inf : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M)
    {χ : E → Real} (hχ : ContDiff Real (∞ : WithTop ℕ∞) χ)
    (htsupp : tsupport χ ⊆ (extChartAt I x₀).target)
    {U : Set E} (hU : IsOpen U) (hχU : Set.EqOn χ 1 U)
    (hUtarget : U ⊆ (extChartAt I x₀).target)
    {Kc : Set M} (hUKc : ∀ z ∈ U, (extChartAt I x₀).symm z ∈ Kc)
    {ι : Type*} (s : Finset ι)
    (frame : ι → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hspan : ∀ (W0 : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
        ∃ c : ι → M → Real,
          (∀ i, ContMDiffOn I 𝓘(Real, Real) (∞ : WithTop ℕ∞) (c i)
            (chartAt H x₀).source)
          ∧ ∀ w ∈ Kc, W0 w = ∑ i ∈ s, c i w • frame i w)
    (hpairs : ∀ (i j : ι), MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w
          (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z))
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    MapCInfConvOnCompacts U
      (fun k z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w (fun a => V a w)) z)
      (fun z => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w (fun a => V a w)) z) := by
  classical
  obtain ⟨c0, hc0, hexp0⟩ := hspan (V 0)
  refine bumpTower_slotExpand_conv (I := I) gRef A0Seq A0inf 0 x₀ hχ htsupp
    hU hχU hUtarget s frame c0 hc0 V 0 hUKc hexp0 ?_
  intro i
  obtain ⟨c1, hc1, hexp1⟩ := hspan (V 1)
  have hexp1' : ∀ w ∈ Kc, (Function.update V 0 (frame i)) 1 w = ∑ j ∈ s, c1 j w • frame j w := by
    intro w hw
    rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    exact hexp1 w hw
  refine bumpTower_slotExpand_conv (I := I) gRef A0Seq A0inf 0 x₀ hχ htsupp
    hU hχU hUtarget s frame c1 hc1 (Function.update V 0 (frame i)) 1 hUKc hexp1' ?_
  intro j
  have hbridge : ∀ (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2),
      (fun w : M => (covDerivOfField (I := I) gRef A0 0) w
          (fun a => (Function.update (Function.update V 0 (frame i)) 1 (frame j)) a w))
        = (fun w : M => (covDerivOfField (I := I) gRef A0 0) w
            (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) := by
    intro A0
    funext w
    congr 1
    funext a
    fin_cases a <;>
      simp [Function.update_of_ne, Function.update_self]
  have hbr_seq : (fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w
          (fun a => (Function.update (Function.update V 0 (frame i)) 1 (frame j)) a w)) z)
      = fun (k : ℕ) (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef (A0Seq k) 0) w
            (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z := by
    funext k z; rw [hbridge (A0Seq k)]
  have hbr_inf : (fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
        (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w
          (fun a => (Function.update (Function.update V 0 (frame i)) 1 (frame j)) a w)) z)
      = fun (z : E) => χ z * writtenInExtChartAt I 𝓘(Real, Real) x₀
          (fun w : M => (covDerivOfField (I := I) gRef A0inf 0) w
            (fun a => (Function.update (fun _ : Fin 2 => frame i) 1 (frame j)) a w)) z := by
    funext z; rw [hbridge A0inf]
  rw [hbr_seq, hbr_inf]
  exact hpairs i j







omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem engine_input_family
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (x₀ : M)
    {ι : Type*}
    (Vfam : ι → Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (hcomp : ∀ (p : ι) (r : ℕ) {Kc : Set M}, IsCompact Kc →
      Kc ⊆ (chartAt H x₀).source →
      ∃ Mr : Real, 0 ≤ Mr ∧ ∀ k : ℕ, ∀ y ∈ Kc,
        ‖iteratedFDeriv Real r (writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => Vfam p a w))) (extChartAt I x₀ y)‖ ≤ Mr)
    {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source) :
    ∃ (χ : E → Real),
      ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ p : ι,
        (∀ k : ℕ, ContDiff Real (∞ : WithTop ℕ∞)
          (fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => Vfam p a w)) x)) ∧
        (∀ r : ℕ, ∃ Mr : Real, ∀ k : ℕ, ∀ x : E,
          ‖iteratedFDeriv Real r (fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => Vfam p a w)) x) x‖ ≤ Mr) := by
  classical
  haveI : NormalSpace E := inferInstance
  haveI : LocallyCompactSpace E := inferInstance
  set tgt := (extChartAt I x₀).target with htgt
  have htgt_open : IsOpen tgt := isOpen_extChartAt_target (I := I) x₀
  set EK₀ : Set E := extChartAt I x₀ '' K₀ with hEK₀
  have hEK₀cpt : IsCompact EK₀ :=
    hK₀.image_of_continuousOn ((continuousOn_extChartAt (I := I) x₀).mono
      (by rw [extChartAt_source]; exact hK₀chart))
  have hEK₀tgt : EK₀ ⊆ tgt := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hK₀chart hy)
  obtain ⟨L, hLcpt, hEK₀L, hLt⟩ := exists_compact_between hEK₀cpt htgt_open hEK₀tgt
  obtain ⟨χM, hχ1, hχ0, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(Real, E)) (M := E)
      (n := (⊤ : ℕ∞)) hEK₀cpt.isClosed hEK₀L
  set χ : E → Real := (χM : E → Real) with hχdef
  have hχcd : ContDiff Real (∞ : WithTop ℕ∞) χ :=
    contMDiff_iff_contDiff.mp (χM.contMDiff.of_le (by exact_mod_cast le_top))
  have hχLsub : tsupport χ ⊆ L :=
    closure_minimal (fun x hx => by by_contra hxL; exact hx (hχ0 x hxL)) hLcpt.isClosed
  have hχcpt : IsCompact (tsupport χ) :=
    hLcpt.of_isClosed_subset (isClosed_tsupport χ) hχLsub
  have hχtsupp : tsupport χ ⊆ tgt := subset_trans hχLsub hLt
  obtain ⟨V₂, hV₂o, htsχV₂, hV₂t⟩ :=
    normal_exists_closure_subset (isClosed_tsupport χ) htgt_open hχtsupp
  obtain ⟨χ1M, hχ1one, hχ1zero, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(Real, E)) (M := E)
      (n := (⊤ : ℕ∞)) (isClosed_tsupport χ) (by rw [hV₂o.interior_eq]; exact htsχV₂)
  set χ1 : E → Real := (χ1M : E → Real) with hχ1def
  have hχ1cd : ContDiff Real (∞ : WithTop ℕ∞) χ1 :=
    contMDiff_iff_contDiff.mp (χ1M.contMDiff.of_le (by exact_mod_cast le_top))
  have hχ1tsupp : tsupport χ1 ⊆ tgt := by
    refine subset_trans (closure_mono ?_) hV₂t
    intro x hx; by_contra hxV; exact hx (hχ1zero x hxV)
  set Kc : Set M := (extChartAt I x₀).symm '' (tsupport χ) with hKcdef
  have hKccpt : IsCompact Kc :=
    hχcpt.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) x₀).mono hχtsupp)
  have hKcsrc : Kc ⊆ (chartAt H x₀).source := by
    rintro w ⟨z, hz, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target (hχtsupp hz)
  refine ⟨χ, hχcd, hχtsupp, fun y hy => hχ1.self_of_nhdsSet _ ⟨y, hy, rfl⟩, fun p => ?_⟩
  set cr : ℕ → E → Real := fun k =>
    writtenInExtChartAt I 𝓘(Real, Real) x₀
      (fun w : M => (covDerivOfField (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => Vfam p a w))
    with hcr
  have hcrOn : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (cr k) tgt := by
    intro k z hz
    have hzsrc : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]; exact (extChartAt I x₀).map_target hz
    have := contDiffAt_chartRep (I := I) _
      (covDerivOfField_eval_contMDiff (I := I) gRef
        (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0 (Vfam p)) x₀ hzsrc
    rw [(extChartAt I x₀).right_inv hz] at this
    exact this.contDiffWithinAt
  refine ⟨fun k => bumpMul_contDiff htgt_open hχcd hχtsupp (hcrOn k), fun r => ?_⟩
  obtain ⟨Bχ, hBχ0, hBχ⟩ : ∃ Bχ : Real, 0 ≤ Bχ ∧ ∀ x ∈ tsupport χ, ∀ i : ℕ, i ≤ r →
      ‖iteratedFDeriv Real i χ x‖ ≤ Bχ := by
    have hbd : ∀ i : ℕ, ∃ Bi : Real, ∀ x ∈ tsupport χ,
        ‖iteratedFDeriv Real i χ x‖ ≤ Bi := by
      intro i
      obtain ⟨Bi, hBi⟩ := hχcpt.bddAbove_image
        ((hχcd.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).continuousOn
      exact ⟨Bi, fun x hx => hBi ⟨x, hx, rfl⟩⟩
    choose Bi hBi using hbd
    refine ⟨∑ i ∈ Finset.range (r + 1), max (Bi i) 0,
      Finset.sum_nonneg (fun i _ => le_max_right _ _), fun x hx i hir => ?_⟩
    exact le_trans (le_trans (hBi i x hx) (le_max_left _ _))
      (Finset.single_le_sum (fun ii _ => le_max_right _ _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hir)))
  choose Mr hMr0 hMrb using fun j => hcomp p j hKccpt hKcsrc
  refine ⟨2 ^ r * Bχ * ∑ j ∈ Finset.range (r + 1), Mr j, fun k x => ?_⟩
  set ggk : E → Real := fun x => χ1 x * cr k x with hggk
  have hggcd : ContDiff Real (∞ : WithTop ℕ∞) ggk :=
    bumpMul_contDiff htgt_open hχ1cd hχ1tsupp (hcrOn k)
  have hΦeq : (fun x : E => χ x * cr k x) = fun x : E => χ x * ggk x := by
    funext z
    by_cases hz : χ z = 0
    · simp [hz]
    · have hzts : z ∈ tsupport χ := subset_tsupport _ hz
      have hχ1z : χ1 z = 1 := hχ1one.self_of_nhdsSet z hzts
      simp [ggk, hχ1z]
  have hgbd : ∀ z ∈ tsupport χ, ∀ j : ℕ, j ≤ r →
      ‖iteratedFDeriv Real j ggk z‖ ≤ ∑ j ∈ Finset.range (r + 1), Mr j := by
    intro z hz j hjr
    have hgerm : ggk =ᶠ[nhds z] cr k := by
      filter_upwards [hχ1one.filter_mono (nhds_le_nhdsSet hz)] with w hw
      simp [ggk, hw]
    rw [(hgerm.iteratedFDeriv Real j).eq_of_nhds]
    have hbnd := hMrb j k ((extChartAt I x₀).symm z) ⟨z, hz, rfl⟩
    rw [(extChartAt I x₀).right_inv (hχtsupp hz)] at hbnd
    exact le_trans hbnd
      (Finset.single_le_sum (fun jj _ => hMr0 jj)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hjr)))
  show ‖iteratedFDeriv Real r (fun x : E => χ x * cr k x) x‖ ≤ _
  simp only [hΦeq]
  exact norm_iteratedFDeriv_bumpMul_le (χ := χ) (gg := ggk) r hχcd hggcd
    hBχ0 (Finset.sum_nonneg (fun j _ => hMr0 j)) hBχ hgbd x


theorem exists_chart_engineInput_family
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) q (gSeq k) gRef z ≤ C)
    (x₀ : M)
    {ι : Type*}
    (Vfam : ι → Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source) :
    ∃ (χ : E → Real),
      ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ p : ι,
        (∀ k : ℕ, ContDiff Real (∞ : WithTop ℕ∞)
          (fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => Vfam p a w)) x)) ∧
        (∀ r : ℕ, ∃ Mr : Real, ∀ k : ℕ, ∀ x : E,
          ‖iteratedFDeriv Real r (fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gRef
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => Vfam p a w)) x) x‖ ≤ Mr) := by
  apply engine_input_family gRef gSeq x₀ Vfam ?_ hK₀ hK₀chart
  intro p r Kc hKc hKchart
  exact metricComp_iteratedFDeriv_le (I := I) gRef gSeq hbdd x₀ hKc hKchart (Vfam p) r


theorem engine_input_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M)
    {ι : Type*}
    (Vfam : ι → Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source) :
    ∃ (χ : E → Real),
      ContDiff Real (∞ : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ (extChartAt I x₀).target ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      ∀ p : ι,
        (∀ k : ℕ, ContDiff Real (∞ : WithTop ℕ∞)
          (fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => Vfam p a w)) x)) ∧
        (∀ r : ℕ, ∃ Mr : Real, ∀ k : ℕ, ∀ x : E,
          ‖iteratedFDeriv Real r (fun x : E => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w
                (fun a => Vfam p a w)) x) x‖ ≤ Mr) := by
  apply engine_input_family gBase gSeq x₀ Vfam ?_ hK₀ hK₀chart
  intro p r Kc hKc hKchart
  obtain ⟨Mr, hMr0, hMr⟩ :=
    metricComp_iter_refs (I := I) gRef gSeq hbdd x₀ hKc hKchart (Vfam p) r
  refine ⟨Mr, hMr0, fun k y hy => ?_⟩
  exact hMr k y hy


theorem exists_chart_refs
    (gBase : SmoothRiemannianMetric I M)
    (gRef : ℕ → SmoothRiemannianMetric I M)
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (hbdd : ∀ r q : ℕ, q ≤ r → ∀ K : Set M, IsCompact K → ∃ C : Real,
      ∀ k : ℕ, ∀ z ∈ K, metricCovDerivNorm (I := I) q (gSeq k) (gRef r) z ≤ C)
    (x₀ : M)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {K₀ : Set M} (hK₀ : IsCompact K₀) (hK₀chart : K₀ ⊆ (chartAt H x₀).source) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → Real) (χ : E → Real),
      StrictMono φ ∧ ContDiff Real (∞ : WithTop ℕ∞) Φinf ∧
      (∀ y ∈ K₀, χ (extChartAt I x₀ y) = 1) ∧
      MapCInfConvOnCompacts Set.univ
        (fun k => fun x : E => χ x *
          writtenInExtChartAt I 𝓘(Real, Real) x₀
            (fun w : M => (covDerivOfField (I := I) gBase
              (Tensor0SBundle.metricTensorField (I := I) (gSeq (φ k))) 0) w
                (fun a => V a w)) x) Φinf := by
  let Vfam : Unit → Fin 2 →
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) := fun _ => V
  obtain ⟨χ, _hχcd, _hχsupp, hχ1, hfamily⟩ :=
    engine_input_refs (I := I) gBase gRef gSeq hbdd x₀ Vfam hK₀ hK₀chart
  obtain ⟨hΦcd, hΦbd⟩ := hfamily ()
  let Φ : ℕ → E → Real := fun k x => χ x * writtenInExtChartAt I 𝓘(Real, Real) x₀
    (fun w : M => (covDerivOfField (I := I) gBase
      (Tensor0SBundle.metricTensorField (I := I) (gSeq k)) 0) w (fun a => V a w)) x
  obtain ⟨φ, Φinf, hφ, hΦinf, hconv⟩ :=
    exists_cInf_subseq Φ hΦcd
      (fun r K _ => by obtain ⟨C, hC⟩ := hΦbd r; exact ⟨C, fun k x _ => hC k x⟩)
  refine ⟨φ, Φinf, χ, hφ, hΦinf, hχ1, ?_⟩
  change MapCInfConvOnCompacts Set.univ (fun k => Φ (φ k)) Φinf
  exact hconv

end HCGCompactness
end DifferentialGeometry
