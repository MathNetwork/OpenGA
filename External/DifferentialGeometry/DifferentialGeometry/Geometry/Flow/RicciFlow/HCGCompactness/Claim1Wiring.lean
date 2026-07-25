import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AkMFold
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.KoszulDifference
import DifferentialGeometry.Geometry.Connection.Chart.Christoffel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option linter.style.longLine false



















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]








omit [I.Boundaryless] [IsManifold I 2 M] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem lcChrist_e_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (d i j : Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) g)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y d i j)
      e₀.baseSet := by
  intro y hy
  refine ((lc_christoffel_contMDiffAt (I := I) e₀ basisE g hy d i j).congr_of_eventuallyEq
    ?_).contMDiffWithinAt
  filter_upwards [e₀.open_baseSet.mem_nhds hy] with z hz
  have hbasis : (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hz =
      e₀.basisAt basisE hz := by
    ext j'
    simp [IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
      Bundle.Trivialization.basisAt, hz]
  simp [christoffelSymbolInFrame, IsLocalFrameOn.coeff, hz,
    Bundle.Trivialization.localFrame_coeff, hbasis]



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] [DecidableEq Idx] in
theorem frame_e_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (basisE : Module.Basis Idx Real E) (d : Idx) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (e₀.localFrame basisE d y))
      e₀.baseSet :=
  (e₀.isLocalFrameOn_localFrame_baseSet I ∞ basisE).contMDiffOn d

set_option backward.isDefEq.respectTransparency false in


omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] [DecidableEq Idx] in
theorem tensorComp_mdiffOn {r : ℕ}
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (basisE : Module.Basis Idx Real E) (k : Fin r → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) T
        (fun a y' => e₀.localFrame basisE a y') y k) e₀.baseSet := by
  intro y hy
  have hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun x : M => Tensor0SSpace r I x) b (T b)) y :=
    T.contMDiff.contMDiffAt
  have hv : ∀ i : Fin r,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b
          (e₀.localFrame basisE (k i) b)) y :=
    fun i => (frame_e_mdiffOn e₀ basisE (k i)).contMDiffAt
      (e₀.open_baseSet.mem_nhds hy)
  have h := TensorMultilinear.contMDiffAt_section_apply_gen
    (T := fun b : M => T b) hT
    (v := fun (i : Fin r) (b : M) => e₀.localFrame basisE (k i) b) hv
  exact h.contMDiffWithinAt




def akCompField
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) :
    M → (Fin (2 + 1) → Idx) → Real :=
  fun y m =>
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK)
      (fun a y' => e₀.localFrame basisE a y')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y (m 0) (m 1) (m 2) -
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
      (fun a y' => e₀.localFrame basisE a y')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y (m 0) (m 1) (m 2)



omit [I.Boundaryless] [IsManifold I 2 M] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem akCompField_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (k : Fin (2 + 1) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => akCompField (I := I) e₀ gK gRef basisE y k) e₀.baseSet := by
  exact (lcChrist_e_mdiffOn e₀ gK basisE (k 0) (k 1) (k 2)).sub
    (lcChrist_e_mdiffOn e₀ gRef basisE (k 0) (k 1) (k 2))

set_option backward.isDefEq.respectTransparency false in



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] [DecidableEq Idx] in
theorem gCompField_mdiffOn
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (k : Fin (1 + 1) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g)
        (fun a y' => e₀.localFrame basisE a y') y k) e₀.baseSet := by
  intro y hy
  have hT : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) b (metricTensorField (I := I) g b)) y :=
    (metricTensorField (I := I) g).contMDiff.contMDiffAt
  have hv : ∀ i : Fin 2,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) b
          (e₀.localFrame basisE (k i) b)) y :=
    fun i => (frame_e_mdiffOn e₀ basisE (k i)).contMDiffAt (e₀.open_baseSet.mem_nhds hy)
  have h := TensorMultilinear.contMDiffAt_section_apply_gen
    (T := fun b : M => metricTensorField (I := I) g b) hT
    (v := fun (i : Fin 2) (b : M) => e₀.localFrame basisE (k i) b) hv
  exact h.contMDiffWithinAt








def gramE
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M) :
    Matrix Idx Idx Real :=
  Matrix.of fun i j => g.inner y (e₀.localFrame basisE i y) (e₀.localFrame basisE j y)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] [DecidableEq Idx] in
theorem gramE_herm
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M) :
    (gramE (I := I) e₀ g basisE y).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, gramE, Matrix.of_apply]
  exact g.symm y _ _



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [DecidableEq Idx] in
theorem gramE_dotVec
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) (y : M)
    (c : Idx → Real) :
    c ⬝ᵥ (gramE (I := I) e₀ g basisE y).mulVec c =
      g.inner y (∑ i, c i • e₀.localFrame basisE i y)
        (∑ j, c j • e₀.localFrame basisE j y) := by
  have hexpand : g.inner y (∑ i, c i • e₀.localFrame basisE i y)
        (∑ j, c j • e₀.localFrame basisE j y) =
      ∑ i, ∑ j, c i * c j *
        g.inner y (e₀.localFrame basisE i y) (e₀.localFrame basisE j y) := by
    have hL : g.inner y (∑ i, c i • e₀.localFrame basisE i y) =
        ∑ i, c i • g.inner y (e₀.localFrame basisE i y) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => ContinuousLinearMap.map_smul _ _ _
    rw [hL, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  rw [hexpand]
  simp only [dotProduct, Matrix.mulVec, gramE, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem gramE_posDef
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {y : M} (hy : y ∈ e₀.baseSet) :
    (gramE (I := I) e₀ g basisE y).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gramE_herm (I := I) e₀ g basisE y) ?_
  intro c hc
  rw [show (star c : Idx → Real) = c from funext fun i => star_trivial _, gramE_dotVec]
  have hwnz : (∑ i, c i • e₀.localFrame basisE i y) ≠ 0 := by
    intro hw0
    have hli := (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).linearIndependent hy
    rw [Fintype.linearIndependent_iff] at hli
    exact hc (funext (hli c hw0))
  exact g.pos y _ hwnz



def ginvCompField
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) :
    M → (Fin (1 + 1) → Idx) → Real :=
  fun y m => (gramE (I := I) e₀ g basisE y)⁻¹ (m 0) (m 1)



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ginv_hinv
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    {y : M} (hy : y ∈ e₀.baseSet) (c e : Idx) :
    (∑ l : Idx,
      frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y') y (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE y (Fin.snoc (fun _ : Fin 1 => e) l)) =
      if c = e then 1 else 0 := by
  classical
  have hdet : IsUnit (gramE (I := I) e₀ g basisE y).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (gramE_posDef (I := I) e₀ g basisE hy).det_pos)
  have hentry := congrArg (fun A : Matrix Idx Idx Real => A e c)
    (Matrix.nonsing_inv_mul (gramE (I := I) e₀ g basisE y) hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply] at hentry
  have hterm : ∀ l : Idx,
      frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y') y (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE y (Fin.snoc (fun _ : Fin 1 => e) l) =
      (gramE (I := I) e₀ g basisE y)⁻¹ e l * gramE (I := I) e₀ g basisE y l c := by
    intro l
    have h0 : (Fin.snoc (fun _ : Fin 1 => l) c : Fin 2 → Idx) 0 = l := by simp [Fin.snoc]
    have h1 : (Fin.snoc (fun _ : Fin 1 => l) c : Fin 2 → Idx) 1 = c := by simp [Fin.snoc]
    have h0' : (Fin.snoc (fun _ : Fin 1 => e) l : Fin 2 → Idx) 0 = e := by simp [Fin.snoc]
    have h1' : (Fin.snoc (fun _ : Fin 1 => e) l : Fin 2 → Idx) 1 = l := by simp [Fin.snoc]
    rw [frameComp0S_apply, metricTensorField_apply, h0, h1,
      show ginvCompField (I := I) e₀ g basisE y (Fin.snoc (fun _ : Fin 1 => e) l) =
        (gramE (I := I) e₀ g basisE y)⁻¹ e l from by
        rw [ginvCompField, h0', h1'],
      show g.inner y (e₀.localFrame basisE l y) (e₀.localFrame basisE c y) =
        gramE (I := I) e₀ g basisE y l c from rfl]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, hentry]
  rcases eq_or_ne e c with rfl | h
  · simp
  · rw [if_neg h, if_neg fun hce => h hce.symm]











omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] [Fintype Idx] [DecidableEq Idx] in
private theorem chr_eq_chartChr {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u) (x : M) (i j k : Idx) :
    christoffelSymbolInFrame cov frame hframe x i j k =
      DifferentialGeometry.Coordinates.christoffelSymbolInFrame cov frame hframe x i j k := rfl

set_option backward.isDefEq.respectTransparency false in





omit [I.Boundaryless] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem koszulComp_at
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    (gK gRef : SmoothRiemannianMetric I M)
    {y : M} (hy : y ∈ u) :
    contrTail
        (fun m : Fin (2 + 1) → Idx =>
          christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK) frame hframe y
              (m 0) (m 1) (m 2) -
            christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y
              (m 0) (m 1) (m 2))
        (frameComp0S (I := I) (metricTensorField (I := I) gK) frame y) =
      fun idx : Fin (2 + 1) → Idx =>
        (1 / 2 : Real) * iterCovComp (I := I) frame
            (fun y' => christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
            (frameComp0S (I := I) (metricTensorField (I := I) gK) frame) 1 y
            (fun j => idx (Equiv.refl (Fin 3) j)) +
        ((1 / 2 : Real) * iterCovComp (I := I) frame
            (fun y' => christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
            (frameComp0S (I := I) (metricTensorField (I := I) gK) frame) 1 y
            (fun j => idx (Equiv.swap (0 : Fin 3) 1 j)) +
          (-(1 / 2) : Real) * iterCovComp (I := I) frame
            (fun y' => christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
            (frameComp0S (I := I) (metricTensorField (I := I) gK) frame) 1 y
            (fun j => idx ((finRotate 3).symm j))) := by
  classical
  funext idx

  obtain ⟨X, hX⟩ : ∃ X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      X y = frame (idx 0) y :=
    ⟨(ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) y (frame (idx 0) y)).choose,
      (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) y (frame (idx 0) y)).choose_spec⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      Y y = frame (idx 1) y :=
    ⟨(ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) y (frame (idx 1) y)).choose,
      (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) y (frame (idx 1) y)).choose_spec⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
      Z y = frame (idx 2) y :=
    ⟨(ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) y (frame (idx 2) y)).choose,
      (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) y (frame (idx 2) y)).choose_spec⟩

  have hmcK : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) (leviCivitaConnectionOfMetric (I := I) gK) gK :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := I) gK
  have htfK : DifferentialGeometry.Integral.Connection.IsTorsionFreeAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) gK) y :=
    leviCivitaConnectionOfMetric_isTorsionFree (I := I) gK y
  have htfR : DifferentialGeometry.Integral.Connection.IsTorsionFreeAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) gRef) y :=
    leviCivitaConnectionOfMetric_isTorsionFree (I := I) gRef y
  have hkos := Tensor0SBundle.koszul_difference (I := I)
    (leviCivitaConnectionOfMetric (I := I) gK) (leviCivitaConnectionOfMetric (I := I) gRef)
    gK hmcK htfK htfR X Y Z
  rw [hX, hY, hZ] at hkos

  have hframe_b : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z => TotalSpace.mk' E (E := TangentSpace I) z (frame (idx 1) z)) y :=
    ((hframe.contMDiffOn (idx 1)).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp)
  have hLHS : contrTail
        (fun m : Fin (2 + 1) → Idx =>
          christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK) frame hframe y (m 0) (m 1) (m 2) -
            christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y (m 0) (m 1) (m 2))
        (frameComp0S (I := I) (metricTensorField (I := I) gK) frame y) idx =
      gK.inner y
        (((CovariantDerivative.difference (leviCivitaConnectionOfMetric (I := I) gK) (leviCivitaConnectionOfMetric (I := I) gRef) y) (frame (idx 1) y)) (frame (idx 0) y))
        (frame (idx 2) y) := by
    rw [contrTail_apply]
    have hsum : ∀ d : Idx,
        (fun m : Fin (2 + 1) → Idx =>
            christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK) frame hframe y (m 0) (m 1) (m 2) -
              christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y (m 0) (m 1) (m 2))
          (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) d) *
          frameComp0S (I := I) (metricTensorField (I := I) gK) frame y
            (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) d) =
        DifferentialGeometry.Coordinates.christoffelSymbolDifferenceInFrame
            (leviCivitaConnectionOfMetric (I := I) gK) (leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe y (idx 0) (idx 1) d *
          gK.inner y (frame (idx 2) y) (frame d y) := by
      intro d
      have e0 : (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) d : Fin 3 → Idx) 0 =
          idx 0 := by simp [Fin.snoc]
      have e1 : (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) d : Fin 3 → Idx) 1 =
          idx 1 := by simp [Fin.snoc]
      have e2 : (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) d : Fin 3 → Idx) 2 = d := by
        simp [Fin.snoc]
      have f0 : (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) d : Fin 2 → Idx) 0 =
          idx 2 := by simp [Fin.snoc]
      have f1 : (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) d : Fin 2 → Idx) 1 = d := by
        simp [Fin.snoc]
      simp only [e0, e1, e2]
      rw [frameComp0S_apply, metricTensorField_apply, f0, f1,
        chr_eq_chartChr (leviCivitaConnectionOfMetric (I := I) gK) frame hframe y
          (idx 0) (idx 1) d,
        chr_eq_chartChr (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y
          (idx 0) (idx 1) d,
        ← DifferentialGeometry.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub
          (leviCivitaConnectionOfMetric (I := I) gK) (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe (idx 0) (idx 1) d hframe_b]
    rw [Finset.sum_congr rfl fun d _ => hsum d]
    have hlin : (∑ d : Idx,
          DifferentialGeometry.Coordinates.christoffelSymbolDifferenceInFrame
              (leviCivitaConnectionOfMetric (I := I) gK) (leviCivitaConnectionOfMetric (I := I) gRef)
              frame hframe y (idx 0) (idx 1) d *
            gK.inner y (frame (idx 2) y) (frame d y)) =
        gK.inner y (frame (idx 2) y)
          (∑ d : Idx,
            DifferentialGeometry.Coordinates.christoffelSymbolDifferenceInFrame
                (leviCivitaConnectionOfMetric (I := I) gK) (leviCivitaConnectionOfMetric (I := I) gRef)
                frame hframe y (idx 0) (idx 1) d • frame d y) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hlin,
      ← DifferentialGeometry.Coordinates.christoffelSymbolDifference_expansion
        (leviCivitaConnectionOfMetric (I := I) gK) (leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe hy (idx 0) (idx 1),
      gK.symm y]

  have hreal := iterCov_realizes (I := I) gRef
    (T := metricTensorField (I := I) gK) 0
  have hbr : ∀ (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
      (v0 v1 v2 : Idx) (w : Fin 3 → Idx),
      W y = frame v0 y → w 0 = v0 → w 1 = v1 → w 2 = v2 →
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (leviCivitaConnectionOfMetric (I := I) gRef) W
          (metricTensorField (I := I) gK) y
          (fun q : Fin 2 => if q = 0 then frame v1 y else frame v2 y) =
        iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) (metricTensorField (I := I) gK) frame) 1 y w := by
    intro W v0 v1 v2 w hW hw0 hw1 hw2
    have h1' : iterCov (I := I) gRef 2 (metricTensorField (I := I) gK) 1 y
        (Fin.cons (W y) (fun q : Fin 2 => if q = 0 then frame v1 y else frame v2 y)) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
          (leviCivitaConnectionOfMetric (I := I) gRef) W
          (metricTensorField (I := I) gK) y
          (fun q : Fin 2 => if q = 0 then frame v1 y else frame v2 y) :=
      hreal W y (fun q : Fin 2 => if q = 0 then frame v1 y else frame v2 y)
    have hvw : (Fin.cons (frame v0 y) (fun q : Fin 2 =>
        if q = 0 then frame v1 y else frame v2 y) : Fin 3 → TangentSpace I y) =
        frameTuple (I := I) frame y w := by
      funext q
      refine Fin.cases ?_ (fun q' => ?_) q
      · show frame v0 y = frame (w 0) y
        rw [hw0]
      · refine Fin.cases ?_ (fun q'' => ?_) q'
        · show (if (0 : Fin 2) = 0 then frame v1 y else frame v2 y) = frame (w 1) y
          rw [if_pos rfl, hw1]
        · have hq2 : q'' = 0 := Subsingleton.elim _ _
          subst hq2
          show (if (Fin.succ 0 : Fin 2) = 0 then frame v1 y else frame v2 y) =
            frame (w 2) y
          rw [if_neg (by decide), hw2]
    rw [← h1', hW, hvw,
      ← iterCovComp_eq_iterCov (I := I) gRef (metricTensorField (I := I) gK)
        frame hframe hu 1 hy w]

  have hb1 := hbr X (idx 0) (idx 1) (idx 2) (fun j => idx (Equiv.refl (Fin 3) j)) hX rfl rfl rfl
  have hb2 := hbr Y (idx 1) (idx 0) (idx 2) (fun j => idx (Equiv.swap (0 : Fin 3) 1 j)) hY
    (by show idx (Equiv.swap (0 : Fin 3) 1 0) = idx 1; congr 1)
    (by show idx (Equiv.swap (0 : Fin 3) 1 1) = idx 0; congr 1)
    (by show idx (Equiv.swap (0 : Fin 3) 1 2) = idx 2; congr 1)
  have hb3 := hbr Z (idx 2) (idx 0) (idx 1) (fun j => idx ((finRotate 3).symm j)) hZ
    (by show idx ((finRotate 3).symm 0) = idx 2; congr 1)
    (by show idx ((finRotate 3).symm 1) = idx 0; congr 1)
    (by show idx ((finRotate 3).symm 2) = idx 1; congr 1)
  rw [hLHS, hkos, hb1, hb2, hb3]
  ring






omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem ginv_compL2_le
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (g : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E) {y : M}
    (c : Real) (hc : 0 < c)
    (hquad : ∀ v : Idx → Real,
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (gramE (I := I) e₀ g basisE y).mulVec v) :
    compL2 (ginvCompField (I := I) e₀ g basisE y) ≤
      Real.sqrt (Fintype.card Idx) / c := by
  classical

  have hpos : (gramE (I := I) e₀ g basisE y).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (gramE_herm (I := I) e₀ g basisE y) ?_
    intro v hv
    rw [show (star v : Idx → Real) = v from funext fun i => star_trivial _]
    have hvv : 0 < v ⬝ᵥ v := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun e _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
    exact lt_of_lt_of_le (mul_pos hc hvv) (hquad v)
  have hdet : IsUnit (gramE (I := I) e₀ g basisE y).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)

  have hcol : ∀ l : Idx,
      ((fun e => (gramE (I := I) e₀ g basisE y)⁻¹ e l) ⬝ᵥ
        (fun e => (gramE (I := I) e₀ g basisE y)⁻¹ e l)) ≤ (1 / c) ^ 2 := by
    intro l
    set w : Idx → Real := fun e => (gramE (I := I) e₀ g basisE y)⁻¹ e l with hw
    have hGw : (gramE (I := I) e₀ g basisE y).mulVec w = Pi.single l 1 := by
      have h1 : w = (gramE (I := I) e₀ g basisE y)⁻¹.mulVec (Pi.single l 1) := by
        funext e
        simp [hw, Matrix.mulVec_single]
      rw [h1, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hq := hquad w
    rw [hGw, show w ⬝ᵥ Pi.single l 1 = w l from by
      simp [dotProduct, Pi.single_apply]] at hq
    have hself : (w l) ^ 2 ≤ w ⬝ᵥ w := by
      have h := Finset.single_le_sum (f := fun e => w e * w e)
        (fun e _ => mul_self_nonneg _) (Finset.mem_univ l)
      simpa [dotProduct, sq] using h
    have hS0 : (0 : Real) ≤ w ⬝ᵥ w :=
      Finset.sum_nonneg fun e _ => mul_self_nonneg _
    have h1 : (c * (w ⬝ᵥ w)) * (c * (w ⬝ᵥ w)) ≤ (w l) * (w l) :=
      mul_self_le_mul_self (mul_nonneg hc.le hS0) hq
    have h3 : c ^ 2 * (w ⬝ᵥ w) ^ 2 ≤ w ⬝ᵥ w := by nlinarith [h1, hself]
    rcases hS0.lt_or_eq with hSpos | hS0'
    · rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
      nlinarith [h3, hSpos]
    · rw [← hS0']
      positivity

  have hsq : compL2Sq (ginvCompField (I := I) e₀ g basisE y) ≤
      (Real.sqrt (Fintype.card Idx) / c) ^ 2 := by
    have hre : compL2Sq (ginvCompField (I := I) e₀ g basisE y) =
        ∑ p : Idx × Idx, ((gramE (I := I) e₀ g basisE y)⁻¹ p.1 p.2) ^ 2 := by
      simp only [compL2Sq]
      exact Fintype.sum_equiv (piFinTwoEquiv (fun _ : Fin 2 => Idx))
        _ _ (fun m => rfl)
    rw [hre, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    calc (∑ p : Idx × Idx, ((gramE (I := I) e₀ g basisE y)⁻¹ p.1 p.2) ^ 2)
        = ∑ l : Idx, ∑ e : Idx, ((gramE (I := I) e₀ g basisE y)⁻¹ e l) ^ 2 := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_comm
      _ ≤ ∑ _l : Idx, (1 / c) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          have h := hcol l
          calc (∑ e : Idx, ((gramE (I := I) e₀ g basisE y)⁻¹ e l) ^ 2)
              = (fun e => (gramE (I := I) e₀ g basisE y)⁻¹ e l) ⬝ᵥ
                (fun e => (gramE (I := I) e₀ g basisE y)⁻¹ e l) := by
                simp [dotProduct, sq]
            _ ≤ (1 / c) ^ 2 := h
      _ = (Fintype.card Idx : Real) * (1 / c) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card Idx : Real) / c ^ 2 := by ring
  calc compL2 (ginvCompField (I := I) e₀ g basisE y)
      = Real.sqrt (compL2Sq (ginvCompField (I := I) e₀ g basisE y)) := rfl
    _ ≤ Real.sqrt ((Real.sqrt (Fintype.card Idx) / c) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Fintype.card Idx) / c := Real.sqrt_sq
        (div_nonneg (Real.sqrt_nonneg _) hc.le)







omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem compL2_tower_eq
    (gRef : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) gRef y (hframe.toBasisAt hy)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (j : ℕ) :
    compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y')
        (frameComp0S (I := I) T frame) j y) =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef y (r + j)
        (iterCov (I := I) gRef r T j y)) := by
  rw [compL2]
  congr 1
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef y (r + j)
    (hframe.toBasisAt hy) hinv (iterCov (I := I) gRef r T j y)]
  simp only [compL2Sq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [iterCovComp_eq_iterCov (I := I) gRef T frame hframe hu j hy n]
  congr 1
  rw [Tensor0SBundle.component0S_apply]
  congr 1
  funext q
  rw [IsLocalFrameOn.toBasisAt_coe]
  rfl



set_option backward.isDefEq.respectTransparency false in







omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem claim1_geom
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (C0 K : Real)
    (hGinv : ∀ y ∈ e₀.baseSet, compL2 (ginvCompField (I := I) e₀ gK basisE y) ≤ C0)
    (m : ℕ)
    (hK : ∀ y ∈ e₀.baseSet, ∀ j, 1 ≤ j → j ≤ m →
      compL2 (iterCovComp (I := I) (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y')
        (frameComp0S (I := I) (metricTensorField (I := I) gK)
          (fun a y' => e₀.localFrame basisE a y')) j y) ≤ K) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ e₀.baseSet,
      compL2 (iterCovCompU (I := I) (fun a y' => e₀.localFrame basisE a y')
          (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y')
          (akCompField (I := I) e₀ gK gRef basisE) m y) ≤
        C * (1 + compL2 (iterCovComp (I := I) (fun a y' => e₀.localFrame basisE a y')
          (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y')
          (frameComp0S (I := I) (metricTensorField (I := I) gK)
            (fun a y' => e₀.localFrame basisE a y')) (m + 1) y)) := by
  obtain ⟨C, hC0, hCb⟩ := claim1 e₀.open_baseSet
    (fun a y' => e₀.localFrame basisE a y')
    (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
      (fun a y'' => e₀.localFrame basisE a y'')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y')
    (fun d => frame_e_mdiffOn e₀ basisE d)
    (fun d i j => lcChrist_e_mdiffOn e₀ gRef basisE d i j)
    (1 / 2) (1 / 2) (-(1 / 2))
    (Equiv.refl (Fin 3)) (Equiv.swap (0 : Fin 3) 1) ((finRotate 3).symm)
    C0 K m
  exact ⟨C, hC0, hCb
    (frameComp0S (I := I) (metricTensorField (I := I) gK)
      (fun a y' => e₀.localFrame basisE a y'))
    (fun k => gCompField_mdiffOn e₀ gK basisE k)
    (ginvCompField (I := I) e₀ gK basisE)
    (akCompField (I := I) e₀ gK gRef basisE)
    (fun k => akCompField_mdiffOn e₀ gK gRef basisE k)
    (fun y hy c e => ginv_hinv e₀ gK basisE hy c e)
    (fun y hy => koszulComp_at (fun a y' => e₀.localFrame basisE a y')
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) e₀.open_baseSet gK gRef hy)
    hGinv hK⟩

end DifferentialGeometry.PDE.RicciFlow
