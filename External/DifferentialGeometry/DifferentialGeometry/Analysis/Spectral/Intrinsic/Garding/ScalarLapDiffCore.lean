import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautTame








noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem clm0_ext {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 0 I x}
    (h : Tensor0SSpace.toModel
          (φ (unitZeroSec (I := I) (M := M) x)) (fun i => Fin.elim0 i) =
        Tensor0SSpace.toModel
          (ψ (unitZeroSec (I := I) (M := M) x)) (fun i => Fin.elim0 i)) :
    φ = ψ := by
  have hunit :
      φ (unitZeroSec (I := I) (M := M) x) =
        ψ (unitZeroSec (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro slots
    have hslots : slots = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    subst slots
    exact h
  ext D
  rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D,
    map_smul, map_smul, hunit]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem traceFib_diag
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) g 0 x D)
        (fun i : Fin 0 => Fin.elim0 i) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  rw [cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 0 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel D) (fun i : Fin 0 => Fin.elim0 i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext a
  fin_cases a <;> rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lapTrace_diag
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    scalarLapTraceAt (I := I) g D =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  let frame : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have horth : ∀ i j, g.inner x (frame i) (frame j) =
      if i = j then 1 else 0 := by
    intro i j
    simpa only [frame] using
      smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hli : LinearIndependent ℝ frame := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hp : g.inner x (∑ i, c i • frame i) (frame j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply,
      Finset.sum_eq_single j] at hp
    · rw [ContinuousLinearMap.map_smul,
        ContinuousLinearMap.smul_apply, horth j j,
        if_pos rfl, smul_eq_mul, mul_one] at hp
      exact hp
    · intro i _ hij
      rw [ContinuousLinearMap.map_smul,
        ContinuousLinearMap.smul_apply, horth i j,
        if_neg (by simpa using hij), smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hli
      (by rw [Fintype.card_fin]; rfl)
  have hbasis (i) : basis i = frame i := by
    simp only [basis, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    intro i j
    constructor <;>
      simp [identityInvMetric, diagonalInvMetric, hbasis, horth]
  rw [scalarLapTraceAt,
    metricTracePair0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) hinv]
  simp only [hbasis, frame]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [identityInvMetric_apply_self, one_mul]
    rfl
  · intro j _ hji
    rw [identityInvMetric,
      diagonalInvMetric_eq_zero_of_ne (fun h => hji h.symm), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem trace_eq_lap
    (a : SmoothRiemannianMetric I M) (x : M)
    (D Hs : Tensor0SSpace 2 I x)
    (hdiag : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) a x i x)
            (smoothOrthoFrame (I := I) a x i x)) =
        Tensor0SSpace.toModel Hs
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) a x i x)
            (smoothOrthoFrame (I := I) a x i x))) :
    Tensor0SSpace.toModel
        (cometricDoubleTraceFib (I := I) a 0 x D)
        (fun i : Fin 0 => Fin.elim0 i) =
      scalarLapTraceAt (I := I) a Hs := by
  rw [traceFib_diag (I := I) (M := M),
    lapTrace_diag (I := I) (M := M)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hdiag i

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem lift_unit {x : M} (c : ℝ) :
    Tensor0SSpace.toModel
        ((Tensor0SSpace.toRS0
            ((Tensor0SNabla.tensor0Iso I M x).symm c))
          (unitZeroSec (I := I) (M := M) x))
        (fun i : Fin 0 => Fin.elim0 i) = c := by
  rw [Tensor0SSpace.toRS0_apply]
  have hu : tensor0SSpace_evalScalar x
      (unitZeroSec (I := I) (M := M) x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hu, one_smul]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm c) = c
  rw [ContinuousLinearEquiv.apply_symm_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem one0_eq_unit (x : M) :
    Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) x =
      unitZeroSec (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro slots
  rw [Tensor0SField.one0_apply, unitZeroSec_apply]
  change (1 : ℝ) =
    ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) slots
  rw [ContinuousMultilinearMap.constOfIsEmpty_apply]

omit [NeZero (Module.finrank ℝ E)] in
private theorem grad_cc_apply
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 0)
    (x : M) (X : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
          (iteratedCovGrad (I := I) (M := M) g 0 0 1 U).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun _ : Fin 1 => X) =
      duSec (I := I)
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection)
        (TensorRSField.scalar0_smooth
          (n := (∞ : WithTop ℕ∞)) U.toSection) x
        (fun _ : Fin 1 => X) := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) U.toSection
  let A : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞ f hf
  have hunit (y : M) :
      tensor0SSpace_evalScalar y (unitZeroSec (I := I) (M := M) y) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  have hsection :
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 0 I y from
          U.toSection y) (unitZeroSec (I := I) (M := M) y)) =
        fun y : M => A y := by
    funext y
    rw [← TensorRSField.lift_scalar0
      (n := (∞ : WithTop ℕ∞)) U.toSection,
      Tensor0SField.toRS0_apply, hunit, one_smul]
  have hscalar :
      Tensor0SNabla.scalarFn I M (fun y : M => A y) = f := by
    funext y
    rw [Tensor0SNabla.scalarFn_eq_apply_zero]
    change Tensor0SField.toScalarField ∞ A y = f y
    exact congrFun (Tensor0SField.toScalarField_fromScalarField ∞ f hf) y
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 0 U x
    (unitZeroSec (I := I) (M := M) x) (fun _ : Fin 1 => X)]
  rw [tensorCovDerivAt_def,
    tensorRSCovariantDerivative_zeroS_unit_eval, hsection,
    Tensor0SNabla.tensor0SCovariantDerivative_apply_zero, hscalar,
    duSec_apply, differential1FormFun_apply_eq_extDerivFun]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (extDerivFun (I := I) f x X)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

omit [NeZero (Module.finrank ℝ E)] in
private theorem grad2_cc_diag
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 0)
    (B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (iteratedCovGrad (I := I) (M := M) g 0 0 2 U).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (vec2 (I := I) (B x) (B x)) =
      hessianSec (I := I) (LeviCivita (I := I) g)
        (by
          simpa [LeviCivita] using
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) g))
        (TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection)
        (TensorRSField.scalar0_smooth
          (n := (∞ : WithTop ℕ∞)) U.toSection) x
        (vec2 (I := I) (B x) (B x)) := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) U.toSection
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) g) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let m0 : Fin 0 → TangentSpace I x := fun i => Fin.elim0 i
  have hslots :
      Fin.cons (B x) (Fin.cons (B x) m0) = vec2 (I := I) (B x) (B x) := by
    funext i
    fin_cases i <;> rfl
  have hiter :
      iteratedCovGrad (I := I) (M := M) g 0 0 2 U =
        covGrad (I := I) (M := M) g 0 1
          (covGrad (I := I) (M := M) g 0 0 U) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hbridge :=
    tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
      (I := I) (M := M) g 0 U
      (X := fun y => B y) (Y := fun y => B y)
      B.contMDiff B.contMDiff x m0
  rw [hiter, ← hslots, hbridge]
  have hrepr : (fun y : M => U.toSection y) =
      fun y : M =>
        (Tensor0SField.fromScalarField ∞ f hf).toTensorRSField ∞ y := by
    funext y
    exact congrArg (fun T => T y)
      (TensorRSField.lift_scalar0
        (n := (∞ : WithTop ℕ∞)) U.toSection).symm
  rw [hrepr]
  rw [tensorSecondCovDeriv_def,
    secondRS_scalar (I := I) (M := M) g hcov hf B x]
  rw [hslots, Tensor0SSpace.toRS0_apply]
  have hunit :
      tensor0SSpace_evalScalar x (unitZeroSec (I := I) (M := M) x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [hunit, one_smul]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm
        (hessianSec (I := I) (LeviCivita (I := I) g) hcov f hf x
          (vec2 (I := I) (B x) (B x)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]



theorem scalarLapDiff_eq
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) (x : M) :
    TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞))
        (scalarLapDiffCc (I := I) q h U).toSection x =
      Δ_g (I := I) h
          (TensorRSField.scalar0_smooth
            (n := (∞ : WithTop ℕ∞)) U.toSection) x -
        Δ_g (I := I) q
          (TensorRSField.scalar0_smooth
            (n := (∞ : WithTop ℕ∞)) U.toSection) x := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) U.toSection
  let hf := TensorRSField.scalar0_smooth
    (n := (∞ : WithTop ℕ∞)) U.toSection
  let hcovh : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) h) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) h)
  let hcovq : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) q) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) q)
  have hmch : IsMetricCompatible_gen (I := I)
      (LeviCivita (I := I) h) h := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) h)
  have hmcq : IsMetricCompatible_gen (I := I)
      (LeviCivita (I := I) q) q := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) q)
  let D2 : Tensor0SSpace 2 I x :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (iteratedCovGrad (I := I) (M := M) q 0 0 2 U).toSection x)
      (unitZeroSec (I := I) (M := M) x))
  let D1 : Tensor0SSpace 1 I x :=
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (iteratedCovGrad (I := I) (M := M) q 0 0 1 U).toSection x)
      (unitZeroSec (I := I) (M := M) x))
  let Hs : Tensor0SSpace 2 I x :=
    hessianSec (I := I) (LeviCivita (I := I) q) hcovq f hf x
  let CD : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffFib (I := I) h q x) D1
  let Corr : Tensor0SSpace 2 I x :=
    connectionDifferenceOutput (I := I)
      (CovariantDerivative.difference
        (LeviCivita (I := I) h) (LeviCivita (I := I) q) x)
      (duSec (I := I) f hf x)
  have hsecond (a : SmoothRiemannianMetric I M) :
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) a 0 x D2)
          (fun i : Fin 0 => Fin.elim0 i) =
        scalarLapTraceAt (I := I) a Hs := by
    apply trace_eq_lap (I := I) (M := M)
    intro i
    simpa only [D2, Hs, hcovq, f, hf] using
      (grad2_cc_diag (I := I) (M := M) q U
        ⟨smoothOrthoFrame (I := I) a x i,
          smoothOrthoFrame_smooth (I := I) a x i⟩ x)
  have hconn :
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x CD)
          (fun i : Fin 0 => Fin.elim0 i) =
        scalarLapTraceAt (I := I) h Corr := by
    apply trace_eq_lap (I := I) (M := M)
    intro i
    dsimp only [CD, D1, Corr]
    change
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          connDiffFib (I := I) h q x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
            (iteratedCovGrad (I := I) (M := M) q 0 0 1 U).toSection x)
          (unitZeroSec (I := I) (M := M) x)))
        (vec2 (I := I)
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x)) =
        connectionDifferenceOutput (I := I)
          (CovariantDerivative.difference
            (LeviCivita (I := I) h) (LeviCivita (I := I) q) x)
          (duSec (I := I) f hf x)
          (vec2 (I := I)
            (smoothOrthoFrame (I := I) h x i x)
            (smoothOrthoFrame (I := I) h x i x))
    rw [connDiffFib_apply_eval]
    rw [show vec2 (I := I)
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x) 0 =
        smoothOrthoFrame (I := I) h x i x by simp only [vec2, ite_self],
      show vec2 (I := I)
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x) 1 =
        smoothOrthoFrame (I := I) h x i x by simp only [vec2, ite_self]]
    change Tensor0SSpace.toModel D1
        (fun _ : Fin 1 => connDiff (I := I) h q x
          (smoothOrthoFrame (I := I) h x i x)
          (smoothOrthoFrame (I := I) h x i x)) = _
    rw [grad_cc_apply (I := I) (M := M) q U x
      (connDiff (I := I) h q x
        (smoothOrthoFrame (I := I) h x i x)
        (smoothOrthoFrame (I := I) h x i x))]
    rw [← connDiff_eq_difference (I := I) q h]
    rw [connectionDifferenceOutput_apply]
    congr 2
  rw [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, one0_eq_unit (I := I) (M := M)]
  rw [scalarLapDiff_apply (I := I) (M := M) q h U x,
    hsecond h, hsecond q, hconn]
  have hlap := lap_sub_conn (I := I) (M := M)
    (LeviCivita (I := I) h) (LeviCivita (I := I) q)
    hcovh hcovq h q hmch hmcq f hf x
  rw [laplacian_levi_eq (I := I) h hf x,
    laplacian_levi_eq (I := I) q hf x] at hlap
  simpa only [Hs, Corr, f, hf] using hlap.symm



private theorem lapDiff_unit
    (q h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) q) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 0 I x from
            (lapDiffSec (I := I) (M := M) q h v).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 0 I x from
            (scalarLapDiffCc (I := I) q h
              (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) := by
  rw [lapDiffSec_apply (I := I) (M := M) q h v x,
    lift_unit (I := I) (M := M)]
  have hvalue := scalarLapDiff_eq (I := I) (M := M) q h
    (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2) x
  rw [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, one0_eq_unit (I := I) (M := M)] at hvalue
  exact hvalue.symm



theorem lapDiffCore_eq_cc
    (q h : SmoothRiemannianMetric I M)
    (v : ScalarH2Core (I := I) (M := M) q) :
    lapDiffCore (I := I) (M := M) q h v =
      SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0)
        (scalarLapDiffCc (I := I) q h
          (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)) := by
  change SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0)
      (lapDiffSec (I := I) (M := M) q h v) = _
  apply congrArg (fun W : SmoothCcTensor q 0 0 =>
    SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0) W)
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  exact clm0_ext (I := I) (M := M) (lapDiff_unit (I := I) (M := M) q h v x)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
