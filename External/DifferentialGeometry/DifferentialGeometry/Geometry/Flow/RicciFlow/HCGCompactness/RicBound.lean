import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTimeDeriv
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBoundClaims
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBoundGoodFrame
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivArityBridge
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

set_option autoImplicit false
set_option linter.style.longLine false







































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

open DifferentialGeometry.PDE.RicciFlow in


omit [Module.Finite ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem normSq0S_nonneg'
    [Module.Finite ℝ E]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    0 ≤ Tensor0SBundle.normSq0S (I := I) g x s A := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv A]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _




omit [Module.Finite ℝ E] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [IsManifold I 1 M] in
omit [I.Boundaryless] [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
private theorem mcdNorm_eq_at
    [Module.Finite ℝ E]
    (h gRef : SmoothRiemannianMetric I M) (N : Nat) (x : M) :
    metricCovDerivNorm (I := I) N h gRef x =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
        (iterCov (I := I) gRef 2
          (Tensor0SBundle.metricTensorField (I := I) h) N x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i j
  exact metricCovDerivNorm_eq_iterCov (I := I) h gRef N basis hinv





noncomputable def ricCovTower
    (g gRef : SmoothRiemannianMetric I M) (s : Nat) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (2 + s) :=
  iterCov (I := I) gRef 2
    (DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
      (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)) s














def MovingShiBoundOn
    (U : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (N : Nat) (KShi : Real) : Prop :=
  forall s : Nat, s <= N -> forall i : Nat,
    forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ U ->
      Real.sqrt
        (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x (2 + s)
          (ricCovTower (I := I) (gSeq i t) (gSeq i t) s x)) <= KShi

set_option backward.isDefEq.respectTransparency false in







omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem perDomain
    [Module.Finite ℝ E]
    (gRef : SmoothRiemannianMetric I M)
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (basisE : Module.Basis (Fin (Module.finrank Real E)) Real E)
    {w : Set M} (hwopen : IsOpen w) (hwsub : w ⊆ e₀.baseSet)
    (eps : Real) (heps0 : 0 ≤ eps)
    (hepsSm : (Fintype.card (Fin (Module.finrank Real E)) : Real) * eps ≤ 1 / 2)
    (hGnear : ∀ z ∈ w, ∀ i j : Fin (Module.finrank Real E),
      |gramE (I := I) e₀ gRef basisE z i j - (if i = j then 1 else 0)| ≤ eps)
    (hFwd : ∀ z, ∀ hz : z ∈ e₀.baseSet, z ∈ w →
      ∀ (s : ℕ) (A : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) s z),
        (∑ I0 : Fin s → Fin (Module.finrank Real E),
          Tensor0SBundle.component0S (I := I)
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hz) A I0 ^ 2) ≤
          2 ^ s * Tensor0SBundle.normSq0S (I := I) gRef z s A)
    (N : ℕ) (hN : 1 ≤ N)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (Cg : ℕ → Real)
    (KShi : Real) (hKShi0 : 0 ≤ KShi) :
    ∃ Cpp Cppp : Real, 0 ≤ Cpp ∧ 0 ≤ Cppp ∧
      ∀ g : SmoothRiemannianMetric I M,
        (∀ z ∈ w, ∀ v : TangentSpace I z,
          Bmax⁻¹ * gRef.inner z v v ≤ g.inner z v v ∧
          Bmax⁻¹ * g.inner z v v ≤ gRef.inner z v v ∧
          gRef.inner z v v ≤ Bmax * g.inner z v v) →
        (∀ z ∈ w, ∀ j : ℕ, 1 ≤ j → j < N →
          metricCovDerivNorm (I := I) j g gRef z ≤ Cg j) →
        (∀ z ∈ w, ∀ s : ℕ, s ≤ N →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g z (2 + s)
            (iterCov (I := I) g 2
              (CovariantDerivative.ricciSection (I := I) (M := M)
                (leviCivitaConnectionOfMetric (I := I) g)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                  (I := I) (M := M) g)) s z)) ≤ KShi) →
        ∀ x ∈ w,
          compL2 (iterCovComp (I := I)
              (fun a y' => e₀.localFrame basisE a y')
              (fun y' => christoffelSymbolInFrame
                (leviCivitaConnectionOfMetric (I := I) gRef)
                (fun a y'' => e₀.localFrame basisE a y'')
                ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
              (frameComp0S (I := I)
                (CovariantDerivative.ricciSection (I := I) (M := M)
                  (leviCivitaConnectionOfMetric (I := I) g)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                    (I := I) (M := M) g))
                (fun a y' => e₀.localFrame basisE a y')) N x) ≤
            Cpp * compL2 (iterCovComp (I := I)
              (fun a y' => e₀.localFrame basisE a y')
              (fun y' => christoffelSymbolInFrame
                (leviCivitaConnectionOfMetric (I := I) gRef)
                (fun a y'' => e₀.localFrame basisE a y'')
                ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
              (frameComp0S (I := I) (metricTensorField (I := I) g)
                (fun a y' => e₀.localFrame basisE a y')) N x) + Cppp := by
  classical
  have hBmax0 : (0 : Real) < Bmax := lt_of_lt_of_le one_pos hBmax1

  set Kg : Real := ∑ j ∈ Finset.range (N + 1), 2 ^ (2 + j) * max (Cg j) 0 with hKgdef
  have hKg0 : 0 ≤ Kg :=
    Finset.sum_nonneg fun j _ => by positivity
  set C0 : Real :=
    Real.sqrt (Fintype.card (Fin (Module.finrank Real E))) * (2 * Bmax) with hC0def
  set KShiC : Real := 2 ^ (2 + N) * Bmax ^ (2 + N) * KShi with hKShiCdef
  have hKShiC0 : 0 ≤ KShiC := by positivity

  have hCLgen := fun c : ℕ => claim1_LC (I := I) hwopen gRef
    (fun a y' => e₀.localFrame basisE a y')
    ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub)
    (fun d => (frame_e_mdiffOn e₀ basisE d).mono hwsub)
    (fun d i j => ((lcChrist_e_mdiffOn e₀ gRef basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j))
    C0 Kg c
  choose CL hCL0 hCLb using hCLgen

  obtain ⟨Cpp, Cppp, hpp0, hppp0, haN⟩ := aN_component (r₀ := 2) (rg := 2) (I := I) hwopen
    (fun a y' => e₀.localFrame basisE a y')
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) gRef)
      (fun a y'' => e₀.localFrame basisE a y'')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
    (fun d => (frame_e_mdiffOn e₀ basisE d).mono hwsub)
    (fun d i j => ((lcChrist_e_mdiffOn e₀ gRef basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j))
    N hN (fun c => CL c * (1 + Kg))
    (fun c => mul_nonneg (hCL0 c) (by linarith))
    (CL (N - 1)) (hCL0 (N - 1)) KShiC hKShiC0
  refine ⟨Cpp, Cppp, hpp0, hppp0, ?_⟩
  intro g hequivW hmcd hShiPt x hx

  have hchrGw : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) g)
        (fun a y'' => e₀.localFrame basisE a y'')
        ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ g basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        (fun a y' => e₀.localFrame basisE a y')
        (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hgsmW := fun k => (gCompField_mdiffOn e₀ g basisE k).mono hwsub
  have hRicSmW := fun k => (ricCompField_mdiffOn e₀ g basisE k).mono hwsub

  have hGinvW : ∀ z ∈ w, compL2 (ginvCompField (I := I) e₀ g basisE z) ≤ C0 := by
    intro z hz
    exact movingGinv_le (I := I) e₀ g gRef basisE Bmax hBmax0
      (fun v => (hequivW z hz v).1) eps heps0 hepsSm (fun i j => hGnear z hz i j)
  have hinvW : ∀ z ∈ w, ∀ c e : Fin (Module.finrank Real E),
      (∑ l, frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y') z
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE z (Fin.snoc (fun _ : Fin 1 => e) l)) =
      if c = e then 1 else 0 :=
    fun z hz c e => ginv_hinv (I := I) e₀ g basisE (hwsub hz) c e

  have hgB : ∀ z ∈ w, ∀ j : ℕ, 1 ≤ j → j ≤ N - 1 →
      compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y')) j z) ≤ Kg := by
    intro z hz j h1 hjN
    have htow := compL2_tower_le (I := I) gRef gRef
      (Tensor0SBundle.metricTensorField (I := I) g)
      (fun a y' => e₀.localFrame basisE a y')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) hwopen hz
      (fun s A => hFwd z (hwsub hz) hz s A) j
    have hmc := mcdNorm_eq_at (I := I) g gRef j z
    have hcg := hmcd z hz j h1 (by omega)
    have hKgterm : (2 : Real) ^ (2 + j) * max (Cg j) 0 ≤ Kg := by
      rw [hKgdef]
      exact Finset.single_le_sum
        (f := fun j' => (2 : Real) ^ (2 + j') * max (Cg j') 0)
        (fun j' _ => by positivity) (Finset.mem_range.mpr (by omega))
    have h2p : (0 : Real) ≤ 2 ^ (2 + j) := by positivity
    calc compL2 (iterCovComp (I := I)
          (fun a y' => e₀.localFrame basisE a y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (frameComp0S (I := I) (metricTensorField (I := I) g)
            (fun a y' => e₀.localFrame basisE a y')) j z)
        ≤ 2 ^ (2 + j) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + j)
            (iterCov (I := I) gRef 2
              (Tensor0SBundle.metricTensorField (I := I) g) j z)) := htow
      _ = 2 ^ (2 + j) * metricCovDerivNorm (I := I) j g gRef z := by rw [hmc]
      _ ≤ 2 ^ (2 + j) * max (Cg j) 0 :=
          mul_le_mul_of_nonneg_left (le_trans hcg (le_max_left _ _)) h2p
      _ ≤ Kg := hKgterm

  have hDlow : ∀ c : ℕ, c < N - 1 → ∀ z ∈ w,
      compL2 (iterCovCompU (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (chrDiffField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')) c z) ≤
      CL c * (1 + Kg) := by
    intro c hc z hz
    have h := hCLb c g hchrGw hgsmW (ginvCompField (I := I) e₀ g basisE)
      hinvW hGinvW (fun z' hz' j h1 h2 => hgB z' hz' j h1 (by omega)) z hz
    have hg := hgB z hz (c + 1) (by omega) (by omega)
    have hnn : (0 : Real) ≤ compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y')) (c + 1) z) := compL2_nonneg _
    nlinarith [hCL0 c, h, hg, hnn]
  have hDtop : ∀ z ∈ w,
      compL2 (iterCovCompU (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (chrDiffField
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')) (N - 1) z) ≤
      CL (N - 1) * (1 + compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I) (metricTensorField (I := I) g)
          (fun a y' => e₀.localFrame basisE a y')) N z)) := by
    intro z hz
    have h := hCLb (N - 1) g hchrGw hgsmW (ginvCompField (I := I) e₀ g basisE)
      hinvW hGinvW (fun z' hz' j h1 h2 => hgB z' hz' j h1 h2) z hz
    rwa [show N - 1 + 1 = N from by omega] at h

  have hShiComp : ∀ z ∈ w, ∀ s : ℕ, s ≤ N →
      compL2 (iterCovComp (I := I)
        (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) g)
          (fun a y'' => e₀.localFrame basisE a y'')
          ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
        (frameComp0S (I := I)
          (CovariantDerivative.ricciSection (I := I) (M := M)
            (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) g))
          (fun a y' => e₀.localFrame basisE a y')) s z) ≤ KShiC := by
    intro z hz s hsN
    have htow := compL2_tower_le (I := I) g gRef
      (CovariantDerivative.ricciSection (I := I) (M := M)
        (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g))
      (fun a y' => e₀.localFrame basisE a y')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) hwopen hz
      (fun s' A => hFwd z (hwsub hz) hz s' A) s
    have hswap := (Tensor0SBundle.normSq0S_le_of_metric_equiv (I := I) g gRef z (2 + s)
      hBmax1 (fun v => ⟨(hequivW z hz v).2.1, (hequivW z hz v).2.2⟩)
      (iterCov (I := I) g 2
        (CovariantDerivative.ricciSection (I := I) (M := M)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
            (I := I) (M := M) g)) s z)).2
    rw [zpow_natCast] at hswap
    have hnn := normSq0S_nonneg' (I := I) g z (2 + s)
      (iterCov (I := I) g 2
        (CovariantDerivative.ricciSection (I := I) (M := M)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
            (I := I) (M := M) g)) s z)
    have hsqv := hShiPt z hz s hsN
    have hval : Tensor0SBundle.normSq0S (I := I) g z (2 + s)
        (iterCov (I := I) g 2
          (CovariantDerivative.ricciSection (I := I) (M := M)
            (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) g)) s z) ≤ KShi ^ 2 := by
      calc Tensor0SBundle.normSq0S (I := I) g z (2 + s)
            (iterCov (I := I) g 2
              (CovariantDerivative.ricciSection (I := I) (M := M)
                (leviCivitaConnectionOfMetric (I := I) g)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                  (I := I) (M := M) g)) s z)
          = Real.sqrt (Tensor0SBundle.normSq0S (I := I) g z (2 + s)
              (iterCov (I := I) g 2
                (CovariantDerivative.ricciSection (I := I) (M := M)
                  (leviCivitaConnectionOfMetric (I := I) g)
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                    (I := I) (M := M) g)) s z)) ^ 2 := (Real.sq_sqrt hnn).symm
        _ ≤ KShi ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqv 2
    have hBp : (0 : Real) ≤ Bmax ^ (2 + s) := by positivity
    have hgRefBound : Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
        (iterCov (I := I) g 2
          (CovariantDerivative.ricciSection (I := I) (M := M)
            (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) g)) s z) ≤ Bmax ^ (2 + s) * KShi ^ 2 :=
      le_trans hswap (mul_le_mul_of_nonneg_left hval hBp)
    have hsqrtBound : Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
        (iterCov (I := I) g 2
          (CovariantDerivative.ricciSection (I := I) (M := M)
            (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) g)) s z)) ≤ Bmax ^ (2 + s) * KShi := by
      calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
            (iterCov (I := I) g 2
              (CovariantDerivative.ricciSection (I := I) (M := M)
                (leviCivitaConnectionOfMetric (I := I) g)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                  (I := I) (M := M) g)) s z))
          ≤ Real.sqrt (Bmax ^ (2 + s) * KShi ^ 2) := Real.sqrt_le_sqrt hgRefBound
        _ = Real.sqrt (Bmax ^ (2 + s)) * Real.sqrt (KShi ^ 2) :=
            Real.sqrt_mul (by positivity) _
        _ = Real.sqrt (Bmax ^ (2 + s)) * KShi := by
            rw [Real.sqrt_sq hKShi0]
        _ ≤ Bmax ^ (2 + s) * KShi := by
            refine mul_le_mul_of_nonneg_right ?_ hKShi0
            have h2 : (Bmax ^ (2 + s)) ≤ (Bmax ^ (2 + s)) ^ 2 := by
              have h1 : (1 : Real) ≤ Bmax ^ (2 + s) := one_le_pow₀ hBmax1
              nlinarith
            calc Real.sqrt (Bmax ^ (2 + s))
                ≤ Real.sqrt ((Bmax ^ (2 + s)) ^ 2) := Real.sqrt_le_sqrt h2
              _ = Bmax ^ (2 + s) := Real.sqrt_sq (by positivity)
    have h2mono : (2 : Real) ^ (2 + s) ≤ 2 ^ (2 + N) :=
      pow_le_pow_right₀ one_le_two (by omega)
    have hBmono : Bmax ^ (2 + s) ≤ Bmax ^ (2 + N) :=
      pow_le_pow_right₀ hBmax1 (by omega)
    calc compL2 (iterCovComp (I := I)
          (fun a y' => e₀.localFrame basisE a y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g)
            (fun a y'' => e₀.localFrame basisE a y'')
            ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
          (frameComp0S (I := I)
            (CovariantDerivative.ricciSection (I := I) (M := M)
              (leviCivitaConnectionOfMetric (I := I) g)
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                (I := I) (M := M) g))
            (fun a y' => e₀.localFrame basisE a y')) s z)
        ≤ 2 ^ (2 + s) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (2 + s)
            (iterCov (I := I) g 2
              (CovariantDerivative.ricciSection (I := I) (M := M)
                (leviCivitaConnectionOfMetric (I := I) g)
                (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                  (I := I) (M := M) g)) s z)) := htow
      _ ≤ 2 ^ (2 + s) * (Bmax ^ (2 + s) * KShi) :=
          mul_le_mul_of_nonneg_left hsqrtBound (by positivity)
      _ ≤ 2 ^ (2 + N) * (Bmax ^ (2 + N) * KShi) := by
          have hb : Bmax ^ (2 + s) * KShi ≤ Bmax ^ (2 + N) * KShi :=
            mul_le_mul_of_nonneg_right hBmono hKShi0
          have hnn2 : (0 : Real) ≤ Bmax ^ (2 + s) * KShi := by positivity
          calc (2 : Real) ^ (2 + s) * (Bmax ^ (2 + s) * KShi)
              ≤ 2 ^ (2 + N) * (Bmax ^ (2 + s) * KShi) :=
                mul_le_mul_of_nonneg_right h2mono hnn2
            _ ≤ 2 ^ (2 + N) * (Bmax ^ (2 + N) * KShi) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
      _ = KShiC := by rw [hKShiCdef]; ring

  exact haN
    (fun y' => christoffelSymbolInFrame
      (leviCivitaConnectionOfMetric (I := I) g)
      (fun a y'' => e₀.localFrame basisE a y'')
      ((e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub) y')
    hchrGw
    (frameComp0S (I := I)
      (CovariantDerivative.ricciSection (I := I) (M := M)
        (leviCivitaConnectionOfMetric (I := I) g)
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g))
      (fun a y' => e₀.localFrame basisE a y'))
    hRicSmW hDlow
    (frameComp0S (I := I) (metricTensorField (I := I) g)
      (fun a y' => e₀.localFrame basisE a y'))
    hDtop hShiComp x hx





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem ric_tower_const
    [Module.Finite ℝ E]
    {K U : Set M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat) (hN : 1 <= N)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (Cg : Nat -> Real)
    (KShi : Real) (hKShi0 : 0 ≤ KShi) :
    exists Cpp Cppp : Real, 0 <= Cpp ∧ 0 <= Cppp ∧
      forall {β ψ : Real}
        {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
        (B : Real -> Real)
        (_hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
        (_hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
        (_hBprev : forall r : Nat, 1 <= r -> r < N ->
          MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
        (_hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi),
        forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
          forall x : M, x ∈ K ->
            Real.sqrt
              (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
                (ricCovTower (I := I) (gSeq i t) gRef N x)) <=
              Cpp * metricCovDerivNorm (I := I) N (gSeq i t) gRef x + Cppp := by
  classical

  choose basisE u' eps hopen hxu hsubB heps0 hepsSm hGnear hON hFwd hRev using
    fun x : M => exists_goodFrame_compBound (I := I) gRef x

  obtain ⟨tF, htF⟩ := hKc.elim_finite_subcover (fun x : M => u' x ∩ U)
    (fun x => (hopen x).inter hU)
    (fun z hz => Set.mem_iUnion.mpr ⟨z, ⟨hxu z, hKU hz⟩⟩)

  have hPD := fun x₀ : M => perDomain (I := I) gRef
    (trivializationAt E (TangentSpace I : M → Type _) x₀) (basisE x₀)
    ((hopen x₀).inter hU)
    ((Set.inter_subset_left).trans (hsubB x₀))
    (eps x₀) (heps0 x₀) (hepsSm x₀)
    (fun z hz i j => hGnear x₀ z hz.1 i j)
    (fun z hz hzw s A => hFwd x₀ z hz hzw.1 s A)
    N hN Bmax hBmax1 Cg KShi hKShi0
  choose Cpp' Cppp' hpp0 hppp0 hPDb using hPD

  set Cu : Real :=
    (3 / 2) * ((Fintype.card (Fin (Module.finrank Real E)) : Real) + 1) with hCudef
  have hCu1 : (1 : Real) ≤ Cu := by
    rw [hCudef]
    have hc0 : (0 : Real) ≤ (Fintype.card (Fin (Module.finrank Real E)) : Real) :=
      Nat.cast_nonneg _
    nlinarith
  have hCuP0 : (0 : Real) ≤ Cu ^ (2 + N) := by positivity
  set CppF : Real := ∑ x₀ ∈ tF, Cu ^ (2 + N) * Cpp' x₀ * 2 ^ (2 + N) with hCppFdef
  set CpppF : Real := ∑ x₀ ∈ tF, Cu ^ (2 + N) * Cppp' x₀ with hCpppFdef
  have hCppF0 : 0 ≤ CppF := Finset.sum_nonneg fun x₀ _ =>
    mul_nonneg (mul_nonneg hCuP0 (hpp0 x₀)) (by positivity)
  have hCpppF0 : 0 ≤ CpppF := Finset.sum_nonneg fun x₀ _ =>
    mul_nonneg hCuP0 (hppp0 x₀)
  refine ⟨CppF, CpppF, hCppF0, hCpppF0, ?_⟩
  intro β ψ gSeq B hequiv hBmax hBprev hShi i t ht x hxK

  have hxcov := htF hxK
  rw [Set.mem_iUnion₂] at hxcov
  obtain ⟨x₀, hx₀F, hxw⟩ := hxcov

  have hequivIt := hequiv i t ht
  have hBt1 : (1 : Real) ≤ B t := hequivIt.1
  have hBtBm : B t ≤ Bmax := hBmax t ht
  have hBt0 : (0 : Real) < B t := lt_of_lt_of_le one_pos hBt1
  have hBm0 : (0 : Real) < Bmax := lt_of_lt_of_le one_pos hBmax1
  have hpack : ∀ z ∈ (u' x₀ ∩ U), ∀ v : TangentSpace I z,
      Bmax⁻¹ * gRef.inner z v v ≤ (gSeq i t).inner z v v ∧
      Bmax⁻¹ * (gSeq i t).inner z v v ≤ gRef.inner z v v ∧
      gRef.inner z v v ≤ Bmax * (gSeq i t).inner z v v := by
    intro z hz v
    have h2 := hequivIt.2 z hz.2 v
    have hgr0 : 0 ≤ gRef.inner z v v := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact (gRef.pos z v hv).le
    have hg0 : 0 ≤ (gSeq i t).inner z v v := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact ((gSeq i t).pos z v hv).le
    have hinvBB : Bmax⁻¹ ≤ (B t)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hBt0 hBtBm
    refine ⟨?_, ?_, ?_⟩
    · have h1' := h2.1
      nlinarith [hinvBB, hgr0, h2.1]
    · have hup : (gSeq i t).inner z v v ≤ Bmax * gRef.inner z v v :=
        le_trans h2.2 (by nlinarith [hgr0])
      calc Bmax⁻¹ * (gSeq i t).inner z v v
          ≤ Bmax⁻¹ * (Bmax * gRef.inner z v v) :=
            mul_le_mul_of_nonneg_left hup (by positivity)
        _ = gRef.inner z v v := by field_simp
    · have hstep : gRef.inner z v v ≤ B t * (gSeq i t).inner z v v := by
        calc gRef.inner z v v
            = B t * ((B t)⁻¹ * gRef.inner z v v) := by field_simp
          _ ≤ B t * (gSeq i t).inner z v v :=
              mul_le_mul_of_nonneg_left h2.1 hBt0.le
      nlinarith [hg0, hBtBm, hstep]

  have hmcdW : ∀ z ∈ (u' x₀ ∩ U), ∀ j : ℕ, 1 ≤ j → j < N →
      metricCovDerivNorm (I := I) j (gSeq i t) gRef z ≤ Cg j :=
    fun z hz j h1 hj => hBprev j h1 hj i t ht z hz.2
  have hShiW : ∀ z ∈ (u' x₀ ∩ U), ∀ s : ℕ, s ≤ N →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (gSeq i t) z (2 + s)
        (iterCov (I := I) (gSeq i t) 2
          (CovariantDerivative.ricciSection (I := I) (M := M)
            (leviCivitaConnectionOfMetric (I := I) (gSeq i t))
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) (gSeq i t))) s z)) ≤ KShi :=
    fun z hz s hs => hShi s hs i t ht z hz.2

  have hAN := hPDb x₀ (gSeq i t) hpack hmcdW hShiW x hxw

  have hxbase : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    ((Set.inter_subset_left).trans (hsubB x₀)) hxw
  have hwsub₀ : (u' x₀ ∩ U) ⊆ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    (Set.inter_subset_left).trans (hsubB x₀)

  have hLHS := sqrt_tower_le_compL2 (I := I) gRef
    (CovariantDerivative.ricciSection (I := I) (M := M)
      (leviCivitaConnectionOfMetric (I := I) (gSeq i t))
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) (gSeq i t)))
    (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')
    (((trivializationAt E (TangentSpace I : M → Type _) x₀).isLocalFrameOn_localFrame_baseSet
        I 1 (basisE x₀)).mono hwsub₀)
    ((hopen x₀).inter hU) hxw Cu hCu1
    (fun s A => hRev x₀ x hxbase hxw.1 s A) N

  have hRHS := compL2_tower_le (I := I) gRef gRef
    (Tensor0SBundle.metricTensorField (I := I) (gSeq i t))
    (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')
    (((trivializationAt E (TangentSpace I : M → Type _) x₀).isLocalFrameOn_localFrame_baseSet
        I 1 (basisE x₀)).mono hwsub₀)
    ((hopen x₀).inter hU) hxw
    (fun s A => hFwd x₀ x hxbase hxw.1 s A) N
  have hmc := mcdNorm_eq_at (I := I) (gSeq i t) gRef N x
  have hmcd0 : 0 ≤ metricCovDerivNorm (I := I) N (gSeq i t) gRef x := by
    rw [hmc]
    exact Real.sqrt_nonneg _

  have hppF : Cu ^ (2 + N) * Cpp' x₀ * 2 ^ (2 + N) ≤ CppF := by
    rw [hCppFdef]
    exact Finset.single_le_sum
      (f := fun x₁ => Cu ^ (2 + N) * Cpp' x₁ * 2 ^ (2 + N))
      (fun x₁ _ => mul_nonneg (mul_nonneg hCuP0 (hpp0 x₁)) (by positivity)) hx₀F
  have hpppF : Cu ^ (2 + N) * Cppp' x₀ ≤ CpppF := by
    rw [hCpppFdef]
    exact Finset.single_le_sum
      (f := fun x₁ => Cu ^ (2 + N) * Cppp' x₁)
      (fun x₁ _ => mul_nonneg hCuP0 (hppp0 x₁)) hx₀F

  have hcompRic0 : 0 ≤ compL2 (iterCovComp (I := I)
      (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')
      (fun y' => christoffelSymbolInFrame
        (leviCivitaConnectionOfMetric (I := I) gRef)
        (fun a y'' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y'')
        (((trivializationAt E (TangentSpace I : M → Type _) x₀).isLocalFrameOn_localFrame_baseSet
            I 1 (basisE x₀)).mono hwsub₀) y')
      (frameComp0S (I := I) (metricTensorField (I := I) (gSeq i t))
        (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')) N x) :=
    compL2_nonneg _
  calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
        (ricCovTower (I := I) (gSeq i t) gRef N x))
      ≤ Cu ^ (2 + N) * compL2 (iterCovComp (I := I)
          (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y'')
            (((trivializationAt E (TangentSpace I : M → Type _) x₀).isLocalFrameOn_localFrame_baseSet
                I 1 (basisE x₀)).mono hwsub₀) y')
          (frameComp0S (I := I)
            (CovariantDerivative.ricciSection (I := I) (M := M)
              (leviCivitaConnectionOfMetric (I := I) (gSeq i t))
              (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                (I := I) (M := M) (gSeq i t)))
            (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')) N x) := hLHS
    _ ≤ Cu ^ (2 + N) * (Cpp' x₀ * compL2 (iterCovComp (I := I)
          (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef)
            (fun a y'' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y'')
            (((trivializationAt E (TangentSpace I : M → Type _) x₀).isLocalFrameOn_localFrame_baseSet
                I 1 (basisE x₀)).mono hwsub₀) y')
          (frameComp0S (I := I) (metricTensorField (I := I) (gSeq i t))
            (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')) N x) + Cppp' x₀) :=
        mul_le_mul_of_nonneg_left hAN hCuP0
    _ ≤ Cu ^ (2 + N) * (Cpp' x₀ * (2 ^ (2 + N) *
          metricCovDerivNorm (I := I) N (gSeq i t) gRef x) + Cppp' x₀) := by
        refine mul_le_mul_of_nonneg_left ?_ hCuP0
        refine add_le_add ?_ le_rfl
        refine mul_le_mul_of_nonneg_left ?_ (hpp0 x₀)
        calc compL2 (iterCovComp (I := I)
              (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')
              (fun y' => christoffelSymbolInFrame
                (leviCivitaConnectionOfMetric (I := I) gRef)
                (fun a y'' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y'')
                (((trivializationAt E (TangentSpace I : M → Type _) x₀).isLocalFrameOn_localFrame_baseSet
                    I 1 (basisE x₀)).mono hwsub₀) y')
              (frameComp0S (I := I) (metricTensorField (I := I) (gSeq i t))
                (fun a y' => (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame (basisE x₀) a y')) N x)
            ≤ 2 ^ (2 + N) * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
                (iterCov (I := I) gRef 2
                  (Tensor0SBundle.metricTensorField (I := I) (gSeq i t)) N x)) := hRHS
          _ = 2 ^ (2 + N) * metricCovDerivNorm (I := I) N (gSeq i t) gRef x := by
              rw [hmc]
    _ = (Cu ^ (2 + N) * Cpp' x₀ * 2 ^ (2 + N)) *
          metricCovDerivNorm (I := I) N (gSeq i t) gRef x +
        Cu ^ (2 + N) * Cppp' x₀ := by ring
    _ ≤ CppF * metricCovDerivNorm (I := I) N (gSeq i t) gRef x + CpppF :=
        add_le_add (mul_le_mul_of_nonneg_right hppF hmcd0) hpppF





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ric_bound
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat) (hN : 1 <= N)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
    (Cg : Nat -> Real)
    (hBprev : forall r : Nat, 1 <= r -> r < N ->
      MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi) :
    exists Cpp Cppp : Real, 0 <= Cpp ∧ 0 <= Cppp ∧
      forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (2 + N)
              (ricCovTower (I := I) (gSeq i t) gRef N x)) <=
            Cpp * metricCovDerivNorm (I := I) N (gSeq i t) gRef x + Cppp := by
  obtain ⟨Cpp, Cppp, hCpp, hCppp, hfield⟩ :=
    ric_tower_const (I := I) hKc hU hKU N hN Bmax hBmax1 Cg KShi hKShi0
  exact ⟨Cpp, Cppp, hCpp, hCppp,
    hfield (β := β) (ψ := ψ) (gSeq := gSeq) B hequiv hBmax hBprev hShi⟩




noncomputable def nablaRicReal
    (gSeq : Nat → Real → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p : Nat) :
    Nat → Real → (x : M) →
      Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (p + 2) x :=
  fun i s x =>
    (ricCovTower (I := I) (gSeq i s) gRef p x).domDomCongr (acEquiv p)


omit [Module.Finite ℝ E] [I.Boundaryless] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [IsManifold I 2 M] in
omit [SigmaCompactSpace M] in
theorem nablaRicReal_normSq
    [Module.Finite ℝ E]
    (gSeq : Nat → Real → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (p i : Nat) (s : Real) (x : M) :
    Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
        (nablaRicReal (I := I) gSeq gRef p i s x) =
      Tensor0SBundle.normSq0S (I := I) gRef x (2 + p)
        (ricCovTower (I := I) (gSeq i s) gRef p x) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i' j'
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i' j'
  exact Tensor0SBundle.normSq0S_domDomCongr (I := I) gRef x basis hinv (acEquiv p)
    (ricCovTower (I := I) (gSeq i s) gRef p x)





omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ric_bound_const
    [Module.Finite ℝ E]
    {K U : Set M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat) (hN : 1 <= N)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (Cg : Nat -> Real)
    (KShi : Real) (hKShi0 : 0 ≤ KShi) :
    exists Cpp Cppp : Real, 0 <= Cpp ∧ 0 <= Cppp ∧
      forall {β ψ : Real}
        {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
        (B : Real -> Real)
        (_hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
        (_hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
        (_hBprev : forall r : Nat, 1 <= r -> r < N ->
          MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
        (_hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi),
        forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
          forall x : M, x ∈ K ->
            Real.sqrt
              (Tensor0SBundle.normSq0S (I := I) gRef x (N + 2)
                (nablaRicReal (I := I) gSeq gRef N i s x)) <=
              Cpp * metricCovDerivNorm (I := I) N (gSeq i s) gRef x + Cppp := by
  obtain ⟨Cpp, Cppp, hCpp, hCppp, hfield⟩ :=
    ric_tower_const (I := I) hKc hU hKU N hN Bmax hBmax1 Cg KShi hKShi0
  refine ⟨Cpp, Cppp, hCpp, hCppp, ?_⟩
  intro β ψ gSeq B hequiv hBmax hBprev hShi i s hs x hx
  rw [nablaRicReal_normSq]
  exact hfield B hequiv hBmax hBprev hShi i s hs x hx




omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ric_bound_field
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat) (hN : 1 <= N)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
    (Cg : Nat -> Real)
    (hBprev : forall r : Nat, 1 <= r -> r < N ->
      MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi) :
    exists Cpp Cppp : Real, 0 <= Cpp ∧ 0 <= Cppp ∧
      forall i : Nat, forall s : Real, s ∈ Set.Icc β ψ ->
        forall x : M, x ∈ K ->
          Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) gRef x (N + 2)
              (nablaRicReal (I := I) gSeq gRef N i s x)) <=
            Cpp * metricCovDerivNorm (I := I) N (gSeq i s) gRef x + Cppp := by
  obtain ⟨Cpp, Cppp, h0, h1, hb⟩ :=
    ric_bound_const (I := I) hKc hU hKU N hN Bmax hBmax1 Cg KShi hKShi0
  exact ⟨Cpp, Cppp, h0, h1,
    hb (β := β) (ψ := ψ) (gSeq := gSeq) B hequiv hBmax hBprev hShi⟩







omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem normsq_evol_of_comp
    [Module.Finite ℝ E]
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {p : Nat}
    {nablaRic : Nat -> Real -> (x : M) ->
      Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (p + 2) x}
    (hev : ∀ i : Nat, ∀ x ∈ K, ∀ s ∈ Set.Icc β ψ,
      ∀ v : Fin (p + 2) → TangentSpace I x,
        HasDerivAt
          (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef p x v)
          (((-2 : Real) • nablaRic i s x) v) s) :
    MetricCovOrderNormSqEvolutionOn (I := I) K β ψ gSeq gRef p nablaRic := by
  intro i x hx s hs
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) gRef x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) gRef x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) gRef basis hON
    intro i' j'
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h' i' j'

  have hcomp : ∀ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
      HasDerivAt
        (fun r => Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (gSeq i r) gRef p x) I0)
        (Tensor0SBundle.component0S (I := I) basis
          ((-2 : Real) • nablaRic i s x) I0) s := by
    intro I0
    have happ := hev i x hx s hs (fun q => basis (I0 q))
    simpa [Tensor0SBundle.component0S_apply] using happ

  have hU_eq : (fun r : Real => metricCovDerivNorm (I := I) p (gSeq i r) gRef x ^ 2) =
      (fun r : Real => ∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
        Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (gSeq i r) gRef p x) I0 ^ 2) := by
    funext r
    have hnn := normSq0S_nonneg' (I := I) gRef x (p + 2)
      (metricCovDeriv (I := I) (gSeq i r) gRef p x)
    rw [metricCovDerivNorm, Real.sq_sqrt hnn,
      Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x (p + 2) basis hinv]

  have hders : HasDerivAt
      (fun r : Real => ∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
        Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (gSeq i r) gRef p x) I0 ^ 2)
      (∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
        2 * Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 *
        Tensor0SBundle.component0S (I := I) basis
          ((-2 : Real) • nablaRic i s x) I0) s := by
    have hterms : ∀ I0 ∈ (Finset.univ :
        Finset (Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)))),
        HasDerivAt
          (fun r => Tensor0SBundle.component0S (I := I) basis
            (metricCovDeriv (I := I) (gSeq i r) gRef p x) I0 ^ 2)
          (2 * Tensor0SBundle.component0S (I := I) basis
            (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 *
           Tensor0SBundle.component0S (I := I) basis
            ((-2 : Real) • nablaRic i s x) I0) s := by
      intro I0 _
      simpa [pow_one] using (hcomp I0).pow 2
    have hsum := HasDerivAt.sum hterms
    have hfn : (∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
        fun r : Real => Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (gSeq i r) gRef p x) I0 ^ 2) =
        (fun r : Real =>
          ∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
            Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) (gSeq i r) gRef p x) I0 ^ 2) := by
      funext r
      simp [Finset.sum_apply]
    rw [hfn] at hsum
    exact hsum
  refine ⟨∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
    2 * Tensor0SBundle.component0S (I := I) basis
      (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 *
    Tensor0SBundle.component0S (I := I) basis
      ((-2 : Real) • nablaRic i s x) I0, ?_, ?_⟩
  · rw [hU_eq]
    exact hders
  ·
    have habs : |∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
        2 * Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 *
        Tensor0SBundle.component0S (I := I) basis
          ((-2 : Real) • nablaRic i s x) I0| ≤
        (∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
          Tensor0SBundle.component0S (I := I) basis
            (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 ^ 2) +
        ∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
          Tensor0SBundle.component0S (I := I) basis
            ((-2 : Real) • nablaRic i s x) I0 ^ 2 := by
      calc |∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
            2 * Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 *
            Tensor0SBundle.component0S (I := I) basis
              ((-2 : Real) • nablaRic i s x) I0|
          ≤ ∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
            |2 * Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 *
            Tensor0SBundle.component0S (I := I) basis
              ((-2 : Real) • nablaRic i s x) I0| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
            (Tensor0SBundle.component0S (I := I) basis
              (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 ^ 2 +
             Tensor0SBundle.component0S (I := I) basis
              ((-2 : Real) • nablaRic i s x) I0 ^ 2) := by
            refine Finset.sum_le_sum fun I0 _ => ?_
            refine abs_le.mpr ⟨?_, ?_⟩
            · nlinarith [sq_nonneg (Tensor0SBundle.component0S (I := I) basis
                (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 +
              Tensor0SBundle.component0S (I := I) basis
                ((-2 : Real) • nablaRic i s x) I0)]
            · nlinarith [sq_nonneg (Tensor0SBundle.component0S (I := I) basis
                (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 -
              Tensor0SBundle.component0S (I := I) basis
                ((-2 : Real) • nablaRic i s x) I0)]
        _ = (∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
              Tensor0SBundle.component0S (I := I) basis
                (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 ^ 2) +
            ∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
              Tensor0SBundle.component0S (I := I) basis
                ((-2 : Real) • nablaRic i s x) I0 ^ 2 :=
            Finset.sum_add_distrib
    have hUs : (∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
        Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (gSeq i s) gRef p x) I0 ^ 2) =
        metricCovDerivNorm (I := I) p (gSeq i s) gRef x ^ 2 := by
      have := congrFun hU_eq s
      exact this.symm
    have hnablaSq : (∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
        Tensor0SBundle.component0S (I := I) basis
          ((-2 : Real) • nablaRic i s x) I0 ^ 2) =
        (2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
          (nablaRic i s x))) ^ 2 := by
      have hnn := normSq0S_nonneg' (I := I) gRef x (p + 2) (nablaRic i s x)
      have hsum : (∑ I0 : Fin (p + 2) → Fin (Module.finrank Real (TangentSpace I x)),
          Tensor0SBundle.component0S (I := I) basis
            ((-2 : Real) • nablaRic i s x) I0 ^ 2) =
          Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
            ((-2 : Real) • nablaRic i s x) :=
        (Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x (p + 2)
          basis hinv _).symm
      have hsmul : Tensor0SBundle.normSq0S (I := I) gRef x (p + 2)
          ((-2 : Real) • nablaRic i s x) =
          4 * Tensor0SBundle.normSq0S (I := I) gRef x (p + 2) (nablaRic i s x) := by
        rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x (p + 2) basis hinv,
          Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) gRef x (p + 2) basis hinv,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun I0 _ => ?_
        have hc : Tensor0SBundle.component0S (I := I) basis
            ((-2 : Real) • nablaRic i s x) I0 =
            (-2 : Real) * Tensor0SBundle.component0S (I := I) basis
              (nablaRic i s x) I0 := by
          rw [Tensor0SBundle.component0S_apply, Tensor0SBundle.component0S_apply]
          simp
        rw [hc]
        ring
      rw [hsum, hsmul, mul_pow, Real.sq_sqrt hnn]
      norm_num
    rw [hUs, hnablaSq] at habs
    exact habs

set_option backward.isDefEq.respectTransparency false in







omit [Module.Finite ℝ E] in
omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
omit [SigmaCompactSpace M] in
theorem hevComp_of_solutions
    [Module.Finite ℝ E]
    {K : Set M} {β ψ : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M} {N : Nat}
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i))
    (hS : ∀ i : Nat, IsSolutionOn (I := I) (S i))
    (hmet : ∀ (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
    (hreg : ∀ i : Nat, Set.Icc β ψ ⊆ (D i).regular)
    (hswap : ∀ i : Nat, ∀ p : ℕ, p < N →
      ∀ V : Fin (p + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _), ∀ x₀ : M,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I) (D i).carrier (D i).regular
        ({x₀} : Set M)
        (fun r p' => (covDerivOfField (I := I) gRef (solnMetricField (I := I) (S i) r) p) p'
          (fun a : Fin (p + 2) => V a p'))
        (fun r p' => (covDerivOfField (I := I) gRef (solnEvolField (I := I) (S i) r) p) p'
          (fun a : Fin (p + 2) => V a p'))) :
    ∀ i : Nat, ∀ x ∈ K, ∀ s ∈ Set.Icc β ψ,
      ∀ v : Fin (N + 2) → TangentSpace I x,
        HasDerivAt
          (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef N x v)
          (((-2 : Real) • nablaRicReal (I := I) gSeq gRef N i s x) v) s := by
  intro i x hx s hs v
  have h := solnTower_hasDerivAt (I := I) gRef (S i) (hS i) N (hswap i)
    N le_rfl s (hreg i hs) x v
  have hfun : (fun r : Real =>
      (covDerivOfField (I := I) gRef (solnMetricField (I := I) (S i) r) N) x v)
      = fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef N x v := by
    funext r
    simp only [solnMetricField, hmet i r]
    rfl
  have hsolng : solnRicField (I := I) (S i) s
      = CovariantDerivative.ricciSection (I := I) (M := M)
          (leviCivitaConnectionOfMetric (I := I) (gSeq i s))
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
            (I := I) (M := M) (gSeq i s)) := by
    simp only [solnRicField, hmet i s]
  have hric : ricCovTower (I := I) (gSeq i s) gRef N
      = iterCov (I := I) gRef 2
          (CovariantDerivative.ricciSection (I := I) (M := M)
            (leviCivitaConnectionOfMetric (I := I) (gSeq i s))
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
              (I := I) (M := M) (gSeq i s))) N := rfl
  have hsec : (covDerivOfField (I := I) gRef (solnRicField (I := I) (S i) s) N) x
      = nablaRicReal (I := I) gSeq gRef N i s x := by
    rw [hsolng, covDerivOfField_eq_iterCov, ← hric]
    show ContinuousMultilinearMap.domDomCongr (acEquiv N)
        (ricCovTower (I := I) (gSeq i s) gRef N x)
      = nablaRicReal (I := I) gSeq gRef N i s x
    simp only [nablaRicReal]
  have hval : (covDerivOfField (I := I) gRef (solnEvolField (I := I) (S i) s) N) x v
      = ((-2 : Real) • nablaRicReal (I := I) gSeq gRef N i s x) v := by
    simp only [solnEvolField]
    rw [covDerivOfField_smul, ContMDiffSection.coe_smul, Pi.smul_apply, hsec]
  rw [hfun, hval] at h
  exact h








omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem covOrderBound_stage
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat) (hN : 1 <= N)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
    (Cg : Nat -> Real)
    (hBprev : forall r : Nat, 1 <= r -> r < N ->
      MetricCovDerivOrderBoundOnWindow (I := I) U β ψ gSeq gRef r (Cg r))
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hevComp : ∀ i : Nat, ∀ x ∈ K, ∀ s ∈ Set.Icc β ψ,
      ∀ v : Fin (N + 2) → TangentSpace I x,
        HasDerivAt
          (fun r : Real => metricCovDeriv (I := I) (gSeq i r) gRef N x v)
          (((-2 : Real) • nablaRicReal (I := I) gSeq gRef N i s x) v) s)
    (initC : Real) (hinitC0 : 0 ≤ initC)
    (hinit : forall i : Nat, forall x : M, x ∈ K ->
      metricCovDerivNorm (I := I) N (gSeq i t0) gRef x <= initC)
    (timeRadius : Real)
    (htime : forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius) :
    exists Cw : Real,
      MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef N Cw := by
  obtain ⟨Cpp, Cppp, hpp0, hppp0, hfield⟩ := ric_bound_field (I := I) hKc hU hKU
    N hN B hequiv Bmax hBmax1 hBmax Cg hBprev KShi hKShi0 hShi
  refine ⟨metricCovOrderEvolutionConstant Cpp Cppp timeRadius initC, ?_⟩
  exact metricCovOrderWindow_of_evolution (I := I)
    { t0_mem := ht0
      nablaRic := nablaRicReal (I := I) gSeq gRef N
      normsq_evol := normsq_evol_of_comp (I := I) hevComp
      Cpp := Cpp
      Cppp := Cppp
      Cpp_nonneg := hpp0
      Cppp_nonneg := hppp0
      ric_bound := hfield
      initC := initC
      initC_nonneg := hinitC0
      init_bound := hinit
      timeRadius := timeRadius
      time_abs_le := htime }









omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem covOrderBound_tower
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hev : ∀ r : Nat, 1 ≤ r → r ≤ N → ∀ i : Nat, ∀ x ∈ U, ∀ s ∈ Set.Icc β ψ,
      ∀ v : Fin (r + 2) → TangentSpace I x,
        HasDerivAt
          (fun r' : Real => metricCovDeriv (I := I) (gSeq i r') gRef r x v)
          (((-2 : Real) • nablaRicReal (I := I) gSeq gRef r i s x) v) s)
    (initC : Nat -> Real) (hinitC0 : ∀ r : Nat, 0 ≤ initC r)
    (hinit : ∀ r : Nat, 1 ≤ r → r ≤ N → ∀ i : Nat, ∀ x ∈ U,
      metricCovDerivNorm (I := I) r (gSeq i t0) gRef x <= initC r)
    (timeRadius : Real)
    (htime : forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius) :
    ∀ r : Nat, 1 ≤ r → r ≤ N →
      exists Cw : Real,
        MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef r Cw := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  suffices hmain : ∀ r : Nat, 1 ≤ r → r ≤ N →
      ∀ K' : Set M, IsCompact K' → ∀ U' : Set M, IsOpen U' → K' ⊆ U' → U' ⊆ U →
        exists Cw : Real,
          MetricCovDerivOrderBoundOnWindow (I := I) K' β ψ gSeq gRef r Cw by
    intro r h1 hrN
    exact hmain r h1 hrN K hKc U hU hKU (subset_refl U)
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
    intro h1 hrN K' hK'c U' hU' hK'U' hU'U
    obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK'c hU' hK'U'
    have hLsubU : (interior L : Set M) ⊆ U := fun x hx =>
      hU'U (hLU (interior_subset hx))

    have hex : ∀ q : Nat, ∃ Cq : Real, 1 ≤ q → q < r →
        MetricCovDerivOrderBoundOnWindow (I := I) (interior L) β ψ gSeq gRef q Cq := by
      intro q
      by_cases hq : 1 ≤ q ∧ q < r
      · obtain ⟨Cq, hCq⟩ := ihr q hq.2 hq.1 (le_trans (le_of_lt hq.2) hrN)
          L hLc U' hU' hLU hU'U
        exact ⟨Cq, fun _ _ =>
          metricCovOrderWindow_mono (I := I) interior_subset hCq⟩
      · exact ⟨0, fun ha hb => absurd ⟨ha, hb⟩ hq⟩
    choose Cg hCg using hex
    exact covOrderBound_stage (I := I) hK'c isOpen_interior hKL r h1 B
      (metricUniformEquivalentOnWindow_mono (I := I) hLsubU hequiv)
      Bmax hBmax1 hBmax Cg
      (fun q hq1 hqr => hCg q hq1 hqr)
      KShi hKShi0
      (fun s hs i t ht x hx => hShi s (le_trans hs hrN) i t ht x (hLsubU hx))
      ht0
      (fun i x hx s hs v => hev r h1 hrN i x (hU'U (hK'U' hx)) s hs v)
      (initC r) (hinitC0 r)
      (fun i x hx => hinit r h1 hrN i x (hU'U (hK'U' hx)))
      timeRadius htime

set_option backward.isDefEq.respectTransparency false in










omit [Module.Finite ℝ E] in
omit [SigmaCompactSpace M] in
theorem covOrderBound_of_soln
    [Module.Finite ℝ E]
    {K U : Set M} {β ψ t0 : Real}
    {gSeq : Nat -> Real -> SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (N : Nat)
    (D : Nat -> RealTimeInterval)
    (S : (i : Nat) -> SolutionOn (I := I) (M := M) (D i))
    (hS : ∀ i : Nat, IsSolutionOn (I := I) (S i))
    (hmet : ∀ (i : Nat) (r : Real), (S i).family.metric r = gSeq i r)
    (hreg : ∀ i : Nat, Set.Icc β ψ ⊆ (D i).regular)
    (B : Real -> Real)
    (hequiv : MetricUniformEquivalentOnWindow (I := I) U β ψ gRef gSeq B)
    (Bmax : Real) (hBmax1 : 1 ≤ Bmax)
    (hBmax : ∀ t ∈ Set.Icc β ψ, B t ≤ Bmax)
    (KShi : Real) (hKShi0 : 0 ≤ KShi)
    (hShi : MovingShiBoundOn (I := I) U β ψ gSeq N KShi)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hDreg : ∀ i : Nat, ∀ {t : Real}, t ∈ (D i).regular → (D i).regular ∈ 𝓝 t)
    (initC : Nat -> Real) (hinitC0 : ∀ r : Nat, 0 ≤ initC r)
    (hinit : ∀ r : Nat, 1 ≤ r → r ≤ N → ∀ i : Nat, ∀ x ∈ U,
      metricCovDerivNorm (I := I) r (gSeq i t0) gRef x <= initC r)
    (timeRadius : Real)
    (htime : forall t : Real, t ∈ Set.Icc β ψ -> |t - t0| <= timeRadius) :
    ∀ r : Nat, 1 ≤ r → r ≤ N →
      exists Cw : Real,
        MetricCovDerivOrderBoundOnWindow (I := I) K β ψ gSeq gRef r Cw := by
  refine covOrderBound_tower (I := I) hKc hU hKU N B hequiv Bmax hBmax1 hBmax
    KShi hKShi0 hShi ht0 ?_ initC hinitC0 hinit timeRadius htime
  intro r h1 hrN
  exact hevComp_of_solutions (I := I) (K := U) D S hS hmet hreg
    (fun i p hp V x₀ =>
      solnTowerSwap_reg (I := I) gRef (S i) (hS i) N (hDreg i)
        p (lt_of_lt_of_le hp hrN) V x₀)

end HCGCompactness
end DifferentialGeometry
