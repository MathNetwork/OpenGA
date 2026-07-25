import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Topology.FiberBundle.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]

def covApply (cov : CovariantDerivative I F V)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, V b) : Π b : M, V b :=
  fun b => cov.toFun Z b (X b)

@[simp] lemma covApply_apply (cov : CovariantDerivative I F V)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (b : M) :
    covApply cov X Z b = cov.toFun Z b (X b) := rfl

def riemannSec (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) : V x :=
  cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
    - cov.toFun Z x (VectorField.mlieBracket I X Y x)

lemma riemannSec_def (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) :
    riemannSec cov X Y Z x =
      cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
        - cov.toFun Z x (VectorField.mlieBracket I X Y x) := rfl

lemma riemannSec_swap (cov : CovariantDerivative I F V)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) :
    riemannSec cov X Y Z x = - riemannSec cov Y X Z x := by
  unfold riemannSec
  rw [VectorField.mlieBracket_swap_apply (V := X) (W := Y)]
  simp
  abel

@[simp] lemma riemannSec_self_eq_zero (cov : CovariantDerivative I F V)
    (X : Π b : M, TangentSpace I b) (Z : Π b : M, V b) (x : M) :
    riemannSec cov X X Z x = 0 := by
  unfold riemannSec
  rw [show VectorField.mlieBracket I X X = 0 from VectorField.mlieBracket_self]
  simp

end General

section TensorVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable {cov : CovariantDerivative I F V}

omit [VectorBundle ℝ F V] in
lemma riemannSec_add_left
    {X X' Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x)
    (hcX'Z : MDiffAt (T% (covApply cov X' Z)) x) :
    riemannSec cov (X + X') Y Z x = riemannSec cov X Y Z x + riemannSec cov X' Y Z x := by
  classical
  unfold riemannSec
  have h1 : cov.toFun (covApply cov Y Z) x ((X + X') x) =
      cov.toFun (covApply cov Y Z) x (X x) + cov.toFun (covApply cov Y Z) x (X' x) := by
    simp [Pi.add_apply]
  have hcov_add : covApply cov (X + X') Z = covApply cov X Z + covApply cov X' Z := by
    funext b
    simp [covApply, Pi.add_apply]
  have h2 : cov.toFun (covApply cov (X + X') Z) x (Y x) =
      cov.toFun (covApply cov X Z) x (Y x) + cov.toFun (covApply cov X' Z) x (Y x) := by
    rw [hcov_add]
    rw [cov.isCovariantDerivativeOnUniv.add hcXZ hcX'Z]
    rfl
  have hbr : VectorField.mlieBracket I (X + X') Y x =
      VectorField.mlieBracket I X Y x + VectorField.mlieBracket I X' Y x :=
    VectorField.mlieBracket_add_left hX hX'
  have h3 : cov.toFun Z x (VectorField.mlieBracket I (X + X') Y x) =
      cov.toFun Z x (VectorField.mlieBracket I X Y x)
        + cov.toFun Z x (VectorField.mlieBracket I X' Y x) := by
    rw [hbr]
    simp
  rw [h1, h2, h3]
  abel

omit [VectorBundle ℝ F V] in
lemma riemannSec_add_right
    {X Y Y' : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x)
    (hcY'Z : MDiffAt (T% (covApply cov Y' Z)) x) :
    riemannSec cov X (Y + Y') Z x = riemannSec cov X Y Z x + riemannSec cov X Y' Z x := by
  rw [riemannSec_swap, riemannSec_add_left hY hY' hcYZ hcY'Z,
      riemannSec_swap (cov := cov) (X := Y) (Y := X) (Z := Z),
      riemannSec_swap (cov := cov) (X := Y') (Y := X) (Z := Z)]
  abel

omit [VectorBundle ℝ F V] in
lemma riemannSec_smul_left
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x) :
    riemannSec cov (f • X) Y Z x = f x • riemannSec cov X Y Z x := by
  classical
  unfold riemannSec
  have h1 : cov.toFun (covApply cov Y Z) x ((f • X) x) =
      f x • cov.toFun (covApply cov Y Z) x (X x) := by
    simp
  have hcov_smul : covApply cov (f • X) Z = f • covApply cov X Z := by
    funext b
    simp [covApply]
  have h2 : cov.toFun (covApply cov (f • X) Z) x (Y x) =
      f x • cov.toFun (covApply cov X Z) x (Y x)
        + extDerivFun f x (Y x) • cov.toFun Z x (X x) := by
    rw [hcov_smul]
    rw [cov.isCovariantDerivativeOnUniv.leibniz hcXZ hf]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply]
  have hbr : VectorField.mlieBracket I (f • X) Y x =
      - (extDerivFun f x (Y x)) • X x
        + f x • VectorField.mlieBracket I X Y x := by
    have := VectorField.mlieBracket_smul_left (V := X) (W := Y) (x := x) hf hX
    convert this using 2
  have h3 : cov.toFun Z x (VectorField.mlieBracket I (f • X) Y x) =
      - extDerivFun f x (Y x) • cov.toFun Z x (X x)
        + f x • cov.toFun Z x (VectorField.mlieBracket I X Y x) := by
    rw [hbr]
    simp [neg_smul]
  rw [h1, h2, h3]
  rw [smul_sub, smul_sub]
  module

omit [VectorBundle ℝ F V] in
lemma riemannSec_smul_right
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x) :
    riemannSec cov X (f • Y) Z x = f x • riemannSec cov X Y Z x := by
  rw [riemannSec_swap, riemannSec_smul_left hf hY hcYZ,
      riemannSec_swap (cov := cov) (X := Y) (Y := X) (Z := Z),
      smul_neg, neg_neg]

end TensorVectorField

section CovApplySmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable {cov : CovariantDerivative I F V}

lemma covApply_contMDiffOn
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X Z)) Set.univ := by
  classical
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun b : M => (⟨b, cov.toFun Z b⟩ :
        TotalSpace (E →L[ℝ] F) fun b : M => TangentSpace I b →L[ℝ] V b)) Set.univ :=
    hcov.contMDiff.contMDiff (σ := Z) (hZ.contMDiffOn)
  intro x _hx
  exact (hop.contMDiffAt (Filter.univ_mem)).clm_bundle_apply (v := X) (hX x) |>.contMDiffWithinAt

lemma covApply_mdifferentiableAt
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, F)) ((∞ : WithTop ℕ∞) + 1) (T% Z)) :
    MDiffAt (T% (covApply cov X Z)) x := by
  have hAt : ContMDiffAt I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov X Z)) x :=
    (covApply_contMDiffOn hX hZ).contMDiffAt (Filter.univ_mem)
  exact hAt.mdifferentiableAt (by simp)

end CovApplySmooth

section TorsionFreeAbstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
variable (htor : cov.torsion = 0)

include htor in

lemma covApply_sub_eq_mlieBracket
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    covApply cov X Y x - covApply cov Y X x = VectorField.mlieBracket I X Y x :=
  (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hX hY

end TorsionFreeAbstract

section TorsionFree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

lemma riemannSec_torsionFree_form
    (htor : cov.torsion = 0)
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    riemannSec cov X Y Z x =
      cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x)
        - (cov.toFun Z x (cov.toFun Y x (X x)) - cov.toFun Z x (cov.toFun X x (Y x))) := by
  classical
  have hXY : VectorField.mlieBracket I X Y x =
      cov.toFun Y x (X x) - cov.toFun X x (Y x) :=
    ((CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hX hY).symm
  unfold riemannSec
  rw [hXY, map_sub]

end TorsionFree

section LeviCivitaTorsionFree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem LeviCivita_riemannSec_torsionFree_form
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    riemannSec (LeviCivita (I := I) g) X Y Z x =
      (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y Z) x (X x)
        - (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) X Z) x (Y x)
        - ((LeviCivita (I := I) g).toFun Z x
              ((LeviCivita (I := I) g).toFun Y x (X x))
            - (LeviCivita (I := I) g).toFun Z x
              ((LeviCivita (I := I) g).toFun X x (Y x))) :=
  riemannSec_torsionFree_form (cov := LeviCivita (I := I) g)
    (LeviCivita_torsion_eq_zero (I := I) g) hX hY

end LeviCivitaTorsionFree

section TensorSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable {cov : CovariantDerivative I F V}

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M] in
lemma riemannSec_add_third
    {X Y : Π b : M, TangentSpace I b} {Z Z' : Π b : M, V b} {x : M}
    (hZnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z) b)
    (hZ'nhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z') b)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x)
    (hcYZ' : MDiffAt (T% (covApply cov Y Z')) x)
    (hcYZZ' : MDiffAt (T% (covApply cov Y (Z + Z'))) x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x)
    (hcXZ' : MDiffAt (T% (covApply cov X Z')) x)
    (hcXZZ' : MDiffAt (T% (covApply cov X (Z + Z'))) x) :
    riemannSec cov X Y (Z + Z') x = riemannSec cov X Y Z x + riemannSec cov X Y Z' x := by
  classical
  unfold riemannSec
  have hYZZ'_ev : ∀ᶠ b in 𝓝 x,
      covApply cov Y (Z + Z') b = (covApply cov Y Z + covApply cov Y Z') b := by
    filter_upwards [hZnhd, hZ'nhd] with b hZb hZ'b
    change cov.toFun (Z + Z') b (Y b) = (cov.toFun Z b (Y b) + cov.toFun Z' b (Y b))
    rw [cov.isCovariantDerivativeOnUniv.add hZb hZ'b]
    rfl
  have hXZZ'_ev : ∀ᶠ b in 𝓝 x,
      covApply cov X (Z + Z') b = (covApply cov X Z + covApply cov X Z') b := by
    filter_upwards [hZnhd, hZ'nhd] with b hZb hZ'b
    change cov.toFun (Z + Z') b (X b) = (cov.toFun Z b (X b) + cov.toFun Z' b (X b))
    rw [cov.isCovariantDerivativeOnUniv.add hZb hZ'b]
    rfl
  have hcYZZ'_split : MDiffAt (T% (covApply cov Y Z + covApply cov Y Z')) x :=
    mdifferentiableAt_add_section hcYZ hcYZ'
  have hcXZZ'_split : MDiffAt (T% (covApply cov X Z + covApply cov X Z')) x :=
    mdifferentiableAt_add_section hcXZ hcXZ'
  have hY_term :
      cov.toFun (covApply cov Y (Z + Z')) x =
        cov.toFun (covApply cov Y Z + covApply cov Y Z') x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcYZZ' hcYZZ'_split (Filter.univ_mem) hYZZ'_ev
  have hX_term :
      cov.toFun (covApply cov X (Z + Z')) x =
        cov.toFun (covApply cov X Z + covApply cov X Z') x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcXZZ' hcXZZ'_split (Filter.univ_mem) hXZZ'_ev
  rw [hY_term, hX_term]
  rw [cov.isCovariantDerivativeOnUniv.add hcYZ hcYZ',
      cov.isCovariantDerivativeOnUniv.add hcXZ hcXZ']
  have hZZ'_at : cov.toFun (Z + Z') x =
      cov.toFun Z x + cov.toFun Z' x :=
    cov.isCovariantDerivativeOnUniv.add (hZnhd.self_of_nhds) (hZ'nhd.self_of_nhds)
  rw [hZZ'_at]
  simp only [ContinuousLinearMap.add_apply]
  abel


omit [CompleteSpace E] [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
lemma riemannSec_smul_third
    {f : M → ℝ} {X Y : Π b : M, TangentSpace I b} {Z : Π b : M, V b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hfnhd : ∀ᶠ b in 𝓝 x, MDiffAt f b)
    (hZnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z) b)
    (hZx : MDiffAt (T% Z) x)
    (hcXZ : MDiffAt (T% (covApply cov X Z)) x)
    (hcYZ : MDiffAt (T% (covApply cov Y Z)) x)
    (hcXfZ : MDiffAt (T% (covApply cov X (f • Z))) x)
    (hcYfZ : MDiffAt (T% (covApply cov Y (f • Z))) x)
    (hYf : MDiffAt (fun b => extDerivFun f b (Y b)) x)
    (hXf : MDiffAt (fun b => extDerivFun f b (X b)) x)
    (hf_smul_cYZ : MDiffAt (T% (f • covApply cov Y Z)) x)
    (hf_smul_cXZ : MDiffAt (T% (f • covApply cov X Z)) x)
    (hYf_smul_Z : MDiffAt (T% ((fun b => extDerivFun f b (Y b)) • Z)) x)
    (hXf_smul_Z : MDiffAt (T% ((fun b => extDerivFun f b (X b)) • Z)) x)
    (hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E)) :
    riemannSec cov X Y (f • Z) x = f x • riemannSec cov X Y Z x := by
  classical
  set Yf : M → ℝ := fun b => extDerivFun f b (Y b) with hYf_def
  set Xf : M → ℝ := fun b => extDerivFun f b (X b) with hXf_def
  have heventY :
      ∀ᶠ b in 𝓝 x, covApply cov Y (f • Z) b =
        ((f • covApply cov Y Z) + (Yf • Z)) b := by
    filter_upwards [hfnhd, hZnhd] with b hfb hZb
    change cov.toFun (f • Z) b (Y b) =
      f b • cov.toFun Z b (Y b) + extDerivFun f b (Y b) • Z b
    rw [cov.isCovariantDerivativeOnUniv.leibniz hZb hfb]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply]
  have heventX :
      ∀ᶠ b in 𝓝 x, covApply cov X (f • Z) b =
        ((f • covApply cov X Z) + (Xf • Z)) b := by
    filter_upwards [hfnhd, hZnhd] with b hfb hZb
    change cov.toFun (f • Z) b (X b) =
      f b • cov.toFun Z b (X b) + extDerivFun f b (X b) • Z b
    rw [cov.isCovariantDerivativeOnUniv.leibniz hZb hfb]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply]
  have hsplitY : MDiffAt (T% ((f • covApply cov Y Z) + (Yf • Z))) x :=
    mdifferentiableAt_add_section hf_smul_cYZ hYf_smul_Z
  have hsplitX : MDiffAt (T% ((f • covApply cov X Z) + (Xf • Z))) x :=
    mdifferentiableAt_add_section hf_smul_cXZ hXf_smul_Z
  have hY_replace :
      cov.toFun (covApply cov Y (f • Z)) x =
        cov.toFun ((f • covApply cov Y Z) + (Yf • Z)) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcYfZ hsplitY (Filter.univ_mem) heventY
  have hX_replace :
      cov.toFun (covApply cov X (f • Z)) x =
        cov.toFun ((f • covApply cov X Z) + (Xf • Z)) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcXfZ hsplitX (Filter.univ_mem) heventX
  unfold riemannSec
  rw [hY_replace, hX_replace]
  rw [cov.isCovariantDerivativeOnUniv.add hf_smul_cYZ hYf_smul_Z,
      cov.isCovariantDerivativeOnUniv.add hf_smul_cXZ hXf_smul_Z]
  have hf_mdiff : MDiffAt f x := hf.mdifferentiableAt (by simp)
  rw [cov.isCovariantDerivativeOnUniv.leibniz hcYZ hf_mdiff,
      cov.isCovariantDerivativeOnUniv.leibniz hZx hYf,
      cov.isCovariantDerivativeOnUniv.leibniz hcXZ hf_mdiff,
      cov.isCovariantDerivativeOnUniv.leibniz hZx hXf]
  rw [show cov.toFun (f • Z) x = f x • cov.toFun Z x + (extDerivFun f x).smulRight (Z x) from
      cov.isCovariantDerivativeOnUniv.leibniz hZx hf_mdiff]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.smulRight_apply]
  have hfound :
      extDerivFun f x (VectorField.mlieBracket I X Y x) =
        extDerivFun Yf x (X x) - extDerivFun Xf x (Y x) :=
    extDerivFun_apply_mlieBracket hX hY hf hx_int
  rw [hfound]
  simp only [hXf_def, hYf_def]
  simp only [covApply_apply]
  rw [sub_smul]
  module

end TensorSection

section Bianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma covApply_sub_eventuallyEq_mlieBracket
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.torsion = 0)
    {A B : Π b : M, TangentSpace I b} {x : M}
    (hAnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% A) b)
    (hBnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% B) b) :
    ∀ᶠ b in 𝓝 x,
      covApply cov A B b - covApply cov B A b = VectorField.mlieBracket I A B b := by
  filter_upwards [hAnhd, hBnhd] with b hAb hBb
  exact (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hAb hBb

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma cov_covApply_sub_eq_cov_mlieBracket
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.torsion = 0)
    {A B : Π b : M, TangentSpace I b} {x : M}
    (hAnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% A) b)
    (hBnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% B) b)
    (hcAB : MDiffAt (T% (covApply cov A B)) x)
    (hcBA : MDiffAt (T% (covApply cov B A)) x)
    (hbracket : MDiffAt (T% (VectorField.mlieBracket I A B)) x) :
    cov.toFun (covApply cov A B) x - cov.toFun (covApply cov B A) x =
      cov.toFun (VectorField.mlieBracket I A B) x := by
  classical
  set σ : Π b : M, TangentSpace I b := covApply cov A B - covApply cov B A with hσ_def
  have hσ_eq : covApply cov A B = σ + covApply cov B A := by funext b; simp [σ]
  have hσ_mdiff : MDiffAt (T% σ) x := by
    have hneg : MDiffAt (T% (-(covApply cov B A))) x :=
      mdifferentiableAt_neg_section hcBA
    have := mdifferentiableAt_add_section hcAB hneg
    convert this using 1
    funext b; simp [σ, sub_eq_add_neg]
  have hadd_at_x :
      cov.toFun (covApply cov A B) x = cov.toFun σ x + cov.toFun (covApply cov B A) x := by
    rw [hσ_eq]
    exact cov.isCovariantDerivativeOnUniv.add hσ_mdiff hcBA
  have hσ_val : cov.toFun σ x =
      cov.toFun (covApply cov A B) x - cov.toFun (covApply cov B A) x := by
    rw [hadd_at_x]; abel
  have hsec_ev : ∀ᶠ b in 𝓝 x, σ b = VectorField.mlieBracket I A B b := by
    have := covApply_sub_eventuallyEq_mlieBracket (cov := cov) htor hAnhd hBnhd
    filter_upwards [this] with b hb
    change (covApply cov A B - covApply cov B A) b = _
    rw [Pi.sub_apply]; exact hb
  have hcov_swap :
      cov.toFun σ x = cov.toFun (VectorField.mlieBracket I A B) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hσ_mdiff hbracket (Filter.univ_mem) hsec_ev
  rw [← hcov_swap, hσ_val]


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem riemannSec_first_bianchi_levi_civita
    (g : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hXnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% X) b)
    (hYnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Y) b)
    (hZnhd : ∀ᶠ b in 𝓝 x, MDiffAt (T% Z) b)
    (hcXY : MDiffAt (T% (covApply (LeviCivita (I := I) g) X Y)) x)
    (hcYX : MDiffAt (T% (covApply (LeviCivita (I := I) g) Y X)) x)
    (hcXZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) X Z)) x)
    (hcZX : MDiffAt (T% (covApply (LeviCivita (I := I) g) Z X)) x)
    (hcYZ : MDiffAt (T% (covApply (LeviCivita (I := I) g) Y Z)) x)
    (hcZY : MDiffAt (T% (covApply (LeviCivita (I := I) g) Z Y)) x)
    (hbrXY : MDiffAt (T% (VectorField.mlieBracket I X Y)) x)
    (hbrYZ : MDiffAt (T% (VectorField.mlieBracket I Y Z)) x)
    (hbrZX : MDiffAt (T% (VectorField.mlieBracket I Z X)) x)
    (hX2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% X) x)
    (hY2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% Y) x)
    (hZ2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2) (T% Z) x) :
    riemannSec (LeviCivita (I := I) g) X Y Z x +
      riemannSec (LeviCivita (I := I) g) Y Z X x +
      riemannSec (LeviCivita (I := I) g) Z X Y x = 0 := by
  classical
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set cov := LeviCivita (I := I) g with hcov
  have htor : cov.torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g
  unfold riemannSec
  have hpairX :
      cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) =
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) := by
    have := cov_covApply_sub_eq_cov_mlieBracket (cov := cov) htor hYnhd hZnhd hcYZ hcZY hbrYZ
    have happ : (cov.toFun (covApply cov Y Z) x - cov.toFun (covApply cov Z Y) x) (X x) =
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) := by rw [this]
    simp only [ContinuousLinearMap.sub_apply] at happ
    exact happ
  have hpairY :
      cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) =
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) := by
    have := cov_covApply_sub_eq_cov_mlieBracket (cov := cov) htor hZnhd hXnhd hcZX hcXZ hbrZX
    have happ : (cov.toFun (covApply cov Z X) x - cov.toFun (covApply cov X Z) x) (Y x) =
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) := by rw [this]
    simp only [ContinuousLinearMap.sub_apply] at happ
    exact happ
  have hpairZ :
      cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) =
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) := by
    have := cov_covApply_sub_eq_cov_mlieBracket (cov := cov) htor hXnhd hYnhd hcXY hcYX hbrXY
    have happ : (cov.toFun (covApply cov X Y) x - cov.toFun (covApply cov Y X) x) (Z x) =
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) := by rw [this]
    simp only [ContinuousLinearMap.sub_apply] at happ
    exact happ
  have hJacobi := VectorField.leibniz_identity_mlieBracket_apply (I := I)
    (U := X) (V := Y) (W := Z) (x := x) hX2 hY2 hZ2
  have hJac_cyc :
      VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x = 0 := by
    have hbr_XZ : VectorField.mlieBracket I X Z =
        - VectorField.mlieBracket I Z X :=
      VectorField.mlieBracket_swap (V := X) (W := Z)
    have hab1 : VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x =
        - VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x :=
      VectorField.mlieBracket_swap_apply (V := VectorField.mlieBracket I X Y) (W := Z)
    have hab2 : VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) x =
        - VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
      conv_lhs => rw [hbr_XZ]
      have hsmul : (-VectorField.mlieBracket I Z X) = (-1 : ℝ) • VectorField.mlieBracket I Z X := by
        ext b; simp
      rw [hsmul]
      rw [VectorField.mlieBracket_const_smul_right (c := (-1 : ℝ)) (V := Y)
        (W := VectorField.mlieBracket I Z X) (x := x) hbrZX]
      simp
    rw [hab1, hab2] at hJacobi
    rw [hJacobi]; abel
  have hpairXYZ :
      cov.toFun (VectorField.mlieBracket I Y Z) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x) =
      VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x := by
    have htf : cov.toFun X x (VectorField.mlieBracket I Y Z x) -
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) =
        VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x :=
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hbrYZ hX
    have hbr_swap :
        VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x =
        - VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x :=
      VectorField.mlieBracket_swap_apply
        (V := VectorField.mlieBracket I Y Z) (W := X)
    have : cov.toFun (VectorField.mlieBracket I Y Z) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x) =
        - VectorField.mlieBracket I (VectorField.mlieBracket I Y Z) X x := by
      rw [← htf]; abel
    rw [this, hbr_swap]; abel
  have hpairYZX :
      cov.toFun (VectorField.mlieBracket I Z X) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x) =
      VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
    have htf : cov.toFun Y x (VectorField.mlieBracket I Z X x) -
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) =
        VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x :=
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hbrZX hY
    have hbr_swap :
        VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x =
        - VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x :=
      VectorField.mlieBracket_swap_apply
        (V := VectorField.mlieBracket I Z X) (W := Y)
    have : cov.toFun (VectorField.mlieBracket I Z X) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x) =
        - VectorField.mlieBracket I (VectorField.mlieBracket I Z X) Y x := by
      rw [← htf]; abel
    rw [this, hbr_swap]; abel
  have hpairZXY :
      cov.toFun (VectorField.mlieBracket I X Y) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x) =
      VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
    have htf : cov.toFun Z x (VectorField.mlieBracket I X Y x) -
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) =
        VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x :=
      (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp htor hbrXY hZ
    have hbr_swap :
        VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x =
        - VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x :=
      VectorField.mlieBracket_swap_apply
        (V := VectorField.mlieBracket I X Y) (W := Z)
    have : cov.toFun (VectorField.mlieBracket I X Y) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x) =
        - VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z x := by
      rw [← htf]; abel
    rw [this, hbr_swap]; abel
  have hgoal :
      (cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x)) +
      (cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x)) +
      (cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x)) =
      (VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x +
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x +
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x) := by
    have e1 : cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) =
        cov.toFun (VectorField.mlieBracket I Y Z) x (X x) := hpairX
    have e2 : cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) =
        cov.toFun (VectorField.mlieBracket I Z X) x (Y x) := hpairY
    have e3 : cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) =
        cov.toFun (VectorField.mlieBracket I X Y) x (Z x) := hpairZ
    have h1 : cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x) =
        VectorField.mlieBracket I X (VectorField.mlieBracket I Y Z) x := by
      rw [e1]; exact hpairXYZ
    have h2 : cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x) =
        VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) x := by
      rw [e2]; exact hpairYZX
    have h3 : cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x) =
        VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) x := by
      rw [e3]; exact hpairZXY
    have hLHS : ((cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x)) +
      (cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x)) +
      (cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x))) =
      (cov.toFun (covApply cov Y Z) x (X x) - cov.toFun (covApply cov Z Y) x (X x) -
        cov.toFun X x (VectorField.mlieBracket I Y Z x)) +
      (cov.toFun (covApply cov Z X) x (Y x) - cov.toFun (covApply cov X Z) x (Y x) -
        cov.toFun Y x (VectorField.mlieBracket I Z X x)) +
      (cov.toFun (covApply cov X Y) x (Z x) - cov.toFun (covApply cov Y X) x (Z x) -
        cov.toFun Z x (VectorField.mlieBracket I X Y x)) := by abel
    rw [hLHS, h1, h2, h3]
  rw [hgoal]
  exact hJac_cyc

end Bianchi

section RiemannOp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F]

noncomputable def smoothExtensionTangent (x : M) (v : TangentSpace I x) :
    Π b : M, TangentSpace I b :=
  fun b => ((ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v).choose : Cₛ^(⊤ : ℕ∞)⟮I; E,
    (TangentSpace I : M → Type _)⟯) b

noncomputable def smoothExtensionFiber (x : M) (u : V x) :
    Π b : M, V b :=
  fun b => ((ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := F) (V := V) x u).choose : Cₛ^(⊤ : ℕ∞)⟮I; F, V⟯) b

omit [CompleteSpace E] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp]
lemma smoothExtensionTangent_eq (x : M) (v : TangentSpace I x) :
    smoothExtensionTangent (I := I) x v x = v := by
  classical
  exact (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v).choose_spec

omit [CompleteSpace E] [SigmaCompactSpace M] [BoundarylessManifold I M] [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)] in
@[simp]
lemma smoothExtensionFiber_eq (x : M) (u : V x) :
    smoothExtensionFiber (I := I) (F := F) (V := V) x u x = u := by
  classical
  exact (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := F) (V := V) x u).choose_spec

noncomputable def riemannOpFun (cov : CovariantDerivative I F V) (x : M) :
    TangentSpace I x → TangentSpace I x → V x → V x :=
  fun v w u =>
    riemannSec cov
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionFiber (I := I) (F := F) (V := V) x u) x

omit [CompleteSpace E] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem riemannOpFun_def (cov : CovariantDerivative I F V) (x : M)
    (v w : TangentSpace I x) (u : V x) :
    riemannOpFun cov x v w u =
      riemannSec cov
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w)
        (smoothExtensionFiber (I := I) (F := F) (V := V) x u) x := rfl

end RiemannOp

end Connection
end Integral
end DifferentialGeometry
