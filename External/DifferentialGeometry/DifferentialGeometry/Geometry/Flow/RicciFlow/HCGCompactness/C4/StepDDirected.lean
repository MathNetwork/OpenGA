import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1ApproxIso
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackField
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.Distances

set_option autoImplicit false
set_option linter.style.longLine false























noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold
open DifferentialGeometry.Integral.Connection Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section Chain


noncomputable def PartialDiffeomorph.refl (M : Type u) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] :
    PartialDiffeomorph I I M M (∞ : WithTop ℕ∞) where
  toPartialEquiv := PartialEquiv.refl M
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn



noncomputable def chainComp {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) (j l : ℕ) :
    PartialDiffeomorph I I (Mf j) (Mf (j + l)) (∞ : WithTop ℕ∞) :=
  Nat.rec
    (motive := fun l => PartialDiffeomorph I I (Mf j) (Mf (j + l)) (∞ : WithTop ℕ∞))
    (PartialDiffeomorph.refl (I := I) (Mf j))
    (fun l prev =>
      PartialDiffeomorph.trans (E := E) (H := H) (I := I) (M := Mf j)
        (N := Mf (j + l)) (P := Mf (j + l + 1)) prev (Ψ (j + l)))
    l





noncomputable def chainComp' {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j m : ℕ), j + l = m → PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞) :=
  Nat.rec
    (motive := fun l => ∀ j m : ℕ, j + l = m →
      PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞))
    (fun j m h => (Nat.add_zero j ▸ h : j = m) ▸ PartialDiffeomorph.refl (I := I) (Mf j))
    (fun l ih j m h =>
      PartialDiffeomorph.trans (E := E) (H := H) (I := I) (M := Mf j)
        (N := Mf (j + 1)) (P := Mf m) (Ψ j) (ih (j + 1) m (by omega)))


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_apply_succ {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j l : ℕ) (x : Mf j) :
    (chainComp (I := I) (Mf := Mf) Ψ j (l + 1) : Mf j → Mf (j + (l + 1))) x
      = (Ψ (j + l) : Mf (j + l) → Mf (j + l + 1))
          ((chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) x) :=
  rfl


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_base {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (b : ∀ j, Mf j)
    (hbase : ∀ j, (Ψ j : Mf j → Mf (j + 1)) (b j) = b (j + 1))
    (j l : ℕ) :
    (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) (b j) = b (j + l) := by
  induction l with
  | zero =>
      rfl
  | succ l ih =>
      rw [chainComp_apply_succ, ih]
      simpa [Nat.add_assoc] using hbase (j + l)



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_add_apply {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) (x : Mf j) :
    cast (congrArg Mf (Nat.add_assoc j a b).symm)
        ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) : Mf j → Mf (j + (a + b))) x) =
      (chainComp (I := I) (Mf := Mf) Ψ (j + a) b : Mf (j + a) → Mf ((j + a) + b))
        ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x) := by
  have cast_step : ∀ (m n : ℕ) (h : m = n) (y : Mf m),
      cast (congrArg Mf (congrArg Nat.succ h))
          ((Ψ m : Mf m → Mf (m + 1)) y) =
        (Ψ n : Mf n → Mf (n + 1)) (cast (congrArg Mf h) y) := by
    intro m n h y
    subst h
    rfl
  induction b with
  | zero =>
      rfl
  | succ b ih =>
      change
        cast (congrArg Mf (Nat.add_assoc j a (b + 1)).symm)
            ((Ψ (j + (a + b)) : Mf (j + (a + b)) → Mf (j + (a + b) + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                Mf j → Mf (j + (a + b))) x)) =
          (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
            ((chainComp (I := I) (Mf := Mf) Ψ (j + a) b :
              Mf (j + a) → Mf ((j + a) + b))
              ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x))
      calc
        cast (congrArg Mf (Nat.add_assoc j a (b + 1)).symm)
            ((Ψ (j + (a + b)) : Mf (j + (a + b)) → Mf (j + (a + b) + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                Mf j → Mf (j + (a + b))) x)) =
            (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
              (cast (congrArg Mf (Nat.add_assoc j a b).symm)
                ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                  Mf j → Mf (j + (a + b))) x)) := by
              simpa only [Nat.add_succ] using
                cast_step (j + (a + b)) ((j + a) + b) (Nat.add_assoc j a b).symm
                  ((chainComp (I := I) (Mf := Mf) Ψ j (a + b) :
                    Mf j → Mf (j + (a + b))) x)
        _ = (Ψ ((j + a) + b) : Mf ((j + a) + b) → Mf ((j + a) + b + 1))
              ((chainComp (I := I) (Mf := Mf) Ψ (j + a) b :
                Mf (j + a) → Mf ((j + a) + b))
                ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x)) := by
              rw [ih]


noncomputable def chainCompAssoc {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    PartialDiffeomorph I I (Mf j) (Mf ((j + a) + b)) (∞ : WithTop ℕ∞) :=
  (Nat.add_assoc j a b).symm ▸ chainComp (I := I) (Mf := Mf) Ψ j (a + b)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
private theorem targetCast_source {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    {j l m : ℕ} (h : l = m)
    (Φ : PartialDiffeomorph I I (Mf j) (Mf l) (∞ : WithTop ℕ∞)) :
    (h ▸ Φ).source = Φ.source := by
  subst h
  rfl


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainAssoc_source {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b).source =
      (chainComp (I := I) (Mf := Mf) Ψ j (a + b)).source := by
  simpa only [chainCompAssoc] using
    targetCast_source (I := I) (Nat.add_assoc j a b).symm
      (chainComp (I := I) (Mf := Mf) Ψ j (a + b))


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainCompAssoc_apply {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) (x : Mf j) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b : Mf j → Mf ((j + a) + b)) x =
      (chainComp (I := I) (Mf := Mf) Ψ (j + a) b : Mf (j + a) → Mf ((j + a) + b))
        ((chainComp (I := I) (Mf := Mf) Ψ j a : Mf j → Mf (j + a)) x) := by
  have cast_apply : ∀ {m n : ℕ} (h : m = n)
      (F : PartialDiffeomorph I I (Mf j) (Mf m) (∞ : WithTop ℕ∞)) (y : Mf j),
      ((h ▸ F : PartialDiffeomorph I I (Mf j) (Mf n) (∞ : WithTop ℕ∞)) : Mf j → Mf n) y =
        cast (congrArg Mf h) ((F : Mf j → Mf m) y) := by
    intro m n h F y
    subst h
    rfl
  unfold chainCompAssoc
  rw [cast_apply]
  exact chainComp_add_apply (I := I) (Mf := Mf) Ψ j a b x


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainCompAssoc_eq {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j a b : ℕ) :
    (chainCompAssoc (I := I) (Mf := Mf) Ψ j a b : Mf j → Mf ((j + a) + b)) =
      (PartialDiffeomorph.trans (I := I)
        (chainComp (I := I) (Mf := Mf) Ψ j a)
        (chainComp (I := I) (Mf := Mf) Ψ (j + a) b) : Mf j → Mf ((j + a) + b)) := by
  funext x
  exact chainCompAssoc_apply (I := I) (Mf := Mf) Ψ j a b x


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp'_apply_succ {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (l j m : ℕ) (h : j + (l + 1) = m) (x : Mf j) :
    (chainComp' (I := I) (Mf := Mf) Ψ (l + 1) j m h : Mf j → Mf m) x
      = (chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) m (by omega) : Mf (j + 1) → Mf m)
          ((Ψ j : Mf j → Mf (j + 1)) x) :=
  rfl



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp'_apply_zero {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (j m : ℕ) (h : j + 0 = m) (x : Mf j) :
    (chainComp' (I := I) (Mf := Mf) Ψ 0 j m h : Mf j → Mf m) x
      = (Nat.add_zero j ▸ h : j = m) ▸ x := by
  have hj : j = m := Nat.add_zero j ▸ h
  subst hj
  rfl





omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp'_snoc {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j m : ℕ) (h : j + (l + 1) = m) (x : Mf j),
      (chainComp' (I := I) (Mf := Mf) Ψ (l + 1) j m h : Mf j → Mf m) x
        = (h ▸ ((Ψ (j + l) : Mf (j + l) → Mf (j + l + 1))
            ((chainComp' (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
              Mf j → Mf (j + l)) x)) : Mf m) := by
  intro l
  induction l with
  | zero =>
      intro j m h x
      subst h
      rw [chainComp'_apply_succ, chainComp'_apply_zero, chainComp'_apply_zero]
      rfl
  | succ l ih =>
      intro j m h x
      subst h
      rw [chainComp'_apply_succ,
        ih (j + 1) (j + (l + 1 + 1)) (by omega) ((Ψ j : Mf j → Mf (j + 1)) x)]
      conv_rhs => rw [chainComp'_apply_succ]




      have hcast : ∀ (a : ℕ) (ha : (j + 1) + l = a),
          (Ψ a : Mf a → Mf (a + 1))
              ((chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) a ha : Mf (j + 1) → Mf a)
                ((Ψ j : Mf j → Mf (j + 1)) x))
            = ha ▸ ((Ψ ((j + 1) + l) : Mf ((j + 1) + l) → Mf ((j + 1) + l + 1))
                ((chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) ((j + 1) + l) rfl :
                    Mf (j + 1) → Mf ((j + 1) + l))
                  ((Ψ j : Mf j → Mf (j + 1)) x))) := by
        intro a ha; subst ha; rfl
      rw [hcast (j + (l + 1)) (by omega)]


      simp only [eqRec_eq_cast]


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_eq_right {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞))
    (l j : ℕ) :
    (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l))
      = (chainComp' (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
          Mf j → Mf (j + l)) := by
  funext x
  induction l generalizing j with
  | zero =>
      rw [chainComp'_apply_zero]
      rfl
  | succ l ih =>
      rw [chainComp_apply_succ, ih j, chainComp'_snoc]





omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem chainComp_coe_head {Mf : ℕ → Type u} [∀ j, TopologicalSpace (Mf j)]
    [∀ j, ChartedSpace H (Mf j)] [∀ j, IsManifold I ∞ (Mf j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (Mf j) (Mf (j + 1)) (∞ : WithTop ℕ∞)) :
    ∀ (l j : ℕ) (x : Mf j),
      (chainComp (I := I) (Mf := Mf) Ψ j (l + 1) : Mf j → Mf (j + (l + 1))) x
        = (chainComp' (I := I) (Mf := Mf) Ψ l (j + 1) (j + (l + 1)) (by omega) :
            Mf (j + 1) → Mf (j + (l + 1)))
            ((Ψ j : Mf j → Mf (j + 1)) x) := by
  have lemmaA : ∀ (l j : ℕ) (x : Mf j),
      (chainComp (I := I) (Mf := Mf) Ψ j l : Mf j → Mf (j + l)) x
        = (chainComp' (I := I) (Mf := Mf) Ψ l j (j + l) rfl :
            Mf j → Mf (j + l)) x := by
    intro l
    induction l with
    | zero =>
        intro j x
        rw [chainComp'_apply_zero]
        rfl
    | succ l ih =>
        intro j x
        rw [chainComp_apply_succ, ih j x, chainComp'_snoc]
  intro l j x
  rw [lemmaA (l + 1) j x]
  rw [chainComp'_apply_succ]

end Chain

section MemberBridge



theorem ball_subset_eball_ofReal {α : Type*} [PseudoMetricSpace α]
    (x : α) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r ⊆ Metric.eball x (ENNReal.ofReal r) := by
  intro y hy
  rw [Metric.mem_ball] at hy
  rw [Metric.mem_eball, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hy



theorem closedEBall_ofReal_subset_ball {α : Type*} [PseudoMetricSpace α]
    (x : α) {r R : ℝ} (hr : 0 ≤ r) (hR : r < R) :
    Metric.closedEBall x (ENNReal.ofReal r) ⊆ Metric.ball x R := by
  intro y hy
  rw [Metric.mem_closedEBall] at hy
  rw [edist_dist] at hy
  rw [Metric.mem_ball]
  have hdist_le : dist y x ≤ r := by
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 hy
  exact lt_of_le_of_lt hdist_le hR

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem data_image_metric_ball
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [PseudoMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
    [SigmaCompactSpace N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [PseudoMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace I y)]
    [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {O : M} {r r₂ R ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hhnorm : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y w w)))
    (hr : 0 < r) (hrr₂ : r ≤ r₂) (hε0 : 0 ≤ ε)
    (hR : Real.sqrt (1 + ε) * r < R)
    (hdata : PreApproxIsoDataOn (I := I)
      (Metric.closedEBall O (ENNReal.ofReal r₂)) ε p (Φ : M → N) g h)
    (hsub : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ Φ.source) :
    (Φ : M → N) '' Metric.ball O r ⊆ Metric.ball ((Φ : M → N) O) R := by
  intro y hy
  have hyE : y ∈ (Φ : M → N) '' Metric.eball O (ENNReal.ofReal r) :=
    Set.image_mono (ball_subset_eball_ofReal O hr) hy
  have hyClosed :
      y ∈ Metric.closedEBall ((Φ : M → N) O)
        (ENNReal.ofReal (Real.sqrt (1 + ε) * r)) :=
    data_image_ball (I := I) Φ hgnorm hhnorm hr hrr₂ hε0 hdata hsub hyE
  exact closedEBall_ofReal_subset_ball ((Φ : M → N) O)
    (mul_nonneg (Real.sqrt_nonneg _) hr.le) hR hyClosed

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem data_image_metric_ball_of_superset
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [PseudoMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
    [SigmaCompactSpace N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [PseudoMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace I y)]
    [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {O : M} {r r₂ R ε : ℝ} {p : ℕ}
    {K : Set M} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hhnorm : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y w w)))
    (hr : 0 < r) (hrr₂ : r ≤ r₂) (hε0 : 0 ≤ ε)
    (hR : Real.sqrt (1 + ε) * r < R)
    (hK : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ K)
    (hdata : PreApproxIsoDataOn (I := I) K ε p (Φ : M → N) g h)
    (hsub : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ Φ.source) :
    (Φ : M → N) '' Metric.ball O r ⊆ Metric.ball ((Φ : M → N) O) R :=
  data_image_metric_ball (I := I) Φ hgnorm hhnorm hr hrr₂ hε0 hR
    (hdata.mono hK le_rfl hdata.eps_lt_one) hsub





omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem member_isRiemannian (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
    letI : MetricSpace Y.M := P.ms
    IsRiemannianManifold I Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
  letI : MetricSpace Y.M := P.ms
  refine ⟨fun x y => ?_⟩
  have hreal := P.realizes x y
  rw [edist_dist, ← hreal]
  rfl

end MemberBridge

section DataTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [MetricSpace M] [Nonempty M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
  [SigmaCompactSpace N]


noncomputable def PreApproxIsoDataOn.congr_eq {K : Set M} {ε : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoDataOn (I := I) K ε p F g h) (hEq : F' = F) :
    PreApproxIsoDataOn (I := I) K ε p F' g h :=
  D.congr (fun _ _ => Filter.EventuallyEq.of_eq hEq)


noncomputable def PreApproxIsoSep.congr {K : Set M} {c0 cov : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoSep (I := I) K c0 cov p F g h)
    (hev : ∀ x ∈ K, F' =ᶠ[nhds x] F) :
    PreApproxIsoSep (I := I) K c0 cov p F' g h where
  c0_nonneg := D.c0_nonneg
  cov_nonneg := D.cov_nonneg
  smoothOn := D.smoothOn.congr (fun x hx => (hev x hx).self_of_nhds)
  pullback := D.pullback
  pullback_apply := by
    intro x hx v
    rw [(hev x hx).self_of_nhds, (hev x hx).mfderiv_eq]
    exact D.pullback_apply x hx v
  c0_small := D.c0_small
  cov_small := D.cov_small


noncomputable def PreApproxIsoSep.congr_eq {K : Set M} {c0 cov : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoSep (I := I) K c0 cov p F g h) (hEq : F' = F) :
    PreApproxIsoSep (I := I) K c0 cov p F' g h :=
  D.congr (fun _ _ => Filter.EventuallyEq.of_eq hEq)


noncomputable def PreApproxIsoSep.congr_set {K K' : Set M} {c0 cov : ℝ} {p : ℕ}
    {F : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoSep (I := I) K c0 cov p F g h) (hK : K' = K) :
    PreApproxIsoSep (I := I) K' c0 cov p F g h := by
  subst hK
  exact D


noncomputable def BookApproxIsoPartialData.ofParts {K : Set M} {ε : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hsrc : K ⊆ Φ.source)
    (forward : PreApproxIsoDataOn (I := I) K ε p (Φ : M → N) g h)
    (reverse : PreApproxIsoDataOn (I := I) ((Φ : M → N) '' K) ε p (Φ.symm : N → M) h g) :
    BookApproxIsoPartialData (I := I) K ε p Φ g h where
  source_sub := hsrc
  forward := forward
  reverse := reverse


noncomputable def BookApproxIsoSep.ofParts {K : Set M} {c0 cov : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hsrc : K ⊆ Φ.source)
    (forward : PreApproxIsoSep (I := I) K c0 cov p (Φ : M → N) g h)
    (reverse : PreApproxIsoSep (I := I) ((Φ : M → N) '' K) c0 cov p (Φ.symm : N → M) h g) :
    BookApproxIsoSep (I := I) K c0 cov p Φ g h where
  source_sub := hsrc
  forward := forward
  reverse := reverse


noncomputable def BookApproxIsoSep.congr_set {K K' : Set M} {c0 cov : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoSep (I := I) K c0 cov p Φ g h) (hK : K' = K) :
    BookApproxIsoSep (I := I) K' c0 cov p Φ g h := by
  subst hK
  exact D


theorem image_eq_of_fun_eq {α β : Type*} {s : Set α} {f g : α → β} (h : f = g) :
    f '' s = g '' s := by
  subst h
  rfl



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [MetricSpace M] [Nonempty M] [T2Space N] [SigmaCompactSpace N] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [IsManifold I ∞ N] in
theorem symm_eventuallyEq_on_image
    {Φ Ψ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {U : TopologicalSpace.Opens M}
    (hUΦ : (U : Set M) ⊆ Φ.source) (hUΨ : (U : Set M) ⊆ Ψ.source)
    (hEq : (Ψ : M → N) = (Φ : M → N)) :
    ∀ y ∈ (Φ : M → N) '' (U : Set M),
      (Ψ.symm : N → M) =ᶠ[nhds y] (Φ.symm : N → M) := by
  intro y hy
  refine Filter.eventuallyEq_of_mem ((image_opens_isOpen (I := I) Φ hUΦ).mem_nhds hy) ?_
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hΨx : (Ψ : M → N) x = (Φ : M → N) x := by rw [hEq]
  calc
    (Ψ.symm : N → M) ((Φ : M → N) x)
        = (Ψ.symm : N → M) ((Ψ : M → N) x) := by rw [hΨx]
    _ = x := Ψ.left_inv' (hUΨ hx)
    _ = (Φ.symm : N → M) ((Φ : M → N) x) := (Φ.left_inv' (hUΦ hx)).symm

end DataTransport

section ReflData

set_option backward.isDefEq.respectTransparency false in



omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem tensor02CovDeriv_metric_zero {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [T2Space M'] [SigmaCompactSpace M']
    [IsManifold I 1 M'] [IsManifold I 2 M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (g : SmoothRiemannianMetric I M') (a : ℕ) :
    tensor02CovDeriv (I := I) (Tensor0SBundle.metricTensorField (I := I) g) g (a + 1) = 0 := by
  rw [tensor02_eq_covDOF, covDerivOfField_eq_iterCov, iterCov_metric_zero,
    MultilinearSection.domDomCongr_zero]






omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem reflBookData {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [T2Space M'] [SigmaCompactSpace M']
    [IsManifold I 1 M'] [IsManifold I 2 M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (K : Set M') (g : SmoothRiemannianMetric I M') (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (p : ℕ) :
    Nonempty (BookApproxIsoPartialData (I := I) K ε p
      (PartialDiffeomorph.refl (I := I) M') g g) := by
  classical

  have hcoe : ∀ x : M', (PartialDiffeomorph.refl (I := I) M' : M' → M') x = x := fun _ => rfl
  have hmfd : ∀ x : M', mfderiv I I (PartialDiffeomorph.refl (I := I) M' : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id
  have hsymmcoe : ∀ x : M', ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x = x :=
    fun _ => rfl
  have hsymmmfd : ∀ x : M', mfderiv I I ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id


  have hnz : ∀ (s : ℕ) (y : M'),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y)) = 0 := by
    intro s y
    have hz : Tensor0SBundle.inner0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y) 0 = 0 := by
      show (Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat 0 0 = 0
      rw [(Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat.map_zero]
      exact LinearMap.zero_apply _
    rw [Tensor0SBundle.normSq0S_eq_inner, hz, Real.sqrt_zero]
  have mkPre : ∀ (K' : Set M') (Φcoe : M' → M')
      (hΦ : ∀ x, Φcoe x = x) (hΦd : ∀ x, mfderiv I I Φcoe x
        = ContinuousLinearMap.id ℝ (TangentSpace I x))
      (hsm : ContMDiffOn I I (∞ : WithTop ℕ∞) Φcoe K'),
      PreApproxIsoDataOn (I := I) K' ε p Φcoe g g := by
    intro K' Φcoe hΦ hΦd hsm
    refine
      { eps_pos := hε
        eps_lt_one := hε1
        smoothOn := hsm
        pullback := Tensor0SBundle.metricTensorField (I := I) g
        pullback_apply := ?_
        c0_small := ?_
        cov_deriv_small := ?_ }
    · intro x _ v
      rw [Tensor0SBundle.metricTensorField_apply, hΦ x, hΦd x]
      simp only [ContinuousLinearMap.id_apply]
    · intro x _
      show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
        (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)) ≤ ε
      have hs : (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)
          = (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') 2 x) :=
        sub_self _
      rw [hs, hnz]
      exact le_of_lt hε
    · intro a ha1 _ x _
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (tensor02CovDeriv (I := I) (Tensor0SBundle.metricTensorField (I := I) g) g (a' + 1) x))
        ≤ ε
      rw [tensor02CovDeriv_metric_zero]
      show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M')
          (a' + 1 + 2) x)) ≤ ε
      rw [hnz]
      exact le_of_lt hε
  refine ⟨{
    source_sub := fun x _ => Set.mem_univ x
    forward := mkPre K (PartialDiffeomorph.refl (I := I) M' : M' → M') hcoe hmfd
      (contMDiffOn_id (I := I))
    reverse := mkPre ((PartialDiffeomorph.refl (I := I) M' : M' → M') '' K)
        ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') hsymmcoe hsymmmfd
      (contMDiffOn_id (I := I)) }⟩





omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem reflSepData {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [T2Space M'] [SigmaCompactSpace M']
    [IsManifold I 1 M'] [IsManifold I 2 M'] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
    (K : Set M') (g : SmoothRiemannianMetric I M') (p : ℕ) :
    Nonempty (BookApproxIsoSep (I := I) K 0 0 p
      (PartialDiffeomorph.refl (I := I) M') g g) := by
  classical
  have hcoe : ∀ x : M', (PartialDiffeomorph.refl (I := I) M' : M' → M') x = x := fun _ => rfl
  have hmfd : ∀ x : M', mfderiv I I (PartialDiffeomorph.refl (I := I) M' : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id
  have hsymmcoe : ∀ x : M', ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x = x :=
    fun _ => rfl
  have hsymmmfd : ∀ x : M', mfderiv I I ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') x
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := fun x => mfderiv_id
  have hnz : ∀ (s : ℕ) (y : M'),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y)) = 0 := by
    intro s y
    have hz : Tensor0SBundle.inner0S (I := I) g y s
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') s y) 0 = 0 := by
      show (Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat 0 0 = 0
      rw [(Tensor0SBundle.tensor0SMetricData (I := I) g y s).flat.map_zero]
      exact LinearMap.zero_apply _
    rw [Tensor0SBundle.normSq0S_eq_inner, hz, Real.sqrt_zero]
  have mkPre : ∀ (K' : Set M') (Φcoe : M' → M')
      (hΦ : ∀ x, Φcoe x = x) (hΦd : ∀ x, mfderiv I I Φcoe x
        = ContinuousLinearMap.id ℝ (TangentSpace I x))
      (hsm : ContMDiffOn I I (∞ : WithTop ℕ∞) Φcoe K'),
      PreApproxIsoSep (I := I) K' 0 0 p Φcoe g g := by
    intro K' Φcoe hΦ hΦd hsm
    refine
      { c0_nonneg := le_rfl
        cov_nonneg := le_rfl
        smoothOn := hsm
        pullback := Tensor0SBundle.metricTensorField (I := I) g
        pullback_apply := ?_
        c0_small := ?_
        cov_small := ?_ }
    · intro x _ v
      rw [Tensor0SBundle.metricTensorField_apply, hΦ x, hΦd x]
      simp only [ContinuousLinearMap.id_apply]
    · intro x _
      show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
        (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)) ≤ 0
      have hs : (Tensor0SBundle.metricTensorField (I := I) g x
          - Tensor0SBundle.metricTensorField (I := I) g x)
          = (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M') 2 x) :=
        sub_self _
      rw [hs, hnz]
    · intro a ha1 _ x _
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (tensor02CovDeriv (I := I) (Tensor0SBundle.metricTensorField (I := I) g) g (a' + 1) x))
        ≤ 0
      rw [tensor02CovDeriv_metric_zero]
      show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (a' + 1 + 2)
        (0 : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M')
          (a' + 1 + 2) x)) ≤ 0
      rw [hnz]
  refine ⟨{
    source_sub := fun x _ => Set.mem_univ x
    forward := mkPre K (PartialDiffeomorph.refl (I := I) M' : M' → M') hcoe hmfd
      (contMDiffOn_id (I := I))
    reverse := mkPre ((PartialDiffeomorph.refl (I := I) M' : M' → M') '' K)
      ((PartialDiffeomorph.refl (I := I) M').symm : M' → M') hsymmcoe hsymmmfd
      (contMDiffOn_id (I := I)) }⟩

end ReflData

section Endpoint






theorem geomTailBudget : ∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
    ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + i) ≤ ε := by
  intro ε hε
  obtain ⟨j₀, hj₀⟩ :=
    exists_pow_lt_of_lt_one (show 0 < ε / 2 by linarith) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨j₀, fun j hj l => ?_⟩
  have hpow : (1 / 2 : ℝ) ^ j ≤ ε / 2 :=
    le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj) hj₀)
  calc ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + i)
      = (1 / 2 : ℝ) ^ j * ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
    _ ≤ (1 / 2 : ℝ) ^ j * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_le_hasSum (Finset.range (l + 1)) (fun i _ => by positivity) hasSum_geometric_two
    _ ≤ (ε / 2) * 2 := by exact mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = ε := by ring



theorem two_pow_lt_openRad (j l : ℕ) :
    (2 : ℝ) ^ j < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  calc
    (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := by ring
    _ < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) :=
      mul_lt_mul_of_pos_left (by linarith) hpow


theorem openRad_pos (j l : ℕ) :
    0 < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  nlinarith [mul_pos hpow (by linarith : (0 : ℝ) < 1 + (1 / 2 : ℝ) ^ (l + 1))]


theorem openRad_succ_lt (j l : ℕ) :
    (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2))
      < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith


def midRad (j l : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (1 + (((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2))


theorem openRad_next_lt_mid (j l : ℕ) :
    (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)) < midRad j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [midRad]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith


theorem midRad_lt_openRad (j l : ℕ) :
    midRad j l < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [midRad]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith


theorem midRad_le_step (j l : ℕ) :
    midRad j l ≤ (2 : ℝ) ^ (j + 1) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc
    midRad j l = (2 : ℝ) ^ j *
        (1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2) := by
      rfl
    _ ≤ (2 : ℝ) ^ j * (1 + (1 + 1) / 2) := by
      have hinner :
          1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2
            ≤ 1 + (1 + 1) / 2 := by
        linarith
      exact mul_le_mul_of_nonneg_left hinner hpow.le
    _ = (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ']
      ring


theorem midRad_le_mid0 (j l : ℕ) :
    midRad j l ≤ midRad j 0 := by
  have hpow : 0 ≤ (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  dsimp [midRad]
  refine mul_le_mul_of_nonneg_left ?_ hpow
  nlinarith


theorem half_pow_succ_le_half (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
  have hpow : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simpa using hpow


omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem properMetric_isOpen_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @IsOpen Y.M Y.topology
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  have hb :
      @IsOpen Y.M P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace Y.M := P.ms
         Metric.ball x r) := by
    letI : MetricSpace Y.M := P.ms
    exact Metric.isOpen_ball
  rw [ProperMetricOn.top_eq Y P] at hb
  exact hb


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem properMetric_mem_ball_self
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    x ∈
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  letI : MetricSpace Y.M := P.ms
  exact Metric.mem_ball_self hr


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem properMetric_ball_nonempty
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) :=
  ⟨⟨x, properMetric_mem_ball_self (I := I) Y P x hr⟩⟩


theorem nonempty_opens_mk {M : Type u} {t : TopologicalSpace M}
    {s : Set M} (hs : @IsOpen M t s) (hne : Nonempty s) :
    Nonempty (⟨s, hs⟩ : @TopologicalSpace.Opens M t) :=
  hne


def properMetricOpenBall
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @TopologicalSpace.Opens Y.M Y.topology :=
  letI : TopologicalSpace Y.M := Y.topology
  ⟨(letI : MetricSpace Y.M := P.ms
    Metric.ball x r),
    properMetric_isOpen_ball (I := I) Y P x r⟩


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem properMetricOpenBall_nonempty
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty (properMetricOpenBall (I := I) Y P x r) := by
  letI : TopologicalSpace Y.M := Y.topology
  dsimp [properMetricOpenBall]
  exact nonempty_opens_mk (properMetric_isOpen_ball (I := I) Y P x r)
    (properMetric_ball_nonempty (I := I) Y P x hr)


theorem imageRad_lt_step {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * ((2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)))
      < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 3 / 2 := by
    have hlt : 1 + a < (3 / 2 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((3 / 2 : ℝ) ^ 2) = 3 / 2 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail_le : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpow_pos : 0 < (2 : ℝ) ^ j := by positivity
  have hR_pos : 0 < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)) := by positivity
  have hR_le :
      (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)) ≤ (5 / 4 : ℝ) * (2 : ℝ) ^ j := by
    nlinarith
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * ((2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2)))
        < (3 / 2 : ℝ) * ((2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 2))) :=
          mul_lt_mul_of_pos_right hsqrt_lt hR_pos
    _ ≤ (3 / 2 : ℝ) * ((5 / 4 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hR_le (by norm_num)
    _ = (15 / 8 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono


theorem imageMid_lt_step {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRad j l < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 5 / 4 := by
    have hlt : 1 + a < (5 / 4 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((5 / 4 : ℝ) ^ 2) = 5 / 4 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmid_pos : 0 < midRad j l := by
    dsimp [midRad]
    positivity
  have hmid_le : midRad j l ≤ (11 / 8 : ℝ) * (2 : ℝ) ^ j := by
    dsimp [midRad]
    nlinarith [show 0 ≤ (2 : ℝ) ^ j by positivity]
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * midRad j l
        < (5 / 4 : ℝ) * midRad j l := mul_lt_mul_of_pos_right hsqrt_lt hmid_pos
    _ ≤ (5 / 4 : ℝ) * ((11 / 8 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hmid_le (by norm_num)
    _ = (55 / 32 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith [show 0 < (2 : ℝ) ^ j by positivity]
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono



theorem imageMid_lt_openRad {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRad j l
      < (2 : ℝ) ^ (j + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg _
  have hle_mid0 : Real.sqrt (1 + a) * midRad j l ≤ Real.sqrt (1 + a) * midRad j 0 :=
    mul_le_mul_of_nonneg_left (midRad_le_mid0 j l) hsqrt_nonneg
  have hlt_step : Real.sqrt (1 + a) * midRad j 0 < (2 : ℝ) ^ (j + 1) := by
    simpa using imageMid_lt_step j 0 ha0 ha2
  exact lt_trans (lt_of_le_of_lt hle_mid0 hlt_step) (two_pow_lt_openRad (j + 1) l)


def nextTol (a δ B : ℝ) : ℝ :=
  max (a / (1 - a) + δ * B) (δ / (1 - δ) + a * B)

theorem nextTol_left (a δ B : ℝ) :
    a / (1 - a) + δ * B ≤ nextTol a δ B :=
  le_max_left _ _

theorem nextTol_right (a δ B : ℝ) :
    δ / (1 - δ) + a * B ≤ nextTol a δ B :=
  le_max_right _ _

theorem nextTol_pos {a δ B : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hδ0 : 0 < δ)
    (hB0 : 0 ≤ B) :
    0 < nextTol a δ B := by
  have hden : 0 < 1 - a := by linarith
  have hfrac : 0 < a / (1 - a) := div_pos ha0 hden
  have hδB : 0 ≤ δ * B := mul_nonneg hδ0.le hB0
  exact lt_of_lt_of_le (by linarith) (nextTol_left a δ B)



def sepFeed (c0 cov : ℝ) : ℝ :=
  max (c0 / (1 - c0)) cov


def sepNextC0 (c0 cov δ : ℝ) : ℝ :=
  c0 + δ * (1 + sepFeed c0 cov)


def sepNextCov (c0 cov δ B : ℝ) : ℝ :=
  sepFeed c0 cov + δ * B

theorem sepFeed_c0 (c0 cov : ℝ) :
    c0 / (1 - c0) ≤ sepFeed c0 cov :=
  le_max_left _ _

theorem sepFeed_cov (c0 cov : ℝ) :
    cov ≤ sepFeed c0 cov :=
  le_max_right _ _

theorem sepFeed_nonneg {c0 cov : ℝ} (hc0 : 0 ≤ c0) (hc1 : c0 < 1) :
    0 ≤ sepFeed c0 cov := by
  have hden : 0 ≤ 1 - c0 := by linarith
  exact le_trans (div_nonneg hc0 hden) (sepFeed_c0 c0 cov)

theorem sepFeed_le_one {c0 cov : ℝ} (hc0_half : c0 ≤ 1 / 2) (hcov : cov ≤ 1) :
    sepFeed c0 cov ≤ 1 := by
  have hden : 0 < 1 - c0 := by linarith
  have hc0frac : c0 / (1 - c0) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  exact max_le hc0frac hcov

theorem sepNextC0_bound (c0 cov δ : ℝ) :
    c0 + δ * (1 + sepFeed c0 cov) ≤ sepNextC0 c0 cov δ :=
  le_rfl

theorem sepNextCov_bound (c0 cov δ B : ℝ) :
    sepFeed c0 cov + δ * B ≤ sepNextCov c0 cov δ B :=
  le_rfl



def sepTail (s l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range l, (1 / 2 : ℝ) ^ (s + i + 1)



def sepBeta (B : ℝ) : ℝ :=
  max B 4

theorem sepTail_succ (s l : ℕ) :
    sepTail s (l + 1) = sepTail s l + (1 / 2 : ℝ) ^ (s + l + 1) := by
  simp [sepTail, Finset.sum_range_succ, add_assoc]

theorem sepTail_succ' (s l : ℕ) :
    sepTail s (l + 1) = (1 / 2 : ℝ) ^ (s + 1) + sepTail (s + 1) l := by
  simp [sepTail, Finset.sum_range_succ', add_assoc, add_comm, add_left_comm]

theorem sepTail_nonneg (s l : ℕ) :
    0 ≤ sepTail s l := by
  dsimp [sepTail]
  positivity

theorem sepBeta_pos (B : ℝ) :
    0 < sepBeta B := by
  have h4 : (4 : ℝ) ≤ sepBeta B := by
    simp [sepBeta]
  linarith

theorem sepBeta_four (B : ℝ) :
    (4 : ℝ) ≤ sepBeta B := by
  simp [sepBeta]

theorem le_sepBeta (B : ℝ) :
    B ≤ sepBeta B := by
  simp [sepBeta]

theorem sepFeed_le_beta {B c0 cov T : ℝ} (hT0 : 0 ≤ T) (hc0 : 0 ≤ c0)
    (hc0T : c0 ≤ 2 * T) (hcovT : cov ≤ sepBeta B * T)
    (hTsmall : T ≤ 1 / sepBeta B) :
    sepFeed c0 cov ≤ sepBeta B * T := by
  have hβpos : 0 < sepBeta B := sepBeta_pos B
  have hβ4 : (4 : ℝ) ≤ sepBeta B := sepBeta_four B
  have hTβ : T * sepBeta B ≤ 1 := by
    rwa [le_div_iff₀ hβpos] at hTsmall
  have hc0half : c0 ≤ 1 / 2 := by
    nlinarith
  have hden : 0 < 1 - c0 := by
    nlinarith
  have hfrac_two : c0 / (1 - c0) ≤ 2 * c0 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hc0 (by nlinarith : 0 ≤ 1 - 2 * c0)]
  have hfrac : c0 / (1 - c0) ≤ sepBeta B * T := by
    calc
      c0 / (1 - c0) ≤ 2 * c0 := hfrac_two
      _ ≤ 4 * T := by nlinarith
      _ ≤ sepBeta B * T := by nlinarith
  exact max_le hfrac hcovT

theorem sepNextC0_le {B c0 cov T δ : ℝ} (hT0 : 0 ≤ T) (hδ0 : 0 ≤ δ)
    (hc0 : 0 ≤ c0) (hc0T : c0 ≤ 2 * T) (hcovT : cov ≤ sepBeta B * T)
    (hTsmall : T ≤ 1 / sepBeta B) :
    sepNextC0 c0 cov δ ≤ 2 * (T + δ) := by
  have hβpos : 0 < sepBeta B := sepBeta_pos B
  have hfeed : sepFeed c0 cov ≤ sepBeta B * T :=
    sepFeed_le_beta hT0 hc0 hc0T hcovT hTsmall
  have hTβ : T * sepBeta B ≤ 1 := by
    rwa [le_div_iff₀ hβpos] at hTsmall
  dsimp [sepNextC0]
  nlinarith

theorem sepNextCov_le {B c0 cov T δ : ℝ} (hT0 : 0 ≤ T) (hδ0 : 0 ≤ δ)
    (hc0 : 0 ≤ c0) (hc0T : c0 ≤ 2 * T) (hcovT : cov ≤ sepBeta B * T)
    (hTsmall : T ≤ 1 / sepBeta B) :
    sepNextCov c0 cov δ B ≤ sepBeta B * (T + δ) := by
  have hfeed : sepFeed c0 cov ≤ sepBeta B * T :=
    sepFeed_le_beta hT0 hc0 hc0T hcovT hTsmall
  have hBβ : B ≤ sepBeta B := le_sepBeta B
  dsimp [sepNextCov]
  nlinarith

theorem sepTailBudget (B ε : ℝ) (hε : 0 < ε) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
      sepBeta B * sepTail j l ≤ ε := by
  have hβpos : 0 < sepBeta B := sepBeta_pos B
  obtain ⟨j₀, hj₀⟩ := geomTailBudget (ε / sepBeta B) (div_pos hε hβpos)
  refine ⟨j₀, fun j hj l => ?_⟩
  have htail :
      sepTail j l ≤ ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i) := by
    dsimp [sepTail]
    calc
      ∑ i ∈ Finset.range l, (1 / 2 : ℝ) ^ (j + i + 1)
          = ∑ i ∈ Finset.range l, (1 / 2 : ℝ) ^ (j + 1 + i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            congr 1
            omega
      _ ≤ ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i) := by
            have hsub : Finset.range l ⊆ Finset.range (l + 1) := by
              intro x hx
              exact Finset.mem_range.2
                (Nat.lt_trans (Finset.mem_range.1 hx) (Nat.lt_succ_self l))
            exact Finset.sum_le_sum_of_subset_of_nonneg
              hsub
              (by intro x _ _; positivity)
  have hgeom :
      ∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i) ≤ ε / sepBeta B :=
    hj₀ (j + 1) (le_trans hj (Nat.le_succ j)) l
  calc
    sepBeta B * sepTail j l
        ≤ sepBeta B * (∑ i ∈ Finset.range (l + 1), (1 / 2 : ℝ) ^ (j + 1 + i)) :=
          mul_le_mul_of_nonneg_left htail hβpos.le
    _ ≤ sepBeta B * (ε / sepBeta B) :=
          mul_le_mul_of_nonneg_left hgeom hβpos.le
    _ = ε := by field_simp [ne_of_gt hβpos]





theorem exists_strictMono_ge (T : ℕ → ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, T j ≤ σ j := by
  classical

  refine ⟨fun j => j + Finset.sup (Finset.range (j + 1)) T, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    show n + Finset.sup (Finset.range (n + 1)) T
        < (n + 1) + Finset.sup (Finset.range (n + 1 + 1)) T
    have hsub : Finset.range (n + 1) ⊆ Finset.range (n + 1 + 1) :=
      Finset.range_mono (Nat.le_succ (n + 1))
    have hmono : Finset.sup (Finset.range (n + 1)) T
        ≤ Finset.sup (Finset.range (n + 1 + 1)) T :=
      Finset.sup_mono hsub
    calc n + Finset.sup (Finset.range (n + 1)) T
        ≤ n + Finset.sup (Finset.range (n + 1 + 1)) T := Nat.add_le_add_left hmono n
      _ < (n + 1) + Finset.sup (Finset.range (n + 1 + 1)) T := by omega
  · intro j
    show T j ≤ j + Finset.sup (Finset.range (j + 1)) T
    exact le_trans (Finset.le_sup (Finset.self_mem_range_succ j)) (Nat.le_add_left _ j)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

set_option maxHeartbeats 1000000 in








theorem directed_of_b1 (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
       letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
       letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
       letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
       letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
       letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
       ∃ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M
          (∞ : WithTop ℕ∞),
        (∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M) ((X.obj (σ j)).basepoint)
            = (X.obj (σ (j + 1))).basepoint) ∧
        ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ l : ℕ,
          Nonempty (BookApproxIsoPartialData (I := I)
            (Metric.closedBall ((X.obj (σ j)).basepoint) ((2 : ℝ) ^ j)) ε p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ j l)
            (X.obj (σ j)).metric (X.obj (σ (j + l))).metric)) := by
  classical

  have hrpos : ∀ j : ℕ, (0 : ℝ) < (2 : ℝ) ^ (j + 1) := fun j => by positivity
  have hepos : ∀ j : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := fun j => by positivity
  have helt : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) < 1 :=
    fun j => pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

  set T : ℕ → ℕ := fun j =>
    (stepB1_of_raw P B ((2 : ℝ) ^ (j + 1)) (hrpos j) ((1 / 2 : ℝ) ^ (j + 1)) (hepos j)
      (helt j) j).choose with hT
  obtain ⟨σ, hσmono, hσge⟩ := exists_strictMono_ge T
  refine ⟨σ, hσmono, ?_⟩

  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  letI : ∀ j, IsManifold I 1 (X.obj (σ j)).M := fun j =>
    IsManifold.of_le (I := I) (M := (X.obj (σ j)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : ∀ j, IsManifold I 2 (X.obj (σ j)).M := fun j =>
    IsManifold.of_le (I := I) (M := (X.obj (σ j)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M; infer_instance

  letI hRB : ∀ j, Bundle.RiemannianBundle (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  haveI hRiem : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j =>
    member_isRiemannian (X.obj (σ j)) (P (σ j))
  haveI hProper : ∀ j, ProperSpace (X.obj (σ j)).M := fun j => (P (σ j)).proper

  have hstep : ∀ j : ℕ, T j ≤ σ j ∧ T j ≤ σ (j + 1) := fun j =>
    ⟨hσge j, le_trans (hσge j) (le_of_lt (hσmono (Nat.lt_succ_self j)))⟩


  have hΨex : ∀ j : ℕ,
      ∃ Φ : PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞),
        Metric.closedBall ((X.obj (σ j)).basepoint) ((2 : ℝ) ^ (j + 1)) ⊆ Φ.source ∧
        (Φ : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M) ((X.obj (σ j)).basepoint)
          = (X.obj (σ (j + 1))).basepoint ∧
        Nonempty (BookApproxIsoPartialData (I := I)
          (Metric.closedBall ((X.obj (σ j)).basepoint) ((2 : ℝ) ^ (j + 1)))
          ((1 / 2 : ℝ) ^ (j + 1)) j Φ (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric) :=
    fun j => (stepB1_of_raw P B ((2 : ℝ) ^ (j + 1)) (hrpos j) ((1 / 2 : ℝ) ^ (j + 1)) (hepos j)
      (helt j) j).choose_spec (σ j) (σ (j + 1)) (hstep j).1 (hstep j).2
  choose Ψ hΨsrc hΨbase hΨdata using hΨex
  refine ⟨Ψ, hΨbase, ?_⟩
  intro ε hε hε1 p
  let C : ℝ := (comp_cov_le_unif.{u, uE, uH} (I := I) p).choose
  have hC0 : 0 ≤ C := (comp_cov_le_unif.{u, uE, uH} (I := I) p).choose_spec.1
  let B : ℝ := max C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right C 2)

  obtain ⟨jε, hjε⟩ := sepTailBudget B ε hε
  obtain ⟨jβ, hjβ⟩ := sepTailBudget B (1 / 2) (by norm_num)
  refine ⟨max (max jε jβ) p, fun j hj => ?_⟩
  have hjεj : jε ≤ j := le_trans (Nat.le_trans (Nat.le_max_left jε jβ)
    (Nat.le_max_left (max jε jβ) p)) hj
  have hjβj : jβ ≤ j := le_trans (Nat.le_trans (Nat.le_max_right jε jβ)
    (Nat.le_max_left (max jε jβ) p)) hj
  have hpj : p ≤ j := le_trans (Nat.le_max_right (max jε jβ) p) hj
  suffices hacc : ∀ (l s : ℕ), j ≤ s → ∃ c0 cov : ℝ,
      0 ≤ c0 ∧ 0 ≤ cov ∧ c0 ≤ ε ∧ cov ≤ ε ∧ c0 ≤ 1 / 2 ∧ cov ≤ 1 / 2 ∧
      c0 ≤ 2 * sepTail s l ∧ cov ≤ sepBeta B * sepTail s l ∧
      Nonempty (BookApproxIsoSep (I := I)
        (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 1)))) c0 cov p
        (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
        (X.obj (σ s)).metric (X.obj (σ (s + l))).metric) ∧
      (∀ m (hm : s + l = m), Nonempty (BookApproxIsoSep (I := I)
        (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 1)))) c0 cov p
        (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l s m hm)
        (X.obj (σ s)).metric (X.obj (σ m)).metric)) by
    intro l
    obtain ⟨c0, cov, _hc0non, _hcovnon, hc0e, hcove, _, _, _, _, ⟨⟨D⟩, _⟩⟩ :=
      hacc l j le_rfl
    have hlt : (2 : ℝ) ^ j < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
      have : (0 : ℝ) < (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (l + 1) := by positivity
      nlinarith [this]
    exact ⟨(D.mono (Metric.closedBall_subset_ball hlt) le_rfl le_rfl).toBook hε hε1 hc0e hcove⟩
  intro l
  induction l with
  | zero =>
      intro s _hs
      refine ⟨0, 0, le_rfl, le_rfl, le_of_lt hε, le_of_lt hε, by norm_num, by norm_num,
        ?_, ?_, ?_⟩
      · simp [sepTail]
      · simp [sepTail]
      · exact ⟨
          reflSepData (I := I)
            (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (0 + 1))))
            (X.obj (σ s)).metric p,
          fun m hm => by
            cases hm
            exact reflSepData (I := I)
              (Metric.ball ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (0 + 1))))
              (X.obj (σ s)).metric p⟩
  | succ l ih =>
      intro s hs
      obtain ⟨c0F, covF, hc0F0, hcovF0, _hc0Fe, _hcovFe, hc0F2, hcovF2,
        hc0Fbudget, hcovFbudget, ⟨⟨DforAcc⟩, DrevAtSAll⟩⟩ := ih s hs
      obtain ⟨DrevAtS⟩ := DrevAtSAll (s + l) rfl
      obtain ⟨c0R, covR, hc0R0, hcovR0, _hc0Re, _hcovRe, hc0R2, hcovR2,
        hc0Rbudget, hcovRbudget, ⟨⟨DforTail⟩, DrevTailAll⟩⟩ :=
        ih (s + 1) (le_trans hs (Nat.le_succ s))
      have htail_index : s + 1 + l = s + (l + 1) := by omega
      obtain ⟨DrevTail⟩ := DrevTailAll (s + (l + 1)) htail_index
      let δF : ℝ := (1 / 2 : ℝ) ^ (s + l + 1)
      let δR : ℝ := (1 / 2 : ℝ) ^ (s + 1)
      have hδF0 : 0 ≤ δF := by positivity
      have hδR0 : 0 ≤ δR := by positivity
      have hδRpos : 0 < δR := by
        dsimp [δR]
        positivity
      let c0NF : ℝ := sepNextC0 c0F covF δF
      let covNF : ℝ := sepNextCov c0F covF δF B
      let c0NR : ℝ := sepNextC0 c0R covR δR
      let covNR : ℝ := sepNextCov c0R covR δR B
      let c0Next : ℝ := max c0NF c0NR
      let covNext : ℝ := max covNF covNR
      have hβpos : 0 < sepBeta B := sepBeta_pos B
      have hβ4 : (4 : ℝ) ≤ sepBeta B := sepBeta_four B
      have hTF0 : 0 ≤ sepTail s l := sepTail_nonneg s l
      have hTR0 : 0 ≤ sepTail (s + 1) l := sepTail_nonneg (s + 1) l
      have hTFsmall : sepTail s l ≤ 1 / sepBeta B := by
        have hsmall : sepBeta B * sepTail s l ≤ 1 :=
          le_trans (hjβ s (le_trans hjβj hs) l) (by norm_num)
        rw [le_div_iff₀ hβpos]
        nlinarith
      have hTRsmall : sepTail (s + 1) l ≤ 1 / sepBeta B := by
        have hs1 : j ≤ s + 1 := le_trans hs (Nat.le_succ s)
        have hsmall : sepBeta B * sepTail (s + 1) l ≤ 1 :=
          le_trans (hjβ (s + 1) (le_trans hjβj hs1) l) (by norm_num)
        rw [le_div_iff₀ hβpos]
        nlinarith
      have hc0NFbudget : c0NF ≤ 2 * sepTail s (l + 1) := by
        dsimp [c0NF]
        calc
          sepNextC0 c0F covF δF ≤ 2 * (sepTail s l + δF) :=
            sepNextC0_le hTF0 hδF0 hc0F0 hc0Fbudget hcovFbudget hTFsmall
          _ = 2 * sepTail s (l + 1) := by
            dsimp [δF]
            rw [sepTail_succ]
      have hcovNFbudget : covNF ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNF]
        calc
          sepNextCov c0F covF δF B ≤ sepBeta B * (sepTail s l + δF) :=
            sepNextCov_le hTF0 hδF0 hc0F0 hc0Fbudget hcovFbudget hTFsmall
          _ = sepBeta B * sepTail s (l + 1) := by
            dsimp [δF]
            rw [sepTail_succ]
      have hc0NRbudget : c0NR ≤ 2 * sepTail s (l + 1) := by
        dsimp [c0NR]
        calc
          sepNextC0 c0R covR δR ≤ 2 * (sepTail (s + 1) l + δR) :=
            sepNextC0_le hTR0 hδR0 hc0R0 hc0Rbudget hcovRbudget hTRsmall
          _ = 2 * sepTail s (l + 1) := by
            dsimp [δR]
            rw [sepTail_succ']
            ring
      have hcovNRbudget : covNR ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNR]
        calc
          sepNextCov c0R covR δR B ≤ sepBeta B * (sepTail (s + 1) l + δR) :=
            sepNextCov_le hTR0 hδR0 hc0R0 hc0Rbudget hcovRbudget hTRsmall
          _ = sepBeta B * sepTail s (l + 1) := by
            dsimp [δR]
            rw [sepTail_succ']
            ring
      have hc0NextBudget : c0Next ≤ 2 * sepTail s (l + 1) := by
        dsimp [c0Next]
        exact max_le hc0NFbudget hc0NRbudget
      have hcovNextBudget : covNext ≤ sepBeta B * sepTail s (l + 1) := by
        dsimp [covNext]
        exact max_le hcovNFbudget hcovNRbudget
      have hfeedF0 : 0 ≤ sepFeed c0F covF :=
        sepFeed_nonneg hc0F0 (lt_of_le_of_lt hc0F2 (by norm_num))
      have hfeedR0 : 0 ≤ sepFeed c0R covR :=
        sepFeed_nonneg hc0R0 (lt_of_le_of_lt hc0R2 (by norm_num))
      have hc0NF0 : 0 ≤ c0NF := by
        dsimp [c0NF, sepNextC0]
        nlinarith
      have hcovNF0 : 0 ≤ covNF := by
        dsimp [covNF, sepNextCov]
        nlinarith [hBpos.le]
      have hc0NR0 : 0 ≤ c0NR := by
        dsimp [c0NR, sepNextC0]
        nlinarith
      have hcovNR0 : 0 ≤ covNR := by
        dsimp [covNR, sepNextCov]
        nlinarith [hBpos.le]
      have hc0Next0 : 0 ≤ c0Next := by
        dsimp [c0Next]
        exact le_max_of_le_left hc0NF0
      have hcovNext0 : 0 ≤ covNext := by
        dsimp [covNext]
        exact le_max_of_le_left hcovNF0
      have htailNext0 : 0 ≤ sepTail s (l + 1) := sepTail_nonneg s (l + 1)
      have htailNextε : sepBeta B * sepTail s (l + 1) ≤ ε :=
        hjε s (le_trans hjεj hs) (l + 1)
      have htailNextHalf : sepBeta B * sepTail s (l + 1) ≤ 1 / 2 :=
        hjβ s (le_trans hjβj hs) (l + 1)
      have htwoTail_le_betaTail :
          2 * sepTail s (l + 1) ≤ sepBeta B * sepTail s (l + 1) := by
        have h2β : (2 : ℝ) ≤ sepBeta B := le_trans (by norm_num) hβ4
        exact mul_le_mul_of_nonneg_right h2β htailNext0
      have hc0Nextε : c0Next ≤ ε := by
        exact le_trans hc0NextBudget (le_trans htwoTail_le_betaTail htailNextε)
      have hcovNextε : covNext ≤ ε := by
        exact le_trans hcovNextBudget htailNextε
      have hc0NextHalf : c0Next ≤ 1 / 2 := by
        exact le_trans hc0NextBudget (le_trans htwoTail_le_betaTail htailNextHalf)
      have hcovNextHalf : covNext ≤ 1 / 2 := by
        exact le_trans hcovNextBudget htailNextHalf
      let Rcur : ℝ := (2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 1))
      let Rnext : ℝ := (2 : ℝ) ^ s * (1 + (1 / 2 : ℝ) ^ (l + 2))
      let Rmid : ℝ := midRad s l
      have hRnext_pos : 0 < Rnext := by
        dsimp [Rnext]
        positivity
      have hRmid_pos : 0 < Rmid := by
        dsimp [Rmid, midRad]
        positivity
      have hRnext_lt_Rmid : Rnext < Rmid := by
        simpa [Rnext, Rmid] using openRad_next_lt_mid s l
      have hRmid_lt_Rcur : Rmid < Rcur := by
        simpa [Rmid, Rcur] using midRad_lt_openRad s l
      let U₁ : TopologicalSpace.Opens (X.obj (σ s)).M :=
        ⟨Metric.ball ((X.obj (σ s)).basepoint) Rmid, by
          have hb :
              @IsOpen (X.obj (σ s)).M
                (P (σ s)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
                (Metric.ball ((X.obj (σ s)).basepoint) Rmid) := by
            letI : MetricSpace (X.obj (σ s)).M := (P (σ s)).ms
            exact Metric.isOpen_ball
          rwa [ProperMetricOn.top_eq (X.obj (σ s)) (P (σ s))] at hb⟩
      let K₂ : TopologicalSpace.Opens (X.obj (σ (s + l))).M :=
        ⟨Metric.ball ((X.obj (σ (s + l))).basepoint) ((2 : ℝ) ^ (s + l + 1)),
          by
            have hb :
                @IsOpen (X.obj (σ (s + l))).M
                  (P (σ (s + l))).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
                  (Metric.ball ((X.obj (σ (s + l))).basepoint) ((2 : ℝ) ^ (s + l + 1))) := by
              letI : MetricSpace (X.obj (σ (s + l))).M := (P (σ (s + l))).ms
              exact Metric.isOpen_ball
            rwa [ProperMetricOn.top_eq (X.obj (σ (s + l))) (P (σ (s + l)))] at hb⟩
      haveI hU₁_nonempty : Nonempty U₁ :=
        ⟨⟨(X.obj (σ s)).basepoint, Metric.mem_ball_self hRmid_pos⟩⟩
      haveI hK₂_nonempty : Nonempty K₂ :=
        ⟨⟨(X.obj (σ (s + l))).basepoint,
          Metric.mem_ball_self (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + l + 1))⟩⟩
      have hU₁_src : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l).source := by
        intro x hx
        exact DforAcc.source_sub (Metric.ball_subset_ball hRmid_lt_Rcur.le hx)
      have hK₂_src : (K₂ : Set (X.obj (σ (s + l))).M) ⊆ (Ψ (s + l)).source := by
        intro y hy
        exact hΨsrc (s + l) (Metric.ball_subset_closedBall hy)
      have D₁mid : BookApproxIsoSep (I := I) (U₁ : Set (X.obj (σ s)).M) c0F covF p
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric :=
        DforAcc.mono (Metric.ball_subset_ball hRmid_lt_Rcur.le) le_rfl le_rfl
      obtain ⟨DstepF⟩ := hΨdata (s + l)
      have hp_stepF : p ≤ s + l :=
        le_trans hpj (le_trans hs (Nat.le_add_right s l))
      have D₂openF : BookApproxIsoSep (I := I) (K₂ : Set (X.obj (σ (s + l))).M)
          δF δF p (Ψ (s + l))
          (X.obj (σ (s + l))).metric (X.obj (σ (s + l + 1))).metric := by
        dsimp [δF]
        exact ((DstepF.monoP hp_stepF).mono Metric.ball_subset_closedBall le_rfl
          DstepF.forward.eps_lt_one).toSep
      have hclosed_mid_sub :
          Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid) ⊆
            Metric.ball ((X.obj (σ s)).basepoint) Rcur :=
        closedEBall_ofReal_subset_ball ((X.obj (σ s)).basepoint)
          (le_of_lt hRmid_pos) hRmid_lt_Rcur
      have hdata_mid : PreApproxIsoDataOn (I := I)
          (Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid)) (1 / 2) p
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
            (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric :=
        (DforAcc.forward.mono hclosed_mid_sub le_rfl le_rfl).toBook
          (by norm_num) (by norm_num) hc0F2 hcovF2
      have hsrc_mid :
          Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid) ⊆
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l).source :=
        fun x hx => DforAcc.source_sub (hclosed_mid_sub hx)
      have hcenter :
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
              (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
              ((X.obj (σ s)).basepoint)
            = (X.obj (σ (s + l))).basepoint :=
        chainComp_base (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ
          (fun i => (X.obj (σ i)).basepoint) hΨbase s l
      have himg_mid :
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
              (X.obj (σ s)).M → (X.obj (σ (s + l))).M) ''
              Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
            Metric.ball ((X.obj (σ (s + l))).basepoint) ((2 : ℝ) ^ (s + l + 1)) := by
        have htmp :
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
                (X.obj (σ s)).M → (X.obj (σ (s + l))).M) ''
                Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
              Metric.ball
                ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l :
                    (X.obj (σ s)).M → (X.obj (σ (s + l))).M)
                  ((X.obj (σ s)).basepoint))
                ((2 : ℝ) ^ (s + l + 1)) :=
          data_image_metric_ball (I := I)
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l)
            (by
              intro x v
              simpa using
                (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                  (I := I) (X.obj (σ s)).metric x v))
            (by
              intro x v
              simpa using
                (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                  (I := I) (X.obj (σ (s + l))).metric x v))
            hRmid_pos le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by
              simpa [Rmid] using
                (imageMid_lt_step (a := (1 / 2 : ℝ)) s l
                  (by norm_num) (by norm_num)))
            hdata_mid hsrc_mid
        intro y hy
        simpa [hcenter] using htmp hy
      have hKcompactF : IsCompact
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) := by
        have hcompact :
            @IsCompact (X.obj (σ s)).M
              (P (σ s)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
              (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) := by
          letI : MetricSpace (X.obj (σ s)).M := (P (σ s)).ms
          haveI : ProperSpace (X.obj (σ s)).M := (P (σ s)).proper
          simpa using (isCompact_closedBall ((X.obj (σ s)).basepoint) Rnext)
        rw [ProperMetricOn.top_eq (X.obj (σ s)) (P (σ s))] at hcompact
        exact hcompact
      have hKU₁F : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (U₁ : Set (X.obj (σ s)).M) :=
        Metric.closedBall_subset_ball hRnext_lt_Rmid
      have hqF1 : sepFeed c0F covF ≤ 1 :=
        sepFeed_le_one hc0F2 (le_trans hcovF2 (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hC_le_B : C ≤ B := by
        dsimp [B]
        exact le_max_left C 2
      have hcovF_out : sepFeed c0F covF + δF * C ≤ covNext := by
        calc
          sepFeed c0F covF + δF * C = δF * C + sepFeed c0F covF := by ring
          _ ≤ δF * B + sepFeed c0F covF := by
            exact add_le_add_left (mul_le_mul_of_nonneg_left hC_le_B hδF0) _
          _ = sepFeed c0F covF + δF * B := by ring
          _ = covNF := by rfl
          _ ≤ covNext := by
            dsimp [covNext]
            exact le_max_left _ _
      have hFclosedSep : PreApproxIsoSep (I := I)
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          (PartialDiffeomorph.trans (I := I)
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l) (Ψ (s + l)) :
              (X.obj (σ s)).M → (X.obj (σ (s + l + 1))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + l + 1))).metric :=
        compSepFwd (I := I)
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l) (Ψ (s + l))
          hU₁_src hK₂_src himg_mid hKcompactF hKU₁F hc0F2
          hfeedF0 hqF1 (sepFeed_c0 c0F covF) (sepFeed_cov c0F covF)
          hδF0 le_rfl le_rfl C hC0
          (by
            dsimp [c0Next, c0NF, sepNextC0]
            exact le_max_left _ _)
          hcovF_out
          ((comp_cov_le_unif.{u, uE, uH} (I := I) p).choose_spec.2)
          (X.obj (σ s)).metric (X.obj (σ (s + l))).metric (X.obj (σ (s + l + 1))).metric
          D₁mid D₂openF
      obtain ⟨DstepR⟩ := hΨdata s
      have hp_stepR : p ≤ s := le_trans hpj hs
      have DstepR_p := DstepR.monoP hp_stepR
      have hstepR_half : δR ≤ 1 / 2 := by
        dsimp [δR]
        exact half_pow_succ_le_half s
      have hRmid_le_step : Rmid ≤ (2 : ℝ) ^ (s + 1) := by
        change midRad s l ≤ (2 : ℝ) ^ (s + 1)
        exact midRad_le_step s l
      have hU₁_sub_step :
          (U₁ : Set (X.obj (σ s)).M) ⊆
            Metric.closedBall ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ (s + 1)) := by
        intro x hx
        exact Metric.closedBall_subset_closedBall hRmid_le_step (Metric.ball_subset_closedBall hx)
      have DstepRopen : BookApproxIsoSep (I := I) (U₁ : Set (X.obj (σ s)).M)
          δR δR p (Ψ s)
          (X.obj (σ s)).metric (X.obj (σ (s + 1))).metric := by
        dsimp [δR]
        exact (DstepR_p.mono hU₁_sub_step le_rfl DstepR.forward.eps_lt_one).toSep
      let Ktail : TopologicalSpace.Opens (X.obj (σ (s + 1))).M :=
        ⟨Metric.ball ((X.obj (σ (s + 1))).basepoint)
            ((2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1))),
          properMetric_isOpen_ball (I := I) (X.obj (σ (s + 1))) (P (σ (s + 1)))
            ((X.obj (σ (s + 1))).basepoint)
            ((2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1)))⟩
      haveI hKtail_nonempty : Nonempty Ktail := by
        dsimp [Ktail]
        exact properMetric_ball_nonempty (I := I) (X.obj (σ (s + 1))) (P (σ (s + 1)))
          ((X.obj (σ (s + 1))).basepoint) (openRad_pos (s + 1) l)
      have DtailR_Ktail : BookApproxIsoSep (I := I) (Ktail : Set (X.obj (σ (s + 1))).M)
          c0R covR p
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1)) htail_index)
          (X.obj (σ (s + 1))).metric (X.obj (σ (s + (l + 1)))).metric := by
        exact DrevTail
      have hKtail_src : (Ktail : Set (X.obj (σ (s + 1))).M) ⊆
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1)) htail_index).source :=
        DtailR_Ktail.source_sub
      let KmidE : Set (X.obj (σ s)).M :=
        Metric.closedEBall ((X.obj (σ s)).basepoint) (ENNReal.ofReal Rmid)
      have hclosed_mid_step : KmidE ⊆
            Metric.closedBall ((X.obj (σ s)).basepoint) ((2 : ℝ) ^ (s + 1)) := by
        dsimp [KmidE]
        rw [Metric.closedEBall_ofReal hRmid_pos.le]
        exact Metric.closedBall_subset_closedBall hRmid_le_step
      have hsrc_step_mid : KmidE ⊆ (Ψ s).source :=
        fun x hx => hΨsrc s (hclosed_mid_step hx)
      have hRmid_le_mid0 : Rmid ≤ midRad s 0 := by
        change midRad s l ≤ midRad s 0
        exact midRad_le_mid0 s l
      have hstep_image_radius :
          Real.sqrt (1 + δR) * Rmid
            < (2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1)) := by
        change Real.sqrt (1 + δR) * midRad s l
          < (2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1))
        exact imageMid_lt_openRad s l hδRpos hstepR_half
      have himg_step_mid :
          (Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M) '' (U₁ : Set (X.obj (σ s)).M) ⊆
            (Ktail : Set (X.obj (σ (s + 1))).M) := by
        have htmp :
            (Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M) ''
                Metric.ball ((X.obj (σ s)).basepoint) Rmid ⊆
              Metric.ball ((Ψ s : (X.obj (σ s)).M → (X.obj (σ (s + 1))).M)
                  ((X.obj (σ s)).basepoint))
                ((2 : ℝ) ^ (s + 1) * (1 + (1 / 2 : ℝ) ^ (l + 1))) :=
          data_image_metric_ball_of_superset (I := I) (Ψ s)
            (by
              intro x v
              simpa using
                (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                  (I := I) (X.obj (σ s)).metric x v))
            (by
              intro x v
              simpa using
                (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                  (I := I) (X.obj (σ (s + 1))).metric x v))
            hRmid_pos le_rfl hδR0 hstep_image_radius hclosed_mid_step DstepR_p.forward
            hsrc_step_mid
        intro y hy
        simpa [Ktail, hΨbase s] using htmp hy
      have hqR1 : sepFeed c0R covR ≤ 1 :=
        sepFeed_le_one hc0R2 (le_trans hcovR2 (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hcovR_out : sepFeed c0R covR + δR * C ≤ covNext := by
        calc
          sepFeed c0R covR + δR * C = δR * C + sepFeed c0R covR := by ring
          _ ≤ δR * B + sepFeed c0R covR := by
            exact add_le_add_left (mul_le_mul_of_nonneg_left hC_le_B hδR0) _
          _ = sepFeed c0R covR + δR * B := by ring
          _ = covNR := by rfl
          _ ≤ covNext := by
            dsimp [covNext]
            exact le_max_right _ _
      have hRclosedSep : PreApproxIsoSep (I := I)
          ((PartialDiffeomorph.trans (I := I) (Ψ s)
              (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1)) htail_index) :
                (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((PartialDiffeomorph.trans (I := I) (Ψ s)
              (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1)) htail_index)).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric :=
        compSepRev (I := I)
          (Ψ s) (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l (s + 1) (s + (l + 1)) htail_index)
          DstepRopen.source_sub hKtail_src himg_step_mid hKcompactF hKU₁F hc0R2
          hfeedR0 hqR1 (sepFeed_c0 c0R covR) (sepFeed_cov c0R covR)
          hδR0 le_rfl le_rfl C hC0
          (by
            dsimp [c0Next, c0NR, sepNextC0]
            exact le_max_right _ _)
          hcovR_out
          ((comp_cov_le_unif.{u, uE, uH} (I := I) p).choose_spec.2)
          (X.obj (σ s)).metric (X.obj (σ (s + 1))).metric (X.obj (σ (s + (l + 1)))).metric
          DstepRopen DtailR_Ktail
      refine ⟨c0Next, covNext, hc0Next0, hcovNext0, hc0Nextε, hcovNextε,
        hc0NextHalf, hcovNextHalf, hc0NextBudget, hcovNextBudget, ?_⟩
      have hfoldF_eq :
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (PartialDiffeomorph.trans (I := I)
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s l) (Ψ (s + l)) :
              (X.obj (σ s)).M → (X.obj (σ (s + l + 1))).M) := by
        funext x
        rw [chainComp_apply_succ]
        rfl
      have hfoldR_eq :
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (PartialDiffeomorph.trans (I := I) (Ψ s)
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l
              (s + 1) (s + (l + 1)) htail_index) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) := by
        funext x
        rw [chainComp'_apply_succ]
        rfl
      have hsrcFchain : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).source := by
        intro x hx
        exact ⟨hU₁_src (hKU₁F hx), hK₂_src (himg_mid (Set.mem_image_of_mem _ (hKU₁F hx)))⟩
      have hsrcRchain : Metric.closedBall ((X.obj (σ s)).basepoint) Rnext ⊆
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).source := by
        intro x hx
        exact ⟨DstepRopen.source_sub (hKU₁F hx),
          hKtail_src (himg_step_mid (Set.mem_image_of_mem _ (hKU₁F hx)))⟩
      have hfoldR_symm_eq :
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl).symm :
              (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
            =
          ((PartialDiffeomorph.trans (I := I) (Ψ s)
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ l
              (s + 1) (s + (l + 1)) htail_index)).symm :
              (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M) := by
        rfl
      have hFclosed : PreApproxIsoSep (I := I)
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
            (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hFclosedSep.congr_eq hfoldF_eq
      have hRclosed : PreApproxIsoSep (I := I)
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric := by
        simpa [image_eq_of_fun_eq hfoldR_eq] using
          hRclosedSep.congr_eq hfoldR_symm_eq
      have hLR_eq :
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
            =
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) :=
        (chainComp_eq_right (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s).symm
      have hRightForward : PreApproxIsoSep (I := I)
          (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl :
            (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M)
          (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hFclosed.congr_eq hLR_eq
      have hRightClosed :
          BookApproxIsoSep (I := I)
            (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        BookApproxIsoSep.ofParts hsrcRchain hRightForward hRclosed
      have hU₁_srcRchain : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).source := by
        intro x hx
        exact ⟨DstepRopen.source_sub hx,
          hKtail_src (himg_step_mid (Set.mem_image_of_mem _ hx))⟩
      have hU₁_srcFchain : (U₁ : Set (X.obj (σ s)).M) ⊆
          (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).source := by
        intro x hx
        exact ⟨hU₁_src hx, hK₂_src (himg_mid (Set.mem_image_of_mem _ hx))⟩
      haveI hNonempty_src_s : Nonempty (X.obj (σ s)).M := ⟨(X.obj (σ s)).basepoint⟩
      have hrev_germ_final :
          ∀ y ∈ (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
                (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
                Metric.closedBall ((X.obj (σ s)).basepoint) Rnext,
            ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
                (s + (l + 1)) rfl).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
              =ᶠ[nhds y]
            ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).symm :
                (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M) := by
        have hgermU :=
          symm_eventuallyEq_on_image (I := I)
            (Φ := chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1))
            (Ψ := chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            hU₁_srcFchain hU₁_srcRchain hLR_eq
        intro y hy
        exact hgermU y (Set.image_mono hKU₁F hy)
      have hR_on_left_zone : PreApproxIsoSep (I := I)
          ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
            (s + (l + 1)) rfl).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric := by
        simpa [image_eq_of_fun_eq hLR_eq] using hRclosed
      have hLeftReverse : PreApproxIsoSep (I := I)
          ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1) :
              (X.obj (σ s)).M → (X.obj (σ (s + (l + 1)))).M) ''
            Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
          ((chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1)).symm :
            (X.obj (σ (s + (l + 1)))).M → (X.obj (σ s)).M)
          (X.obj (σ (s + (l + 1)))).metric (X.obj (σ s)).metric :=
        hR_on_left_zone.congr (fun y hy => (hrev_germ_final y hy).symm)
      have hLeftClosed :
          BookApproxIsoSep (I := I)
            (Metric.closedBall ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1))
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        BookApproxIsoSep.ofParts hsrcFchain hFclosed hLeftReverse
      have hLeftOpen :
          BookApproxIsoSep (I := I)
            (Metric.ball ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainComp (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ s (l + 1))
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hLeftClosed.mono Metric.ball_subset_closedBall le_rfl le_rfl
      have hRightOpen :
          BookApproxIsoSep (I := I)
            (Metric.ball ((X.obj (σ s)).basepoint) Rnext) c0Next covNext p
            (chainComp' (I := I) (Mf := fun i => (X.obj (σ i)).M) Ψ (l + 1) s
              (s + (l + 1)) rfl)
            (X.obj (σ s)).metric (X.obj (σ (s + (l + 1)))).metric :=
        hRightClosed.mono Metric.ball_subset_closedBall le_rfl le_rfl
      exact ⟨⟨by simpa [Rnext] using hLeftOpen⟩, fun m hm => by
        cases hm
        exact ⟨by simpa [Rnext] using hRightOpen⟩⟩


end Endpoint

end HCGCompactness
end DifferentialGeometry
