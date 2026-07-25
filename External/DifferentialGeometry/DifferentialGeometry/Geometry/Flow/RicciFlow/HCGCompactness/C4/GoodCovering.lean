import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepAInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PointedEmetric

set_option autoImplicit false
set_option linter.style.longLine false















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace InjRadiusDecayInput

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}




noncomputable def mu (hd : InjRadiusDecayInput (I := I) X) (r : Real) : Real :=
  hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) * Real.exp (-hd.C * r)


noncomputable def lambda (hd : InjRadiusDecayInput (I := I) X) (D r : Real) : Real :=
  hd.mu r / D

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem mu_pos (hd : InjRadiusDecayInput (I := I) X) (r : Real) : 0 < hd.mu r :=
  mul_pos (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)) (Real.exp_pos _)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem mu_nonneg (hd : InjRadiusDecayInput (I := I) X) (r : Real) : 0 ≤ hd.mu r :=
  (hd.mu_pos r).le

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem mu_antitone (hd : InjRadiusDecayInput (I := I) X) : Antitone hd.mu := by
  intro r₁ r₂ h
  have hK : 0 ≤ hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) :=
    (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)).le
  have hexp : Real.exp (-hd.C * r₂) ≤ Real.exp (-hd.C * r₁) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left h hd.C_nonneg])
  exact mul_le_mul_of_nonneg_left hexp hK



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem mu_hasInj_of_le (hd : InjRadiusDecayInput (I := I) X)
    {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint <= R) :
    HasInjRadiusAt (I := I) (X.obj k) x (hd.mu R) := by
  have hdecay : HasInjRadiusAt (I := I) (X.obj k) x
      (hd.mu (hd.dist k x (X.obj k).basepoint)) := by
    simpa [mu] using hd.decay k x
  exact HasInjRadiusAt.mono (I := I) hdecay (hd.mu_pos R) (hd.mu_antitone hx)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_pos (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (r : Real) : 0 < hd.lambda D r :=
  div_pos (hd.mu_pos r) hD

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_antitone (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D) :
    Antitone (hd.lambda D) := by
  intro r₁ r₂ h
  exact mul_le_mul_of_nonneg_right (hd.mu_antitone h) (inv_nonneg.mpr hD.le)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_le_mu (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 1 ≤ D)
    (r : Real) : hd.lambda D r ≤ hd.mu r :=
  div_le_self (hd.mu_nonneg r) hD



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_continuous (hd : InjRadiusDecayInput (I := I) X) (D : Real) :
    Continuous (hd.lambda D) := by
  unfold InjRadiusDecayInput.lambda InjRadiusDecayInput.mu
  fun_prop



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_le_one_at_zero (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) ≤ D) :
    hd.lambda D 0 ≤ 1 := by
  have hpos : 0 < hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) :=
    mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)
  have hDpos : 0 < D := lt_of_lt_of_le hpos hD
  unfold lambda mu
  rw [mul_zero, Real.exp_zero, mul_one]
  exact (div_le_one hDpos).mpr hD




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_hasInjRadiusAt (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 1 ≤ D) (k : Nat) (x : (X.obj k).M) :
    HasInjRadiusAt (I := I) (X.obj k) x
      (hd.lambda D (hd.dist k x (X.obj k).basepoint)) := by
  have hdecay := hd.decay k x
  rw [hasInjRadiusAt_iff] at hdecay ⊢
  refine ⟨hd.lambda_pos (lt_of_lt_of_le one_pos hD) _, ?_⟩
  exact le_trans (ENNReal.ofReal_le_ofReal (hd.lambda_le_mu hD _)) hdecay.2

end InjRadiusDecayInput








section Packing

variable {α : Type*} {β : Type*}



theorem exists_maximal_pairwiseDisjoint (f : α → Set β) :
    ∃ S : Set α, S.PairwiseDisjoint f ∧
      ∀ T : Set α, S ⊆ T → T.PairwiseDisjoint f → T ⊆ S := by
  have hchainub : ∀ c ⊆ {T : Set α | T.PairwiseDisjoint f}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {T : Set α | T.PairwiseDisjoint f}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    intro x hx y hy hxy
    rw [Set.mem_sUnion] at hx hy
    obtain ⟨s₁, hs₁, hx⟩ := hx
    obtain ⟨s₂, hs₂, hy⟩ := hy
    rcases hchain.total hs₁ hs₂ with hsub | hsub
    · exact hc hs₂ (hsub hx) hy hxy
    · exact hc hs₁ hx (hsub hy) hxy
  obtain ⟨S, hSpd, hSmax⟩ :=
    zorn_subset {T : Set α | T.PairwiseDisjoint f} hchainub
  exact ⟨S, hSpd, fun T hST hT => hSmax hT hST⟩




theorem exists_not_disjoint_of_maximal_pairwiseDisjoint (f : α → Set β) {S : Set α}
    (hS : S.PairwiseDisjoint f)
    (hmax : ∀ T : Set α, S ⊆ T → T.PairwiseDisjoint f → T ⊆ S)
    {z : α} (hz : z ∉ S) :
    ∃ x ∈ S, ¬ Disjoint (f z) (f x) := by
  by_contra hcon
  push Not at hcon
  exact hz (hmax (insert z S) (Set.subset_insert z S)
    (hS.insert fun y hy _ => hcon y hy) (Set.mem_insert z S))

end Packing

namespace InjRadiusDecayInput

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}



def lambdaBall (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (x : (X.obj k).M) : Set ((X.obj k).M) :=
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  Metric.eball x (ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)))





omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_lambdaNet (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat) :
    ∃ S : Set ((X.obj k).M),
      S.PairwiseDisjoint (hd.lambdaBall D k) ∧
      ∀ T : Set ((X.obj k).M),
        S ⊆ T → T.PairwiseDisjoint (hd.lambdaBall D k) → T ⊆ S :=
  exists_maximal_pairwiseDisjoint (hd.lambdaBall D k)








omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambdaNet_cover (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    (hmax : ∀ T : Set ((X.obj k).M),
      S ⊆ T → T.PairwiseDisjoint (hd.lambdaBall D k) → T ⊆ S)
    (z : (X.obj k).M) :
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
    ∃ x ∈ S, edist z x <
      ENNReal.ofReal (hd.lambda D (hd.dist k z (X.obj k).basepoint)) +
      ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  by_cases hz : z ∈ S
  · refine ⟨z, hz, ?_⟩
    rw [edist_self]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (hd.lambda_pos hD _)) le_self_add
  · obtain ⟨x, hxS, hndis⟩ :=
      exists_not_disjoint_of_maximal_pairwiseDisjoint (hd.lambdaBall D k) hS hmax hz
    obtain ⟨w, hwz, hwx⟩ := Set.not_disjoint_iff.mp hndis
    refine ⟨x, hxS, ?_⟩
    have e1 : edist w z <
        ENNReal.ofReal (hd.lambda D (hd.dist k z (X.obj k).basepoint)) := hwz
    have e2 : edist w x <
        ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) := hwx
    calc edist z x ≤ edist z w + edist w x := edist_triangle z w x
      _ < _ := by rw [edist_comm z w]; exact ENNReal.add_lt_add e1 e2







omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambdaNet_separated (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    {x y : (X.obj k).M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
    ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) ≤ edist x y := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have hdisj := Set.disjoint_left.mp (hS hx hy hxy)
  by_contra hlt
  push Not at hlt
  have hyx : y ∈ hd.lambdaBall D k x :=
    lt_of_eq_of_lt (edist_comm y x) hlt
  have hyy : y ∈ hd.lambdaBall D k y :=
    lt_of_eq_of_lt (edist_self y) (ENNReal.ofReal_pos.mpr (hd.lambda_pos hD _))
  exact hdisj hyx hyy






structure RealizesEdist (hd : InjRadiusDecayInput (I := I) X) : Prop where
  dist_nonneg : ∀ (k : Nat) (x y : (X.obj k).M), 0 ≤ hd.dist k x y
  edist_eq : ∀ (k : Nat) (x y : (X.obj k).M),
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     edist x y) = ENNReal.ofReal (hd.dist k x y)

namespace RealizesEdist


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem subseq {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (f : Nat -> Nat) :
    (hd.subseq f).RealizesEdist := by
  refine ⟨?_, ?_⟩
  · intro k x y
    exact hre.dist_nonneg (f k) x y
  · intro k x y
    simpa [InjRadiusDecayInput.subseq, PointedRiemannianSeq.subseq] using
      hre.edist_eq (f k) x y

end RealizesEdist


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem RealizesEdist.dist_comm {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (k : Nat) (x y : (X.obj k).M) :
    hd.dist k x y = hd.dist k y x := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have : ENNReal.ofReal (hd.dist k x y) = ENNReal.ofReal (hd.dist k y x) := by
    rw [← hre.edist_eq k x y, ← hre.edist_eq k y x, edist_comm]
  exact (ENNReal.ofReal_eq_ofReal_iff (hre.dist_nonneg k x y)
    (hre.dist_nonneg k y x)).mp this



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem RealizesEdist.dist_triangle {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (k : Nat) (x y z : (X.obj k).M) :
    hd.dist k x z ≤ hd.dist k x y + hd.dist k y z := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have h1 : ENNReal.ofReal (hd.dist k x z) ≤
      ENNReal.ofReal (hd.dist k x y) + ENNReal.ofReal (hd.dist k y z) := by
    rw [← hre.edist_eq k x z, ← hre.edist_eq k x y, ← hre.edist_eq k y z]
    exact edist_triangle x y z
  rw [← ENNReal.ofReal_add (hre.dist_nonneg k x y) (hre.dist_nonneg k y z)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (hre.dist_nonneg k x y) (hre.dist_nonneg k y z))).mp h1


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem RealizesEdist.distO_sub_le {hd : InjRadiusDecayInput (I := I) X}
    (hre : hd.RealizesEdist) (k : Nat) (x y : (X.obj k).M) :
    hd.dist k y (X.obj k).basepoint - hd.dist k x (X.obj k).basepoint ≤ hd.dist k x y := by
  have h := hre.dist_triangle k y x (X.obj k).basepoint
  have hc := hre.dist_comm k y x
  linarith


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_eq (hd : InjRadiusDecayInput (I := I) X) (D r : Real) :
    hd.lambda D r =
      (hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D) * Real.exp (-hd.C * r) := by
  unfold InjRadiusDecayInput.lambda InjRadiusDecayInput.mu
  ring




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_exp_le (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    {s t d : Real} (h : s - t ≤ d) :
    hd.lambda D t ≤ Real.exp (hd.C * d) * hd.lambda D s := by
  rw [hd.lambda_eq D, hd.lambda_eq D]
  have hP : 0 ≤ hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D :=
    le_of_lt (div_pos (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)) hD)
  rw [show Real.exp (hd.C * d) *
        (hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D *
          Real.exp (-hd.C * s))
      = hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D *
          Real.exp (hd.C * d + -hd.C * s) from by
        rw [Real.exp_add]; ring]
  apply mul_le_mul_of_nonneg_left _ hP
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left h hd.C_nonneg]




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambda_ratio_le (hd : InjRadiusDecayInput (I := I) X) (hre : hd.RealizesEdist)
    (D : Real) (k : Nat) (hD : 0 < D) (x y : (X.obj k).M) :
    hd.lambda D (hd.dist k x (X.obj k).basepoint) ≤
      Real.exp (hd.C * hd.dist k x y) *
        hd.lambda D (hd.dist k y (X.obj k).basepoint) := by
  rw [hd.lambda_eq D, hd.lambda_eq D]
  have hP : 0 ≤ hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D :=
    le_of_lt (div_pos (mul_pos hd.a_pos (pow_pos (lt_min hd.baseInj.pos one_pos) _)) hD)
  rw [show Real.exp (hd.C * hd.dist k x y) *
        (hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D *
          Real.exp (-hd.C * hd.dist k y (X.obj k).basepoint))
      = hd.a * (min hd.baseInj.ρ 1) ^ (Module.finrank Real E) / D *
          Real.exp (hd.C * hd.dist k x y + -hd.C * hd.dist k y (X.obj k).basepoint) from by
        rw [Real.exp_add]; ring]
  apply mul_le_mul_of_nonneg_left _ hP
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (hre.distO_sub_le k x y) hd.C_nonneg]




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambdaNet_dist_separated (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (k : Nat) (hD : 0 < D) (hre : hd.RealizesEdist) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    {x y : (X.obj k).M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    hd.lambda D (hd.dist k x (X.obj k).basepoint) ≤ hd.dist k x y := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  have hsep := hd.lambdaNet_separated D k hD hS hx hy hxy
  exact (ENNReal.ofReal_le_ofReal_iff (hre.dist_nonneg k x y)).mp
    (le_of_le_of_eq hsep (hre.edist_eq k x y))





omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem net_multiplicity (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) (hre : hd.RealizesEdist)
    (vc : VolumeComparisonInput (I := I) X) (hvc : vc.dist = hd.dist) (R : Real)
    (hRcap : 4 * hd.lambda D R ≤ vc.r0)
    {S : Set ((X.obj k).M)} (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    (hSR : ∀ x ∈ S, hd.dist k x (X.obj k).basepoint ≤ R)
    (z : (X.obj k).M) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJz : ∀ x ∈ J, hd.dist k x z ≤ 4 * hd.lambda D R) :
    J.card ≤ vc.Imult 4 := by
  classical
  have hr : 0 < hd.lambda D R := hd.lambda_pos hD R
  have hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → hd.lambda D R ≤ hd.dist k i j := by
    intro i hi j hj hij
    have hiS : i ∈ S := hJS (Finset.mem_coe.mpr hi)
    have hjS : j ∈ S := hJS (Finset.mem_coe.mpr hj)
    calc hd.lambda D R
        ≤ hd.lambda D (hd.dist k i (X.obj k).basepoint) :=
          hd.lambda_antitone hD (hSR i hiS)
      _ ≤ hd.dist k i j :=
          hd.lambdaNet_dist_separated D k hD hre hS hiS hjS hij
  have hmul := vc.ballMult 4 k
    (centers := fun i : {x // x ∈ J} => (i : (X.obj k).M)) (r := hd.lambda D R) hr hRcap
    (fun i j hij => by
      rw [hvc]; exact hsep i i.2 j j.2 (fun h => hij (Subtype.ext h)))
    z Finset.univ
    (fun j _ => by rw [hvc]; exact hJz j j.2)
  rwa [Finset.card_univ, Fintype.card_coe] at hmul





structure PackingBound (hd : InjRadiusDecayInput (I := I) X) (D : Real) where
  A : Real → Nat
  card_le : ∀ (k : Nat) (r : Real) (J : Finset ((X.obj k).M)),
    (∀ x ∈ J, hd.dist k x (X.obj k).basepoint ≤ r) →
    (∀ x ∈ J, ∀ y ∈ J, x ≠ y → hd.lambda D r ≤ hd.dist k x y) →
    J.card ≤ A r

namespace PackingBound


def subseq {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    (pb : hd.PackingBound D) (f : Nat -> Nat) :
    (hd.subseq f).PackingBound D where
  A := pb.A
  card_le := by
    intro k r J hJr hsep
    refine pb.card_le (f k) r J ?_ ?_
    · intro x hx
      simpa [InjRadiusDecayInput.subseq, PointedRiemannianSeq.subseq] using hJr x hx
    · intro x hx y hy hxy
      simpa [InjRadiusDecayInput.subseq, InjRadiusDecayInput.lambda,
        InjRadiusDecayInput.mu, PointedRiemannianSeq.subseq] using hsep x hx y hy hxy

end PackingBound




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem net_count_le (hd : InjRadiusDecayInput (I := I) X) (hre : hd.RealizesEdist)
    (D : Real) (k : Nat) (hD : 0 < D) (pb : hd.PackingBound D)
    {S : Set ((X.obj k).M)} (hS : S.PairwiseDisjoint (hd.lambdaBall D k))
    (r : Real) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJr : ∀ x ∈ J, hd.dist k x (X.obj k).basepoint ≤ r) :
    J.card ≤ pb.A r := by
  refine pb.card_le k r J hJr (fun x hx y hy hxy => ?_)
  calc hd.lambda D r
      ≤ hd.lambda D (hd.dist k x (X.obj k).basepoint) :=
        hd.lambda_antitone hD (hJr x hx)
    _ ≤ hd.dist k x y :=
        hd.lambdaNet_dist_separated D k hD hre hS (hJS (Finset.mem_coe.mpr hx))
          (hJS (Finset.mem_coe.mpr hy)) hxy




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem net_finite_in_ball (hd : InjRadiusDecayInput (I := I) X) (hre : hd.RealizesEdist)
    (D : Real) (k : Nat) (hD : 0 < D) (pb : hd.PackingBound D)
    {S : Set ((X.obj k).M)} (hS : S.PairwiseDisjoint (hd.lambdaBall D k)) (r : Real) :
    (S ∩ {x | hd.dist k x (X.obj k).basepoint ≤ r}).Finite := by
  by_contra hinf
  have hinf' : (S ∩ {x | hd.dist k x (X.obj k).basepoint ≤ r}).Infinite := hinf
  obtain ⟨t, hts, htcard⟩ := hinf'.exists_subset_card_eq (pb.A r + 1)
  have hcard := net_count_le hd hre D k hD pb hS r t
    (hts.trans Set.inter_subset_left)
    (fun x hx => (hts (Finset.mem_coe.mpr hx)).2)
  omega




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_finite_cover (hd : InjRadiusDecayInput (I := I) X) (hre : hd.RealizesEdist)
    (D : Real) (k : Nat) (hD : 0 < D) (pb : hd.PackingBound D)
    {S : Set ((X.obj k).M)} (hSdisj : S.PairwiseDisjoint (hd.lambdaBall D k))
    (hSmax : ∀ T : Set ((X.obj k).M),
      S ⊆ T → T.PairwiseDisjoint (hd.lambdaBall D k) → T ⊆ S) (r : Real) :
    ∃ J ⊆ S, J.Finite ∧
      ∀ z : (X.obj k).M, hd.dist k z (X.obj k).basepoint ≤ r →
        ∃ x ∈ J,
          (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
           edist z x <
             ENNReal.ofReal (hd.lambda D (hd.dist k z (X.obj k).basepoint)) +
             ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint))) := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  refine ⟨S ∩ {x | hd.dist k x (X.obj k).basepoint ≤ r + 2 * hd.lambda D 0},
    Set.inter_subset_left,
    hd.net_finite_in_ball hre D k hD pb hSdisj _, ?_⟩
  intro z hz
  obtain ⟨x, hxS, hcov⟩ := hd.lambdaNet_cover D k hD hSdisj hSmax z
  have hcov_dist : hd.dist k z x <
      hd.lambda D (hd.dist k z (X.obj k).basepoint) +
      hd.lambda D (hd.dist k x (X.obj k).basepoint) := by
    have h := hcov
    rw [hre.edist_eq k z x,
        ← ENNReal.ofReal_add (hd.lambda_pos hD _).le (hd.lambda_pos hD _).le] at h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hre.dist_nonneg k z x)).mp h
  refine ⟨x, ⟨hxS, ?_⟩, hcov⟩
  have ht := hre.dist_triangle k x z (X.obj k).basepoint
  have hcomm := hre.dist_comm k x z
  have hlz := hd.lambda_antitone hD (hre.dist_nonneg k z (X.obj k).basepoint)
  have hlx := hd.lambda_antitone hD (hre.dist_nonneg k x (X.obj k).basepoint)
  simp only [Set.mem_setOf_eq]
  linarith







structure GoodCovering (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) where
  centers : Set ((X.obj k).M)
  disjoint : centers.PairwiseDisjoint (hd.lambdaBall D k)
  maximal : ∀ T : Set ((X.obj k).M),
    centers ⊆ T → T.PairwiseDisjoint (hd.lambdaBall D k) → T ⊆ centers
  cover : ∀ z : (X.obj k).M, ∃ x ∈ centers,
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     edist z x < ENNReal.ofReal (hd.lambda D (hd.dist k z (X.obj k).basepoint)) +
       ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)))
  separated : ∀ {x y : (X.obj k).M}, x ∈ centers → y ∈ centers → x ≠ y →
    (letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
     ENNReal.ofReal (hd.lambda D (hd.dist k x (X.obj k).basepoint)) ≤ edist x y)




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_goodCovering (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) : Nonempty (hd.GoodCovering D k hD) := by
  obtain ⟨S, hSdisj, hSmax⟩ := hd.exists_lambdaNet D k
  exact ⟨{ centers := S
           disjoint := hSdisj
           maximal := hSmax
           cover := fun z => hd.lambdaNet_cover D k hD hSdisj hSmax z
           separated := fun hx hy hxy => hd.lambdaNet_separated D k hD hSdisj hx hy hxy }⟩




def lambdaBallC (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat) (c : Real)
    (x : (X.obj k).M) : Set ((X.obj k).M) :=
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  Metric.eball x (ENNReal.ofReal (c * hd.lambda D (hd.dist k x (X.obj k).basepoint)))


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambdaBallC_subset (hd : InjRadiusDecayInput (I := I) X) (D : Real) (k : Nat)
    (hD : 0 < D) {c : Real} (hc : c ≤ 1) (x : (X.obj k).M) :
    hd.lambdaBallC D k c x ⊆ hd.lambdaBall D k x := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  intro w hw
  exact lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal (by
    nlinarith [hd.lambda_pos hD (hd.dist k x (X.obj k).basepoint)]))




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambdaBallC_pairwiseDisjoint (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (k : Nat) (hD : 0 < D) {c : Real} (hc : c ≤ 1) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (hd.lambdaBall D k)) :
    S.PairwiseDisjoint (hd.lambdaBallC D k c) :=
  hS.mono (fun x => hd.lambdaBallC_subset D k hD hc x)




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem mem_lambdaBallC_dist (hd : InjRadiusDecayInput (I := I) X) (hre : hd.RealizesEdist)
    (D : Real) (k : Nat) (c : Real) (x z : (X.obj k).M) :
    z ∈ hd.lambdaBallC D k c x ↔
      hd.dist k z x < c * hd.lambda D (hd.dist k x (X.obj k).basepoint) := by
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  show edist z x < ENNReal.ofReal (c * hd.lambda D (hd.dist k x (X.obj k).basepoint)) ↔ _
  rw [hre.edist_eq k z x]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hre.dist_nonneg k z x)





omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem lambdaBallC_subset_of_inter (hd : InjRadiusDecayInput (I := I) X)
    (hre : hd.RealizesEdist) (D : Real) (k : Nat) {c₁ c₂ : Real} (x y : (X.obj k).M)
    (hinter : (hd.lambdaBallC D k c₁ x ∩ hd.lambdaBallC D k c₁ y).Nonempty)
    (hc : 2 * (c₁ * hd.lambda D (hd.dist k x (X.obj k).basepoint)) +
          c₁ * hd.lambda D (hd.dist k y (X.obj k).basepoint)
        ≤ c₂ * hd.lambda D (hd.dist k y (X.obj k).basepoint)) :
    hd.lambdaBallC D k c₁ x ⊆ hd.lambdaBallC D k c₂ y := by
  obtain ⟨w, hwx, hwy⟩ := hinter
  rw [hd.mem_lambdaBallC_dist hre] at hwx hwy
  have hxy : hd.dist k x y <
      c₁ * hd.lambda D (hd.dist k x (X.obj k).basepoint) +
      c₁ * hd.lambda D (hd.dist k y (X.obj k).basepoint) := by
    have ht := hre.dist_triangle k x w y
    have hcomm := hre.dist_comm k x w
    linarith
  intro z hz
  rw [hd.mem_lambdaBallC_dist hre] at hz ⊢
  have ht := hre.dist_triangle k z x y
  linarith

end InjRadiusDecayInput

end HCGCompactness
end DifferentialGeometry
