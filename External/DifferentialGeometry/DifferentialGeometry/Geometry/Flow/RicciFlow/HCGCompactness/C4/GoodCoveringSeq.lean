import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringOrdered
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.DiagonalSubseq

set_option autoImplicit false
set_option linter.style.longLine false











noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}


noncomputable def seqCenter (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k α : Nat) :
    Option ((X.obj k).M) :=
  letI : MetricSpace (X.obj k).M := (P k).ms
  haveI : ProperSpace (X.obj k).M := (P k).proper
  OrderedNet.netCenter (X.obj k).basepoint (hd.lambda D) (hd.lambda_continuous D) α


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem seqCenter_zero (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k : Nat) :
    seqCenter hd D P k 0 = some (X.obj k).basepoint := by
  letI : MetricSpace (X.obj k).M := (P k).ms
  haveI : ProperSpace (X.obj k).M := (P k).proper
  exact OrderedNet.netCenter_zero _ _ _



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqCenter_dist_ge (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k : Nat) {α : Nat}
    (hα : α ≠ 0) {c : (X.obj k).M} (hc : seqCenter hd D P k α = some c) :
    letI : MetricSpace (X.obj k).M := (P k).ms
    hd.lambda D 0 ≤ dist c (X.obj k).basepoint := by
  letI : MetricSpace (X.obj k).M := (P k).ms
  haveI : ProperSpace (X.obj k).M := (P k).proper
  have hc' : OrderedNet.netCenter (X.obj k).basepoint (hd.lambda D)
      (hd.lambda_continuous D) α = some c := hc
  have hcO : c ≠ (X.obj k).basepoint :=
    OrderedNet.netCenter_ne (X.obj k).basepoint (hd.lambda_continuous D)
      (fun s => hd.lambda_pos hD s) hα hc'
      (OrderedNet.netCenter_zero (X.obj k).basepoint (hd.lambda D)
        (hd.lambda_continuous D))
  exact OrderedNet.netList_dist_ge (X.obj k).basepoint (hd.lambda_continuous D)
    (hd.lambda_antitone hD) (fun s => hd.lambda_pos hD s) α
    (OrderedNet.netCenter_mem (X.obj k).basepoint (hd.lambda D)
      (hd.lambda_continuous D) α hc') hcO




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqCenter_edist_ge (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k : Nat) {α : Nat}
    (hα : α ≠ 0) {c : (X.obj k).M} (hc : seqCenter hd D P k α = some c) :
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
    ENNReal.ofReal (hd.lambda D 0) ≤ edist c (X.obj k).basepoint := by
  letI : MetricSpace (X.obj k).M := (P k).ms
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace
  rw [(P k).realizes c (X.obj k).basepoint]
  exact ENNReal.ofReal_le_ofReal (seqCenter_dist_ge hd hD P k hα hc)


noncomputable def seqRadius (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k α : Nat) : Real :=
  letI : MetricSpace (X.obj k).M := (P k).ms
  haveI : ProperSpace (X.obj k).M := (P k).proper
  OrderedNet.netRadius (X.obj k).basepoint (hd.lambda D) (hd.lambda_continuous D) α


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqRadius_mem (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (k α : Nat) :
    seqRadius hd D P k α ∈ Set.Icc (0 : Real) (2 * hd.lambda D 0 * (α : Real)) := by
  unfold seqRadius
  letI : MetricSpace (X.obj k).M := (P k).ms
  haveI : ProperSpace (X.obj k).M := (P k).proper
  exact OrderedNet.netRadius_mem (X.obj k).basepoint (hd.lambda_continuous D)
    (hd.lambda_antitone hD) (fun s => hd.lambda_pos hD s) (P k).hint α



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem seqCenter_mu_hasInj (hd : InjRadiusDecayInput (I := I) X)
    {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (k α : Nat) {c : (X.obj k).M}
    (hc : seqCenter hd D P k α = some c) :
    HasInjRadiusAt (I := I) (X.obj k) c
      (hd.mu (2 * hd.lambda D 0 * (α : Real))) := by
  letI : MetricSpace (X.obj k).M := (P k).ms
  haveI : ProperSpace (X.obj k).M := (P k).proper
  apply hd.mu_hasInj_of_le
  rw [← ProperMetricOn.dist_eq hd hre P k]
  have hr : seqRadius hd D P k α = dist c (X.obj k).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ α hc
  rw [← hr]
  exact (seqRadius_mem hd hD P k α).2




structure NetLimitData (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) where
  φ : Nat → Nat
  φ_mono : StrictMono φ
  alive : Nat → Bool
  alive_eventually : ∀ α : Nat,
    ∀ᶠ k in atTop, (seqCenter hd D P (φ k) α).isSome = alive α
  rInf : Nat → Real
  rInf_mem : ∀ α : Nat, rInf α ∈ Set.Icc (0 : Real) (2 * hd.lambda D 0 * (α : Real))
  tendsto : ∀ α : Nat,
    Tendsto (fun k => seqRadius hd D P (φ k) α) atTop (𝓝 (rInf α))

namespace NetLimitData


def subseq {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    NetLimitData hd D P where
  φ := L.φ ∘ ψ
  φ_mono := L.φ_mono.comp hψ
  alive := L.alive
  alive_eventually := by
    intro α
    exact hψ.tendsto_atTop.eventually (L.alive_eventually α)
  rInf := L.rInf
  rInf_mem := L.rInf_mem
  tendsto := by
    intro α
    simpa [Function.comp_apply] using (L.tendsto α).comp hψ.tendsto_atTop

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem subseq_phi {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    (L.subseq hψ).φ = L.φ ∘ ψ := rfl

end NetLimitData




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_netLimitData (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    Nonempty (NetLimitData hd D P) := by
  obtain ⟨φ₁, hφ₁, h₁⟩ := exists_subseq_tendsto_pi
    (C := fun α => 2 * hd.lambda D 0 * (α : Real))
    (f := fun α k => seqRadius hd D P k α)
    (fun α k => seqRadius_mem hd hD P k α)
  choose rInf hrInfmem hrInftendsto using h₁
  obtain ⟨φ₂, hφ₂, h₂⟩ := exists_subseq_eventually_eq
    (b := fun α k => (seqCenter hd D P (φ₁ k) α).isSome)
  choose alive halive using h₂
  refine ⟨⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, alive, fun α => ?_, rInf, hrInfmem, fun α => ?_⟩⟩
  · simpa [Function.comp] using halive α
  · have h := (hrInftendsto α).comp hφ₂.tendsto_atTop
    simpa [Function.comp] using h




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.lambda_window (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (α : Nat) :
    ∀ᶠ k in atTop,
      hd.lambda D (L.rInf α) / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ k) α) ∧
      hd.lambda D (seqRadius hd D P (L.φ k) α) ≤ 2 * hd.lambda D (L.rInf α) := by
  have hpos := hd.lambda_pos hD (L.rInf α)
  have hcont : Tendsto (fun k => hd.lambda D (seqRadius hd D P (L.φ k) α)) atTop
      (𝓝 (hd.lambda D (L.rInf α))) :=
    ((hd.lambda_continuous D).continuousAt.tendsto).comp (L.tendsto α)
  have hmem := hcont.eventually
    (Ioo_mem_nhds (by linarith : hd.lambda D (L.rInf α) / 2 < hd.lambda D (L.rInf α))
      (by linarith : hd.lambda D (L.rInf α) < 2 * hd.lambda D (L.rInf α)))
  exact hmem.mono fun k hk => ⟨hk.1.le, hk.2.le⟩


noncomputable def NetLimitData.lamInf {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)} (L : NetLimitData hd D P)
    (α : Nat) : Real :=
  hd.lambda D (L.rInf α)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem NetLimitData.subseq_lamInf {hd : InjRadiusDecayInput (I := I) X}
    {D : Real} {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    (L.subseq hψ).lamInf = L.lamInf := rfl




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.tilde_disjoint (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) {α β : Nat} (hαβ : α ≠ β) :
    ∀ᶠ k in atTop,
      ∀ x y : (X.obj (L.φ k)).M,
        seqCenter hd D P (L.φ k) α = some x →
        seqCenter hd D P (L.φ k) β = some y →
        (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
         Disjoint (Metric.ball x (L.lamInf α / 2)) (Metric.ball y (L.lamInf β / 2))) := by
  filter_upwards [L.lambda_window hd hD P α, L.lambda_window hd hD P β] with k hkα hkβ
  intro x y hx hy
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  have hx' : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) α = some x := hx
  have hy' : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) β = some y := hy
  have hdisj := OrderedNet.netCenter_disjoint (X.obj (L.φ k)).basepoint
    (hd.lambda_continuous D) (fun s => hd.lambda_pos hD s) hαβ hx' hy'
  have hrx : seqRadius hd D P (L.φ k) α = dist x (X.obj (L.φ k)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ α hx'
  have hry : seqRadius hd D P (L.φ k) β = dist y (X.obj (L.φ k)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ β hy'
  have h1 : L.lamInf α / 2 ≤ hd.lambda D (dist x (X.obj (L.φ k)).basepoint) := by
    have h := hkα.1
    rw [hrx] at h
    exact h
  have h2 : L.lamInf β / 2 ≤ hd.lambda D (dist y (X.obj (L.φ k)).basepoint) := by
    have h := hkβ.1
    rw [hry] at h
    exact h
  exact hdisj.mono (Metric.ball_subset_ball h1) (Metric.ball_subset_ball h2)




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.scaled_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r a : Real) (ha : 2 < a) :
    ∀ᶠ k in atTop,
      ∀ p : (X.obj (L.φ k)).M,
        (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
         dist p (X.obj (L.φ k)).basepoint ≤ r) →
        ∃ γ : Nat, γ < pb.A r ∧ ∃ c : (X.obj (L.φ k)).M,
          seqCenter hd D P (L.φ k) γ = some c ∧
          (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
           dist p c < a * L.lamInf γ) := by
  have hwin : ∀ᶠ k in atTop, ∀ γ ∈ Finset.range (pb.A r),
      hd.lambda D (seqRadius hd D P (L.φ k) γ) <
        a / 2 * hd.lambda D (L.rInf γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ => by
      have hpos := hd.lambda_pos hD (L.rInf γ)
      have hcont : Tendsto (fun k => hd.lambda D (seqRadius hd D P (L.φ k) γ)) atTop
          (𝓝 (hd.lambda D (L.rInf γ))) :=
        ((hd.lambda_continuous D).continuousAt.tendsto).comp (L.tendsto γ)
      exact hcont.eventually (Iio_mem_nhds (by nlinarith))
  filter_upwards [hwin] with k hk
  intro p hp
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  have hpack := packingBound_pack hd hre pb P (L.φ k)
  obtain ⟨m, hm⟩ := OrderedNet.netList_passes (X.obj (L.φ k)).basepoint
    (hd.lambda_continuous D) (hd.lambda_antitone hD) (fun s => hd.lambda_pos hD s)
    hpack r
  have hpast : OrderedNet.availSet (X.obj (L.φ k)).basepoint (hd.lambda D)
      (OrderedNet.forbidden (X.obj (L.φ k)).basepoint (hd.lambda D)
        (OrderedNet.netList (X.obj (L.φ k)).basepoint (hd.lambda D)
          (hd.lambda_continuous D) m)) = ∅ ∨
      ∃ c ∈ OrderedNet.netList (X.obj (L.φ k)).basepoint (hd.lambda D)
          (hd.lambda_continuous D) m,
        dist p (X.obj (L.φ k)).basepoint < dist c (X.obj (L.φ k)).basepoint := by
    rcases hm with hm | ⟨c, hc, hcr⟩
    · exact Or.inl hm
    · exact Or.inr ⟨c, hc, lt_of_le_of_lt hp hcr⟩
  obtain ⟨c, hcmem, hcd, hcb⟩ := OrderedNet.netList_cover (X.obj (L.φ k)).basepoint
    (hd.lambda_continuous D) (hd.lambda_antitone hD) p m hpast
  obtain ⟨γ, hγlen, hγc⟩ := List.mem_iff_getElem.mp hcmem
  have hγm : γ ≤ m := Nat.lt_succ_iff.mp (hγlen.trans_le
    (OrderedNet.netList_length_le (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) m))
  have hcenter : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) γ = some c := by
    rw [OrderedNet.netCenter_of_stage (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) hγm hγlen, List.getElem?_eq_getElem hγlen, hγc]
  have hγA : γ < pb.A r := OrderedNet.netCenter_index_lt (X.obj (L.φ k)).basepoint
    (hd.lambda_continuous D) (hd.lambda_antitone hD) (fun s => hd.lambda_pos hD s)
    hpack γ hcenter (hcd.trans hp)
  have hrad : seqRadius hd D P (L.φ k) γ = dist c (X.obj (L.φ k)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ γ hcenter
  have hwγ := hk γ (Finset.mem_range.mpr hγA)
  rw [hrad] at hwγ
  refine ⟨γ, hγA, c, hcenter, ?_⟩
  have hscale : 2 * hd.lambda D (dist c (X.obj (L.φ k)).basepoint) <
      a * L.lamInf γ := by
    unfold NetLimitData.lamInf
    nlinarith
  exact hcb.trans hscale



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.hat_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) :
    ∀ᶠ k in atTop,
      ∀ p : (X.obj (L.φ k)).M,
        (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
         dist p (X.obj (L.φ k)).basepoint ≤ r) →
        ∃ γ : Nat, γ < pb.A r ∧ ∃ c : (X.obj (L.φ k)).M,
          seqCenter hd D P (L.φ k) γ = some c ∧
          (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
           dist p c < 4 * L.lamInf γ) :=
  L.scaled_cover hd hD P hre pb r 4 (by norm_num)




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.inner_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) :
    ∀ᶠ k in atTop,
      ∀ p : (X.obj (L.φ k)).M,
        (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
         dist p (X.obj (L.φ k)).basepoint ≤ r) →
        ∃ γ : Nat, γ < pb.A r ∧ ∃ c : (X.obj (L.φ k)).M,
          seqCenter hd D P (L.φ k) γ = some c ∧
          (letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
           dist p c < 3 * L.lamInf γ) :=
  L.scaled_cover hd hD P hre pb r 3 (by norm_num)



def BInter (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (lamInf : Nat → Real)
    (α β k : Nat) : Prop :=
  ∃ x y : (X.obj k).M,
    seqCenter hd D P k α = some x ∧ seqCenter hd D P k β = some y ∧
    (letI : MetricSpace (X.obj k).M := (P k).ms
     ¬ Disjoint (Metric.ball x (5 * lamInf α)) (Metric.ball y (5 * lamInf β)))


omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem BInter.symm (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (lamInf : Nat → Real)
    {a b k : Nat} (h : BInter hd D P lamInf a b k) :
    BInter hd D P lamInf b a k := by
  obtain ⟨x, y, hx, hy, hinter⟩ := h
  refine ⟨y, x, hy, hx, ?_⟩
  intro hdisj
  exact hinter hdisj.symm



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.binter_stable_tail
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (hstable : ∀ α β : Nat,
      (∀ᶠ k in atTop, BInter hd D P L.lamInf α β (L.φ k)) ∨
      (∀ᶠ k in atTop, ¬ BInter hd D P L.lamInf α β (L.φ k))) :
    ∀ᶠ k in atTop, ∀ α β : Fin (pb.A r),
      BInter hd D P L.lamInf (α : Nat) (β : Nat) (L.φ k) →
        ∀ᶠ j in atTop,
          BInter hd D P L.lamInf (α : Nat) (β : Nat) (L.φ j) := by
  apply Filter.eventually_all.mpr
  intro α
  apply Filter.eventually_all.mpr
  intro β
  rcases hstable (α : Nat) (β : Nat) with hinter | hdisjoint
  · exact Filter.Eventually.of_forall fun _ _ => hinter
  · filter_upwards [hdisjoint] with k hk
    exact fun hmeet => (hk hmeet).elim





omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_stableNet (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) :
    ∃ L' : NetLimitData hd D P, L'.rInf = L.rInf ∧
      ∀ α β : Nat,
        (∀ᶠ k in atTop, BInter hd D P L.lamInf α β (L'.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter hd D P L.lamInf α β (L'.φ k)) := by
  classical
  obtain ⟨ψ, hψ, hstab⟩ := exists_subseq_eventually_eq
    (ι := Nat × Nat) (b := fun pr k => decide (BInter hd D P L.lamInf pr.1 pr.2 (L.φ k)))
  refine ⟨⟨L.φ ∘ ψ, L.φ_mono.comp hψ, L.alive, fun α => ?_, L.rInf, L.rInf_mem,
    fun α => ?_⟩, rfl, fun α β => ?_⟩
  · have h := hψ.tendsto_atTop.eventually (L.alive_eventually α)
    simpa [Function.comp] using h
  · have h := (L.tendsto α).comp hψ.tendsto_atTop
    simpa [Function.comp] using h
  · obtain ⟨v, hv⟩ := hstab (α, β)
    cases v with
    | true => exact Or.inl (hv.mono fun k hk => of_decide_eq_true hk)
    | false => exact Or.inr (hv.mono fun k hk => of_decide_eq_false hk)



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.stable_subseq (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) {ψ : Nat -> Nat} (hψ : StrictMono ψ)
    (hstab :
      ∀ α β : Nat,
        (∀ᶠ k in atTop, BInter hd D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter hd D P L.lamInf α β (L.φ k))) :
    ∀ α β : Nat,
      (∀ᶠ k in atTop,
        BInter hd D P (L.subseq hψ).lamInf α β ((L.subseq hψ).φ k)) ∨
      (∀ᶠ k in atTop,
        ¬ BInter hd D P (L.subseq hψ).lamInf α β ((L.subseq hψ).φ k)) := by
  intro α β
  rcases hstab α β with h | h
  · exact Or.inl (by
      simpa [NetLimitData.subseq, Function.comp_apply] using
        hψ.tendsto_atTop.eventually h)
  · exact Or.inr (by
      simpa [NetLimitData.subseq, Function.comp_apply] using
        hψ.tendsto_atTop.eventually h)




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.rInf_close (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    {α β : Nat}
    (hfreq : ∃ᶠ k in atTop, BInter hd D P L.lamInf α β (L.φ k)) :
    L.rInf β ≤ L.rInf α + (5 * L.lamInf α + 5 * L.lamInf β) := by
  set l := atTop ⊓ Filter.principal {k : Nat | BInter hd D P L.lamInf α β (L.φ k)} with hl
  haveI hne : l.NeBot := Filter.frequently_iff_neBot.mp hfreq
  have hev : ∀ᶠ k in l, seqRadius hd D P (L.φ k) β ≤
      seqRadius hd D P (L.φ k) α + (5 * L.lamInf α + 5 * L.lamInf β) := by
    rw [hl, Filter.eventually_inf_principal]
    filter_upwards with k hk
    obtain ⟨x, y, hx, hy, hmeet⟩ := hk
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
    obtain ⟨w, hwx, hwy⟩ := Set.not_disjoint_iff.mp hmeet
    rw [Metric.mem_ball] at hwx hwy
    have hx' : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) α = some x := hx
    have hy' : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) β = some y := hy
    have hrx : seqRadius hd D P (L.φ k) α = dist x (X.obj (L.φ k)).basepoint := by
      unfold seqRadius
      exact OrderedNet.netRadius_of_center _ _ _ α hx'
    have hry : seqRadius hd D P (L.φ k) β = dist y (X.obj (L.φ k)).basepoint := by
      unfold seqRadius
      exact OrderedNet.netRadius_of_center _ _ _ β hy'
    rw [hrx, hry]
    have h1 := dist_triangle y x (X.obj (L.φ k)).basepoint
    have h2 := dist_triangle y w x
    rw [dist_comm w y] at hwy
    linarith
  exact le_of_tendsto_of_tendsto ((L.tendsto β).mono_left inf_le_left)
    (((L.tendsto α).mono_left inf_le_left).add_const _) hev





omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.nesting (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) {α β : Nat}
    (hfreq : ∃ᶠ k in atTop, BInter hd D P L.lamInf α β (L.φ k))
    (k : Nat) (hk : BInter hd D P L.lamInf α β (L.φ k))
    {x y : (X.obj (L.φ k)).M}
    (hx : seqCenter hd D P (L.φ k) α = some x)
    (hy : seqCenter hd D P (L.φ k) β = some y) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    Metric.ball x (5 * L.lamInf α) ⊆
      Metric.ball y (45 * Real.exp (hd.C * (10 * hd.lambda D 0)) * L.lamInf β) ∧
    Metric.ball x (45 * Real.exp (hd.C * (10 * hd.lambda D 0)) * L.lamInf α) ⊆
      Metric.ball y (205 * Real.exp (hd.C * (20 * hd.lambda D 0)) * L.lamInf β) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  obtain ⟨x', y', hx', hy', hmeet⟩ := hk
  have hxx : x' = x := Option.some.inj (hx'.symm.trans hx)
  have hyy : y' = y := Option.some.inj (hy'.symm.trans hy)
  rw [hxx, hyy] at hmeet
  obtain ⟨w, hwx, hwy⟩ := Set.not_disjoint_iff.mp hmeet
  rw [Metric.mem_ball] at hwx hwy
  have hdxy : dist x y < 5 * L.lamInf α + 5 * L.lamInf β := by
    have h2 := dist_triangle x w y
    rw [dist_comm w x] at hwx
    linarith
  have hlamβpos : 0 < L.lamInf β := hd.lambda_pos hD (L.rInf β)
  have hlamαpos : 0 < L.lamInf α := hd.lambda_pos hD (L.rInf α)
  have hα0 : L.lamInf α ≤ hd.lambda D 0 := hd.lambda_antitone hD (L.rInf_mem α).1
  have hβ0 : L.lamInf β ≤ hd.lambda D 0 := hd.lambda_antitone hD (L.rInf_mem β).1
  have hclose := L.rInf_close hd P hfreq
  have hgap : L.rInf β - L.rInf α ≤ 10 * hd.lambda D 0 := by linarith
  have hratio : L.lamInf α ≤ Real.exp (hd.C * (10 * hd.lambda D 0)) * L.lamInf β :=
    hd.lambda_exp_le hD hgap
  set E1 := Real.exp (hd.C * (10 * hd.lambda D 0)) with hE1
  set E2 := Real.exp (hd.C * (20 * hd.lambda D 0)) with hE2
  have hE1ge1 : (1 : Real) ≤ E1 := by
    rw [hE1, show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    exact mul_nonneg hd.C_nonneg (by linarith [(hd.lambda_pos hD 0).le])
  have hEmul : E1 * E1 = E2 := by
    rw [hE1, hE2, ← Real.exp_add]
    congr 1
    ring
  constructor
  · intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have ht := dist_triangle z x y
    have h1 : (10 : Real) * L.lamInf α ≤ 10 * (E1 * L.lamInf β) := by linarith
    have h5 : (5 : Real) * L.lamInf β ≤ 5 * (E1 * L.lamInf β) := by nlinarith
    nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one hE1ge1) hlamβpos]
  · intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have ht := dist_triangle z x y
    have hE12 : E1 ≤ E2 := by nlinarith
    have h1 : (45 : Real) * E1 * L.lamInf α ≤ 45 * E2 * L.lamInf β := by
      nlinarith [mul_le_mul_of_nonneg_left hratio
        (le_trans zero_le_one hE1ge1 : (0 : Real) ≤ E1)]
    have h2 : (5 : Real) * L.lamInf α ≤ 5 * E2 * L.lamInf β := by nlinarith
    have h3 : (5 : Real) * L.lamInf β ≤ 5 * E2 * L.lamInf β := by nlinarith
    nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one (hE1ge1.trans hE12)) hlamβpos]



set_option maxHeartbeats 800000 in






omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem NetLimitData.inter_count (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (vc : VolumeComparisonInput (I := I) X) (hvc : vc.dist = hd.dist)
    (hlam0r0 :
      (50 * Real.exp (hd.C * (20 * hd.lambda D 0))) * hd.lambda D 0 ≤ vc.r0)
    (α : Nat) :
    ∀ᶠ k in atTop,
      ∀ xα : (X.obj (L.φ k)).M, seqCenter hd D P (L.φ k) α = some xα →
      ∀ J : Finset Nat, (∀ β ∈ J, BInter hd D P L.lamInf α β (L.φ k)) →
        J.card ≤ vc.Imult (50 * Real.exp (hd.C * (20 * hd.lambda D 0))) := by
  classical
  have hwall : ∀ᶠ k in atTop,
      ∀ β ∈ Finset.range (pb.A (2 * hd.lambda D 0 * (α : Real) + 10 * hd.lambda D 0)),
        hd.lambda D (L.rInf β) / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ k) β) ∧
        hd.lambda D (seqRadius hd D P (L.φ k) β) ≤ 2 * hd.lambda D (L.rInf β) :=
    (Filter.eventually_all_finset _).mpr fun β _ => L.lambda_window hd hD P β
  filter_upwards [hwall, L.lambda_window hd hD P α] with k hkall hkα
  intro xα hxα J hJ
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  have hxα' : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) α = some xα := hxα
  have hpack := packingBound_pack hd hre pb P (L.φ k)
  set lam0 := hd.lambda D 0 with hlam0def
  have hlam0pos : 0 < lam0 := hd.lambda_pos hD 0
  have hE1ge1 : (1 : Real) ≤ Real.exp (hd.C * (10 * lam0)) := by
    rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (mul_nonneg hd.C_nonneg (by linarith))
  have hEmul : Real.exp (hd.C * (10 * lam0)) * Real.exp (hd.C * (10 * lam0)) =
      Real.exp (hd.C * (20 * lam0)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hJdata : ∀ β ∈ J, ∃ y : (X.obj (L.φ k)).M,
      seqCenter hd D P (L.φ k) β = some y ∧
      dist y xα < 5 * L.lamInf α + 5 * L.lamInf β := by
    intro β hβ
    obtain ⟨x', y', hx', hy', hmeet⟩ := hJ β hβ
    have hxx : x' = xα := Option.some.inj (hx'.symm.trans hxα)
    rw [hxx] at hmeet
    obtain ⟨w, hwx, hwy⟩ := Set.not_disjoint_iff.mp hmeet
    rw [Metric.mem_ball] at hwx hwy
    refine ⟨y', hy', ?_⟩
    have ht := dist_triangle y' w xα
    rw [dist_comm w y'] at hwy
    linarith
  haveI : Nonempty ((X.obj (L.φ k)).M) := ⟨(X.obj (L.φ k)).basepoint⟩
  choose! yf hyf hyd using hJdata
  have hα0 : L.lamInf α ≤ lam0 := hd.lambda_antitone hD (L.rInf_mem α).1
  have hrxα : seqRadius hd D P (L.φ k) α = dist xα (X.obj (L.φ k)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ α hxα'
  have hrkα : dist xα (X.obj (L.φ k)).basepoint ≤ 2 * lam0 * (α : Real) := by
    have h := (seqRadius_mem hd hD P (L.φ k) α).2
    rw [hrxα] at h
    exact h
  have hcap : ∀ β ∈ J, β < pb.A (2 * lam0 * (α : Real) + 10 * lam0) := by
    intro β hβ
    have hβ0 : L.lamInf β ≤ lam0 := hd.lambda_antitone hD (L.rInf_mem β).1
    have hyβ' : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) β = some (yf β) := hyf β hβ
    have hdyO : dist (yf β) (X.obj (L.φ k)).basepoint ≤
        2 * lam0 * (α : Real) + 10 * lam0 := by
      have ht := dist_triangle (yf β) xα (X.obj (L.φ k)).basepoint
      have hd1 := hyd β hβ
      linarith
    exact OrderedNet.netCenter_index_lt (X.obj (L.φ k)).basepoint
      (hd.lambda_continuous D) (hd.lambda_antitone hD) (fun s => hd.lambda_pos hD s)
      hpack β hyβ' hdyO
  have hsep : ∀ b c : {β // β ∈ J}, b ≠ c →
      hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) ≤
        dist (yf b) (yf c) := by
    intro b c hbc
    have hidx : (b : Nat) ≠ (c : Nat) := fun h => hbc (Subtype.ext h)
    have hyb : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) (b : Nat) = some (yf b) := hyf b b.2
    have hyc : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) (c : Nat) = some (yf c) := hyf c c.2
    have hne := OrderedNet.netCenter_ne (X.obj (L.φ k)).basepoint
      (hd.lambda_continuous D) (fun s => hd.lambda_pos hD s) hidx hyb hyc
    have hmb : yf b ∈ OrderedNet.netList (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) (max (b : Nat) (c : Nat)) :=
      (OrderedNet.netList_prefix _ _ _ (le_max_left _ _)).subset
        (OrderedNet.netCenter_mem _ _ _ _ hyb)
    have hmc : yf c ∈ OrderedNet.netList (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) (max (b : Nat) (c : Nat)) :=
      (OrderedNet.netList_prefix _ _ _ (le_max_right _ _)).subset
        (OrderedNet.netCenter_mem _ _ _ _ hyc)
    have hβ0 : L.lamInf (b : Nat) ≤ lam0 := hd.lambda_antitone hD (L.rInf_mem _).1
    have hdyO : dist (yf b) (X.obj (L.φ k)).basepoint ≤
        dist xα (X.obj (L.φ k)).basepoint + 10 * lam0 := by
      have ht := dist_triangle (yf b) xα (X.obj (L.φ k)).basepoint
      have hd1 := hyd b b.2
      linarith
    exact OrderedNet.netList_separated (X.obj (L.φ k)).basepoint
      (hd.lambda_continuous D) (hd.lambda_antitone hD) (fun s => hd.lambda_pos hD s)
      (max (b : Nat) (c : Nat)) hmb hmc hne hdyO
  have hcont : ∀ b : {β // β ∈ J},
      dist (yf b) xα ≤ 50 * Real.exp (hd.C * (20 * lam0)) *
        hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) := by
    intro b
    have hβJ := b.2
    have hβ0 : L.lamInf (b : Nat) ≤ lam0 := hd.lambda_antitone hD (L.rInf_mem _).1
    have hyβ' : OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
        (hd.lambda_continuous D) (b : Nat) = some (yf b) := hyf b hβJ
    have hrβ : seqRadius hd D P (L.φ k) (b : Nat) =
        dist (yf b) (X.obj (L.φ k)).basepoint := by
      unfold seqRadius
      exact OrderedNet.netRadius_of_center _ _ _ _ hyβ'
    have hwβ := hkall (b : Nat) (Finset.mem_range.mpr (hcap (b : Nat) hβJ))
    rw [hrβ] at hwβ
    have hwα := hkα
    rw [hrxα] at hwα
    have hlamb : hd.lambda D (L.rInf (b : Nat)) = L.lamInf (b : Nat) := rfl
    have hlama : hd.lambda D (L.rInf α) = L.lamInf α := rfl
    rw [hlamb] at hwβ
    rw [hlama] at hwα
    have hd1 := hyd b hβJ
    have hgapβ : dist xα (X.obj (L.φ k)).basepoint -
        dist (yf b) (X.obj (L.φ k)).basepoint ≤ 10 * lam0 := by
      have ht := dist_triangle xα (yf b) (X.obj (L.φ k)).basepoint
      rw [dist_comm xα (yf b)] at ht
      linarith
    have hlamβk : hd.lambda D (dist (yf b) (X.obj (L.φ k)).basepoint) ≤
        Real.exp (hd.C * (10 * lam0)) *
          hd.lambda D (dist xα (X.obj (L.φ k)).basepoint) :=
      hd.lambda_exp_le hD hgapβ
    have hgapR : (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) -
        dist xα (X.obj (L.φ k)).basepoint ≤ 10 * lam0 := by linarith
    have hlamRk : hd.lambda D (dist xα (X.obj (L.φ k)).basepoint) ≤
        Real.exp (hd.C * (10 * lam0)) *
          hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) :=
      hd.lambda_exp_le hD hgapR
    set E1 := Real.exp (hd.C * (10 * lam0)) with hE1d
    set lkα := hd.lambda D (dist xα (X.obj (L.φ k)).basepoint) with hlkαd
    set lkβ := hd.lambda D (dist (yf b) (X.obj (L.φ k)).basepoint) with hlkβd
    set lRk := hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) with hlRkd
    have hlkαpos : 0 < lkα := hd.lambda_pos hD _
    have hlRkpos : 0 < lRk := hd.lambda_pos hD _
    have h1 : L.lamInf (b : Nat) ≤ 2 * lkβ := by linarith [hwβ.1]
    have h2 : L.lamInf (b : Nat) ≤ 2 * E1 * lkα := by nlinarith
    have h3 : lkα ≤ 2 * L.lamInf α := hwα.2
    have h4 : L.lamInf α ≤ 2 * lkα := by linarith [hwα.1]
    have h5 : dist (yf b) xα < 25 * E1 * L.lamInf α := by nlinarith
    have h6 : L.lamInf α ≤ 2 * E1 * lRk := by nlinarith
    have h7 : (25 : Real) * E1 * L.lamInf α ≤ 50 * (E1 * E1) * lRk := by nlinarith
    rw [← hEmul]
    nlinarith
  have hr0 : 0 < hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) :=
    hd.lambda_pos hD _
  have hcapr :
      (50 * Real.exp (hd.C * (20 * lam0))) *
          hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) ≤ vc.r0 := by
    have hdist0 : (0 : Real) ≤ dist xα (X.obj (L.φ k)).basepoint := dist_nonneg
    have harg : (0 : Real) ≤ dist xα (X.obj (L.φ k)).basepoint + 10 * lam0 := by
      linarith [hlam0pos.le]
    have hrle0 : hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0) ≤ lam0 := by
      rw [hlam0def]
      exact hd.lambda_antitone hD harg
    have hm0_nonneg : 0 ≤ 50 * Real.exp (hd.C * (20 * lam0)) := by positivity
    have hmul :=
      mul_le_mul_of_nonneg_left hrle0 hm0_nonneg
    have h0 :
        (50 * Real.exp (hd.C * (20 * lam0))) * lam0 ≤ vc.r0 := by
      rw [hlam0def]
      exact hlam0r0
    exact hmul.trans h0
  have hmul := vc.ballMult (50 * Real.exp (hd.C * (20 * lam0))) (L.φ k)
    (centers := fun b : ULift.{u} {β // β ∈ J} => yf b.down)
    (r := hd.lambda D (dist xα (X.obj (L.φ k)).basepoint + 10 * lam0)) hr0 hcapr
    (fun b c hbc => by
      rw [hvc, ← ProperMetricOn.dist_eq hd hre P (L.φ k)]
      exact hsep b.down c.down fun h => hbc (ULift.down_injective h))
    xα Finset.univ
    (fun b _ => by
      rw [hvc, ← ProperMetricOn.dist_eq hd hre P (L.φ k)]
      exact hcont b.down)
  rwa [Finset.card_univ, Fintype.card_ulift, Fintype.card_coe] at hmul









omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem exists_stableNetData (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData hd D P,
      ∀ α β : Nat,
        (∀ᶠ k in atTop, BInter hd D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter hd D P L.lamInf α β (L.φ k)) := by
  obtain ⟨L0⟩ := exists_netLimitData hd hD P
  obtain ⟨L, hLr, hstab⟩ := exists_stableNet hd P L0
  have hlam : L0.lamInf = L.lamInf := by
    funext γ
    unfold NetLimitData.lamInf
    rw [hLr]
  rw [hlam] at hstab
  exact ⟨L, hstab⟩

end HCGCompactness
end DifferentialGeometry
