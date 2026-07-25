import DifferentialGeometry.Analysis.Calculus.MapConvergenceDeriv
import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false










noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace Analysis

open HCGCompactness



theorem approx_of_fderiv_le
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {f : E → F} {A : E →L[Real] F} {s : Set E} {c : NNReal}
    (hf : ∀ x ∈ s, DifferentiableAt Real f x)
    (hderiv : ∀ x ∈ s, ‖fderiv Real f x - A‖ ≤ (c : Real))
    (hs : Convex Real s) :
    ApproximatesLinearOn f A s c := by
  intro x hx y hy
  exact hs.norm_image_sub_le_of_norm_fderiv_le'
    (x := y) (y := x) hf hderiv hy hx



theorem exists_eq_of_fderiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {f : E → F} {A : E ≃L[Real] F} {a : E} {r : Real} {c : NNReal} {y : F}
    (hf : ∀ x ∈ Metric.closedBall a r, DifferentiableAt Real f x)
    (hderiv : ∀ x ∈ Metric.closedBall a r,
      ‖fderiv Real f x - (A : E →L[Real] F)‖ ≤ (c : Real))
    (hr : 0 ≤ r)
    (hy : y ∈ Metric.closedBall (f a)
      (((A.toNonlinearRightInverse.nnnorm : Real)⁻¹ - (c : Real)) * r)) :
    ∃ x ∈ Metric.closedBall a r, f x = y := by
  have happ : ApproximatesLinearOn f (A : E →L[Real] F)
      (Metric.closedBall a r) c :=
    approx_of_fderiv_le hf hderiv (convex_closedBall a r)
  exact happ.surjOn_closedBall_of_nonlinearRightInverse
    A.toNonlinearRightInverse hr Subset.rfl hy



theorem exists_preim_tail
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    {D : Set E} (hD : IsOpen D)
    {H : Nat → E → F} {HInf : E → F}
    (hH : ∀ n, ContDiffOn Real ∞ (H n) D)
    (hHInf : ContDiffOn Real ∞ HInf D)
    (hconv : MapCInfConvOnCompacts D H HInf)
    {z₀ : E} (hz₀ : z₀ ∈ D)
    {A : E ≃L[Real] F}
    (hstrict : HasStrictFDerivAt HInf (A : E →L[Real] F) z₀)
    {R : Real} (hR : 0 < R) :
    ∃ r δ : Real, 0 < r ∧ r < R ∧ 0 < δ ∧
      ∃ N : Nat, ∀ n ≥ N,
        Set.InjOn (H n) (Metric.closedBall z₀ r) ∧
        ∀ y ∈ Metric.closedBall (HInf z₀) δ,
          ∃ z ∈ Metric.closedBall z₀ r, H n z = y := by
  classical
  by_cases hsub : Subsingleton E
  · letI : Subsingleton E := hsub
    letI : Subsingleton F := A.toEquiv.symm.subsingleton
    refine ⟨R / 2, 1, by linarith, by linarith, by norm_num, 0, ?_⟩
    intro n hn
    refine ⟨fun x hx y hy hxy => Subsingleton.elim x y, ?_⟩
    intro y hy
    refine ⟨z₀, ?_, Subsingleton.elim _ _⟩
    exact Metric.mem_closedBall_self (by linarith)
  · have hnorm : 0 < ‖(A.symm : F →L[Real] E)‖₊ :=
      A.subsingleton_or_nnnorm_symm_pos.resolve_left hsub
    let invN : NNReal := ‖(A.symm : F →L[Real] E)‖₊⁻¹
    let C : NNReal := invN / 2
    let c : NNReal := C / 2
    have hinvN : 0 < invN := by
      dsimp only [invN]
      exact inv_pos.mpr hnorm
    have hC : 0 < C := by
      dsimp only [C]
      exact div_pos hinvN (by norm_num)
    have hc : 0 < c := by
      dsimp only [c]
      exact div_pos hC (by norm_num)
    have hC_lt : C < invN := by
      dsimp only [C]
      exact NNReal.half_lt_self (ne_of_gt hinvN)
    have hcc : c + c = C := by
      dsimp only [c]
      exact add_halves C
    obtain ⟨s, hs, happInf⟩ :=
      hstrict.approximates_deriv_on_nhds (c := c) (Or.inr hc)
    have hnbhd : s ∩ (D ∩ Metric.ball z₀ R) ∈ 𝓝 z₀ :=
      Filter.inter_mem hs
        (Filter.inter_mem (hD.mem_nhds hz₀) (Metric.ball_mem_nhds z₀ hR))
    obtain ⟨q, hq, hqsub⟩ := Metric.mem_nhds_iff.mp hnbhd
    let r : Real := min (q / 2) (R / 2)
    have hr : 0 < r := by
      dsimp only [r]
      exact lt_min (div_pos hq (by norm_num)) (div_pos hR (by norm_num))
    have hrR : r < R := by
      calc r ≤ R / 2 := min_le_right _ _
        _ < R := by linarith
    have hrq : r < q := by
      calc r ≤ q / 2 := min_le_left _ _
        _ < q := by linarith
    have hballQ : Metric.closedBall z₀ r ⊆ s ∩ (D ∩ Metric.ball z₀ R) :=
      (Metric.closedBall_subset_ball hrq).trans hqsub
    have hballS : Metric.closedBall z₀ r ⊆ s := fun z hz => (hballQ hz).1
    have hballD : Metric.closedBall z₀ r ⊆ D := fun z hz => (hballQ hz).2.1
    have happBall : ApproximatesLinearOn HInf (A : E →L[Real] F)
        (Metric.closedBall z₀ r) c :=
      happInf.mono_set hballS
    have hdfconv : MapCInfConvOnCompacts D
        (fun n z => fderiv Real (H n) z) (fun z => fderiv Real HInf z) :=
      hconv.fderivOn hD hH hHInf
    have hdfUniform : TendstoUniformlyOn
        (fun n z => fderiv Real (H n) z) (fun z => fderiv Real HInf z)
        Filter.atTop (Metric.closedBall z₀ r) :=
      tendstoUniformlyOn_of_cPConv
        (hdfconv.cPConvOn (isCompact_closedBall z₀ r) hballD 0)
    rw [Metric.tendstoUniformlyOn_iff] at hdfUniform
    have hderivEv : ∀ᶠ n in Filter.atTop,
        ∀ z ∈ Metric.closedBall z₀ r,
          dist (fderiv Real (H n) z) (fderiv Real HInf z) < (c : Real) :=
      by simpa only [dist_comm] using hdfUniform (c : Real) (by exact_mod_cast hc)
    let B := A.toNonlinearRightInverse
    let margin : Real := (B.nnnorm : Real)⁻¹ - (C : Real)
    have hC_B : C < B.nnnorm⁻¹ := by
      simpa only [B, ContinuousLinearEquiv.toNonlinearRightInverse] using hC_lt
    have hmargin : 0 < margin := by
      dsimp only [margin]
      exact sub_pos.mpr (by exact_mod_cast hC_B)
    let δ : Real := margin * r / 4
    have hδ : 0 < δ := by
      dsimp only [δ]
      positivity
    have hvalTend : Tendsto (fun n => H n z₀) Filter.atTop (𝓝 (HInf z₀)) :=
      tendsto_of_cInf hconv hz₀
    rw [Metric.tendsto_atTop] at hvalTend
    obtain ⟨Nv, hNv⟩ := hvalTend δ hδ
    have hvalEv : ∀ᶠ n in Filter.atTop, dist (H n z₀) (HInf z₀) < δ :=
      eventually_atTop.mpr ⟨Nv, hNv⟩
    have hboth := hderivEv.and hvalEv
    obtain ⟨N, hN⟩ := eventually_atTop.mp hboth
    refine ⟨r, δ, hr, hrR, hδ, N, ?_⟩
    intro n hn
    obtain ⟨hderiv, hval⟩ := hN n hn
    let g : E → F := fun z => H n z - HInf z
    have hHdiff : ∀ z ∈ Metric.closedBall z₀ r,
        DifferentiableAt Real (H n) z := by
      intro z hz
      have hzD := hballD hz
      exact ((hH n).differentiableOn (by simp) z hzD).differentiableAt
        (hD.mem_nhds hzD)
    have hInfdiff : ∀ z ∈ Metric.closedBall z₀ r,
        DifferentiableAt Real HInf z := by
      intro z hz
      have hzD := hballD hz
      exact (hHInf.differentiableOn (by simp) z hzD).differentiableAt
        (hD.mem_nhds hzD)
    have hgdiff : ∀ z ∈ Metric.closedBall z₀ r,
        DifferentiableAt Real g z := fun z hz => (hHdiff z hz).sub (hInfdiff z hz)
    have hgLip : LipschitzOnWith c g (Metric.closedBall z₀ r) := by
      apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le hgdiff
      · intro z hz
        rw [← NNReal.coe_le_coe]
        change ‖fderiv Real g z‖ ≤ (c : Real)
        rw [show fderiv Real g z =
            fderiv Real (H n) z - fderiv Real HInf z by
          exact fderiv_sub (hHdiff z hz) (hInfdiff z hz)]
        simpa only [dist_eq_norm] using (hderiv z hz).le
      · exact convex_closedBall z₀ r
    have happ : ApproximatesLinearOn (H n) (A : E →L[Real] F)
        (Metric.closedBall z₀ r) C := by
      intro x hx y hy
      have hlim := happBall x hx y hy
      have herr := hgLip.dist_le_mul x hx y hy
      rw [dist_eq_norm, dist_eq_norm] at herr
      calc
        ‖H n x - H n y - A (x - y)‖
            = ‖(HInf x - HInf y - A (x - y)) + (g x - g y)‖ := by
              congr 1
              dsimp only [g]
              abel
        _ ≤ ‖HInf x - HInf y - A (x - y)‖ + ‖g x - g y‖ := norm_add_le _ _
        _ ≤ (c : Real) * ‖x - y‖ + (c : Real) * ‖x - y‖ :=
          add_le_add hlim herr
        _ = (C : Real) * ‖x - y‖ := by
          rw [← add_mul, ← NNReal.coe_add, hcc]
    refine ⟨happ.injOn (Or.inr hC_B), ?_⟩
    intro y hy
    have hyStage : y ∈ Metric.closedBall (H n z₀) (margin * r) := by
      rw [Metric.mem_closedBall] at hy ⊢
      apply le_of_lt
      calc
        dist y (H n z₀) ≤ dist y (HInf z₀) + dist (HInf z₀) (H n z₀) :=
          dist_triangle _ _ _
        _ < δ + δ := add_lt_add_of_le_of_lt hy (by simpa only [dist_comm] using hval)
        _ < margin * r := by
          dsimp only [δ]
          nlinarith [mul_pos hmargin hr]
    have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse
      B hr.le Subset.rfl
    simpa only [margin] using hsurj hyStage



noncomputable def partialFDeriv₂
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    (F : P × X → Y) (p : P) (x : X) : X →L[Real] Y :=
  (fderiv Real F (p, x)).comp (ContinuousLinearMap.inr Real P X)



theorem partialFDeriv₂_eq
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {F : P × X → Y} {p : P} {x : X} {L : X →L[Real] Y}
    (hF : DifferentiableAt Real F (p, x))
    (hL : HasFDerivAt (fun y => F (p, y)) L x) :
    partialFDeriv₂ F p x = L := by
  have hslice := hF.hasFDerivAt.comp x
    ((hasFDerivAt_const (x := x) (c := p)).prodMk (hasFDerivAt_id x))
  exact hslice.unique hL



noncomputable def implicitRootDeriv
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    (A : (P × X) →L[Real] Y) : P →L[Real] X :=
  -((A.comp (ContinuousLinearMap.inr Real P X)).inverse.comp
    (A.comp (ContinuousLinearMap.inl Real P X)))



def implicitRootDomain
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] :
    Set ((P × X) →L[Real] Y) :=
  {A | (A.comp (ContinuousLinearMap.inr Real P X)).IsInvertible}


theorem isOpen_rootDerivDom
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] :
    IsOpen (implicitRootDomain (P := P) (X := X) (Y := Y)) := by
  let restrictRoot : ((P × X) →L[Real] Y) →L[Real] (X →L[Real] Y) :=
    (ContinuousLinearMap.compL Real X (P × X) Y).flip
      (ContinuousLinearMap.inr Real P X)
  change IsOpen (restrictRoot ⁻¹'
    Set.range ((↑) : (X ≃L[Real] Y) → X →L[Real] Y))
  exact ContinuousLinearEquiv.isOpen.preimage restrictRoot.continuous



theorem rootDeriv_contDiffOn
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] :
    ContDiffOn Real ∞ (implicitRootDeriv (P := P) (X := X) (Y := Y))
      (implicitRootDomain (P := P) (X := X) (Y := Y)) := by
  let restrictRoot : ((P × X) →L[Real] Y) →L[Real] (X →L[Real] Y) :=
    (ContinuousLinearMap.compL Real X (P × X) Y).flip
      (ContinuousLinearMap.inr Real P X)
  let restrictParam : ((P × X) →L[Real] Y) →L[Real] (P →L[Real] Y) :=
    (ContinuousLinearMap.compL Real P (P × X) Y).flip
      (ContinuousLinearMap.inl Real P X)
  intro A hA
  have hInv : ContDiffAt Real ∞ ContinuousLinearMap.inverse (restrictRoot A) := by
    apply ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
    exact hA
  have hInvComp : ContDiffAt Real ∞
      (fun B => (restrictRoot B).inverse) A :=
    hInv.comp A restrictRoot.contDiff.contDiffAt
  have hParam : ContDiffAt Real ∞ (fun B => restrictParam B) A :=
    restrictParam.contDiff.contDiffAt
  have hComp : ContDiffWithinAt Real ∞
      (fun B => -((restrictRoot B).inverse.comp (restrictParam B)))
      (implicitRootDomain (P := P) (X := X) (Y := Y)) A :=
    (hInvComp.clm_comp hParam).neg.contDiffWithinAt
  simpa only [implicitRootDeriv, restrictRoot, restrictParam,
    ContinuousLinearMap.compL_apply] using hComp



noncomputable def pinnedRootMap
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    (F : P × X → Y) : P × X → Y × P :=
  fun z => (F z, z.1)



theorem pinnedFDeriv_inv
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {F : P × X → Y} {p : P} {x : X}
    (hF : DifferentiableAt Real F (p, x))
    (hinv : (partialFDeriv₂ F p x).IsInvertible) :
    (fderiv Real (pinnedRootMap F) (p, x)).IsInvertible := by
  let D : P × X →L[Real] Y := fderiv Real F (p, x)
  let A : X →L[Real] Y := partialFDeriv₂ F p x
  let C : P × X →L[Real] Y × P :=
    D.prod (ContinuousLinearMap.fst Real P X)
  let B : Y × P →L[Real] P × X :=
    (ContinuousLinearMap.snd Real Y P).prod
      (A.inverse.comp
        (ContinuousLinearMap.fst Real Y P -
          (D.comp (ContinuousLinearMap.inl Real P X)).comp
            (ContinuousLinearMap.snd Real Y P)))
  have hsplit (u : P) (v : X) :
      D (u, v) = D (u, 0) + D (0, v) := by
    rw [← map_add]
    congr 1
    simp
  have hA_apply (v : X) : A v = D (0, v) := by
    rfl
  have hCB : C.comp B = ContinuousLinearMap.id Real (Y × P) := by
    apply ContinuousLinearMap.ext
    rintro ⟨y, u⟩
    apply Prod.ext
    · change D (u, A.inverse (y - D (u, 0))) = y
      rw [hsplit, ← hA_apply, hinv.self_apply_inverse]
      abel
    · rfl
  have hBC : B.comp C = ContinuousLinearMap.id Real (P × X) := by
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    apply Prod.ext
    · rfl
    · change A.inverse (D (u, v) - D (u, 0)) = v
      rw [hsplit]
      have hsub : D (u, 0) + D (0, v) - D (u, 0) = D (0, v) := by abel
      rw [hsub, ← hA_apply, hinv.inverse_apply_self]
  have hderiv : fderiv Real (pinnedRootMap F) (p, x) = C := by
    exact (hF.hasFDerivAt.prodMk hasFDerivAt_fst).fderiv
  rw [hderiv]
  exact ContinuousLinearMap.IsInvertible.of_inverse hCB hBC



structure CompactRootTube
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    (D : Set (P × X)) (W₀ K : Set P)
    (FInf : P × X → Y) (PhiInf : P → X) where
  W : Set P
  rho : Real
  isOpen_W : IsOpen W
  isCompact_closure_W : IsCompact (closure W)
  K_subset_W : K ⊆ W
  closure_W_subset : closure W ⊆ W₀
  rho_pos : 0 < rho
  isOpen_domain : IsOpen D
  isOpen_ambient : IsOpen W₀
  limit_equation_smooth : ContDiffOn Real ∞ FInf D
  limit_branch_smooth : ContDiffOn Real ∞ PhiInf W₀
  limit_root : ∀ p ∈ closure W, FInf (p, PhiInf p) = 0
  tube_subset : ∀ p ∈ closure W,
    Metric.closedBall (PhiInf p) rho ⊆ Prod.mk p ⁻¹' D
  limit_unique : ∀ p ∈ closure W, ∀ x,
    dist x (PhiInf p) ≤ rho → FInf (p, x) = 0 → x = PhiInf p
  limit_root_deriv_inv : ∀ p ∈ closure W,
    (partialFDeriv₂ FInf p (PhiInf p)).IsInvertible

namespace CompactRootTube


def closedTube
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) (r : Real) : Set (P × X) :=
  (fun q : P × X => (q.1, PhiInf q.1 + q.2)) ''
    (closure T.W ×ˢ Metric.closedBall 0 r)



theorem mem_closedTube
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) {r : Real} {z : P × X} :
    z ∈ T.closedTube r ↔
      z.1 ∈ closure T.W ∧ dist z.2 (PhiInf z.1) ≤ r := by
  constructor
  · rintro ⟨⟨p, u⟩, ⟨hp, hu⟩, rfl⟩
    refine ⟨hp, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm,
      sub_zero, add_sub_cancel_left] using hu
  · rintro ⟨hp, hx⟩
    refine ⟨(z.1, z.2 - PhiInf z.1), ⟨hp, ?_⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hx
    · apply Prod.ext
      · rfl
      · change PhiInf z.1 + (z.2 - PhiInf z.1) = z.2
        rw [add_comm, sub_add_cancel]



theorem closedTube_compact
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) (r : Real) :
    IsCompact (T.closedTube r) := by
  have hPhi : ContinuousOn PhiInf (closure T.W) :=
    T.limit_branch_smooth.continuousOn.mono T.closure_W_subset
  have hmap : ContinuousOn
      (fun q : P × X => (q.1, PhiInf q.1 + q.2))
      (closure T.W ×ˢ Metric.closedBall 0 r) := by
    exact continuousOn_fst.prodMk
      ((hPhi.comp continuousOn_fst (fun q hq => hq.1)).add continuousOn_snd)
  exact (T.isCompact_closure_W.prod (isCompact_closedBall 0 r)).image_of_continuousOn hmap


theorem closedTube_subset
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) {r : Real} (hr : r ≤ T.rho) :
    T.closedTube r ⊆ D := by
  intro z hz
  obtain ⟨hp, hdist⟩ := (T.mem_closedTube).mp hz
  exact T.tube_subset z.1 hp (by
    simpa only [Metric.mem_closedBall] using hdist.trans hr)




theorem exists_domain_buffer
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) :
    ∃ (D' : Set (P × X))
        (T' : CompactRootTube D' W₀ K FInf PhiInf),
      IsCompact (closure D') ∧ closure D' ⊆ D ∧
        T'.W = T.W ∧ T'.rho = T.rho / 2 := by
  let r : Real := T.rho / 2
  have hr : 0 < r := div_pos T.rho_pos (by norm_num)
  have hrle : r ≤ T.rho := by
    dsimp only [r]
    linarith [T.rho_pos]
  have htubeD : T.closedTube r ⊆ D := T.closedTube_subset hrle
  obtain ⟨D', hD', htubeD', hD'D, hD'cpt⟩ :=
    exists_open_between_and_isCompact_closure
      (T.closedTube_compact r) T.isOpen_domain htubeD
  let T' : CompactRootTube D' W₀ K FInf PhiInf :=
    { W := T.W
      rho := r
      isOpen_W := T.isOpen_W
      isCompact_closure_W := T.isCompact_closure_W
      K_subset_W := T.K_subset_W
      closure_W_subset := T.closure_W_subset
      rho_pos := hr
      isOpen_domain := hD'
      isOpen_ambient := T.isOpen_ambient
      limit_equation_smooth :=
        T.limit_equation_smooth.mono fun z hz ↦ hD'D (subset_closure hz)
      limit_branch_smooth := T.limit_branch_smooth
      limit_root := T.limit_root
      tube_subset := by
        intro p hp x hx
        apply htubeD'
        exact T.mem_closedTube.mpr ⟨hp, by
          simpa only [Metric.mem_closedBall] using hx⟩
      limit_unique := by
        intro p hp x hx hroot
        exact T.limit_unique p hp x (hx.trans hrle) hroot
      limit_root_deriv_inv := T.limit_root_deriv_inv }
  exact ⟨D', T', hD'cpt, hD'D, rfl, rfl⟩


def closedAnnulus
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) (inner outer : Real) : Set (P × X) :=
  (fun q : P × X => (q.1, PhiInf q.1 + q.2)) ''
    (closure T.W ×ˢ (Metric.closedBall 0 outer \ Metric.ball 0 inner))



theorem mem_closedAnnulus
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {inner outer : Real} {z : P × X} :
    z ∈ T.closedAnnulus inner outer ↔
      z.1 ∈ closure T.W ∧ inner ≤ dist z.2 (PhiInf z.1) ∧
        dist z.2 (PhiInf z.1) ≤ outer := by
  constructor
  · rintro ⟨⟨p, u⟩, ⟨hp, huBall, huInner⟩, rfl⟩
    have houter : ‖u‖ ≤ outer := by
      simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using huBall
    have hinner : inner ≤ ‖u‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero, not_lt] using huInner
    simpa only [dist_eq_norm, add_sub_cancel_left] using ⟨hp, hinner, houter⟩
  · rintro ⟨hp, hinner, houter⟩
    refine ⟨(z.1, z.2 - PhiInf z.1), ⟨hp, ?_, ?_⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using houter
    · simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero, not_lt] using hinner
    · apply Prod.ext
      · rfl
      · change PhiInf z.1 + (z.2 - PhiInf z.1) = z.2
        rw [add_comm, sub_add_cancel]



theorem annulus_compact
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) (inner outer : Real) :
    IsCompact (T.closedAnnulus inner outer) := by
  have hPhi : ContinuousOn PhiInf (closure T.W) :=
    T.limit_branch_smooth.continuousOn.mono T.closure_W_subset
  have hmap : ContinuousOn
      (fun q : P × X => (q.1, PhiInf q.1 + q.2))
      (closure T.W ×ˢ (Metric.closedBall 0 outer \ Metric.ball 0 inner)) := by
    exact continuousOn_fst.prodMk
      ((hPhi.comp continuousOn_fst (fun q hq => hq.1)).add continuousOn_snd)
  exact (T.isCompact_closure_W.prod
    ((isCompact_closedBall 0 outer).diff Metric.isOpen_ball)).image_of_continuousOn hmap



theorem exists_residual_gap
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {inner : Real} (hinner : 0 < inner) :
    ∃ c : Real, 0 < c ∧ ∀ z ∈ T.closedAnnulus inner T.rho, c ≤ ‖FInf z‖ := by
  by_cases hne : (T.closedAnnulus inner T.rho).Nonempty
  · have hcompact := T.annulus_compact inner T.rho
    have hsub : T.closedAnnulus inner T.rho ⊆ D := by
      intro z hz
      obtain ⟨hp, _, hdist⟩ := (T.mem_closedAnnulus).mp hz
      exact T.tube_subset z.1 hp (by
        simpa only [Metric.mem_closedBall] using hdist)
    have hcont : ContinuousOn (fun z => ‖FInf z‖)
        (T.closedAnnulus inner T.rho) :=
      T.limit_equation_smooth.continuousOn.norm.mono hsub
    obtain ⟨z₀, hz₀, hmin⟩ := hcompact.exists_isMinOn hne hcont
    refine ⟨‖FInf z₀‖, ?_, fun z hz => (isMinOn_iff.mp hmin) z hz⟩
    rw [norm_pos_iff]
    intro hzero
    obtain ⟨hp, hdistInner, hdistOuter⟩ := (T.mem_closedAnnulus).mp hz₀
    have hzEq : z₀.2 = PhiInf z₀.1 :=
      T.limit_unique z₀.1 hp z₀.2 hdistOuter hzero
    rw [hzEq, dist_self] at hdistInner
    exact (not_lt_of_ge hdistInner) hinner
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact False.elim (hne ⟨z, hz⟩)




theorem eventually_no_root
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_conv : MapCInfConvOnCompacts D F FInf)
    {inner : Real} (hinner : 0 < inner) :
    ∀ᶠ n in Filter.atTop, ∀ z ∈ T.closedAnnulus inner T.rho, F n z ≠ 0 := by
  obtain ⟨c, hc, hgap⟩ := T.exists_residual_gap hinner
  have hcompact := T.annulus_compact inner T.rho
  have hsub : T.closedAnnulus inner T.rho ⊆ D := by
    intro z hz
    obtain ⟨hp, _, hdist⟩ := (T.mem_closedAnnulus).mp hz
    exact T.tube_subset z.1 hp (by
      simpa only [Metric.mem_closedBall] using hdist)
  have huniform : TendstoUniformlyOn F FInf Filter.atTop
      (T.closedAnnulus inner T.rho) :=
    tendstoUniformlyOn_of_cPConv (hF_conv.cPConvOn hcompact hsub 0)
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [huniform (c / 2) (by positivity)] with n hn
  intro z hz hzero
  have hclose := hn z hz
  rw [hzero, dist_zero_right] at hclose
  exact (not_lt_of_ge (hgap z hz)) (hclose.trans_le (by linarith))



theorem exists_deriv_radius
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    (hF_conv : MapCInfConvOnCompacts D F FInf) :
    ∃ eta : Real, 0 < eta ∧ eta < T.rho ∧
      (∀ z ∈ T.closedTube eta,
        (partialFDeriv₂ FInf z.1 z.2).IsInvertible) ∧
      ∀ᶠ n in Filter.atTop, ∀ z ∈ T.closedTube eta,
        (partialFDeriv₂ (F n) z.1 z.2).IsInvertible := by
  let restrictPartial : ((P × X) →L[Real] Y) →L[Real] (X →L[Real] Y) :=
    (ContinuousLinearMap.compL Real X (P × X) Y).flip
      (ContinuousLinearMap.inr Real P X)
  let partialInf : P × X → X →L[Real] Y :=
    fun z => partialFDeriv₂ FInf z.1 z.2
  have hdfInf : ContDiffOn Real 0 (fderiv Real FInf) D :=
    T.limit_equation_smooth.fderiv_of_isOpen T.isOpen_domain
      (by exact_mod_cast le_top)
  have hpartial_cont : ContinuousOn partialInf D := by
    have hcomp := restrictPartial.continuous.comp_continuousOn hdfInf.continuousOn
    simpa only [partialInf, partialFDeriv₂, restrictPartial,
      ContinuousLinearMap.compL_apply] using hcomp
  let invSet : Set (X →L[Real] Y) :=
    Set.range ((↑) : (X ≃L[Real] Y) → X →L[Real] Y)
  have hinvOpen : IsOpen invSet := ContinuousLinearEquiv.isOpen
  let good : Set (P × X) := D ∩ partialInf ⁻¹' invSet
  have hgoodOpen : IsOpen good :=
    hpartial_cont.isOpen_inter_preimage T.isOpen_domain hinvOpen
  let graphSet : Set (P × X) := T.closedTube 0
  have hgraphCompact : IsCompact graphSet := T.closedTube_compact 0
  have hgraphGood : graphSet ⊆ good := by
    intro z hz
    obtain ⟨hp, hdist⟩ := (T.mem_closedTube).mp hz
    have hzEq : z.2 = PhiInf z.1 := by
      exact dist_eq_zero.mp (le_antisymm hdist dist_nonneg)
    have hzD : z ∈ D := by
      exact T.tube_subset z.1 hp (by
        simpa only [Metric.mem_closedBall, hzEq, dist_self] using T.rho_pos.le)
    refine ⟨hzD, ?_⟩
    change partialInf z ∈ invSet
    dsimp only [partialInf]
    rw [hzEq]
    rcases T.limit_root_deriv_inv z.1 hp with ⟨e, he⟩
    exact ⟨e, he⟩
  obtain ⟨d, hd, hdsub⟩ :=
    hgraphCompact.exists_cthickening_subset_open hgoodOpen hgraphGood
  let eta : Real := min (d / 2) (T.rho / 2)
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min (div_pos hd (by norm_num)) (div_pos T.rho_pos (by norm_num))
  have heta_d : eta < d := by
    calc eta ≤ d / 2 := min_le_left _ _
      _ < d := by linarith
  have heta_rho : eta < T.rho := by
    calc eta ≤ T.rho / 2 := min_le_right _ _
      _ < T.rho := by linarith [T.rho_pos]
  have htube_thick : T.closedTube eta ⊆ Metric.cthickening d graphSet := by
    intro z hz
    obtain ⟨hp, hdist⟩ := (T.mem_closedTube).mp hz
    apply Metric.mem_cthickening_of_dist_le z (z.1, PhiInf z.1) d graphSet
    · apply (T.mem_closedTube).mpr
      exact ⟨hp, by simp⟩
    · rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact hdist.trans heta_d.le
  have hlimit_inv : ∀ z ∈ T.closedTube eta,
      (partialFDeriv₂ FInf z.1 z.2).IsInvertible := by
    intro z hz
    have hzGood := hdsub (htube_thick hz)
    rcases hzGood.2 with ⟨e, he⟩
    exact ⟨e, he⟩
  have heta_le : eta ≤ T.rho := heta_rho.le
  have htubeCompact : IsCompact (T.closedTube eta) := T.closedTube_compact eta
  have htubeD : T.closedTube eta ⊆ D := T.closedTube_subset heta_le
  have hdf_conv : MapCInfConvOnCompacts D
      (fun n z => fderiv Real (F n) z) (fun z => fderiv Real FInf z) :=
    hF_conv.fderivOn T.isOpen_domain hF_cd T.limit_equation_smooth
  have hdf_uniform : TendstoUniformlyOn
      (fun n z => fderiv Real (F n) z) (fun z => fderiv Real FInf z)
      Filter.atTop (T.closedTube eta) :=
    tendstoUniformlyOn_of_cPConv (hdf_conv.cPConvOn htubeCompact htubeD 0)
  have hpartial_image : IsCompact (partialInf '' T.closedTube eta) :=
    htubeCompact.image_of_continuousOn (hpartial_cont.mono htubeD)
  have hpartial_image_inv : partialInf '' T.closedTube eta ⊆ invSet := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hlimit_inv z hz with ⟨e, he⟩
    exact ⟨e, he⟩
  obtain ⟨delta, hdelta, hdeltaball⟩ :=
    hpartial_image.exists_cthickening_subset_open hinvOpen hpartial_image_inv
  refine ⟨eta, heta, heta_rho, hlimit_inv, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hdf_uniform
  filter_upwards [hdf_uniform (delta / (‖restrictPartial‖ + 1)) (by positivity)] with n hn
  intro z hz
  have hcloseDeriv := hn z hz
  have hclosePartial :
      dist (partialInf z) (partialFDeriv₂ (F n) z.1 z.2) < delta := by
    have hbound := restrictPartial.lipschitz.dist_le_mul
      (fderiv Real FInf z) (fderiv Real (F n) z)
    calc
      dist (partialInf z) (partialFDeriv₂ (F n) z.1 z.2)
          ≤ ‖restrictPartial‖ *
              dist (fderiv Real FInf z) (fderiv Real (F n) z) := by
            simpa only [partialInf, partialFDeriv₂, restrictPartial,
              ContinuousLinearMap.compL_apply] using hbound
      _ ≤ ‖restrictPartial‖ * (delta / (‖restrictPartial‖ + 1)) :=
        mul_le_mul_of_nonneg_left hcloseDeriv.le (norm_nonneg restrictPartial)
      _ < delta := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg restrictPartial, hdelta]
  have hmem : partialFDeriv₂ (F n) z.1 z.2 ∈
      Metric.cthickening delta (partialInf '' T.closedTube eta) := by
    apply Metric.mem_cthickening_of_dist_le _ (partialInf z) delta _
    · exact ⟨z, hz, rfl⟩
    · simpa only [dist_comm] using hclosePartial.le
  rcases hdeltaball hmem with ⟨e, he⟩
  exact ⟨e, he⟩



theorem exists_root_buffer
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    (hF_conv : MapCInfConvOnCompacts D F FInf)
    {inner : Real} (hinner : 0 < inner) :
    ∃ b : Real, 0 < b ∧ b < inner ∧
      ∃ N : Nat, ∀ n ≥ N,
        (∀ p ∈ closure T.W, ∃ x,
          dist x (PhiInf p) < inner ∧ F n (p, x) = 0) ∧
        ∀ p ∈ closure T.W,
          Set.InjOn (fun x => F n (p, x)) (Metric.ball (PhiInf p) b) := by
  classical
  let H : Nat → P × X → Y × P := fun n => pinnedRootMap (F n)
  let HInf : P × X → Y × P := pinnedRootMap FInf
  have hH_cd : ∀ n, ContDiffOn Real ∞ (H n) D := by
    intro n
    simpa only [H, pinnedRootMap] using
      (hF_cd n).prodMk contDiff_fst.contDiffOn
  have hHInf_cd : ContDiffOn Real ∞ HInf D := by
    simpa only [HInf, pinnedRootMap] using
      T.limit_equation_smooth.prodMk contDiff_fst.contDiffOn
  have hH_conv : MapCInfConvOnCompacts D H HInf := by
    simpa only [H, HInf, pinnedRootMap] using
      mapCInfConv_prodMk T.isOpen_domain hF_conv
        (mapCInfConv_const (U := D) (fun z : P × X => z.1))
        hF_cd T.limit_equation_smooth
        (fun _ => contDiff_fst.contDiffOn) contDiff_fst.contDiffOn
  have hlocal : ∀ p ∈ closure T.W,
      ∃ (U : Set P) (b : Real) (N : Nat),
        IsOpen U ∧ p ∈ U ∧ 0 < b ∧ b < inner ∧
        ∀ n ≥ N,
          (∀ q ∈ closure T.W, q ∈ U → ∃ x,
            dist x (PhiInf q) < inner ∧ F n (q, x) = 0) ∧
          ∀ q ∈ closure T.W, q ∈ U →
            Set.InjOn (fun x => F n (q, x))
              (Metric.ball (PhiInf q) b) := by
    intro p hp
    let z₀ : P × X := (p, PhiInf p)
    have hz₀D : z₀ ∈ D := by
      exact T.tube_subset p hp (by
        simpa only [Metric.mem_closedBall, dist_self] using T.rho_pos.le)
    have hFdiff : DifferentiableAt Real FInf z₀ :=
      (T.limit_equation_smooth.contDiffAt
        (T.isOpen_domain.mem_nhds hz₀D)).differentiableAt (by simp)
    have hpinv : (fderiv Real HInf z₀).IsInvertible := by
      simpa only [HInf, z₀] using
        pinnedFDeriv_inv hFdiff (T.limit_root_deriv_inv p hp)
    obtain ⟨A, hA⟩ := hpinv
    have hstrict₀ : HasStrictFDerivAt HInf (fderiv Real HInf z₀) z₀ :=
      (hHInf_cd.contDiffAt (T.isOpen_domain.mem_nhds hz₀D)).hasStrictFDerivAt
        (by simp)
    have hstrict : HasStrictFDerivAt HInf (A : (P × X) →L[Real] (Y × P)) z₀ := by
      rw [hA]
      exact hstrict₀
    let R : Real := min (inner / 4) (T.rho / 4)
    have hR : 0 < R := by
      dsimp only [R]
      exact lt_min (div_pos hinner (by norm_num))
        (div_pos T.rho_pos (by norm_num))
    obtain ⟨r, δ, hr, hrR, hδ, N, hN⟩ :=
      exists_preim_tail T.isOpen_domain hH_cd hHInf_cd hH_conv hz₀D hstrict hR
    let phiTol : Real := min (r / 8) (inner / 4)
    have hphiTol : 0 < phiTol := by
      dsimp only [phiTol]
      exact lt_min (div_pos hr (by norm_num)) (div_pos hinner (by norm_num))
    have hPhiCont : ContinuousAt PhiInf p :=
      T.limit_branch_smooth.continuousOn.continuousAt
        (T.isOpen_ambient.mem_nhds (T.closure_W_subset hp))
    obtain ⟨eps, heps, hPhiClose⟩ :=
      Metric.continuousAt_iff.mp hPhiCont phiTol hphiTol
    let uRad : Real := min (δ / 2) (min (r / 8) eps)
    have huRad : 0 < uRad := by
      dsimp only [uRad]
      exact lt_min (div_pos hδ (by norm_num))
        (lt_min (div_pos hr (by norm_num)) heps)
    let U : Set P := Metric.ball p uRad
    have hR_inner : R ≤ inner / 4 := min_le_left _ _
    have hr_inner : r < inner / 4 := hrR.trans_le hR_inner
    refine ⟨U, r / 4, N, Metric.isOpen_ball, Metric.mem_ball_self huRad,
      div_pos hr (by norm_num), by linarith, ?_⟩
    intro n hn
    obtain ⟨hInj, hSurj⟩ := hN n hn
    have hHInf_z₀ : HInf z₀ = (0, p) := by
      simp only [HInf, pinnedRootMap, z₀, T.limit_root p hp]
    refine ⟨?_, ?_⟩
    · intro q hq hqU
      have hqp : dist q p < uRad := by
        simpa only [U, Metric.mem_ball] using hqU
      have hqδ : dist q p < δ := by
        calc dist q p < uRad := hqp
          _ ≤ δ / 2 := min_le_left _ _
          _ < δ := by linarith
      have hqr : dist q p < r / 8 := by
        calc dist q p < uRad := hqp
          _ ≤ min (r / 8) eps := min_le_right _ _
          _ ≤ r / 8 := min_le_left _ _
      have hqeps : dist q p < eps := by
        calc dist q p < uRad := hqp
          _ ≤ min (r / 8) eps := min_le_right _ _
          _ ≤ eps := min_le_right _ _
      have hPhi := hPhiClose hqeps
      have htarget : (0, q) ∈ Metric.closedBall (HInf z₀) δ := by
        rw [hHInf_z₀, Metric.mem_closedBall, Prod.dist_eq, dist_self,
          max_eq_right dist_nonneg]
        exact hqδ.le
      obtain ⟨z, hzball, hzeq⟩ := hSurj (0, q) htarget
      have hzq : z.1 = q := congrArg Prod.snd hzeq
      have hz2p : dist z.2 (PhiInf p) ≤ r := by
        have hzdist := Metric.mem_closedBall.mp hzball
        rw [Prod.dist_eq] at hzdist
        exact (le_max_right _ _).trans hzdist
      refine ⟨z.2, ?_, ?_⟩
      · calc
          dist z.2 (PhiInf q) ≤
              dist z.2 (PhiInf p) + dist (PhiInf p) (PhiInf q) :=
            dist_triangle _ _ _
          _ < r + phiTol := add_lt_add_of_le_of_lt hz2p (by
            simpa only [dist_comm] using hPhi)
          _ < inner := by
            have htol : phiTol ≤ inner / 4 := min_le_right _ _
            linarith
      · have hzero := congrArg Prod.fst hzeq
        have hzpair : z = (q, z.2) := by
          apply Prod.ext
          · exact hzq
          · rfl
        change F n z = 0 at hzero
        rw [hzpair] at hzero
        exact hzero
    · intro q hq hqU
      have hqp : dist q p < uRad := by
        simpa only [U, Metric.mem_ball] using hqU
      have hqr : dist q p < r / 8 := by
        calc dist q p < uRad := hqp
          _ ≤ min (r / 8) eps := min_le_right _ _
          _ ≤ r / 8 := min_le_left _ _
      have hqeps : dist q p < eps := by
        calc dist q p < uRad := hqp
          _ ≤ min (r / 8) eps := min_le_right _ _
          _ ≤ eps := min_le_right _ _
      have hPhi := hPhiClose hqeps
      have hpair_mem : ∀ x ∈ Metric.ball (PhiInf q) (r / 4),
          (q, x) ∈ Metric.closedBall z₀ r := by
        intro x hx
        rw [Metric.mem_closedBall, Prod.dist_eq]
        apply max_le
        · exact hqr.le.trans (by linarith)
        · apply le_of_lt
          calc
            dist x (PhiInf p) ≤
                dist x (PhiInf q) + dist (PhiInf q) (PhiInf p) :=
              dist_triangle _ _ _
            _ < r / 4 + phiTol := add_lt_add (Metric.mem_ball.mp hx) hPhi
            _ ≤ r := by
              have htol : phiTol ≤ r / 8 := min_le_left _ _
              linarith
      intro x hx y hy hxy
      have hpairs : H n (q, x) = H n (q, y) := by
        apply Prod.ext
        · simpa only [H, pinnedRootMap] using hxy
        · rfl
      exact congrArg Prod.snd (hInj (hpair_mem x hx) (hpair_mem y hy) hpairs)
  have hlocal' : ∀ p : {p // p ∈ closure T.W},
      ∃ (U : Set P) (b : Real) (N : Nat),
        IsOpen U ∧ p.1 ∈ U ∧ 0 < b ∧ b < inner ∧
        ∀ n ≥ N,
          (∀ q ∈ closure T.W, q ∈ U → ∃ x,
            dist x (PhiInf q) < inner ∧ F n (q, x) = 0) ∧
          ∀ q ∈ closure T.W, q ∈ U →
            Set.InjOn (fun x => F n (q, x))
              (Metric.ball (PhiInf q) b) :=
    fun p => hlocal p.1 p.2
  choose U b N hUopen hpU hbpos hbinner htail using hlocal'
  have hcover : closure T.W ⊆ ⋃ p : {p // p ∈ closure T.W}, U p := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hpU ⟨p, hp⟩⟩
  obtain ⟨sf, hsf⟩ :=
    T.isCompact_closure_W.elim_finite_subcover U hUopen hcover
  let b₀ : Real := if h : sf.Nonempty then sf.inf' h b else 1
  have hb₀ : 0 < b₀ := by
    rw [show b₀ = if h : sf.Nonempty then sf.inf' h b else 1 by rfl]
    split
    · next h => rw [Finset.lt_inf'_iff]; exact fun p _ => hbpos p
    · exact one_pos
  let bMin : Real := min b₀ (inner / 2)
  have hbMin : 0 < bMin := by
    dsimp only [bMin]
    exact lt_min hb₀ (div_pos hinner (by norm_num))
  have hbMin_inner : bMin < inner := by
    calc bMin ≤ inner / 2 := min_le_right _ _
      _ < inner := by linarith
  let Nmax : Nat := sf.sup N
  refine ⟨bMin, hbMin, hbMin_inner, Nmax, ?_⟩
  intro n hn
  refine ⟨?_, ?_⟩
  · intro q hq
    have hqcover := hsf hq
    rw [Set.mem_iUnion₂] at hqcover
    obtain ⟨p, hpSf, hqU⟩ := hqcover
    have hpN : N p ≤ Nmax := by
      exact Finset.le_sup (f := N) hpSf
    exact (htail p n (hpN.trans hn)).1 q hq hqU
  · intro q hq
    have hqcover := hsf hq
    rw [Set.mem_iUnion₂] at hqcover
    obtain ⟨p, hpSf, hqU⟩ := hqcover
    have hpN : N p ≤ Nmax := by
      exact Finset.le_sup (f := N) hpSf
    have hlocalInj := (htail p n (hpN.trans hn)).2 q hq hqU
    apply hlocalInj.mono
    apply Metric.ball_subset_ball
    have hbMin_b₀ : bMin ≤ b₀ := min_le_left _ _
    have hb₀_b : b₀ ≤ b p := by
      rw [show b₀ = if h : sf.Nonempty then sf.inf' h b else 1 by rfl]
      split
      · next h => exact Finset.inf'_le _ hpSf
      · next h => exact absurd ⟨p, hpSf⟩ h
    exact hbMin_b₀.trans hb₀_b




theorem exists_root_c0
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    (hF_conv : MapCInfConvOnCompacts D F FInf) :
    ∃ N : Nat, ∃ Phi : Nat → P → X,
      TendstoUniformlyOn Phi PhiInf Filter.atTop (closure T.W) ∧
      (∀ n ≥ N, ∀ p ∈ closure T.W,
        dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
        F n (p, Phi n p) = 0 ∧
        (partialFDeriv₂ (F n) p (Phi n p)).IsInvertible) ∧
      ∀ n ≥ N, ∀ p ∈ closure T.W, ∀ x,
        dist x (PhiInf p) < T.rho →
          (F n (p, x) = 0 ↔ x = Phi n p) := by
  classical
  obtain ⟨eta, heta, hetaRho, hlimitInv, hstageInv⟩ :=
    T.exists_deriv_radius hF_cd hF_conv
  let inner : Real := min (eta / 2) (T.rho / 4)
  have hinner : 0 < inner := by
    dsimp only [inner]
    exact lt_min (div_pos heta (by norm_num))
      (div_pos T.rho_pos (by norm_num))
  have hinner_eta : inner < eta := by
    calc inner ≤ eta / 2 := min_le_left _ _
      _ < eta := by linarith
  have hinner_rho : inner < T.rho := by
    calc inner ≤ T.rho / 4 := min_le_right _ _
      _ < T.rho := by linarith [T.rho_pos]
  obtain ⟨b, hb, hbInner, Nroot, hroot⟩ :=
    T.exists_root_buffer hF_cd hF_conv hinner
  let Phi : Nat → P → X := fun n p =>
    if h : Nroot ≤ n ∧ p ∈ closure T.W then
      Classical.choose ((hroot n h.1).1 p h.2)
    else PhiInf p
  have hPhiSpec : ∀ n ≥ Nroot, ∀ p ∈ closure T.W,
      dist (Phi n p) (PhiInf p) < inner ∧ F n (p, Phi n p) = 0 := by
    intro n hn p hp
    dsimp only [Phi]
    rw [dif_pos ⟨hn, hp⟩]
    exact Classical.choose_spec ((hroot n hn).1 p hp)
  have hPhiConv : TendstoUniformlyOn Phi PhiInf Filter.atTop (closure T.W) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    let a : Real := min (eps / 2) (inner / 2)
    have ha : 0 < a := by
      dsimp only [a]
      exact lt_min (div_pos heps (by norm_num)) (div_pos hinner (by norm_num))
    have hno := T.eventually_no_root hF_conv ha
    filter_upwards [eventually_ge_atTop Nroot, hno] with n hn hnoN
    intro p hp
    obtain ⟨hPhiDist, hPhiRoot⟩ := hPhiSpec n hn p hp
    have hsmall : dist (Phi n p) (PhiInf p) < a := by
      by_contra hnot
      have hge : a ≤ dist (Phi n p) (PhiInf p) := le_of_not_gt hnot
      have hAnn : (p, Phi n p) ∈ T.closedAnnulus a T.rho := by
        apply (T.mem_closedAnnulus).mpr
        exact ⟨hp, hge, hPhiDist.le.trans hinner_rho.le⟩
      exact (hnoN (p, Phi n p) hAnn) hPhiRoot
    have haeps : a ≤ eps := by
      calc a ≤ eps / 2 := min_le_left _ _
        _ ≤ eps := by linarith
    simpa only [dist_comm] using hsmall.trans_le haeps
  obtain ⟨Ninv, hNinv⟩ := eventually_atTop.mp hstageInv
  have hnoOuter := T.eventually_no_root hF_conv
    (inner := b / 2) (div_pos hb (by norm_num))
  obtain ⟨Nouter, hNouter⟩ := eventually_atTop.mp hnoOuter
  let N : Nat := max Nroot (max Ninv Nouter)
  refine ⟨N, Phi, hPhiConv, ?_, ?_⟩
  · intro n hn p hp
    have hnRoot : Nroot ≤ n := by
      dsimp only [N] at hn
      omega
    have hnInv : Ninv ≤ n := by
      dsimp only [N] at hn
      omega
    obtain ⟨hPhiDist, hPhiRoot⟩ := hPhiSpec n hnRoot p hp
    have hPhiRho : dist (Phi n p) (PhiInf p) < T.rho / 2 := by
      calc dist (Phi n p) (PhiInf p) < inner := hPhiDist
        _ ≤ T.rho / 4 := min_le_right _ _
        _ < T.rho / 2 := by linarith [T.rho_pos]
    refine ⟨hPhiRho, hPhiRoot, ?_⟩
    apply hNinv n hnInv (p, Phi n p)
    apply (T.mem_closedTube).mpr
    exact ⟨hp, hPhiDist.le.trans hinner_eta.le⟩
  · intro n hn p hp x hxRho
    have hnRoot : Nroot ≤ n := by
      dsimp only [N] at hn
      omega
    have hnOuter : Nouter ≤ n := by
      dsimp only [N] at hn
      omega
    obtain ⟨hPhiDist, hPhiRoot⟩ := hPhiSpec n hnRoot p hp
    have hroot_small : ∀ y,
        dist y (PhiInf p) < T.rho → F n (p, y) = 0 →
          dist y (PhiInf p) < b / 2 := by
      intro y hyRho hyRoot
      by_contra hnot
      have hge : b / 2 ≤ dist y (PhiInf p) := le_of_not_gt hnot
      have hAnn : (p, y) ∈ T.closedAnnulus (b / 2) T.rho := by
        apply (T.mem_closedAnnulus).mpr
        exact ⟨hp, hge, hyRho.le⟩
      exact (hNouter n hnOuter (p, y) hAnn) hyRoot
    have hPhiRho : dist (Phi n p) (PhiInf p) < T.rho :=
      hPhiDist.trans hinner_rho
    have hPhiSmall := hroot_small (Phi n p) hPhiRho hPhiRoot
    constructor
    · intro hxRoot
      have hxSmall := hroot_small x hxRho hxRoot
      have hinj := (hroot n hnRoot).2 p hp
      apply hinj
      · exact Metric.mem_ball.mpr (hxSmall.trans (half_lt_self hb))
      · exact Metric.mem_ball.mpr (hPhiSmall.trans (half_lt_self hb))
      · exact hxRoot.trans hPhiRoot.symm
    · rintro rfl
      exact hPhiRoot



theorem root_contDiffOn
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    {N : Nat} {Phi : Nat → P → X}
    (hspec : ∀ n ≥ N, ∀ p ∈ closure T.W,
      dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
      F n (p, Phi n p) = 0 ∧
      (partialFDeriv₂ (F n) p (Phi n p)).IsInvertible)
    (huniq : ∀ n ≥ N, ∀ p ∈ closure T.W, ∀ x,
      dist x (PhiInf p) < T.rho →
        (F n (p, x) = 0 ↔ x = Phi n p)) :
    ∀ n ≥ N, ContDiffOn Real ∞ (Phi n) T.W := by
  intro n hn p hp
  have hpClosure : p ∈ closure T.W := subset_closure hp
  obtain ⟨hPhiDist, hPhiRoot, hPhiInv⟩ := hspec n hn p hpClosure
  have hzD : (p, Phi n p) ∈ D := by
    apply T.tube_subset p hpClosure
    rw [Metric.mem_closedBall]
    exact hPhiDist.le.trans (by linarith [T.rho_pos])
  let cdf : ContDiffAt Real ∞ (F n) (p, Phi n p) :=
    (hF_cd n).contDiffAt (T.isOpen_domain.mem_nhds hzD)
  have htop : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv : ((fderiv Real (F n) (p, Phi n p)).comp
      (ContinuousLinearMap.inr Real P X)).IsInvertible := by
    simpa only [partialFDeriv₂] using hPhiInv
  let psi : P → X := cdf.implicitFunction htop hinv
  have hpsiSelf : psi p = Phi n p := by
    simpa only [psi] using cdf.implicitFunction_apply_self htop hinv
  have hpsiCD : ContDiffAt Real ∞ psi p := by
    simpa only [psi] using cdf.contDiffAt_implicitFunction htop hinv
  have hpsiRoot : ∀ᶠ q in 𝓝 p, F n (q, psi q) = 0 := by
    have h := cdf.eventually_apply_implicitFunction htop hinv
    filter_upwards [h] with q hq
    exact hq.trans hPhiRoot
  have hPhiInfCont : ContinuousAt PhiInf p :=
    T.limit_branch_smooth.continuousOn.continuousAt
      (T.isOpen_ambient.mem_nhds (T.closure_W_subset hpClosure))
  have hdistCont : ContinuousAt (fun q => dist (psi q) (PhiInf q)) p :=
    hpsiCD.continuousAt.dist hPhiInfCont
  have hdistBase : dist (psi p) (PhiInf p) < T.rho := by
    rw [hpsiSelf]
    exact hPhiDist.trans (half_lt_self T.rho_pos)
  have hdistEv : ∀ᶠ q in 𝓝 p, dist (psi q) (PhiInf q) < T.rho :=
    hdistCont (Iio_mem_nhds hdistBase)
  have hWEv : ∀ᶠ q in 𝓝 p, q ∈ T.W := T.isOpen_W.mem_nhds hp
  have heq : Phi n =ᶠ[𝓝 p] psi := by
    filter_upwards [hpsiRoot, hdistEv, hWEv] with q hqRoot hqDist hqW
    exact ((huniq n hn q (subset_closure hqW) (psi q) hqDist).mp hqRoot).symm
  exact (hpsiCD.congr_of_eventuallyEq heq).contDiffWithinAt



theorem root_fderiv_eq
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    {N : Nat} {Phi : Nat → P → X}
    (hspec : ∀ n ≥ N, ∀ p ∈ closure T.W,
      dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
      F n (p, Phi n p) = 0 ∧
      (partialFDeriv₂ (F n) p (Phi n p)).IsInvertible)
    (huniq : ∀ n ≥ N, ∀ p ∈ closure T.W, ∀ x,
      dist x (PhiInf p) < T.rho →
        (F n (p, x) = 0 ↔ x = Phi n p)) :
    ∀ n ≥ N, ∀ p ∈ T.W,
      fderiv Real (Phi n) p =
        implicitRootDeriv (fderiv Real (F n) (p, Phi n p)) := by
  intro n hn p hp
  have hpClosure : p ∈ closure T.W := subset_closure hp
  obtain ⟨hPhiDist, hPhiRoot, hPhiInv⟩ := hspec n hn p hpClosure
  have hzD : (p, Phi n p) ∈ D := by
    apply T.tube_subset p hpClosure
    rw [Metric.mem_closedBall]
    exact hPhiDist.le.trans (by linarith [T.rho_pos])
  let cdf : ContDiffAt Real ∞ (F n) (p, Phi n p) :=
    (hF_cd n).contDiffAt (T.isOpen_domain.mem_nhds hzD)
  have htop : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv : ((fderiv Real (F n) (p, Phi n p)).comp
      (ContinuousLinearMap.inr Real P X)).IsInvertible := by
    simpa only [partialFDeriv₂] using hPhiInv
  let psi : P → X := cdf.implicitFunction htop hinv
  have hpsiSelf : psi p = Phi n p := by
    simpa only [psi] using cdf.implicitFunction_apply_self htop hinv
  have hpsiCD : ContDiffAt Real ∞ psi p := by
    simpa only [psi] using cdf.contDiffAt_implicitFunction htop hinv
  have hpsiRoot : ∀ᶠ q in 𝓝 p, F n (q, psi q) = 0 := by
    have h := cdf.eventually_apply_implicitFunction htop hinv
    filter_upwards [h] with q hq
    exact hq.trans hPhiRoot
  have hPhiInfCont : ContinuousAt PhiInf p :=
    T.limit_branch_smooth.continuousOn.continuousAt
      (T.isOpen_ambient.mem_nhds (T.closure_W_subset hpClosure))
  have hdistCont : ContinuousAt (fun q => dist (psi q) (PhiInf q)) p :=
    hpsiCD.continuousAt.dist hPhiInfCont
  have hdistBase : dist (psi p) (PhiInf p) < T.rho := by
    rw [hpsiSelf]
    exact hPhiDist.trans (half_lt_self T.rho_pos)
  have hdistEv : ∀ᶠ q in 𝓝 p, dist (psi q) (PhiInf q) < T.rho :=
    hdistCont (Iio_mem_nhds hdistBase)
  have hWEv : ∀ᶠ q in 𝓝 p, q ∈ T.W := T.isOpen_W.mem_nhds hp
  have heq : Phi n =ᶠ[𝓝 p] psi := by
    filter_upwards [hpsiRoot, hdistEv, hWEv] with q hqRoot hqDist hqW
    exact ((huniq n hn q (subset_closure hqW) (psi q) hqDist).mp hqRoot).symm
  rw [heq.fderiv_eq]
  simpa only [psi, implicitRootDeriv] using
    (cdf.hasStrictFDerivAt_implicitFunction htop hinv).hasFDerivAt.fderiv


theorem limit_fderiv_eq
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf) :
    ∀ p ∈ T.W,
      fderiv Real PhiInf p =
        implicitRootDeriv (fderiv Real FInf (p, PhiInf p)) := by
  have hspec : ∀ n : Nat, n ≥ 0 → ∀ p ∈ closure T.W,
      dist (PhiInf p) (PhiInf p) < T.rho / 2 ∧
      FInf (p, PhiInf p) = 0 ∧
      (partialFDeriv₂ FInf p (PhiInf p)).IsInvertible := by
    intro n hn p hp
    exact ⟨by simpa using half_pos T.rho_pos, T.limit_root p hp,
      T.limit_root_deriv_inv p hp⟩
  have huniq : ∀ n : Nat, n ≥ 0 → ∀ p ∈ closure T.W, ∀ x,
      dist x (PhiInf p) < T.rho →
        (FInf (p, x) = 0 ↔ x = PhiInf p) := by
    intro n hn p hp x hx
    constructor
    · exact T.limit_unique p hp x hx.le
    · rintro rfl
      exact T.limit_root p hp
  exact T.root_fderiv_eq (F := fun _ : Nat => FInf)
    (fun _ => T.limit_equation_smooth) (N := 0)
    (Phi := fun _ : Nat => PhiInf) hspec huniq 0 (by omega)



theorem root_cInf
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    (hF_conv : MapCInfConvOnCompacts D F FInf)
    {Phi : Nat → P → X}
    (hPhi_conv : TendstoUniformlyOn Phi PhiInf Filter.atTop (closure T.W))
    (hPhi_cd : ∀ n, ContDiffOn Real ∞ (Phi n) T.W)
    (hspec : ∀ n, ∀ p ∈ closure T.W,
      dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
      F n (p, Phi n p) = 0 ∧
      (partialFDeriv₂ (F n) p (Phi n p)).IsInvertible)
    (huniq : ∀ n, ∀ p ∈ closure T.W, ∀ x,
      dist x (PhiInf p) < T.rho →
        (F n (p, x) = 0 ↔ x = Phi n p)) :
    MapCInfConvOnCompacts T.W Phi PhiInf := by
  intro K' hK' hK'W p
  have hPhiInf_cd : ContDiffOn Real ∞ PhiInf T.W :=
    T.limit_branch_smooth.mono fun q hq =>
      T.closure_W_subset (subset_closure hq)
  induction p with
  | zero =>
      rw [Metric.tendstoUniformlyOn_iff] at hPhi_conv
      intro eps heps
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hPhi_conv eps heps)
      refine ⟨N, fun n hn r hr q hq => ?_⟩
      have hdist := hN n hn q (subset_closure (hK'W hq))
      have hr0 : r = 0 := by omega
      subst r
      simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, dist_eq_norm,
        norm_sub_rev] using hdist.le
  | succ p ih =>
      have hId : MapCPConvOn K' p (fun _ : Nat => id) id :=
        (mapCInfConv_const (U := T.W) (id : P → P)) K' hK' hK'W p
      have hGraph : MapCPConvOn K' p
          (fun n q => (q, Phi n q)) (fun q => (q, PhiInf q)) :=
        MapCPConvOn.prodMk T.isOpen_W hK'W hId ih
          (fun _ => contDiff_id.contDiffOn) contDiff_id.contDiffOn
          hPhi_cd hPhiInf_cd
      have hGraph_cd : ∀ n, ContDiffOn Real ∞
          (fun q => (q, Phi n q)) T.W :=
        fun n => contDiff_id.contDiffOn.prodMk (hPhi_cd n)
      have hGraphInf_cd : ContDiffOn Real ∞
          (fun q => (q, PhiInf q)) T.W :=
        contDiff_id.contDiffOn.prodMk hPhiInf_cd
      have hGraph_map : ∀ n, Set.MapsTo (fun q => (q, Phi n q)) T.W D := by
        intro n q hq
        apply T.tube_subset q (subset_closure hq)
        rw [Metric.mem_closedBall]
        exact (hspec n q (subset_closure hq)).1.le.trans
          (by linarith [T.rho_pos])
      have hGraphInf_map : Set.MapsTo (fun q => (q, PhiInf q)) T.W D := by
        intro q hq
        apply T.tube_subset q (subset_closure hq)
        rw [Metric.mem_closedBall]
        simpa using T.rho_pos.le
      have hDF_conv : MapCInfConvOnCompacts D
          (fun n z => fderiv Real (F n) z)
          (fun z => fderiv Real FInf z) :=
        hF_conv.fderivOn T.isOpen_domain hF_cd T.limit_equation_smooth
      have hDF_cd : ∀ n, ContDiffOn Real ∞ (fderiv Real (F n)) D :=
        fun n => (hF_cd n).fderiv_of_isOpen T.isOpen_domain
          (by exact_mod_cast le_top)
      have hDFInf_cd : ContDiffOn Real ∞ (fderiv Real FInf) D :=
        T.limit_equation_smooth.fderiv_of_isOpen T.isOpen_domain
          (by exact_mod_cast le_top)
      have hAlong : MapCPConvOn K' p
          (fun n q => fderiv Real (F n) (q, Phi n q))
          (fun q => fderiv Real FInf (q, PhiInf q)) :=
        MapCPConvOn.comp_cInf T.isOpen_W T.isOpen_domain hK' hK'W hGraph
          hDF_conv hGraph_cd hGraphInf_cd hDF_cd hDFInf_cd
          hGraphInf_map hGraph_map
      have hAlong_cd : ∀ n, ContDiffOn Real ∞
          (fun q => fderiv Real (F n) (q, Phi n q)) T.W :=
        fun n => (hDF_cd n).comp (hGraph_cd n) (hGraph_map n)
      have hAlongInf_cd : ContDiffOn Real ∞
          (fun q => fderiv Real FInf (q, PhiInf q)) T.W :=
        hDFInf_cd.comp hGraphInf_cd hGraphInf_map
      have hAlong_dom : ∀ n, Set.MapsTo
          (fun q => fderiv Real (F n) (q, Phi n q)) T.W
          (implicitRootDomain (P := P) (X := X) (Y := Y)) := by
        intro n q hq
        change (partialFDeriv₂ (F n) q (Phi n q)).IsInvertible
        exact (hspec n q (subset_closure hq)).2.2
      have hAlongInf_dom : Set.MapsTo
          (fun q => fderiv Real FInf (q, PhiInf q)) T.W
          (implicitRootDomain (P := P) (X := X) (Y := Y)) := by
        intro q hq
        change (partialFDeriv₂ FInf q (PhiInf q)).IsInvertible
        exact T.limit_root_deriv_inv q (subset_closure hq)
      have hRhs : MapCPConvOn K' p
          (fun n q => implicitRootDeriv
            (fderiv Real (F n) (q, Phi n q)))
          (fun q => implicitRootDeriv
            (fderiv Real FInf (q, PhiInf q))) :=
        MapCPConvOn.comp_cInf T.isOpen_W
          (isOpen_rootDerivDom (P := P) (X := X) (Y := Y))
          hK' hK'W hAlong
          (mapCInfConv_const
            (U := implicitRootDomain (P := P) (X := X) (Y := Y))
            (implicitRootDeriv (P := P) (X := X) (Y := Y)))
          hAlong_cd hAlongInf_cd
          (fun _ => rootDeriv_contDiffOn (P := P) (X := X) (Y := Y))
          (rootDeriv_contDiffOn (P := P) (X := X) (Y := Y))
          hAlongInf_dom hAlong_dom
      have hFormula : ∀ n, Set.EqOn
          (fun q => fderiv Real (Phi n) q)
          (fun q => implicitRootDeriv
            (fderiv Real (F n) (q, Phi n q))) T.W := by
        intro n q hq
        exact T.root_fderiv_eq hF_cd (N := 0) (Phi := Phi)
          (fun m hm => hspec m) (fun m hm => huniq m)
          n (by omega) q hq
      have hFD : MapCPConvOn K' p
          (fun n q => fderiv Real (Phi n) q)
          (fun q => fderiv Real PhiInf q) :=
        hRhs.congr T.isOpen_W hK'W hFormula T.limit_fderiv_eq
      simpa only [Nat.succ_eq_add_one] using
        MapCPConvOn.succ_of_fderiv T.isOpen_W hK'W
          (ih.mono_order (Nat.zero_le p)) hFD
          (fun n => (hPhi_cd n).differentiableOn (by simp))
          (hPhiInf_cd.differentiableOn (by simp))



theorem exists_root_smooth
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    (hF_conv : MapCInfConvOnCompacts D F FInf) :
    ∃ N : Nat, ∃ Phi : Nat → P → X,
      TendstoUniformlyOn Phi PhiInf Filter.atTop (closure T.W) ∧
      (∀ n ≥ N, ContDiffOn Real ∞ (Phi n) T.W) ∧
      (∀ n ≥ N, ∀ p ∈ closure T.W,
        dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
        F n (p, Phi n p) = 0 ∧
        (partialFDeriv₂ (F n) p (Phi n p)).IsInvertible) ∧
      ∀ n ≥ N, ∀ p ∈ closure T.W, ∀ x,
        dist x (PhiInf p) < T.rho →
          (F n (p, x) = 0 ↔ x = Phi n p) := by
  obtain ⟨N, Phi, hconv, hspec, huniq⟩ := T.exists_root_c0 hF_cd hF_conv
  exact ⟨N, Phi, hconv, T.root_contDiffOn hF_cd hspec huniq, hspec, huniq⟩






theorem exists_root_cInf
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ n, ContDiffOn Real ∞ (F n) D)
    (hF_conv : MapCInfConvOnCompacts D F FInf) :
    ∃ N : Nat, ∃ Phi : Nat → P → X,
      MapCInfConvOnCompacts T.W Phi PhiInf ∧
      (∀ n, ContDiffOn Real ∞ (Phi n) T.W) ∧
      (∀ n ≥ N, ∀ p ∈ closure T.W,
        dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
        F n (p, Phi n p) = 0 ∧
        (partialFDeriv₂ (F n) p (Phi n p)).IsInvertible) ∧
      ∀ n ≥ N, ∀ p ∈ closure T.W, ∀ x,
        dist x (PhiInf p) < T.rho →
          (F n (p, x) = 0 ↔ x = Phi n p) := by
  obtain ⟨N, Phi₀, hconv₀, hcd₀, hspec₀, huniq₀⟩ :=
    T.exists_root_smooth hF_cd hF_conv
  let Phi : Nat → P → X := fun n =>
    if N ≤ n then Phi₀ n else PhiInf
  let F' : Nat → P × X → Y := fun n =>
    if N ≤ n then F n else FInf
  have hPhiInf_cd : ContDiffOn Real ∞ PhiInf T.W :=
    T.limit_branch_smooth.mono fun q hq =>
      T.closure_W_subset (subset_closure hq)
  have hPhi_conv : TendstoUniformlyOn Phi PhiInf Filter.atTop (closure T.W) := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv₀ ⊢
    intro eps heps
    filter_upwards [hconv₀ eps heps, eventually_ge_atTop N] with n hnConv hn
    intro q hq
    simpa only [Phi, if_pos hn] using hnConv q hq
  have hPhi_cd : ∀ n, ContDiffOn Real ∞ (Phi n) T.W := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [Phi, if_pos hn] using hcd₀ n hn
    · simpa only [Phi, if_neg hn] using hPhiInf_cd
  have hF'_cd : ∀ n, ContDiffOn Real ∞ (F' n) D := by
    intro n
    by_cases hn : N ≤ n
    · simpa only [F', if_pos hn] using hF_cd n
    · simpa only [F', if_neg hn] using T.limit_equation_smooth
  have hF'_conv : MapCInfConvOnCompacts D F' FInf := by
    apply hF_conv.congr_eventually T.isOpen_domain
    · filter_upwards [eventually_ge_atTop N] with n hn
      intro z hz
      simp only [F', if_pos hn]
    · intro z hz
      rfl
  have hspec : ∀ n, ∀ p ∈ closure T.W,
      dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
      F' n (p, Phi n p) = 0 ∧
      (partialFDeriv₂ (F' n) p (Phi n p)).IsInvertible := by
    intro n p hp
    by_cases hn : N ≤ n
    · simpa only [Phi, F', if_pos hn] using hspec₀ n hn p hp
    · have hdist : dist (PhiInf p) (PhiInf p) < T.rho / 2 := by
        simpa using half_pos T.rho_pos
      simpa only [Phi, F', if_neg hn] using
        ⟨hdist, T.limit_root p hp, T.limit_root_deriv_inv p hp⟩
  have huniq : ∀ n, ∀ p ∈ closure T.W, ∀ x,
      dist x (PhiInf p) < T.rho →
        (F' n (p, x) = 0 ↔ x = Phi n p) := by
    intro n p hp x hx
    by_cases hn : N ≤ n
    · simpa only [Phi, F', if_pos hn] using huniq₀ n hn p hp x hx
    · simp only [Phi, F', if_neg hn]
      constructor
      · exact T.limit_unique p hp x hx.le
      · rintro rfl
        exact T.limit_root p hp
  have hCInf : MapCInfConvOnCompacts T.W Phi PhiInf :=
    T.root_cInf hF'_cd hF'_conv hPhi_conv hPhi_cd hspec huniq
  refine ⟨N, Phi, hCInf, hPhi_cd, ?_, ?_⟩
  · intro n hn p hp
    simpa only [Phi, if_pos hn] using hspec₀ n hn p hp
  · intro n hn p hp x hx
    simpa only [Phi, if_pos hn] using huniq₀ n hn p hp x hx




theorem exists_cInf_tail
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    {FInf : P × X → Y} {PhiInf : P → X}
    (T : CompactRootTube D W₀ K FInf PhiInf)
    {F : Nat → P × X → Y}
    (hF_cd : ∀ᶠ n in Filter.atTop, ContDiffOn Real ∞ (F n) D)
    (hF_conv : MapCInfConvOnCompacts D F FInf) :
    ∃ N : Nat, ∃ Phi : Nat → P → X,
      MapCInfConvOnCompacts T.W Phi PhiInf ∧
      (∀ n, ContDiffOn Real ∞ (Phi n) T.W) ∧
      (∀ n ≥ N, ∀ p ∈ closure T.W,
        dist (Phi n p) (PhiInf p) < T.rho / 2 ∧
        F n (p, Phi n p) = 0 ∧
        (partialFDeriv₂ (F n) p (Phi n p)).IsInvertible) ∧
      ∀ n ≥ N, ∀ p ∈ closure T.W, ∀ x,
        dist x (PhiInf p) < T.rho →
          (F n (p, x) = 0 ↔ x = Phi n p) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hF_cd
  let F' : Nat → P × X → Y := fun n ↦
    if N₀ ≤ n then F n else FInf
  have hF'_cd : ∀ n, ContDiffOn Real ∞ (F' n) D := by
    intro n
    by_cases hn : N₀ ≤ n
    · simpa only [F', if_pos hn] using hN₀ n hn
    · simpa only [F', if_neg hn] using T.limit_equation_smooth
  have hF'_conv : MapCInfConvOnCompacts D F' FInf := by
    apply hF_conv.congr_eventually T.isOpen_domain
    · filter_upwards [eventually_ge_atTop N₀] with n hn
      intro z hz
      simp only [F', if_pos hn]
    · intro z hz
      rfl
  obtain ⟨N₁, Phi, hPhi, hPhiC, hspec, huniq⟩ :=
    T.exists_root_cInf hF'_cd hF'_conv
  let N := max N₀ N₁
  refine ⟨N, Phi, hPhi, hPhiC, ?_, ?_⟩
  · intro n hn p hp
    have hn₀ : N₀ ≤ n := (Nat.le_max_left _ _).trans hn
    have hn₁ : N₁ ≤ n := (Nat.le_max_right _ _).trans hn
    simpa only [F', if_pos hn₀] using hspec n hn₁ p hp
  · intro n hn p hp x hx
    have hn₀ : N₀ ≤ n := (Nat.le_max_left _ _).trans hn
    have hn₁ : N₁ ≤ n := (Nat.le_max_right _ _).trans hn
    simpa only [F', if_pos hn₀] using huniq n hn₁ p hp x hx

end CompactRootTube




theorem exists_compactRootTube
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {W₀ K : Set P}
    (hD : IsOpen D) (hW₀ : IsOpen W₀)
    (hK : IsCompact K) (hKW₀ : K ⊆ W₀)
    {FInf : P × X → Y} {PhiInf : P → X}
    (hFInf : ContDiffOn Real ∞ FInf D)
    (hPhiInf : ContDiffOn Real ∞ PhiInf W₀)
    (hgraph : Set.MapsTo (fun p ↦ (p, PhiInf p)) W₀ D)
    (hroot : ∀ p ∈ W₀, FInf (p, PhiInf p) = 0)
    (hinv : ∀ p ∈ K,
      (partialFDeriv₂ FInf p (PhiInf p)).IsInvertible) :
    Nonempty (CompactRootTube D W₀ K FInf PhiInf) := by
  let graph : P → P × X := fun p ↦ (p, PhiInf p)
  let H : P × X → Y × P := fun z ↦ (FInf z, z.1)
  have hgraph_cont : ContinuousOn graph W₀ := by
    exact continuousOn_id.prodMk hPhiInf.continuousOn
  let S : Set (P × X) := graph '' K
  have hScompact : IsCompact S :=
    hK.image_of_continuousOn (hgraph_cont.mono hKW₀)
  have hSinj : Set.InjOn H S := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
    have hpq' : p = q := congrArg Prod.snd hpq
    subst q
    rfl
  have hHcont : ∀ z ∈ S, ContinuousAt H z := by
    rintro _ ⟨p, hp, rfl⟩
    have hpD : graph p ∈ D := hgraph (hKW₀ hp)
    have hFcont : ContinuousAt FInf (graph p) :=
      hFInf.continuousOn.continuousAt (hD.mem_nhds hpD)
    exact hFcont.prodMk continuousAt_fst
  have hHloc : ∀ z ∈ S, ∃ u ∈ 𝓝 z, Set.InjOn H u := by
    rintro _ ⟨p, hp, rfl⟩
    have hpW₀ : p ∈ W₀ := hKW₀ hp
    have hpD : graph p ∈ D := hgraph hpW₀
    have hcd : ContDiffAt Real ∞ FInf (graph p) :=
      hFInf.contDiffAt (hD.mem_nhds hpD)
    have hstrict := hcd.hasStrictFDerivAt (by simp)
    have hinv' : ((fderiv Real FInf (graph p)).comp
        (ContinuousLinearMap.inr Real P X)).IsInvertible := by
      simpa only [partialFDeriv₂, graph] using hinv p hp
    let data := hstrict.implicitFunctionDataOfProdDomain hinv'
    let e := data.toOpenPartialHomeomorph
    have hmem : graph p ∈ e.source := by
      simpa only [data, e, graph] using
        data.pt_mem_toOpenPartialHomeomorph_source
    refine ⟨e.source, e.open_source.mem_nhds hmem, ?_⟩
    simpa only [H, e, data, ImplicitFunctionData.toOpenPartialHomeomorph_coe,
      ImplicitFunctionData.prodFun_apply,
      HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
      HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain] using e.injOn
  obtain ⟨T, hTopen, hST, hTinj⟩ :=
    Set.InjOn.exists_isOpen_superset hSinj hScompact hHcont hHloc
  let restrictPartial : ((P × X) →L[Real] Y) →L[Real] (X →L[Real] Y) :=
    (ContinuousLinearMap.compL Real X (P × X) Y).flip
      (ContinuousLinearMap.inr Real P X)
  have hdf : ContDiffOn Real 0 (fderiv Real FInf) D :=
    hFInf.fderiv_of_isOpen hD (by exact_mod_cast le_top)
  have hpartial_cont_D : ContinuousOn
      (fun z : P × X ↦ partialFDeriv₂ FInf z.1 z.2) D := by
    have hcomp := restrictPartial.continuous.comp_continuousOn hdf.continuousOn
    simpa only [partialFDeriv₂, restrictPartial,
      ContinuousLinearMap.compL_apply] using hcomp
  have hpartial_cont : ContinuousOn
      (fun p ↦ partialFDeriv₂ FInf p (PhiInf p)) W₀ := by
    exact hpartial_cont_D.comp hgraph_cont hgraph
  let invSet : Set (X →L[Real] Y) :=
    Set.range ((↑) : (X ≃L[Real] Y) → X →L[Real] Y)
  have hinvOpen : IsOpen invSet := ContinuousLinearEquiv.isOpen
  let G : Set P :=
    (W₀ ∩ graph ⁻¹' T) ∩
      (W₀ ∩ (fun p ↦ partialFDeriv₂ FInf p (PhiInf p)) ⁻¹' invSet)
  have hGopen : IsOpen G := by
    exact (hgraph_cont.isOpen_inter_preimage hW₀ hTopen).inter
      (hpartial_cont.isOpen_inter_preimage hW₀ hinvOpen)
  have hKG : K ⊆ G := by
    intro p hp
    have hpW₀ : p ∈ W₀ := hKW₀ hp
    refine ⟨⟨hpW₀, hST ⟨p, hp, rfl⟩⟩, hpW₀, ?_⟩
    rcases hinv p hp with ⟨e, he⟩
    exact ⟨e, he⟩
  obtain ⟨W, hWopen, hKW, hWG, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hGopen hKG
  have hWW₀ : closure W ⊆ W₀ := fun p hp ↦ (hWG hp).1.1
  let S' : Set (P × X) := graph '' closure W
  have hS'compact : IsCompact S' :=
    hWcompact.image_of_continuousOn (hgraph_cont.mono hWW₀)
  have hS'DT : S' ⊆ D ∩ T := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hgraph (hWW₀ hp), (hWG hp).1.2⟩
  obtain ⟨d, hd, hdsub⟩ :=
    hS'compact.exists_cthickening_subset_open (hD.inter hTopen) hS'DT
  let rho : Real := d / 2
  have hrho : 0 < rho := div_pos hd (by norm_num)
  have htube : ∀ p ∈ closure W,
      Metric.closedBall (PhiInf p) rho ⊆ Prod.mk p ⁻¹' D := by
    intro p hp x hx
    have hpair : (p, x) ∈ Metric.cthickening d S' := by
      apply Metric.mem_cthickening_of_dist_le (p, x) (graph p) d S'
      · exact ⟨p, hp, rfl⟩
      · rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        have hxrho : dist x (PhiInf p) ≤ rho := by
          simpa only [Metric.mem_closedBall] using hx
        exact hxrho.trans (by dsimp only [rho]; linarith)
    exact (hdsub hpair).1
  have hunique : ∀ p ∈ closure W, ∀ x,
      dist x (PhiInf p) ≤ rho → FInf (p, x) = 0 → x = PhiInf p := by
    intro p hp x hx hrootx
    have hxball : x ∈ Metric.closedBall (PhiInf p) rho := by
      simpa only [Metric.mem_closedBall] using hx
    have hxthick : (p, x) ∈ Metric.cthickening d S' := by
      apply Metric.mem_cthickening_of_dist_le (p, x) (graph p) d S'
      · exact ⟨p, hp, rfl⟩
      · rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact hx.trans (by dsimp only [rho]; linarith)
    have hxT : (p, x) ∈ T := (hdsub hxthick).2
    have hgraphT : graph p ∈ T := (hWG hp).1.2
    have hHeq : H (p, x) = H (graph p) := by
      dsimp only [H, graph]
      rw [hrootx, hroot p (hWW₀ hp)]
    have hpairEq := hTinj hxT hgraphT hHeq
    exact congrArg Prod.snd hpairEq
  have hderiv : ∀ p ∈ closure W,
      (partialFDeriv₂ FInf p (PhiInf p)).IsInvertible := by
    intro p hp
    rcases (hWG hp).2.2 with ⟨e, he⟩
    exact ⟨e, he⟩
  exact ⟨⟨W, rho, hWopen, hWcompact, hKW, hWW₀, hrho, hD, hW₀,
    hFInf, hPhiInf, fun p hp => hroot p (hWW₀ hp), htube, hunique, hderiv⟩⟩



theorem exists_rootTube
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [FiniteDimensional Real P]
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y] [FiniteDimensional Real Y]
    {D : Set (P × X)} {K : Set P}
    (hD : IsOpen D) (hK : IsCompact K)
    {FInf : P × X → Y} {seed : P → X}
    (hFInf : ContDiffOn Real ∞ FInf D)
    (hseed : ContinuousOn seed K)
    (hgraph : Set.MapsTo (fun p => (p, seed p)) K D)
    (hroot : ∀ p ∈ K, FInf (p, seed p) = 0)
    (hinv : ∀ p ∈ K,
      (partialFDeriv₂ FInf p (seed p)).IsInvertible) :
    ∃ (W₀ : Set P) (PhiInf : P → X),
      Set.EqOn PhiInf seed K ∧
      Nonempty (CompactRootTube D W₀ K FInf PhiInf) := by
  classical
  let graph : P → P × X := fun p => (p, seed p)
  let H : P × X → Y × P := pinnedRootMap FInf
  let S : Set (P × X) := graph '' K
  have hgraph_cont : ContinuousOn graph K :=
    continuousOn_id.prodMk hseed
  have hScompact : IsCompact S :=
    hK.image_of_continuousOn hgraph_cont
  let restrictPartial : ((P × X) →L[Real] Y) →L[Real] (X →L[Real] Y) :=
    (ContinuousLinearMap.compL Real X (P × X) Y).flip
      (ContinuousLinearMap.inr Real P X)
  have hdf : ContDiffOn Real 0 (fderiv Real FInf) D :=
    hFInf.fderiv_of_isOpen hD (by exact_mod_cast le_top)
  have hpartial : ContinuousOn
      (fun z : P × X => partialFDeriv₂ FInf z.1 z.2) D := by
    have hcomp := restrictPartial.continuous.comp_continuousOn hdf.continuousOn
    simpa only [partialFDeriv₂, restrictPartial,
      ContinuousLinearMap.compL_apply] using hcomp
  let invSet : Set (X →L[Real] Y) :=
    Set.range ((↑) : (X ≃L[Real] Y) → X →L[Real] Y)
  have hinvOpen : IsOpen invSet := ContinuousLinearEquiv.isOpen
  let G : Set (P × X) :=
    D ∩ (fun z => partialFDeriv₂ FInf z.1 z.2) ⁻¹' invSet
  have hGopen : IsOpen G :=
    hpartial.isOpen_inter_preimage hD hinvOpen
  have hSG : S ⊆ G := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨hgraph hp, ?_⟩
    change partialFDeriv₂ FInf p (seed p) ∈ invSet
    rcases hinv p hp with ⟨A, hA⟩
    exact ⟨A, hA⟩
  have hGinv : ∀ z ∈ G,
      (partialFDeriv₂ FInf z.1 z.2).IsInvertible := by
    intro z hz
    rcases hz.2 with ⟨A, hA⟩
    exact ⟨A, hA⟩
  have hH_cd : ContDiffOn Real ∞ H D := by
    simpa only [H, pinnedRootMap] using
      hFInf.prodMk contDiff_fst.contDiffOn
  have hlocalG : IsLocalHomeomorphOn H G := by
    intro z hz
    have hzD : z ∈ D := hz.1
    have hFAt : ContDiffAt Real ∞ FInf z :=
      hFInf.contDiffAt (hD.mem_nhds hzD)
    have hHAt : ContDiffAt Real ∞ H z :=
      hH_cd.contDiffAt (hD.mem_nhds hzD)
    have hHInv : (fderiv Real H z).IsInvertible := by
      simpa only [H] using
        pinnedFDeriv_inv
          (hFAt.differentiableAt (by simp)) (hGinv z hz)
    rcases hHInv with ⟨A, hA⟩
    have hHD : HasFDerivAt H
        (A : (P × X) →L[Real] (Y × P)) z := by
      rw [hA]
      exact (hHAt.differentiableAt (by simp)).hasFDerivAt
    let e := hHAt.toOpenPartialHomeomorph H hHD (by simp)
    refine ⟨e, ?_, rfl⟩
    exact hHAt.mem_toOpenPartialHomeomorph_source hHD (by simp)
  have hSinj : Set.InjOn H S := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ heq
    have hpq : p = q := by
      simpa only [H, pinnedRootMap, graph] using congrArg Prod.snd heq
    subst q
    rfl
  have hHcont : ∀ z ∈ S, ContinuousAt H z := by
    intro z hz
    exact hH_cd.continuousOn.continuousAt
      (hD.mem_nhds (hSG hz).1)
  have hHloc : ∀ z ∈ S, ∃ u ∈ 𝓝 z, Set.InjOn H u := by
    intro z hz
    obtain ⟨e, hze, he⟩ := hlocalG z (hSG hz)
    refine ⟨e.source, e.open_source.mem_nhds hze, ?_⟩
    simpa only [he] using e.injOn
  obtain ⟨T₀, hT₀open, hST₀, hT₀inj⟩ :=
    Set.InjOn.exists_isOpen_superset hSinj hScompact hHcont hHloc
  let T : Set (P × X) := T₀ ∩ G
  have hTopen : IsOpen T := hT₀open.inter hGopen
  have hST : S ⊆ T := fun z hz => ⟨hST₀ hz, hSG hz⟩
  have hTinj : Set.InjOn H T := hT₀inj.mono inter_subset_left
  have hlocalT : IsLocalHomeomorphOn H T :=
    hlocalG.mono inter_subset_right
  have hHopen : IsOpenMap (T.restrict H) := by
    intro W hW
    rw [Set.restrict_eq, Set.image_comp]
    let O : Set (P × X) := ((↑) : T → P × X) '' W
    have hOopen : IsOpen O :=
      hTopen.isOpenMap_subtype_val W hW
    have hOT : O ⊆ T := by
      rintro _ ⟨x, hx, rfl⟩
      exact x.2
    change IsOpen (H '' O)
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨x, hxO, rfl⟩ := hy
    obtain ⟨e, hxe, he⟩ := hlocalT x (hOT hxO)
    refine ⟨e '' (O ∩ e.source), ?_, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨w, hw.1, congrFun he w⟩
    · exact e.isOpen_image_of_subset_source
        (hOopen.inter e.open_source) inter_subset_right
    · exact ⟨x, ⟨hxO, hxe⟩, (congrFun he x).symm⟩
  let e : OpenPartialHomeomorph (P × X) (Y × P) :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict
      (hTinj.toPartialEquiv H T)
      hlocalT.continuousOn hHopen hTopen
  have he_source : e.source = T := by rfl
  have he_coe : (e : P × X → Y × P) = H := by rfl
  let pair : P → Y × P := fun p => (0, p)
  let W₀ : Set P := pair ⁻¹' e.target
  let PhiInf : P → X := fun p => (e.symm (pair p)).2
  have hpair_cont : Continuous pair :=
    continuous_const.prodMk continuous_id
  have hpair_cd : ContDiff Real ∞ pair :=
    contDiff_const.prodMk contDiff_id
  have hW₀open : IsOpen W₀ :=
    e.open_target.preimage hpair_cont
  have hseed_image : ∀ p ∈ K, H (graph p) = pair p := by
    intro p hp
    apply Prod.ext
    · simpa only [H, pinnedRootMap, graph, pair] using hroot p hp
    · rfl
  have hKW₀ : K ⊆ W₀ := by
    intro p hp
    have hgraphT : graph p ∈ T := hST ⟨p, hp, rfl⟩
    have hgraphSrc : graph p ∈ e.source := by
      simpa only [he_source] using hgraphT
    have hmap := e.map_source hgraphSrc
    rw [he_coe, hseed_image p hp] at hmap
    exact hmap
  have hPhiInf : ContDiffOn Real ∞ PhiInf W₀ := by
    intro p hp
    let z : P × X := e.symm (pair p)
    have hzSrc : z ∈ e.source := e.symm.map_source hp
    have hzT : z ∈ T := by
      simpa only [he_source] using hzSrc
    have hFAt : ContDiffAt Real ∞ FInf z :=
      hFInf.contDiffAt (hD.mem_nhds hzT.2.1)
    have hHAt : ContDiffAt Real ∞ H z :=
      hH_cd.contDiffAt (hD.mem_nhds hzT.2.1)
    have hHInv : (fderiv Real H z).IsInvertible := by
      simpa only [H] using
        pinnedFDeriv_inv
          (hFAt.differentiableAt (by simp)) (hGinv z hzT.2)
    rcases hHInv with ⟨A, hA⟩
    have hHD : HasFDerivAt H
        (A : (P × X) →L[Real] (Y × P)) z := by
      rw [hA]
      exact (hHAt.differentiableAt (by simp)).hasFDerivAt
    have heD : HasFDerivAt (e : P × X → Y × P)
        (A : (P × X) →L[Real] (Y × P)) z := by
      simpa only [he_coe] using hHD
    have heCD : ContDiffAt Real ∞ (e : P × X → Y × P) z := by
      simpa only [he_coe] using hHAt
    have hsymm : ContDiffAt Real ∞ e.symm (pair p) :=
      e.contDiffAt_symm hp heD heCD
    simpa only [PhiInf, z] using
      (contDiffAt_snd.comp p
        (hsymm.comp p hpair_cd.contDiffAt)).contDiffWithinAt
  have hbranch : ∀ p ∈ W₀,
      (p, PhiInf p) ∈ D ∧ FInf (p, PhiInf p) = 0 := by
    intro p hp
    let z : P × X := e.symm (pair p)
    have hzSrc : z ∈ e.source := e.symm.map_source hp
    have hzT : z ∈ T := by
      simpa only [he_source] using hzSrc
    have hright := e.right_inv hp
    rw [he_coe] at hright
    have hzRoot : FInf z = 0 := by
      simpa only [H, pinnedRootMap, pair] using congrArg Prod.fst hright
    have hzFst : z.1 = p := by
      simpa only [H, pinnedRootMap, pair] using congrArg Prod.snd hright
    have hpz : (p, PhiInf p) = z := by
      apply Prod.ext
      · exact hzFst.symm
      · rfl
    constructor
    · rw [hpz]
      exact hzT.2.1
    · rw [hpz]
      exact hzRoot
  have hEq : Set.EqOn PhiInf seed K := by
    intro p hp
    have hgraphT : graph p ∈ T := hST ⟨p, hp, rfl⟩
    have hgraphSrc : graph p ∈ e.source := by
      simpa only [he_source] using hgraphT
    have hleft := e.left_inv hgraphSrc
    rw [he_coe, hseed_image p hp] at hleft
    simpa only [PhiInf, graph] using congrArg Prod.snd hleft
  refine ⟨W₀, PhiInf, hEq, ?_⟩
  exact exists_compactRootTube
    hD hW₀open hK hKW₀ hFInf hPhiInf
    (fun p hp => (hbranch p hp).1)
    (fun p hp => (hbranch p hp).2)
    (by
      intro p hp
      rw [hEq hp]
      exact hinv p hp)

end Analysis
end DifferentialGeometry
