import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalizedAA
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Analysis.Calculus.RingInverseDeriv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false










namespace DifferentialGeometry
namespace HCGCompactness
namespace H6Isometry

open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]



theorem norm_apply_le_two
    (g : E →L[Real] E →L[Real] Real)
    (h : F →L[Real] F →L[Real] Real)
    (L : E →L[Real] F)
    (hg : forall v : E, g v v <= 2 * ‖v‖ ^ 2)
    (hh : forall w : F, (1 / 2 : Real) * ‖w‖ ^ 2 <= h w w)
    (hiso : forall v : E, h (L v) (L v) = g v v)
    (v : E) :
    ‖L v‖ <= 2 * ‖v‖ := by
  have hquad : (1 / 2 : Real) * ‖L v‖ ^ 2 <= 2 * ‖v‖ ^ 2 :=
    (hh (L v)).trans ((hiso v).trans_le (hg v))
  have hsq : ‖L v‖ ^ 2 <= (2 * ‖v‖) ^ 2 := by
    nlinarith
  exact le_of_sq_le_sq hsq (mul_nonneg (by norm_num) (norm_nonneg v))



theorem opNorm_le_two
    (g : E →L[Real] E →L[Real] Real)
    (h : F →L[Real] F →L[Real] Real)
    (L : E →L[Real] F)
    (hg : forall v : E, g v v <= 2 * ‖v‖ ^ 2)
    (hh : forall w : F, (1 / 2 : Real) * ‖w‖ ^ 2 <= h w w)
    (hiso : forall v : E, h (L v) (L v) = g v v) :
    ‖L‖ <= 2 := by
  refine ContinuousLinearMap.opNorm_le_bound L (by norm_num) ?_
  exact norm_apply_le_two g h L hg hh hiso


theorem isom_first_bound
    (B : E →L[Real] E →L[Real] Real)
    (C : F →L[Real] F →L[Real] Real) (Phi : E -> F) (x : E)
    (hB : forall v : E, B v v <= 2 * ‖v‖ ^ 2)
    (hC : forall w : F, (1 / 2 : Real) * ‖w‖ ^ 2 <= C w w)
    (hiso : forall v : E,
      C (fderiv Real Phi x v) (fderiv Real Phi x v) = B v v) :
    ‖iteratedFDeriv Real 1 Phi x‖ <= 2 := by
  rw [norm_iteratedFDeriv_one]
  exact opNorm_le_two B C (fderiv Real Phi x) hB hC hiso



theorem isom_injective
    (g : E →L[Real] E →L[Real] Real)
    (h : F →L[Real] F →L[Real] Real) (L : E →L[Real] F)
    (hg : forall v : E, (1 / 2 : Real) * ‖v‖ ^ 2 <= g v v)
    (hiso : forall v : E, h (L v) (L v) = g v v) :
    Function.Injective L := by
  intro a b hab
  have hL : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hgzero : g (a - b) (a - b) = 0 := by
    rw [← hiso, hL]
    exact map_zero (h 0)
  have hnorm : ‖a - b‖ = 0 := by
    have hle := hg (a - b)
    rw [hgzero] at hle
    nlinarith [sq_nonneg ‖a - b‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)



theorem opNorm₂_le
    (T : E →L[Real] E →L[Real] F) {C : Real} (hC : 0 <= C)
    (hT : forall u v : E, ‖T u v‖ <= C * ‖u‖ * ‖v‖) :
    ‖T‖ <= C := by
  refine ContinuousLinearMap.opNorm_le_bound T hC ?_
  intro u
  refine ContinuousLinearMap.opNorm_le_bound (T u)
    (mul_nonneg hC (norm_nonneg u)) ?_
  intro v
  simpa only [mul_assoc] using hT u v

set_option synthInstance.maxHeartbeats 800000 in


theorem isom_jet_one
    (B : E -> E →L[Real] E →L[Real] Real)
    (C : F -> F →L[Real] F →L[Real] Real)
    (Phi : E -> F) (A : E -> E →L[Real] F) {x : E}
    (DB : E →L[Real] E →L[Real] E →L[Real] Real)
    (DC : F →L[Real] F →L[Real] F →L[Real] Real)
    (L : E →L[Real] F) (DA : E →L[Real] E →L[Real] F)
    (hB : HasFDerivAt B DB x) (hC : HasFDerivAt C DC (Phi x))
    (hPhi : HasFDerivAt Phi L x) (hA : HasFDerivAt A DA x)
    (hiso : ∀ᶠ y in nhds x, forall u v : E,
      B y u v = C (Phi y) (A y u) (A y v))
    (u v w : E) :
    DB w u v =
      DC (L w) (A x u) (A x v) +
        C (Phi x) (DA w u) (A x v) +
        C (Phi x) (A x u) (DA w v) := by
  have hu : HasFDerivAt (fun _ : E => u) 0 x :=
    hasFDerivAt_const (𝕜 := Real) u x
  have hv : HasFDerivAt (fun _ : E => v) 0 x :=
    hasFDerivAt_const (𝕜 := Real) v x
  have hleft := (hB.clm_apply hu).clm_apply hv
  have hCphi_raw : HasFDerivAt (C ∘ Phi) (DC.comp L) x := by
    exact @HasFDerivAt.comp Real _ E _ _ F _ _
      (F →L[Real] F →L[Real] Real) _ _ Phi L x C DC hC hPhi
  have hCphi : HasFDerivAt (fun y : E => C (Phi y)) (DC.comp L) x := by
    simpa only [Function.comp_apply] using hCphi_raw
  have hAu := hA.clm_apply hu
  have hAv := hA.clm_apply hv
  have hright := (hCphi.clm_apply hAu).clm_apply hAv
  have hscalar :
      (fun y : E => B y u v) =ᶠ[nhds x]
        fun y => C (Phi y) (A y u) (A y v) := by
    filter_upwards [hiso] with y hy
    exact hy u v
  have hderiv := Filter.EventuallyEq.fderiv_eq (𝕜 := Real) hscalar
  rw [hleft.fderiv, hright.fderiv] at hderiv
  have hw := DFunLike.congr_fun hderiv w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add] at hw
  linear_combination hw

section LoweredJet

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

set_option linter.style.setOption false in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in



theorem lowered_jet_next
    (C : F -> F →L[Real] F →L[Real] Real)
    (Phi : E -> F) (A : E -> E →L[Real] F)
    (Q : E -> E →L[Real] E →L[Real] F)
    (KB : E -> E →L[Real] E →L[Real] E →L[Real] Real)
    (KC : F -> F →L[Real] F →L[Real] F →L[Real] Real) {x : E}
    (DC : F →L[Real] F →L[Real] F →L[Real] Real)
    (L : E →L[Real] F) (DA : E →L[Real] E →L[Real] F)
    (DQ : E →L[Real] E →L[Real] E →L[Real] F)
    (DKB : E →L[Real] E →L[Real] E →L[Real] E →L[Real] Real)
    (DKC : E →L[Real] F →L[Real] F →L[Real] F →L[Real] Real)
    (hC : HasFDerivAt C DC (Phi x)) (hPhi : HasFDerivAt Phi L x)
    (hA : HasFDerivAt A DA x) (hQ : HasFDerivAt Q DQ x)
    (hKB : HasFDerivAt KB DKB x)
    (hKC : HasFDerivAt (fun y : E => KC (Phi y)) DKC x)
    (hlow : ∀ᶠ y in nhds x, forall u v w : E,
      C (Phi y) (Q y u v) (A y w) =
        KB y u v w - KC (Phi y) (A y u) (A y v) (A y w))
    (u v w t : E) :
    C (Phi x) (DQ t u v) (A x w) =
      DKB t u v w -
        DKC t (A x u) (A x v) (A x w) -
        KC (Phi x) (DA t u) (A x v) (A x w) -
        KC (Phi x) (A x u) (DA t v) (A x w) -
        KC (Phi x) (A x u) (A x v) (DA t w) -
        DC (L t) (Q x u v) (A x w) -
        C (Phi x) (Q x u v) (DA t w) := by
  have hu : HasFDerivAt (fun _ : E => u) 0 x :=
    hasFDerivAt_const (𝕜 := Real) u x
  have hv : HasFDerivAt (fun _ : E => v) 0 x :=
    hasFDerivAt_const (𝕜 := Real) v x
  have hw : HasFDerivAt (fun _ : E => w) 0 x :=
    hasFDerivAt_const (𝕜 := Real) w x
  have hCphi_raw : HasFDerivAt (C ∘ Phi) (DC.comp L) x := by
    exact @HasFDerivAt.comp Real _ E _ _ F _ _
      (F →L[Real] F →L[Real] Real) _ _ Phi L x C DC hC hPhi
  have hCphi : HasFDerivAt (fun y : E => C (Phi y)) (DC.comp L) x := by
    simpa only [Function.comp_apply] using hCphi_raw
  have hAu := hA.clm_apply hu
  have hAv := hA.clm_apply hv
  have hAw := hA.clm_apply hw
  have hQuv := (hQ.clm_apply hu).clm_apply hv
  have hleft := (hCphi.clm_apply hQuv).clm_apply hAw
  have hKBu := HasFDerivAt.clm_apply (E := E) (G := E)
    (H := E →L[Real] E →L[Real] Real) hKB hu
  have hKBuv := HasFDerivAt.clm_apply (E := E) (G := E)
    (H := E →L[Real] Real) hKBu hv
  have hKBuvw := HasFDerivAt.clm_apply (E := E) (G := E)
    (H := Real) hKBuv hw
  have hKCu := HasFDerivAt.clm_apply (E := E) (G := F)
    (H := F →L[Real] F →L[Real] Real) hKC hAu
  have hKCuv := HasFDerivAt.clm_apply (E := E) (G := F)
    (H := F →L[Real] Real) hKCu hAv
  have hKCuvw := HasFDerivAt.clm_apply (E := E) (G := F)
    (H := Real) hKCuv hAw
  have hright := hKBuvw.sub hKCuvw
  have hscalar :
      (fun y : E => C (Phi y) (Q y u v) (A y w)) =ᶠ[nhds x]
        (fun y => KB y u v w) -
          fun y => KC (Phi y) (A y u) (A y v) (A y w) := by
    filter_upwards [hlow] with y hy
    simpa only [Pi.sub_apply] using hy u v w
  have hderiv := Filter.EventuallyEq.fderiv_eq (𝕜 := Real) hscalar
  rw [hleft.fderiv, hright.fderiv] at hderiv
  have ht := DFunLike.congr_fun hderiv t
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add] at ht
  linear_combination ht

end LoweredJet

variable {E0 F0 : Type*}
  [NormedAddCommGroup E0] [InnerProductSpace Real E0]
  [NormedAddCommGroup F0] [InnerProductSpace Real F0]



theorem lowered_norm_le
    (C : F0 →L[Real] F0 →L[Real] Real) (e : E0 ≃L[Real] F0)
    (T : F0) (R : E0 →L[Real] Real)
    (hClower : forall q : F0, (1 / 2 : Real) * ‖q‖ ^ 2 <= C q q)
    (heinv : ‖(e.symm : F0 →L[Real] E0)‖ <= 2)
    (hpair : forall w : E0, C T (e w) = R w) :
    ‖T‖ <= 4 * ‖R‖ := by
  let w : E0 := e.symm T
  have hew : e w = T := e.apply_symm_apply T
  have hRw : ‖R w‖ <= 2 * ‖R‖ * ‖T‖ := by
    calc
      ‖R w‖ <= ‖R‖ * ‖w‖ := ContinuousLinearMap.le_opNorm R w
      _ <= ‖R‖ * (2 * ‖T‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm (e.symm : F0 →L[Real] E0) T).trans <| by
          gcongr
      _ = 2 * ‖R‖ * ‖T‖ := by ring
  have hsq : (1 / 2 : Real) * ‖T‖ ^ 2 <= 2 * ‖R‖ * ‖T‖ := by
    calc
      (1 / 2 : Real) * ‖T‖ ^ 2 <= C T T := hClower T
      _ = C T (e w) := by rw [hew]
      _ = R w := hpair w
      _ <= ‖R w‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (R w)
      _ <= 2 * ‖R‖ * ‖T‖ := hRw
  by_cases hT : ‖T‖ = 0
  · rw [hT]
    exact mul_nonneg (by norm_num) (norm_nonneg R)
  · have hTpos : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm hT)
    nlinarith [norm_nonneg R]

section Gram

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance dualNormedSpace :
    NormedSpace Real (E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance bilinNormedGroup :
    NormedAddCommGroup (E0 →L[Real] E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance bilinNormedSpace :
    NormedSpace Real (E0 →L[Real] E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance endoNormedGroup :
    NormedAddCommGroup (E0 →L[Real] E0) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance endoNormedSpace :
    NormedSpace Real (E0 →L[Real] E0) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance vecBilinNormedGroup :
    NormedAddCommGroup (E0 →L[Real] E0 →L[Real] E0) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance vecBilinNormedSpace :
    NormedSpace Real (E0 →L[Real] E0 →L[Real] E0) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance triNormedGroup :
    NormedAddCommGroup (E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance triNormedSpace :
    NormedSpace Real (E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace



private noncomputable def gramCLM [CompleteSpace E0] :
    (E0 →L[Real] E0 →L[Real] Real) →L[Real] (E0 →L[Real] E0) :=
  ContinuousLinearMap.compL Real E0 (E0 →L[Real] Real) E0
    (InnerProductSpace.toDual Real E0).symm.toContinuousLinearEquiv.toContinuousLinearMap



private theorem gramCLM_apply [CompleteSpace E0]
    (B : E0 →L[Real] E0 →L[Real] Real) :
    gramCLM B = InnerProductSpace.continuousLinearMapOfBilin (𝕜 := Real) B := by
  rfl


private theorem gram_isUnit [CompleteSpace E0]
    {B : E0 →L[Real] E0 →L[Real] Real} (hB : IsCoercive B) :
    IsUnit (gramCLM B) := by
  rw [gramCLM_apply]
  exact ⟨hB.continuousLinearEquivOfBilin.toUnit, rfl⟩



private theorem gram_inv_eq [CompleteSpace E0]
    {B : E0 →L[Real] E0 →L[Real] Real} (hB : IsCoercive B) :
    Ring.inverse (gramCLM B) =
      (hB.continuousLinearEquivOfBilin.symm : E0 →L[Real] E0) := by
  rw [gramCLM_apply]
  change Ring.inverse
      (↑hB.continuousLinearEquivOfBilin.toUnit : E0 →L[Real] E0) = _
  rw [Ring.inverse_unit]
  rfl


private theorem gram_inv_norm_le [CompleteSpace E0]
    {B : E0 →L[Real] E0 →L[Real] Real} (hB : IsCoercive B)
    (hlower : ∀ v : E0, (1 / 2 : Real) * ‖v‖ ^ 2 ≤ B v v) :
    ‖Ring.inverse (gramCLM B)‖ ≤ 2 := by
  rw [gram_inv_eq hB]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro v
  have h := hB.symm_norm_le (c := (1 / 2 : Real)) (by norm_num)
    (by
      intro w
      simpa only [pow_two, mul_assoc] using hlower w) v
  norm_num at h ⊢
  exact h

set_option synthInstance.maxHeartbeats 800000 in

private theorem gram_apply_norm_le [CompleteSpace E0]
    (B : E0 →L[Real] E0 →L[Real] Real) :
    ‖gramCLM B‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) ?_
  intro v
  change ‖(InnerProductSpace.toDual Real E0).symm (B v)‖ ≤ ‖B‖ * ‖v‖
  rw [(InnerProductSpace.toDual Real E0).symm.norm_map]
  exact ContinuousLinearMap.le_opNorm B v

set_option synthInstance.maxHeartbeats 800000 in


private theorem gram_comp_norm_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    [CompleteSpace E0] {n : Nat}
    (T : ContinuousMultilinearMap Real (fun _ : Fin n => P)
      (E0 →L[Real] E0 →L[Real] Real)) :
    ‖(gramCLM (E0 := E0)).compContinuousMultilinearMap T‖ ≤ ‖T‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg T) ?_
  intro v
  change ‖gramCLM (T v)‖ ≤ ‖T‖ * ∏ i, ‖v i‖
  exact (gram_apply_norm_le (T v)).trans (T.le_opNorm v)

set_option synthInstance.maxHeartbeats 800000 in


private theorem gram_deriv_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    [CompleteSpace E0]
    (B : P → E0 →L[Real] E0 →L[Real] Real) (x : P)
    {m i : Nat} (hB : ContDiffAt Real (m : WithTop ℕ∞) B x) (hi : i ≤ m) :
    ‖iteratedFDeriv Real i (fun y => gramCLM (B y)) x‖ ≤
      ‖iteratedFDeriv Real i B x‖ := by
  have hi' : (i : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast hi
  have hderiv :
      iteratedFDeriv Real i (fun y => gramCLM (B y)) x =
        (gramCLM (E0 := E0)).compContinuousMultilinearMap
          (iteratedFDeriv Real i B x) := by
    simpa only [Function.comp_apply] using
      (gramCLM (E0 := E0)).iteratedFDeriv_comp_left hB hi'
  rw [hderiv]
  exact gram_comp_norm_le _

set_option synthInstance.maxHeartbeats 800000 in

private theorem norm_clm_apply_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (A : P → E0 →L[Real] E0) (V : P → E0) (x : P) (m : Nat)
    (hA : ContDiffAt Real (m : WithTop ℕ∞) A x)
    (hV : ContDiffAt Real (m : WithTop ℕ∞) V x) :
    ‖iteratedFDeriv Real m (fun y => A y (V y)) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
        ‖iteratedFDeriv Real i A x‖ *
        ‖iteratedFDeriv Real (m - i) V x‖ := by
  obtain ⟨u, hu, hAu⟩ := hA.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hVv⟩ := hV.contDiffOn le_rfl (by simp)
  let s : Set P := interior u ∩ interior v
  have hs_open : IsOpen s := isOpen_interior.inter isOpen_interior
  have hxs : x ∈ s :=
    ⟨mem_interior_iff_mem_nhds.mpr hu, mem_interior_iff_mem_nhds.mpr hv⟩
  have hAs : ContDiffOn Real (m : WithTop ℕ∞) A s :=
    hAu.mono (Set.inter_subset_left.trans interior_subset)
  have hVs : ContDiffOn Real (m : WithTop ℕ∞) V s :=
    hVv.mono (Set.inter_subset_right.trans interior_subset)
  have h := norm_iteratedFDerivWithin_clm_apply hAs hVs
    hs_open.uniqueDiffOn hxs (by rfl)
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := Real)
    (f := fun y => A y (V y)) m hs_open hxs] at h
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := Real)
    (f := A) _ hs_open hxs,
    iteratedFDerivWithin_of_isOpen (𝕜 := Real)
      (f := V) _ hs_open hxs] at h
  exact h

set_option synthInstance.maxHeartbeats 800000 in

private theorem norm_bilinAt_le
    {P X Y Z : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (T : X →L[Real] Y →L[Real] Z) (f : P → X) (g : P → Y)
    (x : P) (m : Nat)
    (hf : ContDiffAt Real (m : WithTop ℕ∞) f x)
    (hg : ContDiffAt Real (m : WithTop ℕ∞) g x) :
    ‖iteratedFDeriv Real m (fun y => T (f y) (g y)) x‖ ≤
      ‖T‖ * ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
        ‖iteratedFDeriv Real i f x‖ *
        ‖iteratedFDeriv Real (m - i) g x‖ := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn le_rfl (by simp)
  let s : Set P := interior u ∩ interior v
  have hs_open : IsOpen s := isOpen_interior.inter isOpen_interior
  have hxs : x ∈ s :=
    ⟨mem_interior_iff_mem_nhds.mpr hu, mem_interior_iff_mem_nhds.mpr hv⟩
  have hfs : ContDiffOn Real (m : WithTop ℕ∞) f s :=
    hfu.mono (Set.inter_subset_left.trans interior_subset)
  have hgs : ContDiffOn Real (m : WithTop ℕ∞) g s :=
    hgv.mono (Set.inter_subset_right.trans interior_subset)
  have h := T.norm_iteratedFDerivWithin_le_of_bilinear hfs hgs
    hs_open.uniqueDiffOn hxs (by rfl)
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := Real)
    (f := fun y => T (f y) (g y)) m hs_open hxs] at h
  simp_rw [iteratedFDerivWithin_of_isOpen (𝕜 := Real)
    (f := f) _ hs_open hxs,
    iteratedFDerivWithin_of_isOpen (𝕜 := Real)
      (f := g) _ hs_open hxs] at h
  exact h

set_option synthInstance.maxHeartbeats 800000 in


private theorem norm_compAt_le
    {P X Y : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P]
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    (g : X → Y) (f : P → X) (x : P) (m : Nat) (C D : Real)
    (hg : ContDiffAt Real (m : WithTop ℕ∞) g (f x))
    (hf : ContDiffAt Real (m : WithTop ℕ∞) f x)
    (hC : ∀ i, i ≤ m → ‖iteratedFDeriv Real i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv Real i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv Real m (fun y => g (f y)) x‖ ≤
      (m.factorial : Real) * C * D ^ m := by
  obtain ⟨u, hu, hgu⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hfv⟩ := hf.contDiffOn le_rfl (by simp)
  let t : Set X := interior u
  have ht_open : IsOpen t := isOpen_interior
  have hfxt : f x ∈ t := mem_interior_iff_mem_nhds.mpr hu
  have hpre : f ⁻¹' t ∈ nhds x := hf.continuousAt (ht_open.mem_nhds hfxt)
  let s : Set P := interior v ∩ interior (f ⁻¹' t)
  have hs_open : IsOpen s := isOpen_interior.inter isOpen_interior
  have hxs : x ∈ s :=
    ⟨mem_interior_iff_mem_nhds.mpr hv, mem_interior_iff_mem_nhds.mpr hpre⟩
  have hgs : ContDiffOn Real (m : WithTop ℕ∞) g t := hgu.mono interior_subset
  have hfs : ContDiffOn Real (m : WithTop ℕ∞) f s :=
    hfv.mono (Set.inter_subset_left.trans interior_subset)
  have hmaps : Set.MapsTo f s t := fun y hy => by
    have hy' : y ∈ f ⁻¹' t := interior_subset hy.2
    exact hy'
  have hC' : ∀ i, i ≤ m →
      ‖iteratedFDerivWithin Real i g t (f x)‖ ≤ C := by
    intro i him
    rw [iteratedFDerivWithin_of_isOpen i ht_open hfxt]
    exact hC i him
  have hD' : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDerivWithin Real i f s x‖ ≤ D ^ i := by
    intro i hi him
    rw [iteratedFDerivWithin_of_isOpen i hs_open hxs]
    exact hD i hi him
  have hcomp := norm_iteratedFDerivWithin_comp_le hgs hfs le_rfl
    ht_open.uniqueDiffOn hs_open.uniqueDiffOn hmaps hxs hC' hD'
  rw [iteratedFDerivWithin_of_isOpen m hs_open hxs] at hcomp
  simpa only [Function.comp_apply] using hcomp

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in


private theorem gram_inv_deriv_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    [CompleteSpace E0]
    (B : P → E0 →L[Real] E0 →L[Real] Real) (x : P) (m : Nat) (D : Real)
    (hB : ContDiffAt Real (m : WithTop ℕ∞) B x)
    (hlower : ∀ᶠ y in nhds x, ∀ v : E0,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ B y v v)
    (hD : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv Real i B x‖ ≤ D ^ i) :
    ‖iteratedFDeriv Real m
        (fun y => Ring.inverse (gramCLM (B y))) x‖ ≤
      (m.factorial : Real) *
        ((m.factorial : Real) * 2 ^ (m + 1)) * D ^ m := by
  have hunit : ∀ᶠ y in nhds x, IsUnit (gramCLM (B y)) := by
    filter_upwards [hlower] with y hy
    apply gram_isUnit
    exact ⟨(1 / 2 : Real), by norm_num, fun v => by
      simpa only [pow_two, mul_assoc] using hy v⟩
  have hlowerx := hlower.self_of_nhds
  let hco : IsCoercive (B x) :=
    ⟨(1 / 2 : Real), by norm_num, fun v => by
      simpa only [pow_two, mul_assoc] using hlowerx v⟩
  have hinv : ‖Ring.inverse (gramCLM (B x))‖ ≤ 2 :=
    gram_inv_norm_le hco hlowerx
  have hgram : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv Real i (fun y => gramCLM (B y)) x‖ ≤ D ^ i := by
    intro i hi him
    exact (gram_deriv_le B x hB him).trans (hD i hi him)
  have h := norm_iteratedFDeriv_invComp_le
    (E := E0) (A := fun y => gramCLM (B y)) x m 2 D
    (by
      simpa only [Function.comp_apply] using
        (gramCLM (E0 := E0)).contDiff.comp_contDiffAt x hB)
    hunit hinv hgram
  simpa only [max_eq_left (by norm_num : (1 : Real) ≤ 2)] using h

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in


private theorem gram_apply_deriv_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    [CompleteSpace E0]
    (B : P → E0 →L[Real] E0 →L[Real] Real) (V : P → E0)
    (x : P) (m : Nat) (D : Real)
    (hB : ContDiffAt Real (m : WithTop ℕ∞) B x)
    (hV : ContDiffAt Real (m : WithTop ℕ∞) V x)
    (hlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q)
    (hD : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv Real i B x‖ ≤ D ^ i) :
    ‖iteratedFDeriv Real m
        (fun y => Ring.inverse (gramCLM (B y)) (V y)) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
        ((i.factorial : Real) *
          ((i.factorial : Real) * 2 ^ (i + 1)) * D ^ i) *
        ‖iteratedFDeriv Real (m - i) V x‖ := by
  have hunit : ∀ᶠ y in nhds x, IsUnit (gramCLM (B y)) := by
    filter_upwards [hlower] with y hy
    apply gram_isUnit
    exact ⟨(1 / 2 : Real), by norm_num, fun q => by
      simpa only [pow_two, mul_assoc] using hy q⟩
  obtain ⟨w, hw⟩ := hunit.self_of_nhds
  have hgram : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => gramCLM (B y)) x := by
    simpa only [Function.comp_apply] using
      (gramCLM (E0 := E0)).contDiff.comp_contDiffAt x hB
  have hinv : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => Ring.inverse (gramCLM (B y))) x := by
    have hout : ContDiffAt Real (m : WithTop ℕ∞) Ring.inverse
        (gramCLM (B x)) := by
      rw [← hw]
      exact contDiffAt_ringInverse Real w
    simpa only [Function.comp_apply] using hout.comp x hgram
  refine (norm_clm_apply_le
    (fun y => Ring.inverse (gramCLM (B y))) V x m hinv hV).trans ?_
  refine Finset.sum_le_sum fun i hi_mem => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
  have hi_top : (i : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast him
  have hBi : ContDiffAt Real (i : WithTop ℕ∞) B x := hB.of_le hi_top
  have hinv_i := gram_inv_deriv_le B x i D hBi hlower
    (fun j hj hji => hD j hj (hji.trans him))
  gcongr



private noncomputable def koszulRieszCLM [CompleteSpace E0] (u v : E0) :
    (E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) →L[Real] E0 :=
  (InnerProductSpace.toDual Real E0).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply Real (E0 →L[Real] Real) v).comp
      ((ContinuousLinearMap.apply Real (E0 →L[Real] E0 →L[Real] Real) u).comp
        MetricKoszul.koszulCovCLM))

@[simp] private theorem koszulRieszCLM_apply [CompleteSpace E0] (u v : E0)
    (D : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) :
    koszulRieszCLM u v D =
      (InnerProductSpace.toDual Real E0).symm (MetricKoszul.koszulCov D u v) := by
  simp [koszulRieszCLM]



private noncomputable def raisedKoszul [CompleteSpace E0]
    (B : E0 →L[Real] E0 →L[Real] Real)
    (D : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) (u v : E0) : E0 :=
  Ring.inverse (gramCLM B) (koszulRieszCLM u v D)



private theorem raisedKoszul_eq [CompleteSpace E0]
    {B : E0 →L[Real] E0 →L[Real] Real} (hB : IsCoercive B)
    (D : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) (u v : E0) :
    raisedKoszul B D u v = MetricKoszul.koszulVec hB D u v := by
  rw [raisedKoszul, gramCLM_apply, koszulRieszCLM_apply,
    ← hB.sharp_eq_inverse]
  rfl



private noncomputable def koszulRieszOpCLM [CompleteSpace E0] :
    (E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) →L[Real]
      (E0 →L[Real] E0 →L[Real] E0) :=
  (ContinuousLinearMap.compL Real E0
      (E0 →L[Real] E0 →L[Real] Real) (E0 →L[Real] E0)
      (ContinuousLinearMap.compL Real E0 (E0 →L[Real] Real) E0
        (InnerProductSpace.toDual Real E0).symm.toContinuousLinearEquiv.toContinuousLinearMap)).comp
    MetricKoszul.koszulCovCLM

@[simp] private theorem koszulRieszOpCLM_apply [CompleteSpace E0]
    (D : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) (u v : E0) :
    koszulRieszOpCLM D u v = koszulRieszCLM u v D := by
  simp [koszulRieszOpCLM, koszulRieszCLM]
  rfl


private noncomputable def postBilinCLM :
    (E0 →L[Real] E0) →L[Real]
      (E0 →L[Real] E0 →L[Real] E0) →L[Real]
        (E0 →L[Real] E0 →L[Real] E0) :=
  (ContinuousLinearMap.compL Real E0 (E0 →L[Real] E0) (E0 →L[Real] E0)).comp
    (ContinuousLinearMap.compL Real E0 E0 E0)


private noncomputable def preLeftCLM :
    (E0 →L[Real] E0 →L[Real] E0) →L[Real]
      (E0 →L[Real] E0) →L[Real]
        (E0 →L[Real] E0 →L[Real] E0) :=
  ContinuousLinearMap.compL Real E0 E0 (E0 →L[Real] E0)


private noncomputable def preRightCLM :
    (E0 →L[Real] E0 →L[Real] E0) →L[Real]
      (E0 →L[Real] E0) →L[Real]
        (E0 →L[Real] E0 →L[Real] E0) :=
  ((ContinuousLinearMap.compL Real E0 (E0 →L[Real] E0) (E0 →L[Real] E0)).comp
    (ContinuousLinearMap.compL Real E0 E0 E0).flip).flip


private noncomputable def postBilin
    (A : E0 →L[Real] E0) (K : E0 →L[Real] E0 →L[Real] E0) :
    E0 →L[Real] E0 →L[Real] E0 :=
  postBilinCLM A K

@[simp] private theorem postBilin_apply
    (A : E0 →L[Real] E0) (K : E0 →L[Real] E0 →L[Real] E0) (u v : E0) :
    postBilin A K u v = A (K u v) := by
  rfl



private noncomputable def preBilin
    (K : E0 →L[Real] E0 →L[Real] E0) (A : E0 →L[Real] E0) :
    E0 →L[Real] E0 →L[Real] E0 :=
  preRightCLM (preLeftCLM K A) A

@[simp] private theorem preBilin_apply
    (K : E0 →L[Real] E0 →L[Real] E0) (A : E0 →L[Real] E0) (u v : E0) :
    preBilin K A u v = K (A u) (A v) := by
  rfl


private noncomputable def raisedKoszulOp [CompleteSpace E0]
    (B : E0 →L[Real] E0 →L[Real] Real)
    (D : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) :
    E0 →L[Real] E0 →L[Real] E0 :=
  postBilin (Ring.inverse (gramCLM B)) (koszulRieszOpCLM D)

@[simp] private theorem raisedKoszulOp_apply [CompleteSpace E0]
    (B : E0 →L[Real] E0 →L[Real] Real)
    (D : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real) (u v : E0) :
    raisedKoszulOp B D u v = raisedKoszul B D u v := by
  rfl


private theorem koszulRieszCLM_le [CompleteSpace E0] (u v : E0) :
    ‖koszulRieszCLM u v‖ ≤ (3 / 2 : Real) * ‖u‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro D
  rw [koszulRieszCLM_apply,
    (InnerProductSpace.toDual Real E0).symm.norm_map]
  have hD : ∀ a b c : E0,
      ‖D a b c‖ ≤ ‖D‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
    intro a b c
    calc
      ‖D a b c‖ ≤ ‖D a‖ * ‖b‖ * ‖c‖ := (D a).le_opNorm₂ b c
      _ ≤ (‖D‖ * ‖a‖) * ‖b‖ * ‖c‖ := by
        gcongr
        exact D.le_opNorm a
  calc
    ‖MetricKoszul.koszulCov D u v‖ ≤
        (3 / 2 : Real) * ‖D‖ * ‖u‖ * ‖v‖ :=
      MetricKoszul.koszulCov_norm_le D (norm_nonneg D) hD u v
    _ = ((3 / 2 : Real) * ‖u‖ * ‖v‖) * ‖D‖ := by ring

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in


private theorem raised_deriv_le
    [CompleteSpace E0]
    (B : E0 → E0 →L[Real] E0 →L[Real] Real) (x : E0)
    (m : Nat) (D : Real) (u v : E0)
    (hB : ContDiffAt Real ((m + 1 : Nat) : WithTop ℕ∞) B x)
    (hlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q)
    (hD : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv Real i B x‖ ≤ D ^ i) :
    ‖iteratedFDeriv Real m
        (fun y => Ring.inverse (gramCLM (B y))
          (koszulRieszCLM u v (fderiv Real B y))) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
        ((i.factorial : Real) *
          ((i.factorial : Real) * 2 ^ (i + 1)) * D ^ i) *
        (((3 / 2 : Real) * ‖u‖ * ‖v‖) * D ^ (m - i + 1)) := by
  have hm_top : (m : WithTop ℕ∞) ≤ ((m + 1 : Nat) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ m
  have hBm : ContDiffAt Real (m : WithTop ℕ∞) B x := hB.of_le hm_top
  have hfB : ContDiffAt Real (m : WithTop ℕ∞) (fderiv Real B) x := by
    exact hB.fderiv_right (m := (m : WithTop ℕ∞)) (by
      norm_cast)
  have hV : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => koszulRieszCLM u v (fderiv Real B y)) x := by
    simpa only [Function.comp_apply] using
      (koszulRieszCLM u v).contDiff.comp_contDiffAt x hfB
  have hD_nonneg : 0 ≤ D := by
    have h := hD 1 (by omega) (by omega)
    simpa only [pow_one] using
      (norm_nonneg (iteratedFDeriv Real 1 B x)).trans h
  refine (gram_apply_deriv_le B
    (fun y => koszulRieszCLM u v (fderiv Real B y))
    x m D hBm hV hlower
    (fun i hi him => hD i hi (him.trans (Nat.le_succ m)))).trans ?_
  refine Finset.sum_le_sum fun i hi_mem => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
  have hmi_top : ((m - i : Nat) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast Nat.sub_le m i
  have hfield := (koszulRieszCLM u v).norm_iteratedFDeriv_comp_left
    hfB hmi_top
  have hmetric :
      ‖iteratedFDeriv Real (m - i) (fderiv Real B) x‖ ≤
        D ^ (m - i + 1) := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hD (m - i + 1) (by omega) (by omega)
  have hVbound :
      ‖iteratedFDeriv Real (m - i)
          (fun y => koszulRieszCLM u v (fderiv Real B y)) x‖ ≤
        ((3 / 2 : Real) * ‖u‖ * ‖v‖) * D ^ (m - i + 1) := by
    calc
      ‖iteratedFDeriv Real (m - i)
          (fun y => koszulRieszCLM u v (fderiv Real B y)) x‖
          ≤ ‖koszulRieszCLM u v‖ *
              ‖iteratedFDeriv Real (m - i) (fderiv Real B) x‖ := hfield
      _ ≤ ((3 / 2 : Real) * ‖u‖ * ‖v‖) *
          D ^ (m - i + 1) := by
        gcongr
        exact koszulRieszCLM_le u v
  apply mul_le_mul_of_nonneg_left hVbound
  positivity


private noncomputable def raisedBudget [CompleteSpace E0]
    (D : Real) (m : Nat) : Real :=
  ‖postBilinCLM (E0 := E0)‖ *
    ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
      ((i.factorial : Real) *
        ((i.factorial : Real) * 2 ^ (i + 1)) * D ^ i) *
      (‖koszulRieszOpCLM (E0 := E0)‖ * D ^ (m - i + 1))



private noncomputable def raisedEnvelope [CompleteSpace E0]
    (D : Real) (m : Nat) : Real :=
  ∑ i ∈ Finset.range (m + 1), raisedBudget (E0 := E0) D i



private noncomputable def raisedCompBudget [CompleteSpace E0]
    (D P : Real) (m : Nat) : Real :=
  (m.factorial : Real) * raisedEnvelope (E0 := E0) D m * P ^ m



private noncomputable def isomNextBudget [CompleteSpace E0]
    (D P : Real) (m : Nat) : Real :=
  ‖postBilinCLM (E0 := E0)‖ *
      ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
        P ^ (i + 1) * raisedBudget (E0 := E0) D (m - i) +
    ‖preRightCLM (E0 := E0)‖ *
      ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
        (‖preLeftCLM (E0 := E0)‖ *
          ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
            raisedCompBudget (E0 := E0) D P j * P ^ (i - j + 1)) *
        P ^ (m - i + 1)


private noncomputable def isomBudgetState [CompleteSpace E0]
    (D : Real) : Nat → Real × Real
  | 0 => (0, 1)
  | n + 1 =>
      let prev := isomBudgetState D n
      let next := match n with
        | 0 => 2
        | k + 1 => isomNextBudget (E0 := E0) D prev.2 k
      (next, max prev.2 next)


private noncomputable def isomBudget [CompleteSpace E0]
    (D : Real) (n : Nat) : Real :=
  (isomBudgetState (E0 := E0) D n).1


private noncomputable def isomEnvelope [CompleteSpace E0]
    (D : Real) (n : Nat) : Real :=
  (isomBudgetState (E0 := E0) D n).2

@[simp] private theorem isomBudget_zero [CompleteSpace E0] (D : Real) :
    isomBudget (E0 := E0) D 0 = 0 := by
  rfl

@[simp] private theorem isomBudget_one [CompleteSpace E0] (D : Real) :
    isomBudget (E0 := E0) D 1 = 2 := by
  rfl

@[simp] private theorem isomEnvelope_zero [CompleteSpace E0] (D : Real) :
    isomEnvelope (E0 := E0) D 0 = 1 := by
  rfl

private theorem isomBudget_succ [CompleteSpace E0] (D : Real) (n : Nat) :
    isomBudget (E0 := E0) D (Nat.succ (Nat.succ n)) =
      isomNextBudget (E0 := E0) D
        (isomEnvelope (E0 := E0) D (Nat.succ n)) n := by
  rfl

private theorem isomEnvelope_succ [CompleteSpace E0] (D : Real) (n : Nat) :
    isomEnvelope (E0 := E0) D (Nat.succ n) =
      max (isomEnvelope (E0 := E0) D n)
        (isomBudget (E0 := E0) D (Nat.succ n)) := by
  cases n <;> rfl

private theorem isomBudget_le_env [CompleteSpace E0] (D : Real) (n : Nat) :
    isomBudget (E0 := E0) D n ≤ isomEnvelope (E0 := E0) D n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [isomEnvelope_succ]
      exact le_max_right _ _

private theorem one_le_isomEnv [CompleteSpace E0] (D : Real) (n : Nat) :
    1 ≤ isomEnvelope (E0 := E0) D n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [isomEnvelope_succ]
      exact ih.trans (le_max_left _ _)

private theorem isomEnv_le_succ [CompleteSpace E0] (D : Real) (n : Nat) :
    isomEnvelope (E0 := E0) D n ≤
      isomEnvelope (E0 := E0) D (Nat.succ n) := by
  rw [isomEnvelope_succ]
  exact le_max_left _ _

private theorem isomBudget_le_of_le [CompleteSpace E0] (D : Real)
    {i n : Nat} (hin : i ≤ n) :
    isomBudget (E0 := E0) D i ≤ isomEnvelope (E0 := E0) D n :=
  (isomBudget_le_env (E0 := E0) D i).trans
    ((monotone_nat_of_le_succ (isomEnv_le_succ (E0 := E0) D)) hin)

private theorem raisedBudget_nonneg [CompleteSpace E0]
    {D : Real} (hD : 0 ≤ D) (m : Nat) :
    0 ≤ raisedBudget (E0 := E0) D m := by
  unfold raisedBudget
  positivity

private theorem raisedEnvelope_nonneg [CompleteSpace E0]
    {D : Real} (hD : 0 ≤ D) (m : Nat) :
    0 ≤ raisedEnvelope (E0 := E0) D m := by
  exact Finset.sum_nonneg fun i _ => raisedBudget_nonneg (E0 := E0) hD i

private theorem raisedComp_nonneg [CompleteSpace E0]
    {D P : Real} (hD : 0 ≤ D) (hP : 0 ≤ P) (m : Nat) :
    0 ≤ raisedCompBudget (E0 := E0) D P m := by
  unfold raisedCompBudget
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (raisedEnvelope_nonneg (E0 := E0) hD m))
    (pow_nonneg hP _)

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in


private theorem raisedOp_deriv_le
    [CompleteSpace E0]
    (B : E0 → E0 →L[Real] E0 →L[Real] Real) (x : E0)
    (m : Nat) (D : Real)
    (hB : ContDiffAt Real ((m + 1 : Nat) : WithTop ℕ∞) B x)
    (hlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q)
    (hD : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv Real i B x‖ ≤ D ^ i) :
    ‖iteratedFDeriv Real m
        (fun y => raisedKoszulOp (B y) (fderiv Real B y)) x‖ ≤
      raisedBudget (E0 := E0) D m := by
  unfold raisedBudget
  have hm_top : (m : WithTop ℕ∞) ≤ ((m + 1 : Nat) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ m
  have hBm : ContDiffAt Real (m : WithTop ℕ∞) B x := hB.of_le hm_top
  have hfB : ContDiffAt Real (m : WithTop ℕ∞) (fderiv Real B) x := by
    exact hB.fderiv_right (m := (m : WithTop ℕ∞)) (by norm_cast)
  have hK : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => koszulRieszOpCLM (fderiv Real B y)) x := by
    simpa only [Function.comp_apply] using
      (koszulRieszOpCLM (E0 := E0)).contDiff.comp_contDiffAt x hfB
  have hunit : ∀ᶠ y in nhds x, IsUnit (gramCLM (B y)) := by
    filter_upwards [hlower] with y hy
    apply gram_isUnit
    exact ⟨(1 / 2 : Real), by norm_num, fun q => by
      simpa only [pow_two, mul_assoc] using hy q⟩
  obtain ⟨w, hw⟩ := hunit.self_of_nhds
  have hgram : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => gramCLM (B y)) x := by
    simpa only [Function.comp_apply] using
      (gramCLM (E0 := E0)).contDiff.comp_contDiffAt x hBm
  have hinv : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => Ring.inverse (gramCLM (B y))) x := by
    have hout : ContDiffAt Real (m : WithTop ℕ∞) Ring.inverse
        (gramCLM (B x)) := by
      rw [← hw]
      exact contDiffAt_ringInverse Real w
    simpa only [Function.comp_apply] using hout.comp x hgram
  have hD_nonneg : 0 ≤ D := by
    have h := hD 1 (by omega) (by omega)
    simpa only [pow_one] using
      (norm_nonneg (iteratedFDeriv Real 1 B x)).trans h
  change ‖iteratedFDeriv Real m
      (fun y => postBilinCLM (Ring.inverse (gramCLM (B y)))
        (koszulRieszOpCLM (fderiv Real B y))) x‖ ≤ _
  refine (norm_bilinAt_le (postBilinCLM (E0 := E0))
    (fun y => Ring.inverse (gramCLM (B y)))
    (fun y => koszulRieszOpCLM (fderiv Real B y))
    x m hinv hK).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (norm_nonneg (postBilinCLM (E0 := E0)))
  refine Finset.sum_le_sum fun i hi_mem => ?_
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
  have hi_top : (i : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast him
  have hBi : ContDiffAt Real (i : WithTop ℕ∞) B x := hBm.of_le hi_top
  have hinv_i := gram_inv_deriv_le B x i D hBi hlower
    (fun j hj hji => hD j hj (hji.trans (him.trans (Nat.le_succ m))))
  have hmi_top : ((m - i : Nat) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
    exact_mod_cast Nat.sub_le m i
  have hKderiv := (koszulRieszOpCLM (E0 := E0)).norm_iteratedFDeriv_comp_left
    hfB hmi_top
  have hmetric :
      ‖iteratedFDeriv Real (m - i) (fderiv Real B) x‖ ≤
        D ^ (m - i + 1) := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hD (m - i + 1) (by omega) (by omega)
  have hKbound :
      ‖iteratedFDeriv Real (m - i)
          (fun y => koszulRieszOpCLM (fderiv Real B y)) x‖ ≤
        ‖koszulRieszOpCLM (E0 := E0)‖ * D ^ (m - i + 1) :=
    hKderiv.trans (mul_le_mul_of_nonneg_left hmetric (norm_nonneg _))
  gcongr

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in


private theorem raisedOp_contDiffAt
    [CompleteSpace E0]
    (B : E0 → E0 →L[Real] E0 →L[Real] Real) (x : E0) (m : Nat)
    (hB : ContDiffAt Real ((m + 1 : Nat) : WithTop ℕ∞) B x)
    (hlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q) :
    ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => raisedKoszulOp (B y) (fderiv Real B y)) x := by
  have hm_top : (m : WithTop ℕ∞) ≤ ((m + 1 : Nat) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ m
  have hBm : ContDiffAt Real (m : WithTop ℕ∞) B x := hB.of_le hm_top
  have hfB : ContDiffAt Real (m : WithTop ℕ∞) (fderiv Real B) x := by
    exact hB.fderiv_right (m := (m : WithTop ℕ∞)) (by norm_cast)
  have hK : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => koszulRieszOpCLM (fderiv Real B y)) x := by
    simpa only [Function.comp_apply] using
      (koszulRieszOpCLM (E0 := E0)).contDiff.comp_contDiffAt x hfB
  have hunit : ∀ᶠ y in nhds x, IsUnit (gramCLM (B y)) := by
    filter_upwards [hlower] with y hy
    apply gram_isUnit
    exact ⟨(1 / 2 : Real), by norm_num, fun q => by
      simpa only [pow_two, mul_assoc] using hy q⟩
  obtain ⟨w, hw⟩ := hunit.self_of_nhds
  have hgram : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => gramCLM (B y)) x := by
    simpa only [Function.comp_apply] using
      (gramCLM (E0 := E0)).contDiff.comp_contDiffAt x hBm
  have hinv : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => Ring.inverse (gramCLM (B y))) x := by
    have hout : ContDiffAt Real (m : WithTop ℕ∞) Ring.inverse
        (gramCLM (B x)) := by
      rw [← hw]
      exact contDiffAt_ringInverse Real w
    simpa only [Function.comp_apply] using hout.comp x hgram
  simpa only [raisedKoszulOp, postBilin] using
    (postBilinCLM (E0 := E0)).isBoundedBilinearMap.contDiff.comp₂_contDiffAt hinv hK

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in


private theorem raisedComp_deriv_le
    [CompleteSpace E0]
    (C : E0 → E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 → E0) (x : E0) (m : Nat) (D A : Real)
    (hC : ContDiffAt Real ((m + 1 : Nat) : WithTop ℕ∞) C (Phi x))
    (hPhi : ContDiffAt Real (m : WithTop ℕ∞) Phi x)
    (hlower : ∀ᶠ y in nhds (Phi x), ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q)
    (hD : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv Real i C (Phi x)‖ ≤ D ^ i)
    (hA : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv Real i Phi x‖ ≤ A ^ i) :
    ‖iteratedFDeriv Real m
        (fun y => raisedKoszulOp (C (Phi y)) (fderiv Real C (Phi y))) x‖ ≤
      (m.factorial : Real) * raisedEnvelope (E0 := E0) D m * A ^ m := by
  let K : E0 → E0 →L[Real] E0 →L[Real] E0 :=
    fun z => raisedKoszulOp (C z) (fderiv Real C z)
  have hK : ContDiffAt Real (m : WithTop ℕ∞) K (Phi x) :=
    raisedOp_contDiffAt C (Phi x) m hC hlower
  have hD_nonneg : 0 ≤ D := by
    have h := hD 1 (by omega) (by omega)
    simpa only [pow_one] using
      (norm_nonneg (iteratedFDeriv Real 1 C (Phi x))).trans h
  have hKbound : ∀ i, i ≤ m →
      ‖iteratedFDeriv Real i K (Phi x)‖ ≤
        raisedEnvelope (E0 := E0) D m := by
    intro i him
    have hi_top : ((i + 1 : Nat) : WithTop ℕ∞) ≤
        ((m + 1 : Nat) : WithTop ℕ∞) := by
      exact_mod_cast Nat.succ_le_succ him
    have hCi : ContDiffAt Real ((i + 1 : Nat) : WithTop ℕ∞) C (Phi x) :=
      hC.of_le hi_top
    have hi := raisedOp_deriv_le C (Phi x) i D hCi hlower
      (fun j hj hji => hD j hj (hji.trans (Nat.succ_le_succ him)))
    refine hi.trans ?_
    exact Finset.single_le_sum
      (fun j _ => raisedBudget_nonneg (E0 := E0) hD_nonneg j)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr him))
  simpa only [K] using norm_compAt_le K Phi x m
    (raisedEnvelope (E0 := E0) D m) A hK hPhi hKbound hA

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in



private theorem isom_rec_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace Real P]
    (Q : P → E0 →L[Real] E0 →L[Real] E0)
    (A : P → E0 →L[Real] E0)
    (KB KC : P → E0 →L[Real] E0 →L[Real] E0)
    (x : P) (m : Nat)
    (hA : ContDiffAt Real (m : WithTop ℕ∞) A x)
    (hKB : ContDiffAt Real (m : WithTop ℕ∞) KB x)
    (hKC : ContDiffAt Real (m : WithTop ℕ∞) KC x)
    (heq : Q =ᶠ[nhds x] fun y =>
      postBilin (A y) (KB y) - preBilin (KC y) (A y)) :
    ‖iteratedFDeriv Real m Q x‖ ≤
      ‖postBilinCLM (E0 := E0)‖ *
          ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
            ‖iteratedFDeriv Real i A x‖ *
            ‖iteratedFDeriv Real (m - i) KB x‖ +
        ‖preRightCLM (E0 := E0)‖ *
          ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
            (‖preLeftCLM (E0 := E0)‖ *
              ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                ‖iteratedFDeriv Real j KC x‖ *
                ‖iteratedFDeriv Real (i - j) A x‖) *
            ‖iteratedFDeriv Real (m - i) A x‖ := by
  have hpost : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => postBilin (A y) (KB y)) x := by
    simpa only [postBilin] using
      (postBilinCLM (E0 := E0)).isBoundedBilinearMap.contDiff.comp₂_contDiffAt hA hKB
  have hleft : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => preLeftCLM (KC y) (A y)) x :=
    (preLeftCLM (E0 := E0)).isBoundedBilinearMap.contDiff.comp₂_contDiffAt hKC hA
  have hpre : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => preBilin (KC y) (A y)) x := by
    simpa only [preBilin] using
      (preRightCLM (E0 := E0)).isBoundedBilinearMap.contDiff.comp₂_contDiffAt hleft hA
  have hpost_bound := norm_bilinAt_le (postBilinCLM (E0 := E0))
    A KB x m hA hKB
  have hpre_base := norm_bilinAt_le (preRightCLM (E0 := E0))
    (fun y => preLeftCLM (KC y) (A y)) A x m hleft hA
  have hpre_bound :
      ‖iteratedFDeriv Real m (fun y => preBilin (KC y) (A y)) x‖ ≤
        ‖preRightCLM (E0 := E0)‖ *
          ∑ i ∈ Finset.range (m + 1), (m.choose i : Real) *
            (‖preLeftCLM (E0 := E0)‖ *
              ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                ‖iteratedFDeriv Real j KC x‖ *
                ‖iteratedFDeriv Real (i - j) A x‖) *
            ‖iteratedFDeriv Real (m - i) A x‖ := by
    refine hpre_base.trans ?_
    refine mul_le_mul_of_nonneg_left ?_
      (norm_nonneg (preRightCLM (E0 := E0)))
    refine Finset.sum_le_sum fun i hi_mem => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
    have hi_top : (i : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by
      exact_mod_cast him
    have hleft_i := norm_bilinAt_le (preLeftCLM (E0 := E0))
      KC A x i (hKC.of_le hi_top) (hA.of_le hi_top)
    gcongr
  rw [(Filter.EventuallyEq.iteratedFDeriv Real heq m).self_of_nhds]
  change ‖iteratedFDeriv Real m
    ((fun y => postBilin (A y) (KB y)) -
      fun y => preBilin (KC y) (A y)) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply hpost hpre]
  exact (norm_sub_le _ _).trans (add_le_add hpost_bound hpre_bound)

set_option linter.style.setOption false in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 1200000 in

private theorem isom_next_le
    [CompleteSpace E0]
    (B C : E0 → E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 → E0) (x : E0) (m : Nat) (D P : Real)
    (hB : ContDiffAt Real ((m + 1 : Nat) : WithTop ℕ∞) B x)
    (hC : ContDiffAt Real ((m + 1 : Nat) : WithTop ℕ∞) C (Phi x))
    (hPhi : ContDiffAt Real ((m + 2 : Nat) : WithTop ℕ∞) Phi x)
    (hBlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q)
    (hClower : ∀ᶠ y in nhds (Phi x), ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q)
    (hDB : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv Real i B x‖ ≤ D ^ i)
    (hDC : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv Real i C (Phi x)‖ ≤ D ^ i)
    (hP : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv Real i Phi x‖ ≤ P ^ i)
    (heq : fderiv Real (fderiv Real Phi) =ᶠ[nhds x] fun y =>
      postBilin (fderiv Real Phi y)
          (raisedKoszulOp (B y) (fderiv Real B y)) -
        preBilin
          (raisedKoszulOp (C (Phi y)) (fderiv Real C (Phi y)))
          (fderiv Real Phi y)) :
    ‖iteratedFDeriv Real (m + 2) Phi x‖ ≤
      isomNextBudget (E0 := E0) D P m := by
  have hD_nonneg : 0 ≤ D := by
    have h := hDB 1 (by omega) (by omega)
    simpa only [pow_one] using
      (norm_nonneg (iteratedFDeriv Real 1 B x)).trans h
  have hP_nonneg : 0 ≤ P := by
    have h := hP 1 (by omega) (by omega)
    simpa only [pow_one] using
      (norm_nonneg (iteratedFDeriv Real 1 Phi x)).trans h
  have hA : ContDiffAt Real (m : WithTop ℕ∞) (fderiv Real Phi) x :=
    hPhi.fderiv_right (m := (m : WithTop ℕ∞)) (by norm_cast; omega)
  have hKB : ContDiffAt Real (m : WithTop ℕ∞)
      (fun y => raisedKoszulOp (B y) (fderiv Real B y)) x :=
    raisedOp_contDiffAt B x m hB hBlower
  have hm_top : (m : WithTop ℕ∞) ≤ ((m + 2 : Nat) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : m ≤ m + 2)
  have hPhi_m : ContDiffAt Real (m : WithTop ℕ∞) Phi x := hPhi.of_le hm_top
  let KC : E0 → E0 →L[Real] E0 →L[Real] E0 :=
    fun z => raisedKoszulOp (C z) (fderiv Real C z)
  have hKCouter : ContDiffAt Real (m : WithTop ℕ∞) KC (Phi x) :=
    raisedOp_contDiffAt C (Phi x) m hC hClower
  have hKC : ContDiffAt Real (m : WithTop ℕ∞) (fun y => KC (Phi y)) x :=
    hKCouter.comp x hPhi_m
  have hAderiv : ∀ i, i ≤ m →
      ‖iteratedFDeriv Real i (fderiv Real Phi) x‖ ≤ P ^ (i + 1) := by
    intro i him
    rw [norm_iteratedFDeriv_fderiv]
    exact hP (i + 1) (by omega) (by omega)
  have hKBderiv : ∀ i, i ≤ m →
      ‖iteratedFDeriv Real i
          (fun y => raisedKoszulOp (B y) (fderiv Real B y)) x‖ ≤
        raisedBudget (E0 := E0) D i := by
    intro i him
    have hi_top : ((i + 1 : Nat) : WithTop ℕ∞) ≤
        ((m + 1 : Nat) : WithTop ℕ∞) := by
      exact_mod_cast Nat.succ_le_succ him
    exact raisedOp_deriv_le B x i D (hB.of_le hi_top) hBlower
      (fun j hj hji => hDB j hj (hji.trans (Nat.succ_le_succ him)))
  have hKCderiv : ∀ i, i ≤ m →
      ‖iteratedFDeriv Real i (fun y => KC (Phi y)) x‖ ≤
        raisedCompBudget (E0 := E0) D P i := by
    intro i him
    have hi_metric : ((i + 1 : Nat) : WithTop ℕ∞) ≤
        ((m + 1 : Nat) : WithTop ℕ∞) := by
      exact_mod_cast Nat.succ_le_succ him
    have hi_phi : (i : WithTop ℕ∞) ≤ ((m + 2 : Nat) : WithTop ℕ∞) := by
      exact_mod_cast (him.trans (by omega : m ≤ m + 2))
    have hi := raisedComp_deriv_le C Phi x i D P
      (hC.of_le hi_metric) (hPhi.of_le hi_phi) hClower
      (fun j hj hji => hDC j hj (hji.trans (Nat.succ_le_succ him)))
      (fun j hj hji => hP j hj (hji.trans (him.trans (Nat.le_succ m))))
    simpa only [KC, raisedCompBudget] using hi
  have hrec := isom_rec_le
    (fderiv Real (fderiv Real Phi)) (fderiv Real Phi)
    (fun y => raisedKoszulOp (B y) (fderiv Real B y))
    (fun y => KC (Phi y)) x m hA hKB hKC (by simpa only [KC] using heq)
  calc
    ‖iteratedFDeriv Real (m + 2) Phi x‖ =
        ‖iteratedFDeriv Real (m + 1) (fderiv Real Phi) x‖ := by
      simpa only [Nat.add_assoc] using
        (norm_iteratedFDeriv_fderiv
          (𝕜 := Real) (f := Phi) (x := x) (n := m + 1)).symm
    _ = ‖iteratedFDeriv Real m (fderiv Real (fderiv Real Phi)) x‖ := by
      simpa only using
        (norm_iteratedFDeriv_fderiv
          (𝕜 := Real) (f := fderiv Real Phi) (x := x) (n := m)).symm
    _ ≤ isomNextBudget (E0 := E0) D P m := hrec.trans (by
      unfold isomNextBudget
      apply add_le_add
      · refine mul_le_mul_of_nonneg_left ?_
          (norm_nonneg (postBilinCLM (E0 := E0)))
        refine Finset.sum_le_sum fun i hi_mem => ?_
        have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
        have hpair := mul_le_mul (hAderiv i him)
          (hKBderiv (m - i) (Nat.sub_le m i))
          (norm_nonneg _) (pow_nonneg hP_nonneg _)
        calc
          (m.choose i : Real) * ‖iteratedFDeriv Real i (fderiv Real Phi) x‖ *
                ‖iteratedFDeriv Real (m - i)
                  (fun y => raisedKoszulOp (B y) (fderiv Real B y)) x‖ =
              (m.choose i : Real) *
                (‖iteratedFDeriv Real i (fderiv Real Phi) x‖ *
                  ‖iteratedFDeriv Real (m - i)
                    (fun y => raisedKoszulOp (B y) (fderiv Real B y)) x‖) := by ring
          _ ≤ (m.choose i : Real) *
                (P ^ (i + 1) * raisedBudget (E0 := E0) D (m - i)) :=
            mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _)
          _ = (m.choose i : Real) * P ^ (i + 1) *
                raisedBudget (E0 := E0) D (m - i) := by ring
      · refine mul_le_mul_of_nonneg_left ?_
          (norm_nonneg (preRightCLM (E0 := E0)))
        refine Finset.sum_le_sum fun i hi_mem => ?_
        have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
        have hleft :
            ‖preLeftCLM (E0 := E0)‖ *
                ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                  ‖iteratedFDeriv Real j (fun y => KC (Phi y)) x‖ *
                  ‖iteratedFDeriv Real (i - j) (fderiv Real Phi) x‖ ≤
              ‖preLeftCLM (E0 := E0)‖ *
                ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                  raisedCompBudget (E0 := E0) D P j * P ^ (i - j + 1) := by
          refine mul_le_mul_of_nonneg_left ?_
            (norm_nonneg (preLeftCLM (E0 := E0)))
          refine Finset.sum_le_sum fun j hj_mem => ?_
          have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj_mem)
          have hpair := mul_le_mul (hKCderiv j (hji.trans him))
            (hAderiv (i - j) (Nat.sub_le i j |>.trans him))
            (norm_nonneg _) (raisedComp_nonneg (E0 := E0) hD_nonneg hP_nonneg j)
          calc
            (i.choose j : Real) *
                  ‖iteratedFDeriv Real j (fun y => KC (Phi y)) x‖ *
                  ‖iteratedFDeriv Real (i - j) (fderiv Real Phi) x‖ =
                (i.choose j : Real) *
                  (‖iteratedFDeriv Real j (fun y => KC (Phi y)) x‖ *
                    ‖iteratedFDeriv Real (i - j) (fderiv Real Phi) x‖) := by ring
            _ ≤ (i.choose j : Real) *
                  (raisedCompBudget (E0 := E0) D P j * P ^ (i - j + 1)) :=
              mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _)
            _ = (i.choose j : Real) * raisedCompBudget (E0 := E0) D P j *
                  P ^ (i - j + 1) := by ring
        have hleft_nonneg :
            0 ≤ ‖preLeftCLM (E0 := E0)‖ *
              ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                raisedCompBudget (E0 := E0) D P j * P ^ (i - j + 1) := by
          exact mul_nonneg (norm_nonneg (preLeftCLM (E0 := E0)))
            (Finset.sum_nonneg fun j _ =>
              mul_nonneg
                (mul_nonneg (Nat.cast_nonneg _)
                  (raisedComp_nonneg (E0 := E0) hD_nonneg hP_nonneg j))
                (pow_nonneg hP_nonneg _))
        have hpair := mul_le_mul hleft (hAderiv (m - i) (Nat.sub_le m i))
          (norm_nonneg _) hleft_nonneg
        calc
          (m.choose i : Real) *
                (‖preLeftCLM (E0 := E0)‖ *
                  ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                    ‖iteratedFDeriv Real j (fun y => KC (Phi y)) x‖ *
                    ‖iteratedFDeriv Real (i - j) (fderiv Real Phi) x‖) *
                ‖iteratedFDeriv Real (m - i) (fderiv Real Phi) x‖ =
              (m.choose i : Real) *
                ((‖preLeftCLM (E0 := E0)‖ *
                  ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                    ‖iteratedFDeriv Real j (fun y => KC (Phi y)) x‖ *
                    ‖iteratedFDeriv Real (i - j) (fderiv Real Phi) x‖) *
                  ‖iteratedFDeriv Real (m - i) (fderiv Real Phi) x‖) := by ring
          _ ≤ (m.choose i : Real) *
                ((‖preLeftCLM (E0 := E0)‖ *
                  ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                    raisedCompBudget (E0 := E0) D P j * P ^ (i - j + 1)) *
                  P ^ (m - i + 1)) :=
            mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _)
          _ = (m.choose i : Real) *
                (‖preLeftCLM (E0 := E0)‖ *
                  ∑ j ∈ Finset.range (i + 1), (i.choose j : Real) *
                    raisedCompBudget (E0 := E0) D P j * P ^ (i - j + 1)) *
                P ^ (m - i + 1) := by ring)

set_option linter.style.setOption false in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 1200000 in

private theorem isom_deriv_le
    [CompleteSpace E0]
    (B C : E0 → E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 → E0) (x : E0) (D : Real)
    (hBsm : ContDiffAt Real (⊤ : ℕ∞) B x)
    (hCsm : ContDiffAt Real (⊤ : ℕ∞) C (Phi x))
    (hPhi : ContDiffAt Real (⊤ : ℕ∞) Phi x)
    (hBupper : ∀ q : E0, B x q q ≤ 2 * ‖q‖ ^ 2)
    (hmetric : ∀ q : E0,
      C (Phi x) (fderiv Real Phi x q) (fderiv Real Phi x q) = B x q q)
    (hBlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q)
    (hClower : ∀ᶠ y in nhds (Phi x), ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q)
    (heq : fderiv Real (fderiv Real Phi) =ᶠ[nhds x] fun y =>
      postBilin (fderiv Real Phi y)
          (raisedKoszulOp (B y) (fderiv Real B y)) -
        preBilin
          (raisedKoszulOp (C (Phi y)) (fderiv Real C (Phi y)))
          (fderiv Real Phi y)) :
    ∀ r, 1 ≤ r →
      (∀ i, 1 ≤ i → i ≤ r →
        ‖iteratedFDeriv Real i B x‖ ≤ D ^ i) →
      (∀ i, 1 ≤ i → i ≤ r →
        ‖iteratedFDeriv Real i C (Phi x)‖ ≤ D ^ i) →
      ‖iteratedFDeriv Real r Phi x‖ ≤ isomBudget (E0 := E0) D r := by
  intro r
  refine Nat.strong_induction_on r ?_
  intro r ih hr hDB hDC
  rcases r with _ | n
  · omega
  rcases n with _ | m
  · simpa only [isomBudget_one] using
      isom_first_bound (B x) (C (Phi x)) Phi x hBupper
        hClower.self_of_nhds hmetric
  · let P := isomEnvelope (E0 := E0) D (Nat.succ m)
    have hPjets : ∀ i, 1 ≤ i → i ≤ m + 1 →
        ‖iteratedFDeriv Real i Phi x‖ ≤ P ^ i := by
      intro i hi him
      have hprev := ih i (by omega) hi
        (fun j hj hji => hDB j hj (hji.trans (by omega)))
        (fun j hj hji => hDC j hj (hji.trans (by omega)))
      have htoP : ‖iteratedFDeriv Real i Phi x‖ ≤ P :=
        hprev.trans (by
          simpa only [P] using
            isomBudget_le_of_le (E0 := E0) D
              (show i ≤ Nat.succ m by omega))
      exact htoP.trans
        (le_self_pow₀ (one_le_isomEnv (E0 := E0) D (Nat.succ m)) (by omega))
    have hstep := isom_next_le B C Phi x m D P
      (hBsm.of_le (WithTop.coe_le_coe.mpr le_top))
      (hCsm.of_le (WithTop.coe_le_coe.mpr le_top))
      (hPhi.of_le (WithTop.coe_le_coe.mpr le_top))
      hBlower hClower
      (fun i hi him => hDB i hi (him.trans (by omega)))
      (fun i hi him => hDC i hi (him.trans (by omega)))
      hPjets heq
    simpa only [P, isomBudget_succ, Nat.succ_eq_add_one] using hstep

set_option linter.style.setOption false in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 1200000 in


private theorem isom_pos_deriv_le
    [CompleteSpace E0]
    (B C : E0 → E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 → E0) (x : E0) (D : Real)
    (hBsm : ContDiffAt Real (⊤ : ℕ∞) B x)
    (hCsm : ContDiffAt Real (⊤ : ℕ∞) C (Phi x))
    (hPhi : ContDiffAt Real (⊤ : ℕ∞) Phi x)
    (hBupper : ∀ q : E0, B x q q ≤ 2 * ‖q‖ ^ 2)
    (hmetric : ∀ q : E0,
      C (Phi x) (fderiv Real Phi x q) (fderiv Real Phi x q) = B x q q)
    (hBlower : ∀ᶠ y in nhds x, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B y q q)
    (hClower : ∀ᶠ y in nhds (Phi x), ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q)
    (hDB : ∀ i, 1 ≤ i → ‖iteratedFDeriv Real i B x‖ ≤ D ^ i)
    (hDC : ∀ i, 1 ≤ i → ‖iteratedFDeriv Real i C (Phi x)‖ ≤ D ^ i)
    (heq : fderiv Real (fderiv Real Phi) =ᶠ[nhds x] fun y =>
      postBilin (fderiv Real Phi y)
          (raisedKoszulOp (B y) (fderiv Real B y)) -
        preBilin
          (raisedKoszulOp (C (Phi y)) (fderiv Real C (Phi y)))
          (fderiv Real Phi y)) :
    ∀ r, 1 ≤ r →
      ‖iteratedFDeriv Real r Phi x‖ ≤ isomBudget (E0 := E0) D r := by
  intro r hr
  exact isom_deriv_le B C Phi x D hBsm hCsm hPhi hBupper hmetric
    hBlower hClower heq r hr (fun i hi _ => hDB i hi)
      (fun i hi _ => hDC i hi)

end Gram

set_option synthInstance.maxHeartbeats 800000 in


theorem isom_koszul
    (B : E0 -> E0 →L[Real] E0 →L[Real] Real)
    (C : F0 -> F0 →L[Real] F0 →L[Real] Real)
    (Phi : E0 -> F0) (A : E0 -> E0 →L[Real] F0) {x : E0}
    (DB : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real)
    (DC : F0 →L[Real] F0 →L[Real] F0 →L[Real] Real)
    (L : E0 →L[Real] F0) (DA : E0 →L[Real] E0 →L[Real] F0)
    (hB : HasFDerivAt B DB x) (hC : HasFDerivAt C DC (Phi x))
    (hPhi : HasFDerivAt Phi L x) (hA : HasFDerivAt A DA x)
    (hiso : ∀ᶠ y in nhds x, forall u v : E0,
      B y u v = C (Phi y) (A y u) (A y v))
    (hAx : A x = L)
    (hCsymm : forall a b : F0, C (Phi x) a b = C (Phi x) b a)
    (hDAsymm : forall a b : E0, DA a b = DA b a)
    (u v w : E0) :
    C (Phi x) (DA u v) (L w) =
      MetricKoszul.koszulCov DB u v w -
        MetricKoszul.koszulCov DC (L u) (L v) (L w) := by
  have h1 := isom_jet_one B C Phi A DB DC L DA hB hC hPhi hA hiso v w u
  have h2 := isom_jet_one B C Phi A DB DC L DA hB hC hPhi hA hiso u w v
  have h3 := isom_jet_one B C Phi A DB DC L DA hB hC hPhi hA hiso u v w
  rw [hAx] at h1 h2 h3
  rw [hDAsymm u w, hCsymm (L v) (DA w u)] at h1
  rw [hDAsymm v u, hDAsymm v w] at h2
  rw [MetricKoszul.koszulCov_apply, MetricKoszul.koszulCov_apply]
  linear_combination -(1 / 2 : Real) * h1 - (1 / 2 : Real) * h2 +
    (1 / 2 : Real) * h3



theorem second_eq_koszul
    [CompleteSpace E0] [CompleteSpace F0]
    (B : E0 →L[Real] E0 →L[Real] Real)
    (C : F0 →L[Real] F0 →L[Real] Real)
    (e : E0 ≃L[Real] F0)
    (DB : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real)
    (DC : F0 →L[Real] F0 →L[Real] F0 →L[Real] Real)
    (DA : E0 →L[Real] E0 →L[Real] F0)
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    (hisom : forall a b : E0, C (e a) (e b) = B a b)
    (hpair : forall u v w : E0,
      C (DA u v) (e w) =
        MetricKoszul.koszulCov DB u v w -
          MetricKoszul.koszulCov DC (e u) (e v) (e w))
    (u v : E0) :
    DA u v =
      e (MetricKoszul.koszulVec hBco DB u v) -
        MetricKoszul.koszulVec hCco DC (e u) (e v) := by
  let sourceKoszul := MetricKoszul.koszulVec hBco DB u v
  let targetKoszul := MetricKoszul.koszulVec hCco DC (e u) (e v)
  calc
    DA u v = hCco.sharp (C (DA u v)) := (hCco.sharp_apply _).symm
    _ = hCco.sharp (C (e sourceKoszul - targetKoszul)) := by
      congr 1
      apply ContinuousLinearMap.ext
      intro t
      obtain ⟨w, rfl⟩ := e.surjective t
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      rw [hisom]
      unfold sourceKoszul targetKoszul
      rw [MetricKoszul.apply_koszulVec, MetricKoszul.apply_koszulVec]
      exact hpair u v w
    _ = e sourceKoszul - targetKoszul := hCco.sharp_apply _



theorem second_norm_le
    [CompleteSpace E0] [CompleteSpace F0]
    (B : E0 →L[Real] E0 →L[Real] Real)
    (C : F0 →L[Real] F0 →L[Real] Real)
    (e : E0 ≃L[Real] F0)
    (DB : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real)
    (DC : F0 →L[Real] F0 →L[Real] F0 →L[Real] Real)
    (DA : E0 →L[Real] E0 →L[Real] F0)
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    (hBupper : forall q : E0, B q q <= 2 * ‖q‖ ^ 2)
    (hBlower : forall q : E0, (1 / 2 : Real) * ‖q‖ ^ 2 <= B q q)
    (hClower : forall q : F0, (1 / 2 : Real) * ‖q‖ ^ 2 <= C q q)
    (hisom : forall q : E0, C (e q) (e q) = B q q)
    {CB CC : Real} (hCB : 0 <= CB) (hCC : 0 <= CC)
    (hDB : forall a b c : E0,
      ‖DB a b c‖ <= CB * ‖a‖ * ‖b‖ * ‖c‖)
    (hDC : forall a b c : F0,
      ‖DC a b c‖ <= CC * ‖a‖ * ‖b‖ * ‖c‖)
    (hEq : forall u v : E0,
      DA u v =
        e (MetricKoszul.koszulVec hBco DB u v) -
          MetricKoszul.koszulVec hCco DC (e u) (e v))
    (u v : E0) :
    ‖DA u v‖ <= (6 * CB + 12 * CC) * ‖u‖ * ‖v‖ := by
  have he : ‖(e : E0 →L[Real] F0)‖ <= 2 :=
    opNorm_le_two B C (e : E0 →L[Real] F0) hBupper hClower hisom
  have heu : ‖e u‖ <= 2 * ‖u‖ := by
    exact (ContinuousLinearMap.le_opNorm (e : E0 →L[Real] F0) u).trans <| by
      gcongr
  have hev : ‖e v‖ <= 2 * ‖v‖ := by
    exact (ContinuousLinearMap.le_opNorm (e : E0 →L[Real] F0) v).trans <| by
      gcongr
  have hsource :
      ‖MetricKoszul.koszulVec hBco DB u v‖ <=
        3 * CB * ‖u‖ * ‖v‖ := by
    have hraw := MetricKoszul.koszulVec_norm_le hBco
      (c := (1 / 2 : Real)) (by norm_num)
      (fun q => by simpa [pow_two, mul_assoc] using hBlower q)
      DB hCB hDB u v
    norm_num at hraw
    convert hraw using 1
    ring
  have htarget :
      ‖MetricKoszul.koszulVec hCco DC (e u) (e v)‖ <=
        3 * CC * ‖e u‖ * ‖e v‖ := by
    have hraw := MetricKoszul.koszulVec_norm_le hCco
      (c := (1 / 2 : Real)) (by norm_num)
      (fun q => by simpa [pow_two, mul_assoc] using hClower q)
      DC hCC hDC (e u) (e v)
    norm_num at hraw
    convert hraw using 1
    ring
  rw [hEq]
  calc
    ‖e (MetricKoszul.koszulVec hBco DB u v) -
        MetricKoszul.koszulVec hCco DC (e u) (e v)‖ <=
        ‖e (MetricKoszul.koszulVec hBco DB u v)‖ +
          ‖MetricKoszul.koszulVec hCco DC (e u) (e v)‖ := norm_sub_le _ _
    _ <= ‖(e : E0 →L[Real] F0)‖ *
          ‖MetricKoszul.koszulVec hBco DB u v‖ +
        ‖MetricKoszul.koszulVec hCco DC (e u) (e v)‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm (e : E0 →L[Real] F0) _
    _ <= 2 * (3 * CB * ‖u‖ * ‖v‖) +
        3 * CC * ‖e u‖ * ‖e v‖ := by gcongr
    _ <= 2 * (3 * CB * ‖u‖ * ‖v‖) +
        3 * CC * (2 * ‖u‖) * (2 * ‖v‖) := by gcongr
    _ = (6 * CB + 12 * CC) * ‖u‖ * ‖v‖ := by ring



theorem isom_second_eq
    [CompleteSpace E0] [CompleteSpace F0]
    (B : E0 -> E0 →L[Real] E0 →L[Real] Real)
    (C : F0 -> F0 →L[Real] F0 →L[Real] Real)
    (Phi : E0 -> F0) (A : E0 -> E0 →L[Real] F0) {x : E0}
    (DB : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real)
    (DC : F0 →L[Real] F0 →L[Real] F0 →L[Real] Real)
    (e : E0 ≃L[Real] F0) (DA : E0 →L[Real] E0 →L[Real] F0)
    (hB : HasFDerivAt B DB x) (hC : HasFDerivAt C DC (Phi x))
    (hPhi : HasFDerivAt Phi (e : E0 →L[Real] F0) x)
    (hA : HasFDerivAt A DA x)
    (hiso : ∀ᶠ y in nhds x, forall u v : E0,
      B y u v = C (Phi y) (A y u) (A y v))
    (hAx : A x = (e : E0 →L[Real] F0))
    (hCsymm : forall a b : F0, C (Phi x) a b = C (Phi x) b a)
    (hDAsymm : forall a b : E0, DA a b = DA b a)
    (hBco : IsCoercive (B x)) (hCco : IsCoercive (C (Phi x)))
    (u v : E0) :
    DA u v =
      e (MetricKoszul.koszulVec hBco DB u v) -
        MetricKoszul.koszulVec hCco DC (e u) (e v) := by
  apply second_eq_koszul (B x) (C (Phi x)) e DB DC DA hBco hCco
  · intro a b
    have hxiso := mem_of_mem_nhds hiso
    simpa only [hAx] using (hxiso a b).symm
  · exact fun a b c => isom_koszul B C Phi A DB DC
      (e : E0 →L[Real] F0) DA hB hC hPhi hA hiso hAx hCsymm
      hDAsymm a b c




private theorem isom_second_inv
    [CompleteSpace E0] [CompleteSpace F0]
    (B : E0 -> E0 →L[Real] E0 →L[Real] Real)
    (C : F0 -> F0 →L[Real] F0 →L[Real] Real)
    (Phi : E0 -> F0) (A : E0 -> E0 →L[Real] F0) {x : E0}
    (DB : E0 →L[Real] E0 →L[Real] E0 →L[Real] Real)
    (DC : F0 →L[Real] F0 →L[Real] F0 →L[Real] Real)
    (e : E0 ≃L[Real] F0) (DA : E0 →L[Real] E0 →L[Real] F0)
    (hB : HasFDerivAt B DB x) (hC : HasFDerivAt C DC (Phi x))
    (hPhi : HasFDerivAt Phi (e : E0 →L[Real] F0) x)
    (hA : HasFDerivAt A DA x)
    (hiso : ∀ᶠ y in nhds x, forall u v : E0,
      B y u v = C (Phi y) (A y u) (A y v))
    (hAx : A x = (e : E0 →L[Real] F0))
    (hCsymm : forall a b : F0, C (Phi x) a b = C (Phi x) b a)
    (hDAsymm : forall a b : E0, DA a b = DA b a)
    (hBco : IsCoercive (B x)) (hCco : IsCoercive (C (Phi x)))
    (u v : E0) :
    DA u v =
      e (raisedKoszul (B x) DB u v) -
        raisedKoszul (C (Phi x)) DC (e u) (e v) := by
  rw [raisedKoszul_eq hBco, raisedKoszul_eq hCco]
  exact isom_second_eq B C Phi A DB DC e DA hB hC hPhi hA hiso hAx
    hCsymm hDAsymm hBco hCco u v



private theorem isom_second_field
    [FiniteDimensional Real E0] [CompleteSpace E0]
    (B C : E0 -> E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 -> E0) {x : E0}
    (hBsm : ContDiffAt Real 1 B x)
    (hCsm : ContDiffAt Real 1 C (Phi x))
    (hPhi : ContDiffAt Real 2 Phi x)
    (hiso : ∀ᶠ y in nhds x, forall u v : E0,
      B y u v = C (Phi y) (fderiv Real Phi y u) (fderiv Real Phi y v))
    (hCsymm : forall a b : E0, C (Phi x) a b = C (Phi x) b a)
    (hBlower : forall q : E0, (1 / 2 : Real) * ‖q‖ ^ 2 <= B x q q)
    (hClower : forall q : E0, (1 / 2 : Real) * ‖q‖ ^ 2 <= C (Phi x) q q)
    (u v : E0) :
    fderiv Real (fderiv Real Phi) x u v =
      fderiv Real Phi x
          (raisedKoszul (B x) (fderiv Real B x) u v) -
        raisedKoszul (C (Phi x)) (fderiv Real C (Phi x))
          (fderiv Real Phi x u) (fderiv Real Phi x v) := by
  let L := fderiv Real Phi x
  have hmetric : forall q : E0, C (Phi x) (L q) (L q) = B x q q := by
    intro q
    exact (mem_of_mem_nhds hiso q q).symm
  have hLinj : Function.Injective L :=
    isom_injective (B x) (C (Phi x)) L hBlower hmetric
  have hLsurj : Function.Surjective L := LinearMap.surjective_of_injective hLinj
  let e : E0 ≃L[Real] E0 := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hLinj) (LinearMap.range_eq_top.mpr hLsurj)
  have hBderiv : HasFDerivAt B (fderiv Real B x) x :=
    hBsm.differentiableAt one_ne_zero |>.hasFDerivAt
  have hCderiv : HasFDerivAt C (fderiv Real C (Phi x)) (Phi x) :=
    hCsm.differentiableAt one_ne_zero |>.hasFDerivAt
  have hPhiDeriv : HasFDerivAt Phi (e : E0 →L[Real] E0) x := by
    simpa only [e, L, ContinuousLinearEquiv.coe_ofBijective] using
      hPhi.differentiableAt (by norm_num) |>.hasFDerivAt
  have hAderiv : HasFDerivAt (fderiv Real Phi)
      (fderiv Real (fderiv Real Phi) x) x :=
    (hPhi.fderiv_right (show (1 : WithTop ENat) + 1 <= 2 by norm_num)).differentiableAt
      one_ne_zero |>.hasFDerivAt
  have hAsymm : forall a b : E0,
      fderiv Real (fderiv Real Phi) x a b =
        fderiv Real (fderiv Real Phi) x b a :=
    hPhi.isSymmSndFDerivAt (by norm_num)
  have hBco : IsCoercive (B x) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro q
    simpa [pow_two, mul_assoc] using hBlower q
  have hCco : IsCoercive (C (Phi x)) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro q
    simpa [pow_two, mul_assoc] using hClower q
  simpa only [e, L, ContinuousLinearEquiv.coe_ofBijective] using
    isom_second_inv B C Phi (fderiv Real Phi)
      (fderiv Real B x) (fderiv Real C (Phi x)) e
      (fderiv Real (fderiv Real Phi) x)
      hBderiv hCderiv hPhiDeriv hAderiv hiso
      (by simp only [e, L, ContinuousLinearEquiv.coe_ofBijective])
      hCsymm hAsymm hBco hCco u v



private theorem isom_second_op
    [FiniteDimensional Real E0] [CompleteSpace E0]
    (B C : E0 -> E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 -> E0) {x : E0}
    (hBsm : ContDiffAt Real 1 B x)
    (hCsm : ContDiffAt Real 1 C (Phi x))
    (hPhi : ContDiffAt Real 2 Phi x)
    (hiso : ∀ᶠ y in nhds x, forall u v : E0,
      B y u v = C (Phi y) (fderiv Real Phi y u) (fderiv Real Phi y v))
    (hCsymm : forall a b : E0, C (Phi x) a b = C (Phi x) b a)
    (hBlower : forall q : E0, (1 / 2 : Real) * ‖q‖ ^ 2 <= B x q q)
    (hClower : forall q : E0, (1 / 2 : Real) * ‖q‖ ^ 2 <= C (Phi x) q q) :
    fderiv Real (fderiv Real Phi) x =
      postBilin (fderiv Real Phi x)
          (raisedKoszulOp (B x) (fderiv Real B x)) -
        preBilin (raisedKoszulOp (C (Phi x)) (fderiv Real C (Phi x)))
          (fderiv Real Phi x) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sub_apply, postBilin_apply, preBilin_apply,
    raisedKoszulOp_apply]
  exact isom_second_field B C Phi hBsm hCsm hPhi hiso hCsymm
    hBlower hClower u v




private theorem isom_second_on
    [FiniteDimensional Real E0] [CompleteSpace E0]
    (B C : E0 -> E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 -> E0) (U V : Set E0)
    (hU : IsOpen U) (hV : IsOpen V)
    (hBsm : ContDiffOn Real 1 B U)
    (hCsm : ContDiffOn Real 1 C V)
    (hPhi : ContDiffOn Real 2 Phi U)
    (hmap : Set.MapsTo Phi U V)
    (hiso : ∀ x ∈ U, ∀ u v : E0,
      B x u v = C (Phi x) (fderiv Real Phi x u) (fderiv Real Phi x v))
    (hCsymm : ∀ y ∈ V, ∀ a b : E0, C y a b = C y b a)
    (hBlower : ∀ x ∈ U, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B x q q)
    (hClower : ∀ y ∈ V, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q) :
    ∀ x ∈ U,
      fderiv Real (fderiv Real Phi) x =
        postBilin (fderiv Real Phi x)
            (raisedKoszulOp (B x) (fderiv Real B x)) -
          preBilin (raisedKoszulOp (C (Phi x)) (fderiv Real C (Phi x)))
            (fderiv Real Phi x) := by
  intro x hx
  have hPhiV : Phi x ∈ V := hmap hx
  have hiso_nhds : ∀ᶠ y in nhds x, ∀ u v : E0,
      B y u v = C (Phi y) (fderiv Real Phi y u) (fderiv Real Phi y v) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hiso y hy
  exact isom_second_op B C Phi
    ((hBsm x hx).contDiffAt (hU.mem_nhds hx))
    ((hCsm (Phi x) hPhiV).contDiffAt (hV.mem_nhds hPhiV))
    ((hPhi x hx).contDiffAt (hU.mem_nhds hx))
    hiso_nhds (hCsymm (Phi x) hPhiV) (hBlower x hx)
    (hClower (Phi x) hPhiV)

section IsomBounds

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

set_option linter.style.setOption false in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 1200000 in


theorem isom_deriv_on
    [FiniteDimensional Real E0] [CompleteSpace E0]
    (B C : E0 → E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 → E0) (U V : Set E0)
    (hU : IsOpen U) (hV : IsOpen V)
    (hBsm : ContDiffOn Real (⊤ : ℕ∞) B U)
    (hCsm : ContDiffOn Real (⊤ : ℕ∞) C V)
    (hPhi : ContDiffOn Real (⊤ : ℕ∞) Phi U)
    (hmap : Set.MapsTo Phi U V)
    (hiso : ∀ x ∈ U, ∀ u v : E0,
      B x u v = C (Phi x) (fderiv Real Phi x u) (fderiv Real Phi x v))
    (hCsymm : ∀ y ∈ V, ∀ a b : E0, C y a b = C y b a)
    (hBequiv : ∀ x ∈ U, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B x q q ∧ B x q q ≤ 2 * ‖q‖ ^ 2)
    (hCequiv : ∀ y ∈ V, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C y q q ∧ C y q q ≤ 2 * ‖q‖ ^ 2)
    {r : Nat} (hr : 1 ≤ r) {D : Real}
    (hDB : ∀ i, 1 ≤ i → i ≤ r → ∀ x ∈ U,
      ‖iteratedFDeriv Real i B x‖ ≤ D ^ i)
    (hDC : ∀ i, 1 ≤ i → i ≤ r → ∀ y ∈ V,
      ‖iteratedFDeriv Real i C y‖ ≤ D ^ i)
    {x : E0} (hx : x ∈ U) :
    ‖iteratedFDeriv Real r Phi x‖ ≤ isomBudget (E0 := E0) D r := by
  have hPhiV : Phi x ∈ V := hmap hx
  have hB1 : ContDiffOn Real 1 B U := hBsm.of_le (by
    exact WithTop.coe_le_coe.mpr le_top)
  have hC1 : ContDiffOn Real 1 C V := hCsm.of_le (by
    exact WithTop.coe_le_coe.mpr le_top)
  have hPhi2 : ContDiffOn Real 2 Phi U := hPhi.of_le (by
    exact WithTop.coe_le_coe.mpr le_top)
  have hsecond := isom_second_on B C Phi U V hU hV hB1 hC1 hPhi2
    hmap hiso hCsymm (fun y hy q => (hBequiv y hy q).1)
      (fun y hy q => (hCequiv y hy q).1)
  have heq : fderiv Real (fderiv Real Phi) =ᶠ[nhds x] fun y =>
      postBilin (fderiv Real Phi y)
          (raisedKoszulOp (B y) (fderiv Real B y)) -
        preBilin
          (raisedKoszulOp (C (Phi y)) (fderiv Real C (Phi y)))
          (fderiv Real Phi y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hsecond y hy
  exact isom_deriv_le B C Phi x D
    ((hBsm x hx).contDiffAt (hU.mem_nhds hx))
    ((hCsm (Phi x) hPhiV).contDiffAt (hV.mem_nhds hPhiV))
    ((hPhi x hx).contDiffAt (hU.mem_nhds hx))
    (fun q => (hBequiv x hx q).2)
    (fun q => (hiso x hx q q).symm)
    (by
      filter_upwards [hU.mem_nhds hx] with y hy q
      exact (hBequiv y hy q).1)
    (by
      filter_upwards [hV.mem_nhds hPhiV] with y hy q
      exact (hCequiv y hy q).1)
    heq r hr (fun i hi hir => hDB i hi hir x hx)
      (fun i hi hir => hDC i hi hir (Phi x) hPhiV)

set_option linter.style.setOption false in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 1200000 in



theorem isom_bounds_on
    [FiniteDimensional Real E0] [CompleteSpace E0]
    (B C : Nat → E0 → E0 →L[Real] E0 →L[Real] Real)
    (Phi : Nat → E0 → E0) (U V : Set E0)
    (hU : IsOpen U) (hV : IsOpen V)
    (hVnorm : ∃ Z : Real, ∀ y ∈ V, ‖y‖ ≤ Z)
    (hBsm : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (B k) U)
    (hCsm : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (C k) V)
    (hPhi : ∀ k, ContDiffOn Real (⊤ : ℕ∞) (Phi k) U)
    (hmap : ∀ k, Set.MapsTo (Phi k) U V)
    (hiso : ∀ k, ∀ x ∈ U, ∀ u v : E0,
      B k x u v = C k (Phi k x)
        (fderiv Real (Phi k) x u) (fderiv Real (Phi k) x v))
    (hCsymm : ∀ k, ∀ y ∈ V, ∀ a b : E0, C k y a b = C k y b a)
    (hBequiv : ∀ k, ∀ x ∈ U, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ B k x q q ∧
        B k x q q ≤ 2 * ‖q‖ ^ 2)
    (hCequiv : ∀ k, ∀ y ∈ V, ∀ q : E0,
      (1 / 2 : Real) * ‖q‖ ^ 2 ≤ C k y q q ∧
        C k y q q ≤ 2 * ‖q‖ ^ 2)
    (CB CC : Nat → Real)
    (hCB : ∀ i, 0 ≤ CB i) (hCC : ∀ i, 0 ≤ CC i)
    (hDB : ∀ k i, ∀ x ∈ U, ‖iteratedFDeriv Real i (B k) x‖ ≤ CB i)
    (hDC : ∀ k i, ∀ y ∈ V, ‖iteratedFDeriv Real i (C k) y‖ ≤ CC i) :
    IsometryDerivBoundsOn U Phi := by
  intro r K _ hKU
  rcases r with _ | r
  · obtain ⟨Z, hZ⟩ := hVnorm
    refine ⟨Z, ?_⟩
    intro k x hx
    rw [norm_iteratedFDeriv_zero]
    exact hZ (Phi k x) (hmap k (hKU hx))
  · let D := 1 + (Finset.range (Nat.succ r + 1)).sum (fun i => CB i + CC i)
    have hsum : 0 ≤
        (Finset.range (Nat.succ r + 1)).sum (fun i => CB i + CC i) :=
      Finset.sum_nonneg fun i _ => add_nonneg (hCB i) (hCC i)
    have hDone : 1 ≤ D := by
      dsimp only [D]
      linarith
    have hCB_D : ∀ i, i ≤ Nat.succ r → CB i ≤ D := by
      intro i hi
      have himem : i ∈ Finset.range (Nat.succ r + 1) :=
        Finset.mem_range.mpr (by omega)
      have hterm : CB i + CC i ≤
          (Finset.range (Nat.succ r + 1)).sum (fun j => CB j + CC j) :=
        Finset.single_le_sum
          (fun j _ => add_nonneg (hCB j) (hCC j)) himem
      dsimp only [D]
      linarith [hCC i]
    have hCC_D : ∀ i, i ≤ Nat.succ r → CC i ≤ D := by
      intro i hi
      have himem : i ∈ Finset.range (Nat.succ r + 1) :=
        Finset.mem_range.mpr (by omega)
      have hterm : CB i + CC i ≤
          (Finset.range (Nat.succ r + 1)).sum (fun j => CB j + CC j) :=
        Finset.single_le_sum
          (fun j _ => add_nonneg (hCB j) (hCC j)) himem
      dsimp only [D]
      linarith [hCB i]
    refine ⟨isomBudget (E0 := E0) D (Nat.succ r), ?_⟩
    intro k x hx
    have hxU : x ∈ U := hKU hx
    apply isom_deriv_on (B k) (C k) (Phi k) U V hU hV
      (hBsm k) (hCsm k) (hPhi k) (hmap k) (hiso k) (hCsymm k)
      (hBequiv k) (hCequiv k) (by omega : 1 ≤ Nat.succ r)
      (D := D)
    · intro i hi hir y hy
      exact (hDB k i y hy).trans <|
        (hCB_D i hir).trans (le_self_pow₀ hDone (by omega))
    · intro i hi hir y hy
      exact (hDC k i y hy).trans <|
        (hCC_D i hir).trans (le_self_pow₀ hDone (by omega))
    · exact hxU

end IsomBounds



theorem isom_second_bound
    [FiniteDimensional Real E0] [CompleteSpace E0]
    (B C : E0 -> E0 →L[Real] E0 →L[Real] Real)
    (Phi : E0 -> E0) {x : E0}
    (hBsm : ContDiffAt Real 1 B x)
    (hCsm : ContDiffAt Real 1 C (Phi x))
    (hPhi : ContDiffAt Real 2 Phi x)
    (hiso : ∀ᶠ y in nhds x, forall u v : E0,
      B y u v = C (Phi y) (fderiv Real Phi y u) (fderiv Real Phi y v))
    (hCsymm : forall a b : E0, C (Phi x) a b = C (Phi x) b a)
    (hBupper : forall q : E0, B x q q <= 2 * ‖q‖ ^ 2)
    (hBlower : forall q : E0, (1 / 2 : Real) * ‖q‖ ^ 2 <= B x q q)
    (hClower : forall q : E0, (1 / 2 : Real) * ‖q‖ ^ 2 <= C (Phi x) q q)
    {CB CC : Real} (hCB : 0 <= CB) (hCC : 0 <= CC)
    (hDB : forall a b c : E0,
      ‖fderiv Real B x a b c‖ <= CB * ‖a‖ * ‖b‖ * ‖c‖)
    (hDC : forall a b c : E0,
      ‖fderiv Real C (Phi x) a b c‖ <= CC * ‖a‖ * ‖b‖ * ‖c‖) :
    ‖iteratedFDeriv Real 2 Phi x‖ <= 6 * CB + 12 * CC := by
  let L := fderiv Real Phi x
  have hmetric : forall q : E0, C (Phi x) (L q) (L q) = B x q q := by
    intro q
    exact (mem_of_mem_nhds hiso q q).symm
  have hLinj : Function.Injective L :=
    isom_injective (B x) (C (Phi x)) L hBlower hmetric
  have hLsurj : Function.Surjective L := LinearMap.surjective_of_injective hLinj
  let e : E0 ≃L[Real] E0 := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hLinj) (LinearMap.range_eq_top.mpr hLsurj)
  have hBderiv : HasFDerivAt B (fderiv Real B x) x :=
    hBsm.differentiableAt one_ne_zero |>.hasFDerivAt
  have hCderiv : HasFDerivAt C (fderiv Real C (Phi x)) (Phi x) :=
    hCsm.differentiableAt one_ne_zero |>.hasFDerivAt
  have hPhiDeriv : HasFDerivAt Phi (e : E0 →L[Real] E0) x := by
    simpa only [e, L, ContinuousLinearEquiv.coe_ofBijective] using
      hPhi.differentiableAt (by norm_num) |>.hasFDerivAt
  have hAderiv : HasFDerivAt (fderiv Real Phi)
      (fderiv Real (fderiv Real Phi) x) x :=
    (hPhi.fderiv_right (show (1 : WithTop ENat) + 1 <= 2 by norm_num)).differentiableAt
      one_ne_zero |>.hasFDerivAt
  have hAsymm : forall a b : E0,
      fderiv Real (fderiv Real Phi) x a b =
        fderiv Real (fderiv Real Phi) x b a :=
    hPhi.isSymmSndFDerivAt (by norm_num)
  have hBco : IsCoercive (B x) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro q
    simpa [pow_two, mul_assoc] using hBlower q
  have hCco : IsCoercive (C (Phi x)) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro q
    simpa [pow_two, mul_assoc] using hClower q
  have hEq : forall u v : E0,
      fderiv Real (fderiv Real Phi) x u v =
        e (MetricKoszul.koszulVec hBco (fderiv Real B x) u v) -
          MetricKoszul.koszulVec hCco (fderiv Real C (Phi x)) (e u) (e v) := by
    intro u v
    apply isom_second_eq B C Phi (fderiv Real Phi)
      (fderiv Real B x) (fderiv Real C (Phi x)) e
      (fderiv Real (fderiv Real Phi) x)
      hBderiv hCderiv hPhiDeriv hAderiv hiso
      (by simp only [e, L, ContinuousLinearEquiv.coe_ofBijective])
      hCsymm hAsymm hBco hCco u v
  have hsecond : ‖fderiv Real (fderiv Real Phi) x‖ <=
      6 * CB + 12 * CC := by
    apply opNorm₂_le (fderiv Real (fderiv Real Phi) x)
      (add_nonneg (mul_nonneg (by norm_num) hCB) (mul_nonneg (by norm_num) hCC))
    intro u v
    exact second_norm_le (B x) (C (Phi x)) e
      (fderiv Real B x) (fderiv Real C (Phi x))
      (fderiv Real (fderiv Real Phi) x) hBco hCco hBupper hBlower hClower
      hmetric hCB hCC hDB hDC hEq u v
  calc
    ‖iteratedFDeriv Real 2 Phi x‖ =
        ‖iteratedFDeriv Real 1 (fderiv Real Phi) x‖ :=
      (norm_iteratedFDeriv_fderiv (𝕜 := Real) (f := Phi) (x := x) (n := 1)).symm
    _ = ‖fderiv Real (fderiv Real Phi) x‖ :=
      norm_iteratedFDeriv_one (𝕜 := Real) (fderiv Real Phi)
    _ <= 6 * CB + 12 * CC := hsecond

noncomputable section

universe u uE uH

variable {E' : Type uE} [NormedAddCommGroup E']
  [InnerProductSpace Real E'] [FiniteDimensional Real E']
  [NeZero (Module.finrank Real E')] [CompleteSpace E']
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E' H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [NeZero (Module.finrank Real E')] in
theorem normalTrans_isom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    forall {z : E'},
      z ∈ (expMapDiffeo (I := I) Y.metric x).source ->
      expMapDiffeo (I := I) Y.metric x z ∈
        (normalChartAt (I := I) Y.metric y).source ->
      forall u v : E',
        normalCoordMetric (I := I) Y y (normalTransition (I := I) Y x y z)
            (fderiv Real (normalTransition (I := I) Y x y) z u)
            (fderiv Real (normalTransition (I := I) Y x y) z v) =
          normalCoordMetric (I := I) Y x z u v := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hzx hzy u v
  have hw : normalTransition (I := I) Y x y z ∈
      (expMapDiffeo (I := I) Y.metric y).source := by
    rw [← normalChartAt_target_eq (I := I)]
    change normalChartAt (I := I) Y.metric y
      (expMapDiffeo (I := I) Y.metric x z) ∈
        (normalChartAt (I := I) Y.metric y).target
    exact (normalChartAt (I := I) Y.metric y).map_source hzy
  have hbase :
      expMapDiffeo (I := I) Y.metric y
          (normalTransition (I := I) Y x y z) =
        expMapDiffeo (I := I) Y.metric x z := by
    change (normalChartAt (I := I) Y.metric y).symm
        (normalChartAt (I := I) Y.metric y
          (expMapDiffeo (I := I) Y.metric x z)) =
      expMapDiffeo (I := I) Y.metric x z
    exact (normalChartAt (I := I) Y.metric y).left_inv hzy
  have hdx : MDifferentiableAt 𝓘(Real, E') I
      (expMapDiffeo (I := I) Y.metric x) z :=
    ((expMapDiffeo (I := I) Y.metric x).contMDiffOn_toFun.mdifferentiableOn
      one_ne_zero z hzx).mdifferentiableAt
        ((expMapDiffeo (I := I) Y.metric x).open_source.mem_nhds hzx)
  have hcy : MDifferentiableAt I 𝓘(Real, E')
      (normalChartAt (I := I) Y.metric y)
      (expMapDiffeo (I := I) Y.metric x z) :=
    ((normalChartAt (I := I) Y.metric y).contMDiffOn_toFun.mdifferentiableOn
      one_ne_zero _ hzy).mdifferentiableAt
        ((normalChartAt (I := I) Y.metric y).open_source.mem_nhds hzy)
  have hT : MDifferentiableAt 𝓘(Real, E') 𝓘(Real, E')
      (normalTransition (I := I) Y x y) z := by
    simpa only [normalTransition, Function.comp_apply] using hcy.comp z hdx
  have hdy : MDifferentiableAt 𝓘(Real, E') I
      (expMapDiffeo (I := I) Y.metric y)
      (normalTransition (I := I) Y x y z) :=
    ((expMapDiffeo (I := I) Y.metric y).contMDiffOn_toFun.mdifferentiableOn
      one_ne_zero _ hw).mdifferentiableAt
        ((expMapDiffeo (I := I) Y.metric y).open_source.mem_nhds hw)
  have hnear : ∀ᶠ q in nhds z,
      expMapDiffeo (I := I) Y.metric x q ∈
        (normalChartAt (I := I) Y.metric y).source :=
    hdx.continuousAt.eventually
      ((normalChartAt (I := I) Y.metric y).open_source.mem_nhds hzy)
  have heq :
      (expMapDiffeo (I := I) Y.metric y) ∘
          (normalTransition (I := I) Y x y) =ᶠ[nhds z]
        expMapDiffeo (I := I) Y.metric x := by
    filter_upwards [hnear] with q hq
    change (normalChartAt (I := I) Y.metric y).symm
        (normalChartAt (I := I) Y.metric y
          (expMapDiffeo (I := I) Y.metric x q)) =
      expMapDiffeo (I := I) Y.metric x q
    exact (normalChartAt (I := I) Y.metric y).left_inv hq
  have hcomp :
      (mfderiv 𝓘(Real, E') I
          (fun q : E' => expMapDiffeo (I := I) Y.metric y q)
          (normalTransition (I := I) Y x y z)).comp
          (mfderiv 𝓘(Real, E') 𝓘(Real, E')
            (normalTransition (I := I) Y x y) z) =
        mfderiv 𝓘(Real, E') I
          (fun q : E' => expMapDiffeo (I := I) Y.metric x q) z := by
    have hderiv := Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(Real, E')) (I' := I) heq
    rw [mfderiv_comp z hdy hT] at hderiv
    simpa only using hderiv
  rw [normalCoordMetric_apply (I := I), normalCoordMetric_apply (I := I), hbase]
  have hu := DFunLike.congr_fun hcomp u
  have hv := DFunLike.congr_fun hcomp v
  rw [mfderiv_eq_fderiv (𝕜 := Real) (E := E') (E' := E')
    (f := normalTransition (I := I) Y x y) (x := z)] at hu hv
  change (mfderiv 𝓘(Real, E') I
      (fun q : E' => expMapDiffeo (I := I) Y.metric y q)
      (normalTransition (I := I) Y x y z))
        (fderiv Real (normalTransition (I := I) Y x y) z u) =
      mfderiv 𝓘(Real, E') I
        (fun q : E' => expMapDiffeo (I := I) Y.metric x q) z u at hu
  change (mfderiv 𝓘(Real, E') I
      (fun q : E' => expMapDiffeo (I := I) Y.metric y q)
      (normalTransition (I := I) Y x y z))
        (fderiv Real (normalTransition (I := I) Y x y) z v) =
      mfderiv 𝓘(Real, E') I
        (fun q : E' => expMapDiffeo (I := I) Y.metric x q) z v at hv
  exact congrArg₂
    (fun a b => Y.metric.inner (expMapDiffeo (I := I) Y.metric x z) a b) hu hv



omit [NeZero (Module.finrank Real E')] in
theorem normal_fderiv_bij
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U : Set E'} (hx : NormalCoordMetricEquivOn (I := I) Y x U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    forall {z : E'},
      z ∈ (expMapDiffeo (I := I) Y.metric x).source ->
      expMapDiffeo (I := I) Y.metric x z ∈
        (normalChartAt (I := I) Y.metric y).source ->
      z ∈ U ->
      Function.Bijective
        (fderiv Real (normalTransition (I := I) Y x y) z) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hzx hzy hzU
  have hinj : Function.Injective
      (fderiv Real (normalTransition (I := I) Y x y) z) :=
    isom_injective
      (normalCoordMetric (I := I) Y x z)
      (normalCoordMetric (I := I) Y y
        (normalTransition (I := I) Y x y z))
      (fderiv Real (normalTransition (I := I) Y x y) z)
      (fun v => (hx z hzU v).1)
      (fun v => normalTrans_isom Y x y hzx hzy v v)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩



omit [NeZero (Module.finrank Real E')] in
theorem normal_fderiv_le_two
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E'}
    (hx : NormalCoordMetricEquivOn (I := I) Y x U)
    (hy : NormalCoordMetricEquivOn (I := I) Y y V) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    forall {z : E'},
      z ∈ (expMapDiffeo (I := I) Y.metric x).source ->
      expMapDiffeo (I := I) Y.metric x z ∈
        (normalChartAt (I := I) Y.metric y).source ->
      z ∈ U ->
      normalTransition (I := I) Y x y z ∈ V ->
      ‖fderiv Real (normalTransition (I := I) Y x y) z‖ <= 2 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro z hzx hzy hzU hzV
  exact opNorm_le_two
    (normalCoordMetric (I := I) Y x z)
    (normalCoordMetric (I := I) Y y (normalTransition (I := I) Y x y z))
    (fderiv Real (normalTransition (I := I) Y x y) z)
    (fun v => (hx z hzU v).2)
    (fun w => (hy (normalTransition (I := I) Y x y z) hzV w).1)
    (fun v => normalTrans_isom Y x y hzx hzy v v)

section NormalBounds

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

set_option linter.style.setOption false in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 1200000 in


theorem normal_bounds_on
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (h : NormalCoordMetricBoundInput (I := I) X)
    (x y : ∀ k, (X.obj k).M) (U V : Set E')
    (hU : IsOpen U) (hV : IsOpen V)
    (hVnorm : ∃ Z : Real, ∀ z ∈ V, ‖z‖ ≤ Z)
    (hUmetric : ∀ k,
      U ⊆ Metric.ball (0 : E') (h.radius k (x k)))
    (hVmetric : ∀ k,
      V ⊆ Metric.ball (0 : E') (h.radius k (y k)))
    (hUexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      U ⊆ Metric.ball (0 : E')
        (expMapC2Radius (I := I) (X.obj k).metric (x k)))
    (hVexp : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      V ⊆ Metric.ball (0 : E')
        (expMapC2Radius (I := I) (X.obj k).metric (y k)))
    (hPhi : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (x k) (y k)) U)
    (hovl : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      ∀ z ∈ U,
        z ∈ (expMapDiffeo (I := I) (X.obj k).metric (x k)).source ∧
          expMapDiffeo (I := I) (X.obj k).metric (x k) z ∈
            (normalChartAt (I := I) (X.obj k).metric (y k)).source)
    (hmap : ∀ k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (x k) (y k)) U V) :
    IsometryDerivBoundsOn U
      (fun k => normalTransition (I := I) (X.obj k) (x k) (y k)) := by
  apply isom_bounds_on
    (CB := h.metricC) (CC := h.metricC)
    (fun k => normalCoordMetric (I := I) (X.obj k) (x k))
    (fun k => normalCoordMetric (I := I) (X.obj k) (y k))
    (fun k => normalTransition (I := I) (X.obj k) (x k) (y k))
    U V hU hV hVnorm
  · intro k
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    exact (normalCoordMetric_contDiffOn_expBall (I := I) (X.obj k) (x k)).mono
      (hUexp k)
  · intro k
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    exact (normalCoordMetric_contDiffOn_expBall (I := I) (X.obj k) (y k)).mono
      (hVexp k)
  · exact hPhi
  · exact hmap
  · intro k z hz u v
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    exact (normalTrans_isom (X.obj k) (x k) (y k)
      (hovl k z hz).1 (hovl k z hz).2 u v).symm
  · intro k z _ a b
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    rw [normalCoordMetric_apply (I := I), normalCoordMetric_apply (I := I)]
    exact (X.obj k).metric.symm _ _ _
  · intro k z hz q
    exact h.metric_equiv k (x k) z (hUmetric k hz) q
  · intro k z hz q
    exact h.metric_equiv k (y k) z (hVmetric k hz) q
  · exact h.metricC_nonneg
  · exact h.metricC_nonneg
  · intro k i z hz
    exact h.metric_deriv k i (x k) z (hUmetric k hz)
  · intro k i z hz
    exact h.metric_deriv k i (y k) z (hVmetric k hz)

end NormalBounds

end

end H6Isometry
end HCGCompactness
end DifferentialGeometry
