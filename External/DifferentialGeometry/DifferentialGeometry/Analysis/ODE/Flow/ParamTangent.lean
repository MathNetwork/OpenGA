import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp
import DifferentialGeometry.Analysis.Calculus.MapConvergenceDeriv
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute
import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import DifferentialGeometry.Analysis.ODE.Flow.HigherRegularity.VariationalMapContDiffOnK

set_option autoImplicit false









noncomputable section

open Function Set
open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow



def paramTangentVF
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) :
    ℝ → (X × (P →L[ℝ] X)) → X × (P →L[ℝ] X) :=
  fun t z => (v t z.1, (fderiv ℝ (v t) z.1).comp z.2)


def paramTangentInit
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : P → X) (p : P) : X × (P →L[ℝ] X) :=
  (a p, fderiv ℝ a p)



def paramTangentCurve
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (γ : P → ℝ → X) (p : P) (t : ℝ) : X × (P →L[ℝ] X) :=
  (γ p t, fderiv ℝ (fun q => γ q t) p)



theorem paramTangentInit_contDiffOn
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} (hA : IsOpen A) {a : P → X}
    (ha : ContDiffOn ℝ ∞ a A) :
    ContDiffOn ℝ ∞ (paramTangentInit a) A := by
  have hDa : ContDiffOn ℝ ∞ (fun p => fderiv ℝ a p) A :=
    ha.fderiv_of_isOpen hA (by exact_mod_cast le_top)
  exact ha.prodMk hDa



@[simp]
theorem paramTangentVF_apply
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) (t : ℝ) (x : X) (Z : P →L[ℝ] X) :
    paramTangentVF P v t (x, Z) = (v t x, (fderiv ℝ (v t) x).comp Z) := rfl



theorem paramTangentVF_contDiffOn
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {J : Set ℝ} (hJ : IsOpen J) {V : Set X} (hV : IsOpen V)
    {v : ℝ → X → X}
    (hv : ContDiffOn ℝ ∞ (uncurry v) (J ×ˢ V)) :
    ContDiffOn ℝ ∞ (uncurry (paramTangentVF P v))
      (J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X)))) := by
  let D : Set (ℝ × (X × (P →L[ℝ] X))) :=
    J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X)))
  let proj : ℝ × (X × (P →L[ℝ] X)) → ℝ × X := fun q => (q.1, q.2.1)
  have hproj : ContDiffOn ℝ ∞ proj D :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd) |>.contDiffOn
  have hprojMap : MapsTo proj D (J ×ˢ V) := fun _ hq => ⟨hq.1, hq.2.1⟩
  have hfirst : ContDiffOn ℝ ∞ (fun q : ℝ × (X × (P →L[ℝ] X)) =>
      v q.1 q.2.1) D := by
    exact hv.comp hproj hprojMap
  have hpartial : ContDiffOn ℝ ∞
      (fun q : ℝ × X => fderiv ℝ (v q.1) q.2) (J ×ˢ V) := by
    apply contDiffOn_partial_fderiv_of_succ_local (hJ.prod hV)
    simpa only [top_add] using hv
  have hA : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) => fderiv ℝ (v q.1) q.2.1) D :=
    hpartial.comp hproj hprojMap
  have hZ : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) => q.2.2) D :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hpair : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) =>
        (fderiv ℝ (v q.1) q.2.1, q.2.2)) D :=
    hA.prodMk hZ
  have hcomp : ContDiff ℝ ∞
      (fun q : (X →L[ℝ] X) × (P →L[ℝ] X) => q.1.comp q.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := P) (F := X) (G := X)).contDiff
  have hsecond : ContDiffOn ℝ ∞
      (fun q : ℝ × (X × (P →L[ℝ] X)) =>
        (fderiv ℝ (v q.1) q.2.1).comp q.2.2) D := by
    exact hcomp.contDiffOn.comp hpair (fun _ _ => mem_univ _)
  exact hfirst.prodMk hsecond




theorem paramTangentCurve_initial
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Set P} (hA : IsOpen A) {t₀ : ℝ}
    {a : P → X} {γ : P → ℝ → X}
    (hγ : ∀ p ∈ A, γ p t₀ = a p) {p : P} (hp : p ∈ A) :
    paramTangentCurve γ p t₀ = paramTangentInit a p := by
  have heq : (fun q => γ q t₀) =ᶠ[nhds p] a :=
    Filter.eventuallyEq_of_mem (hA.mem_nhds hp) hγ
  simp only [paramTangentCurve, paramTangentInit, hγ p hp, heq.fderiv_eq]




theorem paramTangentCurve_initial_isIntegralCurveOn
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} (hA : IsOpen A)
    {J : Set ℝ} (hJ : IsOpen J)
    {V : Set X} (hV : IsOpen V)
    {t₀ t₁ : ℝ} (ht₀₁ : t₀ ≤ t₁) (hI : Icc t₀ t₁ ⊆ J)
    {v : ℝ → X → X}
    (hv : ContDiffOn ℝ ∞ (uncurry v) (J ×ˢ V))
    {a : P → X} (ha : ContDiffOn ℝ ∞ a A)
    {γ : P → ℝ → X}
    (hγ : ∀ p, p ∈ A →
      γ p t₀ = a p ∧ IsIntegralCurveOn (γ p) v (Icc t₀ t₁))
    (hstay : ∀ p ∈ A, ∀ t ∈ Icc t₀ t₁, γ p t ∈ V) :
    ∀ p ∈ A,
      paramTangentCurve γ p t₀ = paramTangentInit a p ∧
      IsIntegralCurveOn (paramTangentCurve γ p) (paramTangentVF P v)
        (Icc t₀ t₁) := by
  have hγjoint : ContDiffOn ℝ ∞ (uncurry γ) (A ×ˢ Icc t₀ t₁) :=
    contDiffOn_solutionFamily_of_stays hJ hV hv hA hI ha hγ
      (fun p hp t ht => hstay p hp t ht)
  intro p hp
  refine ⟨paramTangentCurve_initial hA (fun q hq => (hγ q hq).1) hp, ?_⟩
  rcases ht₀₁.eq_or_lt with rfl | ht₀₁
  · intro t ht
    have ht : t = t₀ := by simpa only [Icc_self, mem_singleton_iff] using ht
    subst t
    simpa only [Icc_self] using
      (HasFDerivWithinAt.singleton :
        HasDerivWithinAt (paramTangentCurve γ p)
          (paramTangentVF P v t₀ (paramTangentCurve γ p t₀)) {t₀} t₀)
  · let G : ℝ → P → X := fun t q => γ q t
    let swap : ℝ × P → P × ℝ := fun q => (q.2, q.1)
    have hswap_cd : ContDiffOn ℝ ∞ swap (Icc t₀ t₁ ×ˢ A) :=
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    have hswap_maps : MapsTo swap (Icc t₀ t₁ ×ˢ A)
        (A ×ˢ Icc t₀ t₁) := fun _ hq => ⟨hq.2, hq.1⟩
    have hG : ContDiffOn ℝ ∞ (uncurry G) (Icc t₀ t₁ ×ˢ A) := by
      simpa only [G, swap, uncurry_apply_pair] using
        hγjoint.comp hswap_cd hswap_maps
    have hUD : UniqueDiffOn ℝ (Icc t₀ t₁) := uniqueDiffOn_Icc ht₀₁
    have hsacc : Icc t₀ t₁ ⊆ closure (interior (Icc t₀ t₁)) := by
      rw [closure_interior_Icc (ne_of_lt ht₀₁)]
    have hDG : ContDiffOn ℝ ∞
        (uncurry (fun t q => fderiv ℝ (G t) q)) (Icc t₀ t₁ ×ˢ A) :=
      DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn hUD hA hG
    intro t ht
    have hZslice : ContDiffOn ℝ ∞
        (fun s => fderiv ℝ (fun q => γ q s) p) (Icc t₀ t₁) := by
      simpa only [G, uncurry_apply_pair] using
        hDG.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun s hs => ⟨hs, hp⟩)
    have hZderiv : HasDerivWithinAt
        (fun s => fderiv ℝ (fun q => γ q s) p)
        (derivWithin (fun s => fderiv ℝ (fun q => γ q s) p)
          (Icc t₀ t₁) t)
        (Icc t₀ t₁) t :=
      (hZslice.differentiableOn (by simp) t ht).hasDerivWithinAt
    have hcomm := DifferentialGeometry.Analysis.fderiv_derivWithin_time_comm
      hUD hsacc hA ht hp hG
    have hevol : Set.EqOn
        (fun q => derivWithin (fun s => γ q s) (Icc t₀ t₁) t)
        (fun q => v t (γ q t)) A := by
      intro q hq
      exact ((hγ q hq).2 t ht).derivWithin (hUD t ht)
    have hevol_nhds :
        (fun q => derivWithin (fun s => γ q s) (Icc t₀ t₁) t)
          =ᶠ[nhds p] (fun q => v t (γ q t)) :=
      Filter.eventuallyEq_of_mem (hA.mem_nhds hp) hevol
    have hγslice : ContDiffOn ℝ ∞ (fun q => γ q t) A := by
      exact hγjoint.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun q hq => ⟨hq, ht⟩)
    have hγdiff : DifferentiableAt ℝ (fun q => γ q t) p :=
      (hγslice.contDiffAt (hA.mem_nhds hp)).differentiableAt (by simp)
    have hv_slice : ContDiffOn ℝ ∞ (v t) V := by
      exact hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x hx => ⟨hI ht, hx⟩)
    have hvdiff : DifferentiableAt ℝ (v t) (γ p t) :=
      (hv_slice.contDiffAt (hV.mem_nhds (hstay p hp t ht))).differentiableAt (by simp)
    have hchain : fderiv ℝ (fun q => v t (γ q t)) p =
        (fderiv ℝ (v t) (γ p t)).comp
          (fderiv ℝ (fun q => γ q t) p) := by
      simpa only [comp_apply] using fderiv_comp p hvdiff hγdiff
    have hZeq :
        derivWithin (fun s => fderiv ℝ (fun q => γ q s) p)
            (Icc t₀ t₁) t =
          (fderiv ℝ (v t) (γ p t)).comp
            (fderiv ℝ (fun q => γ q t) p) := by
      rw [← hcomm, hevol_nhds.fderiv_eq, hchain]
    have hstate := (hγ p hp).2 t ht
    simpa only [paramTangentCurve, paramTangentVF] using
      hstate.prodMk (hZderiv.congr_deriv hZeq)

end Flow
end ODE
end Analysis

namespace HCGCompactness

open Set
open scoped ContDiff



theorem MapCInfConvOnCompacts.paramTangentInit
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} (hA : IsOpen A)
    {a : ℕ → P → X} {aInf : P → X}
    (ha_cd : ∀ n, ContDiffOn ℝ ∞ (a n) A)
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_conv : MapCInfConvOnCompacts A a aInf) :
    MapCInfConvOnCompacts A
      (fun n p => Analysis.ODE.Flow.paramTangentInit (a n) p)
      (fun p => Analysis.ODE.Flow.paramTangentInit aInf p) := by
  have hderiv_conv : MapCInfConvOnCompacts A
      (fun n p => fderiv ℝ (a n) p) (fun p => fderiv ℝ aInf p) :=
    MapCInfConvOnCompacts.fderivOn hA ha_conv ha_cd haInf_cd
  have hderiv_cd : ∀ n, ContDiffOn ℝ ∞ (fun p => fderiv ℝ (a n) p) A :=
    fun n => (ha_cd n).fderiv_of_isOpen hA (by exact_mod_cast le_top)
  have hderivInf_cd : ContDiffOn ℝ ∞ (fun p => fderiv ℝ aInf p) A :=
    haInf_cd.fderiv_of_isOpen hA (by exact_mod_cast le_top)
  simpa only [Analysis.ODE.Flow.paramTangentInit] using
    mapCInfConv_prodMk hA ha_conv hderiv_conv ha_cd haInf_cd
      hderiv_cd hderivInf_cd



theorem MapCInfConvOnCompacts.paramTangentVF
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {J : Set ℝ} (hJ : IsOpen J) {V : Set X} (hV : IsOpen V)
    {v : ℕ → ℝ → X → X} {vInf : ℝ → X → X}
    (hv_cd : ∀ n, ContDiffOn ℝ ∞ (uncurry (v n)) (J ×ˢ V))
    (hvInf_cd : ContDiffOn ℝ ∞ (uncurry vInf) (J ×ˢ V))
    (hv_conv : MapCInfConvOnCompacts (J ×ˢ V)
      (fun n q => v n q.1 q.2) (fun q => vInf q.1 q.2)) :
    MapCInfConvOnCompacts
      (J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X))))
      (fun n q => Analysis.ODE.Flow.paramTangentVF P (v n) q.1 q.2)
      (fun q => Analysis.ODE.Flow.paramTangentVF P vInf q.1 q.2) := by
  let Ω : Set (ℝ × X) := J ×ˢ V
  let D : Set (ℝ × (X × (P →L[ℝ] X))) :=
    J ×ˢ (V ×ˢ (Set.univ : Set (P →L[ℝ] X)))
  let proj : ℝ × (X × (P →L[ℝ] X)) → ℝ × X := fun q => (q.1, q.2.1)
  have hΩ : IsOpen Ω := hJ.prod hV
  have hD : IsOpen D := hJ.prod (hV.prod isOpen_univ)
  have hproj_cd : ContDiffOn ℝ ∞ proj D :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd) |>.contDiffOn
  have hprojMap : MapsTo proj D Ω := fun _ hq => ⟨hq.1, hq.2.1⟩
  have hproj_conv : MapCInfConvOnCompacts D (fun _ : ℕ => proj) proj :=
    mapCInfConv_const proj
  have hfirst_conv : MapCInfConvOnCompacts D
      (fun n q => v n q.1 q.2.1) (fun q => vInf q.1 q.2.1) := by
    simpa only [proj] using
      (MapCInfConvOnCompacts.comp
        (U := D) (V := Ω) (B := fun _ : ℕ => proj) (Binf := proj)
        (A := fun n q => v n q.1 q.2) (Ainf := fun q => vInf q.1 q.2)
        hD hΩ hproj_conv hv_conv (fun _ => hproj_cd) hproj_cd
        hv_cd hvInf_cd hprojMap (fun _ => hprojMap))
  have hraw_conv : MapCInfConvOnCompacts Ω
      (fun n q => fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q)
      (fun q => fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q) :=
    MapCInfConvOnCompacts.fderivOn hΩ hv_conv hv_cd hvInf_cd
  have hraw_cd : ∀ n, ContDiffOn ℝ ∞
      (fun q => fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q) Ω := by
    intro n
    exact (hv_cd n).fderiv_of_isOpen hΩ (by exact_mod_cast le_top)
  have hrawInf_cd : ContDiffOn ℝ ∞
      (fun q => fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q) Ω :=
    hvInf_cd.fderiv_of_isOpen hΩ (by exact_mod_cast le_top)
  let postL : ((ℝ × X) →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
    (ContinuousLinearMap.compL ℝ X (ℝ × X) X).flip
      (ContinuousLinearMap.inr ℝ ℝ X)
  have hpartial_conv : MapCInfConvOnCompacts Ω
      (fun n q => postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q))
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q)) :=
    mapCInfConv_clm hΩ postL hraw_conv hraw_cd hrawInf_cd
  have hpartial_cd : ∀ n, ContDiffOn ℝ ∞
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q)) Ω :=
    fun n => (hraw_cd n).continuousLinearMap_comp postL
  have hpartialInf_cd : ContDiffOn ℝ ∞
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q)) Ω :=
    hrawInf_cd.continuousLinearMap_comp postL
  have hpartial_proj_conv : MapCInfConvOnCompacts D
      (fun n q => postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)))
      (fun q => postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q))) := by
    simpa only using
      (MapCInfConvOnCompacts.comp
        (U := D) (V := Ω) (B := fun _ : ℕ => proj) (Binf := proj)
        (A := fun n q => postL
          (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q))
        (Ainf := fun q => postL
          (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q))
        hD hΩ hproj_conv hpartial_conv (fun _ => hproj_cd) hproj_cd
        hpartial_cd hpartialInf_cd hprojMap (fun _ => hprojMap))
  let zproj : ℝ × (X × (P →L[ℝ] X)) → (P →L[ℝ] X) := fun q => q.2.2
  have hz_cd : ContDiffOn ℝ ∞ zproj D :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hz_conv : MapCInfConvOnCompacts D (fun _ : ℕ => zproj) zproj :=
    mapCInfConv_const zproj
  have hpair_conv : MapCInfConvOnCompacts D
      (fun n q =>
        (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q))
      (fun q =>
        (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q)) := by
    apply mapCInfConv_prodMk hD hpartial_proj_conv hz_conv
    · exact fun n => (hpartial_cd n).comp hproj_cd hprojMap
    · exact hpartialInf_cd.comp hproj_cd hprojMap
    · exact fun _ => hz_cd
    · exact hz_cd
  let compMap : (X →L[ℝ] X) × (P →L[ℝ] X) → (P →L[ℝ] X) :=
    fun q => q.1.comp q.2
  have hcomp_cd : ContDiff ℝ ∞ compMap :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := P) (F := X) (G := X)).contDiff
  have hsecond_conv : MapCInfConvOnCompacts D
      (fun n q => compMap
        (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q))
      (fun q => compMap
        (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q)) := by
    simpa only using
      (MapCInfConvOnCompacts.comp
        (U := D) (V := (Set.univ : Set ((X →L[ℝ] X) × (P →L[ℝ] X))))
        (B := fun n q =>
          (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q))
        (Binf := fun q =>
          (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q))
        (A := fun _ : ℕ => compMap) (Ainf := compMap)
        hD isOpen_univ hpair_conv (mapCInfConv_const compMap)
        (fun n => ((hpartial_cd n).comp hproj_cd hprojMap).prodMk hz_cd)
        ((hpartialInf_cd.comp hproj_cd hprojMap).prodMk hz_cd)
        (fun _ => hcomp_cd.contDiffOn) hcomp_cd.contDiffOn
        (fun _ _ => mem_univ _) (fun _ _ _ => mem_univ _))
  have hfinal : MapCInfConvOnCompacts D
      (fun n q =>
        (v n q.1 q.2.1,
          compMap
            (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q)), zproj q)))
      (fun q =>
        (vInf q.1 q.2.1,
          compMap
            (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q)), zproj q))) := by
    apply mapCInfConv_prodMk hD hfirst_conv hsecond_conv
    · intro n
      exact (hv_cd n).comp hproj_cd hprojMap
    · exact hvInf_cd.comp hproj_cd hprojMap
    · intro n
      exact hcomp_cd.contDiffOn.comp
        (((hpartial_cd n).comp hproj_cd hprojMap).prodMk hz_cd)
        (fun _ _ => mem_univ _)
    · exact hcomp_cd.contDiffOn.comp
        ((hpartialInf_cd.comp hproj_cd hprojMap).prodMk hz_cd)
        (fun _ _ => mem_univ _)
  apply hfinal.congr hD
  · intro n q hq
    have hC1 : ContDiffOn ℝ 1 (uncurry (v n)) Ω :=
      (hv_cd n).of_le (by exact_mod_cast le_top)
    have hpartial := Analysis.ODE.Flow.partial_fderiv_eq_comp_inr_on_open
      hΩ hC1 (proj q) (hprojMap hq)
    change
      (v n q.1 q.2.1, (fderiv ℝ (v n q.1) q.2.1).comp q.2.2) =
        (v n q.1 q.2.1,
          (postL (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) (proj q))).comp
            (zproj q))
    rw [hpartial]
    rfl
  · intro q hq
    have hC1 : ContDiffOn ℝ 1 (uncurry vInf) Ω :=
      hvInf_cd.of_le (by exact_mod_cast le_top)
    have hpartial := Analysis.ODE.Flow.partial_fderiv_eq_comp_inr_on_open
      hΩ hC1 (proj q) (hprojMap hq)
    change
      (vInf q.1 q.2.1, (fderiv ℝ (vInf q.1) q.2.1).comp q.2.2) =
        (vInf q.1 q.2.1,
          (postL (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) (proj q))).comp
            (zproj q))
    rw [hpartial]
    rfl

end HCGCompactness
end DifferentialGeometry
