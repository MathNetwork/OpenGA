import DifferentialGeometry.Analysis.Calculus.MapConvergenceDeriv
import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import DifferentialGeometry.Analysis.ODE.Flow.ParamTangent
import DifferentialGeometry.Analysis.ODE.Flow.Variational
import DifferentialGeometry.Analysis.ODE.TubeStability
import Mathlib.Analysis.ODE.Basic
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false










namespace DifferentialGeometry
namespace HCGCompactness

open Filter Metric Set Topology
open DifferentialGeometry.Analysis.ODE.Flow
open scoped ContDiff NNReal

universe uP uX

private theorem ode_c0_on_compact
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} {J : Set ℝ} {V : Set X}
    (hA : IsOpen A)
    (hJ : IsOpen J)
    (hV : IsOpen V)
    {t₀ t₁ : ℝ}
    (ht₀₁ : t₀ ≤ t₁)
    (hI : Set.Icc t₀ t₁ ⊆ J)
    {v : ℕ → ℝ → X → X}
    {vInf : ℝ → X → X}
    (hv_cd :
      ∀ n, ContDiffOn ℝ ∞
        (fun q : ℝ × X => v n q.1 q.2) (J ×ˢ V))
    (hvInf_cd :
      ContDiffOn ℝ ∞
        (fun q : ℝ × X => vInf q.1 q.2) (J ×ˢ V))
    (hv_conv :
      MapCInfConvOnCompacts (J ×ˢ V)
        (fun n q => v n q.1 q.2)
        (fun q => vInf q.1 q.2))
    {a : ℕ → P → X}
    {aInf : P → X}
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_conv : MapCInfConvOnCompacts A a aInf)
    {γ : ℕ → P → ℝ → X}
    {γInf : P → ℝ → X}
    (hγ :
      ∀ n p, p ∈ A →
        γ n p t₀ = a n p ∧
        IsIntegralCurveOn (γ n p) (v n) (Set.Icc t₀ t₁))
    (hγInf :
      ∀ p, p ∈ A →
        γInf p t₀ = aInf p ∧
        IsIntegralCurveOn (γInf p) vInf (Set.Icc t₀ t₁))
    (hstayInf :
      ∀ p ∈ A, ∀ t ∈ Set.Icc t₀ t₁,
        γInf p t ∈ V)
    {K : Set P}
    (hK : IsCompact K)
    (hKA : K ⊆ A) :
    TendstoUniformlyOn
        (fun n (q : P × ℝ) => γ n q.1 q.2)
        (fun q : P × ℝ => γInf q.1 q.2)
        atTop (K ×ˢ Set.Icc t₀ t₁) ∧
      ∀ᶠ n in atTop,
        ∀ p ∈ K, ∀ t ∈ Set.Icc t₀ t₁, γ n p t ∈ V := by
  by_cases hKne : K.Nonempty
  · let G : Set (ℝ × X) :=
      (fun q : P × ℝ => (q.2, γInf q.1 q.2)) ''
        (K ×ˢ Set.Icc t₀ t₁)
    have hKI : IsCompact (K ×ˢ Set.Icc t₀ t₁) :=
      hK.prod isCompact_Icc
    have hγInf_cd : ContDiffOn ℝ ∞
        (fun q : P × ℝ => γInf q.1 q.2) (A ×ˢ Set.Icc t₀ t₁) :=
      DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays
        hJ hV hvInf_cd hA hI haInf_cd hγInf
        (fun p hp t ht => hstayInf p hp t ht)
    have hγInf_cont : ContinuousOn
        (fun q : P × ℝ => γInf q.1 q.2)
        (K ×ˢ Set.Icc t₀ t₁) :=
      hγInf_cd.continuousOn.mono (Set.prod_mono hKA (Subset.rfl))
    have hgraph_cont : ContinuousOn
        (fun q : P × ℝ => (q.2, γInf q.1 q.2))
        (K ×ˢ Set.Icc t₀ t₁) :=
      continuousOn_snd.prodMk hγInf_cont
    have hG : IsCompact G := hKI.image_of_continuousOn hgraph_cont
    have hGU : G ⊆ J ×ˢ V := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨hI hq.2, hstayInf q.1 (hKA hq.1) q.2 hq.2⟩
    obtain ⟨r, hr, hrU⟩ :=
      hG.exists_cthickening_subset_open (hJ.prod hV) hGU
    let ρ : ℝ := r / 2
    have hρ : 0 < ρ := by
      dsimp [ρ]
      positivity
    have hρr : ρ ≤ r := by
      dsimp [ρ]
      linarith
    let Q : Set (ℝ × X) := cthickening ρ G
    have hQ : IsCompact Q := by
      dsimp [Q]
      exact hG.cthickening
    have hQU : Q ⊆ J ×ˢ V := by
      dsimp [Q]
      exact (cthickening_mono hρr G).trans hrU
    have ht₀I : t₀ ∈ Set.Icc t₀ t₁ := left_mem_Icc.mpr ht₀₁
    obtain ⟨p₀, hp₀⟩ := hKne
    have hGne : G.Nonempty := by
      refine ⟨(t₀, γInf p₀ t₀), ?_⟩
      exact ⟨(p₀, t₀), ⟨hp₀, ht₀I⟩, rfl⟩
    have hQne : Q.Nonempty := by
      exact hGne.mono (self_subset_cthickening G)
    have hinit : TendstoUniformlyOn
        (fun n p => γ n p t₀) (fun p => γInf p t₀) atTop K := by
      have ha0 := tendstoUniformlyOn_of_cPConv (ha_conv K hK hKA 0)
      rw [Metric.tendstoUniformlyOn_iff] at ha0 ⊢
      intro ε hε
      filter_upwards [ha0 ε hε] with n hn
      intro p hp
      rw [(hγInf p (hKA hp)).1, (hγ n p (hKA hp)).1]
      exact hn p hp
    have hfield : TendstoUniformlyOn
        (fun n (q : P × ℝ) => v n q.2 (γInf q.1 q.2))
        (fun q : P × ℝ => vInf q.2 (γInf q.1 q.2))
        atTop (K ×ˢ Set.Icc t₀ t₁) := by
      have hfieldG :=
        tendstoUniformlyOn_of_cPConv (hv_conv G hG hGU 0)
      rw [Metric.tendstoUniformlyOn_iff] at hfieldG ⊢
      intro ε hε
      filter_upwards [hfieldG ε hε] with n hn
      intro q hq
      exact hn (q.2, γInf q.1 q.2) ⟨q, hq, rfl⟩
    have hderiv_conv : MapCInfConvOnCompacts (J ×ˢ V)
        (fun n q => fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q)
        (fun q => fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q) :=
      MapCInfConvOnCompacts.fderivOn (hJ.prod hV) hv_conv hv_cd hvInf_cd
    have hderiv_unif :=
      tendstoUniformlyOn_of_cPConv (hderiv_conv Q hQ hQU 0)
    have hlimit_deriv_cont : ContinuousOn
        (fun q : ℝ × X =>
          ‖fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q‖) Q := by
      exact continuous_norm.comp_continuousOn
        ((hvInf_cd.continuousOn_fderiv_of_isOpen (hJ.prod hV) (by simp)).mono hQU)
    obtain ⟨qmax, hqmax, hmax⟩ :=
      hQ.exists_isMaxOn hQne hlimit_deriv_cont
    let M : ℝ :=
      ‖fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) qmax‖ + 1
    have hM : 0 ≤ M := by
      dsimp [M]
      positivity
    have hstage_deriv : ∀ᶠ n in atTop,
        ∀ q ∈ Q,
          ‖fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q‖ ≤ M := by
      rw [Metric.tendstoUniformlyOn_iff] at hderiv_unif
      filter_upwards [hderiv_unif 1 one_pos] with n hn
      intro q hq
      have hdist := hn q hq
      have hlim_le :
          ‖fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q‖ ≤
            ‖fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) qmax‖ :=
        hmax hq
      calc
        ‖fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q‖
            ≤ ‖fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q -
                fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q‖ +
              ‖fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q‖ := by
                simpa only [sub_add_cancel] using
                  norm_add_le
                    (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q -
                      fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q)
                    (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q)
        _ ≤ 1 + ‖fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q‖ := by
              rw [← dist_eq_norm]
              have hdist' :
                  dist
                    (fderiv ℝ (fun z : ℝ × X => v n z.1 z.2) q)
                    (fderiv ℝ (fun z : ℝ × X => vInf z.1 z.2) q) ≤ 1 := by
                simpa [dist_comm] using hdist.le
              linarith
        _ ≤ M := by
              dsimp [M]
              linarith
    let L : NNReal := ⟨M, hM⟩
    have hLip : ∃ L : NNReal, ∀ᶠ n in atTop,
        ∀ p ∈ K, ∀ t ∈ Set.Ico t₀ t₁,
          LipschitzOnWith L (v n t)
            (closedBall (γInf p t) ρ) := by
      refine ⟨L, ?_⟩
      filter_upwards [hstage_deriv] with n hn
      intro p hp t ht
      have htI : t ∈ Set.Icc t₀ t₁ := Ico_subset_Icc_self ht
      have hballQ : ∀ z ∈ closedBall (γInf p t) ρ, (t, z) ∈ Q := by
        intro z hz
        apply mem_cthickening_of_dist_le (t, z) (t, γInf p t) ρ G
          ⟨(p, t), ⟨hp, htI⟩, rfl⟩
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact hz
      have hdiff : ∀ z ∈ closedBall (γInf p t) ρ,
          DifferentiableAt ℝ (v n t) z := by
        intro z hz
        have hqU : (t, z) ∈ J ×ˢ V := hQU (hballQ z hz)
        have hjoint : DifferentiableAt ℝ
            (fun q : ℝ × X => v n q.1 q.2) (t, z) :=
          ((hv_cd n).contDiffAt ((hJ.prod hV).mem_nhds hqU)).differentiableAt
            (by simp)
        exact hjoint.comp z ((differentiableAt_const t).prodMk differentiableAt_id)
      apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff ?_
        (convex_closedBall _ _)
      intro z hz
      have hqQ : (t, z) ∈ Q := hballQ z hz
      have hqU : (t, z) ∈ J ×ˢ V := hQU hqQ
      have hjoint : DifferentiableAt ℝ
          (fun q : ℝ × X => v n q.1 q.2) (t, z) :=
        ((hv_cd n).contDiffAt ((hJ.prod hV).mem_nhds hqU)).differentiableAt
          (by simp)
      have hpartial :=
        DifferentialGeometry.Analysis.ODE.fderiv_eq_comp_inr
          (f := v n) (p := (t, z)) hjoint
      rw [hpartial]
      rw [← NNReal.coe_le_coe]
      change ‖(fderiv ℝ (fun q : ℝ × X => v n q.1 q.2) (t, z)).comp
          (ContinuousLinearMap.inr ℝ ℝ X)‖ ≤ M
      calc
        ‖(fderiv ℝ (fun q : ℝ × X => v n q.1 q.2) (t, z)).comp
            (ContinuousLinearMap.inr ℝ ℝ X)‖
            ≤ ‖fderiv ℝ (fun q : ℝ × X => v n q.1 q.2) (t, z)‖ *
                ‖ContinuousLinearMap.inr ℝ ℝ X‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ (fun q : ℝ × X => v n q.1 q.2) (t, z)‖ := by
              calc
                ‖fderiv ℝ (fun q : ℝ × X => v n q.1 q.2) (t, z)‖ *
                    ‖ContinuousLinearMap.inr ℝ ℝ X‖
                    ≤ ‖fderiv ℝ (fun q : ℝ × X => v n q.1 q.2) (t, z)‖ * 1 :=
                  mul_le_mul_of_nonneg_left
                    (ContinuousLinearMap.norm_inr_le_one ℝ ℝ X)
                    (norm_nonneg _)
                _ = ‖fderiv ℝ (fun q : ℝ × X => v n q.1 q.2) (t, z)‖ := mul_one _
        _ ≤ M := hn (t, z) hqQ
    have hsol :=
      DifferentialGeometry.Analysis.ODE.integralCurve_tendstoUniformlyOn_of_limit_tube
        (K := K) ht₀₁ hρ
        (fun n p hp => (hγ n p (hKA hp)).2)
        (fun p hp => (hγInf p (hKA hp)).2)
        hinit hfield hLip
    refine ⟨hsol, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff] at hsol
    filter_upwards [hsol ρ hρ] with n hn
    intro p hp t ht
    have hdist := hn (p, t) ⟨hp, ht⟩
    have hmemQ : (t, γ n p t) ∈ Q := by
      apply mem_cthickening_of_dist_le (t, γ n p t) (t, γInf p t) ρ G
        ⟨(p, t), ⟨hp, ht⟩, rfl⟩
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      simpa [dist_comm] using hdist.le
    exact (hQU hmemQ).2
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hKne
    subst K
    constructor
    · simpa using
        (tendstoUniformlyOn_empty : TendstoUniformlyOn
          (fun n (q : P × ℝ) => γ n q.1 q.2)
          (fun q : P × ℝ => γInf q.1 q.2) atTop ∅)
    · simp



private theorem ode_iterated_compact
    {P : Type uP}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (m : ℕ)
    {X : Type (max uP uX)}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} {J : Set ℝ} {V : Set X}
    (hA : IsOpen A) (hJ : IsOpen J) (hV : IsOpen V)
    {t₀ t₁ : ℝ} (ht₀₁ : t₀ ≤ t₁) (hI : Icc t₀ t₁ ⊆ J)
    {v : ℕ → ℝ → X → X} {vInf : ℝ → X → X}
    (hv_cd : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (v n)) (J ×ˢ V))
    (hvInf_cd : ContDiffOn ℝ ∞ (Function.uncurry vInf) (J ×ˢ V))
    (hv_conv : MapCInfConvOnCompacts (J ×ˢ V)
      (fun n q => v n q.1 q.2) (fun q => vInf q.1 q.2))
    {a : ℕ → P → X} {aInf : P → X}
    (ha_cd : ∀ n, ContDiffOn ℝ ∞ (a n) A)
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_conv : MapCInfConvOnCompacts A a aInf)
    {γ : ℕ → P → ℝ → X} {γInf : P → ℝ → X}
    (hγ : ∀ n p, p ∈ A →
      γ n p t₀ = a n p ∧ IsIntegralCurveOn (γ n p) (v n) (Icc t₀ t₁))
    (hγInf : ∀ p, p ∈ A →
      γInf p t₀ = aInf p ∧ IsIntegralCurveOn (γInf p) vInf (Icc t₀ t₁))
    (hstay : ∀ n p, p ∈ A → ∀ t ∈ Icc t₀ t₁, γ n p t ∈ V)
    (hstayInf : ∀ p ∈ A, ∀ t ∈ Icc t₀ t₁, γInf p t ∈ V)
    {K : Set P} (hK : IsCompact K) (hKA : K ⊆ A) :
    TendstoUniformlyOn
      (fun n (q : P × ℝ) => iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1)
      (fun q : P × ℝ => iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1)
      atTop (K ×ˢ Icc t₀ t₁) := by
  induction m generalizing X with
  | zero =>
      have hzero := (ode_c0_on_compact hA hJ hV ht₀₁ hI hv_cd hvInf_cd hv_conv
        haInf_cd ha_conv hγ hγInf hstayInf hK hKA).1
      rw [Metric.tendstoUniformlyOn_iff] at hzero ⊢
      intro ε hε
      filter_upwards [hzero ε hε] with n hn
      intro q hq
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        LinearIsometryEquiv.dist_map] using hn q hq
  | succ m ih =>
      let Vtan : Set (X × (P →L[ℝ] X)) := V ×ˢ Set.univ
      have hVtan : IsOpen Vtan := hV.prod isOpen_univ
      have hvTan_cd : ∀ n, ContDiffOn ℝ ∞
          (Function.uncurry
            (DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF P (v n)))
          (J ×ˢ Vtan) := fun n =>
        DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF_contDiffOn
          hJ hV (hv_cd n)
      have hvTanInf_cd : ContDiffOn ℝ ∞
          (Function.uncurry
            (DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF P vInf))
          (J ×ˢ Vtan) :=
        DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF_contDiffOn
          hJ hV hvInf_cd
      have hvTan_conv : MapCInfConvOnCompacts (J ×ˢ Vtan)
          (fun n q =>
            DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF P (v n) q.1 q.2)
          (fun q =>
            DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF P vInf q.1 q.2) :=
        MapCInfConvOnCompacts.paramTangentVF hJ hV hv_cd hvInf_cd hv_conv
      have haTan_cd : ∀ n, ContDiffOn ℝ ∞
          (DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit (a n)) A := fun n =>
        DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit_contDiffOn hA (ha_cd n)
      have haTanInf_cd : ContDiffOn ℝ ∞
          (DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit aInf) A :=
        DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit_contDiffOn hA haInf_cd
      have haTan_conv : MapCInfConvOnCompacts A
          (fun n => DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit (a n))
          (DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit aInf) :=
        MapCInfConvOnCompacts.paramTangentInit hA ha_cd haInf_cd ha_conv
      have hγTan : ∀ n p, p ∈ A →
          DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve (γ n) p t₀ =
              DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit (a n) p ∧
            IsIntegralCurveOn
              (DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve (γ n) p)
              (DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF P (v n))
              (Icc t₀ t₁) := by
        intro n
        exact DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve_initial_isIntegralCurveOn
            hA hJ hV ht₀₁ hI
            (hv_cd n) (ha_cd n) (hγ n) (hstay n)
      have hγTanInf : ∀ p, p ∈ A →
          DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve γInf p t₀ =
              DifferentialGeometry.Analysis.ODE.Flow.paramTangentInit aInf p ∧
            IsIntegralCurveOn
              (DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve γInf p)
              (DifferentialGeometry.Analysis.ODE.Flow.paramTangentVF P vInf)
              (Icc t₀ t₁) :=
        DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve_initial_isIntegralCurveOn
            hA hJ hV ht₀₁ hI
            hvInf_cd haInf_cd hγInf hstayInf
      have hTan := ih hVtan hvTan_cd hvTanInf_cd hvTan_conv
        haTan_cd haTanInf_cd haTan_conv hγTan hγTanInf
        (fun n p hp t ht => ⟨hstay n p hp t ht, mem_univ _⟩)
        (fun p hp t ht => ⟨hstayInf p hp t ht, mem_univ _⟩)
      have hγJoint : ∀ n, ContDiffOn ℝ ∞
          (Function.uncurry (γ n)) (A ×ˢ Icc t₀ t₁) := fun n =>
        DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays
          hJ hV (hv_cd n) hA hI (ha_cd n) (hγ n) (hstay n)
      have hγInfJoint : ContDiffOn ℝ ∞
          (Function.uncurry γInf) (A ×ˢ Icc t₀ t₁) :=
        DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays
          hJ hV hvInf_cd hA hI haInf_cd hγInf hstayInf
      have hγSlice : ∀ n t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => γ n p t) A := by
        intro n t ht
        exact (hγJoint n).comp
          (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun p hp => ⟨hp, ht⟩)
      have hγInfSlice : ∀ t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => γInf p t) A := by
        intro t ht
        exact hγInfJoint.comp
          (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun p hp => ⟨hp, ht⟩)
      have hDγSlice : ∀ n t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fun q => γ n q t) p) A :=
        fun n t ht => (hγSlice n t ht).fderiv_of_isOpen hA
          (by exact_mod_cast le_top)
      have hDγInfSlice : ∀ t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fun q => γInf q t) p) A :=
        fun t ht => (hγInfSlice t ht).fderiv_of_isOpen hA
          (by exact_mod_cast le_top)
      rw [Metric.tendstoUniformlyOn_iff] at hTan ⊢
      intro ε hε
      filter_upwards [hTan ε hε] with n hn
      intro q hq
      have hpair := hn q hq
      have hstageEq :
          iteratedFDeriv ℝ m
              (fun p => DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve
                (γ n) p q.2) q.1 =
            (iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1).prod
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) := by
        simpa only [DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve] using
          iteratedFDeriv_prodMk
            (((hγSlice n q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top))
            (((hDγSlice n q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top)) le_rfl
      have hlimitEq :
          iteratedFDeriv ℝ m
              (fun p => DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve
                γInf p q.2) q.1 =
            (iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1).prod
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1) := by
        simpa only [DifferentialGeometry.Analysis.ODE.Flow.paramTangentCurve] using
          iteratedFDeriv_prodMk
            (((hγInfSlice q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top))
            (((hDγInfSlice q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top)) le_rfl
      have hsecond :
          dist
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1)
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) < ε := by
        rw [hlimitEq, hstageEq] at hpair
        have hsub :
            (iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1).prod
                  (iteratedFDeriv ℝ m
                    (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1) -
                (iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1).prod
                  (iteratedFDeriv ℝ m
                    (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) =
              ((iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1) -
                  iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1).prod
                ((iteratedFDeriv ℝ m
                    (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1) -
                  iteratedFDeriv ℝ m
                    (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) := by
          apply ContinuousMultilinearMap.ext
          intro z
          rfl
        have hpair' :
            max
                ‖iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1 -
                  iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1‖
                ‖iteratedFDeriv ℝ m
                    (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1 -
                  iteratedFDeriv ℝ m
                    (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1‖ < ε := by
          simpa only [dist_eq_norm, hsub, ContinuousMultilinearMap.opNorm_prod] using hpair
        refine lt_of_le_of_lt (le_max_right
          (dist (iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1)
            (iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1))
          (dist
            (iteratedFDeriv ℝ m
              (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1)
            (iteratedFDeriv ℝ m
              (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1))) ?_
        simpa only [dist_eq_norm] using hpair'
      simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.dist_map] using hsecond




private theorem ode_iterated_any
    {P : Type uP}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (m : ℕ)
    {X : Type uX}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} {J : Set ℝ} {V : Set X}
    (hA : IsOpen A) (hJ : IsOpen J) (hV : IsOpen V)
    {t₀ t₁ : ℝ} (ht₀₁ : t₀ ≤ t₁) (hI : Icc t₀ t₁ ⊆ J)
    {v : ℕ → ℝ → X → X} {vInf : ℝ → X → X}
    (hv_cd : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (v n)) (J ×ˢ V))
    (hvInf_cd : ContDiffOn ℝ ∞ (Function.uncurry vInf) (J ×ˢ V))
    (hv_conv : MapCInfConvOnCompacts (J ×ˢ V)
      (fun n q => v n q.1 q.2) (fun q => vInf q.1 q.2))
    {a : ℕ → P → X} {aInf : P → X}
    (ha_cd : ∀ n, ContDiffOn ℝ ∞ (a n) A)
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_conv : MapCInfConvOnCompacts A a aInf)
    {γ : ℕ → P → ℝ → X} {γInf : P → ℝ → X}
    (hγ : ∀ n p, p ∈ A →
      γ n p t₀ = a n p ∧ IsIntegralCurveOn (γ n p) (v n) (Icc t₀ t₁))
    (hγInf : ∀ p, p ∈ A →
      γInf p t₀ = aInf p ∧ IsIntegralCurveOn (γInf p) vInf (Icc t₀ t₁))
    (hstay : ∀ n p, p ∈ A → ∀ t ∈ Icc t₀ t₁, γ n p t ∈ V)
    (hstayInf : ∀ p ∈ A, ∀ t ∈ Icc t₀ t₁, γInf p t ∈ V)
    {K : Set P} (hK : IsCompact K) (hKA : K ⊆ A) :
    TendstoUniformlyOn
      (fun n (q : P × ℝ) => iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1)
      (fun q : P × ℝ => iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1)
      atTop (K ×ˢ Icc t₀ t₁) := by
  cases m with
  | zero =>
      have hzero := (ode_c0_on_compact hA hJ hV ht₀₁ hI hv_cd hvInf_cd hv_conv
        haInf_cd ha_conv hγ hγInf hstayInf hK hKA).1
      rw [Metric.tendstoUniformlyOn_iff] at hzero ⊢
      intro ε hε
      filter_upwards [hzero ε hε] with n hn
      intro q hq
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        LinearIsometryEquiv.dist_map] using hn q hq
  | succ m =>
      let Vtan : Set (X × (P →L[ℝ] X)) := V ×ˢ Set.univ
      have hVtan : IsOpen Vtan := hV.prod isOpen_univ
      have hvTan_cd : ∀ n, ContDiffOn ℝ ∞
          (Function.uncurry (paramTangentVF P (v n))) (J ×ˢ Vtan) :=
        fun n => paramTangentVF_contDiffOn hJ hV (hv_cd n)
      have hvTanInf_cd : ContDiffOn ℝ ∞
          (Function.uncurry (paramTangentVF P vInf)) (J ×ˢ Vtan) :=
        paramTangentVF_contDiffOn hJ hV hvInf_cd
      have hvTan_conv : MapCInfConvOnCompacts (J ×ˢ Vtan)
          (fun n q => paramTangentVF P (v n) q.1 q.2)
          (fun q => paramTangentVF P vInf q.1 q.2) :=
        MapCInfConvOnCompacts.paramTangentVF hJ hV hv_cd hvInf_cd hv_conv
      have haTan_cd : ∀ n, ContDiffOn ℝ ∞ (paramTangentInit (a n)) A :=
        fun n => paramTangentInit_contDiffOn hA (ha_cd n)
      have haTanInf_cd : ContDiffOn ℝ ∞ (paramTangentInit aInf) A :=
        paramTangentInit_contDiffOn hA haInf_cd
      have haTan_conv : MapCInfConvOnCompacts A
          (fun n => paramTangentInit (a n)) (paramTangentInit aInf) :=
        MapCInfConvOnCompacts.paramTangentInit hA ha_cd haInf_cd ha_conv
      have hγTan : ∀ n p, p ∈ A →
          paramTangentCurve (γ n) p t₀ = paramTangentInit (a n) p ∧
            IsIntegralCurveOn (paramTangentCurve (γ n) p)
              (paramTangentVF P (v n)) (Icc t₀ t₁) := by
        intro n
        exact paramTangentCurve_initial_isIntegralCurveOn hA hJ hV ht₀₁ hI
          (hv_cd n) (ha_cd n) (hγ n) (hstay n)
      have hγTanInf : ∀ p, p ∈ A →
          paramTangentCurve γInf p t₀ = paramTangentInit aInf p ∧
            IsIntegralCurveOn (paramTangentCurve γInf p)
              (paramTangentVF P vInf) (Icc t₀ t₁) :=
        paramTangentCurve_initial_isIntegralCurveOn hA hJ hV ht₀₁ hI
          hvInf_cd haInf_cd hγInf hstayInf
      have hTan := ode_iterated_compact.{uP, uX} (P := P)
        (X := X × (P →L[ℝ] X)) m hA hJ hVtan ht₀₁ hI
        hvTan_cd hvTanInf_cd hvTan_conv haTan_cd haTanInf_cd haTan_conv
        hγTan hγTanInf
        (fun n p hp t ht => ⟨hstay n p hp t ht, mem_univ _⟩)
        (fun p hp t ht => ⟨hstayInf p hp t ht, mem_univ _⟩) hK hKA
      have hγJoint : ∀ n, ContDiffOn ℝ ∞
          (Function.uncurry (γ n)) (A ×ˢ Icc t₀ t₁) := fun n =>
        contDiffOn_solutionFamily_of_stays hJ hV (hv_cd n) hA hI
          (ha_cd n) (hγ n) (hstay n)
      have hγInfJoint : ContDiffOn ℝ ∞
          (Function.uncurry γInf) (A ×ˢ Icc t₀ t₁) :=
        contDiffOn_solutionFamily_of_stays hJ hV hvInf_cd hA hI
          haInf_cd hγInf hstayInf
      have hγSlice : ∀ n t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => γ n p t) A := by
        intro n t ht
        exact (hγJoint n).comp (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun p hp => ⟨hp, ht⟩)
      have hγInfSlice : ∀ t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => γInf p t) A := by
        intro t ht
        exact hγInfJoint.comp (contDiff_id.prodMk contDiff_const).contDiffOn
          (fun p hp => ⟨hp, ht⟩)
      have hDγSlice : ∀ n t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fun q => γ n q t) p) A :=
        fun n t ht => (hγSlice n t ht).fderiv_of_isOpen hA
          (by exact_mod_cast le_top)
      have hDγInfSlice : ∀ t, t ∈ Icc t₀ t₁ →
          ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fun q => γInf q t) p) A :=
        fun t ht => (hγInfSlice t ht).fderiv_of_isOpen hA
          (by exact_mod_cast le_top)
      rw [Metric.tendstoUniformlyOn_iff] at hTan ⊢
      intro ε hε
      filter_upwards [hTan ε hε] with n hn
      intro q hq
      have hpair := hn q hq
      have hstageEq :
          iteratedFDeriv ℝ m (fun p => paramTangentCurve (γ n) p q.2) q.1 =
            (iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1).prod
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) := by
        simpa only [paramTangentCurve] using
          iteratedFDeriv_prodMk
            (((hγSlice n q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top))
            (((hDγSlice n q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top)) le_rfl
      have hlimitEq :
          iteratedFDeriv ℝ m (fun p => paramTangentCurve γInf p q.2) q.1 =
            (iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1).prod
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1) := by
        simpa only [paramTangentCurve] using
          iteratedFDeriv_prodMk
            (((hγInfSlice q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top))
            (((hDγInfSlice q.2 hq.2).contDiffAt (hA.mem_nhds (hKA hq.1))).of_le
              (by exact_mod_cast le_top)) le_rfl
      rw [hlimitEq, hstageEq] at hpair
      have hsub :
          (iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1).prod
                (iteratedFDeriv ℝ m
                  (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1) -
              (iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1).prod
                (iteratedFDeriv ℝ m
                  (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) =
            ((iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1) -
                iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1).prod
              ((iteratedFDeriv ℝ m
                  (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1) -
                iteratedFDeriv ℝ m
                  (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) := by
        apply ContinuousMultilinearMap.ext
        intro z
        rfl
      have hpair' :
          max
              ‖iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1 -
                iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1‖
              ‖iteratedFDeriv ℝ m
                  (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1 -
                iteratedFDeriv ℝ m
                  (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1‖ < ε := by
        simpa only [dist_eq_norm, hsub, ContinuousMultilinearMap.opNorm_prod] using hpair
      have hsecond :
          dist
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1)
              (iteratedFDeriv ℝ m
                (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1) < ε := by
        refine lt_of_le_of_lt (le_max_right
          (dist (iteratedFDeriv ℝ m (fun p => γInf p q.2) q.1)
            (iteratedFDeriv ℝ m (fun p => γ n p q.2) q.1))
          (dist
            (iteratedFDeriv ℝ m
              (fun p => fderiv ℝ (fun z => γInf z q.2) p) q.1)
            (iteratedFDeriv ℝ m
              (fun p => fderiv ℝ (fun z => γ n z q.2) p) q.1))) ?_
        simpa only [dist_eq_norm] using hpair'
      simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        LinearIsometryEquiv.dist_map] using hsecond



private theorem mapCP_of_comp_add
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {p N : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvOn K p (fun n => Φ (n + N)) Φinf) :
    MapCPConvOn K p Φ Φinf := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := h ε hε
  refine ⟨k₀ + N, ?_⟩
  intro k hk r hr x hx
  have hNk : N ≤ k := le_trans (Nat.le_add_left N k₀) hk
  have hb := hk₀ (k - N) (Nat.le_sub_of_add_le hk) r hr x hx
  simpa only [Nat.sub_add_cancel hNk] using hb



theorem MapCInfConvOnCompacts.ode_solutionAt
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set P} {J : Set ℝ} {V : Set X}
    (hA : IsOpen A)
    (hJ : IsOpen J)
    (hV : IsOpen V)
    {t₀ t₁ : ℝ}
    (ht₀₁ : t₀ ≤ t₁)
    (hI : Set.Icc t₀ t₁ ⊆ J)
    {v : ℕ → ℝ → X → X}
    {vInf : ℝ → X → X}
    (hv_cd :
      ∀ n, ContDiffOn ℝ ∞
        (fun q : ℝ × X => v n q.1 q.2) (J ×ˢ V))
    (hvInf_cd :
      ContDiffOn ℝ ∞
        (fun q : ℝ × X => vInf q.1 q.2) (J ×ˢ V))
    (hv_conv :
      MapCInfConvOnCompacts (J ×ˢ V)
        (fun n q => v n q.1 q.2)
        (fun q => vInf q.1 q.2))
    {a : ℕ → P → X}
    {aInf : P → X}
    (ha_cd : ∀ n, ContDiffOn ℝ ∞ (a n) A)
    (haInf_cd : ContDiffOn ℝ ∞ aInf A)
    (ha_conv : MapCInfConvOnCompacts A a aInf)
    {γ : ℕ → P → ℝ → X}
    {γInf : P → ℝ → X}
    (hγ :
      ∀ n p, p ∈ A →
        γ n p t₀ = a n p ∧
        IsIntegralCurveOn
          (γ n p) (v n) (Set.Icc t₀ t₁))
    (hγInf :
      ∀ p, p ∈ A →
        γInf p t₀ = aInf p ∧
        IsIntegralCurveOn
          (γInf p) vInf (Set.Icc t₀ t₁))
    (hstayInf :
      ∀ p ∈ A, ∀ t ∈ Set.Icc t₀ t₁,
        γInf p t ∈ V) :
    MapCInfConvOnCompacts A
      (fun n p => γ n p t₁)
      (fun p => γInf p t₁) := by
  intro K hK hKA p
  obtain ⟨W, hW, hKW, hWA, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hA hKA
  have hWA' : W ⊆ A := fun x hx => hWA (subset_closure hx)
  have hc₀ := ode_c0_on_compact hA hJ hV ht₀₁ hI hv_cd hvInf_cd hv_conv
    haInf_cd ha_conv hγ hγInf hstayInf hWcompact hWA
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc₀.2
  have hstayShift : ∀ n p, p ∈ W → ∀ t ∈ Icc t₀ t₁,
      γ (n + N) p t ∈ V := by
    intro n x hx t ht
    exact hN (n + N) (Nat.le_add_left N n) x (subset_closure hx) t ht
  have hvConvShift : MapCInfConvOnCompacts (J ×ˢ V)
      (fun n q => v (n + N) q.1 q.2) (fun q => vInf q.1 q.2) :=
    hv_conv.comp_tendsto_atTop (Filter.tendsto_add_atTop_nat N)
  have haConvW : MapCInfConvOnCompacts W a aInf :=
    fun C hC hCW r => ha_conv C hC (hCW.trans hWA') r
  have haConvShift : MapCInfConvOnCompacts W
      (fun n => a (n + N)) aInf :=
    haConvW.comp_tendsto_atTop (Filter.tendsto_add_atTop_nat N)
  have hγShift : ∀ n x, x ∈ W →
      γ (n + N) x t₀ = a (n + N) x ∧
        IsIntegralCurveOn (γ (n + N) x) (v (n + N)) (Icc t₀ t₁) :=
    fun n x hx => hγ (n + N) x (hWA' hx)
  have hγInfW : ∀ x, x ∈ W →
      γInf x t₀ = aInf x ∧
        IsIntegralCurveOn (γInf x) vInf (Icc t₀ t₁) :=
    fun x hx => hγInf x (hWA' hx)
  have hstayInfW : ∀ x ∈ W, ∀ t ∈ Icc t₀ t₁, γInf x t ∈ V :=
    fun x hx t ht => hstayInf x (hWA' hx) t ht
  have hγJointShift : ∀ n, ContDiffOn ℝ ∞
      (Function.uncurry (γ (n + N))) (W ×ˢ Icc t₀ t₁) := fun n =>
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays
      hJ hV (hv_cd (n + N)) hW hI ((ha_cd (n + N)).mono hWA')
      (hγShift n) (hstayShift n)
  have hγInfJointW : ContDiffOn ℝ ∞
      (Function.uncurry γInf) (W ×ˢ Icc t₀ t₁) :=
    DifferentialGeometry.Analysis.ODE.Flow.contDiffOn_solutionFamily_of_stays
      hJ hV hvInf_cd hW hI (haInf_cd.mono hWA') hγInfW hstayInfW
  have hstageSmooth : ∀ n, ContDiffOn ℝ ∞ (fun x => γ (n + N) x t₁) W := by
    intro n
    exact (hγJointShift n).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x hx => ⟨hx, right_mem_Icc.mpr ht₀₁⟩)
  have hlimitSmooth : ContDiffOn ℝ ∞ (fun x => γInf x t₁) W :=
    hγInfJointW.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x hx => ⟨hx, right_mem_Icc.mpr ht₀₁⟩)
  have htu : ∀ r : ℕ, r ≤ p →
      TendstoUniformlyOn
        (fun n x => iteratedFDeriv ℝ r (fun y => γ (n + N) y t₁) x)
        (fun x => iteratedFDeriv ℝ r (fun y => γInf y t₁) x)
        atTop K := by
    intro r _hr
    have htraj := ode_iterated_any (P := P) (X := X) r hW hJ hV ht₀₁ hI
      (fun n => hv_cd (n + N)) hvInf_cd hvConvShift
      (fun n => (ha_cd (n + N)).mono hWA') (haInf_cd.mono hWA') haConvShift
      hγShift hγInfW hstayShift hstayInfW hK hKW
    rw [Metric.tendstoUniformlyOn_iff] at htraj ⊢
    intro ε hε
    filter_upwards [htraj ε hε] with n hn
    intro x hx
    exact hn (x, t₁) ⟨hx, right_mem_Icc.mpr ht₀₁⟩
  have hshift : MapCPConvOn K p
      (fun n x => γ (n + N) x t₁) (fun x => γInf x t₁) :=
    mapCPConvOn_of_tendstoUniformlyOn hW hKW
      (fun n => (hstageSmooth n).of_le (by exact_mod_cast le_top))
      (hlimitSmooth.of_le (by exact_mod_cast le_top)) htu
  exact mapCP_of_comp_add hshift

end HCGCompactness
end DifferentialGeometry
