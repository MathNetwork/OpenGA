import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import DifferentialGeometry.Bundle.SectionRealized
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent




namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section TangentCovariantDerivative

variable [IsManifold I 1 M]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem covariantDeriv_vectorField_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, covariantDeriv_vectorField (I := I) cov (fun q => X q) (fun q => Y q) p⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) := by
  simpa [covariantDeriv_vectorField] using
    (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff_apply
      (𝕜 := 𝕜) (I := I) (M := M) cov hcov X Y)




noncomputable def covSection
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) where
  toFun := fun p : M => (cov (fun q : M => Y q) p) (X p)
  contMDiff_toFun := by
    simpa [covariantDeriv_vectorField] using
      covariantDeriv_vectorField_contMDiff (I := I) cov hcov X Y

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] theorem covSection_apply
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (p : M) :
    covSection (I := I) cov hcov X Y p = (cov (fun q : M => Y q) p) (X p) :=
  rfl



noncomputable def tangentFieldModelInChart (x₀ : M)
    (V : (x : M) → TangentSpace I x) (y : E) : E :=
  (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt 𝕜
    ((extChartAt I x₀).symm y) (V ((extChartAt I x₀).symm y))



omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem tangentFieldModelInChart_tangentConstInChart_apply_of_mem
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) (v : E) :
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) y = v := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hp_source : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  have hp_base : (extChartAt I x₀).symm y ∈ e.baseSet := by
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
  unfold tangentFieldModelInChart tangentConstInChart
  exact e.continuousLinearMapAt_symmL (R := 𝕜) hp_base v




omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
theorem tangentConstInChart_self_continuousLinearMapAt
    (x : M) (v : TangentSpace I x) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x
        ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
          𝕜 x v) x =
      v := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  rw [tangentConstInChart_apply]
  exact e.symmL_continuousLinearMapAt (R := 𝕜) hx v




omit [CompleteSpace 𝕜] in
theorem tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem
    (x₀ : M) (V : (x : M) → TangentSpace I x) {p₀ : M}
    (hp₀ : p₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    V =ᶠ[𝓝 p₀]
      fun p : M =>
        ∑ i : Fin (Module.finrank 𝕜 E),
          (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) i) p := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis 𝕜 E
  filter_upwards [e.open_baseSet.mem_nhds hp₀] with p hp
  have hp_source : p ∈ (extChartAt I x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
  have hsymm :
      e.symmL 𝕜 p (e.continuousLinearMapAt 𝕜 p (V p)) = V p :=
    e.symmL_continuousLinearMapAt (R := 𝕜) hp (V p)
  calc
    V p = e.symmL 𝕜 p (e.continuousLinearMapAt 𝕜 p (V p)) := hsymm.symm
    _ = e.symmL 𝕜 p
          (∑ i : Fin (Module.finrank 𝕜 E),
            b.coord i (e.continuousLinearMapAt 𝕜 p (V p)) • b i) := by
          congr 1
          exact (b.sum_repr (e.continuousLinearMapAt 𝕜 p (V p))).symm
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
          b.coord i (e.continuousLinearMapAt 𝕜 p (V p)) • e.symmL 𝕜 p (b i) := by
          rw [map_sum]
          congr
          ext i
          rw [map_smul]
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
          b.coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b i) p := by
          have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
            (extChartAt I x₀).left_inv hp_source
          have hmodel :
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                  (extChartAt I x₀ p) =
                e.continuousLinearMapAt 𝕜 p (V p) := by
            unfold tangentFieldModelInChart
            rw [hleft]
          congr
          ext i
          rw [tangentConstInChart_apply]
          rw [hmodel]




omit [CompleteSpace 𝕜] in
theorem tangentField_eq_sum_modelCoord_tangentConst_eventually
    (x₀ : M) (V : (x : M) → TangentSpace I x) :
    V =ᶠ[𝓝 x₀]
      fun p : M =>
        ∑ i : Fin (Module.finrank 𝕜 E),
          (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p)) •
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) i) p := by
  exact tangentField_eq_sum_modelCoord_tangentConst_eventually_of_mem
    (𝕜 := 𝕜) (I := I) x₀ V (FiberBundle.mem_baseSet_trivializationAt' x₀)

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in


omit [IsManifold I n M] in
lemma tangentConstInChart_contMDiffOn_baseSet (x₀ : M) (v : E)
    [IsManifold I (n + 1) M] :
    CMDiff[(trivializationAt E (TangentSpace I) x₀).baseSet] n
      (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v :
        (p : M) → TangentSpace I p)) := by
  let e := trivializationAt E (TangentSpace I) x₀
  haveI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  rw [e.contMDiffOn_section_baseSet_iff]
  refine (contMDiffOn_const (c := v)).congr ?_
  intro y hy
  have hcoe : ⇑(e.linearMapAt 𝕜 y) = fun z => (e ⟨y, z⟩).2 :=
    e.coe_linearMapAt_of_mem (R := 𝕜) hy
  simpa [e, tangentConstInChart, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe] using
    (e.continuousLinearMapAt_symmL (R := 𝕜) hy v)

end TangentCovariantDerivative

end

end TensorLieDeriv

namespace CovariantDerivative

open Bundle
open scoped Manifold ContDiff



theorem smoothSections_cov_contMDiffAt_one
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeLocally cov (1 : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (fun q : M => Y q) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) x := by
  haveI : IsManifold I ((1 : WithTop ℕ∞) + 1) M := by
    have h : ((1 : WithTop ℕ∞) + 1) = (2 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 2 M)
  have hY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) ((1 : WithTop ℕ∞) + 1)
        (fun p : M =>
          (⟨p, Y p⟩ : TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    (Y.contMDiff.of_le
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)).contMDiffOn
  have hcovY :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M =>
                TangentSpace I p →L[𝕜] TangentSpace I p))) Set.univ :=
    (hcov isOpen_univ).contMDiff hY
  have hX :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, X p⟩ : TotalSpace E (TangentSpace I : M → Type _))) Set.univ :=
    (X.contMDiff.of_le
      (by
        change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)).contMDiffOn
  exact (hcovY.clm_bundle_apply hX).contMDiffAt (by simp)







theorem tangentConst_cov_mdiffAt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : ContMDiffCovariantDerivativeLocally cov (1 : WithTop ℕ∞))
    {x : M} (v w : TangentSpace I x) :
    MDiffAt
      (T% (fun p : M =>
        (cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x w) p)
          ((TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x v) p))) x := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  haveI : IsManifold I ((1 : WithTop ℕ∞) + 1) M := by
    have h : ((1 : WithTop ℕ∞) + 1) = (2 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    have h : (((1 : WithTop ℕ∞) + 1) + 1) = (3 : WithTop ℕ∞) := by
      norm_num
    exact h.symm ▸ (inferInstance : IsManifold I 3 M)
  have hw :
      CMDiff[e.baseSet] ((1 : WithTop ℕ∞) + 1)
        (T% (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x w :
          (p : M) → TangentSpace I p)) := by
    simpa [e] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := 𝕜) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞) + 1) x w)
  have hcovw :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (1 : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x w) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M =>
                TangentSpace I p →L[𝕜] TangentSpace I p)))
        e.baseSet := by
    exact (hcov e.open_baseSet).contMDiff hw
  have hv :
      CMDiff[e.baseSet] (1 : WithTop ℕ∞)
        (T% (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x v :
          (p : M) → TangentSpace I p)) := by
    simpa [e] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := 𝕜) (I := I) (M := M)
        (n := (1 : WithTop ℕ∞)) x v)
  have h_on :
      CMDiff[e.baseSet] (1 : WithTop ℕ∞)
        (T% (fun p : M =>
          (cov (TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x w) p)
            ((TensorLieDeriv.tangentConstInChart (𝕜 := 𝕜) (I := I) x v) p))) := by
    simpa [e] using hcovw.clm_bundle_apply hv
  exact ((h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)

end CovariantDerivative
