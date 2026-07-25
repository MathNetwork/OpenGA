import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Readout
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0NormalForm.RzMaster









noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff Matrix

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff
    deTurckVFCovDeriv connDiffOp_homSection_contMDiff metricConnDiffLoweredFib
    metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank
    domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

namespace LieCorr0Core

noncomputable def lieCorr0NEndo
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)
    - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x)
    - deTurckLieWEndo (I := I) g₁ g₀ x

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorr0NEndo_homSection_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x)) := by
  have hBV : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (connDiffOp_homSection_contMDiff (I := I) g₁ g₀)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀).contMDiff
  have hBW : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (connDiffOp_homSection_contMDiff (I := I) g₁ g₀)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hW := deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g₀
  exact (hBV.sub_section hBW).sub_section hW

noncomputable def lieCorr0InsertFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (lieCorr0NEndo (I := I) g₀ g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (lieCorr0NEndo (I := I) g₀ g₁ g_bg x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0InsertFib_toModel
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0 (lieCorr0NEndo (I := I) g₀ g₁ g_bg x (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1 (lieCorr0NEndo (I := I) g₀ g₁ g_bg x (v 1))) := by
  rw [lieCorr0InsertFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorr0InsertFib_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
    (fun x => lieCorr0NEndo (I := I) g₀ g₁ g_bg x)
    (lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 1
    (fun x => lieCorr0NEndo (I := I) g₀ g₁ g_bg x)
    (lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [lieCorr0InsertFib]
  rfl

noncomputable def lieCorr0TraceStep
    (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x :=
  (cometricDoubleTraceFib (I := I) g p x).comp
    (domDomCongrFibRank (I := I) (p + 2) σ x)

def lieCorr0VBPerm : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

noncomputable def lieCorr0VBFib
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ((lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x).comp
    ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)).comp
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x))))

def lieCorr0AMixPermQ : Equiv.Perm (Fin 5) :=
  ⟨![1, 4, 2, 3, 0], ![4, 0, 2, 3, 1], by decide, by decide⟩

def lieCorr0AMixPerm1 : Equiv.Perm (Fin 6) :=
  ⟨![2, 0, 3, 1, 4, 5], ![1, 3, 0, 2, 4, 5], by decide, by decide⟩

def lieCorr0AMixPerm2 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

noncomputable def lieCorr0AMixHalfFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (lieCorr0TraceStep (I := I) g₁ 2 lieCorr0AMixPerm2 x).comp
    ((lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x).comp
      ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)).comp
        ((lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x).comp
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))

noncomputable def lieCorr0AMixFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x +
    (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x).comp
      (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x))

noncomputable def lieCorr0RiemQuadlin
    (g₀ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x)
      (TangentSpace I x →L[ℝ] TangentSpace I x)
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
        (TangentSpace I x →L[ℝ] ℝ) (g₀.inner x))).comp
    (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0RiemQuadlin_apply
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 u w : TangentSpace I x) :
    lieCorr0RiemQuadlin (I := I) g₀ x v0 v1 u w =
      g₀.inner x (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x v0 v1 u) w :=
  rfl

noncomputable def lieCorr0Quadlin4ToModel
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm
    (((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin 3 => F) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℝ F (F →L[ℝ] F →L[ℝ] ℝ)
          (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ)
          ((bilinFormToModelₗᵢ F).toContinuousLinearEquiv.toContinuousLinearMap)).comp Q))

theorem lieCorr0Quadlin4ToModel_apply
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 4 → F) :
    lieCorr0Quadlin4ToModel F Q v = Q (v 0) (v 1) (v 2) (v 3) := by
  have h1 : lieCorr0Quadlin4ToModel F Q v =
      bilinFormToModel F (Q (v 0) (v 1)) (Fin.tail (Fin.tail v)) := rfl
  rw [h1, bilinFormToModel_apply]
  rfl

noncomputable def lieCorr0RiemLoweredFib
    (g₀ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 4 I x :=
  Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (lieCorr0Quadlin4ToModel (TangentSpace I x) (lieCorr0RiemQuadlin (I := I) g₀ x))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0RiemLoweredFib_toModel
    (g₀ : SmoothRiemannianMetric I M) (x : M) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x) v =
      g₀.inner x (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x
        (v 0) (v 1) (v 2)) (v 3) := by
  rw [lieCorr0RiemLoweredFib, Tensor0SSpace.toModel_ofModel]
  exact lieCorr0Quadlin4ToModel_apply (TangentSpace I x) (lieCorr0RiemQuadlin (I := I) g₀ x) v

def lieCorr0RiemPerm1 : Equiv.Perm (Fin 6) :=
  ⟨![1, 5, 2, 3, 4, 0], ![5, 0, 2, 3, 4, 1], by decide, by decide⟩

def lieCorr0RiemPerm2 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

noncomputable def lieCorr0RiemFib
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ((lieCorr0TraceStep (I := I) g₁ 2 lieCorr0RiemPerm2 x).comp
    ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x))))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lieCorr0_ddc_section_contMDiff
    {d : ℕ} (ρ : Equiv.Perm (Fin d)) (Z : ∀ x : M, Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) x
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
    (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SSpace.toModel (Z x))) :
          Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
    (Module.finBasis ℝ E) (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ (Tensor0SSpace.toModel (Z x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lieCorr0_prod_section_contMDiff
    {p q : ℕ} (Y : ∀ x : M, Tensor0SSpace p I x) (K : ∀ x : M, Tensor0SSpace q I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) x (Y x)))
    (hK : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SSpace q I z) x (K x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + q) I z) x
        (tensor0SProdKappaFib (I := I) x (K x) (Y x))) := by
  classical
  have hbase : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + q) I z) x
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SSpace.toModel (Y x)) (Tensor0SSpace.toModel (K x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SSpace.toModel (Y x)) (Tensor0SSpace.toModel (K x))) :
            Tensor0SSpace (p + q) I x))).mpr ?_
    have hYc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E) (fun x => Y x)).mp hY
    have hKc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
      (Module.finBasis ℝ E) (fun x => K x)).mp hK
    intro τ x₀
    refine (((contMDiffAt_const (I := I) (x := x₀) (n := (∞ : WithTop ℕ∞))
      (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
        (hYc (τ ∘ Fin.castAdd q) x₀)).clm_apply
          (hKc (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
      continuousMultilinearMap_basis_repr]
    change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SSpace.toModel (Y x)) (Tensor0SSpace.toModel (K x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  refine hbase.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
    (E := fun z : M => Tensor0SSpace (p + q) I z) x t) ?_
  rw [tensor0SProdKappaFib_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem lieCorr0TraceStep_section_contMDiff
    (g : SmoothRiemannianMetric I M) (p : ℕ) (σ : Equiv.Perm (Fin (p + 2)))
    (Z : ∀ x : M, Tensor0SSpace (p + 2) I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) x
        (lieCorr0TraceStep (I := I) g p σ x (Z x))) := by
  have hZρ := lieCorr0_ddc_section_contMDiff (I := I) σ (fun x => Z x) hZ
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g p) hZρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) x t) ?_
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0VBFib_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorr0VBFib (I := I) g₀ g₁ x)
  intro Y
  have hip : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))) :=
    (Tensor0SBundle.contract_Tensor0SField (𝕜 := ℝ) (I := I) (n := (∞ : WithTop ℕ∞)) 1 Y
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)).contMDiff
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 1) (q := 3)
    (fun x => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    hip (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have htr := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0VBPerm
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x)))
    hprod
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((2 : ℝ) • lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
          (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
            (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
              ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))))) :=
    ContMDiff.smul_section contMDiff_const htr
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0VBFib]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0AMixHalfFib_section_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x))) := by
  classical
  have hprod1 := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 3)
    (fun x => Y x) (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    Y.contMDiff (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have htr1 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 3 lieCorr0AMixPermQ
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      (Y x)) hprod1
  have hprod2 := lieCorr0_prod_section_contMDiff (I := I) (p := 3) (q := 3)
    (fun x => lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    htr1 (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg)
  have htr2 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 4 lieCorr0AMixPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
        (tensor0SProdKappaFib (I := I) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))) hprod2
  have htr3 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0AMixPerm2
    (fun x => lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
          (tensor0SProdKappaFib (I := I) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x))))) htr2
  refine htr3.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0AMixHalfFib]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0AMixFib_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)
  intro Y
  have hhalf := lieCorr0AMixHalfFib_section_contMDiff (I := I) g₀ g₁ g_bg Y
  have hswap := lieCorr0_ddc_section_contMDiff (I := I) (Equiv.swap 0 1)
    (fun x => lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x)) hhalf
  have hswap' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x)))) := by
    refine hswap.congr (fun x => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
    rw [domDomCongrFibRank_apply]
  have hadd := ContMDiff.add_section
    (s := fun x => lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x))
    (t := fun x => domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
      (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x))) hhalf hswap'
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x) +
          domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
            (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x))))) :=
    ContMDiff.smul_section contMDiff_const hadd
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0AMixFib]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0RiemLoweredFib_section_contMDiff
    (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x)) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞))
    (Module.finBasis ℝ E)
    (fun x : M => (lieCorr0RiemLoweredFib (I := I) g₀ x : Tensor0SSpace 4 I x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => g₀.inner x
        (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x
          ((Y (σ 0)) x) ((Y (σ 1)) x) ((Y (σ 2)) x)) ((Y (σ 3)) x)) :=
    Integral.Connection.mixedKernelScalar_global (I := I) g₀ g₀
      (Y (σ 0)).contMDiff (Y (σ 3)).contMDiff (Y (σ 1)).contMDiff (Y (σ 2)).contMDiff
  refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in nhds x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe' : ∀ j : Fin 4, e₁.symmL ℝ x (b (σ j)) = (Y (σ j)) x := by
    intro j
    rw [hYx (σ j), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x)
      (fun j : Fin 4 => e₁.symmL ℝ x (b (σ j))) = _
  rw [lieCorr0RiemLoweredFib_toModel]
  rw [hframe' 0, hframe' 1, hframe' 2, hframe' 3]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lieCorr0RiemFib_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0RiemFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorr0RiemFib (I := I) g₀ g₁ x)
  intro Y
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorr0RiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorr0TraceStep_section_contMDiff (I := I) g₀ 4 lieCorr0RiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  have htr2 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0RiemPerm2
    (fun x => lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))) htr1
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((-1 : ℝ) • lieCorr0TraceStep (I := I) g₁ 2 lieCorr0RiemPerm2 x
          (lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x
            (tensor0SProdKappaFib (I := I) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))))) :=
    ContMDiff.smul_section contMDiff_const htr2
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0RiemFib]
  rfl

noncomputable def lieCorr0TotalFib
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  lieCorr0InsertFib (I := I) g₀ g₁ g_bg x + lieCorr0VBFib (I := I) g₀ g₁ x +
    lieCorr0AMixFib (I := I) g₀ g₁ g_bg x + lieCorr0RiemFib (I := I) g₀ g₁ x

omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorr0TotalFib_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h12 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x)))
    (lieCorr0InsertFib_contMDiff (I := I) g₀ g₁ g_bg)
    (lieCorr0VBFib_contMDiff (I := I) g₀ g₁)
  have h123 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)))
    h12 (lieCorr0AMixFib_contMDiff (I := I) g₀ g₁ g_bg)
  have h1234 := ContMDiff.add_section
    (s := fun x => ((show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x))) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0RiemFib (I := I) g₀ g₁ x)))
    h123 (lieCorr0RiemFib_contMDiff (I := I) g₀ g₁)
  refine h1234.congr (fun x => ?_)
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [lieCorr0TotalFib]
  rfl

end LieCorr0Core

open LieCorr0Core



def lieCorr0Field (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorr0TotalFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _


omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorr0Field_apply
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x)) :=
  rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
