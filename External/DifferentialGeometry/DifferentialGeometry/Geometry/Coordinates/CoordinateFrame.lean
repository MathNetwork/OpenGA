import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import DifferentialGeometry.Tensor.RSTensor.Components
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Set Bundle Tensor0SBundle Filter
open scoped Topology Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


abbrev CoordinateIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] :=
  Fin (Module.finrank 𝕜 E)







structure LocalChartAt (x₀ : M) where
  chart : OpenPartialHomeomorph M H
  mem_source : x₀ ∈ chart.source
  mem_max : chart ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M
  triv : Trivialization E (π E (TangentSpace I : M -> Type _))
  triv_mem : MemTrivializationAtlas triv
  triv_baseSet_eq : triv.baseSet = chart.source

namespace LocalChartAt


def source {x₀ : M} (C : LocalChartAt (I := I) x₀) : Set M :=
  C.chart.source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem source_open {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    IsOpen C.source :=
  C.chart.open_source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem triv_baseSet {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    C.triv.baseSet = C.source :=
  C.triv_baseSet_eq


def default (x₀ : M) : LocalChartAt (I := I) x₀ where
  chart := chartAt H x₀
  mem_source := mem_chart_source H x₀
  mem_max := IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  triv := trivializationAt E (TangentSpace I : M -> Type _) x₀
  triv_mem := inferInstance
  triv_baseSet_eq := by
    simp only [TangentBundle.trivializationAt_baseSet]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem default_mem (x₀ : M) :
    x₀ ∈ (LocalChartAt.default (I := I) x₀).source :=
  (LocalChartAt.default (I := I) x₀).mem_source


def ext {x₀ : M} (C : LocalChartAt (I := I) x₀) : PartialEquiv M E :=
  C.chart.extend I

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp]
theorem ext_source {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    C.ext.source = C.source := by
  simp [ext, source]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem mem_ext_source {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    x₀ ∈ C.ext.source := by
  simpa [ext_source, source] using C.mem_source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem default_ext (x₀ : M) :
    (LocalChartAt.default (I := I) x₀).ext = extChartAt I x₀ := by
  rfl


def overlap {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) : Set M :=
  C.source ∩ D.source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem overlap_open {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    IsOpen (C.overlap D) :=
  C.source_open.inter D.source_open

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem mem_overlap {x₀ x₁ x : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    x ∈ C.overlap D ↔ x ∈ C.source ∧ x ∈ D.source := by
  rfl


def change {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) : PartialEquiv E E :=
  ModelWithCorners.extendCoordChange (I := I) C.chart D.chart

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem change_symm {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    (C.change D).symm = D.change C := by
  simpa [change] using
    (ModelWithCorners.extendCoordChange_symm (I := I) (e := C.chart) (e' := D.chart))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem change_smooth {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    ContDiffOn 𝕜 (∞ : WithTop ℕ∞) (C.change D) (C.change D).source := by
  simpa [change] using
    (ModelWithCorners.contDiffOn_extendCoordChange (I := I) C.mem_max D.mem_max)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem ext_mem_change {x₀ x₁ x : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) (hx : x ∈ C.overlap D) :
    C.ext x ∈ (C.change D).source := by
  have hx' : x ∈ C.chart.source ∩ D.chart.source := by
    simpa [overlap, source] using hx
  have hmem : C.chart.extend I x ∈ C.chart.extend I '' (C.chart.source ∩ D.chart.source) :=
    ⟨x, hx', rfl⟩
  change C.chart.extend I x ∈
    (ModelWithCorners.extendCoordChange (I := I) C.chart D.chart).source
  rw [← OpenPartialHomeomorph.extend_image_source_inter (I := I)]
  exact hmem






def vec {x₀ : M} (C : LocalChartAt (I := I) x₀) {x : M}
    (hx : x ∈ C.source) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    TangentSpace I x := by
  have hx_ext : x ∈ C.ext.source := by
    simpa [source] using hx
  have hleft : C.ext.symm (C.ext x) = x := C.ext.left_inv hx_ext
  exact hleft ▸
    ((mfderiv[Set.range I] C.ext.symm (C.ext x)) ((Module.finBasis 𝕜 E) i))

end LocalChartAt


abbrev coordinateTrivializationAt
    (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  trivializationAt E (TangentSpace I : M -> Type _) x₀

namespace LocalChartAt


abbrev defaultTriv (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  (LocalChartAt.default (I := I) x₀).triv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp]
theorem default_triv (x₀ : M) :
    LocalChartAt.defaultTriv (I := I) x₀ =
      coordinateTrivializationAt (I := I) x₀ := by
  rfl

end LocalChartAt





def coordinateFrameAt (x₀ : M) :
    CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x :=
  (coordinateTrivializationAt (I := I) x₀).localFrame (Module.finBasis 𝕜 E)


def coordinateFrameSet (x₀ : M) : Set M :=
  (coordinateTrivializationAt (I := I) x₀).baseSet

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem coordinateFrameSet_open (x₀ : M) :
    IsOpen (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).open_baseSet

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem coordinateFrameAt_mem (x₀ : M) :
    x₀ ∈ coordinateFrameSet (I := I) x₀ :=
  mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_isLocalFrame (x₀ : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (∞ : WithTop ℕ∞) (Module.finBasis 𝕜 E)

namespace LocalChartAt







structure Frame {x₀ : M} (C : LocalChartAt (I := I) x₀) where
  domain : Set M
  frame : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame domain
  isOpen_domain : IsOpen domain
  mem_base : x₀ ∈ domain
  domain_subset_source : domain ⊆ C.source

namespace Frame


omit [CompleteSpace 𝕜] in
theorem mem_source {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) :
    x ∈ C.source :=
  F.domain_subset_source hx


def basisAt {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame) {x : M}
    (hx : x ∈ F.domain) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x) :=
  F.hframe.toBasisAt hx

omit [CompleteSpace 𝕜] in
theorem basisAt_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    F.basisAt hx i = F.frame i x := by
  simp [basisAt]

end Frame



def toFrame {x₀ : M} (C : LocalChartAt (I := I) x₀) : C.Frame where
  domain := C.triv.baseSet
  frame := by
    haveI : MemTrivializationAtlas C.triv := C.triv_mem
    exact C.triv.localFrame (Module.finBasis 𝕜 E)
  hframe := by
    haveI : MemTrivializationAtlas C.triv := C.triv_mem
    exact C.triv.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (Module.finBasis 𝕜 E)
  isOpen_domain := C.triv.open_baseSet
  mem_base := by
    rw [C.triv_baseSet]
    exact C.mem_source
  domain_subset_source := by
    intro x hx
    rw [C.triv_baseSet] at hx
    exact hx


def defaultFrame (x₀ : M) : (LocalChartAt.default (I := I) x₀).Frame where
  domain := coordinateFrameSet (I := I) x₀
  frame := coordinateFrameAt (I := I) x₀
  hframe := coordinateFrameAt_isLocalFrame (I := I) x₀
  isOpen_domain := coordinateFrameSet_open (I := I) x₀
  mem_base := coordinateFrameAt_mem (I := I) x₀
  domain_subset_source := by
    intro x hx
    have hx_triv : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv

omit [CompleteSpace 𝕜] in
theorem defaultFrame_domain (x₀ : M) :
    (LocalChartAt.defaultFrame (I := I) x₀).domain =
      coordinateFrameSet (I := I) x₀ := by
  rfl

omit [CompleteSpace 𝕜] in
theorem defaultFrame_frame (x₀ : M) :
    (LocalChartAt.defaultFrame (I := I) x₀).frame =
      coordinateFrameAt (I := I) x₀ := by
  rfl

end LocalChartAt


def coordinateFrameAt_isLocalFrame_one (x₀ : M) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (1 : WithTop ℕ∞) (Module.finBasis 𝕜 E)


omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_mdifferentiableAt (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    MDiffAt (T% (coordinateFrameAt (I := I) x₀ i)) x₀ := by
  exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
    (coordinateFrameSet_open (I := I) x₀)
    (coordinateFrameAt_mem (I := I) x₀) i).mdifferentiableAt (by simp)


def coordinateFrameAt_basis (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x) :=
  (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordinateFrameAt_basis_apply (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt_basis (I := I) x₀ hx i =
      coordinateFrameAt (I := I) x₀ i x := by
  simp [coordinateFrameAt_basis]


def coordinateFrameAt_toBasis (x₀ : M) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x₀) :=
  coordinateFrameAt_basis (I := I) x₀ (coordinateFrameAt_mem (I := I) x₀)

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordinateFrameAt_toBasis_apply (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt_toBasis (I := I) x₀ i =
      coordinateFrameAt (I := I) x₀ i x₀ := by
  simp [coordinateFrameAt_toBasis]



omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_coeff_eq_toBasis_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j x₀ Z =
      (coordinateFrameAt_toBasis (I := I) x₀).coord j Z := by
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt
          (coordinateFrameAt_mem (I := I) x₀) =
        coordinateFrameAt_toBasis (I := I) x₀ := by
    ext k
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [coordinateFrameAt_toBasis_apply]
  unfold IsLocalFrameOn.coeff
  rw [dif_pos (coordinateFrameAt_mem (I := I) x₀)]
  rw [hbasis]



omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_apply_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((Module.finBasis 𝕜 E) i) := by
  have hx_src : x ∈ (chartAt H x₀).source := by
    have hx_triv : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv
  have hx_triv :
      x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    change x ∈ coordinateFrameSet (I := I) x₀
    exact hx
  change (trivializationAt E (TangentSpace I : M -> Type _) x₀).localFrame
      (Module.finBasis 𝕜 E) i x =
    (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
      ((Module.finBasis 𝕜 E) i)
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := trivializationAt E (TangentSpace I : M -> Type _) x₀)
    (b := Module.finBasis 𝕜 E) (i := i) hx_triv]
  simpa [Bundle.Trivialization.basisAt, Trivialization.symmL_apply, extChartAt] using
    congrArg (fun L : E →L[𝕜] TangentSpace I x => L ((Module.finBasis 𝕜 E) i))
      (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem LocalChartAt.default_source (x₀ : M) :
    (LocalChartAt.default (I := I) x₀).source =
      coordinateFrameSet (I := I) x₀ := by
  simp only [LocalChartAt.source, LocalChartAt.default, coordinateFrameSet,
    coordinateTrivializationAt, TangentBundle.trivializationAt_baseSet]



omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_basis_triv
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt
        𝕜 x ((coordinateFrameAt_basis (I := I) x₀ hx) i) =
      (Module.finBasis 𝕜 E) i := by
  let e := coordinateTrivializationAt (I := I) x₀
  have hxE : x ∈ e.baseSet := by
    change x ∈ coordinateFrameSet (I := I) x₀
    exact hx
  have hx_src : x ∈ (chartAt H x₀).source := by
    have hx_triv : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv
  have hframe :
      (coordinateFrameAt_basis (I := I) x₀ hx) i =
        e.symmL 𝕜 x ((Module.finBasis 𝕜 E) i) := by
    rw [coordinateFrameAt_basis_apply]
    rw [coordinateFrameAt_apply_of_mem (I := I) hx i]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
    rfl
  rw [hframe]
  exact e.continuousLinearMapAt_symmL (R := 𝕜) hxE ((Module.finBasis 𝕜 E) i)



omit [CompleteSpace 𝕜] in
theorem basisRepr_eq_triv
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) :
    (coordinateFrameAt_basis (I := I) x₀ hx).repr v =
      (Module.finBasis 𝕜 E).repr
        ((coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt 𝕜 x v) := by
  classical
  let b := coordinateFrameAt_basis (I := I) x₀ hx
  let e := Module.finBasis 𝕜 E
  let L := (coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt 𝕜 x
  have hLbasis : ∀ i, L (b i) = e i := by
    intro i
    exact coordinateFrameAt_basis_triv (I := I) x₀ hx i
  have hLv : L v = ∑ i, (b.repr v i) • e i := by
    calc
      L v = L (∑ i, (b.repr v i) • b i) := by
          exact congrArg L (b.sum_repr v).symm
      _ = ∑ i, L ((b.repr v i) • b i) := by
          rw [map_sum]
      _ = ∑ i, (b.repr v i) • L (b i) := by
          simp
      _ = ∑ i, (b.repr v i) • e i := by
          simp [hLbasis]
  rw [hLv]
  ext i
  exact (congrFun (e.repr_sum_self (fun i => b.repr v i)) i).symm


omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_toBasis_eq_finBasis (x₀ : M) :
    coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis 𝕜 E := by
  ext i
  rw [coordinateFrameAt_toBasis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) (coordinateFrameAt_mem (I := I) x₀) i]
  rw [mfderivWithin_range_extChartAt_symm]
  rfl








def normalCoordLinearEquiv (x : M) : TangentSpace I x ≃L[𝕜] E :=
  ContinuousLinearEquiv.refl 𝕜 E


def normalCoord (x : M) (v : TangentSpace I x) : E :=
  normalCoordLinearEquiv (I := I) x v

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalCoord_zero (x : M) :
    normalCoord (I := I) x (0 : TangentSpace I x) = 0 := by
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
theorem normalCoord_injective (x : M) :
    Function.Injective (normalCoord (I := I) x) :=
  (normalCoordLinearEquiv (I := I) x).injective




def normalHCoord (x : M) (v : TangentSpace I x) : H :=
  I.symm (normalCoord (I := I) x v)






def normalHCoordHomeomorph [I.Boundaryless] (x : M) :
    TangentSpace I x ≃ₜ H :=
  (normalCoordLinearEquiv (I := I) x).toHomeomorph.trans I.toHomeomorph.symm

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordHomeomorph_apply [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    normalHCoordHomeomorph (I := I) x v = normalHCoord (I := I) x v := by
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem model_normalHCoord [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    I (normalHCoord (I := I) x v) = normalCoord (I := I) x v := by
  simpa [normalHCoord] using
    I.toHomeomorph.right_inv (normalCoord (I := I) x v)



def modelSymmDiffeomorph [I.Boundaryless] :
    E ≃ₘ^(∞ : WithTop ℕ∞)⟮𝓘(𝕜, E), I⟯ H where
  toEquiv := I.toHomeomorph.symm.toEquiv
  contMDiff_toFun := by
    rw [← contMDiffOn_univ]
    simpa [ModelWithCorners.range_eq_univ (I := I)] using
      (contMDiffOn_model_symm (I := I) (n := (∞ : WithTop ℕ∞)))
  contMDiff_invFun := contMDiff_model (I := I)






def normalHCoordDiffeomorph [I.Boundaryless] (x : M) :
    TangentSpace I x ≃ₘ^(∞ : WithTop ℕ∞)⟮𝓘(𝕜, TangentSpace I x), I⟯ H :=
  (normalCoordLinearEquiv (I := I) x).toDiffeomorph.trans
    (modelSymmDiffeomorph (I := I))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordDiffeomorph_apply [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    normalHCoordDiffeomorph (I := I) x v = normalHCoord (I := I) x v := by
  rfl

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordDiffeomorph_toHomeomorph [I.Boundaryless] (x : M) :
    (normalHCoordDiffeomorph (I := I) x).toHomeomorph =
      normalHCoordHomeomorph (I := I) x := by
  ext v
  rfl



omit [CompleteSpace 𝕜] in
theorem coordCoeff_eq_chart {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i x v =
      (Module.finBasis 𝕜 E).repr
        ((mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x) v) i := by
  have hbasis :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx =
        coordinateFrameAt_basis (I := I) x₀ hx := by
    ext j
    rw [IsLocalFrameOn.toBasisAt_coe]
    rw [coordinateFrameAt_basis_apply]
  have hcoeff :
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i x v =
        (coordinateFrameAt_basis (I := I) x₀ hx).repr v i := by
    unfold IsLocalFrameOn.coeff
    rw [dif_pos hx]
    rw [hbasis]
    rfl
  have hx_chart : x ∈ (chartAt H x₀).source := by
    have hx_triv : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv
  rw [hcoeff]
  rw [basisRepr_eq_triv (I := I) x₀ hx v]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I) (𝕜 := 𝕜) (x₀ := x₀) (x := x) hx_chart]
  rfl

omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_pullback_eq_const (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => (Module.finBasis 𝕜 E i : E) := by
  haveI : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    change (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy_src
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((Module.finBasis 𝕜 E) i)

omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_pullback_eq_const_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x)]
        fun _ : E => (Module.finBasis 𝕜 E i : E) := by
  haveI : IsManifold I (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hx_src : x ∈ (extChartAt I x₀).source := by
    have hx_chart : x ∈ (chartAt H x₀).source := by
      have hx_triv : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
        change x ∈ coordinateFrameSet (I := I) x₀
        exact hx
      rw [TangentBundle.trivializationAt_baseSet] at hx_triv
      exact hx_triv
    rw [extChartAt_source]
    exact hx_chart
  filter_upwards [extChartAt_target_mem_nhdsWithin' (I := I) hx_src] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    change (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy_src
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base i]
  rw [(extChartAt I x₀).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy)
    ((Module.finBasis 𝕜 E) i)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
private theorem lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin 𝕜 (fun _ : E => v) (fun _ : E => w) s x = 0 := by
  simp [VectorField.lieBracketWithin]






omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_bracket_zero (x₀ : M) (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x₀ = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  have hleft :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ i) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis 𝕜 E i : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ i
  have hright :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (coordinateFrameAt (I := I) x₀ j) (Set.range I)
        =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' Set.univ ∩ Set.range I]
            (extChartAt I x₀ x₀)]
          fun _ : E => (Module.finBasis 𝕜 E j : E) := by
    simpa using coordinateFrame_pullback_eq_const (I := I) x₀ j
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright (by simp)]
  rw [lieBracketWithin_const_const]
  exact ContinuousLinearMap.map_zero _






theorem coordinateFrameAt_bracket_zero_of_mem [IsRCLikeNormedField 𝕜] {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x = 0 := by
  haveI : IsManifold I (minSmoothness 𝕜 2) M :=
    by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact IsManifold.of_le (I := I) (M := M) (n := ∞) (by
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let V : (x : M) → TangentSpace I x := coordinateFrameAt (I := I) x₀ i
  let W : (x : M) → TangentSpace I x := coordinateFrameAt (I := I) x₀ j
  let z : E := extChartAt I x₀ x
  let f : E → M := (extChartAt I x₀).symm
  have hx_src : x ∈ (extChartAt I x₀).source := by
    have hx_chart : x ∈ (chartAt H x₀).source := by
      have hx_triv : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
        change x ∈ coordinateFrameSet (I := I) x₀
        exact hx
      rw [TangentBundle.trivializationAt_baseSet] at hx_triv
      exact hx_triv
    rw [extChartAt_source]
    exact hx_chart
  have hz_target : z ∈ (extChartAt I x₀).target := by
    exact (extChartAt I x₀).map_source hx_src
  have hz_range : z ∈ Set.range I :=
    extChartAt_target_subset_range x₀ hz_target
  have hfz : f z = x := by
    exact (extChartAt I x₀).left_inv hx_src
  have hVdiff : MDiffAt[Set.univ] (T% V) (f z) := by
    rw [hfz]
    exact (((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) hx i).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hWdiff : MDiffAt[Set.univ] (T% W) (f z) := by
    rw [hfz]
    exact (((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) hx j).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hf :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞) f (Set.range I) z :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) (x := x₀) hz_target
  have hpb :=
    VectorField.mpullbackWithin_mlieBracketWithin
      (I := 𝓘(𝕜, E)) (I' := I) (n := (∞ : WithTop ℕ∞))
      (f := f) (V := V) (W := W) (x₀ := z)
      (s := Set.range I) (t := Set.univ)
      hVdiff hWdiff I.uniqueMDiffOn hf hz_range
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
      (by simp only [Set.preimage_univ]; exact Filter.univ_mem)
      (by
        simpa [z] using I.range_subset_closure_interior hz_range)
  have hleft :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I f V (Set.range I)
        =ᶠ[𝓝[Set.range I] z]
          fun _ : E => (Module.finBasis 𝕜 E i : E) := by
    simpa [f, V, z] using coordinateFrame_pullback_eq_const_of_mem (I := I) hx i
  have hright :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I f W (Set.range I)
        =ᶠ[𝓝[Set.range I] z]
          fun _ : E => (Module.finBasis 𝕜 E j : E) := by
    simpa [f, W, z] using coordinateFrame_pullback_eq_const_of_mem (I := I) hx j
  have hrhs :
      VectorField.mlieBracketWithin 𝓘(𝕜, E)
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I f V (Set.range I))
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I f W (Set.range I))
          (Set.range I) z = 0 := by
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hleft hright hz_range]
    exact lieBracketWithin_const_const
  rw [hrhs] at hpb
  rw [VectorField.mlieBracketWithin_univ] at hpb
  simp only [VectorField.mpullbackWithin_apply] at hpb
  have hInv :
      (mfderiv[Set.range I] f z).IsInvertible := by
    simpa [f, z] using isInvertible_mfderivWithin_extChartAt_symm (I := I) hz_target
  have hzero := congrArg (fun v => (mfderiv[Set.range I] f z) v) hpb
  change VectorField.mlieBracket I V W x = 0
  rw [← hfz]
  simpa [ContinuousLinearMap.IsInvertible.self_apply_inverse hInv] using hzero


structure CoordinateFrameAt (x₀ : M) where
  u : Set M
  frame : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x
  hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u
  isOpen_u : IsOpen u
  mem_base : x₀ ∈ u
  bracket_zero : ∀ i j : CoordinateIdx (𝕜 := 𝕜) E,
    VectorField.mlieBracket I (frame i) (frame j) x₀ = 0


def coordinateFramePackageAt (x₀ : M) : CoordinateFrameAt (I := I) x₀ where
  u := coordinateFrameSet (I := I) x₀
  frame := coordinateFrameAt (I := I) x₀
  hframe := coordinateFrameAt_isLocalFrame (I := I) x₀
  isOpen_u := coordinateFrameSet_open (I := I) x₀
  mem_base := coordinateFrameAt_mem (I := I) x₀
  bracket_zero := coordinateFrameAt_bracket_zero (I := I) x₀

namespace LocalChartAt
namespace Frame


def comp0S {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {s : ℕ} {x : M} (hx : x ∈ F.domain)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  component0S (I := I) (F.basisAt hx) A slots

omit [CompleteSpace 𝕜] in
theorem comp0S_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {s : ℕ} {x : M} (hx : x ∈ F.domain)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    F.comp0S hx A slots =
      A (fun a => F.basisAt hx (slots a)) :=
  rfl


def compRS {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {r s : ℕ} {x : M} (hx : x ∈ F.domain)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  componentRS_gen (I := I) (F.basisAt hx) T upper lower

theorem compRS_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {r s : ℕ} {x : M} (hx : x ∈ F.domain)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    F.compRS hx T upper lower =
      componentRS_gen (I := I) (F.basisAt hx) T upper lower :=
  rfl

end Frame
end LocalChartAt


def coordComponent0SAt {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  component0S (I := I) (coordinateFrameAt_toBasis (I := I) x₀) A slots

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordComponent0SAt_apply {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I) A slots =
      A (fun a => coordinateFrameAt_toBasis (I := I) x₀ (slots a)) :=
  rfl


def coordComponentRSAt {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  componentRS_gen (I := I) (coordinateFrameAt_toBasis (I := I) x₀) T upper lower

@[simp]
theorem coordComponentRSAt_apply {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I) T upper lower =
      componentRS_gen (I := I) (coordinateFrameAt_toBasis (I := I) x₀) T upper lower :=
  rfl



omit [CompleteSpace 𝕜] in
theorem coordComponent0SAt_congr_slots {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    {slots slots' : Fin s -> CoordinateIdx (𝕜 := 𝕜) E}
    (h : slots = slots') :
    coordComponent0SAt (I := I) A slots = coordComponent0SAt (I := I) A slots' := by
  rw [h]



theorem coordComponentRSAt_congr_slots {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    {upper upper' : Fin r -> CoordinateIdx (𝕜 := 𝕜) E}
    {lower lower' : Fin s -> CoordinateIdx (𝕜 := 𝕜) E}
    (hu : upper = upper') (hl : lower = lower') :
    coordComponentRSAt (I := I) T upper lower =
      coordComponentRSAt (I := I) T upper' lower' := by
  rw [hu, hl]




theorem coordExt0SAt {s : ℕ} {x₀ : M}
    {A B : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀}
    (h : ∀ slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      coordComponent0SAt (I := I) A slots = coordComponent0SAt (I := I) B slots) :
    A = B :=
  ext0S_basis (I := I) (coordinateFrameAt_toBasis (I := I) x₀) h



theorem coordExtRSAt {r s : ℕ} {x₀ : M}
    {A B : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀}
    (h : ∀ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
         ∀ lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      coordComponentRSAt (I := I) A upper lower =
        coordComponentRSAt (I := I) B upper lower) :
    A = B :=
  extRS_basis_gen (I := I) (coordinateFrameAt_toBasis (I := I) x₀) h

namespace LocalChartAt
namespace Frame



omit [CompleteSpace 𝕜] in
theorem default_comp0S {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (LocalChartAt.defaultFrame (I := I) x₀).comp0S
        (LocalChartAt.defaultFrame (I := I) x₀).mem_base A slots =
      coordComponent0SAt (I := I) A slots := by
  simp [LocalChartAt.Frame.comp0S, LocalChartAt.Frame.basisAt,
    LocalChartAt.defaultFrame, coordComponent0SAt, coordinateFrameAt_toBasis,
    coordinateFrameAt_basis]



theorem default_compRS {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (LocalChartAt.defaultFrame (I := I) x₀).compRS
        (LocalChartAt.defaultFrame (I := I) x₀).mem_base T upper lower =
      coordComponentRSAt (I := I) T upper lower := by
  simp [LocalChartAt.Frame.compRS, LocalChartAt.Frame.basisAt,
    LocalChartAt.defaultFrame, coordComponentRSAt, coordinateFrameAt_toBasis,
    coordinateFrameAt_basis]

end Frame
end LocalChartAt

end DifferentialGeometry.Tensor.Coordinates
