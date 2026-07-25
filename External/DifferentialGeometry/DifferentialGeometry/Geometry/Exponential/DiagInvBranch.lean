import DifferentialGeometry.Geometry.Exponential.ExpVariationSmooth
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false










noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]






structure DiagInvBranch
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) where
  hom : OpenPartialHomeomorph (TangentBundle I M) (M × M)
  zero_mem :
    (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) ∈ hom.source
  hom_eq : EqOn (fun u ↦ hom u) (diagExp (I := I) g hEnorm) hom.source
  inv_inf : ContMDiffOn (I.prod I) I.tangent ∞ hom.symm hom.target

namespace DiagInvBranch


def inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    M × M → TangentBundle I M :=
  B.hom.symm


def dom
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) : Set (M × M) :=
  B.hom.target


omit [ConnectedSpace M] in
theorem right_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {y : M × M} (hy : y ∈ B.dom) :
    diagExp (I := I) g hEnorm (B.inv y) = y := by
  have hu : B.inv y ∈ B.hom.source := B.hom.map_target hy
  calc
    diagExp (I := I) g hEnorm (B.inv y) = B.hom (B.inv y) :=
      (B.hom_eq hu).symm
    _ = y := by simpa only [inv] using B.hom.right_inv hy


omit [ConnectedSpace M] in
theorem left_inv
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {u : TangentBundle I M} (hu : u ∈ B.hom.source) :
    B.inv (diagExp (I := I) g hEnorm u) = u := by
  calc
    B.inv (diagExp (I := I) g hEnorm u) = B.inv (B.hom u) :=
      congrArg B.inv (B.hom_eq hu).symm
    _ = u := by simpa only [inv] using B.hom.left_inv hu



omit [ConnectedSpace M] in
theorem inv_eq_of_exp
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p y pt : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {v : TangentSpace I y}
    (hvsrc : (⟨y, v⟩ : TangentBundle I M) ∈ B.hom.source)
    (hexp : expMapIntrinsic (I := I) g hEnorm y v = pt) :
    B.inv (y, pt) = (⟨y, v⟩ : TangentBundle I M) := by
  simpa only [diagExp_apply, hexp] using B.left_inv hvsrc



omit [ConnectedSpace M] in
theorem proj_eq
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {y : M × M} (hy : y ∈ B.dom) :
    (B.inv y).proj = y.1 := by
  simpa only [diagExp_fst] using congrArg Prod.fst (B.right_inv hy)



omit [ConnectedSpace M] in
theorem inv_snd_inf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p pt : M} (B : DiagInvBranch (I := I) g hEnorm p) {S : Set M}
    (hdom : ∀ y ∈ S, (y, pt) ∈ B.dom) :
    ContMDiffOn I I.tangent ∞
      (T% fun y => show TangentSpace I y from (B.inv (y, pt)).snd) S := by
  have hpair : ContMDiffOn I (I.prod I) ∞ (fun y : M ↦ (y, pt)) S :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn
  have hinv : ContMDiffOn I I.tangent ∞
      (fun y : M ↦ B.inv (y, pt)) S := by
    simpa only [inv, dom, Function.comp_apply] using B.inv_inf.comp hpair hdom
  refine hinv.congr ?_
  intro y hy
  refine TotalSpace.ext (B.proj_eq (hdom y hy)).symm ?_
  exact heq_of_eq rfl



omit [ConnectedSpace M] in
theorem exp_eq
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    {y : M × M} (hy : y ∈ B.dom) :
    expMapIntrinsic (I := I) g hEnorm y.1 (B.inv y).snd = y.2 := by
  have h := congrArg Prod.snd (B.right_inv hy)
  simp only [diagExp_snd] at h
  rwa [B.proj_eq hy] at h



omit [ConnectedSpace M] in
theorem inv_eq_normal_lt
    [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p y q : M} (B : DiagInvBranch (I := I) g hEnorm p)
    (hy : (y, q) ∈ B.dom)
    (hsmall : Real.sqrt
      (g.inner y (B.inv (y, q)).snd (B.inv (y, q)).snd) <
        expDiffeoRadius (I := I) g hEnorm y) :
    B.inv (y, q) =
      (⟨y, (show TangentSpace I y from
        NormalCoordinates.normalChartAt (I := I) g y q)⟩ : TangentBundle I M) := by
  have hsrc := expDiffeo_mem_of_lt (I := I) g hEnorm y hsmall
  have hcompat := expDiffeo_eq_intr (I := I) g hEnorm y hsmall
  have hexp : NormalCoordinates.expMapDiffeo (I := I) g y
      (show TangentSpace I y from (B.inv (y, q)).snd) = q :=
    hcompat.trans (B.exp_eq hy)
  have hcoord : (NormalCoordinates.normalChartAt (I := I) g y q : E) =
      (B.inv (y, q)).snd := by
    have hleft := (NormalCoordinates.expMapDiffeo (I := I) g y).left_inv hsrc
    rw [hexp] at hleft
    exact hleft
  refine TotalSpace.ext (B.proj_eq hy) ?_
  exact heq_of_eq hcoord.symm


omit [ConnectedSpace M] in
theorem center_mem
    [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    (p, p) ∈ B.dom := by
  let z : TangentBundle I M := ⟨p, (0 : TangentSpace I p)⟩
  have hz : z ∈ B.hom.source := B.zero_mem
  have hmap : B.hom z ∈ B.hom.target := B.hom.map_source hz
  have heq : B.hom z = diagExp (I := I) g hEnorm z := by
    simpa only using B.hom_eq hz
  have hdiag : diagExp (I := I) g hEnorm z = (p, p) := by
    apply Prod.ext
    · rfl
    · exact expMapIntrinsic_zero (I := I) g hEnorm p
  rw [heq, hdiag] at hmap
  exact hmap


omit [ConnectedSpace M] in
theorem center_inv
    [T2Space (TangentBundle I M)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    B.inv (p, p) =
      (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) := by
  let z : TangentBundle I M := ⟨p, (0 : TangentSpace I p)⟩
  have hz : z ∈ B.hom.source := B.zero_mem
  have hleft := B.left_inv hz
  have hdiag : diagExp (I := I) g hEnorm z = (p, p) := by
    apply Prod.ext
    · rfl
    · exact expMapIntrinsic_zero (I := I) g hEnorm p
  rw [hdiag] at hleft
  exact hleft

end DiagInvBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
