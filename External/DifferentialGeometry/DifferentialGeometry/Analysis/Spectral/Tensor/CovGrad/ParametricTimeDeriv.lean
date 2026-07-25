import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral









noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [CompactSpace M] in


private theorem timeDeriv2_at
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : M × ℝ → F} {p₀ : M × ℝ} {m n : WithTop ℕ∞}
    (hf : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n f p₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) m
      (fun p : M × ℝ => deriv (fun t => f (p.1, t)) p.2) p₀ := by
  have hrw :
      (fun p : M × ℝ => deriv (fun t => f (p.1, t)) p.2) =
        fun p : M × ℝ =>
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun t => f (p.1, t)) p.2) (1 : ℝ) := by
    funext p
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv
      (f := fun t => f (p.1, t)) (x := p.2)).symm
  rw [hrw]
  have harg :
      ContMDiffAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, ℝ)) n
        (fun q : (M × ℝ) × ℝ => (q.1.1, q.2)) (p₀, p₀.2) :=
    ContMDiffAt.prodMk contMDiffAt_fst.fst contMDiffAt_snd
  have hf' :
      ContMDiffAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n
        (fun q : (M × ℝ) × ℝ => f (q.1.1, q.2)) (p₀, p₀.2) :=
    hf.comp (p₀, p₀.2) harg
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F))
      (f := fun (p : M × ℝ) (t : ℝ) => f (p.1, t))
      (g := fun p : M × ℝ => p.2)
      (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ))
      (x₀ := p₀) (m := m) (n := n)
      hf' contMDiffAt_snd contMDiffAt_id contMDiffAt_const hmn
  simpa [inTangentCoordinates_model_space] using hApply

private noncomputable def timeDerivFib
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) (x : M) (t : ℝ) :
    TensorRSSpace b c I x :=
  TensorRSSpace.ofModel (I := I) (x := x)
    (deriv (fun τ => TensorRSSpace.toModel ((Φ τ).toSection x)) t)

omit [CompactSpace M] in
private theorem modelPath_diff
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (t : ℝ) (ht : t ∈ S) :
    DifferentiableAt ℝ
      (fun τ => TensorRSSpace.toModel ((Φ τ).toSection x)) t := by
  let e := trivializationAt (TensorRSModel b c ℝ E)
    (fun y : M => TensorRSSpace b c I y) x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hsource :
      (TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun y : M => TensorRSSpace b c I y) x
        ((Φ t).toSection x)) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact hxe
  have hjpAt : ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun y : M => TensorRSSpace b c I y) q.1
        ((Φ q.2).toSection q.1)) (x, t) :=
    (hjoint (x, t) ⟨Set.mem_univ _, ht⟩).contMDiffAt
      ((isOpen_univ.prod hS).mem_nhds ⟨Set.mem_univ _, ht⟩)
  have hcoordAt : ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel b c ℝ E) ∞
      (fun q : M × ℝ => (e ⟨q.1, (Φ q.2).toSection q.1⟩).2) (x, t) :=
    ((e.contMDiffAt_iff
      (f := fun q : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun y : M => TensorRSSpace b c I y) q.1
        ((Φ q.2).toSection q.1)) (x₀ := (x, t)) hsource).1 hjpAt).2
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun τ : ℝ => (x, τ)) t :=
    (contMDiffAt_const (c := x)).prodMk
      (contMDiffAt_id (I := 𝓘(ℝ, ℝ)) (x := t))
  have hsliceMD : ContMDiffAt 𝓘(ℝ, ℝ)
      𝓘(ℝ, TensorRSModel b c ℝ E) ∞
      (fun τ : ℝ => (e ⟨x, (Φ τ).toSection x⟩).2) t :=
    hcoordAt.comp
      (f := fun τ : ℝ => (x, τ))
      (g := fun q : M × ℝ => (e ⟨q.1, (Φ q.2).toSection q.1⟩).2)
      t hpair
  have hslice : DifferentiableAt ℝ
      (fun τ : ℝ => (e ⟨x, (Φ τ).toSection x⟩).2) t :=
    (contMDiffAt_iff_contDiffAt.mp hsliceMD).differentiableAt (by simp)
  let R := tensorRSSpace_continuousLinearEquiv (I := I) b c x
  let L := e.continuousLinearEquivAt ℝ x hxe
  let K := R.symm.trans L
  have hreadoff (T : TensorRSSpace b c I x) :
      (e ⟨x, T⟩).2 = L T := rfl
  have hcoordEq :
      (fun τ : ℝ => (e ⟨x, (Φ τ).toSection x⟩).2) =
        fun τ : ℝ => K (TensorRSSpace.toModel ((Φ τ).toSection x)) := by
    funext τ
    rw [hreadoff]
    change L ((Φ τ).toSection x) = L (R.symm (R ((Φ τ).toSection x)))
    rw [R.symm_apply_apply]
  rw [hcoordEq] at hslice
  have hback := K.symm.toContinuousLinearMap.differentiableAt.comp t hslice
  convert hback using 1
  funext τ
  exact (K.symm_apply_apply _).symm

omit [CompactSpace M] in
private theorem coord_deriv_eq
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (x₀ : M)
    (p : M × ℝ) (hp : p ∈ (Set.univ : Set M) ×ˢ S)
    (hpe : p.1 ∈ (trivializationAt (TensorRSModel b c ℝ E)
      (fun x : M => TensorRSSpace b c I x) x₀).baseSet) :
    ((trivializationAt (TensorRSModel b c ℝ E)
      (fun x : M => TensorRSSpace b c I x) x₀)
        ⟨p.1, timeDerivFib (I := I) (M := M) g b c Φ p.1 p.2⟩).2 =
      deriv (fun t => ((trivializationAt (TensorRSModel b c ℝ E)
        (fun x : M => TensorRSSpace b c I x) x₀)
          ⟨p.1, (Φ t).toSection p.1⟩).2) p.2 := by
  let e := trivializationAt (TensorRSModel b c ℝ E)
    (fun x : M => TensorRSSpace b c I x) x₀
  let L := e.continuousLinearEquivAt ℝ p.1 hpe
  have hsource :
      (TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1)) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact hpe
  have hjpAt : ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) q.1
        ((Φ q.2).toSection q.1)) p :=
    (hjoint p hp).contMDiffAt
      ((isOpen_univ.prod hS).mem_nhds hp)
  have hcoordAt : ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel b c ℝ E) ∞
      (fun q : M × ℝ => (e ⟨q.1, (Φ q.2).toSection q.1⟩).2) p :=
    ((e.contMDiffAt_iff
      (f := fun q : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) q.1
        ((Φ q.2).toSection q.1)) (x₀ := p) hsource).1 hjpAt).2
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (p.1, t)) p.2 := by
    exact (contMDiffAt_const (c := p.1)).prodMk
      (contMDiffAt_id (I := 𝓘(ℝ, ℝ)) (x := p.2))
  have hsliceMD : ContMDiffAt 𝓘(ℝ, ℝ)
      𝓘(ℝ, TensorRSModel b c ℝ E) ∞
      (fun t : ℝ => (e ⟨p.1, (Φ t).toSection p.1⟩).2) p.2 :=
    hcoordAt.comp
      (f := fun t : ℝ => (p.1, t))
      (g := fun q : M × ℝ => (e ⟨q.1, (Φ q.2).toSection q.1⟩).2)
      p.2 hpair
  have hslice : DifferentiableAt ℝ
      (fun t : ℝ => (e ⟨p.1, (Φ t).toSection p.1⟩).2) p.2 :=
    (contMDiffAt_iff_contDiffAt.mp hsliceMD).differentiableAt (by simp)
  let R := tensorRSSpace_continuousLinearEquiv (I := I) b c p.1
  have hreadoff (T : TensorRSSpace b c I p.1) :
      (e ⟨p.1, T⟩).2 = L T := rfl
  let K := R.symm.trans L
  have hcoordEq :
      (fun t : ℝ => (e ⟨p.1, (Φ t).toSection p.1⟩).2) =
        fun t : ℝ => K (TensorRSSpace.toModel ((Φ t).toSection p.1)) := by
    funext t
    rw [hreadoff]
    change L ((Φ t).toSection p.1) = L (R.symm (R ((Φ t).toSection p.1)))
    rw [R.symm_apply_apply]
  have hmodelDiff : DifferentiableAt ℝ
      (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection p.1)) p.2 := by
    rw [hcoordEq] at hslice
    have hback := K.symm.toContinuousLinearMap.differentiableAt.comp p.2 hslice
    convert hback using 1
    funext t
    exact (K.symm_apply_apply _).symm
  have hcomp := K.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    p.2 hmodelDiff.hasDerivAt
  rw [hreadoff, hcoordEq]
  change K (deriv
    (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection p.1)) p.2) = _
  exact hcomp.deriv.symm

omit [CompactSpace M] in


private theorem timeDeriv_joint
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        (timeDerivFib (I := I) (M := M) g b c Φ p.1 p.2))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  let e := trivializationAt (TensorRSModel b c ℝ E)
    (fun x : M => TensorRSSpace b c I x) p₀.1
  have hcoordWithin :=
    (Bundle.contMDiffWithinAt_totalSpace
      (F := TensorRSModel b c ℝ E)
      (E := fun x : M => TensorRSSpace b c I x)
      (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp (hjoint p₀ hp₀) |>.2
  have hcoordAt : ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, TensorRSModel b c ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1, (Φ p.2).toSection p.1⟩).2) p₀ :=
    hcoordWithin.contMDiffAt ((isOpen_univ.prod hS).mem_nhds hp₀)
  have hd := timeDeriv2_at (I := I) (M := M)
    (m := (∞ : WithTop ℕ∞)) (n := (∞ : WithTop ℕ∞)) hcoordAt (by simp)
  refine hd.contMDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in 𝓝[Set.univ ×ˢ S] p₀,
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
    filter_upwards [hbase, self_mem_nhdsWithin] with p hpbase hp
    exact coord_deriv_eq (I := I) (M := M) g b c Φ hS hjoint p₀.1 p hp hpbase
  · exact coord_deriv_eq (I := I) (M := M) g b c Φ hS hjoint p₀.1 p₀ hp₀
      (mem_baseSet_trivializationAt _ _ _)





theorem exists_timeDerivCc
    (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : ℝ → SmoothCcTensor g b c) {S : Set ℝ} (hS : IsOpen S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ∃ dΦ : ℝ → SmoothCcTensor g b c,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
          (E := fun x : M => TensorRSSpace b c I x) p.1
          ((dΦ p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ S) ∧
      ∀ t ∈ S, ∀ x : M, ∀ W : Tensor0SSpace b I x,
        ∀ slots : Fin c → E,
          HasDerivAt
            (fun τ => Tensor0SSpace.toModel
              (((Φ τ).toSection x) W) slots)
            (Tensor0SSpace.toModel (((dΦ t).toSection x) W) slots) t := by
  classical
  have hraw := timeDeriv_joint (I := I) (M := M) g b c Φ hS hjoint
  have hslice : ∀ t : ℝ, t ∈ S →
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel b c ℝ E)
          (E := fun y : M => TensorRSSpace b c I y) x
          (timeDerivFib (I := I) (M := M) g b c Φ x t)) := by
    intro t ht
    have harg : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => (x, t)) (Set.univ : Set M) :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ S) :=
      fun x _ => ⟨Set.mem_univ _, ht⟩
    have hcomp := hraw.comp harg hmaps
    rw [contMDiffOn_univ] at hcomp
    exact hcomp
  let dSlice : ∀ t : ℝ, t ∈ S → SmoothCcTensor g b c :=
    fun t ht =>
      { toSection :=
          ⟨fun x => timeDerivFib (I := I) (M := M) g b c Φ x t,
            hslice t ht⟩
        hasCompactSupport := HasCompactSupport.of_compactSpace _ }
  let dΦ : ℝ → SmoothCcTensor g b c := fun t =>
    if ht : t ∈ S then dSlice t ht else 0
  have hdjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel b c ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel b c ℝ E)
        (E := fun x : M => TensorRSSpace b c I x) p.1
        ((dΦ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
    refine hraw.congr ?_
    intro p hp
    simp only [dΦ, dif_pos hp.2, dSlice]
    rfl
  refine ⟨dΦ, hdjoint, ?_⟩
  intro t ht x W slots
  let Q : TensorRSModel b c ℝ E →L[ℝ] ℝ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => E) ℝ slots).comp
      (ContinuousLinearMap.apply ℝ (Tensor0SModel c ℝ E)
        (Tensor0SSpace.toModel W))
  have hmodel := modelPath_diff (I := I) (M := M) g b c Φ hS hjoint x t ht
  have hderiv := Q.hasFDerivAt.comp_hasDerivAt t hmodel.hasDerivAt
  have hpath :
      (fun τ => Tensor0SSpace.toModel (((Φ τ).toSection x) W) slots) =
        fun τ => Q (TensorRSSpace.toModel ((Φ τ).toSection x)) := by
    funext τ
    rw [toModel_tensorRS_apply (I := I) b c x ((Φ τ).toSection x) W]
    rfl
  have hdΦ : dΦ t = dSlice t ht := by
    simp only [dΦ, dif_pos ht]
  have hvalue :
      Tensor0SSpace.toModel (((dΦ t).toSection x) W) slots =
        Q (deriv (fun τ => TensorRSSpace.toModel ((Φ τ).toSection x)) t) := by
    rw [hdΦ]
    change Tensor0SSpace.toModel
      ((timeDerivFib (I := I) (M := M) g b c Φ x t) W) slots = _
    rw [toModel_tensorRS_apply (I := I) b c x
      (timeDerivFib (I := I) (M := M) g b c Φ x t) W]
    simp only [timeDerivFib, TensorRSSpace.toModel_ofModel]
    rfl
  rw [hpath, hvalue]
  exact hderiv

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
