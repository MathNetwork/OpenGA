import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false








noncomputable section

open Manifold Set TopologicalSpace
open scoped ContDiff

namespace DifferentialGeometry
namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type*} [TopologicalSpace H]
variable {H' : Type*} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
variable {n : WithTop ℕ∞}



def tangentHome (Φ : PartialDiffeomorph I J M N n) (hn : 1 ≤ n) :
    OpenPartialHomeomorph (TangentBundle I M) (TangentBundle J N) where
  toFun := tangentMapWithin I J (Φ : M → N) Φ.source
  invFun := tangentMapWithin J I (Φ.symm : N → M) Φ.target
  source := Bundle.TotalSpace.proj ⁻¹' Φ.source
  target := Bundle.TotalSpace.proj ⁻¹' Φ.target
  map_source' := by
    intro p hp
    change Φ p.proj ∈ Φ.target
    exact Φ.map_source' hp
  map_target' := by
    intro p hp
    change (Φ.symm : N → M) p.proj ∈ Φ.source
    exact Φ.map_target' hp
  left_inv' := by
    intro p hp
    have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
    have hcomp := tangentMapWithin_comp_at
      (I := I) (I' := J) (I'' := I)
      (f := (Φ : M → N)) (g := (Φ.symm : N → M))
      (s := Φ.source) (u := Φ.target) p
      (Φ.symm.mdifferentiableOn hn0 _ (Φ.map_source' hp))
      (Φ.mdifferentiableOn hn0 _ hp)
      (fun _ hx => Φ.map_source' hx)
      (Φ.open_source.uniqueMDiffOn p.proj hp)
    calc
      tangentMapWithin J I (Φ.symm : N → M) Φ.target
          (tangentMapWithin I J (Φ : M → N) Φ.source p) =
          tangentMapWithin I I
            ((Φ.symm : N → M) ∘ (Φ : M → N)) Φ.source p := hcomp.symm
      _ = tangentMapWithin I I (id : M → M) Φ.source p :=
        tangentMapWithin_congr (fun x hx => Φ.left_inv' hx) p hp
      _ = p := tangentMapWithin_id
        (Φ.open_source.uniqueMDiffOn p.proj hp)
  right_inv' := by
    intro p hp
    have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
    have hcomp := tangentMapWithin_comp_at
      (I := J) (I' := I) (I'' := J)
      (f := (Φ.symm : N → M)) (g := (Φ : M → N))
      (s := Φ.target) (u := Φ.source) p
      (Φ.mdifferentiableOn hn0 _ (Φ.map_target' hp))
      (Φ.symm.mdifferentiableOn hn0 _ hp)
      (fun _ hx => Φ.map_target' hx)
      (Φ.open_target.uniqueMDiffOn p.proj hp)
    calc
      tangentMapWithin I J (Φ : M → N) Φ.source
          (tangentMapWithin J I (Φ.symm : N → M) Φ.target p) =
          tangentMapWithin J J
            ((Φ : M → N) ∘ (Φ.symm : N → M)) Φ.target p := hcomp.symm
      _ = tangentMapWithin J J (id : N → N) Φ.target p :=
        tangentMapWithin_congr (fun x hx => Φ.right_inv' hx) p hp
      _ = p := tangentMapWithin_id
        (Φ.open_target.uniqueMDiffOn p.proj hp)
  open_source := Φ.open_source.preimage
    (FiberBundle.continuous_proj E (TangentSpace I))
  open_target := Φ.open_target.preimage
    (FiberBundle.continuous_proj E' (TangentSpace J))
  continuousOn_toFun :=
    Φ.contMDiffOn_toFun.continuousOn_tangentMapWithin hn
      Φ.open_source.uniqueMDiffOn
  continuousOn_invFun :=
    Φ.contMDiffOn_invFun.continuousOn_tangentMapWithin hn
      Φ.open_target.uniqueMDiffOn

end PartialDiffeomorph
end DifferentialGeometry
