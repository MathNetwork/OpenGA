import DifferentialGeometry.Geometry.Flow.RicciFlow.MaximumPrinciple.TensorWeak.BarrierCore
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false










namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]



def Tensor02RealizesRawAt
    (A : RawTwoTensorField (I := I) (M := M)) (x : M)
    (T : Tensor02At (I := I) (M := M) x) : Prop :=
  ∀ v w : TangentSpace I x, T (vec2 (I := I) v w) = A x v w


def rawRightLM
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x)
    (v : TangentSpace I x) :
    TangentSpace I x →ₗ[Real] Real where
  toFun := fun w => A x v w
  map_add' := by
    intro y z
    exact hA.add_right v y z
  map_smul' := by
    intro c y
    simpa [smul_eq_mul] using hA.smul_right c v y



def rawRightCLM
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x)
    (v : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  ⟨rawRightLM (I := I) (M := M) A hA v,
    LinearMap.continuous_of_finiteDimensional _⟩


def rawRightTensor1
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x)
    (v : TangentSpace I x) :
    ContinuousMultilinearMap Real (fun _ : Fin 1 => TangentSpace I x) Real :=
  (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
    (rawRightCLM (I := I) (M := M) A hA v)

omit [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] in
@[simp]
theorem rawRightTensor1_apply
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x)
    (v : TangentSpace I x) (m : Fin 1 -> TangentSpace I x) :
    rawRightTensor1 (I := I) (M := M) A hA v m = A x v (m 0) := by
  simp [rawRightTensor1, rawRightCLM, rawRightLM,
    continuousMultilinearCurryFin1_symm_apply]


def rawCurriedLM
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x) :
    TangentSpace I x →ₗ[Real]
      ContinuousMultilinearMap Real (fun _ : Fin 1 => TangentSpace I x) Real where
  toFun := fun v => rawRightTensor1 (I := I) (M := M) A hA v
  map_add' := by
    intro v w
    apply ContinuousMultilinearMap.ext
    intro m
    simp [hA.add_left v w (m 0)]
  map_smul' := by
    intro c v
    apply ContinuousMultilinearMap.ext
    intro m
    simp [hA.smul_left c v (m 0), smul_eq_mul]


def rawCurriedCLM
    (A : RawTwoTensorField (I := I) (M := M)) {x : M}
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x) :
    TangentSpace I x →L[Real]
      ContinuousMultilinearMap Real (fun _ : Fin 1 => TangentSpace I x) Real :=
  ⟨rawCurriedLM (I := I) (M := M) A hA,
    LinearMap.continuous_of_finiteDimensional _⟩



def tensor02OfRawAt
    (A : RawTwoTensorField (I := I) (M := M)) (x : M)
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x) :
    Tensor02At (I := I) (M := M) x :=
  (rawCurriedCLM (I := I) (M := M) A hA).uncurryLeft



omit [IsManifold I 1 M] [IsManifold I 2 M] in
theorem tensor02OfRawAt_realizes
    (A : RawTwoTensorField (I := I) (M := M)) (x : M)
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x) :
    Tensor02RealizesRawAt (I := I) (M := M) A x
      (tensor02OfRawAt (I := I) (M := M) A x hA) := by
  intro v w
  rfl


omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem tensor02_realizes_ext
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    {T U : Tensor02At (I := I) (M := M) x}
    (hT : Tensor02RealizesRawAt (I := I) (M := M) A x T)
    (hU : Tensor02RealizesRawAt (I := I) (M := M) A x U) :
    T = U := by
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = vec2 (I := I) (m 0) (m 1) := by
    funext i
    fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hm, hT, hU]


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem rawSym2_idem
    (A : RawTwoTensorField (I := I) (M := M)) :
    rawSym2 (I := I) (M := M) (rawSym2 (I := I) (M := M) A) =
      rawSym2 (I := I) (M := M) A := by
  funext x v w
  unfold rawSym2
  ring


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem rawSym2_eq_of_symm
    {A : RawTwoTensorField (I := I) (M := M)} {x : M}
    (hsym : TwoTensorSymmetricAt (I := I) (M := M) A x) :
    ∀ v w : TangentSpace I x,
      rawSym2 (I := I) (M := M) A x v w = A x v w := by
  intro v w
  unfold rawSym2
  rw [hsym w v]
  ring


abbrev Tensor02ReactionAt : Type _ :=
  Real -> SmoothRiemannianMetric I M -> (x : M) ->
    Tensor02At (I := I) (M := M) x -> Tensor02At (I := I) (M := M) x




def Tensor02ReactionAt.toRawSymm
    (N : Tensor02ReactionAt (I := I) (M := M)) :
    TwoTensorReaction (I := I) (M := M) :=
  by
  classical
  exact fun t g A x v w =>
    if hA : TwoTensorBilinearAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) A) x then
      N t g x (tensor02OfRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) A) x hA) (vec2 (I := I) v w)
    else
      0


omit [IsManifold I 1 M] [IsManifold I 2 M] in
theorem Tensor02ReactionAt.toRawSymm_eval_of_bilin
    (N : Tensor02ReactionAt (I := I) (M := M))
    (t : Real) (g : SmoothRiemannianMetric I M)
    (A : RawTwoTensorField (I := I) (M := M)) (x : M)
    (hA : TwoTensorBilinearAt (I := I) (M := M) A x)
    (v w : TangentSpace I x) :
    Tensor02ReactionAt.toRawSymm (I := I) (M := M) N t g A x v w =
      N t g x
        (tensor02OfRawAt (I := I) (M := M)
          (rawSym2 (I := I) (M := M) A) x
          (rawSym2_bilin (I := I) (M := M) hA))
        (vec2 (I := I) v w) := by
  unfold Tensor02ReactionAt.toRawSymm
  rw [dif_pos (rawSym2_bilin (I := I) (M := M) hA)]



omit [IsManifold I 1 M] [IsManifold I 2 M] in
theorem Tensor02ReactionAt.toRawSymm_symmInputOn
    (G : Real -> SmoothRiemannianMetric I M)
    (N : Tensor02ReactionAt (I := I) (M := M)) (U : Set Real) :
    TensorReactionSymmInputOn (I := I) (M := M) G
      (Tensor02ReactionAt.toRawSymm (I := I) (M := M) N) U := by
  intro t ht A x v
  unfold Tensor02ReactionAt.toRawSymm
  rw [rawSym2_idem (I := I) (M := M) A]


def TensorReactionOutputBilinearOn
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M)) (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ A : RawTwoTensorField (I := I) (M := M), ∀ x,
    TwoTensorBilinearAt (I := I) (M := M) (N t (G t) A) x


omit [IsManifold I 1 M] [IsManifold I 2 M] in
theorem Tensor02ReactionAt.toRawSymm_output_bilin
    (G : Real -> SmoothRiemannianMetric I M)
    (N : Tensor02ReactionAt (I := I) (M := M)) (U : Set Real) :
    TensorReactionOutputBilinearOn (I := I) (M := M) G
      (Tensor02ReactionAt.toRawSymm (I := I) (M := M) N) U := by
  intro t ht A x
  by_cases hA : TwoTensorBilinearAt (I := I) (M := M)
      (rawSym2 (I := I) (M := M) A) x
  · let T : Tensor02At (I := I) (M := M) x :=
      N t (G t) x (tensor02OfRawAt (I := I) (M := M)
        (rawSym2 (I := I) (M := M) A) x hA)
    constructor
    · intro X Y Z
      dsimp [Tensor02ReactionAt.toRawSymm]
      rw [dif_pos hA, dif_pos hA, dif_pos hA]
      change T (vec2 (I := I) (X + Y) Z) =
        T (vec2 (I := I) X Z) + T (vec2 (I := I) Y Z)
      let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
      have hmap := T.map_update_add m 0 X Y
      have hleft :
          Function.update m (0 : Fin 2) (X + Y) = vec2 (I := I) (X + Y) Z := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      have hX : Function.update m (0 : Fin 2) X = vec2 (I := I) X Z := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      have hY : Function.update m (0 : Fin 2) Y = vec2 (I := I) Y Z := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      simpa [hleft, hX, hY] using hmap
    · intro c X Z
      dsimp [Tensor02ReactionAt.toRawSymm]
      rw [dif_pos hA, dif_pos hA]
      change T (vec2 (I := I) (c • X) Z) =
        c * T (vec2 (I := I) X Z)
      let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
      have hmap := T.map_update_smul m 0 c X
      have hleft :
          Function.update m (0 : Fin 2) (c • X) = vec2 (I := I) (c • X) Z := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      have hX : Function.update m (0 : Fin 2) X = vec2 (I := I) X Z := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      simpa [hleft, hX, smul_eq_mul] using hmap
    · intro X Y Z
      dsimp [Tensor02ReactionAt.toRawSymm]
      rw [dif_pos hA, dif_pos hA, dif_pos hA]
      change T (vec2 (I := I) X (Y + Z)) =
        T (vec2 (I := I) X Y) + T (vec2 (I := I) X Z)
      let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Y
      have hmap := T.map_update_add m 1 Y Z
      have hleft :
          Function.update m (1 : Fin 2) (Y + Z) = vec2 (I := I) X (Y + Z) := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      have hY : Function.update m (1 : Fin 2) Y = vec2 (I := I) X Y := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      have hZ : Function.update m (1 : Fin 2) Z = vec2 (I := I) X Z := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      simpa [hleft, hY, hZ] using hmap
    · intro c X Z
      dsimp [Tensor02ReactionAt.toRawSymm]
      rw [dif_pos hA, dif_pos hA]
      change T (vec2 (I := I) X (c • Z)) =
        c * T (vec2 (I := I) X Z)
      let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
      have hmap := T.map_update_smul m 1 c Z
      have hleft :
          Function.update m (1 : Fin 2) (c • Z) = vec2 (I := I) X (c • Z) := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      have hZ : Function.update m (1 : Fin 2) Z = vec2 (I := I) X Z := by
        funext i
        fin_cases i <;> simp [m, vec2, DifferentialGeometry.Integral.Connection.vec2, Function.update]
      simpa [hleft, hZ, smul_eq_mul] using hmap
  · constructor <;> simp [Tensor02ReactionAt.toRawSymm, hA]

end
end DifferentialGeometry.Integral.Connection
