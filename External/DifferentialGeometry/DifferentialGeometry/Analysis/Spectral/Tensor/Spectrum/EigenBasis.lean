import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.Defs
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def TensorNonzeroResolventEigenvalue
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  { μ : ℝ //
    tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧ μ ≠ 0 }

namespace TensorNonzeroResolventEigenvalue

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

def val (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) : ℝ :=
  μ.1

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma eigenspace_ne_bot
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≠ ⊥ :=
  μ.2.1

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma val_ne_zero
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    μ.val ≠ 0 := μ.2.2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma hasEigenvalue
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    Module.End.HasEigenvalue
      ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ.val := by
  have h : tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≠ ⊥ :=
    μ.eigenspace_ne_bot
  unfold tensorResolventEigenspace at h
  exact h

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[ext] lemma ext
    (μ ν : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s)
    (h : μ.val = ν.val) : μ = ν := Subtype.ext h

end TensorNonzeroResolventEigenvalue

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    { μ : ℝ |
      tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧ μ ≠ 0 } =
      ⋃ n : ℕ, { μ : ℝ |
        Module.End.HasEigenvalue
          ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ ∧
        (1 : ℝ) / (n + 1) ≤ |μ| } := by
  ext μ
  constructor
  · rintro ⟨hμ_eig_ne, hμ_ne⟩
    have hμ_has : Module.End.HasEigenvalue
        ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ := by
      unfold tensorResolventEigenspace at hμ_eig_ne
      exact hμ_eig_ne
    have h_abs_pos : 0 < |μ| := abs_pos.mpr hμ_ne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h_abs_pos
    refine Set.mem_iUnion.mpr ⟨n, hμ_has, ?_⟩
    exact le_of_lt hn
  · rintro hμ_in_union
    obtain ⟨n, hμ_in_n⟩ := Set.mem_iUnion.mp hμ_in_union
    obtain ⟨hμ_eig, hμ_size⟩ := hμ_in_n
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have h_abs_pos : 0 < |μ| := lt_of_lt_of_le h_pos hμ_size
    have hμ_ne : μ ≠ 0 := abs_pos.mp h_abs_pos
    have hμ_eig_ne : tensorResolventEigenspace
        (I := I) (M := M) g r s μ ≠ ⊥ := by
      unfold tensorResolventEigenspace
      exact hμ_eig
    exact ⟨hμ_eig_ne, hμ_ne⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nonzero_tensor_resolvent_eigenvalues_set_countable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Set.Countable
      { μ : ℝ |
        tensorResolventEigenspace (I := I) (M := M) g r s μ ≠ ⊥ ∧
          μ ≠ 0 } := by
  rw [nonzero_tensor_resolvent_eigenvalues_set_eq_iUnion]
  apply Set.countable_iUnion
  intro n
  have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
  exact (tensorResolvent_eigenvalues_finite_above
    (I := I) (M := M) g r s h_compact h_pos).countable

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem TensorNonzeroResolventEigenvalue.countable_ofCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Countable (TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) := by
  unfold TensorNonzeroResolventEigenvalue
  exact (nonzero_tensor_resolvent_eigenvalues_set_countable
    (I := I) (M := M) g r s h_compact).to_subtype

@[reducible]
def TensorNonzeroResolventEigenvalue.finiteDimensional_ofCompact
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
  tensorResolventEigenspace_finiteDim
    (I := I) (M := M) g r s h_compact μ.val_ne_zero

noncomputable def tensorResolventEigenspaceONB
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ
        (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)))
      ℝ (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
  letI : FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
    μ.finiteDimensional_ofCompact h_compact
  stdOrthonormalBasis ℝ
    (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenspace_orthogonalFamily_nonzero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    OrthogonalFamily ℝ
      (fun μ : TensorNonzeroResolventEigenvalue
          (I := I) (M := M) g r s =>
        ↥(tensorResolventEigenspace (I := I) (M := M) g r s μ.val))
      (fun μ =>
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtypeₗᵢ) := by
  have hSymm :
      ((tensorResolventL2
        (I := I) (M := M) g r s).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s)
  have h_full : OrthogonalFamily ℝ
      (fun μ : ℝ =>
        ↥(tensorResolventEigenspace (I := I) (M := M) g r s μ))
      (fun μ =>
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ).subtypeₗᵢ) :=
    hSymm.orthogonalFamily_eigenspaces
  have h_inj : Function.Injective
      (fun μ : TensorNonzeroResolventEigenvalue
          (I := I) (M := M) g r s => μ.val) :=
    fun μ ν h => Subtype.ext h
  exact h_full.comp h_inj

noncomputable def tensorResolventEigenbasisVec
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
            (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    TensorL2 r s g :=
  ((tensorResolventEigenspaceONB
        (I := I) (M := M) h_compact i.1 i.2 :
      tensorResolventEigenspace (I := I) (M := M) g r s i.1.val) :
    TensorL2 r s g)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenbasisVec_mem
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
            (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventEigenbasisVec (I := I) (M := M) h_compact i ∈
      tensorResolventEigenspace (I := I) (M := M) g r s i.1.val := by
  unfold tensorResolventEigenbasisVec
  exact (tensorResolventEigenspaceONB
    (I := I) (M := M) h_compact i.1 i.2).property

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenbasisVec_orthonormal
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Orthonormal ℝ
      (tensorResolventEigenbasisVec (I := I) (M := M) (g := g)
        (r := r) (s := s) h_compact) := by
  have h_fam :=
    tensorResolventEigenspace_orthogonalFamily_nonzero
      (I := I) (M := M) g r s
  have h_each : ∀ μ : TensorNonzeroResolventEigenvalue
        (I := I) (M := M) g r s,
      Orthonormal ℝ
        (tensorResolventEigenspaceONB
          (I := I) (M := M) h_compact μ) :=
    fun μ =>
      (tensorResolventEigenspaceONB
        (I := I) (M := M) h_compact μ).orthonormal
  have h_sig := h_fam.orthonormal_sigma_orthonormal h_each
  convert h_sig using 1

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma span_tensorResolventEigenbasisVec_le_iSup_eigenspace
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)) ≤
      ⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine SetLike.mem_coe.mpr ?_
  refine Submodule.mem_iSup_of_mem i.1 ?_
  exact tensorResolventEigenbasisVec_mem
    (I := I) (M := M) h_compact i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :
    tensorResolventEigenspace (I := I) (M := M) g r s μ.val ≤
      Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)) := by
  intro x hx
  letI : FiniteDimensional ℝ
      (tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :=
    μ.finiteDimensional_ofCompact h_compact
  set b := tensorResolventEigenspaceONB
    (I := I) (M := M) h_compact μ
  have h_basis_span : Submodule.span ℝ
      (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) = ⊤ :=
    b.toBasis.span_eq
  have h_subtype_apply :
      ((tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtype '' Set.range b) =
      Set.range (fun k =>
        ((b k : tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
          TensorL2 r s g)) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨k, hk⟩, hzy⟩
      exact ⟨k, by rw [← hzy, ← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨b k, ⟨k, rfl⟩, hk⟩
  have h_in_basis_set : ∀ k : Fin (Module.finrank ℝ
        (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)),
      ((b k :
          tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
            TensorL2 r s g) ∈
      Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact) := by
    intro k
    refine ⟨⟨μ, k⟩, ?_⟩
    rfl
  have h_subtype_subset : Set.range (fun k =>
      ((b k :
          tensorResolventEigenspace (I := I) (M := M) g r s μ.val) :
            TensorL2 r s g)) ⊆
      Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact) := by
    rintro y ⟨k, rfl⟩
    exact h_in_basis_set k
  have hx_subtype : x =
      (tensorResolventEigenspace
        (I := I) (M := M) g r s μ.val).subtype ⟨x, hx⟩ := rfl
  have h_top_mem :
      (⟨x, hx⟩ :
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val) ∈
      Submodule.span ℝ (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)) := by
    rw [h_basis_span]; trivial
  have h_after_map : x ∈ Submodule.map
        (tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val).subtype
        (Submodule.span ℝ (Set.range (b.toBasis :
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val)) →
          tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val))) := by
    refine ⟨⟨x, hx⟩, h_top_mem, rfl⟩
  rw [Submodule.map_span] at h_after_map
  have h_eq_basis : ((b.toBasis :
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val)) →
        tensorResolventEigenspace
          (I := I) (M := M) g r s μ.val)) = (b : _ → _) := by
    funext k
    have := OrthonormalBasis.coe_toBasis b
    exact congr_fun this k
  rw [h_eq_basis] at h_after_map
  rw [h_subtype_apply] at h_after_map
  exact Submodule.span_mono h_subtype_subset h_after_map

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem span_tensorResolventEigenbasisVec_eq_iSup_eigenspace
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)) =
      ⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val := by
  refine le_antisymm
    (span_tensorResolventEigenbasisVec_le_iSup_eigenspace
      (I := I) (M := M) h_compact) ?_
  exact iSup_le
    (tensorResolventEigenspace_le_span_tensorResolventEigenbasisVec
      (I := I) (M := M) h_compact)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    (⨆ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val)ᗮ = ⊥ := by
  suffices h_iSup_eq :
      (⨆ μ : TensorNonzeroResolventEigenvalue
                (I := I) (M := M) g r s,
        tensorResolventEigenspace (I := I) (M := M) g r s μ.val) =
      (⨆ μ : ℝ, tensorResolventEigenspace
                  (I := I) (M := M) g r s μ) by
    rw [h_iSup_eq]
    exact tensorResolventEigenspaces_iSup_orthogonal_eq_bot
      (I := I) (M := M) g r s h_compact
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun μ => ?_)
    exact le_iSup
      (fun ν : ℝ =>
        tensorResolventEigenspace (I := I) (M := M) g r s ν) μ.val
  · refine iSup_le (fun ν => ?_)
    by_cases hν : ν = 0
    · rw [hν,
          tensorResolventEigenspace_zero_eq_bot
            (I := I) (M := M) g r s]
      exact bot_le
    · by_cases h_eig_bot :
          tensorResolventEigenspace (I := I) (M := M) g r s ν = ⊥
      · rw [h_eig_bot]; exact bot_le
      · let hν_in_subtype :
            TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s :=
          ⟨ν, h_eig_bot, hν⟩
        have hval : hν_in_subtype.val = ν := rfl
        calc tensorResolventEigenspace
              (I := I) (M := M) g r s ν
            = tensorResolventEigenspace
                (I := I) (M := M) g r s hν_in_subtype.val := by rw [hval]
          _ ≤ ⨆ μ : TensorNonzeroResolventEigenvalue
                      (I := I) (M := M) g r s,
                  tensorResolventEigenspace
                    (I := I) (M := M) g r s μ.val :=
              le_iSup
                (fun μ : TensorNonzeroResolventEigenvalue
                          (I := I) (M := M) g r s =>
                  tensorResolventEigenspace
                    (I := I) (M := M) g r s μ.val) hν_in_subtype

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventEigenbasisVec_span_orthogonal_eq_bot
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    (Submodule.span ℝ (Set.range
        (tensorResolventEigenbasisVec
          (I := I) (M := M) (g := g) (r := r) (s := s) h_compact)))ᗮ =
      ⊥ := by
  rw [span_tensorResolventEigenbasisVec_eq_iSup_eigenspace]
  exact nonzero_iSup_tensorResolventEigenspace_orthogonal_eq_bot
    (I := I) (M := M) h_compact

noncomputable def tensorResolventHilbertEigenbasisSigma
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    HilbertBasis
      (Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
        Fin (Module.finrank ℝ
          (tensorResolventEigenspace
            (I := I) (M := M) g r s μ.val)))
      ℝ (TensorL2 r s g) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (tensorResolventEigenbasisVec_orthonormal
      (I := I) (M := M) h_compact)
    (tensorResolventEigenbasisVec_span_orthogonal_eq_bot
      (I := I) (M := M) h_compact)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorResolventHilbertEigenbasisSigma_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_compact i =
      tensorResolventEigenbasisVec
        (I := I) (M := M) h_compact i := by
  unfold tensorResolventHilbertEigenbasisSigma
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (tensorResolventEigenbasisVec_orthonormal
        (I := I) (M := M) h_compact)
      (tensorResolventEigenbasisVec_span_orthogonal_eq_bot
        (I := I) (M := M) h_compact))
    i

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolventHilbertEigenbasisSigma_ofCompact_isEigenvector
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (i : Σ μ : TensorNonzeroResolventEigenvalue
              (I := I) (M := M) g r s,
          Fin (Module.finrank ℝ
            (tensorResolventEigenspace
              (I := I) (M := M) g r s μ.val))) :
    tensorResolventL2 (I := I) (M := M) g r s
        (tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact i) =
      i.1.val •
        tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact i := by
  rw [tensorResolventHilbertEigenbasisSigma_apply
    (I := I) (M := M) h_compact i]
  have h_mem := tensorResolventEigenbasisVec_mem
    (I := I) (M := M) h_compact i
  exact (mem_tensorResolventEigenspace_iff
    (I := I) (M := M) g r s i.1.val _).mp h_mem

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
