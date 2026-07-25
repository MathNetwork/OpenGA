import DifferentialGeometry.Geometry.Metric.TensorInner.CoerciveBilinInverse
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false











noncomputable section

namespace MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]



def koszulCov
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (v w : E) :
    E →L[Real] Real :=
  (1 / 2 : Real) • ((D v) w + (D w) v - (D.flip v).flip w)


@[simp] theorem koszulCov_apply
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (u v w : E) :
    koszulCov D v w u =
      (1 / 2 : Real) * (D v w u + D w v u - D u v w) := by
  simp [koszulCov]


theorem koszulCov_sub
    (D F : E →L[Real] E →L[Real] E →L[Real] Real) (v w : E) :
    koszulCov (D - F) v w = koszulCov D v w - koszulCov F v w := by
  ext u
  simp only [koszulCov_apply, ContinuousLinearMap.sub_apply]
  ring



theorem koszulCov_diag_sub
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (v w : E) :
    koszulCov D v v - koszulCov D w w =
      koszulCov D (v - w) v + koszulCov D w (v - w) := by
  ext u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    koszulCov_apply, map_sub]
  ring



theorem koszulCov_norm_le
    (D : E →L[Real] E →L[Real] E →L[Real] Real)
    {C : Real} (hC : 0 ≤ C)
    (hD : ∀ u v w : E, ‖D u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖)
    (v w : E) :
    ‖koszulCov D v w‖ ≤ (3 / 2 : Real) * C * ‖v‖ * ‖w‖ := by
  let K : Real := C * ‖v‖ * ‖w‖
  have hK : 0 ≤ K := by positivity
  have hfirst : ‖(D v) w‖ ≤ K := by
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun u ↦ ?_
    simpa only [K] using hD v w u
  have hsecond : ‖(D w) v‖ ≤ K := by
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun u ↦ ?_
    calc
      ‖D w v u‖ ≤ C * ‖w‖ * ‖v‖ * ‖u‖ := hD w v u
      _ = K * ‖u‖ := by simp only [K]; ring
  have hthird : ‖(D.flip v).flip w‖ ≤ K := by
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun u ↦ ?_
    simp only [ContinuousLinearMap.flip_apply]
    calc
      ‖D u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖ := hD u v w
      _ = K * ‖u‖ := by simp only [K]; ring
  have hsum :
      ‖(D v) w + (D w) v - (D.flip v).flip w‖ ≤ 3 * K := by
    calc
      ‖(D v) w + (D w) v - (D.flip v).flip w‖
          ≤ ‖(D v) w + (D w) v‖ + ‖(D.flip v).flip w‖ := norm_sub_le _ _
      _ ≤ (‖(D v) w‖ + ‖(D w) v‖) + ‖(D.flip v).flip w‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (K + K) + K := add_le_add (add_le_add hfirst hsecond) hthird
      _ = 3 * K := by ring
  unfold koszulCov
  calc
    ‖(1 / 2 : Real) • ((D v) w + (D w) v - (D.flip v).flip w)‖ =
        (1 / 2 : Real) * ‖(D v) w + (D w) v - (D.flip v).flip w‖ := by
          rw [norm_smul]
          norm_num
    _ ≤ (1 / 2 : Real) * (3 * K) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (3 / 2 : Real) * C * ‖v‖ * ‖w‖ := by
      simp only [K]
      ring

section CovCLM

noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance dualNormedSpace :
    NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance bilinNormedGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance bilinNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance triNormedGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance triNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private theorem tri_norm_apply
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (u v w : E) :
    ‖D u v w‖ ≤ ‖D‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
  calc
    ‖D u v w‖ ≤ ‖D u‖ * ‖v‖ * ‖w‖ := (D u).le_opNorm₂ v w
    _ ≤ (‖D‖ * ‖u‖) * ‖v‖ * ‖w‖ := by
      gcongr
      exact D.le_opNorm u

private noncomputable def koszulCovBilin
    (D : E →L[Real] E →L[Real] E →L[Real] Real) :
    E →L[Real] E →L[Real] E →L[Real] Real :=
  let f : E →ₗ[Real] E →ₗ[Real] E →L[Real] Real :=
    LinearMap.mk₂ Real (fun v w => koszulCov D v w)
      (fun v₁ v₂ w => by
        ext u
        simp [koszulCov_apply]
        ring)
      (fun c v w => by
        ext u
        simp [koszulCov_apply]
        ring)
      (fun v w₁ w₂ => by
        ext u
        simp [koszulCov_apply]
        ring)
      (fun c v w => by
        ext u
        simp [koszulCov_apply]
        ring)
  f.mkContinuous₂ ((3 / 2 : Real) * ‖D‖) fun v w =>
    koszulCov_norm_le D (norm_nonneg D) (tri_norm_apply D) v w

@[simp] private theorem koszulCovBilin_apply
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (v w : E) :
    koszulCovBilin D v w = koszulCov D v w := by
  simp [koszulCovBilin]

private theorem koszulCovBilin_le
    (D : E →L[Real] E →L[Real] E →L[Real] Real) :
    ‖koszulCovBilin D‖ ≤ (3 / 2 : Real) * ‖D‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro v
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro w
  simpa only [koszulCovBilin_apply, mul_assoc] using
    koszulCov_norm_le D (norm_nonneg D) (tri_norm_apply D) v w



noncomputable def koszulCovCLM :
    (E →L[Real] E →L[Real] E →L[Real] Real) →L[Real]
      E →L[Real] E →L[Real] E →L[Real] Real :=
  let f : (E →L[Real] E →L[Real] E →L[Real] Real) →ₗ[Real]
      E →L[Real] E →L[Real] E →L[Real] Real :=
    { toFun := koszulCovBilin
      map_add' := fun D F => by
        ext v w u
        simp [koszulCov_apply]
        ring
      map_smul' := fun c D => by
        ext v w u
        simp [koszulCov_apply]
        ring }
  f.mkContinuous (3 / 2 : Real) koszulCovBilin_le


@[simp] theorem koszulCovCLM_apply
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (v w : E) :
    koszulCovCLM D v w = koszulCov D v w := by
  simp [koszulCovCLM]


theorem koszulCovCLM_norm_le : ‖koszulCovCLM (E := E)‖ ≤ (3 / 2 : Real) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  exact koszulCovBilin_le

end CovCLM




noncomputable def koszulVec
    [CompleteSpace E] [CoerciveBilinInverse E]
    {B : E →L[Real] E →L[Real] Real} (hco : IsCoercive B)
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (v w : E) : E :=
  hco.sharp (koszulCov D v w)


@[simp] theorem apply_koszulVec
    [CompleteSpace E] [CoerciveBilinInverse E]
    {B : E →L[Real] E →L[Real] Real} (hco : IsCoercive B)
    (D : E →L[Real] E →L[Real] E →L[Real] Real) (v w : E) :
    B (koszulVec hco D v w) = koszulCov D v w := by
  exact hco.apply_sharp _



theorem koszulVec_norm_le
    [CompleteSpace E] [CoerciveBilinInverse E]
    {B : E →L[Real] E →L[Real] Real} (hco : IsCoercive B)
    {c : Real} (hc : 0 < c)
    (hB : ∀ u : E, c * ‖u‖ * ‖u‖ ≤ B u u)
    (D : E →L[Real] E →L[Real] E →L[Real] Real)
    {C : Real} (hC : 0 ≤ C)
    (hD : ∀ u v w : E, ‖D u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖)
    (v w : E) :
    ‖koszulVec hco D v w‖ ≤
      c⁻¹ * ((3 / 2 : Real) * C * ‖v‖ * ‖w‖) := by
  calc
    ‖koszulVec hco D v w‖ ≤ c⁻¹ * ‖koszulCov D v w‖ :=
      hco.sharp_norm_le hc hB _
    _ ≤ c⁻¹ * ((3 / 2 : Real) * C * ‖v‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left (koszulCov_norm_le D hC hD v w) (inv_nonneg.mpr hc.le)


theorem koszulVec_diag_le
    [CompleteSpace E] [CoerciveBilinInverse E]
    {B : E →L[Real] E →L[Real] Real} (hco : IsCoercive B)
    {c : Real} (hc : 0 < c)
    (hB : ∀ u : E, c * ‖u‖ * ‖u‖ ≤ B u u)
    (D : E →L[Real] E →L[Real] E →L[Real] Real)
    {C : Real} (hC : 0 ≤ C)
    (hD : ∀ u v w : E, ‖D u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖)
    (v w : E) :
    ‖koszulVec hco D v v - koszulVec hco D w w‖ ≤
      c⁻¹ * ((3 / 2 : Real) * C * (‖v‖ + ‖w‖) * ‖v - w‖) := by
  have hsplit :
      koszulVec hco D v v - koszulVec hco D w w =
        koszulVec hco D (v - w) v + koszulVec hco D w (v - w) := by
    calc
      koszulVec hco D v v - koszulVec hco D w w =
          hco.sharp (koszulCov D v v - koszulCov D w w) :=
        (hco.sharp_sub _ _).symm
      _ = hco.sharp (koszulCov D (v - w) v + koszulCov D w (v - w)) :=
        congrArg hco.sharp (koszulCov_diag_sub D v w)
      _ = koszulVec hco D (v - w) v + koszulVec hco D w (v - w) := by
        simp only [koszulVec, IsCoercive.sharp, map_add]
  rw [hsplit]
  calc
    ‖koszulVec hco D (v - w) v + koszulVec hco D w (v - w)‖ ≤
        ‖koszulVec hco D (v - w) v‖ + ‖koszulVec hco D w (v - w)‖ :=
      norm_add_le _ _
    _ ≤ c⁻¹ * ((3 / 2 : Real) * C * ‖v - w‖ * ‖v‖) +
        c⁻¹ * ((3 / 2 : Real) * C * ‖w‖ * ‖v - w‖) :=
      add_le_add
        (koszulVec_norm_le hco hc hB D hC hD (v - w) v)
        (koszulVec_norm_le hco hc hB D hC hD w (v - w))
    _ = c⁻¹ * ((3 / 2 : Real) * C * (‖v‖ + ‖w‖) * ‖v - w‖) := by
      ring



theorem koszulVec_sub_le
    [CompleteSpace E] [CoerciveBilinInverse E]
    {B C : E →L[Real] E →L[Real] Real}
    (hBco : IsCoercive B) (hCco : IsCoercive C)
    {cB cC : Real} (hcB : 0 < cB) (hcC : 0 < cC)
    (hB : ∀ u : E, cB * ‖u‖ * ‖u‖ ≤ B u u)
    (hC : ∀ u : E, cC * ‖u‖ * ‖u‖ ≤ C u u)
    (D F : E →L[Real] E →L[Real] E →L[Real] Real)
    {Csub CF : Real} (hCsub : 0 ≤ Csub) (hCF : 0 ≤ CF)
    (hsub : ∀ u v w : E,
      ‖(D - F) u v w‖ ≤ Csub * ‖u‖ * ‖v‖ * ‖w‖)
    (hF : ∀ u v w : E, ‖F u v w‖ ≤ CF * ‖u‖ * ‖v‖ * ‖w‖)
    (v w : E) :
    ‖koszulVec hBco D v w - koszulVec hCco F v w‖ ≤
      cB⁻¹ * ((3 / 2 : Real) * Csub * ‖v‖ * ‖w‖) +
        cB⁻¹ * (‖C - B‖ *
          (cC⁻¹ * ((3 / 2 : Real) * CF * ‖v‖ * ‖w‖))) := by
  have hsplit :
      koszulVec hBco D v w - koszulVec hCco F v w =
        (hBco.sharp (koszulCov D v w) - hBco.sharp (koszulCov F v w)) +
          (hBco.sharp (koszulCov F v w) - hCco.sharp (koszulCov F v w)) := by
    simp only [koszulVec]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← hBco.sharp_sub, ← koszulCov_sub]
    exact hBco.sharp_norm_le hcB hB _ |>.trans
      (mul_le_mul_of_nonneg_left
        (koszulCov_norm_le (D - F) hCsub hsub v w)
        (inv_nonneg.mpr hcB.le))
  · exact (hBco.sharp_sub_le hCco hcB hcC hB hC (koszulCov F v w)).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (koszulCov_norm_le F hCF hF v w)
            (inv_nonneg.mpr hcC.le))
          (norm_nonneg (C - B)))
        (inv_nonneg.mpr hcB.le))

end MetricKoszul
