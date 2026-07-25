import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.InductiveSuccessor
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.PolymorphicRegularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedFChartEffRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStepScaffold
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStep
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private def dirsOf (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (m : ℕ) :
    Fin m → Fin (Module.finrank ℝ E) :=
  fun i => dirs_seq i.val

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma dirsOf_zero (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) :
    dirsOf dirs_seq 0 = Fin.elim0 := by
  funext i; exact i.elim0

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma dirsOf_succ (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (m : ℕ) :
    dirsOf dirs_seq (m + 1) = Fin.snoc (dirsOf dirs_seq m) (dirs_seq m) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hlast
  · subst hj
    rw [Fin.snoc_castSucc]
    rfl
  · subst hlast
    rw [Fin.snoc_last]
    rfl

structure CanonicalIteratedDataBundle
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (m : ℕ) where

  data : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m

  directions_eq : data.directions = dirsOf dirs_seq m

  fChartEff_memW1p :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 data.diffChartForcing
      (chartTargetEuclid (I := I) (M := M) α)

  fChartEff_ae_zero_off_K :
    data.diffChartForcing =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ))

namespace CanonicalIteratedDataBundle

def ofBase
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))) :
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq 0 where
  data := IteratedDiffChartBilinearData.ofBase
    (I := I) (M := M) g α hu_h
  directions_eq := by
    funext i; exact i.elim0
  fChartEff_memW1p := h_base_f_chart_memW1p
  fChartEff_ae_zero_off_K := h_base_f_chart_ae_zero

def step
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g}
    {dirs_seq : ℕ → Fin (Module.finrank ℝ E)} {m : ℕ}
    (B_m : CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq m)
    (h_chart_H_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_next_fChartEff_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
          B_m.data.diffChartForcing (dirs_seq m))
        (chartTargetEuclid (I := I) (M := M) α)) :
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq (m + 1) where
  data := iteratedDiffChartBilinearData_step (I := I) (M := M) g α
    (u_h := u_h) m B_m.data (dirs_seq m)
    h_chart_H_m_plus_1 h_chart_H_m_plus_2
    B_m.fChartEff_memW1p B_m.fChartEff_ae_zero_off_K
  directions_eq := by
    change Fin.snoc B_m.data.directions (dirs_seq m) = dirsOf dirs_seq (m + 1)
    rw [B_m.directions_eq, dirsOf_succ]
  fChartEff_memW1p := h_next_fChartEff_memW1p
  fChartEff_ae_zero_off_K := by
    change fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
        B_m.data.diffChartForcing (dirs_seq m) =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))
    have h_diff_open : IsOpen
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
        (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    refine (ae_restrict_iff' h_diff_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    unfold fChartEffStep
    exact Set.indicator_of_notMem hy.2 _

end CanonicalIteratedDataBundle

def ChartHRegHyp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (M_max : ℕ) : Prop :=
  ∀ k ≤ M_max,
    MemWkp (d := Module.finrank ℝ E) k 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)

def FChartEffStepW1pHyp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (M_max : ℕ) : Prop :=
  ∀ m < M_max,
    ∀ (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m),
    D_m.directions = dirsOf dirs_seq m →
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D_m.diffChartForcing
      (chartTargetEuclid (I := I) (M := M) α) →
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
        D_m.diffChartForcing (dirs_seq m))
      (chartTargetEuclid (I := I) (M := M) α)

def canonicalBundle
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (m : ℕ)
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m) :
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq m := by
  induction m with
  | zero =>
      exact CanonicalIteratedDataBundle.ofBase (I := I) (M := M) g α
        dirs_seq hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero
  | succ m ih =>
      have h_chart_H_seq_m : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2) := by
        intro k hk
        exact h_chart_H_seq k (hk.trans (by omega))
      have h_step_propagator_m : FChartEffStepW1pHyp
          (I := I) (M := M) g α u_h dirs_seq m := by
        intro k hk D_k h_dirs h_W1p
        exact h_step_propagator k (hk.trans (Nat.lt_succ_self _)) D_k h_dirs h_W1p
      let B_m := ih h_chart_H_seq_m h_step_propagator_m
      have h_chart_H_m_plus_1 := h_chart_H_seq (m + 1) (by omega)
      have h_chart_H_m_plus_2 := h_chart_H_seq (m + 2) (by omega)
      have h_next_W1p := h_step_propagator m (Nat.lt_succ_self _) B_m.data
        B_m.directions_eq B_m.fChartEff_memW1p
      exact CanonicalIteratedDataBundle.step (I := I) (M := M)
        (g := g) (α := α) (u_h := u_h) (dirs_seq := dirs_seq) (m := m)
        B_m h_chart_H_m_plus_1 h_chart_H_m_plus_2 h_next_W1p

def iteratedDiffChartBilinearData_canonical
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (m : ℕ)
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m :=
  (canonicalBundle (I := I) (M := M) g α dirs_seq hu_h h_base_f_chart_memW1p
    h_base_f_chart_ae_zero m h_chart_H_seq h_step_propagator).data

theorem fChartEff_at_level_ae_zero_off_K_alpha
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (m : ℕ)
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m) :
    (iteratedDiffChartBilinearData_canonical (I := I) (M := M) g α
        dirs_seq hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero m
        h_chart_H_seq h_step_propagator).diffChartForcing =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) :=
  (canonicalBundle (I := I) (M := M) g α dirs_seq hu_h h_base_f_chart_memW1p
    h_base_f_chart_ae_zero m h_chart_H_seq h_step_propagator).fChartEff_ae_zero_off_K

def FChartEffStepMemWkpHyp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (M_max K : ℕ) : Prop :=
  ∀ (m : ℕ), m < M_max →
    ∀ (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m),
    D_m.directions = dirsOf dirs_seq m →
    MemWkp (d := Module.finrank ℝ E) ((K + (M_max - 1 - m)) + 1) 2
      D_m.diffChartForcing (chartTargetEuclid (I := I) (M := M) α) →
    MemWkp (d := Module.finrank ℝ E) (K + (M_max - 1 - m)) 2
      (fChartEffStep (I := I) (M := M) g α u_h m D_m.directions
        D_m.diffChartForcing (dirs_seq m))
      (chartTargetEuclid (I := I) (M := M) α)

private structure CanonicalBundleWithMemWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E)) (M_max K m : ℕ) extends
    CanonicalIteratedDataBundle (I := I) (M := M) g α u_h dirs_seq m where

  fChartEff_memWkp :
    MemWkp (d := Module.finrank ℝ E) (K + (M_max - m)) 2 data.diffChartForcing
      (chartTargetEuclid (I := I) (M := M) α)

namespace CanonicalBundleWithMemWkp

private def ofBase
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (M_max K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + M_max) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq M_max K 0 :=
  { toCanonicalIteratedDataBundle :=
      CanonicalIteratedDataBundle.ofBase (I := I) (M := M) g α dirs_seq hu_h
        h_base_f_chart_memW1p h_base_f_chart_ae_zero
    fChartEff_memWkp := by
      change MemWkp (d := Module.finrank ℝ E) (K + (M_max - 0)) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)
      have h_eq : M_max - 0 = M_max := Nat.sub_zero _
      rw [h_eq]
      exact h_base_f_chart_memWkp }

private def step
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g}
    {dirs_seq : ℕ → Fin (Module.finrank ℝ E)}
    {M_max K m : ℕ}
    (_hm : m + 1 ≤ M_max)
    (B_m : CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq
      M_max K m)
    (h_chart_H_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_step_W1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
          B_m.data.diffChartForcing (dirs_seq m))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_step_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + (M_max - (m + 1))) 2
        (fChartEffStep (I := I) (M := M) g α u_h m B_m.data.directions
          B_m.data.diffChartForcing (dirs_seq m))
        (chartTargetEuclid (I := I) (M := M) α)) :
    CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq
      M_max K (m + 1) :=
  { toCanonicalIteratedDataBundle :=
      CanonicalIteratedDataBundle.step (I := I) (M := M)
        (g := g) (α := α) (u_h := u_h) (dirs_seq := dirs_seq) (m := m)
        B_m.toCanonicalIteratedDataBundle h_chart_H_m_plus_1 h_chart_H_m_plus_2
        h_step_W1p
    fChartEff_memWkp := h_step_memWkp }

end CanonicalBundleWithMemWkp

private def canonicalBundleWithMemWkp_aux
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (M_max K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + M_max) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (M_max + 2))
    (h_step_W1p : FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq M_max)
    (h_step_memWkp :
      FChartEffStepMemWkpHyp (I := I) (M := M) g α u_h dirs_seq M_max K)
    (m : ℕ) (hm : m ≤ M_max) :
    CanonicalBundleWithMemWkp (I := I) (M := M) g α u_h dirs_seq
      M_max K m := by
  induction m with
  | zero =>
      exact CanonicalBundleWithMemWkp.ofBase (I := I) (M := M) g α dirs_seq
        M_max K hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero
        h_base_f_chart_memWkp
  | succ m ih =>
      have hm_le : m ≤ M_max := (Nat.le_succ _).trans hm
      let B_m := ih hm_le
      have h_chart_H_m_plus_1 := h_chart_H_seq (m + 1) (by omega)
      have h_chart_H_m_plus_2 := h_chart_H_seq (m + 2) (by omega)
      have h_step_w1p_m :=
        h_step_W1p m hm B_m.data B_m.directions_eq B_m.fChartEff_memW1p
      have h_idx_eq : M_max - 1 - m = M_max - (m + 1) := by omega
      have h_idx_eq_2 : K + (M_max - m) = (K + (M_max - 1 - m)) + 1 := by
        omega
      have h_Bm_memWkp := B_m.fChartEff_memWkp
      have h_Bm_memWkp' :
          MemWkp (d := Module.finrank ℝ E) ((K + (M_max - 1 - m)) + 1) 2
            B_m.data.diffChartForcing
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [← h_idx_eq_2]; exact h_Bm_memWkp
      have h_step_memWkp_m :=
        h_step_memWkp m hm B_m.data B_m.directions_eq h_Bm_memWkp'
      rw [h_idx_eq] at h_step_memWkp_m
      exact CanonicalBundleWithMemWkp.step (I := I) (M := M)
        (g := g) (α := α) (u_h := u_h) (dirs_seq := dirs_seq)
        (M_max := M_max) (K := K) (m := m) hm B_m
        h_chart_H_m_plus_1 h_chart_H_m_plus_2 h_step_w1p_m h_step_memWkp_m

def iteratedDiffChartBilinearData_canonicalMemWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (m K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + m) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m)
    (h_step_memWkp :
      FChartEffStepMemWkpHyp (I := I) (M := M) g α u_h dirs_seq m K) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m :=
  (canonicalBundleWithMemWkp_aux (I := I) (M := M) g α dirs_seq m K
    hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero h_base_f_chart_memWkp
    h_chart_H_seq h_step_propagator h_step_memWkp m (le_refl _)).data

theorem fChartEff_at_level_memWkp_K
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (dirs_seq : ℕ → Fin (Module.finrank ℝ E))
    (m K : ℕ)
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_base_f_chart_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_base_f_chart_ae_zero :
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_base_f_chart_memWkp :
      MemWkp (d := Module.finrank ℝ E) (K + m) 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_seq : ChartHRegHyp (I := I) (M := M) g α u_h (m + 2))
    (h_step_propagator :
      FChartEffStepW1pHyp (I := I) (M := M) g α u_h dirs_seq m)
    (h_step_memWkp :
      FChartEffStepMemWkpHyp (I := I) (M := M) g α u_h dirs_seq m K) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (iteratedDiffChartBilinearData_canonicalMemWkp (I := I) (M := M) g α
        dirs_seq m K hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero
        h_base_f_chart_memWkp h_chart_H_seq h_step_propagator
        h_step_memWkp).diffChartForcing
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_mem := (canonicalBundleWithMemWkp_aux (I := I) (M := M) g α dirs_seq
    m K hu_h h_base_f_chart_memW1p h_base_f_chart_ae_zero h_base_f_chart_memWkp
    h_chart_H_seq h_step_propagator h_step_memWkp m (le_refl _)).fChartEff_memWkp
  have h_idx_eq : K + (m - m) = K := by
    rw [Nat.sub_self, Nat.add_zero]
  rw [h_idx_eq] at h_mem
  exact h_mem

end IteratedFChartEffRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
