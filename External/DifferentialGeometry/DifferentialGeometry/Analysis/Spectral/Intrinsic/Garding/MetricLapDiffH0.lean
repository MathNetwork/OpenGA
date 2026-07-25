import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffTime
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic









noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private noncomputable def scalarL2ToH0
    (g : SmoothRiemannianMetric I M) :
    TensorL2 0 0 g →ₗᵢ[Real]
      tensorHs (I := I) (M := M) g 0 0 0 :=
  (tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) g 0 0)).symm.toLinearIsometry



noncomputable def lapDiffA20
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (T : D.RegularTime) (s : Real) :
    tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
      tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 0 :=
  (scalarL2ToH0 (I := I) (M := M)
    (G.metric (T : Real))).toContinuousLinearMap.comp
      (lapDiffA2 (I := I) (M := M) G T s)


@[simp] theorem lapDiffA20_apply
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (T : D.RegularTime) (s : Real)
    (v : tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2) :
    lapDiffA20 (I := I) (M := M) G T s v =
      (tensorHsZeroEquivL2 (I := I) (M := M)
        (tensorResolventL2_isCompactOperator
          (I := I) (M := M) (G.metric (T : Real)) 0 0)).symm
        (lapDiffA2 (I := I) (M := M) G T s v) :=
  rfl



theorem lapDiffA20_norm
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (T : D.RegularTime) (s : Real) :
    ‖lapDiffA20 (I := I) (M := M) G T s‖ =
      ‖lapDiffA2 (I := I) (M := M) G T s‖ := by
  unfold lapDiffA20
  exact (scalarL2ToH0 (I := I) (M := M)
    (G.metric (T : Real))).norm_toContinuousLinearMap_comp



theorem lapDiffA20_cont_of
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (T : D.RegularTime) {S : Set Real}
    (hcont : ContinuousOn
      (fun s : Real => lapDiffA2 (I := I) (M := M) G T s) S) :
    ContinuousOn
      (fun s : Real => lapDiffA20 (I := I) (M := M) G T s) S := by
  change ContinuousOn
    (fun s : Real =>
      (scalarL2ToH0 (I := I) (M := M)
        (G.metric (T : Real))).toContinuousLinearMap.comp
          (lapDiffA2 (I := I) (M := M) G T s)) S
  let post :
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
          TensorL2 0 0 (G.metric (T : Real))) →L[Real]
        (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →L[Real]
          tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 0) :=
    (ContinuousLinearMap.compL Real
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2)
      (TensorL2 0 0 (G.metric (T : Real)))
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 0))
      (scalarL2ToH0 (I := I) (M := M)
        (G.metric (T : Real))).toContinuousLinearMap
  exact post.continuous.comp_continuousOn hcont



theorem lapDiffA20_core
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∀ᶠ s in nhds (0 : Real),
      ∀ v : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (G.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) G T s v.1) =
          lapDiffCore (I := I) (M := M) (G.metric (T : Real))
            (G.metric ((T : Real) - s)) v := by
  filter_upwards [lapDiffA2_core (I := I) (M := M) G hG T] with s hs
  intro v
  rw [lapDiffA20_apply, LinearIsometryEquiv.apply_symm_apply, hs v]



theorem lapDiffA20_graph
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∀ᶠ s in nhds (0 : Real),
      ∀ u : tensorHs (I := I) (M := M)
          (G.metric (T : Real)) 0 0 2,
        (u,
            tensorHsZeroEquivL2 (I := I) (M := M)
              (tensorResolventL2_isCompactOperator
                (I := I) (M := M) (G.metric (T : Real)) 0 0)
              (lapDiffA20 (I := I) (M := M) G T s u)) ∈
          closure
            (Set.range fun
              v : ScalarH2Core (I := I) (M := M)
                  (G.metric (T : Real)) =>
                ((v.1 : tensorHs (I := I) (M := M)
                    (G.metric (T : Real)) 0 0 2),
                  lapDiffCore (I := I) (M := M)
                    (G.metric (T : Real))
                    (G.metric ((T : Real) - s)) v)) := by
  filter_upwards [lapDiffA20_core (I := I) (M := M) G hG T] with s hs
  intro u
  let J := tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) (G.metric (T : Real)) 0 0)
  let graph :
      tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 →
        tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 ×
          TensorL2 0 0 (G.metric (T : Real)) :=
    fun w => (w, J (lapDiffA20 (I := I) (M := M) G T s w))
  have hgraph : Continuous graph :=
    continuous_id.prodMk
      (J.continuous.comp
        (lapDiffA20 (I := I) (M := M) G T s).continuous)
  have hu :
      u ∈ closure
        (ScalarH2Core (I := I) (M := M) (G.metric (T : Real)) :
          Set (tensorHs (I := I) (M := M)
            (G.metric (T : Real)) 0 0 2)) :=
    tensorHs.mem_closure_finiteSupportSubmodule (I := I) (M := M) u
  have hmem := mem_closure_image hgraph.continuousAt hu
  rw [Set.image_eq_range] at hmem
  change graph u ∈ closure
    (Set.range fun
      v : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)) =>
        ((v.1 : tensorHs (I := I) (M := M)
            (G.metric (T : Real)) 0 0 2),
          lapDiffCore (I := I) (M := M) (G.metric (T : Real))
            (G.metric ((T : Real) - s)) v))
  refine closure_mono ?_ hmem
  rintro _ ⟨x, rfl⟩
  let v : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)) :=
    ⟨x.1, x.2⟩
  refine ⟨v, Prod.ext rfl ?_⟩
  exact (hs v).symm



theorem lapDiffA20_test
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (T : D.RegularTime) (s : Real)
    (u : tensorHs (I := I) (M := M)
      (G.metric (T : Real)) 0 0 2)
    (w : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)))
    (hgraph :
      (u,
          tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (G.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) G T s u)) ∈
        closure
          (Set.range fun
            v : ScalarH2Core (I := I) (M := M)
                (G.metric (T : Real)) =>
              ((v.1 : tensorHs (I := I) (M := M)
                  (G.metric (T : Real)) 0 0 2),
                lapDiffCore (I := I) (M := M)
                  (G.metric (T : Real))
                  (G.metric ((T : Real) - s)) v))) :
    (u,
        inner Real
          (tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (G.metric (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) G T s u))
          (SmoothCcTensor.toL2
            (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2))) ∈
      closure
        (Set.range fun
          v : ScalarH2Core (I := I) (M := M)
              (G.metric (T : Real)) =>
            ((v.1 : tensorHs (I := I) (M := M)
                (G.metric (T : Real)) 0 0 2),
              ∫ x, (Δ_g (I := I) (G.metric ((T : Real) - s))
                      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
                    Δ_g (I := I) (G.metric (T : Real))
                      (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x) *
                  reprScalar0 (I := I) (M := M) w.1 w.2 x
                ∂(riemannianVolumeMeasure (I := I) (M := M)
                  (G.metric (T : Real))))) := by
  let J := tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) (G.metric (T : Real)) 0 0)
  let test : TensorL2 0 0 (G.metric (T : Real)) :=
    SmoothCcTensor.toL2
      (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)
  let eval :
      (tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 ×
          TensorL2 0 0 (G.metric (T : Real))) →
        tensorHs (I := I) (M := M) (G.metric (T : Real)) 0 0 2 × Real :=
    fun p => (p.1, inner Real p.2 test)
  have heval : Continuous eval :=
    continuous_fst.prodMk
      (((innerSL Real).flip test).continuous.comp continuous_snd)
  have hmem := mem_closure_image heval.continuousAt hgraph
  change eval (u, J (lapDiffA20 (I := I) (M := M) G T s u)) ∈
    closure
      (Set.range fun
        v : ScalarH2Core (I := I) (M := M) (G.metric (T : Real)) =>
          ((v.1 : tensorHs (I := I) (M := M)
              (G.metric (T : Real)) 0 0 2),
            ∫ x, (Δ_g (I := I) (G.metric ((T : Real) - s))
                    (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x -
                  Δ_g (I := I) (G.metric (T : Real))
                    (reprScalar0_smooth (I := I) (M := M) v.1 v.2) x) *
                reprScalar0 (I := I) (M := M) w.1 w.2 x
              ∂(riemannianVolumeMeasure (I := I) (M := M)
                (G.metric (T : Real)))))
  refine closure_mono ?_ hmem
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  refine ⟨v, Prod.ext rfl ?_⟩
  simpa only [eval, test] using
    (lapDiffCore_pair (I := I) (M := M)
      (G.metric (T : Real)) (G.metric ((T : Real) - s)) v w).symm



theorem lapDiffA20_bound
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ omega : Real → Real,
      Tendsto omega (nhds 0) (nhds 0) ∧
      ∀ᶠ s in nhds (0 : Real),
        ∀ v : tensorHs (I := I) (M := M)
            (G.metric (T : Real)) 0 0 2,
          (Function.support v.coeff).Finite →
            ‖lapDiffA20 (I := I) (M := M) G T s v‖ ≤
              omega s * ‖v‖ := by
  obtain ⟨omega, homega, hbound⟩ :=
    lapDiffA2_bound (I := I) (M := M) G hG T
  refine ⟨omega, homega, ?_⟩
  filter_upwards [hbound] with s hs
  intro v hv
  simpa only [lapDiffA20_apply,
    LinearIsometryEquiv.norm_map] using hs v hv



theorem lapDiffA20_zero
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    Tendsto (fun s : Real => ‖lapDiffA20 (I := I) (M := M) G T s‖)
      (nhds 0) (nhds 0) := by
  have heq :
      (fun s : Real => ‖lapDiffA20 (I := I) (M := M) G T s‖) =
        fun s : Real => ‖lapDiffA2 (I := I) (M := M) G T s‖ := by
    funext s
    exact lapDiffA20_norm (I := I) (M := M) G T s
  rw [heq]
  exact lapDiffA2_zero (I := I) (M := M) G hG T

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
