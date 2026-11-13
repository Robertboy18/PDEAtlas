/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Pullback.SecondOrder
public import PDE.Analysis.MeasureTheory.Lp.Composition.MeasureBound
import PDE.Analysis.Normed.Operator.InjectiveLift
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Bounded H² composition along the local flow

The weak real-line pullback theorem supplies the graph. Injectivity of the
base coordinate lifts the existing L² composition operator to H². The resulting
operator has the quantitative bound from the weak chain rule and represents
ordinary composition pointwise through the canonical continuous representative.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev

namespace SobolevSpace.GraphSpace

/-- A bounded positive C² coordinate map induces a bounded linear pullback on
the canonical H² graph. Its representative and norm estimate are derived from
the weak change of variables theorem. -/
theorem exists_h2PullbackCLM
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm)
    {J J' : ℝ → ℝ} {M N : ℝ}
    (hJ : Continuous J) (hJ' : Continuous J')
    (hJpos : ∀ x, 0 ≤ J x) (he' : ∀ x, HasDerivAt e (J x) x)
    (hderiv : ∀ x, HasDerivAt J (J' x) x)
    (hJbound : ∀ x, ‖J x‖ ≤ M) (hJ'bound : ∀ x, ‖J' x‖ ≤ N) :
    ∃ P : W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1),
      (∀ W, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (P W)) =
        fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) (e x)) ∧
      ∀ W, ‖P W‖ ≤ succOrderAssemblyNormBound 1 1 *
        (Real.sqrt K * (1 + 2 * (M + N + M * M)) * ‖W‖) := by
  let A : W^{2,2}(ℝ^1) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
    oneDimensionalPushforwardL2.toContinuousLinearMap.comp wkpBaseCoordinateCLM
  let L := Lp.compMeasureLeSMul (E := ℝ) (p := 2) e e.continuous.measurable
    ENNReal.coe_ne_top (map_volume_le_of_lipschitz_inverse e he)
  have hA : Function.Injective A := fun _ _ h ↦
    wkpBaseCoordinateCLM_injective isOpen_univ
      (oneDimensionalPushforwardL2.injective h)
  have heq : QuasiMeasurePreserving e volume volume :=
    ⟨e.continuous.measurable,
      Measure.absolutelyContinuous_of_le_smul (map_volume_le_of_lipschitz_inverse e he)⟩
  have hrep (W : W^{2,2}(ℝ^1)) :
      (A W : ℝ → ℝ) =ᵐ[volume]
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) := by
    change (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume] _
    rw [← realLineCoordinateCLM_base_lowerOrder]
    exact realLineCoordinate_ae_representative _
  have hLrep (W : W^{2,2}(ℝ^1)) :
      (L (A W) : ℝ → ℝ) =ᵐ[volume]
        fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) (e x) :=
    (Lp.coeFn_compMeasureLeSMul _ _ _ _ _).trans (heq.ae_eq_comp (hrep W))
  have hex (W : W^{2,2}(ℝ^1)) :
      ∃ V : W^{2,2}(ℝ^1), A V = L (A W) ∧
        ‖V‖ ≤ succOrderAssemblyNormBound 1 1 *
          (Real.sqrt K * (1 + 2 * (M + N + M * M)) * ‖W‖) := by
    obtain ⟨V, hV, hnorm⟩ := exists_h2_comp_of_bounded_positive_jacobian
      e he hJ hJ' hJpos he' hderiv hJbound hJ'bound W
      (continuous_realLineRepresentative _) (hrep W)
    exact ⟨V, Lp.ext (hV.trans (hLrep W).symm), hnorm⟩
  obtain ⟨P, hP⟩ := ContinuousLinearMap.exists_lift_of_injective A (L.comp A) hA
    (fun W ↦ (hex W).imp fun V hV ↦ hV.1)
  have hbase (W : W^{2,2}(ℝ^1)) : A (P W) = L (A W) :=
    congrArg (fun D : W^{2,2}(ℝ^1) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) ↦ D W) hP
  refine ⟨P, ?_, ?_⟩
  · intro W
    apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _)
      ((continuous_realLineRepresentative _).comp e.continuous)).mp
    exact (hrep (P W)).symm.trans ((hbase W) ▸ hLrep W)
  · intro W
    obtain ⟨V, hV, hnorm⟩ := hex W
    exact (hA ((hbase W).trans hV.symm)) ▸ hnorm

end SobolevSpace.GraphSpace
