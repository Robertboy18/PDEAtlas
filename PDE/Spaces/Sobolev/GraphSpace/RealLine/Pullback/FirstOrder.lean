/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Measurability

/-!
# First-order Sobolev pullbacks

A differentiable coordinate change with bounded nonnegative Jacobian and a
Lipschitz inverse preserves H¹. The weak chain rule supplies the derivative
and its quantitative norm bound. A jointly measurable coordinate family
preserves measurability of the pulled-back Sobolev graphs.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Sobolev
open SobolevSpace SobolevSpace.GraphSpace

namespace SobolevSpace.GraphSpace

/-- First-order pullback for a bounded positive Jacobian, including its graph
norm. No classical derivative of the input representative is required. -/
theorem exists_h1_comp_of_bounded_positive_jacobian
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm)
    {J : ℝ → ℝ} {M : ℝ} (hJ : Continuous J) (hJpos : ∀ x, 0 ≤ J x)
    (he' : ∀ x, HasDerivAt e (J x) x) (hJbound : ∀ x, ‖J x‖ ≤ M)
    (V : W^{1,2}(ℝ^1)) :
    ∃ W : W^{1,2}(ℝ^1),
      realLineRepresentative W = (fun x ↦ realLineRepresentative V (e x)) ∧
      ‖W‖ ≤ Real.sqrt K * (1 + M) * ‖V‖ := by
  let g := realLineCoordinateCLM (singleDerivIndex 1 0) V
  have hv := memLp_comp_of_lipschitz_inverse e he (memLp_realLineRepresentative V)
  have hg := memLp_comp_of_lipschitz_inverse e he (Lp.memLp g)
  have hd := memLp_mul_of_bounded hg hJ hJbound
  have hweak := hasWeakTimeDerivativeOn_comp_of_positive_jacobian e he hJ hJpos he'
    hJbound (continuous_realLineRepresentative V) (Lp.memLp g)
    (hasWeakTimeDerivativeOn_realLineRepresentative V)
  refine ⟨mkW12OfWeakDerivative hv hd hweak,
    realLineRepresentative_mkW12 hv hd hweak
      ((continuous_realLineRepresentative V).comp e.continuous), ?_⟩
  have hM : 0 ≤ M := (norm_nonneg (J 0)).trans (hJbound 0)
  have hbase := norm_toLp_comp_of_lipschitz_inverse e he (memLp_realLineRepresentative V)
  rw [toLp_realLineRepresentative] at hbase
  have hrow := norm_toLp_comp_of_lipschitz_inverse e he (Lp.memLp g)
  rw [Lp.toLp_coeFn] at hrow
  have hdBound := (norm_toLp_mul_of_bounded hg hJ hJbound).trans
    (mul_le_mul_of_nonneg_left hrow hM)
  change ‖realLineH1Jet _ _‖ ≤ _
  calc
    _ ≤ _ := (norm_realLineH1Jet_le _ _).trans (add_le_add hbase hdBound)
    _ ≤ Real.sqrt K * ‖V‖ + M * (Real.sqrt K * ‖V‖) := by
      gcongr
      · exact norm_realLineCoordinateCLM_le _ V
      · exact norm_realLineCoordinateCLM_le _ V
    _ = _ := by ring

/-- Time measurability of an H¹ pullback follows from its representative,
without operator-norm measurability of the coordinate family. -/
theorem stronglyMeasurable_h1_pullback
    {T : Type*} [MeasurableSpace T] {e : T → ℝ → ℝ}
    (he : Measurable (Function.uncurry e))
    {V W : T → W^{1,2}(ℝ^1)}
    (hW : ∀ t, realLineRepresentative (W t) =
      fun x ↦ realLineRepresentative (V t) (e t x))
    (hV : StronglyMeasurable V) : StronglyMeasurable W := by
  apply stronglyMeasurable_hk_of_joint_representative W
    (v := fun t x ↦ realLineRepresentative (V t) (e t x))
    ((stronglyMeasurable_realLineRepresentative hV).comp_measurable
      (measurable_fst.prodMk he))
  intro t
  exact (realLineCoordinate_ae_representative (W t)).trans
    (Filter.EventuallyEq.of_eq (hW t))

end SobolevSpace.GraphSpace
