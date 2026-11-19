/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.Estimates
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The nonlinear wave map on bounded continuous spacetime strips

Only time is clipped when extending a strip field. Joint spacetime continuity
avoids assuming strong continuity of translations on all bounded continuous functions.
The source estimate retains the term ‖f(0)‖.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter Function
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- A closed finite time strip, with its joint spacetime topology. -/
abbrev ForwardStrip (T : NNReal) := Icc (0 : ℝ) (T : ℝ) × ℝ

/-- Clip only the time coordinate when extending a strip function. -/
def stripProjection (T : NNReal) (p : ℝ^2) : ForwardStrip T :=
  (projIcc (0 : ℝ) T T.coe_nonneg (p 0), p 1)

/-- Clipping time preserves joint spacetime continuity. -/
theorem continuous_stripProjection (T : NNReal) : Continuous (stripProjection T) :=
  (continuous_projIcc.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0)).prodMk
    (PiLp.continuous_apply 2 _ 1)

/-- The spacetime field associated with a point of a finite strip. -/
def stripInclusion {T : NNReal} (p : ForwardStrip T) : ℝ^2 :=
  timeSpaceCons p.1.1 (EuclideanSpace.single (0 : Fin 1) p.2)

/-- The strip inclusion carries the product topology into the spacetime topology. -/
theorem continuous_stripInclusion (T : NNReal) :
    Continuous (stripInclusion (T := T)) :=
  (contDiff_timeSpaceCons_uncurry 1 (m := 0)).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      ((PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).comp
        (continuous_pi fun i ↦ by fin_cases i; simpa using continuous_snd)))

/-- A Lipschitz scalar nonlinearity sends bounded strip functions to bounded sources. -/
theorem norm_nonlinear_stripSource_le {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (u : ForwardStrip T →ᵇ ℝ) (p : ℝ^2) :
    ‖f (u (stripProjection T p))‖ ≤ ‖f 0‖ + L * ‖u‖ := by
  calc
    ‖f (u (stripProjection T p))‖ ≤
        ‖f (u (stripProjection T p)) - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ L * ‖u‖ + ‖f 0‖ := by
      gcongr
      simpa only [dist_eq_norm, sub_zero] using hf.dist_le_mul_of_le (y := 0)
          (by simpa only [dist_zero_right] using u.norm_coe_le_norm (stripProjection T p))
    _ = ‖f 0‖ + L * ‖u‖ := add_comm _ _

/-- Restrict the retarded wave driven by a nonlinear strip source. -/
def nonlinearStripRetarded {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (u : ForwardStrip T →ᵇ ℝ) : ForwardStrip T →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p ↦ dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q)))
      (stripInclusion p))
    (((contDiff_one_dAlembertDuhamelSolution
      (hf.continuous.comp (u.continuous.comp (continuous_stripProjection T)))).continuous).comp
        (continuous_stripInclusion T))
    ((T : ℝ) ^ 2 / 2 * (‖f 0‖ + L * ‖u‖)) (fun p ↦ by
      have hb := norm_dAlembertDuhamelSolution_le
        (norm_nonlinear_stripSource_le hf u) (p := stripInclusion p)
        (by simpa [stripInclusion] using p.1.property.1)
      apply hb.trans
      simp only [stripInclusion, timeSpaceCons_zero]
      gcongr
      · exact p.1.property.1
      · exact p.1.property.2)

/-- The nonlinear Volterra map, with any prescribed bounded continuous free field. -/
def nonlinearStripMap {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (H u : ForwardStrip T →ᵇ ℝ) : ForwardStrip T →ᵇ ℝ :=
  H - nonlinearStripRetarded hf u

/-- The scalar Lipschitz estimate passes through the double integral. -/
theorem dist_nonlinearStripRetarded_le {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (u v : ForwardStrip T →ᵇ ℝ) :
    dist (nonlinearStripRetarded hf u) (nonlinearStripRetarded hf v) ≤
      ((T : ℝ) ^ 2 / 2 * L) * dist u v := by
  refine (BoundedContinuousFunction.dist_le (by positivity)).mpr fun p ↦ ?_
  change ‖dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q))) (stripInclusion p) -
    dAlembertDuhamelSolution (fun q ↦ f (v (stripProjection T q))) (stripInclusion p)‖ ≤ _
  rw [← dAlembertDuhamelSolution_sub (f := fun q ↦ f (u (stripProjection T q)))
    (g := fun q ↦ f (v (stripProjection T q)))
    (hf.continuous.comp (u.continuous.comp (continuous_stripProjection T)))
    (hf.continuous.comp (v.continuous.comp (continuous_stripProjection T)))]
  have hb (q : ℝ^2) : ‖f (u (stripProjection T q)) - f (v (stripProjection T q))‖ ≤
      L * dist u v := by
    simpa only [dist_eq_norm] using hf.dist_le_mul_of_le
      (BoundedContinuousFunction.dist_coe_le_dist (f := u) (g := v) (stripProjection T q))
  have he := norm_dAlembertDuhamelSolution_le hb (p := stripInclusion p)
    (by simpa [stripInclusion] using p.1.property.1)
  apply he.trans
  simp only [stripInclusion, timeSpaceCons_zero]
  calc
    (p.1.1 ^ 2 / 2) * (L * dist u v) ≤ ((T : ℝ) ^ 2 / 2) * (L * dist u v) := by
      gcongr
      · exact p.1.property.1
      · exact p.1.property.2
    _ = _ := (mul_assoc _ _ _).symm

/-- The Volterra map contracts on every strip with `L T² / 2 < 1`. -/
theorem contractingWith_nonlinearStripMap {T L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (H : ForwardStrip T →ᵇ ℝ) (hsmall : T ^ 2 / 2 * L < 1) :
    ContractingWith (T ^ 2 / 2 * L) (nonlinearStripMap hf H) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  simpa only [nonlinearStripMap, dist_sub_left, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_pow, NNReal.coe_ofNat] using dist_nonlinearStripRetarded_le hf u v

/-- A bounded continuous solution of the nonlinear integral equation on a short strip.
The source is `-f(u)`, with `f(0)` arbitrary. -/
theorem existsUnique_nonlinearStrip_fixedPoint {T L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (H : ForwardStrip T →ᵇ ℝ) (hsmall : T ^ 2 / 2 * L < 1) :
    ∃! u : ForwardStrip T →ᵇ ℝ, ∀ p, u p = H p -
      dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q))) (stripInclusion p) := by
  let hc := contractingWith_nonlinearStripMap hf H hsmall
  refine ⟨hc.fixedPoint (nonlinearStripMap hf H), ?_, ?_⟩
  · exact fun p ↦ (congrArg (fun u : ForwardStrip T →ᵇ ℝ ↦ u p) hc.fixedPoint_isFixedPt).symm
  · intro v hv
    apply hc.fixedPoint_unique
    ext p
    exact (hv p).symm

end WaveEquation
