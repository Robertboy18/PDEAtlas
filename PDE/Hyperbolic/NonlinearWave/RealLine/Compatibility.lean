/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Iteration
import CAS.ExactTactic

/-!
# Compatible finite-strip nonlinear waves

Causality and uniqueness identify the restriction of a longer-strip solution with
the solution selected on a shorter strip.

The Duhamel term (43) of Evans, §2.4.2, Example (i), at a point `(x, t)` depends only on the
source in the triangle `{(y, s) : 0 ≤ s ≤ t, |y - x| ≤ t - s}`, so on `ℝ × [0, S]` it does not
see the solution at later times. The restriction of the solution on `ℝ × [0, T]` therefore
solves the fixed point equation on `ℝ × [0, S]` for `S ≤ T`, and uniqueness identifies it with
the solution there (`stripRestriction_nonlinearStripSolution`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.2, Example (i), equation (43).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter Function
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- The inclusion of one closed time strip into a longer strip. -/
def stripEmbedding {S T : NNReal} (hST : S ≤ T) : C(ForwardStrip S, ForwardStrip T) where
  toFun p := (⟨p.1.1, ⟨p.1.property.1, p.1.property.2.trans hST⟩⟩, p.2)
  continuous_toFun := by fun_prop

/-- Restriction preserves bounded joint continuity. -/
def stripRestriction {S T : NNReal} (hST : S ≤ T)
    (u : ForwardStrip T →ᵇ ℝ) : ForwardStrip S →ᵇ ℝ :=
  u.compContinuous (stripEmbedding hST)

/-- Clipping to either horizon has the same value at times in the shorter strip. -/
theorem stripEmbedding_projection_of_mem {S T : NNReal} (hST : S ≤ T)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (S : ℝ)) (x : ℝ^1) :
    stripEmbedding hST (stripProjection S (timeSpaceCons s x)) =
      stripProjection T (timeSpaceCons s x) := by
  have ht : s ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs.1, hs.2.trans hST⟩
  change stripEmbedding hST (projIcc (0 : ℝ) S S.coe_nonneg s, x 0) =
    (projIcc (0 : ℝ) T T.coe_nonneg s, x 0)
  rw [projIcc_of_mem S.coe_nonneg hs, projIcc_of_mem T.coe_nonneg ht]
  rfl

/-- A solution on a longer strip restricts to the same nonlinear integral problem. -/
theorem stripRestriction_satisfies_integralEquation {S T : NNReal} (hST : S ≤ T) {f g h : ℝ → ℝ}
    (u : ForwardStrip T →ᵇ ℝ)
    (hu : ∀ p : ForwardStrip T, u p = dAlembertFormula g h p.2 p.1.1 -
      dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q))) (stripInclusion p)) :
    ∀ p : ForwardStrip S, stripRestriction hST u p = dAlembertFormula g h p.2 p.1.1 -
      dAlembertDuhamelSolution (fun q ↦ f (stripRestriction hST u (stripProjection S q)))
      (stripInclusion p) := by
  intro p
  change u (stripEmbedding hST p) = _
  rw [hu]
  change dAlembertFormula g h p.2 p.1.1 -
      dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q))) (stripInclusion p) = _
  congr 1
  refine dAlembertDuhamelSolution_eq_of_eqOn_past p.1.property.1 fun s hs x ↦ ?_
  have hsS : s ∈ Icc (0 : ℝ) (S : ℝ) := ⟨hs.1, hs.2.trans p.1.property.2⟩
  change f (u (stripProjection T (timeSpaceCons s x))) =
    f (u (stripEmbedding hST (stripProjection S (timeSpaceCons s x))))
  rw [stripEmbedding_projection_of_mem hST hsS]

/-- Select the unique integral solution on a prescribed finite strip. -/
def nonlinearStripSolution {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (T : NNReal) : ForwardStrip T →ᵇ ℝ :=
  Classical.choose (existsUnique_nonlinearStrip_of_boundedContinuousData_anyTime (T := T) hf g h)

/-- The selected strip field satisfies the nonlinear Duhamel equation. -/
theorem nonlinearStripSolution_satisfies_integralEquation {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (T : NNReal) (p : ForwardStrip T) :
    nonlinearStripSolution hf g h T p = dAlembertFormula g h p.2 p.1.1 - dAlembertDuhamelSolution
      (fun q ↦ f (nonlinearStripSolution hf g h T (stripProjection T q))) (stripInclusion p) :=
  (Classical.choose_spec
    (existsUnique_nonlinearStrip_of_boundedContinuousData_anyTime (T := T) hf g h)).1 p

/-- Uniqueness forces compatibility of the selected fields on overlapping strips. -/
theorem stripRestriction_nonlinearStripSolution {L S T : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (hST : S ≤ T) :
    stripRestriction hST (nonlinearStripSolution hf g h T) = nonlinearStripSolution hf g h S := by
  apply (Classical.choose_spec
    (existsUnique_nonlinearStrip_of_boundedContinuousData_anyTime (T := S) hf g h)).2
  exact stripRestriction_satisfies_integralEquation hST (nonlinearStripSolution hf g h T)
    (nonlinearStripSolution_satisfies_integralEquation hf g h T)

/-- The selected integral field has the assigned displacement at time zero. -/
theorem nonlinearStripSolution_initial {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) (T : NNReal) (x : ℝ) :
    nonlinearStripSolution hf g h T (⟨0, ⟨le_rfl, T.coe_nonneg⟩⟩, x) = g x := by
  rw [nonlinearStripSolution_satisfies_integralEquation]
  suffices (1 / 2 : ℝ) * (g x + g x) = g x by
    simpa [stripInclusion, dAlembertFormula] using this
  cas

end WaveEquation
