/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import PDE.Analysis.MeasureTheory.Lp.Duality
import PDE.Analysis.MeasureTheory.Lp.WithDensity
import PDE.Analysis.Normed.Reflexivity

/-!
# Reflexivity of real `Lp` over a σ-finite measure

For `1 < p < ∞`, every continuous functional on the dual of real `Lp` is evaluation at
an `Lp` element. For a finite measure, the proof applies the conjugate dual representation
twice: pull the bidual functional back along the `Lq` pairing, then use surjectivity of that
pairing to identify its values on every `Lp` functional.

A σ-finite measure has the same null sets as a finite measure. Multiplication by the
appropriate density root identifies their `Lp` spaces isometrically, so the finite-measure
result transfers to the original space. In particular, this covers Lebesgue measure on
unbounded Euclidean domains.
-/

@[expose] public section

open Set Filter Function
open scoped ENNReal NNReal Topology symmDiff

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem surjective_inclusionInDoubleDual_of_finite [IsFiniteMeasure μ]
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (Lp ℝ p μ)) := by
  let q := ENNReal.conjExponent p
  have : ENNReal.HolderConjugate p q := inferInstance
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq_top : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp).ne
  let P : Lp ℝ q μ →L[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p
  let Q : Lp ℝ p μ →L[ℝ] StrongDual ℝ (Lp ℝ q μ) :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q
  intro H
  obtain ⟨u, hu⟩ := surjective_lpPairing (p := q) (q := p) hq_top hp_top (H.comp P)
  refine ⟨u, ?_⟩
  ext Λ
  obtain ⟨g, hg⟩ := surjective_lpPairing (p := p) (q := q) hp_top hq_top Λ
  change P g = Λ at hg
  rw [← hg]
  change P g u = H (P g)
  have hu' := congrArg (fun T : StrongDual ℝ (Lp ℝ q μ) ↦ T g) hu
  change Q u g = H (P g) at hu'
  calc
    P g u = Q u g := by
      simp only [P, Q, ContinuousLinearMap.lpPairing_eq_integral,
        ContinuousLinearMap.mul_apply', mul_comm]
    _ = H (P g) := hu'

/-- Real `Lp` over a σ-finite measure is reflexive for `1 < p < ∞`, expressed as
surjectivity of Mathlib's canonical continuous bidual inclusion. No finiteness of the
total measure is required. -/
theorem surjective_inclusionInDoubleDual [SigmaFinite μ] (hp : 1 < p) (hp_top : p ≠ ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (Lp ℝ p μ)) := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r = p :=
    ⟨p.toReal, ENNReal.toReal_pos (zero_lt_one.trans hp).ne' hp_top,
      ENNReal.ofReal_toReal hp_top⟩
  obtain ⟨ν, hν, hμν, hνμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  have := hν
  let e := withDensityRootLIEOfEq (E := ℝ) (p := r)
    (Measure.measurable_rnDeriv ν μ) (Measure.rnDeriv_pos' hμν)
    (Measure.rnDeriv_lt_top ν μ) (Measure.withDensity_rnDeriv_eq ν μ hνμ) hr
  exact NormedSpace.surjective_inclusionInDoubleDual_of_equiv e.toContinuousLinearEquiv
    (surjective_inclusionInDoubleDual_of_finite hp hp_top)

end MeasureTheory.Lp
