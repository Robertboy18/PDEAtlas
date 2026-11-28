/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.CriticalNonexistence

/-!
# Nonexistence of globally compactly propagating power-source waves

The spatial mass identity and ball-volume inequality give a weighted Kato
contradiction in the strict range `(n-1)*(p-1)<2`, for `p>1`. The initial velocity has
positive integral; the initial displacement and solution may have either sign.
The statements are the strict case of `not_global_cauchy_solution_of_le`, which also
covers the endpoint `(n-1)*(p-1)=2`.

The conclusion excludes a global jointly `C²` field satisfying the equation at all
positive times and the support cone at all nonnegative times. It does not construct a
maximal solution or prove norm blowup at its lifespan. In dimension three the range is
`1<p<2`, not the stronger John/Strauss range.

Compare Evans, §12.5.2, Theorem 2: for the problem (8) in three dimensions with data (9),
Evans excludes smooth global solutions for `1 < p < 1 + √2`. Step 1 of Evans's proof is the
mass inequality (10), which we derive in the same way in every dimension; Evans obtains the
support in `B(0, R + t)` from §12.1.2, Theorem 3, while here it is a hypothesis. Step 2
gets the growth (12) from the retarded potential and Huygens' principle. We use only the
linear growth of the mass that `∫ h > 0` gives, which yields the smaller range and needs no
sign condition on `∫ g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.2, Theorem 2 and its proof, equations (8)-(14);
  §12.1.2, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common

namespace WaveEquation.SmallData

variable {n : ℕ}

/-- Positive initial mass velocity rules out a global compactly propagating classical wave
in the strict elementary Kato range. The initial mass can be negative. This is the strict case
of `not_global_cauchy_solution_of_le`. -/
theorem not_global_cauchy_solution {u : ℝ^(n + 1) → ℝ} {h : ℝ^n → ℝ} {R p : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R) (hR : 0 < R) (hp : 1 < p) (hcrit : ((n : ℝ) - 1) * (p - 1) < 2)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hinitial : ∀ x : ℝ^n, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^n, h x) :
    False :=
  not_global_cauchy_solution_of_le hu hs hR hp hcrit.le hwave hinitial hpositive

/-- In three dimensions the elementary Kato argument excludes global solutions for
`1 < p < 2`. -/
theorem not_global_cauchy_solution_three {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R p : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R) (hR : 0 < R) (hp : 1 < p) (hp2 : p < 2)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^3, h x) :
    False := by
  apply not_global_cauchy_solution hu hs hR hp _ hwave hinitial hpositive
  norm_num
  linarith

end WaveEquation.SmallData
