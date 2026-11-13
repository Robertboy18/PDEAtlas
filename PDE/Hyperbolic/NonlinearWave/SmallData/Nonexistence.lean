/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Inequality
public import PDE.Hyperbolic.NonlinearWave.SmallData.Kato

/-!
# Nonexistence of globally compactly propagating power-source waves

The spatial mass identity and ball-volume inequality give a weighted Kato
contradiction in the strict range `(n-1)*(p-1)<2`, for `p>1`. The initial velocity has
positive integral; the initial displacement and solution may have either sign.

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
in the strict elementary Kato range. The initial mass can be negative. -/
theorem not_global_cauchy_solution {u : ℝ^(n + 1) → ℝ} {h : ℝ^n → ℝ} {R p : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R) (hR : 0 < R) (hp : 1 < p) (hcrit : ((n : ℝ) - 1) * (p - 1) < 2)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hinitial : ∀ x : ℝ^n, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^n, h x) :
    False := by
  let H := ∫ x : ℝ^n, h x
  let F := spatialMass u
  let P := spatialMass (∂[0] u)
  let a := max 1 (R + 2 * |F 0| / H)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨hest, hgrowth⟩ := cauchy_spatialMass_estimates hu hs hR hp hwave hinitial hpositive
  have hH : 0 < H := hpositive
  have hlinear (t : ℝ) (ht : a ≤ t) : (H / 2) * (R + t) ≤ F t := by
    have hta : R + 2 * |F 0| / H ≤ t := (le_max_right _ _).trans ht
    have hmul := mul_le_mul_of_nonneg_left hta hH.le
    have hid : H * (R + 2 * |F 0| / H) = H * R + 2 * |F 0| := by
      have hH0 := hH.ne'
      field_simp
    rw [hid] at hmul
    have hg := hgrowth t (ha.le.trans ht)
    change F 0 + H * t ≤ F t at hg
    nlinarith [neg_abs_le (F 0)]
  apply Kato.not_weighted_second_order_on_Ici
    (F := F) (P := P) (C := massCoefficient n p) (q := (n : ℝ) * (p - 1))
    (δ := H / 2) (a := a) (R := R)
    (massCoefficient_pos n p) hp (mul_nonneg (Nat.cast_nonneg n) (by linarith))
    (by nlinarith [hcrit]) (div_pos hH (by norm_num)) (add_pos hR ha)
  · exact fun t ht ↦ hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs (ha.trans_le ht)
  · exact fun t ht ↦ (hasDerivAt_spatialMass_time hu hs (ha.trans_le ht)).differentiableAt
  · intro t ht
    have hd := hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs (ha.trans_le ht)
    change 0 ≤ spatialMass (∂[0] u) t
    rw [← hd.deriv]
    exact (hest t (ha.trans_le ht)).2.2.le
  · exact hlinear
  · intro t ht
    have ht0 := ha.trans_le ht
    have hFpos : 0 < F t :=
      (mul_pos (div_pos hH (by norm_num)) (add_pos hR ht0)).trans_le (hlinear t ht)
    have hd := hasDerivAt_spatialMass_time_eq_source hu hs ht0 (hwave t ht0)
    rw [hd.deriv]
    have hi := (hest t ht0).2.1
    rw [(hest t ht0).1] at hi
    change massCoefficient n p * (R + t) ^ (-(n : ℝ) * (p - 1)) *
      |F t| ^ p ≤ _ at hi
    simpa only [neg_mul, abs_of_pos hFpos] using hi

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
