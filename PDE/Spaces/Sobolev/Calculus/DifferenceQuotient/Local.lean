/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalConverse
public import PDE.Analysis.Metric.BoundaryDistance

/-!
# Evans's interior difference quotient theorem

For an interior set with compact closure, the forward estimate holds at every nonzero
step smaller than half the distance to the boundary. Conversely, a uniform bound for
the Euclidean vector of these quotients constructs the weak gradient with the same
bound. Only the forward direction uses a Sobolev input.

These are the two clauses of Evans, §5.8.2, Theorem 3. The converse below assumes
`u ∈ Lᵖ(V)` on the open test domain `V`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2, Theorem 3, pp. 291-293: (i) for `1 ≤ p < ∞` and
  `u ∈ W^{1,p}(U)`, `‖D^h u‖_{Lᵖ(V)} ≤ C ‖Du‖_{Lᵖ(U)}` when `0 < |h| < dist(V, ∂U)/2`; (ii) for
  `1 < p < ∞`, a uniform bound on the difference quotients of `u ∈ Lᵖ(V)` gives `u ∈ W^{1,p}(V)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The half-boundary-distance condition in the equivalent doubled-step form. -/
theorem lt_half_boundaryEDist_iff {Ω V : Set (ℝ^n)} (h : ℝ) :
    ENNReal.ofReal |h| < Metric.boundaryEDist V Ω / 2 ↔
      ENNReal.ofReal (2 * |h|) < Metric.boundaryEDist V Ω := by
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  rw [mul_comm (2 : ℝ), ENNReal.ofReal_mul (abs_nonneg h)]
  norm_num

/-- Evans §5.8.2, Theorem 3(i): for `1 ≤ p < ∞`, open `Ω`, measurable `V` with compact closure in
`Ω` and `U ∈ W^{1,p}(Ω)` with representative `u`, the vector of difference quotients of `u` with
step `h ≠ 0`, `|h|` less than half the distance from `V` to `∂Ω`, has `Lᵖ(V)` norm at most
`n * ‖∇ U‖`. The constant `n` is independent of the function and the step. No extension-domain
assumption is imposed on the open domain. -/
theorem eLpNorm_vectorDifference_le_of_lt_half_boundaryEDist
    (hp : p ≠ ∞) {Ω V : Set (ℝ^n)} (hΩ : IsOpen Ω) (hV : MeasurableSet V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (U : W^{1,p}(Ω)) {u : ℝ^n → ℝ}
    (hu : baseRepresentative U =ᵐ[domainMeasure n Ω] u)
    {h : ℝ} (hh : h ≠ 0)
    (hmargin : ENNReal.ofReal |h| < Metric.boundaryEDist V Ω / 2) :
    eLpNorm (vectorDifference h u) p (domainMeasure n V) ≤
      ENNReal.ofReal ((n : ℝ) * ‖∇ U‖) := by
  have hpos : 0 < |h| := abs_pos.mpr hh
  have hdouble := (lt_half_boundaryEDist_iff h).mp hmargin
  apply eLpNorm_vectorDifference_le_of_thickening hp hΩ hV hVc (by positivity)
    (Metric.thickening_subset_of_le_boundaryEDist (subset_closure.trans hVΩ) hdouble.le)
    U hu hh
  linarith

/-- Evans §5.8.2, Theorem 3(ii): for `1 < p < ∞`, open `V` with compact closure in the open set
`Ω` and `u ∈ Lᵖ(V)`, if the vector of difference quotients of `u` has `Lᵖ(V)` norm at most `C`
for every step `h ≠ 0` with `|h|` less than half the distance from `V` to `∂Ω`, then `u`
represents some `U ∈ W^{1,p}(V)` with `‖∇ U‖ ≤ C`. -/
theorem exists_sobolev_of_bounded_vectorDifference_boundary
    (hp : 1 < p) (hp_top : p ≠ ∞) {Ω V : Set (ℝ^n)}
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {u : ℝ^n → ℝ} (hu : MemLp u p (domainMeasure n V))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ h : ℝ, h ≠ 0 →
      ENNReal.ofReal |h| < Metric.boundaryEDist V Ω / 2 →
      eLpNorm (vectorDifference h u) p (domainMeasure n V) ≤ ENNReal.ofReal C) :
    ∃ U : W^{1,p}(V),
      baseRepresentative U =ᵐ[domainMeasure n V] u ∧ ‖∇ U‖ ≤ C := by
  obtain ⟨ρ, hρ, hρd⟩ := Metric.exists_pos_le_boundaryEDist hΩ hVc hVΩ
  apply exists_sobolev_of_bounded_vectorDifference hp hp_top hV hu
    (δ := ρ / 2) (half_pos hρ) hC
  intro h hh hhρ
  apply hbound h hh
  apply (lt_half_boundaryEDist_iff h).mpr
  apply lt_of_lt_of_le _ hρd
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
  linarith

end SobolevSpace.GraphSpace.DifferenceQuotient
