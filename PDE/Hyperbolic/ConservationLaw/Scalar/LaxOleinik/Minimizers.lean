/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Slope
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.UniformlyConvex
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Footpoint.Order
import CAS.ExactTactic

/-!
# The Lax–Oleinik formula for arbitrary essentially bounded data

Evans, §3.4.2, Theorem 1, combines positive-time attainment, countable failure
of uniqueness, monotone footpoints, and the spatial derivative formula.
Here the primitive is the oriented integral of the supplied `L∞` datum.
It need not be convex, bounded, or differentiable at a minimizing footpoint.

The fixed-time exceptional set may depend on time. The joint almost-everywhere
partial derivative identity comes separately from the potential
regularity theorem, not from a union of the fixed-time exceptions.

Monotonicity of the selected footpoints and the inverse-flux Lipschitz estimate
give the sharp Oleinik bound `u(t,x+z) - u(t,x) ≤ z / (θ*t)` for every positive
time and nonnegative increment; this is the estimate (36) of Evans, §3.4.3, with `C = θ⁻¹`.
The bound holds even at nonunique footpoints: it uses the selected representative itself, not a
pointwise derivative identity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, Theorem 1, equations (27)-(29); §3.4.3, Lemma (36)
  and the definition of an entropy solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The full scalar Lax–Oleinik formula under C² uniform convexity and
`L∞` data. Every positive time has an attained monotone footpoint selection,
unique outside a countable set, and the derivative formula almost
everywhere. Joint almost-everywhere equality is an independent conclusion.
Arbitrary linear and constant flux terms are retained. -/
theorem laxOleinik_formula_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) :
    let L := HopfLax1D.legendreTransform F
    let h := fun x ↦ ∫ s in (0 : ℝ)..x, g s
    let G : ℝ → ℝ := (orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower).symm
    (∀ t : ℝ, 0 < t →
      (∀ x, value L h t x = h (minimizingFootpoint L h t x) +
        t * L ((x - minimizingFootpoint L h t x) / t)) ∧
      Monotone (minimizingFootpoint L h t) ∧
      {x | ¬ ∃! y, value L h t x = h y + t * L ((x - y) / t)}.Countable ∧
      (∀ᵐ x : ℝ, HasDerivAt (value L h t)
        (G ((x - minimizingFootpoint L h t x) / t)) x ∧
        solution F g !₂[t, x] = G ((x - minimizingFootpoint L h t x) / t))) ∧
    solution F g =ᵐ[volume.restrict forwardHalfSpace]
      (∂[1] (initialPotential F g)) := by
  dsimp only
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  have hcont := HopfLax1D.continuous_legendreTransform hFin
  have hL := superlinear_scalar_legendre hFin
  have hstrict := strictConvexOn_legendreTransform_of_deriv2_lower_bound hF hθ hlower
  have hh := lipschitzWith_intervalIntegral_of_memLp_top hg 0
  refine ⟨?_, solution_ae_eq_partialDeriv_of_deriv2_lower_bound hF hθ hlower hg⟩
  intro t ht
  refine ⟨minimizingFootpoint_spec hcont hL hh ht,
    monotone_minimizingFootpoint hcont hL hstrict hh ht,
    countable_not_existsUnique_fixed_footpoint hcont hL hstrict hh ht, ?_⟩
  filter_upwards [(lipschitzWith_value hL hh ht.le).ae_differentiableAt,
    solution_ae_eq_deriv_value_of_deriv2_lower_bound hF hθ hlower hg ht] with x hdiff heq
  have hs := solution_eq_inverse_footpoint_of_deriv2_lower_bound hF hθ hlower
    (g := g) (p := !₂[t, x]) (by simpa using ht)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hs
  exact ⟨heq.symm.trans hs ▸ hdiff.hasDerivAt, hs⟩

/-- The constructed solution for arbitrary essentially bounded data satisfies
the sharp one-sided estimate under `F'' ≥ θ > 0`. Monotone footpoints bound
the increase in characteristic speed by `z / t`, and the inverse flux derivative
has Lipschitz constant `θ⁻¹`. The estimate holds for the selected representative
at every positive-time point, including points with nonunique minimizers. -/
theorem solution_slope_le_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) {t : ℝ} (ht : 0 < t)
    (x : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    solution F g !₂[t, x + z] - solution F g !₂[t, x] ≤ z / (θ * t) := by
  let y := minimizingFootpoint (HopfLax1D.legendreTransform F) (fun x ↦ ∫ s in (0 : ℝ)..x, g s) t
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  have hmono : Monotone y := ((laxOleinik_formula_of_deriv2_lower_bound hF hθ hlower hg).1 t ht).2.1
  have hLip : LipschitzWith (⟨θ, hθ.le⟩⁻¹ : ℝ≥0) e.symm :=
    lipschitzWith_orderIsoOfDerivLowerBound_symm hF.differentiable_deriv_two hθ hlower
  let q := (x - y x) / t
  have hspeed : (x + z - y (x + z)) / t ≤ q + z / t := by
    calc
      _ ≤ (x + z - y x) / t := div_le_div_of_nonneg_right
          (sub_le_sub_left (hmono (le_add_of_nonneg_right hz)) _) ht.le
      _ = _ := by dsimp only [q]; cas
  rw [solution_eq_inverse_footpoint_of_deriv2_lower_bound hF hθ hlower (p := !₂[t, x + z]) ht,
    solution_eq_inverse_footpoint_of_deriv2_lower_bound hF hθ hlower (p := !₂[t, x]) ht]
  change e.symm ((x + z - y (x + z)) / t) - e.symm q ≤ z / (θ * t)
  calc
    _ ≤ e.symm (q + z / t) - e.symm q := sub_le_sub_right (e.symm.monotone hspeed) _
    _ ≤ |e.symm (q + z / t) - e.symm q| := le_abs_self _
    _ ≤ θ⁻¹ * (z / t) := by
      have hdist : dist (e.symm (q + z / t)) (e.symm q) ≤
          θ⁻¹ * dist (q + z / t) q := hLip.dist_le_mul (q + z / t) q
      simpa only [Real.dist_eq, add_sub_cancel_left,
        abs_of_nonneg (div_nonneg hz ht.le)] using hdist
    _ = z / (θ * t) := by cas

/-- The Lax–Oleinik solution satisfies the almost-everywhere one-sided entropy condition (ii) of
Evans, §3.4.3(b), with constant `θ⁻¹`. Only the flux's C² uniform
convexity and essential boundedness of the initial datum are assumed; the
slope bound is derived from the minimizers. -/
theorem hasOleinikBound_solution_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) :
    HasOleinikBound (solution F g) θ⁻¹ := by
  refine ⟨inv_nonneg.mpr hθ.le, Filter.Eventually.of_forall fun p ht hz ↦ ?_⟩
  apply (solution_slope_le_of_deriv2_lower_bound hF hθ hlower hg ht p.2.1 hz.le).trans
  have halgebra (θ t z : ℝ) :
      θ⁻¹ * (1 + t⁻¹) * z = z / (θ * t) + θ⁻¹ * z := by cas
  rw [halgebra]
  exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hθ.le) hz.le)

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
