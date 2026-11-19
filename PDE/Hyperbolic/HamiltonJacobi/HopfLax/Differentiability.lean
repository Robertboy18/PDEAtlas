/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Regularity
import CAS.ExactTactic

/-!
# The Hopf–Lax equation at differentiability points

At an upper contact, dynamic programming tests every backward straight path.
Taking the dual supremum gives the subsolution inequality. At a lower contact,
one minimizing path suffices; its exact cost gives the opposite inequality.
The proof differentiates only the test function, never the minimizing velocity
or the Lagrangian.

The contact inequalities require differentiability only at the contact point.
Taking the value function itself as both tests gives the Hamilton–Jacobi equation
at every positive-time differentiability point. The initial data are continuous
with an affine norm lower bound.

The equation at differentiability points is Theorem 5 of Evans, §3.3.2, and the two
inequalities follow the two steps of its proof, written for test functions as in the proof of
Theorem 3 in §10.3.4. The viscosity construction and the almost-everywhere equation
reuse the same two inequalities.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 5 and its proof; §10.3.4, proof of
  Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

open Filter
open scoped Topology

set_option linter.missingDocs true

/-- Differentiating a backward straight path gives the negative directional
derivative as the limit of its right-hand difference quotients. -/
private theorem tendsto_backward_slope {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : F → ℝ} {z : F} (hφ : DifferentiableAt ℝ φ z) (v : F) :
    Tendsto (fun h : ℝ ↦ (φ (z - h • v) - φ z) / h) (𝓝[>] (0 : ℝ)) (𝓝 (-(fderiv ℝ φ z) v)) := by
  have hline : HasDerivAt (fun h : ℝ ↦ z - h • v) (-v) 0 := by
    simpa only [Pi.sub_def, id, one_smul, zero_sub] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := z)).sub ((hasDerivAt_id (x := (0 : ℝ))).smul_const v)
  have hcomp := hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
    (by simp : z = z - (0 : ℝ) • v)
  simpa only [Function.comp_def, zero_add, zero_smul, sub_zero, map_neg,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hcomp.tendsto_slope_zero_right

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]

/-- A spacetime directional derivative splits into the time derivative and
the pairing of the spatial gradient with the velocity. -/
private theorem test_direction {φ : E × ℝ → ℝ} {z : E × ℝ} (hφ : DifferentiableAt ℝ φ z) (q : E) :
    fderiv ℝ φ z (q, 1) = fderiv ℝ φ z (0, 1) + inner ℝ (∇ (fun x ↦ φ (x, z.2)) z.1) q := by
  have hspace : inner ℝ (∇ (fun x ↦ φ (x, z.2)) z.1) q =
      fderiv ℝ φ z (q, 0) := by
    rw [inner_gradient_left, fderiv_spaceSlice hφ]
    rfl
  have hsplit : (q, (1 : ℝ)) = (q, (0 : ℝ)) + (0, (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, hspace, add_comm]

variable [ProperSpace E] {L g : E → ℝ}
    (hcont : Continuous L) (hL : Superlinear L)
    (hconv : ConvexOn ℝ Set.univ L) (hg : Continuous g)
    {K : NNReal} {A : ℝ} (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y)

include hcont hL hg hlower

include hconv in
/-- Dynamic programming bounds the residual of a differentiable upper test
by zero. Differentiability is needed only at the contact point. -/
theorem residual_le_zero_of_isLocalMaxOn {z : E × ℝ} (ht : 0 < z.2) {φ : E × ℝ → ℝ}
    (hdiff : DifferentiableAt ℝ φ z)
    (hmax : IsLocalMaxOn (fun w ↦ value L g w.2 w.1 - φ w) positiveTimeDomain z) :
    fderiv ℝ φ z (0, 1) + hamiltonian L (∇ (fun x ↦ φ (x, z.2)) z.1) ≤ 0 := by
  have hlocal : ∀ᶠ w in 𝓝 z, value L g w.2 w.1 - φ w ≤ value L g z.2 z.1 - φ z :=
    hmax.isLocalMax (isOpen_positiveTimeDomain.mem_nhds ht)
  have hdir : ∀ q : E, (fderiv ℝ φ z) (q, 1) ≤ L q := by
    intro q
    let γ : ℝ → E × ℝ := fun h ↦ z - h • (q, 1)
    have hγ : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      have hc : ContinuousAt γ (0 : ℝ) :=
        continuousAt_const.sub (continuousAt_id.smul continuousAt_const)
      have hfull : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 z) := by
        simpa only [γ, zero_smul, sub_zero] using hc.tendsto
      exact hfull.mono_left nhdsWithin_le_nhds
    have hquot : ∀ᶠ h in 𝓝[>] (0 : ℝ),
        -L q ≤ (φ (γ h) - φ z) / h := by
      filter_upwards [Ioo_mem_nhdsGT ht, hγ.eventually hlocal] with h hh hcontact
      have hstep := value_le_step_of_norm_lower_bound hcont hL hconv hg hlower
        (sub_pos.mpr hh.2) hh.1 z.1 q
      have heq : z.2 - h + h = z.2 := by cas
      rw [heq] at hstep
      change value L g (z.2 - h * 1) (z.1 - h • q) - φ (γ h) ≤ value L g z.2 z.1 - φ z at hcontact
      simp only [mul_one] at hcontact
      apply (le_div_iff₀ hh.1).mpr
      linarith
    have htend := tendsto_backward_slope hdiff (q, (1 : ℝ))
    have hlim : -L q ≤ -(fderiv ℝ φ z) (q, 1) := ge_of_tendsto htend hquot
    linarith
  have hsup : hamiltonian L (∇ (fun x ↦ φ (x, z.2)) z.1) ≤
      -(fderiv ℝ φ z) (0, 1) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨q, rfl⟩
    have hq := hdir q
    rw [test_direction hdiff q] at hq
    linarith
  linarith

/-- An attained minimizing path bounds the residual of a differentiable
lower test from below by zero. Convexity is not needed for this direction. -/
theorem residual_nonneg_of_isLocalMinOn {z : E × ℝ} (ht : 0 < z.2) {φ : E × ℝ → ℝ}
    (hdiff : DifferentiableAt ℝ φ z)
    (hmin : IsLocalMinOn (fun w ↦ value L g w.2 w.1 - φ w) positiveTimeDomain z) :
    0 ≤ fderiv ℝ φ z (0, 1) + hamiltonian L (∇ (fun x ↦ φ (x, z.2)) z.1) := by
  obtain ⟨q, hq, _⟩ := exists_minimizer_of_norm_lower_bound hcont hL hg hlower ht z.1
  have hlocal : ∀ᶠ w in 𝓝 z, value L g z.2 z.1 - φ z ≤ value L g w.2 w.1 - φ w :=
    hmin.isLocalMin (isOpen_positiveTimeDomain.mem_nhds ht)
  let γ : ℝ → E × ℝ := fun h ↦ z - h • (q, 1)
  have hγ : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc : ContinuousAt γ (0 : ℝ) :=
      continuousAt_const.sub (continuousAt_id.smul continuousAt_const)
    have hfull : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 z) := by
      simpa only [γ, zero_smul, sub_zero] using hc.tendsto
    exact hfull.mono_left nhdsWithin_le_nhds
  have hquot : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (φ (γ h) - φ z) / h ≤ -L q := by
    filter_upwards [Ioo_mem_nhdsGT ht, hγ.eventually hlocal] with h hh hcontact
    have hstep : value L g (z.2 - h) (z.1 - h • q) ≤ cost L g (z.2 - h) (z.1 - h • q) q :=
      csInf_le (bddBelow_cost_of_norm_lower_bound hL hlower
        (sub_pos.mpr hh.2).le (z.1 - h • q)) ⟨q, rfl⟩
    have hx : (z.1 - h • q) - (z.2 - h) • q = z.1 - z.2 • q := by module
    dsimp only [cost] at hq hstep
    rw [hx] at hstep
    change value L g z.2 z.1 - φ z ≤ value L g (z.2 - h * 1) (z.1 - h • q) - φ (γ h) at hcontact
    simp only [mul_one] at hcontact
    apply (div_le_iff₀ hh.1).mpr
    nlinarith
  have htend := tendsto_backward_slope hdiff (q, (1 : ℝ))
  have hlim : -(fderiv ℝ φ z) (q, 1) ≤ -L q := le_of_tendsto htend hquot
  have hfenchel := le_hamiltonian hL (∇ (fun x ↦ φ (x, z.2)) z.1) q
  rw [test_direction hdiff q] at hlim
  linarith

include hconv in
/-- The Hopf–Lax value solves the Hamilton–Jacobi equation wherever it is
differentiable at positive time. The value itself supplies both contact tests. -/
theorem residual_eq_zero_of_differentiableAt {z : E × ℝ} (ht : 0 < z.2)
    (hdiff : DifferentiableAt ℝ (fun w : E × ℝ ↦ value L g w.2 w.1) z) :
    fderiv ℝ (fun w : E × ℝ ↦ value L g w.2 w.1) z (0, 1) +
      hamiltonian L (∇ (value L g z.2) z.1) = 0 := by
  apply le_antisymm
  · apply residual_le_zero_of_isLocalMaxOn hcont hL hconv hg hlower ht hdiff
    exact Filter.Eventually.of_forall fun w ↦ by simp
  · apply residual_nonneg_of_isLocalMinOn hcont hL hg hlower ht hdiff
    exact Filter.Eventually.of_forall fun w ↦ by simp

end HamiltonJacobi.HopfLax

end
