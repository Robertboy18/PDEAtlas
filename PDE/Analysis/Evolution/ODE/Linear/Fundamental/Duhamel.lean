/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental

/-!
# Duhamel's formula for time-dependent bounded operators

For a fundamental solution `Φ, Ψ` of `B : ℝ → E →L[ℝ] E` on a Banach space `E`, the
variation-of-constants solution `u(t) = Φ(t) (Ψ(s) x + ∫ₛᵗ Ψ(r) f(r) dr)` has
`u(s) = x`, solves `u' = B(t) u + f(t)` for continuous `f`, and equals
`U(t, s) x + ∫ₛᵗ U(t, r) f(r) dr`. Conversely, the fundamental theorem of calculus
applied to `Ψ u` identifies every classical trajectory with this formula.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution.FundamentalSolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : ℝ → E →L[ℝ] E} {t₀ : ℝ} {times : Set ℝ}
  (S : FundamentalSolution B t₀ times)

/-- Variation of constants through data `x` at time `s`. -/
def solution (f : ℝ → E) (s : ℝ) (x : E) (t : ℝ) : E :=
  S.forward t (S.backward s x + ∫ r in s..t, S.backward r (f r))

/-- Variation of constants takes the prescribed data at every starting time in the domain. -/
theorem solution_initial_of_mem (f : ℝ → E) {s : ℝ} (hs : s ∈ times) (x : E) :
    S.solution f s x s = x := by
  simp only [solution, intervalIntegral.integral_same, add_zero,
    ← mul_apply_eq_comp, S.forward_mul_backward s hs]
  rfl

variable (S : FundamentalSolution B t₀)

/-- The whole-line variation-of-constants solution takes the prescribed initial value. -/
@[simp] theorem solution_initial (f : ℝ → E) (s : ℝ) (x : E) :
    S.solution f s x s = x :=
  S.solution_initial_of_mem f (mem_univ s) x

variable [CompleteSpace E]

/-- The constructed solution solves the forced equation at every time. -/
theorem hasDerivAt_solution {f : ℝ → E} (hf : Continuous f) (s : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (S.solution f s x) (B t (S.solution f s x t) + f t) t := by
  have hq : Continuous (fun r ↦ S.backward r (f r)) := S.continuous_backward.clm_apply hf
  have hprim := (intervalIntegral.integral_hasDerivAt_right
    (hq.intervalIntegrable s t) hq.aestronglyMeasurable.stronglyMeasurableAtFilter
    hq.continuousAt).const_add (S.backward s x)
  convert! (S.forward_derivative t).clm_apply hprim using 1
  simp only [solution, mul_apply_eq_comp,
    ← mul_apply_eq_comp (S.forward t) (S.backward t),
    S.forward_backward]
  rfl

omit [CompleteSpace E] in
/-- Duhamel's formula using the two-time propagator of the same coefficient. The forward
operator is invertible, so it commutes with every Bochner integral: neither continuity of `f`
nor completeness of `E` is needed. -/
theorem solution_eq_propagator_add_integral {f : ℝ → E}
    (s : ℝ) (x : E) (t : ℝ) :
    S.solution f s x t =
      S.propagator t s x + ∫ r in s..t, S.propagator t r (f r) := by
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse' (S.forward t) (S.backward t)
    (S.forward_backward t) (S.backward_forward t)
  have hL : S.forward t (∫ r in s..t, S.backward r (f r)) =
      ∫ r in s..t, S.forward t (S.backward r (f r)) := by
    change L _ = ∫ r in s..t, L (S.backward r (f r))
    simp only [intervalIntegral, map_sub, L.integral_comp_comm]
  simp only [solution, propagator, mul_apply_eq_comp, map_add]
  rw [hL]

/-- If `[a, b]` lies in the domain of `S`, `u` and `f` are continuous on `[a, b]` and
`u' = B(t) u + f(t)` on `(a, b)`, then `u(b)` is the variation-of-constants solution
from `(a, u(a))` evaluated at `b`. -/
theorem eq_solution_of_hasDerivWithinAt_of_subset
    (S : FundamentalSolution B t₀ times) {u f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (htimes : Icc a b ⊆ times)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt u (B t (u t) + f t) (Icc a b) t) :
    u b = S.solution f a (u a) b := by
  have hq : ContinuousOn (fun r ↦ S.backward r (f r)) (Icc a b) :=
    (S.continuousOn_backward.mono htimes).clm_apply hf
  have hv : ContinuousOn (fun r ↦ S.backward r (u r)) (Icc a b) :=
    (S.continuousOn_backward.mono htimes).clm_apply hu
  have hvd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun r ↦ S.backward r (u r)) (S.backward t (f t)) t := by
    have hud := (hd t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hbd := ((S.backward_hasDerivWithinAt t
      (htimes ⟨ht.1.le, ht.2.le⟩)).mono htimes).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    convert! hbd.clm_apply hud using 1
    simp only [neg_apply, mul_apply_eq_comp, map_add, neg_add_cancel_left]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hv hvd
    (hq.intervalIntegrable_of_Icc hab)
  calc
    u b = S.forward b (S.backward b (u b)) := by
      rw [← mul_apply_eq_comp, S.forward_mul_backward b (htimes ⟨hab, le_rfl⟩)]
      rfl
    _ = S.solution f a (u a) b := by
      rw [solution, hint]
      congr 1
      abel

/-- `eq_solution_of_hasDerivWithinAt_of_subset` for a whole-line fundamental solution. -/
theorem eq_solution_of_hasDerivWithinAt {u f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt u (B t (u t) + f t) (Icc a b) t) :
    u b = S.solution f a (u a) b :=
  S.eq_solution_of_hasDerivWithinAt_of_subset hab (subset_univ _) hu hf hd

end PDE.Analysis.Evolution.FundamentalSolution
