/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.PotentialLimit

/-!
# Coupled quadratic and potential energy under limits

Weak convergence passes a nonnegative quadratic energy to the limit together
with an almost-everywhere convergent nonnegative potential density. Fatou's
lemma proves the potential integrable and retains the combined energy budget,
rather than bounding its two terms independently.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- A common total-energy budget survives simultaneous weak convergence of
quadratic variables and almost-everywhere convergence of nonnegative potential
densities. Finiteness of the limiting potential integral is a conclusion. -/
theorem quadratic_add_integral_le_of_weak_ae_limit
    {H α : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace α]
    {μ : Measure α} (B : H →L[ℝ] StrongDual ℝ H)
    (hsym : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x)
    {u : ℕ → H} {v : H}
    (hweak : ∀ ell : StrongDual ℝ H,
      Tendsto (fun i ↦ ell (u i)) atTop (𝓝 (ell v)))
    {F : ℕ → α → ℝ} {G : α → ℝ} {C : ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hFpos : ∀ i, ∀ᵐ x ∂μ, 0 ≤ F i x)
    (hb : ∀ i, B (u i) (u i) + (∫ x, F i x ∂μ) ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) atTop (𝓝 (G x))) :
    Integrable G μ ∧ B v v + (∫ x, G x ∂μ) ≤ C := by
  have hbudget (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ i in atTop, (∫ x, F i x ∂μ) ≤ C - B v v + ε := by
    have hp := ((hweak (B v)).const_mul 2).eventually (lt_mem_nhds (sub_lt_self (2 * B v v) hε))
    filter_upwards [hp] with i hi
    have hdiff := hpos (u i - v)
    simp only [map_sub, sub_apply, hsym (u i) v] at hdiff
    have he := hb i
    linarith
  have hG := integrable_and_integral_le_of_nonnegative_limit hF hFpos (hbudget 1 zero_lt_one) hlim
  refine ⟨hG.1, ?_⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have h := (integrable_and_integral_le_of_nonnegative_limit hF hFpos (hbudget ε hε) hlim).2
  linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
