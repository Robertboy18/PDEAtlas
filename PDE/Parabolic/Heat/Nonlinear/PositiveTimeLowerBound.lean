/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.QuadraticLowerBound

/-!
# The quadratic heat lower bound away from an omitted initial corner

Positive-time translation gives a closed regular strip without any hypothesis
at time zero. Applying the strip maximum principle and letting the translation
tend to zero proves `t * u(t,x) ≥ -1` for a global signed candidate.

The bound uses only the PDE and the lateral values, and it is singular at `t = 0`.
-/

@[expose] public noncomputable section

open Filter Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ}

/-- A positive-time translate has continuous values on every closed finite strip,
although the original candidate need not have a value at the initial corner. -/
theorem isInteriorDirichletSquareSolution_shift_of_positive_time
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    {a T : ℝ} (ha : 0 < a) :
    IsInteriorDirichletSquareSolution Ω T (u a) (fun t x ↦ u (a + t) x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hc.comp ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ ⟨by change 0 < a + q.1; linarith [hq.1.1], hq.2⟩)
  · exact hs.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q hq ↦ ⟨by change 0 < a + q.1; linarith [hq.1.1], hq.2⟩)
  · intro t ht x hx
    rw [deriv_comp_const_add (fun r ↦ u r x) a t]
    exact heq (a + t) (by linarith [ht.1]) x hx
  · intro x hx t ht
    exact hboundary x hx (a + t) (by linarith [ht.1])
  · intro x _
    simp

/-- The quadratic reaction bounds the negative part of a global classical
Dirichlet solution by `1 / t`. No initial value, sign, or corner bound is assumed. -/
theorem neg_one_le_time_mul_of_global_dirichlet_square_solution
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    {t : ℝ} (ht : 0 < t) {x : ℝ^n} (hx : x ∈ closure Ω) :
    -1 ≤ t * u t x := by
  let a : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have halim : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k ↦ (t - a k) * u t x) atTop (𝓝 (t * u t x)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub halim).mul_const (u t x)
  apply ge_of_tendsto hlim
  filter_upwards [halim.eventually (gt_mem_nhds ht)] with k hk
  have hu := isInteriorDirichletSquareSolution_shift_of_positive_time
    hc hs heq hboundary (T := t + 1) (ha k)
  have h := hu.neg_one_le_time_mul hΩ hne hb (sub_pos.mpr hk)
    (by linarith [ha k]) (t - a k) ⟨(sub_pos.mpr hk).le, le_rfl⟩ x hx
  simpa only [add_comm (a k), sub_add_cancel] using h

end HeatEquation.Nonlinear
