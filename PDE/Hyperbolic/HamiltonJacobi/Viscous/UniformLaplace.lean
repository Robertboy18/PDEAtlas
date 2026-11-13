/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscous.LaplaceBounds

/-!
# A Laplace limit uniform over bounded equicontinuous data

The Gaussian estimates use only a common bound and a common continuity modulus.
First choose the tilt and the ball radius to control the spatial errors. Their
Gaussian constants are then fixed, so their logarithms disappear after
multiplication by the viscosity.

In `Viscous.VanishingViscosity`, translated and dilated copies of one datum
use this uniformity to give convergence on an entire finite time slab.
-/

@[expose] public section

namespace HamiltonJacobi.ColeHopf

open MeasureTheory Set Metric Filter
open scoped Topology

variable {n : ℕ}

/-- For a uniformly bounded, uniformly equicontinuous family of data, the
Cole–Hopf potentials at time one converge uniformly in both the datum and the spatial point
to their quadratic Hopf–Lax values. No topology on the family index is needed. -/
theorem tendstoUniformly_initialValueSolution_one {A : Type*} {g : A → ℝ^n → ℝ}
    (hg : UniformEquicontinuous g) {M : ℝ} (hM : 0 ≤ M) (hgb : ∀ a y, |g a y| ≤ M) :
    TendstoUniformly (fun ν (z : A × ℝ^n) ↦ initialValueSolution ν (g z.1) z.2 1)
      (fun z ↦ HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) (g z.1) 1 z.2) (𝓝[>] (0 : ℝ)) := by
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  have hMone : 0 < M + 1 := by positivity
  let θ := min 1 (ε / (8 * (M + 1))) / 2
  have hθ : 0 < θ := half_pos (lt_min zero_lt_one (div_pos hε (by positivity)))
  have hθone : θ ≤ 1 := by
    have hm := min_le_left (1 : ℝ) (ε / (8 * (M + 1)))
    dsimp only [θ]
    linarith only [hm]
  have hθsmall : θ < ε / (8 * (M + 1)) :=
    (half_lt_self (lt_min zero_lt_one (div_pos hε (by positivity)))).trans_le (min_le_right _ _)
  have htilt : 2 * M * θ < ε / 4 := by
    have hh := (lt_div_iff₀ (show 0 < 8 * (M + 1) by positivity)).mp hθsmall
    nlinarith only [hh, hθ]
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformEquicontinuous_iff.mp hg
    (ε / 4) (by positivity)
  let K := 2 * Real.sqrt M + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  let r := min δ (min 1 (ε / (4 * K))) / 2
  have hr : 0 < r := half_pos
    (lt_min hδ (lt_min zero_lt_one (div_pos hε (by positivity))))
  have hrδ : r < δ := (half_lt_self
    (lt_min hδ (lt_min zero_lt_one (div_pos hε (by positivity))))).trans_le (min_le_left _ _)
  have hrhalf : r < min 1 (ε / (4 * K)) := (half_lt_self
    (lt_min hδ (lt_min zero_lt_one (div_pos hε (by positivity))))).trans_le (min_le_right _ _)
  have hrone : r < 1 := hrhalf.trans_le (min_le_left _ _)
  have hrsmall : r < ε / (4 * K) := hrhalf.trans_le (min_le_right _ _)
  have hball : 2 * Real.sqrt M * r + r ^ 2 / 2 < ε / 4 := by
    have hh := (lt_div_iff₀ (show 0 < 4 * K by positivity)).mp hrsmall
    have hsq : r ^ 2 ≤ r := by nlinarith only [hr, hrone]
    dsimp only [K] at hh
    nlinarith only [hh, hsq, hr]
  let a := |Real.log (θ ^ (-(n : ℝ) / 2))|
  let b := |Real.log (∫ y in ball (0 : ℝ^n) r, HeatEquation.fundamentalSolutionHeat y 1)|
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hab : 0 < a + b + 1 := by positivity
  have hbound : 0 < min 1 (ε / (8 * (a + b + 1))) :=
    lt_min zero_lt_one (div_pos hε (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hbound] with ν hν
  have hνone : ν ≤ 1 := (hν.2.trans_le (min_le_left _ _)).le
  have hνsmall : ν < ε / (8 * (a + b + 1)) := hν.2.trans_le (min_le_right _ _)
  have hlogs : 2 * ν * (a + b + 1) < ε / 4 := by
    have hh := (lt_div_iff₀ (show 0 < 8 * (a + b + 1) by positivity)).mp hνsmall
    linarith only [hh]
  have haerr : 2 * ν * a < ε / 4 :=
    (mul_le_mul_of_nonneg_left (show a ≤ a + b + 1 by linarith only [hb])
      (mul_nonneg (by positivity) hν.1.le)).trans_lt hlogs
  have hberr : 2 * ν * b < ε / 4 :=
    (mul_le_mul_of_nonneg_left (show b ≤ a + b + 1 by linarith only [ha])
      (mul_nonneg (by positivity) hν.1.le)).trans_lt hlogs
  intro z
  have hcont := (hg.uniformContinuous z.1).continuous
  have hlower := quadratic_value_sub_le_initialValueSolution_one hν.1 hθ hθone hcont (hgb z.1) z.2
  have hmod : ∀ y w, ‖y - w‖ < r → |g z.1 y - g z.1 w| ≤ ε / 4 := by
    intro y w hyw
    have hh := hclose y w (show dist y w < δ by
      simpa only [dist_eq_norm] using hyw.trans hrδ) z.1
    simpa only [Real.dist_eq] using hh.le
  have hupper := initialValueSolution_one_le_quadratic_value_add hν.1 hνone hr
    hcont (hgb z.1) hmod z.2
  change HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) (g z.1) 1 z.2 -
    2 * M * θ - 2 * ν * a ≤ initialValueSolution ν (g z.1) z.2 1 at hlower
  change initialValueSolution ν (g z.1) z.2 1 ≤
    HopfLax.value (fun q : ℝ^n ↦ ‖q‖ ^ 2 / 2) (g z.1) 1 z.2 +
      ε / 4 + 2 * Real.sqrt M * r + r ^ 2 / 2 + 2 * ν * b at hupper
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith only [hlower, hupper, htilt, hball, haerr, hberr, hε]

end HamiltonJacobi.ColeHopf
