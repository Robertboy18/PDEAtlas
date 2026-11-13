/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.MetricSpace.Lipschitz
import CAS.ExactTactic

/-!
# A quartic energy on an arbitrary Hilbert space

For a vector `e` of a real Hilbert space, `energy e u = ‖u‖² - ⟪e, u⟫⁴` has a negative
quartic term in the direction `e` and is quadratic in the orthogonal directions. It is
smooth, its gradient is `2u - 4⟪e, u⟫³ e` (`gradient_energy`), and for a unit vector `e`
the gradient is Lipschitz on `closedBall 0 R` with constant `2 + 12 R²`
(`lipschitzOnWith_gradient_energy`). All estimates hold in every Hilbert dimension.
-/

@[expose] public noncomputable section

open Metric
open scoped ContDiff RealInnerProductSpace Gradient

namespace PDE.Examples.CriticalPoint.Quartic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A quadratic energy with a negative quartic term in the direction `e`. -/
def energy (e u : H) : ℝ := ‖u‖ ^ 2 - ⟪e, u⟫ ^ 4

omit [CompleteSpace H] in
/-- The energy is smooth in every Hilbert space. -/
theorem contDiff_energy (e : H) {n : ℕ∞ω} : ContDiff ℝ n (energy e) :=
  (contDiff_norm_sq ℝ).sub ((innerSL ℝ e).contDiff.pow 4)

/-- The gradient of the energy at `u` is `2u - 4⟪e, u⟫³ e`. -/
theorem hasGradientAt_energy (e u : H) :
    HasGradientAt (energy e) ((2 : ℝ) • u - (4 * ⟪e, u⟫ ^ 3) • e) u := by
  have hscalar : HasDerivAt (fun s : ℝ ↦ s ^ 4) (4 * ⟪e, u⟫ ^ 3) ⟪e, u⟫ := by
    cas
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (hasStrictFDerivAt_norm_sq u).hasFDerivAt.sub
    (hscalar.comp_hasFDerivAt u (innerSL ℝ e).hasFDerivAt)
  have heq : (InnerProductSpace.toDual ℝ H) ((2 : ℝ) • u - (4 * ⟪e, u⟫ ^ 3) • e) =
      (2 : ℝ) • innerSL ℝ u - (4 * ⟪e, u⟫ ^ 3) • innerSL ℝ e := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
  rw [heq]
  convert! h using 1
  simp [two_smul]

/-- The gradient formula, as an equation for `∇ (energy e)`. -/
theorem gradient_energy (e u : H) :
    ∇ (energy e) u = (2 : ℝ) • u - (4 * ⟪e, u⟫ ^ 3) • e :=
  (hasGradientAt_energy e u).gradient

omit [CompleteSpace H] in
/-- For a unit direction, the scalar coordinate is bounded by the norm. -/
theorem abs_inner_le_norm {e : H} (he : ‖e‖ = 1) (u : H) : |⟪e, u⟫| ≤ ‖u‖ := by
  simpa [he] using abs_real_inner_le_norm e u

/-- On `closedBall 0 R` the gradient is Lipschitz with constant `2 + 12 R²`. -/
theorem lipschitzOnWith_gradient_energy {e : H} (he : ‖e‖ = 1) (R : NNReal) :
    LipschitzOnWith (2 + 12 * R ^ 2) (∇ (energy e)) (closedBall 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [mem_closedBall_zero_iff] at hx hy
  have hs : |⟪e, x⟫| ≤ R := (abs_inner_le_norm he x).trans hx
  have ht : |⟪e, y⟫| ≤ R := (abs_inner_le_norm he y).trans hy
  have hsub : |⟪e, x⟫ - ⟪e, y⟫| ≤ ‖x - y‖ := by
    simpa only [← inner_sub_right] using abs_inner_le_norm he (x - y)
  have hpow : |⟪e, x⟫ ^ 3 - ⟪e, y⟫ ^ 3| ≤ ‖x - y‖ * 3 * (R : ℝ) ^ 2 := by
    calc
      _ ≤ |⟪e, x⟫ - ⟪e, y⟫| * 3 * max |⟪e, x⟫| |⟪e, y⟫| ^ 2 := by
        simpa using (abs_pow_sub_pow_le (a := ⟪e, x⟫) (b := ⟪e, y⟫) (n := 3))
      _ ≤ _ := by gcongr; exact max_le hs ht
  have hdiff :
      ∇ (energy e) x - ∇ (energy e) y =
        (2 : ℝ) • (x - y) - (4 * (⟪e, x⟫ ^ 3 - ⟪e, y⟫ ^ 3)) • e := by
    simp only [gradient_energy, smul_sub, mul_sub, sub_smul]
    abel
  rw [dist_eq_norm, hdiff, dist_eq_norm]
  calc
    _ ≤ ‖(2 : ℝ) • (x - y)‖ + ‖(4 * (⟪e, x⟫ ^ 3 - ⟪e, y⟫ ^ 3)) • e‖ :=
      norm_sub_le _ _
    _ = 2 * ‖x - y‖ + 4 * |⟪e, x⟫ ^ 3 - ⟪e, y⟫ ^ 3| := by
      simp [norm_smul, Real.norm_eq_abs, he]
    _ ≤ (2 + 12 * (R : ℝ) ^ 2) * ‖x - y‖ := by nlinarith [hpow]
    _ = _ := by norm_cast

/-- The gradient is Lipschitz on bounded balls, with one constant for each ball. -/
theorem gradient_energy_lipschitzOn_balls {e : H} (he : ‖e‖ = 1) :
    ∀ R : ℝ, 0 < R →
      ∃ K : NNReal, LipschitzOnWith K (∇ (energy e)) (closedBall 0 R) := by
  intro R hR
  exact ⟨2 + 12 * (⟨R, hR.le⟩ : NNReal) ^ 2, lipschitzOnWith_gradient_energy he ⟨R, hR.le⟩⟩

end PDE.Examples.CriticalPoint.Quartic
