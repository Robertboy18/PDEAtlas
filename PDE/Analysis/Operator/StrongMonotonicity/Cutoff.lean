/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Extending a monotone flux by a cutoff

Blend a locally monotone flux with the positive linear flux `βz`. Monotonicity
is needed only where the cutoff is nonzero. Centering the original flux at zero
makes the spatial cutoff error grow linearly in the state, as required in
localized difference-quotient estimates.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open scoped RealInnerProductSpace

variable {X E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A scalar cutoff blends a flux with a positive scalar multiple of the identity. -/
def cutoffFlux (χ : X → ℝ) (A : X → E → E) (β : ℝ) (x : X) (z : E) : E :=
  χ x • A x z + (1 - χ x) • (β • z)

/-- On the core of the cutoff, the extended flux is exactly the original flux. -/
theorem cutoffFlux_eq_of_eq_one (χ : X → ℝ) (A : X → E → E) (β : ℝ)
    {x : X} (hx : χ x = 1) (z : E) :
    cutoffFlux χ A β x z = A x z := by
  simp only [cutoffFlux, hx, one_smul, sub_self, zero_smul, add_zero]

/-- A centered flux remains centered under the extension. -/
theorem cutoffFlux_zero (χ : X → ℝ) (A : X → E → E) (β : ℝ)
    {x : X} (hA : A x 0 = 0) : cutoffFlux χ A β x 0 = 0 := by
  simp only [cutoffFlux, hA, smul_zero, add_zero]

/-- Convex blending preserves a common monotonicity constant. The original
flux need only be monotone where its weight is nonzero. -/
theorem cutoffFlux_pairing_lower_bound
    (χ : X → ℝ) (A : X → E → E) {β m : ℝ} {x : X}
    (hχ : 0 ≤ χ x) (hχone : χ x ≤ 1) (hβ : m ≤ β)
    (hmono : χ x ≠ 0 → ∀ z w : E,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (z w : E) :
    m * ‖z - w‖ * ‖z - w‖ ≤
      ⟪cutoffFlux χ A β x z - cutoffFlux χ A β x w, z - w⟫ := by
  have heq : cutoffFlux χ A β x z - cutoffFlux χ A β x w =
      χ x • (A x z - A x w) + ((1 - χ x) * β) • (z - w) := by
    simp only [cutoffFlux, smul_sub, mul_smul]
    abel
  rw [heq, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  have hβsq := mul_le_mul_of_nonneg_right hβ (sq_nonneg ‖z - w‖)
  by_cases hx : χ x = 0
  · simp only [hx, zero_mul, sub_zero, one_mul, zero_add]
    nlinarith only [hβsq]
  · have h1 := mul_le_mul_of_nonneg_left (hmono hx z w) hχ
    have h2 := mul_le_mul_of_nonneg_left hβsq (sub_nonneg.mpr hχone)
    nlinarith only [h1, h2]

/-- The state Lipschitz estimate survives the cutoff, with a harmless uniform
constant independent of the state and the point. -/
theorem norm_cutoffFlux_state_sub_le
    (χ : X → ℝ) (A : X → E → E) (β : ℝ) {C : ℝ} {x : X}
    (hχ : 0 ≤ χ x) (hχone : χ x ≤ 1) (hC : 0 ≤ C)
    (hA : ∀ z w : E, ‖A x z - A x w‖ ≤ C * ‖z - w‖) (z w : E) :
    ‖cutoffFlux χ A β x w - cutoffFlux χ A β x z‖ ≤
      (C + |β|) * ‖w - z‖ := by
  have heq : cutoffFlux χ A β x w - cutoffFlux χ A β x z =
      χ x • (A x w - A x z) + ((1 - χ x) * β) • (w - z) := by
    simp only [cutoffFlux, smul_sub, mul_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖χ x • (A x w - A x z)‖ + ‖((1 - χ x) * β) • (w - z)‖ :=
      norm_add_le _ _
    _ = χ x * ‖A x w - A x z‖ + (1 - χ x) * |β| * ‖w - z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hχ, abs_of_nonneg (sub_nonneg.mpr hχone)]
    _ ≤ χ x * (C * ‖w - z‖) + (1 - χ x) * |β| * ‖w - z‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (hA w z) hχ) le_rfl
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right hχone (mul_nonneg hC (norm_nonneg (w - z)))
      have h2 := mul_le_mul_of_nonneg_right (show 1 - χ x ≤ 1 by linarith)
        (mul_nonneg (abs_nonneg β) (norm_nonneg (w - z)))
      nlinarith only [h1, h2]

variable [NormedAddCommGroup X]

/-- The spatial error introduced by the cutoff is linear in the state norm.
Only the coefficient and cutoff estimates enter its constant. -/
theorem norm_cutoffFlux_spatial_sub_le
    (χ : X → ℝ) (A : X → E → E) (β : ℝ) {K C D : ℝ} {x y : X}
    (hχy : |χ y| ≤ 1) (hχdiff : |χ y - χ x| ≤ D * ‖y - x‖)
    (hD : 0 ≤ D) (hzero : A x 0 = 0)
    (hstate : ∀ z w : E, ‖A x z - A x w‖ ≤ C * ‖z - w‖)
    (hspace : ∀ z : E, ‖A y z - A x z‖ ≤ K * ‖y - x‖ * ‖z‖)
    (z : E) :
    ‖cutoffFlux χ A β y z - cutoffFlux χ A β x z‖ ≤
      (K + D * (C + |β|)) * ‖y - x‖ * ‖z‖ := by
  have hgrowth : ‖A x z - β • z‖ ≤ (C + |β|) * ‖z‖ := by
    have ha : ‖A x z‖ ≤ C * ‖z‖ := by
      simpa only [hzero, sub_zero] using hstate z 0
    calc
      _ ≤ ‖A x z‖ + ‖β • z‖ := norm_sub_le _ _
      _ ≤ C * ‖z‖ + |β| * ‖z‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using add_le_add ha (le_refl ‖β • z‖)
      _ = _ := by ring
  have heq : cutoffFlux χ A β y z - cutoffFlux χ A β x z =
      χ y • (A y z - A x z) + (χ y - χ x) • (A x z - β • z) := by
    simp only [cutoffFlux, smul_sub, sub_smul, one_smul]
    abel
  calc
    _ ≤ |χ y| * ‖A y z - A x z‖ + |χ y - χ x| * ‖A x z - β • z‖ := by
      rw [heq]
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        (χ y • (A y z - A x z)) ((χ y - χ x) • (A x z - β • z))
    _ ≤ ‖A y z - A x z‖ + (D * ‖y - x‖) * ((C + |β|) * ‖z‖) := by
      apply add_le_add
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hχy (norm_nonneg _)
      · exact mul_le_mul hχdiff hgrowth (norm_nonneg _) (mul_nonneg hD (norm_nonneg _))
    _ ≤ K * ‖y - x‖ * ‖z‖ + (D * ‖y - x‖) * ((C + |β|) * ‖z‖) :=
      add_le_add (hspace z) le_rfl
    _ = _ := by ring

end PDE.Analysis.Operator
