/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Normalize
public import PDE.Analysis.Calculus.LocalExtension
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Differentiating vector normalization

Normalization is smooth away from zero. On the unit sphere its derivative
removes the component parallel to the original vector, leaving a tangent
vector. These formulas use Mathlib's `NormedSpace.normalize`.

An annular cutoff gives a smooth compactly supported map that agrees with
normalization near the unit sphere. Its derivative is bounded, so it can be
composed with Sobolev maps taking values near the sphere.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology InnerProductSpace

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Vector normalization is smooth at every nonzero vector. -/
theorem contDiffAt_normalize {k : WithTop ℕ∞} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ k (normalize : E → E) x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

/-- Vector normalization is smooth on the complement of the origin. -/
theorem contDiffOn_normalize {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (normalize : E → E) ({0}ᶜ : Set E) :=
  fun _ hx ↦ (contDiffAt_normalize hx).contDiffWithinAt

/-- The derivative of normalization consists of a rescaling followed by removal
of the component in the radial direction. -/
theorem hasFDerivAt_normalize {x : E} (hx : x ≠ 0) :
    HasFDerivAt (normalize : E → E)
      (‖x‖⁻¹ • ContinuousLinearMap.id ℝ E -
        (‖x‖⁻¹) ^ 3 • (innerSL ℝ x).smulRight x) x := by
  have hn : HasFDerivAt (norm : E → ℝ) (‖x‖⁻¹ • innerSL ℝ x) x := by
    convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) using 1
    · ext y
      exact (Real.sqrt_sq (norm_nonneg y)).symm
    · ext y
      simp [Real.sqrt_sq (norm_nonneg x)]
      field_simp
  convert ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn).smul
    (hasFDerivAt_id x) using 1
  · rfl
  · ext y
    simp [smul_smul, sub_eq_add_neg, pow_succ, mul_assoc]

/-- At a unit vector, the derivative of normalization is the orthogonal
projection onto its tangent space. -/
theorem fderiv_normalize_apply_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) (v : E) :
    fderiv ℝ (normalize : E → E) x v = v - ⟪x, v⟫_ℝ • x := by
  have hne : x ≠ 0 := by
    intro h
    simp [h] at hx
  rw [(hasFDerivAt_normalize hne).fderiv]
  simp [hx]

/-- A smooth compactly supported map agrees with normalization on any prescribed
annulus and has a globally bounded derivative. Finite dimension is used only
for the cutoff and compactness. -/
theorem exists_contDiff_compactSupport_eqOn_normalize
    [FiniteDimensional ℝ E] {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ G : E → E, ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧
      (∀ z, a ≤ ‖z‖ → ‖z‖ ≤ b → G z = normalize z) ∧
      ∃ C : ℝ, ∀ z, ‖fderiv ℝ G z‖ ≤ C := by
  obtain ⟨G, hG, hcompact, heq⟩ :=
    (contDiffOn_normalize (E := E) (k := (⊤ : ℕ∞))).exists_contDiff_compactSupport_eqOn_annulus
      ha hb
  exact ⟨G, hG, hcompact, heq,
    (hcompact.fderiv ℝ).exists_bound_of_continuous (hG.continuous_fderiv (by simp))⟩

end NormedSpace
