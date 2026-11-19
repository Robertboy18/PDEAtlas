/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Calculus.Normalization
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Energy of a normalized variation

The derivative of normalization projects away the radial component. Its
squared norm therefore has a formula involving only squared norms and inner
products. That formula makes the first variation of the Dirichlet energy a
scalar quotient calculation, including when the original tangent vector is
zero.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology InnerProductSpace

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared norm of the derivative of normalization is the rescaled
squared length of the tangential component. -/
theorem norm_fderiv_normalize_apply_sq {x : E} (hx : x ≠ 0) (a : E) :
    ‖fderiv ℝ (normalize : E → E) x a‖ ^ 2 =
      ‖a‖ ^ 2 / ‖x‖ ^ 2 - ⟪x, a⟫_ℝ ^ 2 / ‖x‖ ^ 4 := by
  rw [(hasFDerivAt_normalize hx).fderiv]
  change ‖‖x‖⁻¹ • a - (‖x‖⁻¹) ^ 3 • (⟪x, a⟫_ℝ • x)‖ ^ 2 = _
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm a x]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

/-- At a unit vector, a normalized variation has the usual Dirichlet
first-variation density. The vector `a` is tangent; the perturbations `v` and
`b` are arbitrary. -/
theorem hasDerivAt_normalized_energy {u : E} (hu : ‖u‖ = 1)
    (v a b : E) (ha : ⟪u, a⟫_ℝ = 0) :
    HasDerivAt
      (fun t : ℝ ↦ ‖fderiv ℝ (normalize : E → E) (u + t • v) (a + t • b)‖ ^ 2 / 2)
      (⟪a, b⟫_ℝ - ‖a‖ ^ 2 * ⟪u, v⟫_ℝ) 0 := by
  let z : ℝ → E := fun t ↦ u + t • v
  let q : ℝ → E := fun t ↦ a + t • b
  have hz : HasDerivAt z v 0 := by
    simpa [z] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hq : HasDerivAt q b 0 := by
    simpa [q] using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  have hz0 : ‖z 0‖ ^ 2 ≠ 0 := by simp [z, hu]
  have hquot := ((hq.norm_sq.div hz.norm_sq hz0).sub
    (((hz.inner ℝ hq).pow 2).div (hz.norm_sq.pow 2) (pow_ne_zero 2 hz0))).div_const 2
  have hscalar : HasDerivAt
      (fun t ↦ (‖q t‖ ^ 2 / ‖z t‖ ^ 2 -
        ⟪z t, q t⟫_ℝ ^ 2 / (‖z t‖ ^ 2) ^ 2) / 2)
      (⟪a, b⟫_ℝ - ‖a‖ ^ 2 * ⟪u, v⟫_ℝ) 0 := by
    convert hquot using 1
    simp [z, q, hu, ha]
    ring
  have hne : z 0 ≠ 0 := by
    intro h
    have hnorm := congrArg norm h
    simp [z, hu] at hnorm
  have hnear : ∀ᶠ t in 𝓝 0, z t ≠ 0 :=
    hz.continuousAt.eventually (isOpen_ne.mem_nhds hne)
  apply hscalar.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  dsimp only [z, q]
  rw [norm_fderiv_normalize_apply_sq ht]
  ring

end NormedSpace
