/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.LowerOrderForm

/-!
# The dual norm as a minimum over generalized loads

For the full `H¹₀(Ω)` norm, Evans, Section 5.9.1, Theorem 1 identifies the
dual norm with the infimum of

`sqrt (‖f₀‖² + ∑ᵢ ‖fᵢ‖²)`

over all representations `ell = f₀ - div f`. The coefficients are independent
`L²(Ω)` functions. Pairing their tuple with the base and gradient of a test
function gives the sharp bound by Cauchy–Schwarz in the ambient Hilbert product.
The norm-preserving representation from `exists_generalizedLoad_representation`
attains this bound, so the infimum is a minimum.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open scoped InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω
local notation "Ambient" => WkpAmbientOn n 1 2 Ω

/-- Every coefficient tuple bounds the dual norm by its Hilbert product norm.
The test space carries the full `H¹` norm, including the zeroth-order term. -/
theorem norm_generalizedLoad_le_sqrt (f0 : L2) (f : Fin n → L2) :
    ‖generalizedLoad (n := n) (Ω := Ω) f0 f‖ ≤
      Real.sqrt (‖f0‖ ^ 2 + ∑ i : Fin n, ‖f i‖ ^ 2) := by
  let F : Ambient := WithLp.toLp 2 (firstOrderRows f0 f)
  have hF_sq : ‖F‖ ^ 2 = ‖f0‖ ^ 2 + ∑ i : Fin n, ‖f i‖ ^ 2 := by
    simpa only [F, PiLp.toLp_apply, firstOrderRows_baseIndex,
      firstOrderRows_singleDerivIndex] using
      ambient_norm_sq_eq_base_sq_add_sum_deriv_sq F
  have hF : ‖F‖ = Real.sqrt (‖f0‖ ^ 2 + ∑ i : Fin n, ‖f i‖ ^ 2) := by
    rw [← hF_sq, Real.sqrt_sq (norm_nonneg F)]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  let vAmbient : Ambient := ((h10SubtypeL (n := n) (Ω := Ω) v : H¹(Ω)) : Ambient)
  have hpair : generalizedLoad (n := n) (Ω := Ω) f0 f v =
      inner ℝ F vAmbient := by
    rw [generalizedLoad_apply, ambient_inner_eq_base_add_sum_deriv]
    simp only [F, firstOrderRows_baseIndex, firstOrderRows_singleDerivIndex]
    rfl
  calc
    ‖generalizedLoad (n := n) (Ω := Ω) f0 f v‖ = ‖inner ℝ F vAmbient‖ :=
      congrArg norm hpair
    _ ≤ ‖F‖ * ‖vAmbient‖ := norm_inner_le_norm _ _
    _ = Real.sqrt (‖f0‖ ^ 2 + ∑ i : Fin n, ‖f i‖ ^ 2) * ‖v‖ := by
      rw [hF]
      rfl

/-- Among all `L²` representations of a functional, the dual norm is an attained
minimum of the square-summed coefficient norms. No optimality is assumed of the
coefficients: attainment comes from the norm-preserving representation theorem. -/
theorem isLeast_generalizedLoad_representation_norm (ell : StrongDual ℝ H¹₀(Ω)) :
    IsLeast {r : ℝ | ∃ (f0 : L2) (f : Fin n → L2),
      generalizedLoad (n := n) (Ω := Ω) f0 f = ell ∧
        Real.sqrt (‖f0‖ ^ 2 + ∑ i : Fin n, ‖f i‖ ^ 2) = r} ‖ell‖ := by
  constructor
  · obtain ⟨f0, f, hrep, hnorm⟩ := exists_generalizedLoad_representation ell
    refine ⟨f0, f, hrep, ?_⟩
    rw [hnorm, Real.sqrt_sq (norm_nonneg ell)]
  · rintro r ⟨f0, f, hrep, rfl⟩
    rw [← hrep]
    exact norm_generalizedLoad_le_sqrt f0 f

/-- Evans' infimum formula for the norm in the dual of `H¹₀(Ω)`. The set of
representing coefficient norms is nonempty and contains its infimum. -/
theorem norm_eq_sInf_generalizedLoad_representation (ell : StrongDual ℝ H¹₀(Ω)) :
    ‖ell‖ = sInf {r : ℝ | ∃ (f0 : L2) (f : Fin n → L2),
      generalizedLoad (n := n) (Ω := Ω) f0 f = ell ∧
        Real.sqrt (‖f0‖ ^ 2 + ∑ i : Fin n, ‖f i‖ ^ 2) = r} :=
  (isLeast_generalizedLoad_representation_norm ell).csInf_eq.symm

end SobolevSpace.GraphSpace
