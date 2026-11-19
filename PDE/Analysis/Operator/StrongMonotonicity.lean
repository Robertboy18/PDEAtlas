/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Strongly monotone Lipschitz operators

Let `A` be a globally Lipschitz self-map of a real Hilbert space. If

`m * ‖x - y‖² ≤ ⟪A x - A y, x - y⟫`

for some `m > 0`, then `A` is bijective. The proof applies Banach's fixed-point
theorem, Mathlib's `ContractingWith.fixedPoint`, to the forward step
`x ↦ x - τ • (A x - b)`, with an explicit positive step size depending on `m` and a
Lipschitz constant for `A`.

The final theorem transfers this result to maps into the strong dual through
the Fréchet–Riesz isometry `InnerProductSpace.toDual`. The global Lipschitz assumption is
stronger than the hypotheses of the Browder–Minty theorem
`surjective_of_monotone_of_hemicontinuous_of_coercive`, and the proof gives an explicit step
size.

## Main results

* `bijective_of_pairing_lower_bound_of_lipschitzWith`: a Lipschitz `A : V → V` on a real
  Hilbert space with `m ‖x - y‖² ≤ ⟪A x - A y, x - y⟫` and `m > 0` is bijective.
* `bijective_dual_of_pairing_lower_bound_of_lipschitzWith`: the same for a Lipschitz
  `A : V → StrongDual ℝ V` with `m ‖x - y‖² ≤ (A x - A y) (x - y)`.
-/

@[expose] public section

namespace PDE.Analysis.Operator

open scoped NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The forward step of a strongly monotone Lipschitz map is Lipschitz with
the constant obtained by expanding its squared Hilbert norm. -/
private theorem lipschitzWith_forward_step_of_pairing_lower_bound
    (A : V → V) (m τ : ℝ) {K q : NNReal}
    (hmono : ∀ x y,
      m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A x - A y, x - y⟫)
    (hA : LipschitzWith K A) (hτ : 0 ≤ τ)
    (hstep :
      1 - 2 * τ * m + τ ^ 2 * (K : ℝ) ^ 2 ≤ (q : ℝ) ^ 2) :
    LipschitzWith q (fun x ↦ x - τ • A x) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  let d : V := x - y
  let e : V := A x - A y
  have he : ‖e‖ ≤ (K : ℝ) * ‖d‖ := by
    simpa only [d, e, dist_eq_norm] using hA.dist_le_mul x y
  have hmono' : m * ‖d‖ * ‖d‖ ≤ ⟪e, d⟫ := by
    simpa only [d, e] using hmono x y
  have he_sq : ‖e‖ ^ 2 ≤ (K : ℝ) ^ 2 * ‖d‖ ^ 2 := by
    have he_nonneg : 0 ≤ ‖e‖ := norm_nonneg e
    have hKd_nonneg : 0 ≤ (K : ℝ) * ‖d‖ :=
      mul_nonneg K.coe_nonneg (norm_nonneg d)
    nlinarith
  have hsq :
      ‖d - τ • e‖ ^ 2 ≤ (q : ℝ) ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ,
      inner_smul_right, real_inner_comm]
    have hstep' := mul_le_mul_of_nonneg_right hstep (sq_nonneg ‖d‖)
    nlinarith
  have hvector :
      (x - τ • A x) - (y - τ • A y) = d - τ • e := by
    dsimp only [d, e]
    module
  rw [hvector]
  have hleft_nonneg : 0 ≤ ‖d - τ • e‖ := norm_nonneg _
  have hright_nonneg : 0 ≤ (q : ℝ) * ‖d‖ :=
    mul_nonneg q.coe_nonneg (norm_nonneg d)
  nlinarith

/-- A globally Lipschitz self-map of a real Hilbert space is bijective when
its inner-product pairing has a positive quadratic lower bound. -/
theorem bijective_of_pairing_lower_bound_of_lipschitzWith
    [CompleteSpace V]
    (A : V → V) (m : ℝ) (hm : 0 < m) {K : NNReal}
    (hmono : ∀ x y,
      m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A x - A y, x - y⟫)
    (hA : LipschitzWith K A) :
    Function.Bijective A := by
  constructor
  · intro x y hxy
    have h := hmono x y
    rw [hxy, sub_self, inner_zero_left] at h
    have hproduct : m * (‖x - y‖ * ‖x - y‖) = 0 := by
      apply le_antisymm
      · simpa only [mul_assoc] using h
      · exact mul_nonneg hm.le (mul_self_nonneg _)
    have hsquare : ‖x - y‖ * ‖x - y‖ = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hm.ne'
    exact sub_eq_zero.mp (norm_eq_zero.mp (mul_self_eq_zero.mp hsquare))
  · intro b
    let D : ℝ := (K : ℝ) ^ 2 + m ^ 2
    have hD : 0 < D := by
      dsimp only [D]
      nlinarith [sq_nonneg (K : ℝ), sq_pos_of_pos hm]
    let τ : ℝ := m / D
    have hτ : 0 < τ := div_pos hm hD
    let r : ℝ := 1 - 2 * τ * m + τ ^ 2 * (K : ℝ) ^ 2
    have hτK : τ * (K : ℝ) ^ 2 < 2 * m := by
      dsimp only [τ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      dsimp only [D]
      nlinarith [sq_nonneg (K : ℝ), sq_pos_of_pos hm]
    have hr : r < 1 := by
      dsimp only [r]
      nlinarith [mul_lt_mul_of_pos_left hτK hτ]
    let q : NNReal := ⟨√(max r 0), Real.sqrt_nonneg _⟩
    have hq : q < 1 := by
      rw [← NNReal.coe_lt_one]
      change √(max r 0) < 1
      rw [Real.sqrt_lt' zero_lt_one]
      simpa only [one_pow] using max_lt hr zero_lt_one
    have hrq : r ≤ (q : ℝ) ^ 2 := by
      change r ≤ √(max r 0) ^ 2
      rw [Real.sq_sqrt (le_max_right r 0)]
      exact le_max_left r 0
    let F : V → V := fun x ↦ x - τ • (A x - b)
    have hshift_mono : ∀ x y,
        m * ‖x - y‖ * ‖x - y‖ ≤
          ⟪(A x - b) - (A y - b), x - y⟫ := by
      intro x y
      simpa only [sub_sub_sub_cancel_right] using hmono x y
    have hshift_lipschitz : LipschitzWith K (fun x ↦ A x - b) := by
      refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hA.dist_le_mul x y
    have hF_lipschitz : LipschitzWith q F := by
      dsimp only [F]
      exact lipschitzWith_forward_step_of_pairing_lower_bound
        (fun x ↦ A x - b) m τ hshift_mono hshift_lipschitz hτ.le hrq
    have hF : ContractingWith q F := ⟨hq, hF_lipschitz⟩
    let z : V := ContractingWith.fixedPoint F hF
    have hz : F z = z := hF.fixedPoint_isFixedPt
    have hsmul : τ • (A z - b) = 0 := by
      dsimp only [F] at hz
      exact sub_eq_self.mp hz
    have hAz : A z = b :=
      sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left hτ.ne')
    exact ⟨z, hAz⟩

/-- A globally Lipschitz map from a real Hilbert space to its strong dual is
bijective when its dual pairing has a positive quadratic lower bound. -/
theorem bijective_dual_of_pairing_lower_bound_of_lipschitzWith
    [CompleteSpace V]
    (A : V → StrongDual ℝ V) (m : ℝ) (hm : 0 < m) {K : NNReal}
    (hmono : ∀ x y,
      m * ‖x - y‖ * ‖x - y‖ ≤ (A x - A y) (x - y))
    (hA : LipschitzWith K A) :
    Function.Bijective A := by
  let toPrimal : StrongDual ℝ V → V :=
    (InnerProductSpace.toDual ℝ V).symm
  let A' : V → V := fun x ↦ toPrimal (A x)
  have hmono' : ∀ x y,
      m * ‖x - y‖ * ‖x - y‖ ≤ ⟪A' x - A' y, x - y⟫ := by
    intro x y
    have hmap : A' x - A' y = toPrimal (A x - A y) := by
      simp only [A', toPrimal, map_sub]
    rw [hmap]
    simpa only [toPrimal, InnerProductSpace.toDual_symm_apply] using hmono x y
  have hA' : LipschitzWith K A' := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hmap : A' x - A' y = toPrimal (A x - A y) := by
      simp only [A', toPrimal, map_sub]
    rw [hmap]
    change ‖(InnerProductSpace.toDual ℝ V).symm (A x - A y)‖ ≤
      (K : ℝ) * ‖x - y‖
    rw [(InnerProductSpace.toDual ℝ V).symm.norm_map]
    simpa only [dist_eq_norm] using hA.dist_le_mul x y
  have hbijective :=
    bijective_of_pairing_lower_bound_of_lipschitzWith A' m hm hmono' hA'
  constructor
  · intro x y hxy
    apply hbijective.1
    exact congrArg toPrimal hxy
  · intro ell
    obtain ⟨x, hx⟩ := hbijective.2 (toPrimal ell)
    refine ⟨x, ?_⟩
    apply (InnerProductSpace.toDual ℝ V).symm.injective
    exact hx

end PDE.Analysis.Operator
