/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.Separation
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Quadratic perturbations of signed extended energies

The proximal energy retains `+∞` outside the finite domain and permits negative finite values.
An affine minorant, obtained by separation, makes every real sublevel of a positive quadratic
perturbation bounded. This provides the compactness input without assuming coercivity of the
original energy.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The quadratic penalty at a positive proximal parameter. -/
def quadraticPenalty (lambda : ℝ) (w u : H) : ℝ := ‖u - w‖ ^ 2 / (2 * lambda)

/-- The signed extended energy minimized by the proximal map. -/
def proximalEnergy (I : H → EReal) (lambda : ℝ) (w u : H) : EReal :=
  I u + (quadraticPenalty lambda w u : EReal)

omit [NormedSpace ℝ H] in
/-- The quadratic penalty is continuous in the space variable for every fixed parameter. -/
theorem continuous_quadraticPenalty (lambda : ℝ) (w : H) :
    Continuous (quadraticPenalty lambda w) := by
  unfold quadraticPenalty
  fun_prop

/-- The quadratic penalty is convex for a nonnegative parameter. -/
theorem convexOn_quadraticPenalty {lambda : ℝ} (hlambda : 0 ≤ lambda) (w : H) :
    ConvexOn ℝ Set.univ (quadraticPenalty lambda w) := by
  have hs := (convexOn_univ_dist w).pow (fun _ _ ↦ dist_nonneg) 2
  have hm := hs.smul (c := (2 * lambda)⁻¹) (by positivity)
  unfold quadraticPenalty
  simpa only [Pi.pow_apply, dist_eq_norm, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using hm

omit [NormedSpace ℝ H] in
/-- Properness is preserved by the finite quadratic penalty. -/
theorem isProper_proximalEnergy {I : H → EReal} (hI : IsProper I) (lambda : ℝ) (w : H) :
    IsProper (proximalEnergy I lambda w) :=
  hI.add_real (quadraticPenalty lambda w)

/-- Convexity of the signed extended proximal energy. -/
theorem convex_realEpigraph_proximalEnergy {I : H → EReal} (hI : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) {lambda : ℝ} (hlambda : 0 ≤ lambda) (w : H) :
    Convex ℝ (realEpigraph (proximalEnergy I lambda w)) :=
  convex_realEpigraph_add_real hI.1 hconvex (convexOn_quadraticPenalty hlambda w)

omit [NormedSpace ℝ H] in
/-- Lower semicontinuity of the signed extended proximal energy. -/
theorem lowerSemicontinuous_proximalEnergy {I : H → EReal} (hI : LowerSemicontinuous I)
    (lambda : ℝ) (w : H) : LowerSemicontinuous (proximalEnergy I lambda w) :=
  lowerSemicontinuous_add_real hI (continuous_quadraticPenalty lambda w)

/-- An affine lower bound makes every real proximal sublevel bounded. -/
theorem isBounded_proximal_sublevel_of_affine_minorant {I : H → EReal}
    (L : H →L[ℝ] ℝ) (b : ℝ) (hminorant : ∀ u, ((L u + b : ℝ) : EReal) ≤ I u)
    {lambda : ℝ} (hlambda : 0 < lambda) (w : H) (r : ℝ) :
    Bornology.IsBounded {u | proximalEnergy I lambda w u ≤ (r : EReal)} := by
  let D := r - b - L w
  let B := 4 * lambda * |D| + 4 * lambda ^ 2 * ‖L‖ ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply isBounded_iff_forall_norm_le.2
  refine ⟨B + 1 + ‖w‖, fun u hu ↦ ?_⟩
  have hreal : L u + b + quadraticPenalty lambda w u ≤ r := by
    apply EReal.coe_le_coe_iff.1
    rw [EReal.coe_add]
    exact (add_le_add (hminorant u) (le_refl (quadraticPenalty lambda w u : EReal))).trans hu
  have hlinear : -(‖L‖ * ‖u - w‖) ≤ L u - L w := by
    have h := (neg_abs_le (L (u - w))).trans'
      (neg_le_neg (L.le_opNorm (u - w)))
    simpa only [Real.norm_eq_abs, map_sub] using h
  have hquad : ‖u - w‖ ^ 2 ≤ 2 * lambda * (D + ‖L‖ * ‖u - w‖) := by
    rw [mul_comm (2 * lambda)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * lambda)).1
    dsimp [quadraticPenalty] at hreal
    dsimp [D]
    nlinarith
  have hD := mul_le_mul_of_nonneg_left (le_abs_self D)
    (by positivity : 0 ≤ 4 * lambda)
  have hsquare : ‖u - w‖ ^ 2 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg (‖u - w‖ - 2 * lambda * ‖L‖)]
  have hnorm : ‖u - w‖ ≤ B + 1 := by
    nlinarith [sq_nonneg (‖u - w‖ - 1)]
  calc
    ‖u‖ = ‖u - w + w‖ := by rw [sub_add_cancel]
    _ ≤ ‖u - w‖ + ‖w‖ := norm_add_le _ _
    _ ≤ B + 1 + ‖w‖ := add_le_add hnorm le_rfl

end PDE.Analysis.Convex
