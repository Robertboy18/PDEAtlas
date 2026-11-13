/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.FiniteSums
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeEnergy

/-!
# First-order Sobolev energy

For finite `p ≥ 1`, the `p`-th power of the `W^{1,p}(Ω)` norm is the sum of
the `L^p` energy of the function and its first weak partial derivatives.
The derivatives are elements of `W^{0,p}(Ω)`, whose norms agree with their
`L^p` coordinate norms.

The identity holds on arbitrary domains, including in dimension zero, where
the derivative sum is empty. Dropping the nonnegative function term bounds the
total weak derivative energy with coefficient one.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- The first-order graph norm splits exactly into function and weak derivative energies. -/
theorem norm_rpow_eq_base_add_sum_partialDeriv (hp : p ≠ ∞) (u : W^{1,p}(Ω)) :
    ‖u‖ ^ p.toReal = ‖wkpBaseCoordinateCLM u‖ ^ p.toReal +
      ∑ i : Fin n, ‖∂[i] u‖ ^ p.toReal := by
  have hp0 : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have hnorm :
      ‖(u : WkpAmbientOn n 1 p Ω)‖ ^ p.toReal =
        ∑ a, ‖(u : WkpAmbientOn n 1 p Ω) a‖ ^ p.toReal := by
    rw [PiLp.norm_eq_sum hp0, one_div, Real.rpow_inv_rpow (by positivity) hp0.ne']
  simpa only [sum_derivIndex_one, norm_partialDeriv_eq_wkpCoordinateCLM,
    wkpCoordinateCLM_apply, wkpBaseCoordinateCLM_apply, Submodule.norm_coe] using hnorm

/-- The total extended weak derivative energy is bounded by the first-order Sobolev energy. -/
theorem sum_enorm_partialDeriv_rpow_le (hp : p ≠ ∞) (u : W^{1,p}(Ω)) :
    ∑ i : Fin n, ‖∂[i] u‖ₑ ^ p.toReal ≤ ‖u‖ₑ ^ p.toReal := by
  have hle : (∑ i : Fin n, ‖∂[i] u‖ ^ p.toReal) ≤ ‖u‖ ^ p.toReal := by
    rw [norm_rpow_eq_base_add_sum_partialDeriv hp]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
  simpa only [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    ofReal_norm] using ENNReal.ofReal_le_ofReal hle

end SobolevSpace.GraphSpace
