/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives
import PDE.Analysis.Normed.PiLp.CompareExp
import PDE.Spaces.Sobolev.GraphSpace.FiniteSums
import PDE.Spaces.Sobolev.GraphSpace.VectorValued.ZeroOrder

/-!
# First-order Banach-valued Sobolev energy

The norm of a first weak partial derivative equals that of its original `Lp` coordinate.
For finite exponents, the graph energy is the function energy plus the sum of
the derivative energies. At every exponent, the graph norm is at most the sum of the
coordinate norms. These identities hold on any open domain, including in dimension
zero, for arbitrary real Banach targets.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A first weak partial derivative has the norm of its original `Lp` coordinate. -/
theorem norm_partialDeriv_eq_coordinate {d : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {Ω : Opens ℝ^d} (i : Fin d) (U : W^{1,q}(Ω; F)) :
    ‖∂[i] U‖ = ‖U.val (singleDerivIndex d i)‖ := by
  rw [norm_eq_norm_base_of_order_zero]
  change ‖(partialDerivCLM i U).val (baseIndex d 0)‖ = _
  rw [partialDerivCLM, derivativeWordCLM_apply, derivativeWordIndex_baseIndex]
  rfl

/-- Extended norms also identify the weak derivative with its `Lp` coordinate. -/
theorem enorm_partialDeriv_eq_coordinate {d : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {Ω : Opens ℝ^d} (i : Fin d) (U : W^{1,q}(Ω; F)) :
    ‖∂[i] U‖ₑ = ‖U.val (singleDerivIndex d i)‖ₑ := by
  simpa only [ofReal_norm] using
    congrArg ENNReal.ofReal (norm_partialDeriv_eq_coordinate i U)

/-- The first-order energy is the sum of the function and derivative energies. -/
theorem norm_rpow_eq_base_add_sum_partialDeriv
    {d : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {Ω : Opens ℝ^d} (hq : q ≠ ∞) (U : W^{1,q}(Ω; F)) :
    ‖U‖ ^ q.toReal = ‖U.val (baseIndex d 1)‖ ^ q.toReal +
      ∑ i : Fin d, ‖∂[i] U‖ ^ q.toReal := by
  have hq0 : 0 < q.toReal := q.toReal_pos_iff_ne_top.mpr hq
  have h : ‖U.val‖ ^ q.toReal = ∑ a, ‖U.val a‖ ^ q.toReal := by
    rw [PiLp.norm_eq_sum hq0, one_div,
      Real.rpow_inv_rpow (by positivity) hq0.ne']
  simpa only [sum_derivIndex_one, norm_partialDeriv_eq_coordinate,
    Submodule.norm_coe] using h

/-- The graph norm is bounded by the sum of the function and derivative norms,
including at the infinite exponent. -/
theorem norm_le_base_add_sum_partialDeriv
    {d : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {Ω : Opens ℝ^d} (U : W^{1,q}(Ω; F)) :
    ‖U‖ ≤ ‖U.val (baseIndex d 1)‖ + ∑ i : Fin d, ‖∂[i] U‖ := by
  simpa only [sum_derivIndex_one, norm_partialDeriv_eq_coordinate,
    Submodule.norm_coe] using PiLp.norm_le_sum_norm U.val

/-- The sum of the weak derivative energies is bounded by the first-order energy. -/
theorem sum_enorm_partialDeriv_rpow_le {d : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {Ω : Opens ℝ^d} (hq : q ≠ ∞) (U : W^{1,q}(Ω; F)) :
    ∑ i : Fin d, ‖∂[i] U‖ₑ ^ q.toReal ≤ ‖U‖ₑ ^ q.toReal := by
  have hle : ∑ i : Fin d, ‖∂[i] U‖ ^ q.toReal ≤ ‖U‖ ^ q.toReal := by
    rw [norm_rpow_eq_base_add_sum_partialDeriv hq]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
  simpa only [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    ofReal_norm] using ENNReal.ofReal_le_ofReal hle

end SobolevSpace.VectorValued
