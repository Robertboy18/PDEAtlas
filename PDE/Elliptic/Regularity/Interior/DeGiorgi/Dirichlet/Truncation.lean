/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.TruncatedTesting
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Order
import PDE.Elliptic.Variational.Comparison.Locality
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.PositivePart

/-!
# Superlevel tests for the zero-boundary equation

For a nonnegative level, `(u-k)₊` belongs to `H¹₀` whenever `u` does.
The trace domination theorem proves the boundary assertion; the
positive-part chain rule and locality of multiplication coefficients give
the exact weak test identity. Uniform ellipticity then controls its gradient.

These are the zero-boundary truncations used in the Stampacchia boundedness
argument for a scalar divergence-form equation with bounded forcing.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

open Approximation.UpToBoundary

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- A nonnegative superlevel truncation of a zero-boundary function still has
zero trace. The trace argument uses only domination by `u₊`. -/
theorem superlevel_mem_H10 (P : InwardPartition Ω) (u : H¹₀(Ω))
    {k : ℝ} (hk : 0 ≤ k) :
    lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
      ((u : H¹(Ω)) - wkpConstant k) ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
  apply Trace.C1.mem_H10_of_abs_le_ae P
    (positivePartWkp0 hΩ.isOpen.measurableSet (by norm_num) u).property
  filter_upwards [
    lipschitzCompositionOn_base_ae hΩ.isOpen Lp.lipschitzWith_pos_part
      ((u : H¹(Ω)) - wkpConstant k),
    baseRepresentative_sub_ae (u : H¹(Ω)) (wkpConstant k),
    wkpConstant_base_ae (n := m + 1) (p := 2) (Ω := Ω) k,
    positivePartWkp0_base_ae hΩ.isOpen.measurableSet (by norm_num) u] with
    x ht hs hc hp
  change baseRepresentative
    (lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part
      ((u : H¹(Ω)) - wkpConstant k)) x =
        max (baseRepresentative ((u : H¹(Ω)) - wkpConstant k) x) 0 at ht
  change baseRepresentative (wkpConstant (n := m + 1) (p := 2)
    (Ω := Ω) k) x = k at hc
  change baseRepresentative
    (positivePartWkp0 hΩ.isOpen.measurableSet (by norm_num) u : H¹(Ω)) x =
      max (baseRepresentative (u : H¹(Ω)) x) 0 at hp
  rw [ht, hs, hc, hp, abs_of_nonneg (le_max_right _ _)]
  exact max_le_max (sub_le_self _ hk) le_rfl

/-- The superlevel truncation, with its derived zero-boundary membership. -/
def superlevelH10 (P : InwardPartition Ω) (u : H¹₀(Ω)) {k : ℝ} (hk : 0 ≤ k) :
    H¹₀(Ω) :=
  ⟨_, superlevel_mem_H10 P u hk⟩

/-- The zero-boundary truncation represents the usual positive part. -/
theorem superlevelH10_base_ae (P : InwardPartition Ω) (u : H¹₀(Ω))
    {k : ℝ} (hk : 0 ≤ k) :
    (baseCoordCLM (superlevelH10 P u hk) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ max (baseCoordCLM u x - k) 0 := by
  filter_upwards [
    lipschitzCompositionOn_base_ae hΩ.isOpen Lp.lipschitzWith_pos_part
      ((u : H¹(Ω)) - wkpConstant k),
    baseRepresentative_sub_ae (u : H¹(Ω)) (wkpConstant k),
    wkpConstant_base_ae (n := n) (p := 2) (Ω := Ω) k] with x ht hs hc
  exact ht.trans (congrArg (fun s : ℝ ↦ max s 0)
    (hs.trans (congrArg (baseCoordCLM u x - ·) hc)))

/-- Testing the weak equation with a nonnegative superlevel gives
the principal quadratic form of the truncated function. -/
theorem IsInteriorWeakDivergenceSolution.superlevelH10_equation
    (P : InwardPartition Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (f : DerivLp n 2 Ω) (u : H¹₀(Ω))
    (hu : IsInteriorWeakDivergenceSolution a f (u : H¹(Ω)))
    {k : ℝ} (hk : 0 ≤ k) :
    variableCoeffForm (multiplicationCoefficientOperator a)
      (superlevelH10 P u hk) (superlevelH10 P u hk) =
        loadFunctional f (superlevelH10 P u hk) := by
  let U : H¹(Ω) := (u : H¹(Ω)) - wkpConstant k
  let T := superlevelH10 P u hk
  have hloc (i : DerivIndex n 1) :
      (coordCLM i T : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < wkpBaseCoordinateCLM U x then wkpCoordinateCLM i U x else 0 :=
    lipschitzCompositionOn_posPart_coordinate_ae U i
  have hlocal := interiorFullDivergenceOperator_positivePart_right
    a 0 0 0 U T hloc
  have hD (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n j) U =
        wkpCoordinateCLM (singleDerivIndex n j) (u : H¹(Ω)) := by
    have hc : wkpCoordinateCLM (singleDerivIndex n j)
        (wkpConstant (n := n) (p := 2) (Ω := Ω) k) = 0 :=
      Lp.ext ((wkpConstant_deriv_ae k j).trans
        (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)).symm)
    simp only [U, map_sub, hc, sub_zero]
  have he : interiorVariableCoeffForm (multiplicationCoefficientOperator a) U T =
      variableCoeffForm (multiplicationCoefficientOperator a) T T := by
    simpa only [interiorFullDivergenceOperator, add_apply,
      ContinuousLinearMap.comp_apply, interiorLowerOrderOperator_apply,
      Pi.zero_apply, Lp.zero_smul, Finset.sum_const_zero, zero_add, map_zero, zero_apply,
      add_zero, zero_mul, shiftedDivergenceForm_apply, fullDivergenceForm_apply,
      multiplicationFirstOrderOperator_apply, multiplicationZeroOrderOperator_apply,
      inner_zero_left, variableCoeffForm_apply] using hlocal
  rw [← he]
  convert hu.equation T using 1
  simp only [interiorVariableCoeffForm_apply, hD]

/-- The truncated gradient is controlled by the scalar load pairing.
No boundedness of the state or smoothness of the coefficients is required. -/
theorem IsInteriorWeakDivergenceSolution.superlevelH10_gradient_sq_le
    (P : InwardPartition Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (f : DerivLp n 2 Ω) (u : H¹₀(Ω))
    (hu : IsInteriorWeakDivergenceSolution a f (u : H¹(Ω)))
    {k : ℝ} (hk : 0 ≤ k) :
    α * ‖∇ (superlevelH10 P u hk : H¹(Ω))‖ ^ 2 ≤
      loadFunctional f (superlevelH10 P u hk) := by
  have hnorm : ‖∇ (superlevelH10 P u hk : H¹(Ω))‖ ^ 2 =
      ∑ i, ‖derivCoordCLM i (superlevelH10 P u hk)‖ ^ 2 :=
    Lp.norm_euclideanTuple_sq _
  rw [← hu.superlevelH10_equation P a f u hk, hnorm]
  simpa only [real_inner_self_eq_norm_sq, variableCoeffForm_apply] using
    aeUniformlyElliptic_energy_le a ha (fun i ↦ derivCoordCLM i (superlevelH10 P u hk))

end SobolevSpace.GraphSpace
