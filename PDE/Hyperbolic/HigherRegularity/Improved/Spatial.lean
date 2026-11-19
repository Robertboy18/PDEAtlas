/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.ClassicalFull
public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# The spatial lift of an improved weak wave

A bounded shifted elliptic solver acts on the load `f - u_tt + mu * u`.
The resulting Bochner `H²` curve represents the same `H¹₀` displacement, and its
uniform bound follows from the three bounded terms of that load.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Lift the spatial residual of a full weak wave using a bounded elliptic solver.
The equality in `H¹` identifies every first derivative as well as the base function. -/
theorem exists_h2_trajectory_of_full_weakWave
    (hopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (mu : ℝ) (S : DerivLp n 2 Ω →L[ℝ] W^{2,2}(Ω))
    (hS : ∀ (f : DerivLp n 2 Ω) (u : H¹₀(Ω)),
      IsWeakShiftedFullDivergenceSolution A B C 0 f 0 u →
      wkpBaseCoordinateCLM (S (f + mu • baseCoordCLM u)) = baseCoordCLM u)
    {f w : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {g : H¹₀(Ω)} {h : DerivLp n 2 Ω}
    (hweak : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
      u v ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2
        (volume.restrict (Ioc a b)) w) g h)
    {Cf Cw Cu : ℝ}
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖f t‖ ≤ Cf)
    (hw : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖w t‖ ≤ Cw)
    (hu : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖u t‖ ≤ Cu) :
    ∃ U : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc a b)),
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        lowerOrderCLM (k := 1) (m := 2) (by omega) (U t) = h10SubtypeL (u t)) ∧
      MemLp (fun t ↦ U t) ∞ (volume.restrict (Ioc a b)) ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), ‖U t‖ ≤ ‖S‖ * (Cf + Cw + |mu| * Cu) := by
  let μ := volume.restrict (Ioc a b)
  let T := h10L2GelfandTriple hopen
  let uBase := T.inclusion.compLpL 2 μ u
  let r := f - w + mu • uBase
  let U := S.compLpL 2 μ r
  have hr : (r : ℝ → DerivLp n 2 Ω) =ᵐ[μ]
      fun t ↦ f t - w t + mu • baseCoordCLM (u t) := by
    filter_upwards [Lp.coeFn_add (f - w) (mu • uBase), Lp.coeFn_sub f w,
      Lp.coeFn_smul mu uBase, T.inclusion.coeFn_compLpL u] with t hadd hsub hsmul hbase
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hadd hsub hsmul
    rw [hadd, hsub, hsmul, hbase]
    rfl
  have hrbound : ∀ᵐ t ∂μ, ‖r t‖ ≤ Cf + Cw + |mu| * Cu := by
    filter_upwards [hr, hf, hw, hu] with t ht hft hwt hut
    rw [ht]
    calc
      _ ≤ ‖f t‖ + ‖w t‖ + |mu| * ‖baseCoordCLM (u t)‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using
          (norm_add_le (f t - w t) (mu • baseCoordCLM (u t))).trans
            (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hft hwt)
        (mul_le_mul_of_nonneg_left ((baseCoordCLM_norm_le (u t)).trans hut) (abs_nonneg mu))
  have hU := S.coeFn_compLpL r
  have hUbound : ∀ᵐ t ∂μ, ‖U t‖ ≤ ‖S‖ * (Cf + Cw + |mu| * Cu) := by
    filter_upwards [hU, hrbound] with t ht hb
    rw [show U t = S (r t) from ht]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg S))
  refine ⟨U, ?_, memLp_top_of_bound (Lp.aestronglyMeasurable U) _ hUbound, hUbound⟩
  filter_upwards [hU, hr, hweak.equationAE, T.pivotToDual.coeFn_compLpL f,
    T.pivotToDual.coeFn_compLpL w] with t hUt hrt hEq hft hwt
  have hspatial : IsWeakShiftedFullDivergenceSolution A B C 0 (f t - w t) 0 (u t) := by
    apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
      hopen A B C 0 (f t - w t) 0 (u t)).mp
    intro x
    have hx := congrArg (fun ell ↦ ell x) hEq
    rw [hft, hwt] at hx
    simp only [shiftedDivergenceForm_apply, zero_mul, add_zero,
      generalizedLoad_apply, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, inner_sub_left]
    change T.pivotToDual (w t) x + fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C) (u t) x = T.pivotToDual (f t) x at hx
    change fullDivergenceForm (multiplicationCoefficientOperator A)
      (fun i ↦ mulLpLeft (B i)) (mulLpLeft C) (u t) x =
      T.pivotToDual (f t) x - T.pivotToDual (w t) x
    exact eq_sub_of_add_eq' hx
  apply wkpBaseCoordinateCLM_injective hopen
  have hbase := hS (f t - w t) (u t) hspatial
  rw [show U t = S (r t) from hUt, hrt]
  change (lowerOrderCLM (k := 1) (m := 2) (by omega)
    (S (f t - w t + mu • baseCoordCLM (u t))) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) = _
  simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
    wkpBaseCoordinateCLM_h10SubtypeL, wkpBaseCoordinateCLM_apply,
    baseCoordCLM_apply, h10SubtypeL_apply] using hbase

end SobolevSpace.GraphSpace
