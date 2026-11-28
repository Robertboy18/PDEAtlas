/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import PDE.Analysis.MeasureTheory.Lp.SymbolDecay
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Smooth functions with symbol decay: gradients, global bounds, decay at infinity

What does symbol decay of order `d` say about a function that is smooth on the whole space, and
not only away from the origin? `HasSymbolDecay.exists_bound_one_add_norm` bounds its `k`th
derivative by `C (1 + ‖x‖) ^ (d - k)` everywhere. For `k ≥ d` the right side is at most `C`, so
these derivatives are bounded. For `k > d` it tends to zero, so these derivatives vanish at
infinity. A smooth field of order `-1`, such as the far field of a self-similar profile, is
therefore in `W^{∞,∞}`, and all its derivatives tend to zero. The module also gives the
gradient form of `HasSymbolDecay.fderiv` on a Hilbert space, through the Riesz isometry, and the
bound `O(‖x‖ ^ d)` at infinity.

## Main results

* `HasSymbolDecay.gradient`: on a real Hilbert space the gradient of a scalar function of order
  `d` has order `d - 1`.
* `HasSymbolDecay.exists_bound_iteratedFDeriv`: on a finite-dimensional space, a smooth function
  of order `d` has a bounded `k`th derivative for every `k ≥ d`.
* `HasSymbolDecay.tendsto_iteratedFDeriv_cocompact`: such a function has its `k`th derivative
  tending to zero at infinity for every `k > d`.
* `HasSymbolDecay.isBigO_cocompact`: a function of order `d` on a finite-dimensional space is
  `O(‖x‖ ^ d)` at infinity.
* `isLittleO_inv_norm_sq_inv_norm`: `‖x‖⁻² = o(‖x‖⁻¹)` at infinity, on every proper space.
-/

@[expose] public section

open Filter
open scoped ContDiff Topology Gradient Asymptotics

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace HasSymbolDecay

/-- The gradient of a scalar function with symbol decay of order `d` has order `d - 1`: it is
the derivative read through the Riesz isometry, which preserves every bound. -/
theorem gradient {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    {d : ℤ} {f : V → ℝ} (hf : HasSymbolDecay d f) : HasSymbolDecay (d - 1) (∇ f) :=
  hf.fderiv.clm_comp
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

variable [FiniteDimensional ℝ E] {d : ℤ} {f : E → F}

/-- A smooth function with symbol decay of order `d` has bounded derivatives of every order
`k ≥ d`, since its `k`th derivative is at most `C / (1 + ‖x‖) ^ (k - d)`. -/
theorem exists_bound_iteratedFDeriv (hf : HasSymbolDecay d f) (hfc : ContDiff ℝ ∞ f) {k : ℕ}
    (hdk : d ≤ k) : ∃ C, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound_one_add_norm hfc hdk
  exact ⟨C, fun x ↦ (hC x).trans (div_le_self hC0 (one_le_pow₀ (by linarith [norm_nonneg x])))⟩

/-- A smooth function with symbol decay of order `d` has derivatives of every order `k > d`
tending to zero at infinity, since its `k`th derivative is at most `C / (1 + ‖x‖) ^ (k - d)`
with `k - d ≥ 1`. -/
theorem tendsto_iteratedFDeriv_cocompact (hf : HasSymbolDecay d f) (hfc : ContDiff ℝ ∞ f)
    {k : ℕ} (hdk : d < k) : Tendsto (iteratedFDeriv ℝ k f) (cocompact E) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := hf.exists_bound_one_add_norm hfc hdk.le
  have hpos : ((k : ℤ) - d).toNat ≠ 0 := by omega
  have hlim : Tendsto (fun x : E ↦ C / (1 + ‖x‖) ^ ((k : ℤ) - d).toNat) (cocompact E) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hpos).comp
      (tendsto_atTop_add_const_left _ 1 (tendsto_norm_cocompact_atTop (E := E))))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun x ↦ norm_nonneg _) hC hlim)

/-- A function with symbol decay of order `d` is `O(‖x‖ ^ d)` at infinity: this is the bound of
order zero of the definition. -/
theorem isBigO_cocompact (hf : HasSymbolDecay d f) :
    f =O[cocompact E] fun x ↦ ‖x‖ ^ d := by
  obtain ⟨C, -, hC⟩ := hf.exists_bound_nonneg
  refine Asymptotics.IsBigO.of_bound (C 0) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop 1] with x hx
  have h := hC 0 x hx
  rw [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at h
  rwa [Real.norm_of_nonneg (zpow_nonneg (norm_nonneg x) d)]

end HasSymbolDecay

omit [NormedSpace ℝ E] in
/-- `‖x‖⁻² = o(‖x‖⁻¹)` at infinity: `t ^ 2 = o(t)` as `t → 0`, applied to `t = ‖x‖⁻¹`. -/
theorem isLittleO_inv_norm_sq_inv_norm [ProperSpace E] :
    (fun x : E ↦ ‖x‖⁻¹ ^ 2) =o[cocompact E] fun x ↦ ‖x‖⁻¹ :=
  (Asymptotics.isLittleO_pow_id (n := 2) (by norm_num)).comp_tendsto
    (tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop)

end PDE.Analysis
