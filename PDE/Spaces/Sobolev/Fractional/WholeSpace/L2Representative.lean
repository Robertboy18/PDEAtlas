/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Operators
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Embedding

/-!
# Elements of `H^s` with `s ≥ 0` are square-integrable functions

An element of `H^s(ℝ^n; ℂ)` is by definition a tempered distribution.  For `s ≥ 0`
it is more than that: it is represented by an `L²` function, and the
representation is norm-decreasing.

This is the first step towards comparing the fractional scale with the
integer-order weak-derivative graph space `SobolevSpace.GraphSpace.HkSpaceOn`,
whose elements are tuples of `L²` functions.  Any such comparison has to begin
by turning a distribution into a function, which is what `toL2Fun` does.

The mechanism is that `H^0` is `L²`: the Bessel potential of order zero is the
identity, so for `u : H^{0}(ℝ^n)` the defining property of `toLp` degenerates to
`toDistr u = toLp u`.  For general `s ≥ 0` one first includes `H^s ⊆ H^0` using
`inclLinear`, which is norm-decreasing by `norm_inclLinear_le`.

## Main definitions

* `SobolevSpace.Fractional.toL2Fun`: the `L²` function underlying an element of
  `H^s` for `s ≥ 0`.

## Main results

* `SobolevSpace.Fractional.toDistr_eq_toL2`: `H^0` is `L²`.
* `SobolevSpace.Fractional.toDistr_eq_toL2Fun`: an element of `H^s` is its `L²`
  representative, as a distribution.
* `SobolevSpace.Fractional.norm_toL2Fun_le`: `‖u‖_{L²} ≤ ‖u‖_{H^s}`.
* `SobolevSpace.Fractional.toL2Fun_injective`: distinct elements of `H^s` have
  distinct representatives, so `H^s` embeds in `L²`.
-/

@[expose] public section

open TemperedDistribution MeasureTheory
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

open BesselPotentialSpace

/-- `H^0(ℝ^n)` is `L²(ℝ^n)`: at order zero the Bessel potential is the identity, so
an element of `H^0` is its own `L²` representative. -/
theorem toDistr_eq_toL2 (u : H^{0}(ℝ^n)) :
    toDistr u = ((toLp u : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ)) := by
  have h := bessel_toDistr_eq_toLp u
  rwa [besselPotential_zero, ContinuousLinearMap.id_apply] at h

/-- The `L²` function underlying an element of `H^s` when `s ≥ 0`. -/
noncomputable def toL2Fun (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) : Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  toLp (inclLinear n hs u)

/-- An element of `H^s` with `s ≥ 0` is its `L²` representative. -/
theorem toDistr_eq_toL2Fun (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    toDistr u = ((toL2Fun hs u : Lp ℂ 2 (volume : Measure (ℝ^n))) : 𝓢'(ℝ^n, ℂ)) := by
  rw [toL2Fun, ← toDistr_eq_toL2, toDistr_inclLinear]

/-- Passing to the `L²` representative does not increase the norm. -/
theorem norm_toL2Fun_le (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) : ‖toL2Fun hs u‖ ≤ ‖u‖ := by
  rw [toL2Fun, norm_toLp_eq]
  exact norm_inclLinear_le hs u

/-- The `L²` representative is additive. -/
theorem toL2Fun_add (hs : 0 ≤ s) (u v : H^{s}(ℝ^n)) :
    toL2Fun hs (u + v) = toL2Fun hs u + toL2Fun hs v := by
  rw [toL2Fun, toL2Fun, toL2Fun, map_add, toLp_add]

/-- The `L²` representative commutes with complex scalars. -/
theorem toL2Fun_smul (hs : 0 ≤ s) (c : ℂ) (u : H^{s}(ℝ^n)) :
    toL2Fun hs (c • u) = c • toL2Fun hs u := by
  rw [toL2Fun, toL2Fun, map_smul, toLp_smul]

/-- Distinct elements of `H^s` have distinct `L²` representatives, so for `s ≥ 0`
the space `H^s` embeds into `L²`. -/
theorem toL2Fun_injective (hs : 0 ≤ s) :
    Function.Injective (toL2Fun (n := n) hs) := by
  intro u v huv
  refine ext ?_
  rw [toDistr_eq_toL2Fun hs, toDistr_eq_toL2Fun hs, huv]

/-- The `L²` representative as a `ℂ`-linear map. -/
noncomputable def toL2FunLinear (n : ℕ) (hs : 0 ≤ s) :
    H^{s}(ℝ^n) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) where
  toFun := toL2Fun hs
  map_add' := toL2Fun_add hs
  map_smul' := toL2Fun_smul hs

/-- `toL2FunLinear` evaluates to `toL2Fun`. -/
@[simp] theorem toL2FunLinear_apply (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    toL2FunLinear n hs u = toL2Fun hs u := rfl

/-- The `L²` representative as a continuous linear map of norm at most one. -/
noncomputable def toL2FunCLM (n : ℕ) (hs : 0 ≤ s) :
    H^{s}(ℝ^n) →L[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  { toL2FunLinear n hs with
    cont := by
      refine AddMonoidHomClass.continuous_of_bound (toL2FunLinear n hs) 1 ?_
      intro u
      simpa using norm_toL2Fun_le hs u }

/-- `toL2FunCLM` evaluates to `toL2Fun`. -/
@[simp] theorem toL2FunCLM_apply (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    toL2FunCLM n hs u = toL2Fun hs u := rfl

/-- The operator norm of `H^s → L²`, `s ≥ 0`, is at most one. This is `norm_toL2Fun_le` in
operator-norm form; for `s = 0` the map is an isometry, so the bound is sharp there. -/
theorem norm_toL2FunCLM_le_one (hs : 0 ≤ s) : ‖toL2FunCLM n hs‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa using norm_toL2Fun_le hs u

/-- The `L²` representative of a Schwartz function, viewed in `H^s`, is that
Schwartz function's own `L²` class.

This lets concrete functions enter the `H^s` theory. -/
theorem toL2Fun_ofSchwartz (hs : 0 ≤ s) (φ : 𝓢(ℝ^n, ℂ)) :
    toL2Fun hs (SchwartzMap.memSobolev (s := s) φ).toBesselPotentialSpace =
      φ.toLp 2 (volume : Measure (ℝ^n)) := by
  apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
  simpa using (toDistr_eq_toL2Fun hs
    (SchwartzMap.memSobolev (s := s) φ).toBesselPotentialSpace).symm

/-- For `0 ≤ t ≤ s`, the inclusion `H^s ⊆ H^t` does not change the `L²` representative. -/
theorem toL2Fun_inclLinear {t : ℝ} (hst : t ≤ s) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (u : H^{s}(ℝ^n)) :
    toL2Fun ht (inclLinear n hst u) = toL2Fun hs u := by
  apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
  have h := (toDistr_eq_toL2Fun ht (inclLinear n hst u)).symm.trans
    ((toDistr_inclLinear hst u).trans (toDistr_eq_toL2Fun hs u))
  simpa only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply] using h

end SobolevSpace.Fractional
