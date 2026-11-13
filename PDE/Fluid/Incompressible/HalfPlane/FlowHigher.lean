/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityFieldHigher
public import PDE.Analysis.ODE.Flow.HigherHolder
public import PDE.Analysis.Calculus.HolderComposition
import PDE.Analysis.Calculus.IntegralMajorant

/-!
# Bounds of the flow of the velocity of a `C^{k,α}` history with a top-order majorant

Let `ω` be a `C^{k,α}` history on `[-T, T]`, `k ≥ 2`, whose derivatives of order at most `k - 1`
have the bounds `Nlow` of a `C^{k-1,α}` history and whose `k`-th derivative at time `t` is bounded,
with its Hölder constant, by `P |t|` (`IsTopBoundedHistory`). Its field
`v r = extendedVelocity (k + 1) (ω r)` has, on the closed half-plane `H̄`, derivatives of order at
most `k` bounded by `c_v Nlow`, the derivative of order `k + 1` bounded by `c_v (Nlow + P |r|)` and
`α`-Hölder with constant `c_h P |r|`, where `c_v = velocityConst k α R` and
`c_h = velocityHolderConst k α`.

The flow maps `X = flowOn v (-T) T s t` then have, on `H̄`, derivatives of orders `1 ≤ j ≤ k` at
most `flowBound` and `α`-Hölder with constant `flowHolder`, constants depending only on
`k, α, R, Nlow, T`; the derivative of order `k + 1` is at most
`flowTopConst + flowTopSlope |∫ₜˢ P(|r|) dr|` and `α`-Hölder with constant
`flowTopHolderConst + flowTopHolderSlope |∫ₜˢ P(|r|) dr|`, affine in the integral of the
majorant with coefficients of the same kind.

## Main results

* `IsTopBoundedHistory.norm_iteratedFDeriv_flowOn_le`,
  `IsTopBoundedHistory.norm_iteratedFDeriv_flowOn_sub_le`: the orders `1 ≤ j ≤ k`.
* `IsTopBoundedHistory.norm_iteratedFDeriv_flowOn_top_le`,
  `IsTopBoundedHistory.norm_iteratedFDeriv_flowOn_top_sub_le`: the order `k + 1`.
* `IsTopBoundedHistory.hasHolderBounds_flowOn`, `IsTopBoundedHistory.hasHolderBounds_flowOn_succ`:
  the same bounds as `PDE.Analysis.HasHolderBounds` of orders `k` and `k + 1`.

## How it works

The field bounds are the bounds of the half-plane velocity in terms of the vorticity
(`norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul`,
`norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le`), applied on `H̄`, where the field is that
velocity (`iteratedFDeriv_extendedVelocity_of_nonneg`). The flow maps preserve `H̄`
(`IsTopBoundedHistory.mapsTo_flowOn`), so the estimates for flows of fields smooth in space apply
with `H̄` as the invariant set.
`PDE.Analysis.ODE.IsC1FieldOn.norm_iteratedFDeriv_flowOn_le_flowDerivBound` gives the orders up to
`k`, and `PDE.Analysis.ODE.IsC1FieldOn.norm_iteratedFDeriv_flowOn_le_of_top` gives the order
`k + 1`, linear in the integral of the time-dependent bound of the top derivative of the field. The
Hölder constants come from `PDE.Analysis.ODE.IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_max_rpow`
and, at the order `k + 1`, from
`PDE.Analysis.ODE.IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_max_rpow_of_holder`, in which the
lower orders enter through Hölder constants, so that the bound stays affine in the integral of the
majorant. The rest is arithmetic that collects the constants.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal
open PDE.Analysis PDE.Analysis.ODE

namespace IncompressibleFlow

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The constant `c_v = 200/α + 40π(1 + max(R, 0)²) + k + 33` of the derivative bounds of the
velocity of a `C^{k,α}` history. -/
def velocityConst (k : ℕ) (α R : ℝ) : ℝ :=
  200 / α + 40 * Real.pi * (1 + max R 0 ^ 2) + k + 33

/-- The constant `c_h = 844/(α(1 - α)) + k` of the top Hölder bound of the velocity of a
`C^{k,α}` history. -/
def velocityHolderConst (k : ℕ) (α : ℝ) : ℝ :=
  844 / (α * (1 - α)) + k

/-- For `α > 0` the constant `c_v` is nonnegative. -/
theorem velocityConst_nonneg (k : ℕ) {α : ℝ} (hα : 0 < α) (R : ℝ) : 0 ≤ velocityConst k α R := by
  unfold velocityConst
  have := Real.pi_pos
  positivity

/-- For `0 < α < 1` the constant `c_h` is nonnegative. -/
theorem velocityHolderConst_nonneg (k : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    0 ≤ velocityHolderConst k α := by
  unfold velocityHolderConst
  have : 0 < 1 - α := by linarith
  positivity

/-- The Hölder rate `flowHolderRate` of a flow map is nonnegative when the bounds and constants
`K₂, M, M', L, L₂, Fm, Λ, k, h` entering it are. -/
theorem flowHolderRate_nonneg {m : ℕ} {α K₂ M M' L L₂ F₀ Fm Λ k h : ℝ} (hK₂ : 0 ≤ K₂)
    (hM : 0 ≤ M) (hM' : 0 ≤ M') (hL : 0 ≤ L) (hL₂ : 0 ≤ L₂) (hFm : 0 ≤ Fm) (hΛ : 0 ≤ Λ)
    (hk : 0 ≤ k) (hh : 0 ≤ h) : 0 ≤ flowHolderRate m α K₂ M M' L L₂ F₀ Fm Λ k h := by
  unfold flowHolderRate
  have hF : 0 ≤ max 1 F₀ ^ m := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hLα := Real.rpow_nonneg hL α
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition m) := Nat.cast_nonneg _
  exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hK₂ hL) hFm)
    (mul_nonneg (mul_nonneg (mul_nonneg hk hm) (pow_nonneg hL _)) hL₂))
    (mul_nonneg (mul_nonneg hh hLα) (pow_nonneg hL _)))
    (mul_nonneg hc (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hM hm) hΛ)
      (mul_nonneg hM' hL)) hF))

/-- The bound `c_v Nlow` of the derivatives of orders at most `k` of the field. -/
def fieldBound (k : ℕ) (α R Nlow : ℝ) : ℝ :=
  velocityConst k α R * Nlow

/-- The bound of the derivatives of orders `1 ≤ j ≤ k` of the flow maps over `[-T, T]`. -/
def flowBound (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  flowDerivBound (fun _ ↦ fieldBound k α R Nlow) (T - -T) k

/-- The Hölder constant of the derivatives of orders `1 ≤ j ≤ k` of the flow maps over
`[-T, T]`. -/
def flowHolder (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  (T - -T) * flowHolderRate k α (fieldBound k α R Nlow) (fieldBound k α R Nlow)
      (fieldBound k α R Nlow) (flowBound k α R Nlow T) (flowBound k α R Nlow T)
      (flowBound k α R Nlow T) (flowBound k α R Nlow T) (flowBound k α R Nlow T)
      (fieldBound k α R Nlow) (velocityHolderConst k α * Nlow) *
    Real.exp (fieldBound k α R Nlow * (T - -T)) + 2 * flowBound k α R Nlow T

/-- The constant term of the bound of the derivative of order `k + 1` of the flow maps. -/
def flowTopConst (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  (flowBound k α R Nlow T ^ (k + 1) * (fieldBound k α R Nlow * (T - -T)) +
      (T - -T) * (Fintype.card (OrderedFinpartition (k + 1)) *
        (lowerFieldBound (fun _ ↦ fieldBound k α R Nlow) (k + 1) *
          max 1 (flowBound k α R Nlow T) ^ (k + 1)))) *
    Real.exp (fieldBound k α R Nlow * (T - -T))

/-- The coefficient of `|∫ₜˢ P(|r|) dr|` in the bound of the derivative of order `k + 1` of the
flow maps. -/
def flowTopSlope (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  flowBound k α R Nlow T ^ (k + 1) * velocityConst k α R *
    Real.exp (fieldBound k α R Nlow * (T - -T))

/-- The Hölder constant of the derivatives of orders `2 ≤ i ≤ k` of the field. -/
def fieldHolder (k : ℕ) (α R Nlow : ℝ) : ℝ :=
  2 * fieldBound k α R Nlow + velocityHolderConst k α * Nlow

/-- The part of the rate of the top Hölder constant of the flow maps of lower order. -/
def flowTopRateConst (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  fieldBound k α R Nlow * ((k + 1 : ℕ) : ℝ) * flowBound k α R Nlow T ^ k *
      flowBound k α R Nlow T +
    Fintype.card (OrderedFinpartition (k + 1)) *
      ((fieldBound k α R Nlow * ((k + 1 : ℕ) : ℝ) * flowHolder k α R Nlow T +
          fieldHolder k α R Nlow * flowBound k α R Nlow T ^ α) *
        max 1 (flowBound k α R Nlow T) ^ (k + 1))

/-- The coefficient of `P(|r|)` in the rate of the top Hölder constant of the flow maps. -/
def flowTopRateSlope (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  velocityConst k α R * ((k + 1 : ℕ) : ℝ) * flowBound k α R Nlow T ^ k *
      flowBound k α R Nlow T +
    velocityHolderConst k α * flowBound k α R Nlow T ^ α * flowBound k α R Nlow T ^ (k + 1)

/-- The constant term of the Hölder constant of the derivative of order `k + 1` of the flow
maps. -/
def flowTopHolderConst (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  (fieldBound k α R Nlow * flowBound k α R Nlow T * flowTopConst k α R Nlow T +
      flowTopRateConst k α R Nlow T) * (T - -T) * Real.exp (fieldBound k α R Nlow * (T - -T)) +
    2 * flowTopConst k α R Nlow T

/-- The coefficient of `|∫ₜˢ P(|r|) dr|` in the Hölder constant of the derivative of order
`k + 1` of the flow maps. -/
def flowTopHolderSlope (k : ℕ) (α R Nlow T : ℝ) : ℝ :=
  (fieldBound k α R Nlow * flowBound k α R Nlow T * flowTopSlope k α R Nlow T * (T - -T) +
      flowTopRateSlope k α R Nlow T) * Real.exp (fieldBound k α R Nlow * (T - -T)) +
    2 * flowTopSlope k α R Nlow T

/-- The Hölder constant `fieldHolder` is nonnegative when `c_v Nlow`, `c_h` and `Nlow` are. -/
theorem fieldHolder_nonneg {k : ℕ} {α R Nlow : ℝ} (hc : 0 ≤ fieldBound k α R Nlow)
    (hch : 0 ≤ velocityHolderConst k α) (hN : 0 ≤ Nlow) : 0 ≤ fieldHolder k α R Nlow := by
  unfold fieldHolder; positivity

/-- The Hölder constant `flowHolder` of the flow maps is nonnegative when the field and flow bounds,
`c_h`, `Nlow` and the length `2T` of the time interval are. -/
theorem flowHolder_nonneg {k : ℕ} {α R Nlow T : ℝ} (hc : 0 ≤ fieldBound k α R Nlow)
    (hF : 0 ≤ flowBound k α R Nlow T) (hch : 0 ≤ velocityHolderConst k α) (hN : 0 ≤ Nlow)
    (hτ : 0 ≤ T - -T) : 0 ≤ flowHolder k α R Nlow T := by
  unfold flowHolder
  have := flowHolderRate_nonneg (m := k) (α := α) (F₀ := flowBound k α R Nlow T) hc hc hc hF hF
    hF hF hc (mul_nonneg hch hN)
  positivity

/-- The constant term `flowTopConst` is nonnegative when the field and flow bounds and the length
`2T` of the time interval are. -/
theorem flowTopConst_nonneg {k : ℕ} {α R Nlow T : ℝ} (hc : 0 ≤ fieldBound k α R Nlow)
    (hF : 0 ≤ flowBound k α R Nlow T) (hτ : 0 ≤ T - -T) : 0 ≤ flowTopConst k α R Nlow T := by
  unfold flowTopConst
  have : 0 ≤ lowerFieldBound (fun _ ↦ fieldBound k α R Nlow) (k + 1) :=
    Finset.sum_nonneg fun _ _ ↦ hc
  positivity

/-- The coefficient `flowTopSlope` is nonnegative when `c_v` and the flow bound are. -/
theorem flowTopSlope_nonneg {k : ℕ} {α R Nlow T : ℝ} (hcv : 0 ≤ velocityConst k α R)
    (hF : 0 ≤ flowBound k α R Nlow T) : 0 ≤ flowTopSlope k α R Nlow T := by
  unfold flowTopSlope; positivity

/-- The rate term `flowTopRateConst` is nonnegative when the field and flow bounds and their
Hölder constants are. -/
theorem flowTopRateConst_nonneg {k : ℕ} {α R Nlow T : ℝ} (hc : 0 ≤ fieldBound k α R Nlow)
    (hF : 0 ≤ flowBound k α R Nlow T) (hHf : 0 ≤ flowHolder k α R Nlow T)
    (hM' : 0 ≤ fieldHolder k α R Nlow) : 0 ≤ flowTopRateConst k α R Nlow T := by
  unfold flowTopRateConst; positivity

/-- The coefficient `flowTopRateSlope` is nonnegative when `c_v`, `c_h` and the flow bound are. -/
theorem flowTopRateSlope_nonneg {k : ℕ} {α R Nlow T : ℝ} (hcv : 0 ≤ velocityConst k α R)
    (hch : 0 ≤ velocityHolderConst k α) (hF : 0 ≤ flowBound k α R Nlow T) :
    0 ≤ flowTopRateSlope k α R Nlow T := by
  unfold flowTopRateSlope; positivity

/-- A `C^{k,α}` history on `[-T, T]` with a top-order majorant: a `C^{k,α}` history which is a
`C^{k-1,α}` history with the bound `Nlow`, whose `k`-th derivative at time `t` is bounded on the
closed half-plane, with its `α`-Hölder constant, by `P |t|`, for a function `P ≥ 0` continuous on
`[0, T]`. -/
structure IsTopBoundedHistory (k : ℕ) (ω : ℝ → ℝ^2 → ℝ) (T α R B Nlow : ℝ) (P : ℝ → ℝ) :
    Prop where
  /-- The history is `C^{k,α}`. -/
  history : IsCkVorticityHistory k ω (-T) T α R B
  /-- The derivatives of order at most `k - 1` have the bounds `Nlow`. -/
  low : IsCkVorticityHistory (k - 1) ω (-T) T α R Nlow
  /-- The majorant is continuous on `[0, T]`. -/
  continuousOn : ContinuousOn P (Icc 0 T)
  /-- The majorant is nonnegative on `[0, T]`. -/
  nonneg : ∀ r ∈ Icc 0 T, 0 ≤ P r
  /-- The `k`-th derivative at time `t` is at most `P |t|`. -/
  norm_le : ∀ t ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 →
    ‖iteratedFDerivWithin ℝ k (ω t) H̄ y‖ ≤ P |t|
  /-- The `k`-th derivative at time `t` is `α`-Hölder with constant `P |t|`. -/
  holder : ∀ t ∈ Icc (-T) T, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖iteratedFDerivWithin ℝ k (ω t) H̄ y - iteratedFDerivWithin ℝ k (ω t) H̄ z‖ ≤
      P |t| * ‖y - z‖ ^ α

namespace IsTopBoundedHistory

variable {k : ℕ} {ω : ℝ → ℝ^2 → ℝ} {T α R B Nlow : ℝ} {P : ℝ → ℝ}

/-- For `t ∈ [-T, T]`, `|t| ∈ [0, T]`. -/
theorem abs_mem_Icc {t : ℝ} (ht : t ∈ Icc (-T) T) : |t| ∈ Icc 0 T :=
  ⟨abs_nonneg t, abs_le.mpr ⟨ht.1, ht.2⟩⟩

/-- The majorant is nonnegative along the times of `[-T, T]`: `0 ≤ P |t|`. -/
theorem nonneg_abs (h : IsTopBoundedHistory k ω T α R B Nlow P) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    0 ≤ P |t| :=
  h.nonneg _ (abs_mem_Icc ht)

/-- For `T ≥ 0` the lower-order bound `Nlow` is nonnegative. -/
theorem low_nonneg (h : IsTopBoundedHistory k ω T α R B Nlow P) (hT : 0 ≤ T) : 0 ≤ Nlow :=
  h.low.nonneg (t := 0) ⟨by linarith, hT⟩

/-- The majorant along the times of `[-T, T]` is continuous. -/
theorem continuousOn_abs (h : IsTopBoundedHistory k ω T α R B Nlow P) :
    ContinuousOn (fun r ↦ P |r|) (Icc (-T) T) :=
  h.continuousOn.comp continuous_abs.continuousOn fun _ hr ↦ abs_mem_Icc hr

/-- For `α > 0` and `T ≥ 0` the field bound `c_v Nlow` is nonnegative. -/
theorem fieldBound_nonneg (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hT : 0 ≤ T) : 0 ≤ fieldBound k α R Nlow :=
  mul_nonneg (velocityConst_nonneg k hα R) (h.low_nonneg hT)

/-- For `k ≥ 1` the bound `flowBound` of the derivatives of the flow maps is nonnegative. -/
theorem flowBound_nonneg (hk : 1 ≤ k) : 0 ≤ flowBound k α R Nlow T := by
  have h1 := flowDerivBound_mono (fun _ ↦ fieldBound k α R Nlow) (T - -T) le_rfl hk
  rw [flowDerivBound_one] at h1
  exact (Real.exp_pos _).le.trans h1

/-! ### The field -/

/-- **The derivatives of order at most `k` of the field**, of lower order: at most `c_v Nlow` on
the closed half-plane. -/
theorem norm_iteratedFDeriv_le (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc (-T) T) {j : ℕ} (hj : j ≤ k) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ j (extendedVelocity (k + 1) (ω r)) y‖ ≤ fieldBound k α R Nlow := by
  rw [iteratedFDeriv_extendedVelocity_of_nonneg (by omega)
    (h.history.contDiffOn_halfPlaneVelocity hα hα1 hr) (by omega) hy]
  have hN := h.low.nonneg hr
  refine (norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul hα hα1 (le_max_right R 0)
    (h.low.contDiffOn r hr) (h.low.eq_zero_max hr) (h.low.norm_le r hr) (h.low.holder r hr)
    (by omega : j ≤ k - 1 + 1) hy).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hN
  unfold velocityConst
  have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  linarith

/-- **The derivative of order `k + 1` of the field**: at most `c_v Nlow + c_v P |r|` on the
closed half-plane. -/
theorem norm_iteratedFDeriv_top_le (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ (k + 1) (extendedVelocity (k + 1) (ω r)) y‖ ≤
      fieldBound k α R Nlow + velocityConst k α R * P |r| := by
  rw [iteratedFDeriv_extendedVelocity_of_nonneg (by omega)
    (h.history.contDiffOn_halfPlaneVelocity hα hα1 hr) le_rfl hy, fieldBound, ← mul_add]
  have hN := h.low.nonneg hr
  have hP := h.nonneg_abs hr
  refine norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul hα hα1 (le_max_right R 0)
    (h.history.contDiffOn r hr) (h.history.eq_zero_max hr) (fun j hj z hz ↦ ?_)
    (fun z z' hz hz' ↦ (h.holder r hr z z' hz hz').trans (mul_le_mul_of_nonneg_right
      (by linarith) (Real.rpow_nonneg (norm_nonneg _) α))) le_rfl hy
  rcases hj.lt_or_eq with hjk | rfl
  · exact (h.low.norm_le r hr j (by omega) z hz).trans (by linarith)
  · exact (h.norm_le r hr z hz).trans (by linarith)

/-- **The Hölder constant of the derivative of order `k + 1` of the field**: `c_h P |r|`. -/
theorem norm_iteratedFDeriv_top_sub_le (h : IsTopBoundedHistory k ω T α R B Nlow P)
    (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc (-T) T) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖iteratedFDeriv ℝ (k + 1) (extendedVelocity (k + 1) (ω r)) y -
        iteratedFDeriv ℝ (k + 1) (extendedVelocity (k + 1) (ω r)) z‖ ≤
      velocityHolderConst k α * P |r| * ‖y - z‖ ^ α := by
  have hu := h.history.contDiffOn_halfPlaneVelocity hα hα1 hr
  rw [iteratedFDeriv_extendedVelocity_of_nonneg (by omega) hu le_rfl hy,
    iteratedFDeriv_extendedVelocity_of_nonneg (by omega) hu le_rfl hz]
  exact norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα hα1 (h.history.contDiffOn r hr)
    (h.history.eq_zero r hr) (h.holder r hr) hy hz

/-- **The Hölder constant of the derivative of order `k` of the field**, of lower order:
`c_h Nlow`. -/
theorem norm_iteratedFDeriv_sub_le (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) (hk : 1 ≤ k) {r : ℝ} (hr : r ∈ Icc (-T) T) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖iteratedFDeriv ℝ k (extendedVelocity (k + 1) (ω r)) y -
        iteratedFDeriv ℝ k (extendedVelocity (k + 1) (ω r)) z‖ ≤
      velocityHolderConst k α * Nlow * ‖y - z‖ ^ α := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hlow : IsCkVorticityHistory k' ω (-T) T α R Nlow := by simpa using h.low
  have hu := h.history.contDiffOn_halfPlaneVelocity hα hα1 hr
  rw [iteratedFDeriv_extendedVelocity_of_nonneg (by omega) hu (by omega) hy,
    iteratedFDeriv_extendedVelocity_of_nonneg (by omega) hu (by omega) hz]
  refine (norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le hα hα1 (hlow.contDiffOn r hr)
    (hlow.eq_zero r hr) (hlow.holder r hr) hy hz).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (hlow.nonneg hr))
    (Real.rpow_nonneg (norm_nonneg _) α)
  unfold velocityHolderConst
  push_cast
  linarith

/-- The field is a smooth family of order `k + 1`. -/
theorem isSmoothFamilyOn (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) :
    IsSmoothFamilyOn (k + 1) (fun r ↦ extendedVelocity (k + 1) (ω r)) (Icc (-T) T) :=
  h.history.isSmoothFamilyOn_extendedVelocity hα hα1

/-- Below the order `k`, the derivatives of the field are `α`-Hölder on the closed half-plane
with constant `2 c_v Nlow`. -/
theorem norm_iteratedFDeriv_sub_le_of_lt (h : IsTopBoundedHistory k ω T α R B Nlow P)
    (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc (-T) T) {i : ℕ} (hi : i < k) {y z : ℝ^2}
    (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖iteratedFDeriv ℝ i (extendedVelocity (k + 1) (ω r)) y -
        iteratedFDeriv ℝ i (extendedVelocity (k + 1) (ω r)) z‖ ≤
      2 * fieldBound k α R Nlow * ‖y - z‖ ^ α := by
  have hc : ContDiff ℝ (i + 1) (extendedVelocity (k + 1) (ω r)) :=
    ((h.isSmoothFamilyOn hα hα1).contDiff hr).of_le (by exact_mod_cast (by omega : i + 1 ≤ k + 1))
  have hN := h.low.nonneg hr
  have hc0 : 0 ≤ fieldBound k α R Nlow := mul_nonneg (velocityConst_nonneg k hα R) hN
  have hm := norm_sub_le_max_mul_rpow (f := iteratedFDeriv ℝ i (extendedVelocity (k + 1) (ω r)))
    (S := H̄) (L := fieldBound k α R Nlow) (M := fieldBound k α R Nlow) (fun y hy z hz ↦ by
      rw [dist_eq_norm]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane hc
        (fun w hw ↦ h.norm_iteratedFDeriv_le hα hα1 hr (by omega) hw) hy hz)
    (fun y hy ↦ h.norm_iteratedFDeriv_le hα hα1 hr hi.le hy) hα.le hα1.le hy hz
  rwa [max_eq_right (by linarith), dist_eq_norm] at hm

/-! ### The flow maps up to the order `k` -/

/-- The flow maps preserve the closed half-plane. -/
theorem mapsTo_flowOn (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α) (hα1 : α < 1)
    {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    MapsTo (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) H̄ H̄ :=
  mapsTo_flowOn_extendedVelocity (h.history.toIsVorticityHistory hα.le hα1.le)
    (h.history.isC1FieldOn_extendedVelocity hα hα1).isLipschitzFieldOn hs ht

/-- The flow maps are `C^{k+1}`. -/
theorem contDiff_flowOn (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α) (hα1 : α < 1)
    {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    ContDiff ℝ (k + 1) (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) :=
  (h.history.isC1FieldOn_extendedVelocity hα hα1).contDiff_flowOn_of_family
    (h.isSmoothFamilyOn hα hα1) hs ht

/-- **The derivatives of orders `1 ≤ j ≤ k` of the flow maps** are at most `flowBound` on the
closed half-plane. -/
theorem norm_iteratedFDeriv_flowOn_le (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ k) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDeriv ℝ j (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) x‖ ≤
      flowBound k α R Nlow T := by
  have hv := h.history.isC1FieldOn_extendedVelocity hα hα1
  have hN := h.low.nonneg ht
  refine (hv.norm_iteratedFDeriv_flowOn_le_flowDerivBound
    ((h.isSmoothFamilyOn hα hα1).mono (Nat.le_succ k)) ht
    (fun s hs t ht ↦ h.mapsTo_flowOn hα hα1 hs ht)
    (fun _ ↦ mul_nonneg (velocityConst_nonneg k hα R) hN)
    (fun i _ hik r hr y hy ↦ h.norm_iteratedFDeriv_le hα hα1 hr hik hy) hj hjk hx hs).trans ?_
  exact flowDerivBound_mono _ _ hj hjk

/-- The flow maps are `flowBound`-Lipschitz on the closed half-plane. -/
theorem norm_flowOn_sub_le (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) (hk : 1 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T)
    {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t x -
        flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t y‖ ≤
      flowBound k α R Nlow T * ‖x - y‖ := by
  have hc := h.contDiff_flowOn hα hα1 hs ht
  refine convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (hc.differentiable (by simp)).differentiableAt) (fun z hz ↦ ?_) hy hx
  rw [← norm_iteratedFDeriv_one]
  exact h.norm_iteratedFDeriv_flowOn_le hα hα1 hs ht le_rfl hk hz

/-- Below the order `k`, the derivatives of the flow maps are `flowBound`-Lipschitz on the closed
half-plane. -/
theorem norm_iteratedFDeriv_flowOn_sub_le_of_lt (h : IsTopBoundedHistory k ω T α R B Nlow P)
    (hα : 0 < α) (hα1 : α < 1) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) {i : ℕ}
    (hi : i < k) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ i (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) x -
        iteratedFDeriv ℝ i (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) y‖ ≤
      flowBound k α R Nlow T * ‖x - y‖ :=
  norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
    ((h.contDiff_flowOn hα hα1 hs ht).of_le (by exact_mod_cast (by omega : i + 1 ≤ k + 1)))
    (fun z hz ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hs ht (by omega) (by omega) hz) hx hy

/-- **The Hölder constant of the derivatives of orders `1 ≤ j ≤ k` of the flow maps**:
`flowHolder`, for `k ≥ 2`. -/
theorem norm_iteratedFDeriv_flowOn_sub_le (h : IsTopBoundedHistory k ω T α R B Nlow P)
    (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T)
    (ht : t ∈ Icc (-T) T) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x y : ℝ^2} (hx : 0 ≤ x 1)
    (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ j (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) x -
        iteratedFDeriv ℝ j (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) y‖ ≤
      flowHolder k α R Nlow T * ‖x - y‖ ^ α := by
  set v := fun r ↦ extendedVelocity (k + 1) (ω r)
  set c := fieldBound k α R Nlow
  set F := flowBound k α R Nlow T
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  have hN := h.low_nonneg hT
  have hc0 : 0 ≤ c := h.fieldBound_nonneg hα hT
  have hF0 : 0 ≤ F := flowBound_nonneg (by omega)
  have hch : 0 ≤ velocityHolderConst k α * Nlow :=
    mul_nonneg (velocityHolderConst_nonneg k hα hα1) hN
  set ρ := flowHolderRate k α c c c F F F F F c (velocityHolderConst k α * Nlow)
  have hρ : 0 ≤ ρ := flowHolderRate_nonneg hc0 hc0 hc0 hF0 hF0 hF0 hF0 hc0 hch
  have hτ : |s - t| ≤ T - -T := abs_sub_le_iff.mpr ⟨by linarith [hs.2, ht.1],
    by linarith [hs.1, ht.2]⟩
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  have hX0 : 0 ≤ (T - -T) * ρ * Real.exp (c * (T - -T)) :=
    mul_nonneg (mul_nonneg (by linarith) hρ) (Real.exp_pos _).le
  rcases hjk.lt_or_eq with hjk' | hjk'
  · have hm := norm_sub_le_max_mul_rpow
      (f := iteratedFDeriv ℝ j (flowOn v (-T) T s t)) (S := H̄) (L := F) (M := F)
      (fun y hy z hz ↦ by
        rw [dist_eq_norm]; exact h.norm_iteratedFDeriv_flowOn_sub_le_of_lt hα hα1 hs ht hjk' hy hz)
      (fun y hy ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hs ht hj hjk'.le hy) hα.le hα1.le hx hy
    rw [max_eq_right (by linarith), dist_eq_norm] at hm
    refine hm.trans (mul_le_mul_of_nonneg_right ?_ hd)
    simp only [flowHolder]
    linarith
  rw [hjk']
  have hv := h.history.isC1FieldOn_extendedVelocity hα hα1
  have hsm : IsSmoothFamilyOn k v (Icc (-T) T) := (h.isSmoothFamilyOn hα hα1).mono (Nat.le_succ k)
  have hcd (r : ℝ) (hr : r ∈ Icc (-T) T) (i : ℕ) (hi : i + 1 ≤ k + 1) :
      ContDiff ℝ (i + 1) (v r) :=
    ((h.isSmoothFamilyOn hα hα1).contDiff hr).of_le (by exact_mod_cast hi)
  have hXd (r : ℝ) (hr : r ∈ Icc (-T) T) (i : ℕ) (hi : i + 1 ≤ k + 1) :
      ContDiff ℝ (i + 1) (flowOn v (-T) T r t) :=
    (h.contDiff_flowOn hα hα1 hr ht).of_le (by exact_mod_cast hi)
  have hb := hv.norm_iteratedFDeriv_flowOn_sub_le_max_rpow hsm ht
    (fun s hs ↦ h.mapsTo_flowOn hα hα1 hs ht) hk hα.le hα1.le (K₁ := c) (K₂ := c) (M := c)
    (M' := c) (L := F) (L₂ := F) (F₀ := F) (Fm := F) (Λ := F) (Km := fun _ ↦ c)
    (Hm := fun _ ↦ velocityHolderConst k α * Nlow)
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]; exact h.norm_iteratedFDeriv_le hα hα1 hr (by omega) hy)
    hc0 (fun r hr y hy i _ hij ↦ h.norm_iteratedFDeriv_le hα hα1 hr hij.le hy)
    (fun r hr y hy ↦ h.norm_iteratedFDeriv_le hα hα1 hr le_rfl hy) continuousOn_const hc0 hc0
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hcd r hr 1 (by omega)) (fun w hw ↦ h.norm_iteratedFDeriv_le hα hα1 hr hk hw) hy hz)
    (fun r hr y hy z hz i _ hij ↦ norm_iteratedFDeriv_sub_le_of_convex
      convex_closedUpperHalfPlane (hcd r hr i (by omega))
      (fun w hw ↦ h.norm_iteratedFDeriv_le hα hα1 hr (by omega) hw) hy hz)
    (fun _ _ ↦ hch) (fun r hr y hy z hz ↦ h.norm_iteratedFDeriv_sub_le hα hα1 (by omega) hr hy hz)
    continuousOn_const
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]
      exact h.norm_iteratedFDeriv_flowOn_le hα hα1 hr ht le_rfl (by omega) hy)
    (fun r hr y hy z hz ↦ h.norm_flowOn_sub_le hα hα1 (by omega) hr ht hy hz)
    (fun r hr y hy i hi hij ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hr ht hi hij.le hy)
    (fun r hr y hy ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hr ht (by omega) le_rfl hy) hF0 hF0
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hXd r hr 1 (by omega)) (fun w hw ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hr ht
          (by omega) hk hw) hy hz)
    (fun r hr y hy z hz i _ hij ↦ h.norm_iteratedFDeriv_flowOn_sub_le_of_lt hα hα1 hr ht hij
      hy hz) hx hy hs
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ hd)
  rw [intervalIntegral.integral_const, smul_eq_mul, abs_mul]
  simp only [flowHolder]
  refine max_le ?_ (by linarith)
  rw [abs_of_nonneg hρ]
  linarith [show |s - t| * ρ * Real.exp (c * |s - t|) ≤ (T - -T) * ρ * Real.exp (c * (T - -T))
    by gcongr; exact mul_nonneg (by linarith) hρ]

/-! ### The derivative of order `k + 1` of the flow maps -/

/-- For `s, t ∈ [-T, T]` the majorant `r ↦ P |r|` is interval integrable between `t` and `s`. -/
theorem intervalIntegrable_abs (h : IsTopBoundedHistory k ω T α R B Nlow P) {s t : ℝ}
    (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    IntervalIntegrable (fun r ↦ P |r|) volume t s :=
  (h.continuousOn_abs.mono (uIcc_subset_Icc ht hs)).intervalIntegrable

/-- **The derivative of order `k + 1` of the flow maps**:
`‖D^{k+1} X(s, t)‖ ≤ flowTopConst + flowTopSlope |∫ₜˢ P(|r|) dr|` on the closed half-plane. -/
theorem norm_iteratedFDeriv_flowOn_top_le (h : IsTopBoundedHistory k ω T α R B Nlow P)
    (hα : 0 < α) (hα1 : α < 1) (hk : 1 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T)
    (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDeriv ℝ (k + 1) (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) x‖ ≤
      flowTopConst k α R Nlow T + flowTopSlope k α R Nlow T * |∫ r in t..s, P (|r|)| := by
  have hv := h.history.isC1FieldOn_extendedVelocity hα hα1
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  set c := fieldBound k α R Nlow
  set F := flowBound k α R Nlow T
  have hc0 : 0 ≤ c := h.fieldBound_nonneg hα hT
  have hcv := velocityConst_nonneg k hα R
  have hb := hv.norm_iteratedFDeriv_flowOn_le_of_top (h.isSmoothFamilyOn hα hα1) ht
    (by omega : 2 ≤ k + 1) (fun s hs t ht ↦ h.mapsTo_flowOn hα hα1 hs ht) (B := fun _ ↦ c)
    (fun _ ↦ hc0) (fun i _ hik r hr y hy ↦ h.norm_iteratedFDeriv_le hα hα1 hr (by omega) hy)
    (Km := fun r ↦ c + velocityConst k α R * P |r|)
    (fun r hr y hy ↦ h.norm_iteratedFDeriv_top_le hα hα1 hr hy)
    (continuousOn_const.add (continuousOn_const.mul h.continuousOn_abs)) hx hs
  rw [abs_integral_const_add_mul (h.intervalIntegrable_abs hs ht)
    (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc ht hs hr)) hc0 hcv, Nat.add_sub_cancel] at hb
  refine hb.trans ?_
  have hτ : |s - t| ≤ T - -T := abs_sub_le_iff.mpr ⟨by linarith [hs.2, ht.1],
    by linarith [hs.1, ht.2]⟩
  have hL1 : flowDerivBound (fun _ ↦ c) (T - -T) 1 ≤ F := flowDerivBound_mono _ _ le_rfl hk
  have hL0 : 0 ≤ flowDerivBound (fun _ ↦ c) (T - -T) 1 := by
    rw [flowDerivBound_one]; exact (Real.exp_pos _).le
  have hΨ : 0 ≤ |∫ r in t..s, P (|r|)| := abs_nonneg _
  have hC : 0 ≤ (Fintype.card (OrderedFinpartition (k + 1)) : ℝ) *
      (lowerFieldBound (fun _ ↦ c) (k + 1) * max 1 F ^ (k + 1)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Finset.sum_nonneg fun _ _ ↦ hc0)
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  have hF0 : 0 ≤ F := flowBound_nonneg hk
  have hτ0 : 0 ≤ T - -T := by linarith
  have e1 : flowDerivBound (fun _ ↦ c) (T - -T) k = F := rfl
  rw [e1] at hb
  calc _ ≤ (F ^ (k + 1) * (c * (T - -T) + velocityConst k α R * |∫ r in t..s, P (|r|)|) +
        (T - -T) * (Fintype.card (OrderedFinpartition (k + 1)) *
          (lowerFieldBound (fun _ ↦ c) (k + 1) * max 1 F ^ (k + 1)))) *
        Real.exp (c * (T - -T)) := by
        refine mul_le_mul (add_le_add (mul_le_mul (pow_le_pow_left₀ hL0 hL1 _)
          (add_le_add (mul_le_mul_of_nonneg_left hτ hc0) le_rfl)
          (add_nonneg (mul_nonneg hc0 (abs_nonneg _)) (mul_nonneg hcv hΨ)) (pow_nonneg hF0 _))
          (mul_le_mul_of_nonneg_right hτ hC))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ hc0)) (Real.exp_pos _).le
          (add_nonneg (mul_nonneg (pow_nonneg hF0 _) (add_nonneg (mul_nonneg hc0 hτ0)
            (mul_nonneg hcv hΨ))) (mul_nonneg hτ0 hC))
    _ = _ := by simp only [flowTopConst, flowTopSlope, c, F]; ring

/-- **The Hölder constant of the derivative of order `k + 1` of the flow maps**:
`flowTopHolderConst + flowTopHolderSlope |∫ₜˢ P(|r|) dr|`, for `k ≥ 2`. -/
theorem norm_iteratedFDeriv_flowOn_top_sub_le (h : IsTopBoundedHistory k ω T α R B Nlow P)
    (hα : 0 < α) (hα1 : α < 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T)
    (ht : t ∈ Icc (-T) T) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ (k + 1) (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) x -
        iteratedFDeriv ℝ (k + 1)
          (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) y‖ ≤
      (flowTopHolderConst k α R Nlow T +
        flowTopHolderSlope k α R Nlow T * |∫ r in t..s, P (|r|)|) * ‖x - y‖ ^ α := by
  set v := fun r ↦ extendedVelocity (k + 1) (ω r)
  have hv := h.history.isC1FieldOn_extendedVelocity hα hα1
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  have hN := h.low_nonneg hT
  set c := fieldBound k α R Nlow
  set F := flowBound k α R Nlow T
  set A₃ := flowTopConst k α R Nlow T
  set C₃ := flowTopSlope k α R Nlow T
  set Hf := flowHolder k α R Nlow T
  set M' := fieldHolder k α R Nlow
  have hc0 : 0 ≤ c := h.fieldBound_nonneg hα hT
  have hcv := velocityConst_nonneg k hα R
  have hch := velocityHolderConst_nonneg k hα hα1
  have hF0 : 0 ≤ F := flowBound_nonneg (by omega)
  have hE0 : 0 ≤ Real.exp (c * (T - -T)) := (Real.exp_pos _).le
  have hτ0 : 0 ≤ T - -T := by linarith
  have hA₃ : 0 ≤ A₃ := flowTopConst_nonneg hc0 hF0 hτ0
  have hC₃ : 0 ≤ C₃ := flowTopSlope_nonneg hcv hF0
  have hM'0 : 0 ≤ M' := fieldHolder_nonneg hc0 hch hN
  have hHf0 : 0 ≤ Hf := flowHolder_nonneg hc0 hF0 hch hN hτ0
  have hτ (r : ℝ) (hr : r ∈ Icc (-T) T) : |r - t| ≤ T - -T :=
    abs_sub_le_iff.mpr ⟨by linarith [hr.2, ht.1], by linarith [hr.1, ht.2]⟩
  set Fm : ℝ → ℝ := fun r ↦ A₃ + C₃ * |∫ r' in t..r, P (|r'|)|
  have hFmc : ContinuousOn Fm (Icc (-T) T) := by
    have hint : IntervalIntegrable (fun r ↦ P |r|) volume (-T) T :=
      (h.continuousOn_abs.mono (uIcc_subset_Icc ⟨le_rfl, by linarith⟩
        ⟨by linarith, le_rfl⟩)).intervalIntegrable
    have hp := intervalIntegral.continuousOn_primitive_interval' hint
      (by rw [uIcc_of_le (by linarith)]; exact ht)
    rw [uIcc_of_le (by linarith)] at hp
    exact continuousOn_const.add (continuousOn_const.mul hp.abs)
  have hcd (r : ℝ) (hr : r ∈ Icc (-T) T) (i : ℕ) (hi : i + 1 ≤ k + 1) :
      ContDiff ℝ (i + 1) (v r) :=
    ((h.isSmoothFamilyOn hα hα1).contDiff hr).of_le (by exact_mod_cast hi)
  have hXd (r : ℝ) (hr : r ∈ Icc (-T) T) (i : ℕ) (hi : i + 1 ≤ k + 1) :
      ContDiff ℝ (i + 1) (flowOn v (-T) T r t) :=
    (h.contDiff_flowOn hα hα1 hr ht).of_le (by exact_mod_cast hi)
  have hb := hv.norm_iteratedFDeriv_flowOn_sub_le_max_rpow_of_holder (h.isSmoothFamilyOn hα hα1)
    ht (fun s hs ↦ h.mapsTo_flowOn hα hα1 hs ht) (by omega : 2 ≤ k + 1) hα.le hα1.le
    (K₁ := c) (K₂ := c) (M := c) (M' := M') (L := F) (L₂ := F) (F₀ := F) (Λ := Hf)
    (Km := fun r ↦ c + velocityConst k α R * P |r|)
    (Hm := fun r ↦ velocityHolderConst k α * P |r|) (Fm := Fm)
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]; exact h.norm_iteratedFDeriv_le hα hα1 hr (by omega) hy)
    hc0 (fun r hr y hy i _ hij ↦ h.norm_iteratedFDeriv_le hα hα1 hr (by omega) hy)
    (fun r hr y hy ↦ h.norm_iteratedFDeriv_top_le hα hα1 hr hy)
    (continuousOn_const.add (continuousOn_const.mul h.continuousOn_abs)) hc0 hM'0
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hcd r hr 1 (by omega)) (fun w hw ↦ h.norm_iteratedFDeriv_le hα hα1 hr hk hw) hy hz)
    (fun r hr y hy z hz i _ hij ↦ by
      rcases (show i < k ∨ i = k by omega) with hik | rfl
      · refine (h.norm_iteratedFDeriv_sub_le_of_lt hα hα1 hr hik hy hz).trans
          (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α))
        simp only [M', fieldHolder]
        nlinarith [mul_nonneg hch hN]
      · refine (h.norm_iteratedFDeriv_sub_le hα hα1 (by omega) hr hy hz).trans
          (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α))
        simp only [M', fieldHolder]
        linarith)
    (fun r hr ↦ mul_nonneg hch (h.nonneg_abs hr))
    (fun r hr y hy z hz ↦ h.norm_iteratedFDeriv_top_sub_le hα hα1 hr hy hz)
    (continuousOn_const.mul h.continuousOn_abs)
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]
      exact h.norm_iteratedFDeriv_flowOn_le hα hα1 hr ht le_rfl (by omega) hy)
    (fun r hr y hy z hz ↦ h.norm_flowOn_sub_le hα hα1 (by omega) hr ht hy hz)
    (fun r hr y hy i hi hij ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hr ht hi (by omega) hy)
    (fun r hr y hy ↦ h.norm_iteratedFDeriv_flowOn_top_le hα hα1 (by omega) hr ht hy) hFmc hHf0
    hF0
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hXd r hr 1 (by omega)) (fun w hw ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hr ht
          (by omega) hk hw) hy hz)
    (fun r hr y hy z hz i hi hij ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα hα1 hk hr ht hi
      (by omega) hy hz) hx hy hs
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α))
  set Ψ := |∫ r in t..s, P (|r|)|
  have hΨ : 0 ≤ Ψ := abs_nonneg _
  -- the rate is affine in `P(|r|)` between `t` and `s`
  set A' := c * F * (A₃ + C₃ * Ψ) + flowTopRateConst k α R Nlow T
  have hR0 : 0 ≤ flowTopRateConst k α R Nlow T := flowTopRateConst_nonneg hc0 hF0 hHf0 hM'0
  have hA' : 0 ≤ A' := by positivity
  have hB' : 0 ≤ flowTopRateSlope k α R Nlow T := flowTopRateSlope_nonneg hcv hch hF0
  have hρ : ∀ r ∈ uIcc t s, ‖flowHolderRateOfHolder (k + 1) α c c M' F F F Hf (Fm r)
      (c + velocityConst k α R * P |r|) (velocityHolderConst k α * P |r|)‖ ≤
        A' + flowTopRateSlope k α R Nlow T * P |r| := by
    intro r hr
    have hr' := uIcc_subset_Icc ht hs hr
    have hP := h.nonneg_abs hr'
    have hFmr : Fm r ≤ A₃ + C₃ * Ψ := by
      simp only [Fm]
      gcongr
      exact abs_integral_le_of_mem_uIcc (h.intervalIntegrable_abs hs ht)
        (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc ht hs hr)) hr
    have hFm0 : 0 ≤ Fm r := by simp only [Fm]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold flowHolderRateOfHolder; positivity)]
    simp only [flowHolderRateOfHolder, A', flowTopRateConst, flowTopRateSlope, Nat.add_sub_cancel]
    have h1 : c * F * Fm r ≤ c * F * (A₃ + C₃ * Ψ) := by gcongr
    nlinarith [mul_nonneg hP hcv, mul_nonneg hP hch]
  have hI := norm_integral_le_const_add_mul (h.intervalIntegrable_abs hs ht)
    (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc ht hs hr)) hA' hB' hρ
  rw [Real.norm_eq_abs] at hI
  have hst := hτ s hs
  have hexp : Real.exp (c * |s - t|) ≤ Real.exp (c * (T - -T)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc0)
  refine max_le ?_ ?_
  · calc _ ≤ (A' * (T - -T) + flowTopRateSlope k α R Nlow T * Ψ) * Real.exp (c * (T - -T)) :=
          mul_le_mul (hI.trans (by gcongr)) hexp (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by
          simp only [flowTopHolderConst, flowTopHolderSlope, A', A₃, C₃, c, F]
          nlinarith [mul_nonneg hA₃ hE0, mul_nonneg hC₃ hΨ]
  · simp only [Fm, flowTopHolderConst, flowTopHolderSlope]
    have : 0 ≤ (c * F * A₃ + flowTopRateConst k α R Nlow T) * (T - -T) *
        Real.exp (c * (T - -T)) := by positivity
    have : 0 ≤ (c * F * C₃ * (T - -T) + flowTopRateSlope k α R Nlow T) *
        Real.exp (c * (T - -T)) * Ψ := by positivity
    nlinarith

/-! ### The bounds of the flow maps on the closed half-plane -/

/-- **The `C^{k,α}` bounds of the flow maps** on the closed half-plane, for `k ≥ 2`. -/
theorem hasHolderBounds_flowOn (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) α
      (flowBound k α R Nlow T) (flowHolder k α R Nlow T) (flowBound k α R Nlow T)
      (flowHolder k α R Nlow T) :=
  HasHolderBounds.of_contDiff ((h.contDiff_flowOn hα hα1 hs ht).of_le (by
      exact_mod_cast Nat.le_succ k))
    (fun j hj hjk z hz ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hs ht hj hjk.le hz)
    (fun j hj hjk z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα hα1 hk hs ht hj hjk.le hz
      hz')
    (fun z hz ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hs ht (by omega) le_rfl hz)
    (fun z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα hα1 hk hs ht (by omega) le_rfl hz
      hz')

/-- **The `C^{k+1,α}` bounds of the flow maps** on the closed half-plane, for `k ≥ 2`: the
top-order constants are affine in `|∫ₜˢ P(|r|) dr|`. -/
theorem hasHolderBounds_flowOn_succ (h : IsTopBoundedHistory k ω T α R B Nlow P) (hα : 0 < α)
    (hα1 : α < 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (flowOn (fun r ↦ extendedVelocity (k + 1) (ω r)) (-T) T s t) α
      (flowBound k α R Nlow T) (flowHolder k α R Nlow T)
      (flowTopConst k α R Nlow T + flowTopSlope k α R Nlow T * |∫ r in t..s, P (|r|)|)
      (flowTopHolderConst k α R Nlow T +
        flowTopHolderSlope k α R Nlow T * |∫ r in t..s, P (|r|)|) :=
  HasHolderBounds.of_contDiff (by exact_mod_cast h.contDiff_flowOn hα hα1 hs ht)
    (fun j hj hjk z hz ↦ h.norm_iteratedFDeriv_flowOn_le hα hα1 hs ht hj (by omega) hz)
    (fun j hj hjk z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα hα1 hk hs ht hj (by omega)
      hz hz')
    (fun z hz ↦ h.norm_iteratedFDeriv_flowOn_top_le hα hα1 (by omega) hs ht hz)
    (fun z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_top_sub_le hα hα1 hk hs ht hz hz')

end IsTopBoundedHistory

end IncompressibleFlow
