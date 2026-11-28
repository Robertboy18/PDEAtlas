/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.FieldHigher
public import PDE.Fluid.Incompressible.HalfPlane.FlowHigher
import PDE.Analysis.Calculus.HolderInterpolation
import PDE.Analysis.Calculus.IntegralMajorant

/-!
# Flow bounds at level `k`

The flow of a velocity field with `k + 1` spatial derivatives has `k + 1` derivatives too. This
module proves that when the top-order derivative of the field is bounded at each time by a function
`P` of time, the top-order derivative of the flow is bounded affinely in the time integral of `P`.
That affine bound is what makes the propagation of regularity a linear problem.

A field `v` on the times `[-T, T]` has level-`k` bounds with the constants `c, c'` and the majorant
`P` (`IsTopBoundedField k v T α c c' P`) if it is a smooth family of order `k + 1` and a `C¹` field
whose flows preserve the closed half-plane `H̄`, and on `H̄` its derivatives of order at most `k`
are at most `c`, its derivative of order `k` is `α`-Hölder with constant `c`, and its derivative of
order `k + 1` at time `r` is at most `c + c' P(|r|)` and `α`-Hölder with constant `c + c' P(|r|)`,
for a function `P ≥ 0` continuous on `[0, T]`.

The flow maps `X = flowOn v (-T) T s t` then have, on `H̄`, derivatives of orders `1 ≤ j ≤ k` at
most `flowBound k c T` and `α`-Hölder with constant `flowHolder k α c T`; the derivative of order
`k + 1` is at most `flowTopConst + flowTopSlope |∫ₜˢ P(|r|) dr|` and `α`-Hölder with constant
`flowTopHolderConst + flowTopHolderSlope |∫ₜˢ P(|r|) dr|`, with coefficients depending only on
`k, α, c, c', T`. The derivative of order `j` of the flow solves a linear equation in time whose
forcing contains the derivatives of the field up to the order `j` and the derivatives of the flow of
lower order. In the equation of order `k + 1` the top-order derivative of the field appears once,
multiplied by `k + 1` first derivatives of the flow, so Grönwall's inequality gives a bound affine
in `∫ P`. The constants are explicit but large: they contain the number of ordered partitions of a
set with `k + 1` elements and exponentials of `c T`.

For a velocity law `U` and a `C^{k,α}` history `ω`, `k ≥ 2`, `0 < α < 1`, with lower-order bound
`Nlow` and top-order majorant `P` (`IncompressibleFlow.IsTopBoundedHistory`), the extensions of
order `k + 1` of the fields of the law have level-`k` bounds with `c = lawConst C k α · Nlow` and
`c' = lawConst C k α`, where `lawConst C k α = C (k - 1) α + C k α`: the bounds of the law of order
`k - 1` give the derivatives up to the order `k`, those of order `k`, with the bound `Nlow + P(|r|)`
of the history at time `r`, the derivative of order `k + 1`.

## Main results

* `IsTopBoundedField`: fields with level-`k` bounds.
* `IsTopBoundedField.norm_iteratedFDeriv_flowOn_le`,
  `IsTopBoundedField.norm_iteratedFDeriv_flowOn_sub_le`: the bound `flowBound` and the Hölder
  constant `flowHolder` of the derivatives of orders `1 ≤ j ≤ k` of the flow maps on `H̄`.
* `IsTopBoundedField.norm_iteratedFDeriv_flowOn_top_le`,
  `IsTopBoundedField.norm_iteratedFDeriv_flowOn_top_sub_le`: the bound and the Hölder constant of
  the derivative of order `k + 1`, affine in `|∫ₜˢ P(|r|) dr|`.
* `IsTopBoundedField.hasHolderBounds_flowOn`, `IsTopBoundedField.hasHolderBounds_flowOn_succ`: the
  `C^{k,α}` and `C^{k+1,α}` bounds of the flow maps on `H̄`, for `k ≥ 2`.
* `IncompressibleFlow.IsTopBoundedHistory.isTopBoundedField_law`: the extensions of the fields of a
  law have level-`k` bounds.
* `lawConst` and the constants `flowBound`, `flowHolder`, `flowTopConst`, `flowTopSlope`,
  `flowTopHolderConst`, `flowTopHolderSlope`.

`CarriedHigherForcing.lean` and `CarriedHigher.lean` compose the data with these flow maps and
obtain the bounds of the carried temperature and of the carried vorticity at level `k`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal
open PDE.Analysis PDE.Analysis.ODE
open IncompressibleFlow (flowHolderRate_nonneg)

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The constants -/

/-- The bound of the derivatives of orders `1 ≤ j ≤ k` of the flow maps over `[-T, T]`. -/
def flowBound (k : ℕ) (c T : ℝ) : ℝ :=
  flowDerivBound (fun _ ↦ c) (T - -T) k

/-- The Hölder constant of the derivatives of orders `1 ≤ j ≤ k` of the flow maps over
`[-T, T]`. -/
def flowHolder (k : ℕ) (α c T : ℝ) : ℝ :=
  (T - -T) * flowHolderRate k α c c c (flowBound k c T) (flowBound k c T) (flowBound k c T)
      (flowBound k c T) (flowBound k c T) c c * Real.exp (c * (T - -T)) +
    2 * flowBound k c T

/-- The constant term of the bound of the derivative of order `k + 1` of the flow maps. -/
def flowTopConst (k : ℕ) (c T : ℝ) : ℝ :=
  (flowBound k c T ^ (k + 1) * (c * (T - -T)) +
      (T - -T) * (Fintype.card (OrderedFinpartition (k + 1)) *
        (lowerFieldBound (fun _ ↦ c) (k + 1) * max 1 (flowBound k c T) ^ (k + 1)))) *
    Real.exp (c * (T - -T))

/-- The coefficient of `|∫ₜˢ P(|r|) dr|` in the bound of the derivative of order `k + 1` of the
flow maps. -/
def flowTopSlope (k : ℕ) (c c' T : ℝ) : ℝ :=
  flowBound k c T ^ (k + 1) * c' * Real.exp (c * (T - -T))

/-- The part of the rate of the top Hölder constant of the flow maps that does not grow with the
majorant. -/
def flowTopRateConst (k : ℕ) (α c T : ℝ) : ℝ :=
  c * ((k + 1 : ℕ) : ℝ) * flowBound k c T ^ k * flowBound k c T +
    c * flowBound k c T ^ α * flowBound k c T ^ (k + 1) +
    Fintype.card (OrderedFinpartition (k + 1)) *
      ((c * ((k + 1 : ℕ) : ℝ) * flowHolder k α c T + 2 * c * flowBound k c T ^ α) *
        max 1 (flowBound k c T) ^ (k + 1))

/-- The coefficient of `P(|r|)` in the rate of the top Hölder constant of the flow maps. -/
def flowTopRateSlope (k : ℕ) (α c c' T : ℝ) : ℝ :=
  c' * ((k + 1 : ℕ) : ℝ) * flowBound k c T ^ k * flowBound k c T +
    c' * flowBound k c T ^ α * flowBound k c T ^ (k + 1)

/-- The constant term of the Hölder constant of the derivative of order `k + 1` of the flow
maps. -/
def flowTopHolderConst (k : ℕ) (α c T : ℝ) : ℝ :=
  (c * flowBound k c T * flowTopConst k c T + flowTopRateConst k α c T) * (T - -T) *
      Real.exp (c * (T - -T)) +
    2 * flowTopConst k c T

/-- The coefficient of `|∫ₜˢ P(|r|) dr|` in the Hölder constant of the derivative of order
`k + 1` of the flow maps. -/
def flowTopHolderSlope (k : ℕ) (α c c' T : ℝ) : ℝ :=
  (c * flowBound k c T * flowTopSlope k c c' T * (T - -T) + flowTopRateSlope k α c c' T) *
      Real.exp (c * (T - -T)) +
    2 * flowTopSlope k c c' T

/-- The flow bound of order `k ≥ 1` is nonnegative. -/
theorem flowBound_nonneg {k : ℕ} (c T : ℝ) (hk : 1 ≤ k) : 0 ≤ flowBound k c T := by
  have h1 := flowDerivBound_mono (fun _ ↦ c) (T - -T) le_rfl hk
  rw [flowDerivBound_one] at h1
  exact (Real.exp_pos _).le.trans h1

/-- The Hölder constant `flowHolder` of the flow is nonnegative. -/
theorem flowHolder_nonneg {k : ℕ} {α c T : ℝ} (hc : 0 ≤ c) (hF : 0 ≤ flowBound k c T)
    (hτ : 0 ≤ T - -T) : 0 ≤ flowHolder k α c T := by
  unfold flowHolder
  have := flowHolderRate_nonneg (m := k) (α := α) (F₀ := flowBound k c T) hc hc hc hF hF hF hF hc
    hc
  positivity

/-- The constant `flowTopConst` of the top-order bound of the flow is nonnegative. -/
theorem flowTopConst_nonneg {k : ℕ} {c T : ℝ} (hc : 0 ≤ c) (hF : 0 ≤ flowBound k c T)
    (hτ : 0 ≤ T - -T) : 0 ≤ flowTopConst k c T := by
  unfold flowTopConst
  have : 0 ≤ lowerFieldBound (fun _ ↦ c) (k + 1) := Finset.sum_nonneg fun _ _ ↦ hc
  positivity

/-- The slope `flowTopSlope` of the top-order bound of the flow is nonnegative. -/
theorem flowTopSlope_nonneg {k : ℕ} {c c' T : ℝ} (hc' : 0 ≤ c') (hF : 0 ≤ flowBound k c T) :
    0 ≤ flowTopSlope k c c' T := by
  unfold flowTopSlope; positivity

/-- The constant `flowTopRateConst` of the top-order rate of the flow is nonnegative. -/
theorem flowTopRateConst_nonneg {k : ℕ} {α c T : ℝ} (hc : 0 ≤ c) (hF : 0 ≤ flowBound k c T)
    (hHf : 0 ≤ flowHolder k α c T) : 0 ≤ flowTopRateConst k α c T := by
  unfold flowTopRateConst; positivity

/-- The slope `flowTopRateSlope` of the top-order rate of the flow is nonnegative. -/
theorem flowTopRateSlope_nonneg {k : ℕ} {α c c' T : ℝ} (hc' : 0 ≤ c')
    (hF : 0 ≤ flowBound k c T) : 0 ≤ flowTopRateSlope k α c c' T := by
  unfold flowTopRateSlope; positivity

/-- The slope `flowTopHolderSlope` of the top-order Hölder bound of the flow is nonnegative. -/
theorem flowTopHolderSlope_nonneg {k : ℕ} {α c c' T : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hF : 0 ≤ flowBound k c T) (hτ : 0 ≤ T - -T) : 0 ≤ flowTopHolderSlope k α c c' T := by
  have := flowTopSlope_nonneg (c := c) (T := T) (k := k) hc' hF
  have := flowTopRateSlope_nonneg (α := α) (c := c) (T := T) (k := k) hc' hF
  unfold flowTopHolderSlope; positivity

/-! ### Fields with level-`k` bounds -/

/-- A field on the times `[-T, T]` with **level-`k` bounds** `c, c'` and majorant `P`: a smooth
family of order `k + 1` and a `C¹` field whose flows preserve the closed half-plane, with, on the
closed half-plane, derivatives of order at most `k` bounded by `c`, the derivative of order `k`
`α`-Hölder with constant `c`, and the derivative of order `k + 1` at time `r` bounded by
`c + c' P(|r|)` and `α`-Hölder with constant `c + c' P(|r|)`, for `c' ≥ 0` and a function
`P ≥ 0` continuous on `[0, T]`. -/
structure IsTopBoundedField (k : ℕ) (v : ℝ → ℝ^2 → ℝ^2) (T α c c' : ℝ) (P : ℝ → ℝ) :
    Prop where
  /-- Smoothness of order `k + 1`. -/
  smooth : IsSmoothFamilyOn (k + 1) v (Icc (-T) T)
  /-- The field is a `C¹` field. -/
  isC1FieldOn : ∃ L : ℝ≥0, IsC1FieldOn v (fun r x ↦ fderiv ℝ (v r) x) (-T) T L
  /-- The flows preserve the closed half-plane. -/
  mapsTo : ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T, MapsTo (flowOn v (-T) T s t) H̄ H̄
  /-- The majorant is continuous on `[0, T]`. -/
  continuousOn : ContinuousOn P (Icc 0 T)
  /-- The majorant is nonnegative on `[0, T]`. -/
  nonneg : ∀ r ∈ Icc 0 T, 0 ≤ P r
  /-- The coefficient of the majorant is nonnegative. -/
  slope_nonneg : 0 ≤ c'
  /-- The derivatives of order at most `k`. -/
  norm_le : ∀ r ∈ Icc (-T) T, ∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDeriv ℝ j (v r) y‖ ≤ c
  /-- The Hölder constant of the derivative of order `k`. -/
  holder : ∀ r ∈ Icc (-T) T, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖iteratedFDeriv ℝ k (v r) y - iteratedFDeriv ℝ k (v r) z‖ ≤ c * ‖y - z‖ ^ α
  /-- The derivative of order `k + 1`. -/
  norm_top_le : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 →
    ‖iteratedFDeriv ℝ (k + 1) (v r) y‖ ≤ c + c' * P |r|
  /-- The Hölder constant of the derivative of order `k + 1`. -/
  holder_top : ∀ r ∈ Icc (-T) T, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
    ‖iteratedFDeriv ℝ (k + 1) (v r) y - iteratedFDeriv ℝ (k + 1) (v r) z‖ ≤
      (c + c' * P |r|) * ‖y - z‖ ^ α

namespace IsTopBoundedField

variable {k : ℕ} {v : ℝ → ℝ^2 → ℝ^2} {T α c c' : ℝ} {P : ℝ → ℝ}

/-- The majorant of a field with top-order bounds is nonnegative at `|t|` for the times of
`[-T, T]`. -/
theorem nonneg_abs (h : IsTopBoundedField k v T α c c' P) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    0 ≤ P |t| :=
  h.nonneg _ (IncompressibleFlow.IsTopBoundedHistory.abs_mem_Icc ht)

/-- The constant `c` of a field with top-order bounds is nonnegative. -/
theorem const_nonneg (h : IsTopBoundedField k v T α c c' P) (hT : 0 ≤ T) : 0 ≤ c :=
  (norm_nonneg _).trans (h.norm_le 0 ⟨by linarith, hT⟩ 0 (Nat.zero_le k) 0 (by simp))

/-- The majorant along the times of `[-T, T]` is continuous. -/
theorem continuousOn_abs (h : IsTopBoundedField k v T α c c' P) :
    ContinuousOn (fun r ↦ P |r|) (Icc (-T) T) :=
  h.continuousOn.comp continuous_abs.continuousOn fun _ hr ↦
    IncompressibleFlow.IsTopBoundedHistory.abs_mem_Icc hr

/-- The majorant along `|r|` is interval integrable between two times of `[-T, T]`. -/
theorem intervalIntegrable_abs (h : IsTopBoundedField k v T α c c' P) {s t : ℝ}
    (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    IntervalIntegrable (fun r ↦ P |r|) volume t s :=
  (h.continuousOn_abs.mono (uIcc_subset_Icc ht hs)).intervalIntegrable

/-- Below the order `k`, the derivatives of the field are `α`-Hölder on the closed half-plane
with constant `2c`. -/
theorem norm_iteratedFDeriv_sub_le_of_lt (h : IsTopBoundedField k v T α c c' P) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {r : ℝ} (hr : r ∈ Icc (-T) T) {i : ℕ} (hi : i < k) {y z : ℝ^2}
    (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖iteratedFDeriv ℝ i (v r) y - iteratedFDeriv ℝ i (v r) z‖ ≤ 2 * c * ‖y - z‖ ^ α := by
  have hc : ContDiff ℝ (i + 1) (v r) :=
    (h.smooth.contDiff hr).of_le (by exact_mod_cast (by omega : i + 1 ≤ k + 1))
  have hc0 := h.const_nonneg (by linarith [hr.1, hr.2])
  have hm := norm_sub_le_max_mul_rpow (f := iteratedFDeriv ℝ i (v r)) (S := H̄) (L := c) (M := c)
    (fun y hy z hz ↦ by
      rw [dist_eq_norm]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane hc
        (fun w hw ↦ h.norm_le r hr (i + 1) (by omega) w hw) hy hz)
    (fun y hy ↦ h.norm_le r hr i hi.le y hy) hα0 hα1 hy hz
  rwa [max_eq_right (by linarith), dist_eq_norm] at hm

/-! ### The flow maps up to the order `k` -/

/-- The flow maps are `C^{k+1}`. -/
theorem contDiff_flowOn (h : IsTopBoundedField k v T α c c' P) {s t : ℝ} (hs : s ∈ Icc (-T) T)
    (ht : t ∈ Icc (-T) T) : ContDiff ℝ (k + 1) (flowOn v (-T) T s t) := by
  obtain ⟨L, hv⟩ := h.isC1FieldOn
  exact hv.contDiff_flowOn_of_family h.smooth hs ht

/-- **The derivatives of orders `1 ≤ j ≤ k` of the flow maps** are at most `flowBound` on the
closed half-plane. -/
theorem norm_iteratedFDeriv_flowOn_le (h : IsTopBoundedField k v T α c c' P) {s t : ℝ}
    (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x : ℝ^2}
    (hx : 0 ≤ x 1) : ‖iteratedFDeriv ℝ j (flowOn v (-T) T s t) x‖ ≤ flowBound k c T := by
  obtain ⟨L, hv⟩ := h.isC1FieldOn
  have hc0 := h.const_nonneg (by linarith [ht.1, ht.2])
  refine (hv.norm_iteratedFDeriv_flowOn_le_flowDerivBound (h.smooth.mono (Nat.le_succ k)) ht
    h.mapsTo (fun _ ↦ hc0) (fun i _ hik r hr y hy ↦ h.norm_le r hr i hik y hy) hj hjk hx
    hs).trans ?_
  exact flowDerivBound_mono _ _ hj hjk

/-- The flow maps are `flowBound`-Lipschitz on the closed half-plane. -/
theorem norm_flowOn_sub_le (h : IsTopBoundedField k v T α c c' P) (hk : 1 ≤ k) {s t : ℝ}
    (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖flowOn v (-T) T s t x - flowOn v (-T) T s t y‖ ≤ flowBound k c T * ‖x - y‖ := by
  have hc := h.contDiff_flowOn hs ht
  refine convex_closedUpperHalfPlane.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ (hc.differentiable (by simp)).differentiableAt) (fun z hz ↦ ?_) hy hx
  rw [← norm_iteratedFDeriv_one]
  exact h.norm_iteratedFDeriv_flowOn_le hs ht le_rfl hk hz

/-- Below the order `k`, the derivatives of the flow maps are `flowBound`-Lipschitz on the closed
half-plane. -/
theorem norm_iteratedFDeriv_flowOn_sub_le_of_lt (h : IsTopBoundedField k v T α c c' P)
    {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) {i : ℕ} (hi : i < k) {x y : ℝ^2}
    (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ i (flowOn v (-T) T s t) x - iteratedFDeriv ℝ i (flowOn v (-T) T s t) y‖ ≤
      flowBound k c T * ‖x - y‖ :=
  norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
    ((h.contDiff_flowOn hs ht).of_le (by exact_mod_cast (by omega : i + 1 ≤ k + 1)))
    (fun z hz ↦ h.norm_iteratedFDeriv_flowOn_le hs ht (by omega) (by omega) hz) hx hy

/-- **The Hölder constant of the derivatives of orders `1 ≤ j ≤ k` of the flow maps**:
`flowHolder`, for `k ≥ 2`. -/
theorem norm_iteratedFDeriv_flowOn_sub_le (h : IsTopBoundedField k v T α c c' P) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) {j : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ j (flowOn v (-T) T s t) x - iteratedFDeriv ℝ j (flowOn v (-T) T s t) y‖ ≤
      flowHolder k α c T * ‖x - y‖ ^ α := by
  obtain ⟨L, hv⟩ := h.isC1FieldOn
  set F := flowBound k c T
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  have hc0 : 0 ≤ c := h.const_nonneg hT
  have hF0 : 0 ≤ F := flowBound_nonneg c T (by omega)
  set ρ := flowHolderRate k α c c c F F F F F c c
  have hρ : 0 ≤ ρ := flowHolderRate_nonneg hc0 hc0 hc0 hF0 hF0 hF0 hF0 hc0 hc0
  have hτ : |s - t| ≤ T - -T := abs_sub_le_iff.mpr ⟨by linarith [hs.2, ht.1],
    by linarith [hs.1, ht.2]⟩
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  have hX0 : 0 ≤ (T - -T) * ρ * Real.exp (c * (T - -T)) :=
    mul_nonneg (mul_nonneg (by linarith) hρ) (Real.exp_pos _).le
  rcases hjk.lt_or_eq with hjk' | hjk'
  · have hm := norm_sub_le_max_mul_rpow
      (f := iteratedFDeriv ℝ j (flowOn v (-T) T s t)) (S := H̄) (L := F) (M := F)
      (fun y hy z hz ↦ by
        rw [dist_eq_norm]; exact h.norm_iteratedFDeriv_flowOn_sub_le_of_lt hs ht hjk' hy hz)
      (fun y hy ↦ h.norm_iteratedFDeriv_flowOn_le hs ht hj hjk'.le hy) hα0 hα1 hx hy
    rw [max_eq_right (by linarith), dist_eq_norm] at hm
    refine hm.trans (mul_le_mul_of_nonneg_right ?_ hd)
    simp only [flowHolder]
    linarith
  rw [hjk']
  have hsm : IsSmoothFamilyOn k v (Icc (-T) T) := h.smooth.mono (Nat.le_succ k)
  have hcd (r : ℝ) (hr : r ∈ Icc (-T) T) (i : ℕ) (hi : i + 1 ≤ k + 1) :
      ContDiff ℝ (i + 1) (v r) :=
    (h.smooth.contDiff hr).of_le (by exact_mod_cast hi)
  have hXd (r : ℝ) (hr : r ∈ Icc (-T) T) (i : ℕ) (hi : i + 1 ≤ k + 1) :
      ContDiff ℝ (i + 1) (flowOn v (-T) T r t) :=
    (h.contDiff_flowOn hr ht).of_le (by exact_mod_cast hi)
  have hb := hv.norm_iteratedFDeriv_flowOn_sub_le_max_rpow hsm ht
    (fun s hs ↦ h.mapsTo s hs t ht) hk hα0 hα1 (K₁ := c) (K₂ := c) (M := c)
    (M' := c) (L := F) (L₂ := F) (F₀ := F) (Fm := F) (Λ := F) (Km := fun _ ↦ c)
    (Hm := fun _ ↦ c)
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]; exact h.norm_le r hr 1 (by omega) y hy)
    hc0 (fun r hr y hy i _ hij ↦ h.norm_le r hr i hij.le y hy)
    (fun r hr y hy ↦ h.norm_le r hr k le_rfl y hy) continuousOn_const hc0 hc0
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hcd r hr 1 (by omega)) (fun w hw ↦ h.norm_le r hr 2 hk w hw) hy hz)
    (fun r hr y hy z hz i _ hij ↦ norm_iteratedFDeriv_sub_le_of_convex
      convex_closedUpperHalfPlane (hcd r hr i (by omega))
      (fun w hw ↦ h.norm_le r hr (i + 1) (by omega) w hw) hy hz)
    (fun _ _ ↦ hc0) (fun r hr y hy z hz ↦ h.holder r hr y z hy hz)
    continuousOn_const
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]
      exact h.norm_iteratedFDeriv_flowOn_le hr ht le_rfl (by omega) hy)
    (fun r hr y hy z hz ↦ h.norm_flowOn_sub_le (by omega) hr ht hy hz)
    (fun r hr y hy i hi hij ↦ h.norm_iteratedFDeriv_flowOn_le hr ht hi hij.le hy)
    (fun r hr y hy ↦ h.norm_iteratedFDeriv_flowOn_le hr ht (by omega) le_rfl hy) hF0 hF0
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hXd r hr 1 (by omega)) (fun w hw ↦ h.norm_iteratedFDeriv_flowOn_le hr ht
          (by omega) hk hw) hy hz)
    (fun r hr y hy z hz i _ hij ↦ h.norm_iteratedFDeriv_flowOn_sub_le_of_lt hr ht hij
      hy hz) hx hy hs
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ hd)
  rw [intervalIntegral.integral_const, smul_eq_mul, abs_mul]
  simp only [flowHolder]
  refine max_le ?_ (by linarith)
  have h1 : |s - t| * |ρ| ≤ (T - -T) * ρ := by
    rw [abs_of_nonneg hρ]; exact mul_le_mul_of_nonneg_right hτ hρ
  have h2 : Real.exp (c * |s - t|) ≤ Real.exp (c * (T - -T)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ hc0)
  have := mul_le_mul h1 h2 (Real.exp_pos _).le (mul_nonneg (by linarith) hρ)
  linarith

/-! ### The derivative of order `k + 1` of the flow maps -/

/-- **The derivative of order `k + 1` of the flow maps**:
`‖D^{k+1} X(s, t)‖ ≤ flowTopConst + flowTopSlope |∫ₜˢ P(|r|) dr|` on the closed half-plane. The
bound is affine in the integral of the majorant, which keeps the top order linear in the
estimates of the carried fields. Proof: the derivative of order `k + 1` of the flow solves a
linear equation in time; the top-order derivative of the field enters its forcing once, with
`k + 1` first derivatives of the flow, and the other terms are bounded without `P`. -/
theorem norm_iteratedFDeriv_flowOn_top_le (h : IsTopBoundedField k v T α c c' P) (hk : 1 ≤ k)
    {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖iteratedFDeriv ℝ (k + 1) (flowOn v (-T) T s t) x‖ ≤
      flowTopConst k c T + flowTopSlope k c c' T * |∫ r in t..s, P (|r|)| := by
  obtain ⟨L, hv⟩ := h.isC1FieldOn
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  set F := flowBound k c T
  have hc0 : 0 ≤ c := h.const_nonneg hT
  have hc' := h.slope_nonneg
  -- The general bound of the top-order derivative of a flow, with the bound `c` of the
  -- derivatives of the field up to the order `k` and `c + c' P(|r|)` of the order `k + 1`.
  have hb := hv.norm_iteratedFDeriv_flowOn_le_of_top h.smooth ht
    (by omega : 2 ≤ k + 1) h.mapsTo (B := fun _ ↦ c)
    (fun _ ↦ hc0) (fun i _ hik r hr y hy ↦ h.norm_le r hr i (by omega) y hy)
    (Km := fun r ↦ c + c' * P |r|)
    (fun r hr y hy ↦ h.norm_top_le r hr y hy)
    (continuousOn_const.add (continuousOn_const.mul h.continuousOn_abs)) hx hs
  -- The time integral of `c + c' P(|r|)` is `c |s - t| + c' |∫ₜˢ P(|r|) dr|`.
  rw [abs_integral_const_add_mul (h.intervalIntegrable_abs hs ht)
    (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc ht hs hr)) hc0 hc', Nat.add_sub_cancel] at hb
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
  have hF0 : 0 ≤ F := flowBound_nonneg c T hk
  have hτ0 : 0 ≤ T - -T := by linarith
  have e1 : flowDerivBound (fun _ ↦ c) (T - -T) k = F := rfl
  rw [e1] at hb
  -- Replace `|s - t|` by the length `2T` of the interval of times; the result is affine in
  -- the integral of the majorant.
  calc _ ≤ (F ^ (k + 1) * (c * (T - -T) + c' * |∫ r in t..s, P (|r|)|) +
        (T - -T) * (Fintype.card (OrderedFinpartition (k + 1)) *
          (lowerFieldBound (fun _ ↦ c) (k + 1) * max 1 F ^ (k + 1)))) *
        Real.exp (c * (T - -T)) := by
        refine mul_le_mul (add_le_add (mul_le_mul (pow_le_pow_left₀ hL0 hL1 _)
          (add_le_add (mul_le_mul_of_nonneg_left hτ hc0) le_rfl)
          (add_nonneg (mul_nonneg hc0 (abs_nonneg _)) (mul_nonneg hc' hΨ)) (pow_nonneg hF0 _))
          (mul_le_mul_of_nonneg_right hτ hC))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ hc0)) (Real.exp_pos _).le
          (add_nonneg (mul_nonneg (pow_nonneg hF0 _) (add_nonneg (mul_nonneg hc0 hτ0)
            (mul_nonneg hc' hΨ))) (mul_nonneg hτ0 hC))
    _ = _ := by simp only [flowTopConst, flowTopSlope, F]; ring

/-- **The Hölder constant of the derivative of order `k + 1` of the flow maps**:
`flowTopHolderConst + flowTopHolderSlope |∫ₜˢ P(|r|) dr|`, for `k ≥ 2`. -/
theorem norm_iteratedFDeriv_flowOn_top_sub_le (h : IsTopBoundedField k v T α c c' P)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T)
    (ht : t ∈ Icc (-T) T) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖iteratedFDeriv ℝ (k + 1) (flowOn v (-T) T s t) x -
        iteratedFDeriv ℝ (k + 1) (flowOn v (-T) T s t) y‖ ≤
      (flowTopHolderConst k α c T + flowTopHolderSlope k α c c' T * |∫ r in t..s, P (|r|)|) *
        ‖x - y‖ ^ α := by
  obtain ⟨L, hv⟩ := h.isC1FieldOn
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  set F := flowBound k c T
  set A₃ := flowTopConst k c T
  set C₃ := flowTopSlope k c c' T
  set Hf := flowHolder k α c T
  have hc0 : 0 ≤ c := h.const_nonneg hT
  have hc' := h.slope_nonneg
  have hF0 : 0 ≤ F := flowBound_nonneg c T (by omega)
  have hE0 : 0 ≤ Real.exp (c * (T - -T)) := (Real.exp_pos _).le
  have hF1 : 0 ≤ max 1 F ^ (k + 1) := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hFα : 0 ≤ F ^ α := Real.rpow_nonneg hF0 α
  have hτ0 : 0 ≤ T - -T := by linarith
  have hA₃ : 0 ≤ A₃ := flowTopConst_nonneg hc0 hF0 hτ0
  have hC₃ : 0 ≤ C₃ := flowTopSlope_nonneg hc' hF0
  have hHf0 : 0 ≤ Hf := flowHolder_nonneg hc0 hF0 hτ0
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
    (h.smooth.contDiff hr).of_le (by exact_mod_cast hi)
  have hXd (r : ℝ) (hr : r ∈ Icc (-T) T) (i : ℕ) (hi : i + 1 ≤ k + 1) :
      ContDiff ℝ (i + 1) (flowOn v (-T) T r t) :=
    (h.contDiff_flowOn hr ht).of_le (by exact_mod_cast hi)
  have hKmc : ContinuousOn (fun r ↦ c + c' * P |r|) (Icc (-T) T) :=
    continuousOn_const.add (continuousOn_const.mul h.continuousOn_abs)
  have hb := hv.norm_iteratedFDeriv_flowOn_sub_le_max_rpow_of_holder h.smooth
    ht (fun s hs ↦ h.mapsTo s hs t ht) (by omega : 2 ≤ k + 1) hα0 hα1
    (K₁ := c) (K₂ := c) (M := c) (M' := 2 * c) (L := F) (L₂ := F) (F₀ := F) (Λ := Hf)
    (Km := fun r ↦ c + c' * P |r|) (Hm := fun r ↦ c + c' * P |r|) (Fm := Fm)
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]; exact h.norm_le r hr 1 (by omega) y hy)
    hc0 (fun r hr y hy i _ hij ↦ h.norm_le r hr i (by omega) y hy)
    (fun r hr y hy ↦ h.norm_top_le r hr y hy) hKmc hc0 (by linarith)
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hcd r hr 1 (by omega)) (fun w hw ↦ h.norm_le r hr 2 hk w hw) hy hz)
    (fun r hr y hy z hz i _ hij ↦ by
      rcases (show i < k ∨ i = k by omega) with hik | rfl
      · exact h.norm_iteratedFDeriv_sub_le_of_lt hα0 hα1 hr hik hy hz
      · exact (h.holder r hr y z hy hz).trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg (norm_nonneg _) α)))
    (fun r hr ↦ add_nonneg hc0 (mul_nonneg hc' (h.nonneg_abs hr)))
    (fun r hr y hy z hz ↦ h.holder_top r hr y z hy hz) hKmc
    (fun r hr y hy ↦ by
      rw [← norm_iteratedFDeriv_one]
      exact h.norm_iteratedFDeriv_flowOn_le hr ht le_rfl (by omega) hy)
    (fun r hr y hy z hz ↦ h.norm_flowOn_sub_le (by omega) hr ht hy hz)
    (fun r hr y hy i hi hij ↦ h.norm_iteratedFDeriv_flowOn_le hr ht hi (by omega) hy)
    (fun r hr y hy ↦ h.norm_iteratedFDeriv_flowOn_top_le (by omega) hr ht hy) hFmc hHf0
    hF0
    (fun r hr y hy z hz ↦ by
      rw [norm_fderiv_sub_eq]
      exact norm_iteratedFDeriv_sub_le_of_convex convex_closedUpperHalfPlane
        (hXd r hr 1 (by omega)) (fun w hw ↦ h.norm_iteratedFDeriv_flowOn_le hr ht
          (by omega) hk hw) hy hz)
    (fun r hr y hy z hz i hi hij ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα0 hα1 hk hr ht hi
      (by omega) hy hz) hx hy hs
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α))
  set Ψ := |∫ r in t..s, P (|r|)|
  have hΨ : 0 ≤ Ψ := abs_nonneg _
  -- the rate is affine in `P(|r|)` between `t` and `s`
  set A' := c * F * (A₃ + C₃ * Ψ) + flowTopRateConst k α c T
  have hR0 : 0 ≤ flowTopRateConst k α c T := flowTopRateConst_nonneg hc0 hF0 hHf0
  have hA' : 0 ≤ A' := by positivity
  have hB' : 0 ≤ flowTopRateSlope k α c c' T := flowTopRateSlope_nonneg hc' hF0
  have hρ : ∀ r ∈ uIcc t s, ‖flowHolderRateOfHolder (k + 1) α c c (2 * c) F F F Hf (Fm r)
      (c + c' * P |r|) (c + c' * P |r|)‖ ≤ A' + flowTopRateSlope k α c c' T * P |r| := by
    intro r hr
    have hr' := uIcc_subset_Icc ht hs hr
    have hP := h.nonneg_abs hr'
    have hFmr : Fm r ≤ A₃ + C₃ * Ψ := by
      simp only [Fm]
      gcongr
      exact abs_integral_le_of_mem_uIcc (h.intervalIntegrable_abs hs ht)
        (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc ht hs hr)) hr
    have hFm0 : 0 ≤ Fm r := by simp only [Fm]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold flowHolderRateOfHolder
      positivity)]
    have h1 : c * F * Fm r ≤ c * F * (A₃ + C₃ * Ψ) := by gcongr
    have e : flowHolderRateOfHolder (k + 1) α c c (2 * c) F F F Hf (Fm r)
        (c + c' * P |r|) (c + c' * P |r|) =
        c * F * Fm r + flowTopRateConst k α c T + flowTopRateSlope k α c c' T * P |r| := by
      simp only [flowHolderRateOfHolder, flowTopRateConst, flowTopRateSlope, Nat.add_sub_cancel]
      ring
    rw [e]
    simp only [A']
    linarith
  have hI := norm_integral_le_const_add_mul (h.intervalIntegrable_abs hs ht)
    (fun r hr ↦ h.nonneg_abs (uIcc_subset_Icc ht hs hr)) hA' hB' hρ
  rw [Real.norm_eq_abs] at hI
  have hst := hτ s hs
  have hexp : Real.exp (c * |s - t|) ≤ Real.exp (c * (T - -T)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc0)
  refine max_le ?_ ?_
  · calc _ ≤ (A' * (T - -T) + flowTopRateSlope k α c c' T * Ψ) * Real.exp (c * (T - -T)) :=
          mul_le_mul (hI.trans (by gcongr)) hexp (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by
          simp only [flowTopHolderConst, flowTopHolderSlope, A', A₃, C₃, F]
          nlinarith [mul_nonneg hA₃ hE0, mul_nonneg hC₃ hΨ]
  · simp only [Fm, flowTopHolderConst, flowTopHolderSlope]
    have : 0 ≤ (c * F * A₃ + flowTopRateConst k α c T) * (T - -T) *
        Real.exp (c * (T - -T)) := by positivity
    have : 0 ≤ (c * F * C₃ * (T - -T) + flowTopRateSlope k α c c' T) *
        Real.exp (c * (T - -T)) * Ψ := by positivity
    nlinarith

/-! ### The bounds of the flow maps on the closed half-plane -/

/-- **The `C^{k,α}` bounds of the flow maps** on the closed half-plane, for `k ≥ 2`. -/
theorem hasHolderBounds_flowOn (h : IsTopBoundedField k v T α c c' P) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    HasHolderBounds k (flowOn v (-T) T s t) α (flowBound k c T) (flowHolder k α c T)
      (flowBound k c T) (flowHolder k α c T) :=
  HasHolderBounds.of_contDiff ((h.contDiff_flowOn hs ht).of_le (by
      exact_mod_cast Nat.le_succ k))
    (fun j hj hjk z hz ↦ h.norm_iteratedFDeriv_flowOn_le hs ht hj hjk.le hz)
    (fun j hj hjk z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα0 hα1 hk hs ht hj hjk.le
      hz hz')
    (fun z hz ↦ h.norm_iteratedFDeriv_flowOn_le hs ht (by omega) le_rfl hz)
    (fun z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα0 hα1 hk hs ht (by omega) le_rfl hz
      hz')

/-- **The `C^{k+1,α}` bounds of the flow maps** on the closed half-plane, for `k ≥ 2`: the
top-order constants are affine in `|∫ₜˢ P(|r|) dr|`. This is the form in which the bounds of
the flow enter the bounds of the carried fields. Proof: the four bounds of this module, for
the orders up to `k` and for the order `k + 1`. -/
theorem hasHolderBounds_flowOn_succ (h : IsTopBoundedField k v T α c c' P) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (flowOn v (-T) T s t) α (flowBound k c T) (flowHolder k α c T)
      (flowTopConst k c T + flowTopSlope k c c' T * |∫ r in t..s, P (|r|)|)
      (flowTopHolderConst k α c T + flowTopHolderSlope k α c c' T * |∫ r in t..s, P (|r|)|) :=
  HasHolderBounds.of_contDiff (by exact_mod_cast h.contDiff_flowOn hs ht)
    (fun j hj hjk z hz ↦ h.norm_iteratedFDeriv_flowOn_le hs ht hj (by omega) hz)
    (fun j hj hjk z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_sub_le hα0 hα1 hk hs ht hj
      (by omega) hz hz')
    (fun z hz ↦ h.norm_iteratedFDeriv_flowOn_top_le (by omega) hs ht hz)
    (fun z z' hz hz' ↦ h.norm_iteratedFDeriv_flowOn_top_sub_le hα0 hα1 hk hs ht hz hz')

end IsTopBoundedField

/-- The constant `C (k - 1) α + C k α` of the level-`k` bounds of the fields of a velocity law
with the constants `C`. -/
def lawConst (C : ℕ → ℝ → ℝ) (k : ℕ) (α : ℝ) : ℝ :=
  C (k - 1) α + C k α

end HalfPlaneSystem

namespace IncompressibleFlow.IsTopBoundedHistory

open HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}
variable {k : ℕ} {ω : ℝ → ℝ^2 → ℝ} {T α R B Nlow : ℝ} {P : ℝ → ℝ}

/-- **The fields of the law of a history with a top-order majorant have level-`k` bounds.** For
`k ≥ 2`, `0 < α < 1` and a support radius `R ≤ R₀`, the extensions of order `k + 1` of the fields
of the law have level-`k` bounds with the constants `lawConst C k α · Nlow` and `lawConst C k α`
and the majorant `P` of the history. It is the instance of `IsTopBoundedField` that the
iteration uses. Proof: the Schauder estimates of the law of order `k - 1`, with the lower-order
bound `Nlow`, give the derivatives of the field up to the order `k`; those of order `k`, with
the bound `Nlow + P(|r|)` of the history at the time `r`, give the derivative of order `k + 1`. -/
theorem isTopBoundedField_law (h : IsTopBoundedHistory k ω T α R B Nlow P)
    (hU : IsVelocityLaw U R₀ C) (hR : R ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) :
    IsTopBoundedField k (fun r ↦ extendedField (k + 1) (U (ω r))) T α
      (lawConst C k α * Nlow) (lawConst C k α) P := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hlow : IsCkVorticityHistory k ω (-T) T α R Nlow := by simpa using h.low
  have hc : lawConst C (k + 1) α = C k α + C (k + 1) α := by simp [lawConst]
  have hC₁ := hU.const_nonneg k α
  have hC₂ := hU.const_nonneg (k + 1) α
  have hu (r : ℝ) (hr : r ∈ Icc (-T) T) :=
    h.history.contDiffOn_law hU hR (by omega) hα hα1 hr
  have hv := h.history.isC1FieldOn_extendedField_law hU hR (by omega) hα hα1
  -- the bounds of the history at a time `r`, of order `k + 1`, with `Nlow + P |r|`
  have hN (r : ℝ) (hr : r ∈ Icc (-T) T) : ∀ j ≤ k + 1, ∀ z : ℝ^2, 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ j (ω r) H̄ z‖ ≤ Nlow + P |r| := by
    intro j hj z hz
    have hP := h.nonneg_abs hr
    have hNl := hlow.nonneg hr
    rcases hj.lt_or_eq with hjk | rfl
    · exact (hlow.norm_le r hr j (by omega) z hz).trans (by linarith)
    · exact (h.norm_le r hr z hz).trans (by linarith)
  have hH (r : ℝ) (hr : r ∈ Icc (-T) T) : ∀ z z' : ℝ^2, 0 ≤ z 1 → 0 ≤ z' 1 →
      ‖iteratedFDerivWithin ℝ (k + 1) (ω r) H̄ z - iteratedFDerivWithin ℝ (k + 1) (ω r) H̄ z'‖ ≤
        (Nlow + P |r|) * ‖z - z'‖ ^ α := fun z z' hz hz' ↦
    (h.holder r hr z z' hz hz').trans (mul_le_mul_of_nonneg_right
      (by linarith [hlow.nonneg hr]) (Real.rpow_nonneg (norm_nonneg _) α))
  exact
    { smooth := h.history.isSmoothFamilyOn_extendedField_law hU hR (by omega) hα hα1
      isC1FieldOn := ⟨_, hv⟩
      mapsTo := fun s hs t ht ↦ mapsTo_flowOn_extendedField hU
        (h.history.toIsVorticityHistory hα.le hα1.le) hR hv.isLipschitzFieldOn hs ht
      continuousOn := h.continuousOn
      nonneg := h.nonneg
      slope_nonneg := by rw [hc]; positivity
      norm_le := fun r hr j hj y hy ↦ by
        rw [iteratedFDeriv_extendedField_of_nonneg (by omega) (hu r hr) (by omega) hy]
        refine (hlow.norm_iteratedFDerivWithin_law_le hU hR (by omega) hα hα1 hr hj hy).trans ?_
        rw [hc]
        nlinarith [hlow.nonneg hr]
      holder := fun r hr y z hy hz ↦ by
        rw [iteratedFDeriv_extendedField_of_nonneg (by omega) (hu r hr) (by omega) hy,
          iteratedFDeriv_extendedField_of_nonneg (by omega) (hu r hr) (by omega) hz]
        refine (hlow.holder_iteratedFDerivWithin_law hU hR (by omega) hα hα1 hr hy hz).trans
          (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α))
        rw [hc]
        nlinarith [hlow.nonneg hr]
      norm_top_le := fun r hr y hy ↦ by
        rw [iteratedFDeriv_extendedField_of_nonneg (by omega) (hu r hr) le_rfl hy]
        refine (hU.norm_iteratedFDerivWithin_le (k := k + 1) (by omega) hα hα1 hR
          (h.history.contDiffOn r hr) (h.history.eq_zero r hr) (hN r hr) (hH r hr) (k + 1 + 1)
          le_rfl y hy).trans ?_
        rw [hc]
        nlinarith [hlow.nonneg hr, h.nonneg_abs hr]
      holder_top := fun r hr y z hy hz ↦ by
        rw [iteratedFDeriv_extendedField_of_nonneg (by omega) (hu r hr) le_rfl hy,
          iteratedFDeriv_extendedField_of_nonneg (by omega) (hu r hr) le_rfl hz]
        refine (hU.holder_iteratedFDerivWithin (k := k + 1) (by omega) hα hα1 hR
          (h.history.contDiffOn r hr) (h.history.eq_zero r hr) (hN r hr) (hH r hr) y z hy
          hz).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) α))
        rw [hc]
        nlinarith [hlow.nonneg hr, h.nonneg_abs hr] }

end IncompressibleFlow.IsTopBoundedHistory
