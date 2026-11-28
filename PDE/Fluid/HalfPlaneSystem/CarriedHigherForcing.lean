/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.FieldHigherFlow
public import PDE.Fluid.HalfPlaneSystem.CarriedVorticity
public import PDE.Fluid.Boussinesq.HalfPlane.CarriedBoundsHigher
public import PDE.Analysis.Calculus.HolderProduct
import PDE.Analysis.ODE.Flow.Basic

/-!
# The carried temperature and the weighted forcing at level `k`

This module shows that when the data of a half-plane system have `k ≥ 2` derivatives and a Hölder
condition, the temperature and the forcing of the vorticity equation carried by the flow of a
velocity field with as many derivatives keep them, with top-order bounds that depend affinely on the
top-order bound of the field. The propagation of regularity needs the top order to enter linearly.

Let `v` be a field with level-`k` bounds `c, c'` and majorant `P` on `[-T, T]`
(`IsTopBoundedField k v T α c c' P`), `(ω₀, θ₀)` data of order `k` with bound `N`
(`Boussinesq.HalfPlane.IsHolderDataOf k`) and `κ` a forcing coefficient with the bounds `Bκ`. With
`Y_t = flowOn v (-T) T 0 t` the label map, `X_r = flowOn v (-T) T r 0` the position map and
`Ψ(t) = |∫ₜ⁰ P(|r|) dr|`:

* the temperature `θ₀ ∘ Y_t` has `C^{k+1,α}` bounds on the closed half-plane `H̄` with constants
  `temperatureBound`, `temperatureHolder` below the top order and top-order constants affine in
  `Ψ(t)`;
* the Eulerian forcing `κ ∂₀(θ₀ ∘ Y_r)` has `C^{k,α}` bounds with the same structure: a product with
  the smooth factor `κ` multiplies the constants by `2^k` and the bound `coefficientBound Bκ k` of
  the derivatives of `κ` of order at most `k + 1`;
* the forcing in label form `(κ ∂₀(θ₀ ∘ Y_r)) ∘ X_r` has `C^{k,α}` bounds with constants
  `forcingBound`, `forcingHolder` below the top order and top-order constants affine in `Ψ(r)`.

The bounds of a composition are those of the chain rule of higher order: the derivative of top order
of the inner or of the outer function enters once, with a coefficient made of lower-order bounds, so
a bound that is affine in `Ψ` stays affine. The constants are compositions of the constants of the
chain rule and are not simplified.

For a velocity law `U` and a `C^{k,α}` history `ω` with a top-order majorant
(`IncompressibleFlow.IsTopBoundedHistory`), the extensions of order `k + 1` of the fields of the law
are such a field (`IncompressibleFlow.IsTopBoundedHistory.isTopBoundedField_law`), and on `H̄` the
carried temperature and the weighted forcing of the iteration, built with the field `lawField U ω`
of order two, are `θ₀ ∘ Y_t` and `(κ ∂₀(θ₀ ∘ Y_r)) ∘ X_r`.

## Main results

* `IsTopBoundedField.hasHolderBounds_comp_flowOn`, `IsTopBoundedField.hasHolderBounds_eulerForcing`,
  `IsTopBoundedField.hasHolderBounds_forcing`: the three bounds above.
* `hasHolderBounds_mul`: for `n ≥ 2`, the `C^{n,α}` bounds of a product with a `C^{n+1}` factor with
  bounded derivatives are linear in the bounds of the other factor.
* `carriedTemperature_eqOn`, `labelForcing_lawField_eq`, `weightedForcing_lawField_eq`: on `H̄` the
  carried temperature and the two forcings of the iteration are the expressions with the flow of the
  extension of order `k + 1`.
* `hasHolderBounds_carriedTemperature`, `abs_carriedTemperature_le`: the `C^{k+1,α}` bounds of the
  carried temperature of the iteration, with `c = lawConst C k α · Nlow` and `c' = lawConst C k α`,
  and the bound `N` of its values.
* `coefficientBound` and the constants `temperatureBound`, `temperatureHolder`,
  `temperatureTopConst`, `temperatureTopSlope`, `temperatureTopHolderConst`,
  `temperatureTopHolderSlope`, with their counterparts `eulerForcing…` and `forcing…`.

`CarriedHigher.lean` integrates the forcing in time and obtains the `C^{k,α}` bounds of the carried
vorticity, and `IterationHigher.lean` uses the bounds of the carried temperature for the regularity
of the solution at level `k`. The case `k = 1` is the class of the local existence theorem
(`Iteration.lean`).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open IncompressibleFlow PDE.Analysis PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

open PDE.Analysis.ODE (zero_mem_Icc_neg_of_mem)
namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### Products with a smooth factor -/

/-- The bound `∑_{j ≤ k + 1} Bκ j` of the derivatives of order at most `k + 1` of a forcing
coefficient with the bounds `Bκ`. -/
def coefficientBound (Bκ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 2), Bκ j

/-- The derivatives of order at most `k + 1` of a forcing coefficient are at most
`coefficientBound Bκ k`. -/
theorem IsForcingCoefficient.norm_iteratedFDeriv_le_coefficientBound {κ : ℝ^2 → ℝ}
    {Bκ : ℕ → ℝ} (hκ : IsForcingCoefficient κ Bκ) {k j : ℕ} (hj : j ≤ k + 1) (x : ℝ^2) :
    ‖iteratedFDeriv ℝ j κ x‖ ≤ coefficientBound Bκ k :=
  (hκ.norm_iteratedFDeriv_le j x).trans (Finset.single_le_sum (f := Bκ)
    (fun i _ ↦ hκ.bound_nonneg i) (Finset.mem_range.mpr (by omega)))

/-- **The bounds of a product with a smooth factor.** For `n ≥ 2`, if `w` is `C^{n+1}` with
derivatives of order at most `n + 1` bounded by `Bw`, and `g` has `C^{n,α}` bounds on the closed
half-plane and is bounded there by `G₀`, then `w g` has `C^{n,α}` bounds whose constants are
linear in those of `g`. -/
theorem hasHolderBounds_mul {n : ℕ} {w g : ℝ^2 → ℝ} {α M H N K Bw G₀ : ℝ} (hn : 2 ≤ n)
    (hα : 0 < α) (hα1 : α ≤ 1) (hw : ContDiff ℝ (n + 1) w)
    (hwb : ∀ j ≤ n + 1, ∀ z : ℝ^2, ‖iteratedFDeriv ℝ j w z‖ ≤ Bw)
    (hg : HasHolderBounds n g α M H N K) (hg₀ : ∀ z : ℝ^2, 0 ≤ z 1 → ‖g z‖ ≤ G₀) :
    HasHolderBounds n (fun z ↦ w z * g z) α (2 ^ n * Bw * (G₀ + M))
      (2 ^ n * 6 * Bw * (G₀ + M + H)) (2 ^ n * Bw * (G₀ + M + N))
      (2 ^ n * 6 * Bw * (G₀ + M + N + K)) := by
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  have hS := convex_closedUpperHalfPlane
  set B := ContinuousLinearMap.mul ℝ ℝ
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have hfun : (fun z ↦ w z * g z) = fun z ↦ B (w z) (g z) := rfl
  have hBw : 0 ≤ Bw := (norm_nonneg _).trans (hwb 0 (Nat.zero_le _) 0)
  have hG₀ : 0 ≤ G₀ := (norm_nonneg _).trans (hg₀ 0 (by simp))
  have hM := hg.bound_nonneg hn
  have hH := hg.holder_nonneg hn
  have hN := hg.top_nonneg
  have hK := hg.holder_top_nonneg
  have hwS : ∀ j ≤ n + 1, ∀ x ∈ H̄, ‖iteratedFDerivWithin ℝ j w H̄ x‖ ≤ Bw := fun j hj x hx ↦ by
    rw [iteratedFDerivWithin_closedUpper_eq hw hj hx]; exact hwb j hj x
  have hgl : ∀ i < n, ∀ x ∈ H̄, ‖iteratedFDerivWithin ℝ i g H̄ x‖ ≤ G₀ + M := fun i hi x hx ↦ by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [norm_iteratedFDerivWithin_zero]; linarith [hg₀ x hx]
    · linarith [hg.norm_le i hi0 hi x hx]
  have hgt : ∀ i ≤ n, ∀ x ∈ H̄, ‖iteratedFDerivWithin ℝ i g H̄ x‖ ≤ G₀ + M + N :=
    fun i hi x hx ↦ by
      rcases hi.lt_or_eq with hi | rfl
      · linarith [hgl i hi x hx]
      · linarith [hg.norm_top_le x hx]
  have h2 (j : ℕ) (hj : j ≤ n) : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have hd (z z' : ℝ^2) : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  refine ⟨(hw.contDiffOn.of_le (by exact_mod_cast Nat.le_succ n)).mul hg.contDiffOn,
    fun j hj hjn z hz ↦ ?_, fun j hj hjn z z' hz hz' ↦ ?_, fun z hz ↦ ?_,
    fun z z' hz hz' ↦ ?_⟩
  · rw [hfun]
    refine (norm_iteratedFDerivWithin_bilinear_le_mul B hU
      (hw.contDiffOn.of_le (by exact_mod_cast (by omega : j ≤ n + 1)))
      (hg.contDiffOn.of_le (by exact_mod_cast hjn.le)) (fun i hi x hx ↦ hwS i (by omega) x hx)
      (fun i hi x hx ↦ hgl i (by omega) x hx) hz).trans ?_
    calc ‖B‖ * (2 ^ j * (Bw * (G₀ + M))) ≤ 1 * (2 ^ n * (Bw * (G₀ + M))) :=
          mul_le_mul hB (mul_le_mul_of_nonneg_right (h2 j hjn.le) (by positivity))
            (by positivity) zero_le_one
      _ = _ := by ring
  · rw [hfun]
    refine (norm_iteratedFDerivWithin_bilinear_sub_le_rpow B hS hU
      (hw.contDiffOn.of_le (by exact_mod_cast (by omega : j + 1 ≤ n + 1)))
      (hg.contDiffOn.of_le (by exact_mod_cast hjn.le)) hα hα1 (Mw := Bw) (Mf := G₀ + M + H)
      (fun i hi x hx ↦ hwS i (by omega) x hx)
      (fun i hi x hx ↦ (hgl i (by omega) x hx).trans (by linarith))
      (fun x hx y hy ↦ (hg.holder j hj hjn x y hx hy).trans
        (mul_le_mul_of_nonneg_right (by linarith) (hd x y))) hz hz').trans
      (mul_le_mul_of_nonneg_right ?_ (hd z z'))
    calc ‖B‖ * (2 ^ j * (6 * (Bw * (G₀ + M + H)))) ≤ 1 * (2 ^ n * (6 * (Bw * (G₀ + M + H)))) :=
          mul_le_mul hB (mul_le_mul_of_nonneg_right (h2 j hjn.le) (by positivity))
            (by positivity) zero_le_one
      _ = _ := by ring
  · rw [hfun]
    refine (norm_iteratedFDerivWithin_bilinear_le_mul B hU
      (hw.contDiffOn.of_le (by exact_mod_cast Nat.le_succ n)) hg.contDiffOn
      (fun i hi x hx ↦ hwS i (by omega) x hx) hgt hz).trans ?_
    calc ‖B‖ * (2 ^ n * (Bw * (G₀ + M + N))) ≤ 1 * (2 ^ n * (Bw * (G₀ + M + N))) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
      _ = _ := by ring
  · rw [hfun]
    refine (norm_iteratedFDerivWithin_bilinear_sub_le_rpow B hS hU hw.contDiffOn hg.contDiffOn hα
      hα1 (Mw := Bw) (Mf := G₀ + M + N + K) hwS
      (fun i hi x hx ↦ (hgt i hi x hx).trans (by linarith))
      (fun x hx y hy ↦ (hg.holder_top x y hx hy).trans
        (mul_le_mul_of_nonneg_right (by linarith) (hd x y))) hz hz').trans
      (mul_le_mul_of_nonneg_right ?_ (hd z z'))
    calc ‖B‖ * (2 ^ n * (6 * (Bw * (G₀ + M + N + K)))) ≤
          1 * (2 ^ n * (6 * (Bw * (G₀ + M + N + K)))) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
      _ = _ := by ring

/-! ### The constants -/

section Constants

variable (Bκ : ℕ → ℝ) (k : ℕ) (α c c' N T : ℝ)

/-- The bound of the derivatives of orders `1 ≤ j ≤ k` of the carried temperature. -/
def temperatureBound : ℝ :=
  compBound (k + 1) N (flowBound k c T)

/-- The Hölder constant of the derivatives of orders `1 ≤ j ≤ k` of the carried temperature. -/
def temperatureHolder : ℝ :=
  compHolder (k + 1) α N (2 * N) (flowBound k c T) (flowHolder k α c T) (flowBound k c T)

/-- The constant term of the bound of the derivative of order `k + 1` of the carried
temperature. -/
def temperatureTopConst : ℝ :=
  compTopBound (k + 1) N N (flowBound k c T) (flowTopConst k c T)

/-- The coefficient of `Ψ(t)` in the bound of the derivative of order `k + 1` of the carried
temperature. -/
def temperatureTopSlope : ℝ :=
  N * flowTopSlope k c c' T

/-- The constant term of the Hölder constant of the derivative of order `k + 1` of the carried
temperature. -/
def temperatureTopHolderConst : ℝ :=
  compTopHolder (k + 1) α N (2 * N) N N (flowBound k c T) (flowHolder k α c T)
    (flowTopConst k c T) (flowTopHolderConst k α c T) (flowBound k c T)

/-- The coefficient of `Ψ(t)` in the Hölder constant of the derivative of order `k + 1` of the
carried temperature. -/
def temperatureTopHolderSlope : ℝ :=
  N * flowTopHolderSlope k α c c' T + 2 * N * flowBound k c T ^ α * flowTopSlope k c c' T

/-- The bound of the derivatives of orders `1 ≤ j < k` of the Eulerian forcing. -/
def eulerForcingBound : ℝ :=
  2 ^ k * coefficientBound Bκ k * (temperatureBound k c N T + temperatureBound k c N T)

/-- The Hölder constant of the derivatives of orders `1 ≤ j < k` of the Eulerian forcing. -/
def eulerForcingHolder : ℝ :=
  2 ^ k * 6 * coefficientBound Bκ k *
    (temperatureBound k c N T + temperatureBound k c N T + temperatureHolder k α c N T)

/-- The constant term of the bound of the derivative of order `k` of the Eulerian forcing. -/
def eulerForcingTopConst : ℝ :=
  2 ^ k * coefficientBound Bκ k *
    (temperatureBound k c N T + temperatureBound k c N T + temperatureTopConst k c N T)

/-- The coefficient of `Ψ(r)` in the bound of the derivative of order `k` of the Eulerian
forcing. -/
def eulerForcingTopSlope : ℝ :=
  2 ^ k * coefficientBound Bκ k * temperatureTopSlope k c c' N T

/-- The constant term of the Hölder constant of the derivative of order `k` of the Eulerian
forcing. -/
def eulerForcingTopHolderConst : ℝ :=
  2 ^ k * 6 * coefficientBound Bκ k *
    (temperatureBound k c N T + temperatureBound k c N T + temperatureTopConst k c N T +
      temperatureTopHolderConst k α c N T)

/-- The coefficient of `Ψ(r)` in the Hölder constant of the derivative of order `k` of the
Eulerian forcing. -/
def eulerForcingTopHolderSlope : ℝ :=
  2 ^ k * 6 * coefficientBound Bκ k *
    (temperatureTopSlope k c c' N T + temperatureTopHolderSlope k α c c' N T)

/-- The bound of the derivatives of orders `1 ≤ j < k` of the forcing in label form. -/
def forcingBound : ℝ :=
  compBound k (eulerForcingBound Bκ k c N T) (flowBound k c T)

/-- The Hölder constant of the derivatives of orders `1 ≤ j < k` of the forcing in label
form. -/
def forcingHolder : ℝ :=
  compHolder k α (eulerForcingBound Bκ k c N T) (eulerForcingHolder Bκ k α c N T)
    (flowBound k c T) (flowHolder k α c T) (flowBound k c T)

/-- The constant term of the bound of the derivative of order `k` of the forcing in label
form. -/
def forcingTopConst : ℝ :=
  compTopBound k (eulerForcingBound Bκ k c N T) (eulerForcingTopConst Bκ k c N T)
    (flowBound k c T) (flowBound k c T)

/-- The coefficient of `Ψ(r)` in the bound of the derivative of order `k` of the forcing in
label form. -/
def forcingTopSlope : ℝ :=
  eulerForcingTopSlope Bκ k c c' N T * flowBound k c T ^ k

/-- The constant term of the Hölder constant of the derivative of order `k` of the forcing in
label form. -/
def forcingTopHolderConst : ℝ :=
  compTopHolder k α (eulerForcingBound Bκ k c N T) (eulerForcingHolder Bκ k α c N T)
    (eulerForcingTopConst Bκ k c N T) (eulerForcingTopHolderConst Bκ k α c N T)
    (flowBound k c T) (flowHolder k α c T) (flowBound k c T) (flowHolder k α c T)
    (flowBound k c T)

/-- The coefficient of `Ψ(r)` in the Hölder constant of the derivative of order `k` of the
forcing in label form. -/
def forcingTopHolderSlope : ℝ :=
  eulerForcingTopSlope Bκ k c c' N T * k * flowBound k c T ^ (k - 1) * flowHolder k α c T +
    eulerForcingTopHolderSlope Bκ k α c c' N T * flowBound k c T ^ α * flowBound k c T ^ k

end Constants

/-! ### Fields with level-`k` bounds -/

namespace IsTopBoundedField

variable {k : ℕ} {v : ℝ → ℝ^2 → ℝ^2} {T α c c' : ℝ} {P : ℝ → ℝ}
variable {κ ω₀ θ₀ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ} {R N : ℝ}

/-- **The `C^{k+1,α}` bounds of the temperature carried by the flow.** For a field with level-`k`
bounds and data of order `k`, `k ≥ 2`, the function `θ₀ ∘ Y_t` has `C^{k+1,α}` bounds on the
closed half-plane whose top-order constants are affine in `Ψ(t) = |∫ₜ⁰ P(|r|) dr|`. Proof: the
bounds of a composition, with the `C^{k+1,α}` bounds of the datum and of the label map; the top
order of the label map enters once. -/
theorem hasHolderBounds_comp_flowOn (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (θ₀ ∘ flowOn v (-T) T 0 t) α (temperatureBound k c N T)
      (temperatureHolder k α c N T)
      (temperatureTopConst k c N T + temperatureTopSlope k c c' N T * |∫ r in t..0, P (|r|)|)
      (temperatureTopHolderConst k α c N T +
        temperatureTopHolderSlope k α c c' N T * |∫ r in t..0, P (|r|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem ht
  have hc := (hd.hasHolderBounds_temperature hα0 hα1).comp
    (h.hasHolderBounds_flowOn_succ hα0 hα1 hk h0 ht) (h.mapsTo 0 h0 t ht)
    (flowBound_nonneg c T (by omega))
    (fun z z' hz hz' ↦ h.norm_flowOn_sub_le (by omega) h0 ht hz hz') (by omega) hα0
  rw [compTopBound_inner_affine, compTopHolder_inner_affine] at hc
  exact hc

/-- **The `C^{k,α}` bounds of the Eulerian forcing** `κ ∂₀(θ₀ ∘ Y_r)` at a time `r ∈ [-T, T]`.
The top-order constants are affine in `Ψ(r)`. Proof: a derivative of the carried temperature
loses one order, and the product with the smooth factor `κ` is bounded by `hasHolderBounds_mul`. -/
theorem hasHolderBounds_eulerForcing (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) {r : ℝ} (hr : r ∈ Icc (-T) T) :
    HasHolderBounds k (fun z ↦ κ z * fderivWithin ℝ (θ₀ ∘ flowOn v (-T) T 0 r) H̄ z
        (EuclideanSpace.single 0 1)) α
      (eulerForcingBound Bκ k c N T) (eulerForcingHolder Bκ k α c N T)
      (eulerForcingTopConst Bκ k c N T +
        eulerForcingTopSlope Bκ k c c' N T * |∫ r' in r..0, P (|r'|)|)
      (eulerForcingTopHolderConst Bκ k α c N T +
        eulerForcingTopHolderSlope Bκ k α c c' N T * |∫ r' in r..0, P (|r'|)|) := by
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  have hθt := h.hasHolderBounds_comp_flowOn hd hα.le hα1 hk hr
  have hθ := hθt.fderivWithin_apply (EuclideanSpace.single 0 1)
  simp only [he, one_mul] at hθ
  have hg₀ : ∀ z : ℝ^2, 0 ≤ z 1 → ‖fderivWithin ℝ (θ₀ ∘ flowOn v (-T) T 0 r) H̄ z
      (EuclideanSpace.single 0 1)‖ ≤ temperatureBound k c N T := fun z hz ↦ by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [he, mul_one, ← norm_iteratedFDerivWithin_one _ (hU z hz)]
    exact hθt.norm_le 1 le_rfl (by omega) z hz
  have hm := hasHolderBounds_mul (n := k) hk hα hα1 (hκ.contDiff.of_le (by exact_mod_cast le_top))
    (fun j hj z ↦ hκ.norm_iteratedFDeriv_le_coefficientBound hj z) hθ hg₀
  refine hm.mono le_rfl le_rfl (le_of_eq ?_) (le_of_eq ?_)
  · simp only [eulerForcingTopConst, eulerForcingTopSlope]; ring
  · simp only [eulerForcingTopHolderConst, eulerForcingTopHolderSlope]; ring

/-- **The `C^{k,α}` bounds of the forcing in label form** `(κ ∂₀(θ₀ ∘ Y_r)) ∘ X_r` at a time
`r ∈ [-T, T]`, with top-order constants affine in `Ψ(r) = |∫ᵣ⁰ P(|r'|) dr'|`. This is the
integrand of the carried vorticity. Proof: the bounds of a composition of the Eulerian forcing
with the position map, whose derivatives up to the order `k` are bounded without `P`. -/
theorem hasHolderBounds_forcing (h : IsTopBoundedField k v T α c c' P)
    (hd : IsHolderDataOf k ω₀ θ₀ α R N) (hκ : IsForcingCoefficient κ Bκ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hk : 2 ≤ k) {r : ℝ} (hr : r ∈ Icc (-T) T) :
    HasHolderBounds k ((fun z ↦ κ z * fderivWithin ℝ (θ₀ ∘ flowOn v (-T) T 0 r) H̄ z
        (EuclideanSpace.single 0 1)) ∘ flowOn v (-T) T r 0) α
      (forcingBound Bκ k c N T) (forcingHolder Bκ k α c N T)
      (forcingTopConst Bκ k c N T + forcingTopSlope Bκ k c c' N T * |∫ r' in r..0, P (|r'|)|)
      (forcingTopHolderConst Bκ k α c N T +
        forcingTopHolderSlope Bκ k α c c' N T * |∫ r' in r..0, P (|r'|)|) := by
  have h0 := zero_mem_Icc_neg_of_mem hr
  have hc := (h.hasHolderBounds_eulerForcing hd hκ hα hα1 hk hr).comp
    (h.hasHolderBounds_flowOn hα.le hα1 hk hr h0) (h.mapsTo r hr 0 h0)
    (flowBound_nonneg c T (by omega))
    (fun z z' hz hz' ↦ h.norm_flowOn_sub_le (by omega) hr h0 hz hz') hk hα.le
  rw [compTopBound_outer_affine, compTopHolder_outer_affine] at hc
  exact hc

/-- At a label `y` of the closed half-plane and a time `r ∈ [-T, T]`, the derivative within `H̄`
of `θ₀` at `y` applied to the inverse first variation along the particle is the derivative
within `H̄` of `θ₀ ∘ Y_r` at the position `X_r y`. -/
theorem fderivWithin_apply_variationOn_eq (h : IsTopBoundedField k v T α c c' P)
    (hθ : DifferentiableOn ℝ θ₀ H̄) {r : ℝ} (hr : r ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1)
    (e : ℝ^2) :
    fderivWithin ℝ θ₀ H̄ y (variationOn v (fun r y ↦ fderiv ℝ (v r) y) (-T) T 0 r
        (flowOn v (-T) T r 0 y) e) =
      fderivWithin ℝ (θ₀ ∘ flowOn v (-T) T 0 r) H̄ (flowOn v (-T) T r 0 y) e := by
  obtain ⟨L, hv⟩ := h.isC1FieldOn
  have h0 := zero_mem_Icc_neg_of_mem hr
  have hU := uniqueDiffOn_coordinateHalfSpace (n := 2) 1
  set z := flowOn v (-T) T r 0 y
  have hz : 0 ≤ z 1 := h.mapsTo r hr 0 h0 hy
  have hzy : flowOn v (-T) T 0 r z = y := hv.isLipschitzFieldOn.flowOn_flowOn_self hr h0 y
  have hY : HasFDerivAt (flowOn v (-T) T 0 r)
      (variationOn v (fun r y ↦ fderiv ℝ (v r) y) (-T) T 0 r z) z := hv.hasFDerivAt_flowOn h0 hr z
  rw [fderivWithin_comp z (hθ _ (by rw [hzy]; exact hy)) hY.differentiableAt.differentiableWithinAt
      (h.mapsTo 0 h0 r hr) (hU z hz),
    hY.differentiableAt.fderivWithin (hU z hz), hY.fderiv, hzy]
  rfl

end IsTopBoundedField

/-! ### The fields of a velocity law -/

section Law

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}
variable {k : ℕ} {κ ω₀ θ₀ : ℝ^2 → ℝ} {ω : ℝ → ℝ^2 → ℝ} {α R N T R₁ B Nlow : ℝ}
  {P : ℝ → ℝ}

/-- The flows of the extension of order `k + 1` of the fields of the law preserve the closed
half-plane. -/
theorem mapsTo_flowOn_extendedField_succ (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hR₁ : R₁ ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {s t : ℝ} (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    MapsTo (flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T s t) H̄ H̄ :=
  mapsTo_flowOn_extendedField hU (h.history.toIsVorticityHistory hα.le hα1.le) hR₁
    (h.history.isC1FieldOn_extendedField_law hU hR₁ hk hα hα1).isLipschitzFieldOn hs ht

/-- On the closed half-plane the carried temperature at time `t` is `θ₀ ∘ Y_t`, with the flow of
the extension of order `k + 1`. -/
theorem carriedTemperature_eqOn (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hR₁ : R₁ ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α)
    (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    EqOn (fun x ↦ carriedTemperature θ₀ (lawField U ω) (-T) T x t)
      (θ₀ ∘ flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T 0 t) H̄ := fun x hx ↦ by
  simp only [carriedTemperature, Function.comp_apply]
  rw [flowOn_lawField_eq hU h.history hR₁ hk hα hα1 (zero_mem_Icc_neg_of_mem ht) ht hx,
    dataTemperature_of_nonneg θ₀
      (mapsTo_flowOn_extendedField_succ hU h hR₁ hk hα hα1 (zero_mem_Icc_neg_of_mem ht) ht hx)]

/-- **The `C^{k+1,α}` bounds of the carried temperature** at a time `t ∈ [-T, T]`, for `k ≥ 2`. -/
theorem hasHolderBounds_carriedTemperature (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    HasHolderBounds (k + 1) (fun x ↦ carriedTemperature θ₀ (lawField U ω) (-T) T x t) α
      (temperatureBound k (lawConst C k α * Nlow) N T)
      (temperatureHolder k α (lawConst C k α * Nlow) N T)
      (temperatureTopConst k (lawConst C k α * Nlow) N T +
        temperatureTopSlope k (lawConst C k α * Nlow) (lawConst C k α) N T *
          |∫ r in t..0, P (|r|)|)
      (temperatureTopHolderConst k α (lawConst C k α * Nlow) N T +
        temperatureTopHolderSlope k α (lawConst C k α * Nlow) (lawConst C k α) N T *
          |∫ r in t..0, P (|r|)|) :=
  ((h.isTopBoundedField_law hU hR₁ hk hα hα1).hasHolderBounds_comp_flowOn hd hα.le hα1.le hk
    ht).congr (carriedTemperature_eqOn hU h hR₁ (by omega) hα hα1 ht)

/-- The carried temperature is bounded by `N` on the closed half-plane. -/
theorem abs_carriedTemperature_le (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 1 ≤ k) (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc (-T) T)
    {x : ℝ^2} (hx : 0 ≤ x 1) : |carriedTemperature θ₀ (lawField U ω) (-T) T x t| ≤ N := by
  have he : carriedTemperature θ₀ (lawField U ω) (-T) T x t = _ :=
    carriedTemperature_eqOn hU h hR₁ hk hα hα1 ht hx
  rw [he, Function.comp_apply]
  have h0 := hd.norm_temperature_le 0 (Nat.zero_le _) _
    (mapsTo_flowOn_extendedField_succ hU h hR₁ hk hα hα1 (zero_mem_Icc_neg_of_mem ht) ht hx)
  rwa [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] at h0

/-- **The label forcing of the iteration** at a label `y` of the closed half-plane and a time
`r ∈ [-T, T]` is `∂₀(θ₀ ∘ Y_r)` at the position `X_r y`, with the flow of the extension of order
`k + 1`. -/
theorem labelForcing_lawField_eq (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc (-T) T)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    labelForcing (lawField U ω) (lawFieldDeriv U ω) (-T) T (dataTemperature θ₀)
        (EuclideanSpace.single 0 1) y r =
      fderivWithin ℝ (θ₀ ∘ flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T 0 r) H̄
        (flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T r 0 y)
        (EuclideanSpace.single 0 1) := by
  have h0 := zero_mem_Icc_neg_of_mem hr
  have hθ : DifferentiableOn ℝ θ₀ H̄ :=
    hd.temperature_contDiffOn.differentiableOn (by exact_mod_cast (show k + 1 ≠ 0 by omega))
  unfold labelForcing
  rw [flowOn_lawField_eq hU h.history hR₁ (by omega) hα hα1 hr h0 hy,
    variationOn_lawField_eq hU h.history hR₁ (by omega) hα hα1 h0 hr
      (mapsTo_flowOn_extendedField_succ hU h hR₁ (by omega) hα hα1 hr h0 hy),
    (hd.toIsHolderData (by omega) hα.le hα1.le).fderiv_dataTemperature hy]
  exact (h.isTopBoundedField_law hU hR₁ hk hα hα1).fderivWithin_apply_variationOn_eq hθ hr hy _

/-- **The weighted forcing of the iteration** at a label `y` of the closed half-plane and a time
`r ∈ [-T, T]` is the Eulerian forcing `κ ∂₀(θ₀ ∘ Y_r)` at the position `X_r y`, with the flow of
the extension of order `k + 1`. -/
theorem weightedForcing_lawField_eq (hU : IsVelocityLaw U R₀ C)
    (h : IsTopBoundedHistory k ω T α R₁ B Nlow P) (hd : IsHolderDataOf k ω₀ θ₀ α R N)
    (hR₁ : R₁ ≤ R₀) (hk : 2 ≤ k) (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : r ∈ Icc (-T) T)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    weightedForcing (lawField U ω) (lawFieldDeriv U ω) (-T) T κ (dataTemperature θ₀)
        (EuclideanSpace.single 0 1) y r =
      ((fun z ↦ κ z * fderivWithin ℝ
          (θ₀ ∘ flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T 0 r) H̄ z
          (EuclideanSpace.single 0 1)) ∘
        flowOn (fun r ↦ extendedField (k + 1) (U (ω r))) (-T) T r 0) y := by
  rw [weightedForcing, labelForcing_lawField_eq hU h hd hR₁ hk hα hα1 hr hy,
    flowOn_lawField_eq hU h.history hR₁ (by omega) hα hα1 hr (zero_mem_Icc_neg_of_mem hr) hy]
  rfl

end Law

end HalfPlaneSystem
