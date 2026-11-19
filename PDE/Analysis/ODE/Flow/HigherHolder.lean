/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.HigherEstimates

/-!
# Hölder bound of the top derivative of a flow map from Hölder bounds of the lower orders

`IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_rpow` bounds the Hölder constant of the derivative
of order `m` of the flow maps with Lipschitz constants of the lower-order derivatives of the field
and of the flow maps. When these are themselves of top order (the derivative of order `m - 1` of
the field is Lipschitz with the bound of `D^m v` as constant), the bound is not linear in the top
order. Here the lower orders enter through `α`-Hölder constants instead: `M'` for the derivatives
of the field of orders `2 ≤ i < m` and `Λ` for those of the flow maps of orders `1 ≤ i < m`, which
are of lower order in an induction on the regularity. The bound of `D^m X` may depend on time, so
that the rate

`K₂ L Fm(r) + Km(r) m L^(m-1) L₂ + Hm(r) L^α L^m + c_m (M m Λ + M' L^α) max(1, F)^m`

is linear in the top-order quantities `Fm`, `Km`, `Hm` with coefficients of lower order.

## Main results

* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_rpow_of_holder`: points at distance at most one.
* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_max_rpow_of_holder`: all points of the set.
-/

@[expose] public section

open Set Filter Metric ContinuousLinearMap MeasureTheory
open scoped NNReal Topology Interval

noncomputable section

namespace PDE.Analysis.ODE

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b t : ℝ} {K : ℝ≥0} {m : ℕ} {S : Set E}

/-- The Hölder rate `K₂ L Fm + k m L^(m-1) L₂ + h L^α L^m + c_m (M m Λ + M' L^α) max(1, F)^m` of
the derivative of order `m` of a flow map, with `k`, `h`, `Fm` the bound and Hölder constant of
`D^m v` and the bound of `D^m X` at the time, and the lower orders measured by bounds and
`α`-Hölder constants. -/
def flowHolderRateOfHolder (m : ℕ) (α K₂ M M' L L₂ F₀ Λ Fm k h : ℝ) : ℝ :=
  K₂ * L * Fm + k * m * L ^ (m - 1) * L₂ + h * L ^ α * L ^ m +
    Fintype.card (OrderedFinpartition m) * ((M * m * Λ + M' * L ^ α) * max 1 F₀ ^ m)

/-- **Hölder bound of the top-order derivative of the flow maps at nearby points**, with the
lower-order derivatives of the field and of the flow maps measured by `α`-Hölder constants and a
time-dependent bound `Fm` of the top derivative of the flow maps. For `x, y ∈ S` with
`‖x - y‖ ≤ 1`,
`‖D^m X(s) x - D^m X(s) y‖ ≤ |∫ₜˢ ρ(r)| exp (K₁ |s - t|) ‖x - y‖^α` with
`ρ(r) = flowHolderRateOfHolder m α K₂ M M' L L₂ F₀ Λ (Fm r) (Km r) (Hm r)`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_rpow_of_holder
    (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b)
    (hS : ∀ s ∈ Icc a b, MapsTo (flowOn v a b s t) S S) (hm : 2 ≤ m) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {K₁ K₂ M M' L L₂ F₀ Λ : ℝ} {Km Hm Fm : ℝ → ℝ}
    (hK₁ : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (v r) y‖ ≤ K₁) (hM0 : 0 ≤ M)
    (hM : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 2 ≤ i → i < m → ‖iteratedFDeriv ℝ i (v r) y‖ ≤ M)
    (hKm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (v r) y‖ ≤ Km r)
    (hKmc : ContinuousOn Km (Icc a b)) (hK₂ : 0 ≤ K₂) (hM'0 : 0 ≤ M')
    (hLip1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (v r) y - fderiv ℝ (v r) z‖ ≤ K₂ * ‖y - z‖)
    (hHol : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 2 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (v r) y - iteratedFDeriv ℝ i (v r) z‖ ≤ M' * ‖y - z‖ ^ α)
    (hHm0 : ∀ r ∈ Icc a b, 0 ≤ Hm r)
    (hHm : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖iteratedFDeriv ℝ m (v r) y - iteratedFDeriv ℝ m (v r) z‖ ≤ Hm r * ‖y - z‖ ^ α)
    (hHmc : ContinuousOn Hm (Icc a b))
    (hL : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (flowOn v a b r t) y‖ ≤ L)
    (hXL : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖flowOn v a b r t y - flowOn v a b r t z‖ ≤ L * ‖y - z‖)
    (hF : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y‖ ≤ F₀)
    (hFm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (flowOn v a b r t) y‖ ≤ Fm r)
    (hFmc : ContinuousOn Fm (Icc a b))
    (hΛ0 : 0 ≤ Λ) (hL₂0 : 0 ≤ L₂)
    (hXd1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (flowOn v a b r t) y - fderiv ℝ (flowOn v a b r t) z‖ ≤ L₂ * ‖y - z‖)
    (hXH : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y - iteratedFDeriv ℝ i (flowOn v a b r t) z‖ ≤
        Λ * ‖y - z‖ ^ α)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hxy : ‖x - y‖ ≤ 1) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m (flowOn v a b s t) x - iteratedFDeriv ℝ m (flowOn v a b s t) y‖ ≤
      |∫ r in t..s, flowHolderRateOfHolder m α K₂ M M' L L₂ F₀ Λ (Fm r) (Km r) (Hm r)| *
        Real.exp (K₁ * |s - t|) * ‖x - y‖ ^ α := by
  have hL' := hv.isLipschitzFieldOn
  have hX := hv.isSmoothFamilyOn_flowOn hsm ht
  set d := ‖x - y‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdα : d ≤ d ^ α := Real.self_le_rpow_of_le_one hd0 hxy hα1
  have hdα0 : 0 ≤ d ^ α := Real.rpow_nonneg hd0 α
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ t ht x hx)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL t ht x hx)
  have hLα0 : 0 ≤ L ^ α := Real.rpow_nonneg hL0 α
  have hKm0 : ∀ r ∈ Icc a b, 0 ≤ Km r := fun r hr ↦
    (norm_nonneg _).trans (hKm r hr _ (hS r hr hx))
  -- the coefficients of the rate are nonnegative
  have hA : ∀ r ∈ Icc a b, 0 ≤ K₂ * L * Fm r := fun r hr ↦
    mul_nonneg (mul_nonneg hK₂ hL0) ((norm_nonneg _).trans (hFm r hr x hx))
  have hB : ∀ r ∈ Icc a b, 0 ≤ Km r * m * L ^ (m - 1) * L₂ := fun r hr ↦
    mul_nonneg (mul_nonneg (mul_nonneg (hKm0 r hr) (Nat.cast_nonneg _)) (pow_nonneg hL0 _)) hL₂0
  have hc0 : 0 ≤ (Fintype.card (OrderedFinpartition m) : ℝ) *
      ((M * m * Λ + M' * L ^ α) * max 1 F₀ ^ m) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hM0
      (Nat.cast_nonneg _)) hΛ0) (mul_nonneg hM'0 hLα0))
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  set ρ : ℝ → ℝ := fun r ↦ flowHolderRateOfHolder m α K₂ M M' L L₂ F₀ Λ (Fm r) (Km r) (Hm r)
  have hρ0 : ∀ r ∈ Icc a b, 0 ≤ ρ r := fun r hr ↦ add_nonneg (add_nonneg (add_nonneg (hA r hr)
    (hB r hr)) (mul_nonneg (mul_nonneg (hHm0 r hr) hLα0) (pow_nonneg hL0 _))) hc0
  have hρc : ContinuousOn ρ (Icc a b) := by
    simp only [ρ, flowHolderRateOfHolder]
    exact (((continuousOn_const.mul hFmc).add ((hKmc.mul continuousOn_const).mul
      continuousOn_const |>.mul continuousOn_const)).add
      ((hHmc.mul continuousOn_const).mul continuousOn_const)).add continuousOn_const
  set e : ℝ → (E [×m]→L[ℝ] E) := fun r ↦
    iteratedFDeriv ℝ m (flowOn v a b r t) x - iteratedFDeriv ℝ m (flowOn v a b r t) y
  set e' : ℝ → (E [×m]→L[ℝ] E) := fun r ↦
    iteratedFDeriv ℝ m (fun z ↦ v r (flowOn v a b r t z)) x -
      iteratedFDeriv ℝ m (fun z ↦ v r (flowOn v a b r t z)) y
  have he : ∀ r ∈ Icc a b, HasDerivWithinAt e (e' r) (Icc a b) r := fun r hr ↦
    (hv.hasDerivWithinAt_iteratedFDeriv_flowOn hsm ht le_rfl x hr).sub
      (hv.hasDerivWithinAt_iteratedFDeriv_flowOn hsm ht le_rfl y hr)
  have he0 : ‖e t‖ ≤ 0 := by
    simp only [e, hL'.flowOn_self_eq ht, iteratedFDeriv_id_eq_zero hm, sub_zero, norm_zero,
      le_refl]
  have hbound : ∀ r ∈ Icc a b, ‖e' r‖ ≤ K₁ * ‖e r‖ + ρ r * d ^ α := by
    intro r hr
    have hxr : flowOn v a b r t x ∈ S := hS r hr hx
    have hyr : flowOn v a b r t y ∈ S := hS r hr hy
    have hgg : ‖flowOn v a b r t x - flowOn v a b r t y‖ ≤ L * d := hXL r hr x hx y hy
    have hpow : ‖flowOn v a b r t x - flowOn v a b r t y‖ ^ α ≤ L ^ α * d ^ α := by
      rw [← Real.mul_rpow hL0 hd0]
      exact Real.rpow_le_rpow (norm_nonneg _) hgg hα0
    have h := norm_iteratedFDeriv_comp_sub_le_add (hsm.contDiff hr) (hX.contDiff hr) hm x y hM0
      (le_trans (norm_nonneg _) (hF r hr x hx 1 le_rfl (by omega)))
      (mul_nonneg hM'0 (mul_nonneg hLα0 hdα0)) (mul_nonneg hΛ0 hdα0)
      (fun i hi him ↦ hM r hr _ hxr i hi him)
      (fun i hi him ↦ (hHol r hr _ hxr _ hyr i hi him).trans
        (mul_le_mul_of_nonneg_left hpow hM'0))
      (fun i hi him ↦ hF r hr x hx i hi him) (fun i hi him ↦ hF r hr y hy i hi him)
      (fun i hi him ↦ hXH r hr x hx y hy i hi him)
    have t1 : ‖fderiv ℝ (v r) (flowOn v a b r t x)‖ *
        ‖iteratedFDeriv ℝ m (flowOn v a b r t) x - iteratedFDeriv ℝ m (flowOn v a b r t) y‖ ≤
        K₁ * ‖e r‖ := mul_le_mul_of_nonneg_right (hK₁ r hr _ hxr) (norm_nonneg _)
    have t2 : ‖fderiv ℝ (v r) (flowOn v a b r t x) - fderiv ℝ (v r) (flowOn v a b r t y)‖ *
        ‖iteratedFDeriv ℝ m (flowOn v a b r t) y‖ ≤ K₂ * L * Fm r * d :=
      (mul_le_mul ((hLip1 r hr _ hxr _ hyr).trans (mul_le_mul_of_nonneg_left hgg hK₂))
        (hFm r hr y hy) (norm_nonneg _) (mul_nonneg hK₂ (mul_nonneg hL0 hd0))).trans_eq
        (by ring)
    have t3 : ‖iteratedFDeriv ℝ m (v r) (flowOn v a b r t x)‖ * m *
        max ‖fderiv ℝ (flowOn v a b r t) x‖ ‖fderiv ℝ (flowOn v a b r t) y‖ ^ (m - 1) *
        ‖fderiv ℝ (flowOn v a b r t) x - fderiv ℝ (flowOn v a b r t) y‖ ≤
        Km r * m * L ^ (m - 1) * L₂ * d := by
      have hk0 := mul_nonneg (hKm0 r hr) (Nat.cast_nonneg (α := ℝ) m)
      refine (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (hKm r hr _ hxr)
        (Nat.cast_nonneg _)) (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _))
          (max_le (hL r hr x hx) (hL r hr y hy)) _)
        (pow_nonneg (le_max_of_le_left (norm_nonneg _)) _) hk0) (hXd1 r hr x hx y hy)
        (norm_nonneg _) (mul_nonneg hk0 (pow_nonneg hL0 _))).trans_eq (by ring)
    have t4 : ‖iteratedFDeriv ℝ m (v r) (flowOn v a b r t x) -
        iteratedFDeriv ℝ m (v r) (flowOn v a b r t y)‖ *
        ‖fderiv ℝ (flowOn v a b r t) y‖ ^ m ≤ Hm r * L ^ α * L ^ m * d ^ α :=
      (mul_le_mul ((hHm r hr _ hxr _ hyr).trans (mul_le_mul_of_nonneg_left hpow (hHm0 r hr)))
        (pow_le_pow_left₀ (norm_nonneg _) (hL r hr y hy) m) (by positivity)
        (mul_nonneg (hHm0 r hr) (mul_nonneg hLα0 hdα0))).trans_eq (by ring)
    simp only [ρ, flowHolderRateOfHolder]
    linear_combination h + t1 + t2 + t3 + t4 + mul_le_mul_of_nonneg_left hdα (hA r hr) +
      mul_le_mul_of_nonneg_left hdα (hB r hr)
  have h := norm_le_abs_integral_mul_exp (g := fun r ↦ ρ r * d ^ α) ht he hK₁0
    (hρc.mul continuousOn_const)
    (fun r hr ↦ mul_nonneg (hρ0 r hr) hdα0) he0 hbound hs
  rw [intervalIntegral.integral_mul_const, abs_mul, abs_of_nonneg hdα0] at h
  exact h.trans_eq (by ring)

/-- **Hölder bound of the top-order derivative of the flow maps on `S`**, under the hypotheses of
`norm_iteratedFDeriv_flowOn_sub_le_rpow_of_holder`, for all `x, y ∈ S`:
`‖D^m X(s) x - D^m X(s) y‖ ≤ max (|∫ₜˢ ρ| exp (K₁ |s - t|)) (2 Fm(s)) ‖x - y‖^α`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_max_rpow_of_holder
    (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b)
    (hS : ∀ s ∈ Icc a b, MapsTo (flowOn v a b s t) S S) (hm : 2 ≤ m) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {K₁ K₂ M M' L L₂ F₀ Λ : ℝ} {Km Hm Fm : ℝ → ℝ}
    (hK₁ : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (v r) y‖ ≤ K₁) (hM0 : 0 ≤ M)
    (hM : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 2 ≤ i → i < m → ‖iteratedFDeriv ℝ i (v r) y‖ ≤ M)
    (hKm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (v r) y‖ ≤ Km r)
    (hKmc : ContinuousOn Km (Icc a b)) (hK₂ : 0 ≤ K₂) (hM'0 : 0 ≤ M')
    (hLip1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (v r) y - fderiv ℝ (v r) z‖ ≤ K₂ * ‖y - z‖)
    (hHol : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 2 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (v r) y - iteratedFDeriv ℝ i (v r) z‖ ≤ M' * ‖y - z‖ ^ α)
    (hHm0 : ∀ r ∈ Icc a b, 0 ≤ Hm r)
    (hHm : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖iteratedFDeriv ℝ m (v r) y - iteratedFDeriv ℝ m (v r) z‖ ≤ Hm r * ‖y - z‖ ^ α)
    (hHmc : ContinuousOn Hm (Icc a b))
    (hL : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (flowOn v a b r t) y‖ ≤ L)
    (hXL : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖flowOn v a b r t y - flowOn v a b r t z‖ ≤ L * ‖y - z‖)
    (hF : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y‖ ≤ F₀)
    (hFm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (flowOn v a b r t) y‖ ≤ Fm r)
    (hFmc : ContinuousOn Fm (Icc a b))
    (hΛ0 : 0 ≤ Λ) (hL₂0 : 0 ≤ L₂)
    (hXd1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (flowOn v a b r t) y - fderiv ℝ (flowOn v a b r t) z‖ ≤ L₂ * ‖y - z‖)
    (hXH : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y - iteratedFDeriv ℝ i (flowOn v a b r t) z‖ ≤
        Λ * ‖y - z‖ ^ α)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m (flowOn v a b s t) x - iteratedFDeriv ℝ m (flowOn v a b s t) y‖ ≤
      max (|∫ r in t..s, flowHolderRateOfHolder m α K₂ M M' L L₂ F₀ Λ (Fm r) (Km r) (Hm r)| *
        Real.exp (K₁ * |s - t|)) (2 * Fm s) * ‖x - y‖ ^ α := by
  rcases le_or_gt ‖x - y‖ 1 with hxy | hxy
  · refine (hv.norm_iteratedFDeriv_flowOn_sub_le_rpow_of_holder hsm ht hS hm hα0 hα1 hK₁ hM0
      hM hKm hKmc hK₂ hM'0 hLip1 hHol hHm0 hHm hHmc hL hXL hF hFm hFmc hΛ0 hL₂0 hXd1 hXH hx hy
      hxy hs).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)
  · have h1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hxy.le hα0
    have hF0 : 0 ≤ Fm s := (norm_nonneg _).trans (hFm s hs x hx)
    calc _ ≤ ‖iteratedFDeriv ℝ m (flowOn v a b s t) x‖ +
          ‖iteratedFDeriv ℝ m (flowOn v a b s t) y‖ := norm_sub_le _ _
      _ ≤ 2 * Fm s := by linarith [hFm s hs x hx, hFm s hs y hy]
      _ ≤ 2 * Fm s * ‖x - y‖ ^ α := le_mul_of_one_le_right (by linarith) h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

end PDE.Analysis.ODE
