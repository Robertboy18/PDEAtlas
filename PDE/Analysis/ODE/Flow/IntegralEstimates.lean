/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.Comparison

/-!
# Grönwall's inequality with a variable coefficient and flow bounds by integrals

If `‖f'‖ ≤ A ‖f‖ + g` on `[a, b]` with `A, g ≥ 0` continuous, then
`‖f x‖ ≤ (‖f a‖ + ∫ₐˣ g) exp (∫ₐˣ A)` (`norm_le_mul_exp_integral`), and the same holds backward
from `b` (`norm_le_mul_exp_integral_left`). For a flow that preserves a set `S` on which the
derivative of the field is bounded by a continuous function `A r` of the time, the first
variation is bounded by `exp |∫ₜˢ A|` and the flow maps are Lipschitz on a convex `S` with this
constant. These are the forms used when only the time integral of `‖Dv‖` is controlled, as in
the continuation criterion of transport equations.

`norm_le_mul_exp_integral` is the differential form of Grönwall's inequality in Evans,
App. B.2(j), (15) and (16), for `η = ‖f‖`, with `‖f'‖ ≤ A ‖f‖ + g` in place of (15), and with
continuous coefficients and a differentiable `f` in place of summable coefficients and an
absolutely continuous `η`. Its proof uses Mathlib's comparison theorem
`image_norm_le_of_norm_deriv_right_lt_deriv_boundary`. `le_of_le_add_integral_of_monotoneOn`
is the integral form, B.2(k), (17) and (18), for a monotone function and at every point.

## Main results

* `norm_le_mul_exp_integral`, `norm_le_mul_exp_integral_left`: Grönwall's inequality with a
  variable coefficient, forward and backward.
* `le_of_le_add_integral_of_monotoneOn`: the integral form for monotone functions, which are
  integrable without any continuity.
* `IsC1FieldOn.norm_variationOn_le_exp_integral`: `‖J‖ ≤ exp |∫ₜˢ A|`.
* `IsC1FieldOn.norm_flowOn_sub_le_exp_integral`: the flow is `exp |∫ₜˢ A|`-Lipschitz on `S`.
* `IsC1FieldOn.hasDerivWithinAt_variationOn_inverse`: the inverse first variation solves
  `W' = -W ∘ Dv`.
* `norm_le_mul_exp_of_integral_le`: the same with the coefficient `k A`, `∫₀ᵇ A ≤ Λ`.
* `hessianTransport`, `norm_hessianTransport_le`, `norm_hessianTransport_sub_le`: the field of
  the equation of a transported second derivative and its bounds.
* `hasDerivWithinAt_of_forall_apply`, `hasDerivWithinAt_of_forall_apply_apply`: operator-valued
  functions on finite-dimensional spaces are differentiable when all their values are.
* `flowOn_eq_of_eqOn`, `IsC1FieldOn.variationOn_eq_of_eqOn`: fields that agree on an invariant set
  have the same flow and the same first variation there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. B.2(j), Gronwall's inequality (differential form),
  (15) and (16), pp. 708-709, and App. B.2(k), Gronwall's inequality (integral form), (17) and
  (18), p. 709. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace PDE.Analysis.ODE

section Gronwall

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The clamped extension of a function continuous on `[a, b]` is continuous. -/
private theorem continuous_comp_projIcc {a b : ℝ} (hab : a ≤ b) {A : ℝ → ℝ}
    (hA : ContinuousOn A (Icc a b)) : Continuous fun y ↦ A (projIcc a b hab y) :=
  hA.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun y ↦ (projIcc a b hab y).2

/-- Integrals of the clamped extension over subintervals of `[a, b]` are integrals of the
function. -/
private theorem integral_comp_projIcc {a b : ℝ} (hab : a ≤ b) (A : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Icc a b) : ∫ y in a..x, A (projIcc a b hab y) = ∫ y in a..x, A y := by
  refine intervalIntegral.integral_congr fun y hy ↦ ?_
  rw [uIcc_of_le hx.1] at hy
  simp [projIcc_of_mem hab ⟨hy.1, hy.2.trans hx.2⟩]

/-- Integrals of a function nonnegative on `[a, b]` over `[a, x] ⊆ [a, b]` are nonnegative. -/
theorem integral_nonneg_of_mem_Icc {a b : ℝ} {A : ℝ → ℝ} (hA0 : ∀ x ∈ Icc a b, 0 ≤ A x) {x : ℝ}
    (hx : x ∈ Icc a b) : 0 ≤ ∫ y in a..x, A y :=
  intervalIntegral.integral_nonneg hx.1 fun y hy ↦ hA0 y ⟨hy.1, hy.2.trans hx.2⟩

/-- **Grönwall's inequality with a variable coefficient.** If `‖f'‖ ≤ A ‖f‖ + g` on `[a, b]`
with `A, g ≥ 0` continuous on `[a, b]`, then `‖f x‖ ≤ (δ + ∫ₐˣ g) exp (∫ₐˣ A)` for
`‖f a‖ ≤ δ`. -/
theorem norm_le_mul_exp_integral {f f' : ℝ → F} {A g : ℝ → ℝ} {a b δ : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hA : ContinuousOn A (Icc a b)) (hA0 : ∀ x ∈ Icc a b, 0 ≤ A x)
    (hg : ContinuousOn g (Icc a b)) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (ha : ‖f a‖ ≤ δ) (bound : ∀ x ∈ Icc a b, ‖f' x‖ ≤ A x * ‖f x‖ + g x) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ (δ + ∫ y in a..x, g y) * Real.exp (∫ y in a..x, A y) := by
  intro x hx
  have hab : a ≤ b := hx.1.trans hx.2
  set Ac : ℝ → ℝ := fun y ↦ A (projIcc a b hab y)
  set gc : ℝ → ℝ := fun y ↦ g (projIcc a b hab y)
  have hAc : Continuous Ac := continuous_comp_projIcc hab hA
  have hgc : Continuous gc := continuous_comp_projIcc hab hg
  have hAcx (y : ℝ) (hy : y ∈ Icc a b) : Ac y = A y := by simp [Ac, projIcc_of_mem hab hy]
  have hgcx (y : ℝ) (hy : y ∈ Icc a b) : gc y = g y := by simp [gc, projIcc_of_mem hab hy]
  have hIA : ∀ y, HasDerivAt (fun z ↦ ∫ w in a..z, Ac w) (Ac y) y :=
    fun y ↦ (hAc.integral_hasStrictDerivAt a y).hasDerivAt
  have hIg : ∀ y, HasDerivAt (fun z ↦ ∫ w in a..z, gc w) (gc y) y :=
    fun y ↦ (hgc.integral_hasStrictDerivAt a y).hasDerivAt
  have hfc : ContinuousOn f (Icc a b) := fun y hy ↦ (hf y hy).continuousWithinAt
  have hf' : ∀ y ∈ Ico a b, HasDerivWithinAt f (f' y) (Ici y) y := fun y hy ↦
    (hf y (Ico_subset_Icc_self hy)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ico_mem_nhdsGE hy.2) fun z hz ↦ ⟨hy.1.trans hz.1, hz.2.le⟩)
  have hkey : ∀ ε > 0, ‖f x‖ ≤ (δ + ε * (1 + (x - a)) + ∫ y in a..x, gc y) *
      Real.exp (∫ y in a..x, Ac y) := by
    intro ε hε
    set B : ℝ → ℝ := fun y ↦ (δ + ε * (1 + (y - a)) + ∫ w in a..y, gc w) *
      Real.exp (∫ w in a..y, Ac w)
    set B' : ℝ → ℝ := fun y ↦ (ε + gc y) * Real.exp (∫ w in a..y, Ac w) +
      (δ + ε * (1 + (y - a)) + ∫ w in a..y, gc w) * (Real.exp (∫ w in a..y, Ac w) * Ac y)
    have hB : ∀ y, HasDerivAt B (B' y) y := by
      intro y
      have h1 : HasDerivAt (fun z ↦ δ + ε * (1 + (z - a)) + ∫ w in a..z, gc w) (ε + gc y) y := by
        have hlin : HasDerivAt (fun z : ℝ ↦ δ + ε * (1 + (z - a))) ε y := by
          simpa using ((((hasDerivAt_id y).sub_const a).const_add 1).const_mul ε).const_add δ
        exact hlin.add (hIg y)
      exact h1.mul ((hIA y).exp)
    have ha' : ‖f a‖ ≤ B a := by
      simp only [B, sub_self, add_zero, mul_one, intervalIntegral.integral_same, Real.exp_zero]
      linarith
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary hfc hf' ha' hB
      (fun y hy hfy ↦ ?_) hx
    have hy' : y ∈ Icc a b := Ico_subset_Icc_self hy
    have hE : 1 ≤ Real.exp (∫ w in a..y, Ac w) := by
      refine Real.one_le_exp ?_
      rw [integral_comp_projIcc hab A hy']
      exact integral_nonneg_of_mem_Icc hA0 hy'
    have hg0' : 0 ≤ g y := hg0 y hy'
    calc ‖f' y‖ ≤ A y * ‖f y‖ + g y := bound y hy'
      _ = Ac y * B y + gc y := by rw [hfy, hAcx y hy', hgcx y hy']
      _ < B' y := by
        have h₁ : gc y < (ε + gc y) * Real.exp (∫ w in a..y, Ac w) := by
          rw [hgcx y hy']
          nlinarith
        simp only [B, B']
        nlinarith
  have hlim : ‖f x‖ ≤ (δ + ∫ y in a..x, gc y) * Real.exp (∫ y in a..x, Ac y) := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    set c := (1 + (x - a)) * Real.exp (∫ y in a..x, Ac y)
    have hc : 0 < c := mul_pos (by linarith [hx.1]) (Real.exp_pos _)
    have h := hkey (ε / c) (div_pos hε hc)
    calc ‖f x‖ ≤ (δ + ε / c * (1 + (x - a)) + ∫ y in a..x, gc y) *
          Real.exp (∫ y in a..x, Ac y) := h
      _ = (δ + ∫ y in a..x, gc y) * Real.exp (∫ y in a..x, Ac y) + ε := by
        field_simp [c]
        ring
  rwa [integral_comp_projIcc hab A hx, integral_comp_projIcc hab g hx] at hlim

/-- **Grönwall's inequality with a variable coefficient, backward.** If `‖f'‖ ≤ A ‖f‖ + g` on
`[a, b]` with `A, g ≥ 0` continuous on `[a, b]` and `‖f b‖ ≤ δ`, then
`‖f x‖ ≤ (δ + ∫ₓᵇ g) exp (∫ₓᵇ A)` on `[a, b]`. -/
theorem norm_le_mul_exp_integral_left {f f' : ℝ → F} {A g : ℝ → ℝ} {a b δ : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hA : ContinuousOn A (Icc a b)) (hA0 : ∀ x ∈ Icc a b, 0 ≤ A x)
    (hg : ContinuousOn g (Icc a b)) (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hb : ‖f b‖ ≤ δ) (bound : ∀ x ∈ Icc a b, ‖f' x‖ ≤ A x * ‖f x‖ + g x) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ (δ + ∫ y in x..b, g y) * Real.exp (∫ y in x..b, A y) := by
  have hmaps : MapsTo (fun y : ℝ ↦ -y) (Icc (-b) (-a)) (Icc a b) := fun y hy ↦
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hneg (x : ℝ) (hx : x ∈ Icc (-b) (-a)) : -x ∈ Icc a b := hmaps hx
  have hrev : ∀ y ∈ Icc (-b) (-a),
      HasDerivWithinAt (fun z ↦ f (-z)) (-f' (-y)) (Icc (-b) (-a)) y := by
    intro y hy
    have h := (hf (-y) (hneg y hy)).scomp y (hasDerivAt_neg y).hasDerivWithinAt hmaps
    simpa [Function.comp_def] using h
  have hcomp (h : ℝ → ℝ) (hc : ContinuousOn h (Icc a b)) :
      ContinuousOn (fun z ↦ h (-z)) (Icc (-b) (-a)) :=
    hc.comp continuous_neg.continuousOn hmaps
  have h := norm_le_mul_exp_integral (f := fun z ↦ f (-z)) (f' := fun z ↦ -f' (-z))
    (A := fun z ↦ A (-z)) (g := fun z ↦ g (-z)) (δ := δ) hrev (hcomp A hA)
    (fun y hy ↦ hA0 _ (hneg y hy)) (hcomp g hg) (fun y hy ↦ hg0 _ (hneg y hy))
    (by simpa using hb) (fun y hy ↦ by simpa using bound (-y) (hneg y hy))
  intro x hx
  have hx' : -x ∈ Icc (-b) (-a) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hI (h : ℝ → ℝ) : ∫ y in (-b)..(-x), h (-y) = ∫ y in x..b, h y := by
    rw [intervalIntegral.integral_comp_neg]
    simp
  simpa [hI A, hI g] using h (-x) hx'


/-- **Grönwall's inequality for monotone functions.** A function monotone on `[0, b]` with
`y s ≤ c + C ∫₀ˢ y` for `c, C ≥ 0` satisfies `y s ≤ c (1 + C s exp (C s))`. -/
theorem le_of_le_add_integral_of_monotoneOn {y : ℝ → ℝ} {b c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hy : MonotoneOn y (Icc 0 b)) (hle : ∀ s ∈ Icc 0 b, y s ≤ c + C * ∫ r in (0)..s, y r) :
    ∀ s ∈ Icc 0 b, y s ≤ c * (1 + C * s * Real.exp (C * s)) := by
  intro s₀ hs₀
  have hb : 0 ≤ b := hs₀.1.trans hs₀.2
  have hint : ∀ s ∈ Icc 0 b, IntervalIntegrable y volume 0 s := fun s hs ↦
    (hy.mono (by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)).intervalIntegrable
  set G : ℝ → ℝ := fun s ↦ C * ∫ r in (0)..s, y r
  have hG : ContinuousOn G (Icc 0 b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := b)
      (by rw [uIcc_of_le hb]; exact hy.integrableOn_isCompact isCompact_Icc)
    rw [uIcc_of_le hb] at h
    exact continuousOn_const.mul h
  have hyG : ∀ s ∈ Icc 0 b, y s ≤ c + G s := hle
  have hGle : ∀ s ∈ Icc 0 b, G s ≤ ∫ r in (0)..s, (C * G r + C * c) := by
    intro s hs
    have hGi : IntervalIntegrable (fun r ↦ C * G r + C * c) volume 0 s :=
      ((continuousOn_const.mul (hG.mono (Icc_subset_Icc le_rfl hs.2))).add
        continuousOn_const).intervalIntegrable_of_Icc hs.1
    calc G s = C * ∫ r in (0)..s, y r := rfl
      _ ≤ C * ∫ r in (0)..s, (c + G r) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          have hcG : ContinuousOn (fun r ↦ c + G r) (Icc 0 s) :=
            continuousOn_const.add (hG.mono (Icc_subset_Icc le_rfl hs.2))
          have hci : IntervalIntegrable (fun r ↦ c + G r) volume 0 s :=
            hcG.intervalIntegrable_of_Icc hs.1
          exact intervalIntegral.integral_mono_on hs.1 (hint s hs) hci
            fun r hr ↦ hyG r ⟨hr.1, hr.2.trans hs.2⟩
      _ = ∫ r in (0)..s, (C * G r + C * c) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext r
          ring
  have h := le_exp_mul_integral_of_le_integral hC hG intervalIntegrable_const
    (fun _ _ ↦ mul_nonneg hC hc) hGle s₀ hs₀
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  calc y s₀ ≤ c + G s₀ := hyG s₀ hs₀
    _ ≤ c + Real.exp (C * s₀) * (s₀ * (C * c)) := by linarith
    _ = c * (1 + C * s₀ * Real.exp (C * s₀)) := by ring

/-- **Grönwall's inequality with a coefficient of bounded integral.** If `‖f'‖ ≤ k A ‖f‖ + g` on
`[0, b]` with `k ≥ 0`, `A, g ≥ 0` continuous and `∫₀ᵇ A ≤ Λ`, then
`‖f r‖ ≤ (δ + ∫₀ʳ g) exp (k Λ)` on `[0, b]` for `‖f 0‖ ≤ δ`. -/
theorem norm_le_mul_exp_of_integral_le {f f' : ℝ → F} {A g : ℝ → ℝ} {b k Λ δ : ℝ} (hk : 0 ≤ k)
    (hf : ∀ x ∈ Icc 0 b, HasDerivWithinAt f (f' x) (Icc 0 b) x) (hA : ContinuousOn A (Icc 0 b))
    (hA0 : ∀ x ∈ Icc 0 b, 0 ≤ A x) (hΛ : ∫ x in (0)..b, A x ≤ Λ) (hg : ContinuousOn g (Icc 0 b))
    (hg0 : ∀ x ∈ Icc 0 b, 0 ≤ g x) (h0 : ‖f 0‖ ≤ δ)
    (bound : ∀ x ∈ Icc 0 b, ‖f' x‖ ≤ k * A x * ‖f x‖ + g x) {r : ℝ} (hr : r ∈ Icc 0 b) :
    ‖f r‖ ≤ (δ + ∫ x in (0)..r, g x) * Real.exp (k * Λ) := by
  have h := norm_le_mul_exp_integral (A := fun x ↦ k * A x) hf (continuousOn_const.mul hA)
    (fun x hx ↦ mul_nonneg hk (hA0 x hx)) hg hg0 h0 bound r hr
  have hAr : ∫ x in (0)..r, A x ≤ Λ := by
    refine le_trans ?_ hΛ
    refine intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2 ?_
      (hA.intervalIntegrable_of_Icc (hr.1.trans hr.2))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hA0 x ⟨hx.1.le, hx.2⟩
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h0
  refine h.trans (mul_le_mul_of_nonneg_left ?_
    (add_nonneg hδ (integral_nonneg_of_mem_Icc hg0 hr)))
  rw [intervalIntegral.integral_const_mul]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hAr hk)

end Gronwall

/-! ### The transport field of a second derivative -/

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The right-hand side `-H[D ·, ·] - H[·, D ·] - G ∘ T` of the equation of the second
derivative `H` of a quantity carried by a flow, with `D` and `T` the first and second derivatives
of the field and `G` the first derivative of the quantity. -/
def hessianTransport (H : E →L[ℝ] E →L[ℝ] F) (D : E →L[ℝ] E) (G : E →L[ℝ] F)
    (T : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] F :=
  -H.comp D - ((ContinuousLinearMap.compL ℝ E E F).flip D).comp H -
    (ContinuousLinearMap.compL ℝ E E F G).comp T

/-- The norm of `L ↦ L ∘ D` is at most the norm of `D`. -/
theorem norm_compL_flip_le (D : E →L[ℝ] E) :
    ‖(ContinuousLinearMap.compL ℝ E E F).flip D‖ ≤ ‖D‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun L ↦
    (L.opNorm_comp_le D).trans_eq (mul_comm _ _)

/-- `‖-H[D ·, ·] - H[·, D ·] - G ∘ T‖ ≤ 2 ‖D‖ ‖H‖ + ‖G‖ ‖T‖`. -/
theorem norm_hessianTransport_le (H : E →L[ℝ] E →L[ℝ] F) (D : E →L[ℝ] E) (G : E →L[ℝ] F)
    (T : E →L[ℝ] E →L[ℝ] E) : ‖hessianTransport H D G T‖ ≤ 2 * ‖D‖ * ‖H‖ + ‖G‖ * ‖T‖ := by
  have h1 : ‖H.comp D‖ ≤ ‖D‖ * ‖H‖ := (H.opNorm_comp_le D).trans_eq (mul_comm _ _)
  have h2 : ‖((ContinuousLinearMap.compL ℝ E E F).flip D).comp H‖ ≤ ‖D‖ * ‖H‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_compL_flip_le D) (norm_nonneg _))
  have h3 : ‖(ContinuousLinearMap.compL ℝ E E F G).comp T‖ ≤ ‖G‖ * ‖T‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_compL_apply_le (E := E) G) (norm_nonneg _))
  rw [hessianTransport]
  calc ‖-H.comp D - ((ContinuousLinearMap.compL ℝ E E F).flip D).comp H -
        (ContinuousLinearMap.compL ℝ E E F G).comp T‖
      ≤ ‖H.comp D‖ + ‖((ContinuousLinearMap.compL ℝ E E F).flip D).comp H‖ +
          ‖(ContinuousLinearMap.compL ℝ E E F G).comp T‖ := by
        have := norm_sub_le (-H.comp D - ((ContinuousLinearMap.compL ℝ E E F).flip D).comp H)
          ((ContinuousLinearMap.compL ℝ E E F G).comp T)
        have := norm_sub_le (-H.comp D) (((ContinuousLinearMap.compL ℝ E E F).flip D).comp H)
        rw [ContinuousLinearMap.opNorm_neg] at this
        linarith
    _ ≤ 2 * ‖D‖ * ‖H‖ + ‖G‖ * ‖T‖ := by linarith

/-- The difference of two transport fields:
`‖hessianTransport H D G T - hessianTransport H' D' G' T'‖ ≤
2 ‖D‖ ‖H - H'‖ + 2 ‖H'‖ ‖D - D'‖ + ‖G - G'‖ ‖T‖ + ‖G'‖ ‖T - T'‖`. -/
theorem norm_hessianTransport_sub_le (H H' : E →L[ℝ] E →L[ℝ] F) (D D' : E →L[ℝ] E)
    (G G' : E →L[ℝ] F) (T T' : E →L[ℝ] E →L[ℝ] E) :
    ‖hessianTransport H D G T - hessianTransport H' D' G' T'‖ ≤
      2 * ‖D‖ * ‖H - H'‖ + 2 * ‖H'‖ * ‖D - D'‖ + ‖G - G'‖ * ‖T‖ + ‖G'‖ * ‖T - T'‖ := by
  have hsplit : hessianTransport H D G T - hessianTransport H' D' G' T' =
      hessianTransport (H - H') D (G - G') T +
        (-H'.comp (D - D') - ((ContinuousLinearMap.compL ℝ E E F).flip (D - D')).comp H' -
          (ContinuousLinearMap.compL ℝ E E F G').comp (T - T')) := by
    simp only [hessianTransport, map_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_sub]
    abel
  have h1 : ‖H'.comp (D - D')‖ ≤ ‖H'‖ * ‖D - D'‖ := H'.opNorm_comp_le _
  have h2 : ‖((ContinuousLinearMap.compL ℝ E E F).flip (D - D')).comp H'‖ ≤ ‖H'‖ * ‖D - D'‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right
      (norm_compL_flip_le (D - D')) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have h3 : ‖(ContinuousLinearMap.compL ℝ E E F G').comp (T - T')‖ ≤ ‖G'‖ * ‖T - T'‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_compL_apply_le (E := E) G') (norm_nonneg _))
  have h4 := norm_hessianTransport_le (H - H') D (G - G') T
  have h5 : ‖-H'.comp (D - D') - ((ContinuousLinearMap.compL ℝ E E F).flip (D - D')).comp H' -
      (ContinuousLinearMap.compL ℝ E E F G').comp (T - T')‖ ≤
        2 * ‖H'‖ * ‖D - D'‖ + ‖G'‖ * ‖T - T'‖ := by
    have := norm_sub_le
      (-H'.comp (D - D') - ((ContinuousLinearMap.compL ℝ E E F).flip (D - D')).comp H')
      ((ContinuousLinearMap.compL ℝ E E F G').comp (T - T'))
    have := norm_sub_le (-H'.comp (D - D'))
      (((ContinuousLinearMap.compL ℝ E E F).flip (D - D')).comp H')
    rw [ContinuousLinearMap.opNorm_neg] at this
    linarith
  rw [hsplit]
  have := norm_add_le (hessianTransport (H - H') D (G - G') T)
    (-H'.comp (D - D') - ((ContinuousLinearMap.compL ℝ E E F).flip (D - D')).comp H' -
      (ContinuousLinearMap.compL ℝ E E F G').comp (T - T'))
  linarith

/-- `‖H[·, e] - Z ∘ D‖ ≤ ‖e‖ ‖H‖ + ‖D‖ ‖Z‖`. -/
theorem norm_apply_comp_sub_comp_le (e : E) (H : E →L[ℝ] E →L[ℝ] F) (Z : E →L[ℝ] F)
    (D : E →L[ℝ] E) :
    ‖(ContinuousLinearMap.apply ℝ F e).comp H - Z.comp D‖ ≤ ‖e‖ * ‖H‖ + ‖D‖ * ‖Z‖ := by
  have h1 : ‖(ContinuousLinearMap.apply ℝ F e).comp H‖ ≤ ‖e‖ * ‖H‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
      calc ‖H u e‖ ≤ ‖H u‖ * ‖e‖ := (H u).le_opNorm e
        _ ≤ ‖H‖ * ‖u‖ * ‖e‖ := mul_le_mul_of_nonneg_right (H.le_opNorm u) (norm_nonneg _)
        _ = ‖e‖ * ‖H‖ * ‖u‖ := by ring
  have h2 : ‖Z.comp D‖ ≤ ‖D‖ * ‖Z‖ := (Z.opNorm_comp_le D).trans_eq (mul_comm _ _)
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- The difference of two such fields:
`‖(H[·, e] - Z ∘ D) - (H'[·, e] - Z' ∘ D')‖ ≤ ‖e‖ ‖H - H'‖ + ‖D‖ ‖Z - Z'‖ + ‖Z'‖ ‖D - D'‖`. -/
theorem norm_apply_comp_sub_comp_sub_le (e : E) (H H' : E →L[ℝ] E →L[ℝ] F) (Z Z' : E →L[ℝ] F)
    (D D' : E →L[ℝ] E) :
    ‖((ContinuousLinearMap.apply ℝ F e).comp H - Z.comp D) -
        ((ContinuousLinearMap.apply ℝ F e).comp H' - Z'.comp D')‖ ≤
      ‖e‖ * ‖H - H'‖ + ‖D‖ * ‖Z - Z'‖ + ‖Z'‖ * ‖D - D'‖ := by
  have hsplit : ((ContinuousLinearMap.apply ℝ F e).comp H - Z.comp D) -
      ((ContinuousLinearMap.apply ℝ F e).comp H' - Z'.comp D') =
        ((ContinuousLinearMap.apply ℝ F e).comp (H - H') - (Z - Z').comp D) -
          Z'.comp (D - D') := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_apply_comp_sub_comp_le e (H - H') (Z - Z') D
  have h2 : ‖Z'.comp (D - D')‖ ≤ ‖Z'‖ * ‖D - D'‖ := Z'.opNorm_comp_le _
  linarith

end Transport

/-! ### Derivatives of operator-valued functions on finite-dimensional spaces -/

section OperatorValued

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map on a finite-dimensional space is the sum over a basis of the
coordinate functionals times its values on the basis. -/
theorem sum_coord_smulRight {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (L : E →L[ℝ] F) :
    (∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (L (b i))) = L := by
  ext u
  have hu : L u = L (∑ i, (b.repr u) i • b i) := by rw [b.sum_repr]
  rw [hu, map_sum]
  simp [Module.Basis.coord_apply]

/-- **Derivatives of operator-valued functions from their values.** On a finite-dimensional
space, if `r ↦ f r u` has derivative `f' u` for every `u`, then `f` has derivative `f'`. -/
theorem hasDerivWithinAt_of_forall_apply {f : ℝ → E →L[ℝ] F} {f' : E →L[ℝ] F} {s : Set ℝ}
    {x : ℝ} (h : ∀ u, HasDerivWithinAt (fun r ↦ f r u) (f' u) s x) :
    HasDerivWithinAt f f' s x := by
  have hterm (i : Fin (Module.finrank ℝ E)) :
      HasDerivWithinAt (fun r ↦ (LinearMap.toContinuousLinearMap
        ((Module.finBasis ℝ E).coord i)).smulRight (f r (Module.finBasis ℝ E i)))
        ((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).smulRight
          (f' (Module.finBasis ℝ E i))) s x :=
    HasFDerivAt.comp_hasDerivWithinAt x
      (ContinuousLinearMap.smulRightL ℝ E F
        (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i))).hasFDerivAt
      (h (Module.finBasis ℝ E i))
  have hsum := HasDerivWithinAt.sum (u := Finset.univ) fun i _ ↦ hterm i
  have hfun : (fun r ↦ ∑ i ∈ Finset.univ, (LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ E).coord i)).smulRight (f r (Module.finBasis ℝ E i))) = f :=
    funext fun r ↦ sum_coord_smulRight _ (f r)
  rwa [Finset.sum_fn, hfun, sum_coord_smulRight] at hsum

/-- The bilinear version of `hasDerivWithinAt_of_forall_apply`. -/
theorem hasDerivWithinAt_of_forall_apply_apply {f : ℝ → E →L[ℝ] E →L[ℝ] F}
    {f' : E →L[ℝ] E →L[ℝ] F} {s : Set ℝ} {x : ℝ}
    (h : ∀ u w, HasDerivWithinAt (fun r ↦ f r u w) (f' u w) s x) :
    HasDerivWithinAt f f' s x :=
  hasDerivWithinAt_of_forall_apply fun u ↦ hasDerivWithinAt_of_forall_apply fun w ↦ h u w

end OperatorValued

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b : ℝ} {K₀ : ℝ≥0} {S : Set E} {A : ℝ → ℝ}

namespace IsC1FieldOn

/-- The first variation along the flow line is inverted by the first variation back to the base
time: `variationOn t s (flowOn s t x) ∘ variationOn s t x = id` and the composition in the other
order is the identity as well. -/
theorem variationOn_comp_variationOn_flowOn (hv : IsC1FieldOn v Dv a b K₀) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    (variationOn v Dv a b s t x).comp (variationOn v Dv a b t s (flowOn v a b s t x)) =
      ContinuousLinearMap.id ℝ E := by
  have h := hv.variationOn_flowOn_comp_variationOn ht hs (flowOn v a b s t x)
  rwa [hv.isLipschitzFieldOn.flowOn_flowOn_self hs ht x] at h

/-- **The time derivative of the inverse first variation.** With `J r = variationOn r t x` and
`W r = variationOn t r (flowOn r t x)` its inverse, `W' = -W ∘ Dv(r, flowOn r t x)` within
`[a, b]`. -/
theorem hasDerivWithinAt_variationOn_inverse (hv : IsC1FieldOn v Dv a b K₀) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasDerivWithinAt (fun r ↦ variationOn v Dv a b t r (flowOn v a b r t x))
      (-(variationOn v Dv a b t s (flowOn v a b s t x)).comp (Dv s (flowOn v a b s t x)))
      (Icc a b) s := by
  set J : ℝ → E →L[ℝ] E := fun r ↦ variationOn v Dv a b r t x
  set W : ℝ → E →L[ℝ] E := fun r ↦ variationOn v Dv a b t r (flowOn v a b r t x)
  have hunit (r : ℝ) (hr : r ∈ Icc a b) : ∃ u : (E →L[ℝ] E)ˣ, (u : E →L[ℝ] E) = J r ∧
      ((u⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) = W r :=
    ⟨⟨J r, W r, hv.variationOn_comp_variationOn_flowOn hr ht x,
      hv.variationOn_flowOn_comp_variationOn hr ht x⟩, rfl, rfl⟩
  have hinv (r : ℝ) (hr : r ∈ Icc a b) : W r = Ring.inverse (J r) := by
    obtain ⟨u, hu, hu'⟩ := hunit r hr
    rw [← hu, Ring.inverse_unit, hu']
  obtain ⟨u, hu, hu'⟩ := hunit s hs
  have hd : HasFDerivAt (Ring.inverse : (E →L[ℝ] E) → E →L[ℝ] E)
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (W s) (W s)) (J s) := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [hu, hu'] at h
  have hJ := (hv.hasDerivAt_variationOn hs ht x).hasDerivWithinAt (s := Icc a b)
  have hcomp := hd.comp_hasDerivWithinAt s hJ
  have heq : (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (W s) (W s))
      ((Dv s (flowOn v a b s t x)).comp (J s)) =
        -(W s).comp (Dv s (flowOn v a b s t x)) := by
    rw [neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    congr 1
    change (W s).comp (((Dv s (flowOn v a b s t x)).comp (J s)).comp (W s)) = _
    rw [ContinuousLinearMap.comp_assoc, hv.variationOn_comp_variationOn_flowOn hs ht x,
      ContinuousLinearMap.comp_id]
  rw [heq] at hcomp
  exact hcomp.congr_of_mem (fun r hr ↦ hinv r hr) hs

/-- **Bound of the first variation by an integral.** If the flow keeps `S` and `‖Dv r‖ ≤ A r` on
`S` with `A ≥ 0` continuous on `[a, b]`, then `‖variationOn v Dv a b s t x‖ ≤ exp |∫ₜˢ A|` for
`x ∈ S`. -/
theorem norm_variationOn_le_exp_integral (hv : IsC1FieldOn v Dv a b K₀)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hA : ContinuousOn A (Icc a b)) (hA0 : ∀ r ∈ Icc a b, 0 ≤ A r)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ A r) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) :
    ‖variationOn v Dv a b s t x‖ ≤ Real.exp |∫ r in t..s, A r| := by
  have hbound (c d : ℝ) (hcd : Icc c d ⊆ Icc a b) : ∀ r ∈ Icc c d,
      ‖(Dv r (flowOn v a b r t x)).comp (variationOn v Dv a b r t x)‖ ≤
        A r * ‖variationOn v Dv a b r t x‖ + 0 := fun r hr ↦ by
    rw [add_zero]
    exact ((Dv r _).opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right
      (hDv r (hcd hr) _ (hS r (hcd hr) t ht hx)) (norm_nonneg _))
  have hJt : ‖variationOn v Dv a b t t x‖ ≤ 1 := by
    rw [hv.variationOn_self ht]
    exact ContinuousLinearMap.norm_id_le
  rcases le_total t s with hts | hst
  · have hsub : Icc t s ⊆ Icc a b := Icc_subset_Icc ht.1 hs.2
    have h := norm_le_mul_exp_integral (g := fun _ ↦ 0)
      (fun r hr ↦ (hv.hasDerivAt_variationOn (hsub hr) ht x).hasDerivWithinAt)
      (hA.mono hsub) (fun r hr ↦ hA0 r (hsub hr)) continuousOn_const (fun _ _ ↦ le_rfl)
      hJt (hbound t s hsub) s ⟨hts, le_rfl⟩
    have hpos : 0 ≤ ∫ r in t..s, A r :=
      intervalIntegral.integral_nonneg hts fun r hr ↦ hA0 r (hsub hr)
    simpa [abs_of_nonneg hpos] using h
  · have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have h := norm_le_mul_exp_integral_left (g := fun _ ↦ 0)
      (fun r hr ↦ (hv.hasDerivAt_variationOn (hsub hr) ht x).hasDerivWithinAt)
      (hA.mono hsub) (fun r hr ↦ hA0 r (hsub hr)) continuousOn_const (fun _ _ ↦ le_rfl)
      hJt (hbound s t hsub) s ⟨le_rfl, hst⟩
    have hpos : 0 ≤ ∫ r in s..t, A r :=
      intervalIntegral.integral_nonneg hst fun r hr ↦ hA0 r (hsub hr)
    rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hpos]
    simpa using h

/-- **Lipschitz bound of the flow by an integral** on a convex invariant set. -/
theorem norm_flowOn_sub_le_exp_integral (hv : IsC1FieldOn v Dv a b K₀) (hSc : Convex ℝ S)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hA : ContinuousOn A (Icc a b))
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ A r) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖flowOn v a b s t x - flowOn v a b s t y‖ ≤ Real.exp |∫ r in t..s, A r| * ‖x - y‖ :=
  hSc.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := flowOn v a b s t)
    (f' := fun z ↦ variationOn v Dv a b s t z)
    (fun z _ ↦ (hv.hasFDerivAt_flowOn hs ht z).hasFDerivWithinAt)
    (fun _ hz ↦ hv.norm_variationOn_le_exp_integral hS hA
      (fun r hr ↦ (norm_nonneg _).trans (hDv r hr x hx)) hDv hs ht hz) hy hx

end IsC1FieldOn

/-! ### Fields that agree on an invariant set -/

/-- **Flows of fields that agree on an invariant set.** If the flow of `v'` keeps `S` and
`v = v'` on `S`, the two flows agree on `S`. -/
theorem flowOn_eq_of_eqOn {v' : ℝ → E → E} {K₁ : ℝ≥0} (hv : IsLipschitzFieldOn v a b K₀)
    (hv' : IsLipschitzFieldOn v' a b K₁)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v' a b s t) S S)
    (heq : ∀ r ∈ Icc a b, ∀ y ∈ S, v r y = v' r y) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) : flowOn v a b s t x = flowOn v' a b s t x :=
  (hv.eq_flowOn_of_hasDerivWithinAt subset_rfl ht (hv'.flowOn_self ht x) (fun r hr ↦ by
    rw [heq r hr _ (hS r hr t ht hx)]
    exact hv'.hasDerivWithinAt_flowOn hr ht x) s hs).symm

namespace IsC1FieldOn

/-- **Variations of fields that agree on an invariant set.** If the flow of `v'` keeps `S` and
`v = v'`, `Dv = Dv'` on `S`, the two first variations agree on `S`. -/
theorem variationOn_eq_of_eqOn {v' : ℝ → E → E} {Dv' : ℝ → E → E →L[ℝ] E} {K₁ : ℝ≥0}
    (hv : IsC1FieldOn v Dv a b K₀) (hv' : IsC1FieldOn v' Dv' a b K₁)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v' a b s t) S S)
    (heq : ∀ r ∈ Icc a b, ∀ y ∈ S, v r y = v' r y)
    (hDeq : ∀ r ∈ Icc a b, ∀ y ∈ S, Dv r y = Dv' r y) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) :
    variationOn v Dv a b s t x = variationOn v' Dv' a b s t x := by
  have hflow (r : ℝ) (hr : r ∈ Icc a b) : flowOn v a b r t x = flowOn v' a b r t x :=
    flowOn_eq_of_eqOn hv.isLipschitzFieldOn hv'.isLipschitzFieldOn hS heq hr ht hx
  refine ((hv.isLipschitzFieldOn_variation ht x).eq_flowOn_of_hasDerivWithinAt
    (γ := fun r ↦ variationOn v' Dv' a b r t x) subset_rfl ht
    (hv'.variationOn_self ht x) (fun r hr ↦ ?_) s hs).symm
  have h := hv'.hasDerivWithinAt_variationOn hr ht x
  rwa [← hflow r hr, ← hDeq r hr _ (by rw [hflow r hr]; exact hS r hr t ht hx)] at h

end IsC1FieldOn

/-- Differences of continuous functions with values in bilinear maps are continuous. Instance
search does not find `ContinuousSub` for `E →L[ℝ] E →L[ℝ] F`, so the instance is given. -/
theorem continuousOn_sub_bilinear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : ℝ → E →L[ℝ] E →L[ℝ] F} {s : Set ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ f x - g x) s :=
  @ContinuousOn.sub _ _ _ _ _
    (@IsTopologicalAddGroup.to_continuousSub (E →L[ℝ] E →L[ℝ] F) _ _ _) _ _ _ hf hg

/-- Norms of continuous functions with values in bilinear maps are continuous, with the operator
norm of `E →L[ℝ] E →L[ℝ] F` fixed for elaboration. -/
theorem continuousOn_norm_bilinear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E →L[ℝ] E →L[ℝ] F} {s : Set ℝ}
    (hf : ContinuousOn f s) : ContinuousOn (fun x ↦ ‖f x‖) s :=
  ContinuousOn.norm (E := E →L[ℝ] E →L[ℝ] F) hf

end PDE.Analysis.ODE
