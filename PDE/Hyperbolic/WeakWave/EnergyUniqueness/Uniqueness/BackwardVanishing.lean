/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PDE.Analysis.Evolution.Core.Gronwall

/-!
# Vanishing from the backward estimate

The Grönwall step of the uniqueness proof for weak solutions of second-order hyperbolic
equations (Evans, §7.2.2), separated from the coefficient calculation. Suppose that for
every terminal time `σ ∈ [d, e]` the backward estimate

`½ ‖u_H(σ)‖²_H + ½ κ ‖v_σ(d)‖²_V ≤ ½ L_A ∫_d^σ ‖v_σ‖² + ½ L_R (∫_d^σ ‖J u‖² + ∫_d^σ ‖v_σ‖²)`

holds, where `v_σ(t) = ∫ₜ^σ u`. Writing `w(t) = ∫_d^t u`, so that `v_σ(t) = w(σ) - w(t)`, and
using `‖w(σ) - w(t)‖² ≤ 2 ‖w(σ)‖² + 2 ‖w(t)‖²`, the term in `‖w(σ)‖²` on the right can be
absorbed into the left when `(2 (L_A + L_R) / κ)(e - d) < 1`. What remains is an integral
inequality for a continuous energy of the form `‖u_H(t)‖² + c ‖w(t)‖²`, and Grönwall's
inequality forces it to vanish on `[d, e]`.

## Main results

* `continuousDisplacement_eq_zero_of_backward_estimate`: under the estimate and the shortness
  condition, both the continuous displacement representative and `w(t) = ∫_d^t u` vanish on
  `[d, e]`.

## Implementation notes

The theorem takes the estimate as a hypothesis and mentions no coefficients, so the initial
interval and every restarted interval of the finite-partition argument share one proof. The
coefficient-level version is `continuousDisplacement_eq_zero_of_short_subinterval` in
`ShortInterval`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, step 2 (equation (41) and
  Gronwall's inequality).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}

/--
Short-time vanishing from Evans's backward estimate.

This theorem isolates the Grönwall portion of the uniqueness proof from the
coefficient calculation.  It assumes estimate (40) for every terminal time
in `[d,e]`, rewrites the backward primitive as
`w(σ)-w(t)` for `w(t)=∫_d^t u`, absorbs the short-interval endpoint term, and
proves that both the continuous pivot representative and `w` vanish.

Keeping this assembly theorem coefficient-free lets the initial interval and
every restarted interval share exactly the same proof.
-/
theorem continuousDisplacement_eq_zero_of_backward_estimate (hab : a < b)
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    {d e : ℝ} (hd : d ∈ Set.Icc a b) (he : e ∈ Set.Icc a b) (hde : d ≤ e) (κ LA LR : ℝ) (hκ : 0 < κ)
    (hLA : 0 ≤ LA) (hLR : 0 ≤ LR)
    (hestimate : ∀ σ ∈ Set.Icc d e, (1 / 2 : ℝ) * ‖E.representative σ‖ ^ 2 + (1 / 2 : ℝ) * κ *
      ‖backwardTimePrimitive (fun r ↦ u r) σ d‖ ^ 2 ≤ (1 / 2 : ℝ) * LA *
      (∫ t in d..σ, ‖backwardTimePrimitive (fun r ↦ u r) σ t‖ ^ 2) + (1 / 2 : ℝ) * LR *
      ((∫ t in d..σ, ‖T.inclusion (u t)‖ ^ 2) +
      (∫ t in d..σ, ‖backwardTimePrimitive (fun r ↦ u r) σ t‖ ^ 2)))
    (hshort : (2 * (LA + LR) / κ) * (e - d) < 1) :
    ∀ t ∈ Set.Icc d e, E.representative t = 0 ∧ (∫ r in d..t, u r) = 0 := by
  have hlocalSubset : uIcc d e ⊆ uIcc a b :=
    uIcc_subset_uIcc (Icc_subset_uIcc hd) (Icc_subset_uIcc he)
  have huDE : IntervalIntegrable (fun t ↦ u t) volume d e :=
    (intervalIntegrable_coeFn_L2_restrict_Ioc u hab.le).mono_set hlocalSubset
  let w : ℝ → V := fun t ↦ ∫ r in d..t, u r
  have hwContinuous : ContinuousOn w (Icc d e) := by
    simpa only [uIcc_of_le hde, w] using
      intervalIntegral.continuousOn_primitive_interval' huDE left_mem_uIcc
  have hEContinuous : ContinuousOn E.representative (Icc d e) :=
    E.continuousOn.mono fun t ht ↦ hlocalSubset (Icc_subset_uIcc ht)
  suffices h : ∀ t ∈ Icc d e, ‖E.representative t‖ ^ 2 + κ * ‖w t‖ ^ 2 = 0 by
    intro t ht
    obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (by positivity)).1 (h t ht)
    exact ⟨by simpa using h1, by simpa [w, hκ.ne'] using h2⟩
  refine eq_zero_on_of_le_integral_add_length_mul_self (C := 2 * (LA + LR) / κ + LR) hde
    ((hEContinuous.norm.pow 2).add ((hwContinuous.norm.pow 2).const_mul κ))
    (fun t _ ↦ by positivity) (div_nonneg (by linarith) hκ.le) hshort fun σ hσ ↦ ?_
  have hsub : uIcc d σ ⊆ uIcc d e := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hσ)
  let v : ℝ → V := backwardTimePrimitive (fun r ↦ u r) σ
  have hvContinuous : ContinuousOn v (Icc d σ) := by
    simpa only [uIcc_of_le hσ.1, v] using
      continuousOn_backwardTimePrimitive (huDE.mono_set hsub) right_mem_uIcc
  have hwSq : IntervalIntegrable (fun t ↦ ‖w t‖ ^ 2) volume d σ :=
    ((hwContinuous.mono (Icc_subset_Icc_right hσ.2)).norm.pow 2).intervalIntegrable_of_Icc hσ.1
  refine backward_energy_estimate_to_gronwall (W := ‖w σ‖ ^ 2) (V := ∫ t in d..σ, ‖v t‖ ^ 2)
    (Iw := ∫ t in d..σ, ‖w t‖ ^ 2) hκ hLA hLR (sq_nonneg _)
    (intervalIntegral.integral_nonneg hσ.1 fun _ _ ↦ sq_nonneg _)
    (intervalIntegral.integral_nonneg hσ.1 fun _ _ ↦ sq_nonneg _) (sub_nonneg.mpr hσ.1)
    (hestimate σ hσ) ?_ rfl ?_
  · calc (∫ t in d..σ, ‖v t‖ ^ 2) ≤ ∫ t in d..σ, 2 * ‖w σ‖ ^ 2 + 2 * ‖w t‖ ^ 2 :=
          intervalIntegral.integral_mono_on hσ.1
            ((hvContinuous.norm.pow 2).intervalIntegrable_of_Icc hσ.1)
            (intervalIntegrable_const.add (hwSq.const_mul 2)) fun t ht ↦ by
              simpa only [v, w] using norm_sq_backwardTimePrimitive_le_forward huDE
                (Icc_subset_uIcc hσ) (Icc_subset_uIcc ⟨ht.1, ht.2.trans hσ.2⟩)
      _ = _ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hwSq.const_mul 2),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        ring
  · have hESq : IntervalIntegrable (fun t ↦ ‖E.representative t‖ ^ 2) volume d σ :=
      ((hEContinuous.mono (Icc_subset_Icc_right hσ.2)).norm.pow 2).intervalIntegrable_of_Icc hσ.1
    rw [intervalIntegral.integral_add hESq (hwSq.const_mul κ), intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr_ae_restrict ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun t ht ↦ hlocalSubset (hsub (uIoc_subset_uIcc ht))) E.ae_eq_inclusion] with t ht
    rw [ht]

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
