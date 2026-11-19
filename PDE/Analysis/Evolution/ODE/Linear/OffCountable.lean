/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.Gronwall
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Linear ODEs with zero data and countably many exceptional times

A function continuous on `[0, T]` that vanishes at `0` and has, at every time of `(0, T)`
outside a countable set, a derivative of norm at most `K` times its norm vanishes on `[0, T]`
(`eqOn_zero_of_norm_deriv_le_off_countable`), in particular when `f' = A f`. The
fundamental theorem of calculus with countably many exceptional points gives `f(t) = ∫₀ᵗ f'`, and
the integral Grönwall inequality gives `f = 0`. The exceptional set allows functions built from
Duhamel integrals of kernels that jump at finitely many times. In particular a function continuous
on `[0, T]` with zero derivative on `(0, T)` is constant there (`eqOn_const_of_hasDerivAt_zero`).

## Main results

* `eqOn_zero_of_norm_deriv_le_off_countable`: a function continuous on `[0, T]`, zero at `0`,
  with `‖f'‖ ≤ K ‖f‖` on `(0, T)` off a countable set, vanishes on `[0, T]`.
* `eqOn_zero_of_hasDerivAt_off_countable`: uniqueness for `f' = A f` with zero data, with the
  derivative required only off a countable set of times.
* `eqOn_const_of_hasDerivAt_zero`: a function continuous on `[0, t₀]` with zero derivative on
  `(0, t₀)` is constant there.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Uniqueness with zero data for a derivative bounded by the function**, off a countable set of
times: a function continuous on `[0, T]` that vanishes at `0` and has, at every time of `(0, T)`
outside a countable set, a derivative of norm at most `K` times its norm vanishes on `[0, T]`. The
coefficient need not be continuous: the derivative is measurable and bounded off a null set, so it
is integrable, the fundamental theorem of calculus gives `f(t) = ∫₀ᵗ f'`, and the integral
Grönwall inequality gives `f = 0`. -/
theorem eqOn_zero_of_norm_deriv_le_off_countable {f : ℝ → E} {T K : ℝ} {S : Set ℝ}
    (hS : S.Countable) (hf : ContinuousOn f (Icc 0 T)) (h0 : f 0 = 0)
    (hd : ∀ t ∈ Ioo 0 T \ S, ∃ f', HasDerivAt f f' t ∧ ‖f'‖ ≤ K * ‖f t‖) :
    EqOn f 0 (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · intro t ht
    exact absurd (ht.1.trans ht.2) (not_le.2 hT)
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hd' : ∀ t ∈ Ioo 0 T \ S, HasDerivAt f (deriv f t) t ∧ ‖deriv f t‖ ≤ K' * ‖f t‖ := by
    intro t ht
    obtain ⟨f', hf', hle⟩ := hd t ht
    rw [hf'.deriv]
    exact ⟨hf', hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hnull : volume (S ∪ {0, T}) = 0 :=
    (hS.union ((countable_singleton 0).insert T |>.mono (by
      intro x hx
      rcases hx with rfl | rfl <;> simp))).measure_zero volume
  have hae : ∀ᵐ s ∂volume, s ∈ Icc 0 T → s ∈ Ioo 0 T \ S := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hsI
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hs
    exact ⟨⟨lt_of_le_of_ne hsI.1 (Ne.symm hs.2.1), lt_of_le_of_ne hsI.2 hs.2.2⟩, hs.1⟩
  have hint : ∀ t ∈ Icc 0 T, IntervalIntegrable (deriv f) volume 0 t := by
    intro t ht
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
      (Measure.integrableOn_of_bounded (M := K' * M) (by simp)
        (aestronglyMeasurable_deriv f _) ?_)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae] with s hs hsI
    have hsT : s ∈ Icc 0 T := ⟨hsI.1, hsI.2.trans ht.2⟩
    exact (hd' s (hs hsT)).2.trans (mul_le_mul_of_nonneg_left (hM s hsT) hK'0)
  have hrepr : ∀ t ∈ Icc 0 T, f t = ∫ s in (0 : ℝ)..t, deriv f s := by
    intro t ht
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have := integral_eq_of_hasDerivAt_off_countable_of_le f (deriv f) ht.1 hS (hf.mono hsub)
      (fun s hs ↦ (hd' s ⟨⟨hs.1.1, hs.1.2.trans_le ht.2⟩, hs.2⟩).1) (hint t ht)
    rw [this, h0, sub_zero]
  have hnorm : ContinuousOn (fun t ↦ ‖f t‖) (Icc 0 T) := hf.norm
  have key := eq_zero_on_of_nonneg_le_mul_intervalIntegral (e := fun t ↦ ‖f t‖) (K := K') hT
    hnorm (fun _ _ ↦ norm_nonneg _) fun t ht ↦ by
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
      rw [hrepr t ht, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ ?_
      · filter_upwards [hae] with s hs hsI
        exact (hd' s (hs ⟨hsI.1.le, hsI.2.trans ht.2⟩)).2
      · exact ((hnorm.mono hsub).intervalIntegrable_of_Icc ht.1).const_mul _
  intro t ht
  exact norm_eq_zero.1 (key t ht)

/-- **Uniqueness for `f' = A f` with zero data**, with the derivative required only off a
countable set of times. -/
theorem eqOn_zero_of_hasDerivAt_off_countable {A : E →L[ℝ] E} {f : ℝ → E} {T : ℝ} {S : Set ℝ}
    (hS : S.Countable) (hf : ContinuousOn f (Icc 0 T)) (h0 : f 0 = 0)
    (hd : ∀ t ∈ Ioo 0 T \ S, HasDerivAt f (A (f t)) t) : EqOn f 0 (Icc 0 T) :=
  eqOn_zero_of_norm_deriv_le_off_countable (K := ‖A‖) hS hf h0 fun t ht ↦
    ⟨_, hd t ht, A.le_opNorm (f t)⟩

/-- A function continuous on `[0, t₀]` with zero derivative on `(0, t₀)` is constant there. -/
theorem eqOn_const_of_hasDerivAt_zero {f : ℝ → ℝ} {t₀ : ℝ} (hf : ContinuousOn f (Icc 0 t₀))
    (hd : ∀ t ∈ Ioo 0 t₀, HasDerivAt f 0 t) : ∀ t ∈ Icc 0 t₀, f t = f 0 := by
  have h := eqOn_zero_of_hasDerivAt_off_countable
    (A := (0 : ℝ →L[ℝ] ℝ)) (f := fun t ↦ f t - f 0) (T := t₀) (S := ∅) countable_empty
    (hf.sub continuousOn_const) (by simp) fun t ht ↦ by
      simpa using (hd t ht.1).sub_const (f 0)
  intro t ht
  have := h ht
  simp only [Pi.zero_apply] at this
  linarith

end PDE.Analysis.Evolution
