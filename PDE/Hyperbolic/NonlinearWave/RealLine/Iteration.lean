/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Strip
import Mathlib.Topology.Algebra.Order.Floor
import CAS.ExactTactic

/-!
# Arbitrary-horizon nonlinear wave iteration

Repeated retarded integration produces a factorial denominator. Consequently some
iterate contracts on every finite strip, with no smallness restriction on the
horizon, the Lipschitz constant, or the initial data.

The map is `u ↦ u⁰ - D[f(u)]`, with `u⁰` given by d'Alembert's formula (8) of Evans, §2.4.1(a),
and `D` the Duhamel formula (43) of Example (i) in §2.4.2. On the strip `ℝ × [0, T]`,
`dist_iterate_nonlinearStripMap_le` bounds the distance of the `n`-th iterates by
`(T² L)ⁿ / n!` times the distance of the starting functions, where `L` is the Lipschitz constant
of `f`. Some iterate is therefore a contraction, and Mathlib's Banach fixed point theorem gives
the unique fixed point.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(a), equation (8); §2.4.2, Example (i),
  equation (43).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter Function
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- Bounded continuous scalar Cauchy data give a bounded free wave on every finite strip. -/
def freeStripWave (T : NNReal) (g h : ℝ →ᵇ ℝ) : ForwardStrip T →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p ↦ dAlembertFormula g h p.2 p.1.1)
    (by
      have hz : Continuous (fun p : ForwardStrip T ↦
          dAlembertFormula (fun _ ↦ 0) h p.2 p.1.1) := by
        have hc := continuous_dAlembert_zero_displacement_family
          (T := Unit) (h := fun _ ↦ h) (h.continuous.comp continuous_snd)
        simpa [Function.comp_def, stripInclusion, timeSpaceCons] using hc.comp
          ((continuous_const (y := ())).prodMk (continuous_stripInclusion T))
      have hg : Continuous (fun p : ForwardStrip T ↦
          (1 / 2 : ℝ) * (g (p.2 + p.1.1) + g (p.2 - p.1.1))) := by
        fun_prop
      convert hg.add hz using 1
      funext p
      simp [dAlembertFormula])
    (‖g‖ + T * ‖h‖) (fun p ↦ by
      have he : dAlembertFormula g h p.2 p.1.1 =
          (1 / 2 : ℝ) * (g (p.2 + p.1.1) + g (p.2 - p.1.1)) +
            dAlembertFormula (fun _ ↦ 0) h p.2 p.1.1 := by
        simp [dAlembertFormula]
      rw [he]
      apply (norm_add_le _ _).trans
      apply add_le_add
      · rw [norm_mul]
        have hb := (norm_add_le (g (p.2 + p.1.1)) (g (p.2 - p.1.1))).trans
          (add_le_add (g.norm_coe_le_norm _) (g.norm_coe_le_norm _))
        norm_num
        simp only [Real.norm_eq_abs] at hb
        linarith
      · exact (norm_dAlembert_zero_le h.norm_coe_le_norm p.1.property.1 p.2).trans
          (mul_le_mul_of_nonneg_right p.1.property.2 (norm_nonneg h)))

/-- The short-strip fixed point has the d'Alembert free field of the given data. -/
theorem existsUnique_nonlinearStrip_of_boundedContinuousData {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (hsmall : T ^ 2 / 2 * L < 1) :
    ∃! u : ForwardStrip T →ᵇ ℝ, ∀ p, u p = dAlembertFormula g h p.2 p.1.1 -
      dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q))) (stripInclusion p) := by
  exact existsUnique_nonlinearStrip_fixedPoint hf (freeStripWave T g h) hsmall

/-- A pointwise distance envelope passes through the nonlinear retarded wave.
The inner integration contributes at most the fixed strip length. -/
theorem dist_nonlinearStripMap_apply_le_integral {T L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (H u v : ForwardStrip T →ᵇ ℝ) (p : ForwardStrip T) {D : ℝ → ℝ} (hD : Continuous D)
    (hbound : ∀ q : ForwardStrip T, q.1.1 ≤ p.1.1 → dist (u q) (v q) ≤ D q.1.1) :
    dist (nonlinearStripMap hf H u p) (nonlinearStripMap hf H v p) ≤
      (T : ℝ) * ∫ s in (0 : ℝ)..p.1.1, L * D s := by
  change dist (H p - dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q)))
      (stripInclusion p)) (H p - dAlembertDuhamelSolution (fun q ↦ f (v (stripProjection T q)))
      (stripInclusion p)) ≤ _
  rw [dist_sub_left, dist_eq_norm, ← dAlembertDuhamelSolution_sub
    (f := fun q ↦ f (u (stripProjection T q))) (g := fun q ↦ f (v (stripProjection T q)))
    (hf.continuous.comp (u.continuous.comp (continuous_stripProjection T)))
    (hf.continuous.comp (v.continuous.comp (continuous_stripProjection T)))]
  have hsource : ∀ s ∈ Icc 0 (stripInclusion p 0), ∀ x : ℝ^1,
      ‖f (u (stripProjection T (timeSpaceCons s x))) -
        f (v (stripProjection T (timeSpaceCons s x)))‖ ≤ L * D s := by
    intro s hs x
    have hst : s ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs.1, hs.2.trans p.1.property.2⟩
    have hproj : stripProjection T (timeSpaceCons s x) = (⟨s, hst⟩, x 0) := by
      change (projIcc (0 : ℝ) T T.coe_nonneg s, x 0) = _
      rw [projIcc_of_mem T.coe_nonneg hst]
    simpa only [hproj, dist_eq_norm] using
      (hf.dist_le_mul (u (⟨s, hst⟩, x 0)) (v (⟨s, hst⟩, x 0))).trans
        (mul_le_mul_of_nonneg_left (hbound (⟨s, hst⟩, x 0) hs.2) L.coe_nonneg)
  have hnorm := norm_dAlembertDuhamelSolution_le_integral
    (f := fun q ↦ f (u (stripProjection T q)) - f (v (stripProjection T q)))
    (b := fun s ↦ (L : ℝ) * D s)
    (continuous_const.mul hD) (p := stripInclusion p) p.1.property.1 hsource
  apply hnorm.trans
  change (∫ s in (0 : ℝ)..p.1.1, (p.1.1 - s) * ((L : ℝ) * D s)) ≤ _
  calc
    (∫ s in (0 : ℝ)..p.1.1, (p.1.1 - s) * ((L : ℝ) * D s)) ≤
        ∫ s in (0 : ℝ)..p.1.1, (T : ℝ) * (L * D s) := by
      have hleft : Continuous (fun s : ℝ ↦ (p.1.1 - s) * ((L : ℝ) * D s)) := by
        fun_prop
      have hright : Continuous (fun s : ℝ ↦ (T : ℝ) * (L * D s)) := by fun_prop
      apply intervalIntegral.integral_mono_on p.1.property.1
        (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _)
      intro s hs
      have hst : s ∈ Icc (0 : ℝ) (T : ℝ) := ⟨hs.1, hs.2.trans p.1.property.2⟩
      have hDs : 0 ≤ D s := dist_nonneg.trans (hbound (⟨s, hst⟩, 0) hs.2)
      exact mul_le_mul_of_nonneg_right
        ((sub_le_self _ hs.1).trans p.1.property.2) (mul_nonneg L.coe_nonneg hDs)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Every retarded iteration gains a factorial denominator, pointwise in spacetime. -/
theorem dist_iterate_nonlinearStripMap_apply_le {T L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (H u v : ForwardStrip T →ᵇ ℝ) (n : ℕ) (p : ForwardStrip T) :
    dist (((nonlinearStripMap hf H)^[n]) u p) (((nonlinearStripMap hf H)^[n]) v p) ≤
      (((T : ℝ) * L * p.1.1) ^ n / n.factorial) * dist u v := by
  induction n generalizing p with
  | zero =>
      simpa using BoundedContinuousFunction.dist_coe_le_dist (f := u) (g := v) p
  | succ n hn =>
      let P := nonlinearStripMap hf H
      let D : ℝ → ℝ := fun s ↦ (((T : ℝ) * L * s) ^ n / n.factorial) * dist u v
      have hD : Continuous D := by fun_prop
      have hnorm := dist_nonlinearStripMap_apply_le_integral hf H
        ((P^[n]) u) ((P^[n]) v) p hD (fun q _ ↦ hn q)
      rw [iterate_succ_apply', iterate_succ_apply']
      apply hnorm.trans_eq
      dsimp only [D]
      simp_rw [mul_pow]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, div_eq_mul_inv, mul_inv_rev]
      cas

/-- The pointwise factorial bound gives uniform convergence on each fixed strip. -/
theorem dist_iterate_nonlinearStripMap_le {T L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (H u v : ForwardStrip T →ᵇ ℝ) (n : ℕ) :
    dist (((nonlinearStripMap hf H)^[n]) u) (((nonlinearStripMap hf H)^[n]) v) ≤
      (((T : ℝ) * L * T) ^ n / n.factorial) * dist u v := by
  apply (BoundedContinuousFunction.dist_le (by positivity)).mpr
  intro p
  apply (dist_iterate_nonlinearStripMap_apply_le hf H u v n p).trans
  have ht : 0 ≤ p.1.1 := p.1.property.1
  gcongr
  exact p.1.property.2

/-- On every finite strip, some iterate of the nonlinear wave map contracts. -/
theorem exists_contractingWith_iterate_nonlinearStripMap {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (H : ForwardStrip T →ᵇ ℝ) :
    ∃ (n : ℕ) (q : NNReal), ContractingWith q ((nonlinearStripMap hf H)^[n]) := by
  obtain ⟨n, hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop ((T : ℝ) * L * T)).eventually
      (gt_mem_nhds zero_lt_one) |>.exists
  let q : NNReal := ⟨((T : ℝ) * L * T) ^ n / n.factorial, by positivity⟩
  refine ⟨n, q, hn, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  exact dist_iterate_nonlinearStripMap_le hf H u v n

/-- Every finite time strip admits exactly one bounded continuous integral solution.
This conclusion has no small-time restriction and no condition on `f(0)`. -/
theorem existsUnique_nonlinearStrip_fixedPoint_anyTime {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (H : ForwardStrip T →ᵇ ℝ) :
    ∃! u : ForwardStrip T →ᵇ ℝ, ∀ p, u p = H p - dAlembertDuhamelSolution
      (fun q ↦ f (u (stripProjection T q))) (stripInclusion p) := by
  obtain ⟨n, q, hPn⟩ := exists_contractingWith_iterate_nonlinearStripMap hf H
  let P := nonlinearStripMap hf H
  let u := hPn.fixedPoint (P^[n])
  have hu : IsFixedPt P u := hPn.isFixedPt_fixedPoint_iterate
  refine ⟨u, ?_, ?_⟩
  · intro p
    exact (congrArg (fun w : ForwardStrip T →ᵇ ℝ ↦ w p) hu).symm
  · intro v hv
    have hvfix : IsFixedPt P v := by
      ext p
      exact (hv p).symm
    exact hPn.fixedPoint_unique (hvfix.iterate n)

/-- The arbitrary-horizon solution uses the free wave of the bounded continuous data. -/
theorem existsUnique_nonlinearStrip_of_boundedContinuousData_anyTime {T L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) :
    ∃! u : ForwardStrip T →ᵇ ℝ, ∀ p, u p = dAlembertFormula g h p.2 p.1.1 -
      dAlembertDuhamelSolution (fun q ↦ f (u (stripProjection T q))) (stripInclusion p) :=
  existsUnique_nonlinearStrip_fixedPoint_anyTime hf (freeStripWave T g h)

end WaveEquation
