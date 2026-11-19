/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.L1.Integrability
import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Front
import CAS.ExactTactic

/-!
# N-wave error at large times

A central interval and two strips dominate the error. Their computed
measures turn the localization and pointwise bounds into the global L¹ estimate.

This is step 5 of the proof of Evans, §3.4.5(b), Theorem 6, at time `t = s²`: the bound (78) on
the central interval, the bounds `|u| = O(t^{-1/2})` of Theorem 5 and `|N| = O(t^{-1/2})` on two
strips of bounded width, and the vanishing (72)-(73) outside them give the estimate (67) for
large `t`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(a), Theorem 5, equation (57); §3.4.5(b),
  equation (63), Theorem 6 and step 5 of its proof, equations (67), (72)-(73) and (78).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- For sufficiently large squared times the `L¹` error is at most `C / s`.
An interior interval of length `O(s)` has error `O(s⁻²)`; two strips of bounded width
have error `O(s⁻¹)`. The derived exterior vanishing makes these estimates global. -/
theorem exists_integral_abs_sub_nWave_le_of_sq_time_ge {F g : ℝ → ℝ} (hF : ContDiff ℝ 3 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0) (hp : 0 < negativeLobeMass g)
    (hq : 0 < positiveLobeMass g) :
    ∃ S : ℝ, 0 < S ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, S ≤ s → (∫ x, |solution F g !₂[s ^ 2, x] - nWave F g (s ^ 2) x|) ≤ C / s := by
  obtain ⟨S, hS, D, hD, C, hC, hfront⟩ :=
    exists_nWave_front_localization hF hθ hlower hzero hg hg1 hR hsupport hp hq
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  let d := deriv (deriv F) 0
  let σ := deriv F 0
  let P := √(negativeLobeMass g * d)
  let Q := √(positiveLobeMass g * d)
  let A := √(2 * (∫ y, |g y|) / θ)
  let B := (P + Q) / d
  have hd : 0 < d := hθ.trans_le (hlower 0)
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by positivity
  refine ⟨max S 1, hS.trans_le (le_max_left _ _),
    C * (P + Q + 2 * D) + 4 * D * (A + B), by positivity, fun s hs ↦ ?_⟩
  have hsS : S ≤ s := (le_max_left _ _).trans hs
  have hs1 : 1 ≤ s := (le_max_right _ _).trans hs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  obtain ⟨hzeroOuter, hinner⟩ := hfront s hsS
  let a := σ * s ^ 2 - P * s - D
  let b := σ * s ^ 2 + Q * s + D
  let c := σ * s ^ 2 - P * s + D
  let e := σ * s ^ 2 + Q * s - D
  let J := (Icc a b).indicator (fun _ : ℝ ↦ C / s ^ 2)
  let Jₗ := (Icc a c).indicator (fun _ : ℝ ↦ (A + B) / s)
  let Jᵣ := (Icc e b).indicator (fun _ : ℝ ↦ (A + B) / s)
  -- integrals of the three constant indicators
  have hi (u v k : ℝ) : Integrable ((Icc u v).indicator fun _ : ℝ ↦ k) volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hint (u v k : ℝ) (huv : u ≤ v) :
      ∫ x, (Icc u v).indicator (fun _ : ℝ ↦ k) x = (v - u) * k := by
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Real.volume_real_Icc_of_le huv]
  have hiJ : Integrable J volume := hi _ _ _
  have hiL : Integrable Jₗ volume := hi _ _ _
  have hiR : Integrable Jᵣ volume := hi _ _ _
  have hnJ : ∀ x : ℝ, 0 ≤ J x := indicator_nonneg fun _ _ ↦ by positivity
  have hnL : ∀ x : ℝ, 0 ≤ Jₗ x := indicator_nonneg fun _ _ ↦ by positivity
  have hnR : ∀ x : ℝ, 0 ≤ Jᵣ x := indicator_nonneg fun _ _ ↦ by positivity
  have hheight (x : ℝ) : |solution F g !₂[s ^ 2, x] - nWave F g (s ^ 2) x| ≤ (A + B) / s := by
    have hu : |solution F g !₂[s ^ 2, x]| ≤ A / s := by
      simpa only [Real.sqrt_sq hs0.le] using
        abs_solution_le_sqrt_div_sqrt hF2 hθ hlower hzero hg hg1 (sq_pos_of_pos hs0) x
    have hN : |nWave F g (s ^ 2) x| ≤ B / s :=
      (abs_nWave_sq_le hp.le hq.le hd hs0 x).trans_eq (by dsimp [B]; cas)
    exact (abs_sub _ _).trans ((add_le_add hu hN).trans_eq (by cas))
  have hdom (x : ℝ) : |solution F g !₂[s ^ 2, x] - nWave F g (s ^ 2) x| ≤
      J x + Jₗ x + Jᵣ x := by
    by_cases hx : x ∈ Icc a b
    · by_cases hxL : x ∈ Icc a c
      · linarith [hheight x, hnJ x, hnR x, show Jₗ x = (A + B) / s from indicator_of_mem hxL _]
      by_cases hxR : x ∈ Icc e b
      · linarith [hheight x, hnJ x, hnL x, show Jᵣ x = (A + B) / s from indicator_of_mem hxR _]
      have hxc : c < x := by by_contra h; exact hxL ⟨hx.1, le_of_not_gt h⟩
      have hxe : x < e := by by_contra h; exact hxR ⟨le_of_not_gt h, hx.2⟩
      have hprof : nWave F g (s ^ 2) x = (x - σ * s ^ 2) / (d * s ^ 2) := by
        rw [nWave_sq_eq hp.le hq.le hd hs0]
        apply indicator_of_mem
        dsimp only [c, e] at hxc hxe
        constructor <;> linarith
      rw [hprof, show J x = C / s ^ 2 from indicator_of_mem hx _]
      linarith [hnL x, hnR x, hinner x hxc.le hxe.le]
    · have hN : nWave F g (s ^ 2) x = 0 := by
        rw [nWave_sq_eq hp.le hq.le hd hs0]
        exact indicator_of_notMem (fun hn ↦ hx ⟨by linarith [hn.1], by linarith [hn.2]⟩) _
      rw [hzeroOuter x (by by_contra! h; exact hx ⟨h.1.le, h.2.le⟩), hN, sub_self, abs_zero]
      linarith [hnJ x, hnL x, hnR x]
  have hmain := integral_mono
    (integrable_abs_solution_sub_nWave_of_ae_support_Icc hF2 hθ hlower hzero hg hsupport
      (sq_pos_of_pos hs0)) ((hiJ.add hiL).add hiR) hdom
  have hab : a ≤ b := by dsimp [a, b]; nlinarith
  have hac : a ≤ c := by dsimp [a, c]; linarith
  have heb : e ≤ b := by dsimp [e, b]; linarith
  simp only [Pi.add_apply] at hmain
  rw [integral_add (f := fun x ↦ J x + Jₗ x) (hiJ.add hiL) hiR, integral_add hiJ hiL,
    hint _ _ _ hab, hint _ _ _ hac, hint _ _ _ heb] at hmain
  refine hmain.trans ?_
  have hdiv : 2 * D * C / s ^ 2 ≤ 2 * D * C / s :=
    div_le_div_of_nonneg_left (by positivity) hs0 (by nlinarith)
  calc _ = C * (P + Q) / s + 2 * D * C / s ^ 2 + 4 * D * (A + B) / s := by
        simp only [a, b, c, e]
        cas
    _ ≤ C * (P + Q) / s + 2 * D * C / s + 4 * D * (A + B) / s := by gcongr
    _ = (C * (P + Q + 2 * D) + 4 * D * (A + B)) / s := by cas

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
