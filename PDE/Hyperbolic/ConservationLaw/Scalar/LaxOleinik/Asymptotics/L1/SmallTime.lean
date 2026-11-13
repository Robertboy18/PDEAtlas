/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.L1.Integrability
import CAS.ExactTactic

/-!
# N-wave error on bounded time intervals

The propagation cone gives a common bounded interval for bounded times. Combining
its measure with the solution and profile height bounds gives the required
inverse-square-root estimate down to every strictly positive time.

Evans, §3.4.5(b), Theorem 6, asserts (67) for all `t > 0`, and step 5 of its proof concludes for
large `t`. Here `t = s²` with `s ≤ T`: the supports of `u` and `N` lie in a fixed interval, where
the decay (57) of Theorem 5 and the bound `|N| = O(t^{-1/2})` bound the integrand.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(a), Theorem 5, equation (57); §3.4.5(b),
  equation (63), Theorem 6 and step 5 of its proof, equation (67).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- On any bounded positive time interval the error is bounded by `C / s`
at time `s²`. Finite propagation and the pointwise solution and profile bounds prove this
without an assumed mass identity, contraction principle, or integrable solution slice. -/
theorem exists_integral_abs_sub_nWave_le_of_sq_time_le {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, 0 < s → s ≤ T → (∫ x, |solution F g !₂[s ^ 2, x] - nWave F g (s ^ 2) x|) ≤
        C / s := by
  have hd : 0 < deriv (deriv F) 0 := hθ.trans_le (hlower 0)
  obtain ⟨hp, hq⟩ := lobeMass_nonneg hg1 (by linarith) hsupport
  obtain ⟨c, hc, hcone⟩ := exists_solution_eq_zero_of_abs_gt hF hθ hlower hzero hg hg1 hsupport
  let A := √(2 * (∫ y, |g y|) / θ)
  let P := √(negativeLobeMass g * deriv (deriv F) 0)
  let Q := √(positiveLobeMass g * deriv (deriv F) 0)
  let B := (P + Q) / deriv (deriv F) 0
  let K := R + c * T ^ 2 + |deriv F 0| * T ^ 2 + (P + Q) * T
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by positivity
  have hK : 0 ≤ K := by positivity
  refine ⟨2 * K * (A + B), by positivity, fun s hs hsT ↦ ?_⟩
  have hs2 : s ^ 2 ≤ T ^ 2 := (sq_le_sq₀ hs.le hT.le).2 hsT
  have hu (x : ℝ) : |solution F g !₂[s ^ 2, x]| ≤ A / s := by
    simpa only [Real.sqrt_sq hs.le] using
      abs_solution_le_sqrt_div_sqrt hF hθ hlower hzero hg hg1 (sq_pos_of_pos hs) x
  have hN (x : ℝ) : |nWave F g (s ^ 2) x| ≤ B / s :=
    (abs_nWave_sq_le hp hq hd hs x).trans_eq (by dsimp [B]; cas)
  have herr (x : ℝ) : |solution F g !₂[s ^ 2, x] - nWave F g (s ^ 2) x| ≤ (A + B) / s :=
    (abs_sub _ _).trans ((add_le_add (hu x) (hN x)).trans_eq (by cas))
  have hvanish (x : ℝ) (hx : x ∉ Icc (-K) K) :
      |solution F g !₂[s ^ 2, x] - nWave F g (s ^ 2) x| = 0 := by
    have hxK : K < |x| := lt_of_not_ge fun h ↦ hx (abs_le.mp h)
    have h₁ := mul_le_mul_of_nonneg_left hs2 hc
    have h₂ := mul_le_mul_of_nonneg_left hs2 (abs_nonneg (deriv F 0))
    have h₃ := mul_le_mul_of_nonneg_left hsT (add_nonneg hP hQ)
    have h₄ := mul_nonneg hc (sq_nonneg T)
    have h₅ := mul_nonneg (abs_nonneg (deriv F 0)) (sq_nonneg T)
    have h₆ := mul_nonneg (add_nonneg hP hQ) hT.le
    simp only [K] at hxK
    rw [hcone (s ^ 2) (sq_pos_of_pos hs) x (by linarith),
      nWave_sq_eq_zero_of_abs_gt hp hq hd hs (by linarith), sub_self, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Icc (-K) K) (f := fun x ↦ |solution F g !₂[s ^ 2, x] - nWave F g (s ^ 2) x|)
    measure_Icc_lt_top (fun x _ ↦ by simpa only [Real.norm_eq_abs, abs_abs] using herr x)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _),
    Real.volume_real_Icc_of_le (by linarith : -K ≤ K)] at hb
  exact hb.trans_eq (by cas)

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
