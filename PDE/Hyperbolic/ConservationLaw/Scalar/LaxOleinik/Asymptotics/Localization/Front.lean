/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Cost
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Exterior
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Interior
import PDE.Analysis.Convex.Real.Quadratic
import CAS.ExactTactic

/-!
# N-wave front localization

We combine the cost and primitive comparisons. The cost constant is chosen first,
then the front displacement, then the large-time threshold. Taylor control is only
used for small states and one fixed competing primitive minimizer.

`exists_nWave_front_localization` combines steps 1-5 of the proof of Evans, §3.4.5(b), Theorem 6,
at time `t = s²`: `u = 0` outside the outer fronts, as in (72)-(73), and the bound (78),
`|u - (1/d)(x/t - σ)| ≤ C/t`, between the inner fronts. The outer and inner fronts are
`x - σt = -(pdt)^{1/2} ∓ D` and `x - σt = (qdt)^{1/2} ± D` for a constant `D`, in place of the
radius `R` and the factors `1 ± ε` of (71) used by Evans. The competitor in the cost
comparisons is a minimizer `z` of the primitive, as in step 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(b), Theorem 6 and steps 1-5 of its
  proof, equations (69)-(78).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The solution vanishes outside bounded displacements of the N-wave fronts
and differs from the linear profile by `C / s²` between the inner fronts, at time `s²`.
All constants and comparisons are derived from the flux and datum. The fixed primitive
minimizer is used only after the local cost constants have been chosen. -/
theorem exists_nWave_front_localization {F g : ℝ → ℝ} (hF : ContDiff ℝ 3 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0) (hp : 0 < negativeLobeMass g)
    (hq : 0 < positiveLobeMass g) :
    ∃ S : ℝ, 0 < S ∧ ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, S ≤ s →
      (∀ x : ℝ,
        x ≤ deriv F 0 * s ^ 2 - √(negativeLobeMass g * deriv (deriv F) 0) * s - D ∨
        deriv F 0 * s ^ 2 + √(positiveLobeMass g * deriv (deriv F) 0) * s + D ≤ x →
        solution F g !₂[s ^ 2, x] = 0) ∧
      (∀ x : ℝ,
        deriv F 0 * s ^ 2 - √(negativeLobeMass g * deriv (deriv F) 0) * s + D ≤ x →
        x ≤ deriv F 0 * s ^ 2 + √(positiveLobeMass g * deriv (deriv F) 0) * s - D →
        |solution F g !₂[s ^ 2, x] -
          (x - deriv F 0 * s ^ 2) / (deriv (deriv F) 0 * s ^ 2)| ≤ C / s ^ 2) := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  let d := deriv (deriv F) 0
  let σ := deriv F 0
  let P := √(negativeLobeMass g * d)
  let Q := √(positiveLobeMass g * d)
  let L := HopfLax1D.legendreTransform F
  have hd : 0 < d := hθ.trans_le (hlower 0)
  have hP : 0 < P := Real.sqrt_pos.mpr (mul_pos hp hd)
  have hQ : 0 < Q := Real.sqrt_pos.mpr (mul_pos hq hd)
  have hpdiv : P ^ 2 / (2 * d) = negativeLobeMass g / 2 := by
    rw [show P ^ 2 = negativeLobeMass g * d from Real.sq_sqrt (by positivity)]
    cas
  have hqdiv : Q ^ 2 / (2 * d) = positiveLobeMass g / 2 := by
    rw [show Q ^ 2 = positiveLobeMass g * d from Real.sq_sqrt (by positivity)]
    cas
  obtain ⟨z, hz, hzmin, _, _⟩ := exists_lobe_minimizer hg1 (by linarith) hsupport
  let M := max P Q
  have hM : 0 < M := hP.trans_le (le_max_left _ _)
  obtain ⟨S₀, hS₀, E, hE, hcost⟩ := exists_uniform_scaled_cost_error hF hθ hlower hzero hg hg1 hM.le
  let D := R + max (d * (E + 2) / P) (d * (E + 2) / Q) + 1
  have hDR : R < D := by
    have hnonneg : 0 ≤ max (d * (E + 2) / P) (d * (E + 2) / Q) := by positivity
    dsimp [D]
    linarith
  have hD : 0 < D := hR.trans_lt hDR
  have hgap {P' : ℝ} (hP' : 0 < P') (hle : d * (E + 2) / P' ≤ D - R) : E + 2 ≤ P' * (D - R) / d :=
    (le_div_iff₀ hd).2 (by nlinarith only [(div_le_iff₀ hP').1 hle])
  have hgapP := hgap hP (by dsimp [D]; linarith [le_max_left (d * (E + 2) / P) (d * (E + 2) / Q)])
  have hgapQ := hgap hQ (by dsimp [D]; linarith [le_max_right (d * (E + 2) / P) (d * (E + 2) / Q)])
  let S := max S₀ (max (D + R) ((D + R) ^ 2 / (2 * d)))
  refine ⟨S, hS₀.trans_le (le_max_left _ _), D, hD, E + R / d, by positivity, fun s hs ↦ ?_⟩
  have hsA : S₀ ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := hS₀.trans_le hsA
  have hsDR : D + R ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hslarge : (D + R) ^ 2 / (2 * d) ≤ s := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  obtain ⟨hactual, hfixed⟩ := hcost s hsA
  constructor
  · exact solution_eq_zero_outside_nWave_strip_of_cost_error hF2 hθ hlower hzero hg hg1 hR
      hsupport hp hq hs0 hDR.le (by linarith) (by linarith) (fun x ↦ (hactual x).1)
  · let xL := σ * s ^ 2 - P * s + D
    let xR := σ * s ^ 2 + Q * s - D
    have hξL : xL - σ * s ^ 2 - z = -(P * s - (D - z)) := by dsimp [xL]; cas
    have hξR : xR - σ * s ^ 2 - z = Q * s - (D + z) := by dsimp [xR]; cas
    have haL : 0 ≤ D - z := by linarith [hz.2]
    have haR : 0 ≤ D + z := by linarith [hz.1]
    have haLM : D - z ≤ D + R := by linarith [hz.1]
    have haRM : D + z ≤ D + R := by linarith [hz.2]
    have hv {P' a : ℝ} (hP' : 0 < P') (hPM : P' ≤ M) (ha : 0 ≤ a) (haM : a ≤ D + R) :
        |P' * s - a| ≤ (M + 1) * s := by
      have h := abs_sub (P' * s) a
      rw [abs_of_pos (mul_pos hP' hs0), abs_of_nonneg ha] at h
      nlinarith only [h, hPM, hsDR, haM, hs0]
    have hvL : |xL - σ * s ^ 2 - z| ≤ (M + 1) * s := by
      rw [hξL, abs_neg]
      exact hv hP (le_max_left _ _) haL haLM
    have hvR : |xR - σ * s ^ 2 - z| ≤ (M + 1) * s := by
      rw [hξR]
      exact hv hQ (le_max_right _ _) haR haRM
    have hgL : E + 2 ≤ P * (D - z) / d := hgapP.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [hz.2]) hP.le) hd.le)
    have hgR : E + 2 ≤ Q * (D + z) / d := hgapQ.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [hz.1]) hQ.le) hd.le)
    have hqL := quadratic_inward_gap hd hs0 haL haLM hgL hslarge
    have hqR := quadratic_inward_gap hd hs0 haR haRM hgR hslarge
    rw [hpdiv] at hqL
    rw [hqdiv] at hqR
    have hcL : s ^ 2 * L ((xL - z) / s ^ 2) < negativeLobeMass g / 2 := by
      have hb := (abs_le.mp (hfixed xL z hvL)).2
      change s ^ 2 * L ((xL - z) / s ^ 2) - (xL - σ * s ^ 2 - z) ^ 2 / (2 * d * s ^ 2) ≤ E / s at hb
      rw [hξL, neg_sq] at hb
      linarith only [hb, hqL]
    have hcR : s ^ 2 * L ((xR - z) / s ^ 2) < positiveLobeMass g / 2 := by
      have hb := (abs_le.mp (hfixed xR z hvR)).2
      change s ^ 2 * L ((xR - z) / s ^ 2) - (xR - σ * s ^ 2 - z) ^ 2 / (2 * d * s ^ 2) ≤ E / s at hb
      rw [hξR] at hb
      linarith only [hb, hqR]
    exact abs_sub_linear_le_of_inner_cost_comparison hF2 hθ hlower hzero hg hg1 hR hsupport
      hs0 hzmin hcL hcR (fun x ↦ (hactual x).2)

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
