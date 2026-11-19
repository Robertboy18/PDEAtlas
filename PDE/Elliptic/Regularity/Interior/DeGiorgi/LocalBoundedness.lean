/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallEnergy
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Iteration

/-!
# Local bounds from the De Giorgi energy iteration

A homogeneous weak solution with small upper-tail energy on a ball lies below the next level almost
everywhere on a smaller ball (`exists_small_tail_threshold_on_balls`). The proof iterates the
PDE-derived ball estimate on decreasing radii and increasing levels. The terminal tail has zero
integral because it is dominated by every energy in the convergent iteration.

This is the first De Giorgi lemma for scalar uniformly elliptic equations with measurable
coefficients, in every positive dimension. Evans states the De Giorgi-Nash theorem in §8.3.2 without
proof and refers to Gilbarg-Trudinger, Chapter 8.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.3.2, the De Giorgi-Nash theorem for the linear equation
  (17), stated without proof, p. 487.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity).
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric Filter
open scoped NNReal Sobolev ENNReal Topology

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

private theorem dyadic_energy_factor {C g δ : ℝ} (hg : 0 < g) (j : ℕ) :
    C / (g / (2 : ℝ) ^ (j + 1)) ^ 2 /
        (1 / (2 : ℝ) ^ (j + 1)) ^ (2 * δ) =
      (C / g ^ 2 * (2 : ℝ) ^ (2 + 2 * δ)) *
        ((2 : ℝ) ^ (2 + 2 * δ)) ^ j := by
  have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  rw [div_pow, Real.div_rpow zero_le_one hp.le, Real.one_rpow]
  have hprod : ((2 : ℝ) ^ (j + 1)) ^ 2 *
      ((2 : ℝ) ^ (j + 1)) ^ (2 * δ) =
        ((2 : ℝ) ^ (2 + 2 * δ)) ^ (j + 1) := by
    rw [← Real.rpow_two, ← Real.rpow_add hp, ← Real.rpow_pow_comm (by norm_num)]
  calc
    _ = C / g ^ 2 * (((2 : ℝ) ^ (j + 1)) ^ 2 *
        ((2 : ℝ) ^ (j + 1)) ^ (2 * δ)) := by
      field_simp [hg.ne']
    _ = _ := by rw [hprod, pow_succ]; ring

/-- Small upper-tail energy forces an almost-everywhere upper bound on the
smaller ball. The positive threshold is uniform in the centre, level,
coefficient matrix within the stated bounds, and weak solution.
No boundedness or continuity of that solution is assumed. -/
theorem exists_small_tail_threshold_on_balls
    {W : Set ℝ^n} (hWb : Bornology.IsBounded W)
    {q : ℝ≥0∞}
    (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(W)), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (z : ℝ^n), ball z R ⊆ W → ∀ k : ℝ,
        (∫ x in ball z R, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2) ≤ ε →
        ∀ᵐ x ∂volume.restrict (ball z r), wkpBaseCoordinateCLM u x ≤ k + 1 := by
  obtain ⟨C, hC, hball⟩ := exists_superlevel_ball_energy_le hWb hq2 hq hα hΛ
  let δ := 1 - 2 / q.toReal
  have hqr : (2 : ℝ) < q.toReal := by
    exact_mod_cast (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top
      (hq.trans_lt ENNReal.coe_lt_top).ne).mpr hq2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith [(div_lt_one (by linarith : 0 < q.toReal)).mpr hqr]
  let g := R - r
  have hg : 0 < g := sub_pos.mpr hrR
  let B := (2 : ℝ) ^ (2 + 2 * δ)
  have hB : 0 < B := by positivity
  obtain ⟨ε, hε, hiteration⟩ :=
    PDE.Elliptic.Regularity.DeGiorgi.exists_small_energy_threshold
      (mul_pos (div_pos hC (sq_pos_of_pos hg)) hB) hB hδ
  refine ⟨ε, hε, fun a haΛ ha u hu z hz k hsmall ↦ ?_⟩
  let ρ (j : ℕ) := r + g / (2 : ℝ) ^ j
  let l (j : ℕ) := k + 1 - 1 / (2 : ℝ) ^ j
  let Y (j : ℕ) := ∫ x in ball z (ρ j), max (wkpBaseCoordinateCLM u x - l j) 0 ^ 2
  have hρ0 : ρ 0 = R := by simp [ρ, g]
  have hl0 : l 0 = k := by simp [l]
  have hρr (j : ℕ) : r < ρ j := lt_add_of_pos_right r (div_pos hg (by positivity))
  have hρR (j : ℕ) : ρ j ≤ R := by
    have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hg' := div_le_self hg.le hp
    dsimp only [ρ, g] at *
    linarith
  have hρgap (j : ℕ) : ρ j - ρ (j + 1) = g / (2 : ℝ) ^ (j + 1) := by
    dsimp only [ρ]
    rw [pow_succ]
    field_simp
    ring
  have hlgap (j : ℕ) : l (j + 1) - l j = 1 / (2 : ℝ) ^ (j + 1) := by
    dsimp only [l]
    rw [pow_succ]
    field_simp
    ring
  have hρlt (j : ℕ) : ρ (j + 1) < ρ j :=
    sub_pos.mp ((hρgap j).symm ▸ div_pos hg (by positivity))
  have hllt (j : ℕ) : l j < l (j + 1) :=
    sub_pos.mp ((hlgap j).symm ▸ one_div_pos.mpr (by positivity))
  have hY (j : ℕ) : 0 ≤ Y j := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hY0 : Y 0 ≤ ε := by simpa only [Y, hρ0, hl0] using hsmall
  have hstep (j : ℕ) : Y (j + 1) ≤ (C / g ^ 2 * B) * B ^ j * Y j ^ (1 + δ) := by
    have h := hball a haΛ ha u hu z (ρ (j + 1)) (ρ j) (l j) (l (j + 1))
      (hr.trans (hρr _)) (hρlt j) ((ball_subset_ball (hρR j)).trans hz) (hllt j)
    rwa [hρgap, hlgap, show 2 - 2 / q.toReal = 1 + δ by dsimp only [δ]; ring,
      dyadic_energy_factor hg] at h
  have hlim := hiteration Y hY hY0 hstep
  let f : ℝ^n → ℝ := fun x ↦ max (wkpBaseCoordinateCLM u x - (k + 1)) 0 ^ 2
  have hmem (s t : ℝ) (hs : s ≤ R) :
      MemLp (fun x ↦ max (wkpBaseCoordinateCLM u x - t) 0) 2
        (volume.restrict (ball z s)) := by
    have := isFiniteMeasure_domainMeasure_of_isBounded hWb
    have hm := ((Lp.memLp (wkpBaseCoordinateCLM u)).sub (memLp_const t)).pos_part
    exact hm.mono_measure
      (domainMeasure_le ((ball_subset_ball hs).trans hz))
  have hfint : Integrable f (volume.restrict (ball z r)) := (hmem r (k + 1) hrR.le).integrable_sq
  have hle (j : ℕ) : (∫ x in ball z r, f x) ≤ Y j := by
    refine (integral_mono hfint (hmem r (l j) hrR.le).integrable_sq fun x ↦ ?_).trans
      (setIntegral_mono_set (hmem (ρ j) (l j) (hρR j)).integrable_sq
        (.of_forall fun _ ↦ sq_nonneg _) (.of_forall (ball_subset_ball (hρr j).le)))
    dsimp only [f, l]
    gcongr
    linarith [one_div_pos.mpr (show 0 < (2 : ℝ) ^ j by positivity)]
  have hzero : (∫ x in ball z r, f x) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hle))
      (integral_nonneg (fun _ ↦ sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _) hfint).mp hzero
  filter_upwards [hae] with x hx
  have hm := le_max_left (wkpBaseCoordinateCLM u x - (k + 1)) 0
  change max (wkpBaseCoordinateCLM u x - (k + 1)) 0 ^ 2 = 0 at hx
  nlinarith

end SobolevSpace.GraphSpace
