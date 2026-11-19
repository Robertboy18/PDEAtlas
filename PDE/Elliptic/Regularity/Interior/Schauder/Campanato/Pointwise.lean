/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Averages

/-!
# Mean oscillation at Lebesgue points

Power decay of integral mean oscillation controls a Lebesgue point's difference
from a ball average. The proof sums the differences along concentric dyadic
balls. Comparing two balls to a common containing ball then gives the Hölder
bound between Lebesgue points.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology

namespace PDE.Elliptic.Regularity.Campanato

variable {n : ℕ} {f : ℝ^n → ℝ}

/-- At a point where ball averages recover the function, a power bound on mean
oscillation controls its difference from each ball average. The geometric
series converges for every positive exponent. -/
theorem norm_sub_average_le
    (hf : LocallyIntegrable f volume) {x : ℝ^n} {R M γ : ℝ}
    (hγ : 0 < γ)
    (hcamp : ∀ r, 0 < r → r ≤ R →
      (⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w‖) ≤ M * r ^ γ)
    (hlim : Tendsto (fun r ↦ ⨍ z in closedBall x r, f z) (𝓝[>] 0) (𝓝 (f x)))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ‖f x - ⨍ z in closedBall x r, f z‖ ≤
      (2 : ℝ) ^ n * M * r ^ γ / (1 - (1 / 2 : ℝ) ^ γ) := by
  let δ (j : ℕ) : ℝ := r * (1 / 2) ^ j
  let v (j : ℕ) : ℝ := ⨍ z in closedBall x (δ j), f z
  have hδpos (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδle (j : ℕ) : δ j ≤ R :=
    (mul_le_of_le_one_right hr.le
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))).trans hrR
  have hδsucc (j : ℕ) : 2 * δ (j + 1) = δ j := by
    dsimp [δ]
    rw [pow_succ]
    ring
  have hstep (j : ℕ) :
      dist (v j) (v (j + 1)) ≤
        ((2 : ℝ) ^ n * M * r ^ γ) * ((1 / 2 : ℝ) ^ γ) ^ j := by
    have hsub : closedBall x (δ (j + 1)) ⊆ closedBall x (2 * δ (j + 1)) :=
      closedBall_subset_closedBall (by linarith [hδpos (j + 1)])
    have h := norm_average_sub_le_double (hδpos (j + 1)) hsub
      (hf.integrableOn_isCompact (isCompact_closedBall _ _)) (v j)
    rw [hδsucc] at h
    have hmean := hcamp (δ j) (hδpos j) (hδle j)
    calc
      _ = ‖v (j + 1) - v j‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ (2 : ℝ) ^ n * ⨍ z in closedBall x (δ j), ‖f z - v j‖ := h
      _ ≤ (2 : ℝ) ^ n * (M * (δ j) ^ γ) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = _ := by
        dsimp [δ]
        rw [Real.mul_rpow hr.le (by positivity), ← Real.rpow_pow_comm (by norm_num)]
        ring
  have hδlim : Tendsto δ atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall hδpos⟩
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul r
  have h := dist_le_of_le_geometric_of_tendsto₀ ((1 / 2 : ℝ) ^ γ)
    ((2 : ℝ) ^ n * M * r ^ γ)
    (Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hγ)
    hstep (hlim.comp hδlim)
  simpa only [v, δ, pow_zero, mul_one, dist_eq_norm, norm_sub_rev] using h

/-- Power mean-oscillation bounds near two Lebesgue points imply their
pointwise Hölder estimate. Only balls of radius at most twice their distance
are used. The two coefficient terms come from the geometric series and
comparison with a common containing ball. -/
theorem dist_le_of_meanOscillation
    (hf : LocallyIntegrable f volume) {x y : ℝ^n} {R M γ : ℝ}
    (hγ : 0 < γ) (hxy : 2 * dist x y ≤ R)
    (hx : ∀ r, 0 < r → r ≤ R →
      (⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w‖) ≤ M * r ^ γ)
    (hy : ∀ r, 0 < r → r ≤ R →
      (⨍ z in closedBall y r, ‖f z - ⨍ w in closedBall y r, f w‖) ≤ M * r ^ γ)
    (hlx : Tendsto (fun r ↦ ⨍ z in closedBall x r, f z) (𝓝[>] 0) (𝓝 (f x)))
    (hly : Tendsto (fun r ↦ ⨍ z in closedBall y r, f z) (𝓝[>] 0) (𝓝 (f y))) :
    dist (f x) (f y) ≤
      (2 * (2 : ℝ) ^ n / (1 - (1 / 2 : ℝ) ^ γ) + 2 * (2 : ℝ) ^ n * 2 ^ γ) *
        M * dist x y ^ γ := by
  rcases eq_or_ne x y with rfl | hne
  · simp [Real.zero_rpow hγ.ne']
  have hd : 0 < dist x y := dist_pos.mpr hne
  have hdR : dist x y ≤ R := by linarith
  let ax := ⨍ z in closedBall x (dist x y), f z
  let ay := ⨍ z in closedBall y (dist x y), f z
  let c := ⨍ z in closedBall x (2 * dist x y), f z
  have hex := norm_sub_average_le hf hγ hx hlx hd hdR
  have hey := norm_sub_average_le hf hγ hy hly hd hdR
  have hax := norm_average_sub_le_double hd
    (closedBall_subset_closedBall (by linarith : dist x y ≤ 2 * dist x y))
    (hf.integrableOn_isCompact (isCompact_closedBall x _)) c
  have hsub : closedBall y (dist x y) ⊆ closedBall x (2 * dist x y) := by
    intro z hz
    exact (dist_triangle z y x).trans
      (by rw [dist_comm y x]; linarith [mem_closedBall.mp hz])
  have hay := norm_average_sub_le_double hd hsub
    (hf.integrableOn_isCompact (isCompact_closedBall x _)) c
  have hm := mul_le_mul_of_nonneg_left (hx (2 * dist x y) (by positivity) hxy)
    (by positivity : 0 ≤ (2 : ℝ) ^ n)
  have hmiddle : dist ax ay ≤ 2 * (2 : ℝ) ^ n * M * (2 * dist x y) ^ γ := by
    have ht := dist_triangle ax c ay
    rw [dist_eq_norm ax c, dist_eq_norm c ay, norm_sub_rev c ay] at ht
    dsimp [ax, ay, c] at *
    linarith
  have htri := dist_triangle4 (f x) ax ay (f y)
  rw [dist_eq_norm (f x) ax, dist_eq_norm ay (f y), norm_sub_rev ay (f y)] at htri
  have hbound : dist (f x) (f y) ≤
      2 * ((2 : ℝ) ^ n * M * dist x y ^ γ / (1 - (1 / 2 : ℝ) ^ γ)) +
        2 * (2 : ℝ) ^ n * M * (2 * dist x y) ^ γ := by
    dsimp [ax, ay] at htri hmiddle
    simp only [Real.norm_eq_abs] at hex hey
    linarith
  refine hbound.trans_eq ?_
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le]
  ring

end PDE.Elliptic.Regularity.Campanato
