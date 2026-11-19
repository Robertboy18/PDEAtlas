/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.RadialPowerCells

/-!
# Bounds of the mean degree of a radial weight

For a radial weight `w(x) = ∑ c_k |x|^{b_k}` with `c_k ≥ 0` the mean degree
`Γ(R) = ∑ b_k c_k R^{b_k/2} / ∑ c_k R^{b_k/2}` at `R = |x|²` (`radialDegree`) is a weighted mean of
the exponents, so it lies between the smallest and the largest (`radialMean_le`,
`le_radialMean`). Far out it approaches the top exponent `d`: if the other exponents are at most
`d - g`, then for `R ≥ R₀ ≥ 1`,
`d - Γ(R) ≤ R₀^{-g/2} ∑ (d - b_k) c_k / c_*` with `c_*` the coefficient of a top term
(`top_sub_radialDegree_le`): divide numerator and denominator by `R^{d/2}` and keep the top term in
the denominator.

## Main results

* `radialMean_le`, `le_radialMean`: the weighted mean of a statistic bounded above (below) by `c`
  is at most (at least) `c`.
* `top_sub_radialDegree_le`: if a top term has positive coefficient `c₀` and every other
  exponent is at most `d - g`, then `d - Γ(R) ≤ R₀^{-g/2} ∑ (d - b_k) c_k / c₀` for
  `R ≥ R₀ ≥ 1`.
-/

@[expose] public section

namespace CAS.Numerics

/-- The mean of a statistic bounded above by `c` is at most `c`. -/
theorem radialMean_le {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts) {f : AxialTerm → ℚ}
    {c : ℝ} (hf : ∀ t ∈ ts, (f t : ℝ) ≤ c) {R : ℝ} (hR : 0 ≤ R) (hM : 0 < radialMoment ts 1 R) :
    radialMean ts f R ≤ c := by
  unfold radialMean
  rw [div_le_iff₀ hM]
  unfold radialMoment
  rw [mul_comm, ← List.sum_map_mul_right]
  refine List.sum_le_sum fun t ht ↦ ?_
  have h0 : (0 : ℝ) ≤ t.coeff * R ^ ((t.radial : ℝ) / 2) :=
    mul_nonneg (by exact_mod_cast hts t ht) (Real.rpow_nonneg hR _)
  simp only [Pi.one_apply, Rat.cast_one, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hf t ht) h0]

/-- The mean of a statistic bounded below by `c` is at least `c`. -/
theorem le_radialMean {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts) {f : AxialTerm → ℚ}
    {c : ℝ} (hf : ∀ t ∈ ts, c ≤ (f t : ℝ)) {R : ℝ} (hR : 0 ≤ R) (hM : 0 < radialMoment ts 1 R) :
    c ≤ radialMean ts f R := by
  unfold radialMean
  rw [le_div_iff₀ hM]
  unfold radialMoment
  rw [mul_comm, ← List.sum_map_mul_right]
  refine List.sum_le_sum fun t ht ↦ ?_
  have h0 : (0 : ℝ) ≤ t.coeff * R ^ ((t.radial : ℝ) / 2) :=
    mul_nonneg (by exact_mod_cast hts t ht) (Real.rpow_nonneg hR _)
  simp only [Pi.one_apply, Rat.cast_one, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hf t ht) h0]

/-- **The approach of the mean degree to the top exponent.** If `t₀` is a top term with positive
coefficient and every other exponent is at most `d - g`, `d = t₀.radial`, then for `R ≥ R₀ ≥ 1`,
`d - Γ(R) ≤ R₀^{-g/2} ∑ (d - b_k) c_k / c₀`. -/
theorem top_sub_radialDegree_le {ts : List AxialTerm} (hts : AxialTerm.NonnegCoeff ts)
    {t₀ : AxialTerm} (ht₀ : t₀ ∈ ts) (hc₀ : 0 < t₀.coeff) (htop : ∀ t ∈ ts, t.radial ≤ t₀.radial)
    {g : ℚ} (hg : 0 ≤ g) (hgap : ∀ t ∈ ts, t.radial < t₀.radial → t.radial ≤ t₀.radial - g)
    {R₀ R : ℝ} (hR₀ : 1 ≤ R₀) (hR : R₀ ≤ R) :
    (t₀.radial : ℝ) - radialDegree ts R ≤
      R₀ ^ (-(g : ℝ) / 2) * (ts.map fun t ↦ ((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff).sum /
        t₀.coeff := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (hR₀.trans hR)
  have hR1 : 1 ≤ R := hR₀.trans hR
  have hM : 0 < radialMoment ts 1 R := radialMoment_one_pos hts ⟨t₀, ht₀, hc₀⟩ hRpos
  set d : ℝ := (t₀.radial : ℝ) with hd
  set A : ℝ := R ^ (d / 2)
  have hA : 0 < A := Real.rpow_pos_of_pos hRpos _
  set S : ℝ := (ts.map fun t ↦ ((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff).sum with hSdef
  have hS : 0 ≤ S := List.sum_nonneg fun y hy ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    have h1 : (0 : ℝ) ≤ ((t₀.radial - t.radial : ℚ) : ℝ) := by
      exact_mod_cast sub_nonneg.2 (htop t ht)
    exact mul_nonneg h1 (by exact_mod_cast hts t ht)
  -- the numerator `d M₁ - M_b`
  have hnum : d * radialMoment ts 1 R - radialMoment ts AxialTerm.radial R ≤
      A * R₀ ^ (-(g : ℝ) / 2) * S := by
    have e1 : d * radialMoment ts 1 R - radialMoment ts AxialTerm.radial R =
        (ts.map fun t ↦ d * (t.coeff * R ^ ((t.radial : ℝ) / 2)) +
          (-1) * ((t.radial : ℝ) * t.coeff * R ^ ((t.radial : ℝ) / 2))).sum := by
      rw [list_sum_map_add_mul]
      unfold radialMoment
      simp only [Pi.one_apply, Rat.cast_one, one_mul]
      ring
    rw [e1, hSdef, mul_assoc, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun t ht ↦ ?_
    have hc : (0 : ℝ) ≤ t.coeff := by exact_mod_cast hts t ht
    have e : d * (t.coeff * R ^ ((t.radial : ℝ) / 2)) +
        (-1) * ((t.radial : ℝ) * t.coeff * R ^ ((t.radial : ℝ) / 2)) =
        ((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff * R ^ ((t.radial : ℝ) / 2) := by
      push_cast; ring
    rw [e]
    rcases (htop t ht).lt_or_eq with hlt | heq
    · have hb := hgap t ht hlt
      have hsplit : R ^ ((t.radial : ℝ) / 2) = A * R ^ (((t.radial : ℝ) - d) / 2) := by
        rw [← Real.rpow_add hRpos]; congr 1; ring
      have h1 : R ^ (((t.radial : ℝ) - d) / 2) ≤ R ^ (-(g : ℝ) / 2) := by
        apply Real.rpow_le_rpow_of_exponent_le hR1
        have : (t.radial : ℝ) ≤ d - g := by rw [hd]; exact_mod_cast hb
        linarith
      have h2 : R ^ (-(g : ℝ) / 2) ≤ R₀ ^ (-(g : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos hR₀) hR
          (by have : (0 : ℝ) ≤ g := by exact_mod_cast hg
              linarith)
      have hdb : (0 : ℝ) ≤ ((t₀.radial - t.radial : ℚ) : ℝ) := by
        exact_mod_cast sub_nonneg.2 (htop t ht)
      rw [hsplit]
      have hk : 0 ≤ ((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff := mul_nonneg hdb hc
      calc ((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff * (A * R ^ (((t.radial : ℝ) - d) / 2))
          = (((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff) * A *
              R ^ (((t.radial : ℝ) - d) / 2) := by ring
        _ ≤ (((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff) * A * R₀ ^ (-(g : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hk hA.le)
        _ = A * (R₀ ^ (-(g : ℝ) / 2) * (((t₀.radial - t.radial : ℚ) : ℝ) * t.coeff)) := by ring
    · have : ((t₀.radial - t.radial : ℚ) : ℝ) = 0 := by rw [heq]; simp
      rw [this]
      simp
  -- the denominator `M₁ ≥ c₀ R^{d/2}`
  have hden : (t₀.coeff : ℝ) * A ≤ radialMoment ts 1 R := by
    unfold radialMoment
    have hnn : ∀ y ∈ ts.map fun t ↦ ((1 : AxialTerm → ℚ) t : ℝ) * t.coeff *
        R ^ ((t.radial : ℝ) / 2), 0 ≤ y := fun y hy ↦ by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
      simp only [Pi.one_apply, Rat.cast_one, one_mul]
      exact mul_nonneg (by exact_mod_cast hts s hs) (Real.rpow_nonneg hRpos.le _)
    have h := List.single_le_sum hnn _ (List.mem_map_of_mem ht₀)
    simpa [A] using h
  have hc₀' : (0 : ℝ) < t₀.coeff := by exact_mod_cast hc₀
  have hB : 0 ≤ R₀ ^ (-(g : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  rw [radialDegree, radialMean, sub_div' hM.ne', div_le_div_iff₀ hM hc₀']
  calc (d * radialMoment ts 1 R - radialMoment ts AxialTerm.radial R) * t₀.coeff
      ≤ (A * R₀ ^ (-(g : ℝ) / 2) * S) * t₀.coeff :=
        mul_le_mul_of_nonneg_right hnum hc₀'.le
    _ = R₀ ^ (-(g : ℝ) / 2) * S * ((t₀.coeff : ℝ) * A) := by ring
    _ ≤ R₀ ^ (-(g : ℝ) / 2) * S * radialMoment ts 1 R :=
        mul_le_mul_of_nonneg_left hden (mul_nonneg hB hS)

end CAS.Numerics
