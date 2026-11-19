/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Semigroup

/-!
# Regularity and the initial trace of the Hopf–Lax evolution

For Lipschitz initial data, we prove the spatial, temporal, and spacetime
Lipschitz estimates of Lemma 2 in Evans, §3.3.2(b). We also define the
closed-time evolution obtained by inserting the initial datum at `t = 0`
and prove its quantitative continuity and right-hand initial trace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Lemma 2 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

open scoped Topology

/-- A uniform time-Lipschitz coefficient for Hopf–Lax evolution of
`K`-Lipschitz data. -/
def timeLipschitzConstant (H : ℝ → ℝ) (K : NNReal) : ℝ :=
  max |legendreTransform H 0| |max (H (K : ℝ)) (H (-(K : ℝ)))|

/-- The Hopf–Lax time-Lipschitz coefficient is nonnegative. -/
theorem timeLipschitzConstant_nonneg (H : ℝ → ℝ) (K : NNReal) :
    0 ≤ timeLipschitzConstant H K :=
  (abs_nonneg _).trans (le_max_left _ _)

/-- Evans, §3.3.2, Lemma 2 (spatial Lipschitz estimate): the Hopf–Lax profile is Lipschitz in `x`
with the same Lipschitz constant as the initial data. -/
theorem abs_sub_hopfLax_le_lipschitz_space {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t : ℝ} (ht : 0 < t) :
    ∀ x x' : ℝ, |hopfLax H φ t x - hopfLax H φ t x'| ≤ (K : ℝ) * |x - x'| := by
  have key (x x' : ℝ) : hopfLax H φ t x' - hopfLax H φ t x ≤ (K : ℝ) * |x - x'| := by
    obtain ⟨y, hy⟩ := exists_hopfLax_eq_integrand_of_lipschitz (x := x) hFin hφ ht
    have hle := hopfLax_le_integrand (y := x' - x + y)
      (hopfLaxBddBelow_of_lipschitz (x := x') hFin hφ ht)
    have hLip := hφ.dist_le_mul (x' - x + y) y
    rw [Real.dist_eq, Real.dist_eq, show x' - x + y - y = -(x - x') by ring, abs_neg] at hLip
    simp only [hopfLaxIntegrand, show (x' - (x' - x + y)) / t = (x - y) / t by ring] at hle hy
    linarith [le_abs_self (φ (x' - x + y) - φ y)]
  exact fun x x' ↦ abs_sub_le_iff.2 ⟨by simpa only [abs_sub_comm] using key x' x, key x x'⟩

/-- Evans, §3.3.2, Lemma 2 (time-to-initial bound): for `t > 0`,
`|u(t, x) - φ(x)| ≤ C t`, where `C` depends only on `H` and the Lipschitz constant of `φ`. -/
theorem abs_sub_hopfLax_le_initial_mul {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    |hopfLax H φ t x - φ x| ≤ timeLipschitzConstant H K * t := by
  have hu_le : hopfLax H φ t x ≤ φ x + t * legendreTransform H 0 := by
    simpa [hopfLaxIntegrand] using
      hopfLax_le_integrand (y := x) (hopfLaxBddBelow_of_lipschitz (x := x) hFin hφ ht)
  have hu_ge : φ x - t * max (H (K : ℝ)) (H (-(K : ℝ))) ≤ hopfLax H φ t x :=
    le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun y ↦ by
      have hL := mul_le_mul_of_nonneg_left
        (legendreTransform_lower_bound_abs hFin (K : ℝ) ((x - y) / t)) ht.le
      have habs : t * ((K : ℝ) * |(x - y) / t|) = K * |x - y| := by
        rw [abs_div, abs_of_pos ht]
        field_simp
      have hLip : |φ x - φ y| ≤ K * |x - y| := by simpa [Real.dist_eq] using hφ.dist_le_mul x y
      unfold hopfLaxIntegrand
      linarith [le_abs_self (φ x - φ y)])
  have h0 := mul_le_mul_of_nonneg_left (le_abs_self (legendreTransform H 0)) ht.le
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self (max (H (K : ℝ)) (H (-(K : ℝ))))) ht.le
  have hC0 := mul_le_mul_of_nonneg_left
    (le_max_left |legendreTransform H 0| |max (H (K : ℝ)) (H (-(K : ℝ)))|) ht.le
  have hC1 := mul_le_mul_of_nonneg_left
    (le_max_right |legendreTransform H 0| |max (H (K : ℝ)) (H (-(K : ℝ)))|) ht.le
  rw [abs_sub_le_iff, timeLipschitzConstant]
  constructor <;> linarith

/-- Evans, §3.3.2, Lemma 2 (spatial Lipschitz continuity), bundled as a `LipschitzWith` property. -/
theorem hopfLax_lipschitzWith_space_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t : ℝ} (ht : 0 < t) :
    LipschitzWith K (fun x : ℝ ↦ hopfLax H φ t x) :=
  LipschitzWith.of_dist_le_mul fun x x' ↦ by
    simpa [Real.dist_eq] using abs_sub_hopfLax_le_lipschitz_space hFin hφ ht x x'

/-- Evans, §3.3.2, Lemma 2 (time Lipschitz bound), `s ≤ t` version. -/
theorem abs_sub_hopfLax_le_lipschitz_time_of_le {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t s x : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    |hopfLax H φ t x - hopfLax H φ s x| ≤ timeLipschitzConstant H K * (t - s) := by
  have ht : 0 < t := by linarith
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hτ := sub_pos.mpr hst
  have hψ := hopfLax_lipschitzWith_space_of_lipschitz hFin hφ hs
  have hsem := hopfLax_semigroup (x := x) hFin hτ hs
    (by simpa using hopfLaxBddBelow_of_lipschitz (x := x) hFin hφ ht)
    (fun z ↦ hopfLaxBddBelow_of_lipschitz (x := z) hFin hφ hs)
    (hopfLaxBddBelow_of_lipschitz hFin hψ hτ)
  rw [sub_add_cancel] at hsem
  rw [hsem]
  exact abs_sub_hopfLax_le_initial_mul hFin hψ hτ

/-- Evans, §3.3.2, Lemma 2 (time Lipschitz bound) for `t, s > 0`. -/
theorem abs_sub_hopfLax_le_lipschitz_time {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t s x : ℝ} (ht : 0 < t) (hs : 0 < s) :
    |hopfLax H φ t x - hopfLax H φ s x| ≤ timeLipschitzConstant H K * |t - s| := by
  rcases le_total s t with hst | hts
  · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using
      abs_sub_hopfLax_le_lipschitz_time_of_le (x := x) hFin hφ hs hst
  · simpa [abs_sub_comm, abs_of_nonpos (sub_nonpos.mpr hts)] using
      abs_sub_hopfLax_le_lipschitz_time_of_le (x := x) hFin hφ ht hts

/-- Evans, §3.3.2, Lemma 2 (combined spacetime estimate): for `t, s > 0`,
`|u(t, x) - u(s, y)| ≤ Lip(φ) |x - y| + C |t - s|`. -/
theorem abs_sub_hopfLax_le_lipschitz_spacetime {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t s x y : ℝ} (ht : 0 < t) (hs : 0 < s) :
    |hopfLax H φ t x - hopfLax H φ s y| ≤
      (K : ℝ) * |x - y| + timeLipschitzConstant H K * |t - s| := by
  linarith [abs_sub_hopfLax_le_lipschitz_space hFin hφ ht x y,
    abs_sub_hopfLax_le_lipschitz_time (x := y) hFin hφ ht hs,
    abs_sub_le (hopfLax H φ t x) (hopfLax H φ t y) (hopfLax H φ s y)]

/-- Hopf–Lax on `t ≥ 0`, extended by the initial condition at `t = 0` (Evans, §3.3.2). -/
noncomputable def hopfLaxEvolution (H φ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if t = 0 then φ x else hopfLax H φ t x

/-- At time zero, the closed-time Hopf–Lax evolution is the initial datum. -/
@[simp]
theorem hopfLaxEvolution_zero (H φ : ℝ → ℝ) (x : ℝ) :
    hopfLaxEvolution H φ 0 x = φ x := by
  simp [hopfLaxEvolution]

/-- Away from time zero, the closed-time evolution is the usual Hopf–Lax infimum. -/
theorem hopfLaxEvolution_of_ne_zero (H φ : ℝ → ℝ) {t x : ℝ} (ht : t ≠ 0) :
    hopfLaxEvolution H φ t x = hopfLax H φ t x := by
  simp [hopfLaxEvolution, ht]

/-- Evans, §3.3.2, Lemma 2 (Lipschitz continuity on `ℝ × [0,∞)`), as a quantitative estimate. -/
theorem abs_sub_hopfLaxEvolution_le_lipschitz_spacetime {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t s x y : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    |hopfLaxEvolution H φ t x - hopfLaxEvolution H φ s y| ≤
      (K : ℝ) * |x - y| + timeLipschitzConstant H K * |t - s| := by
  have hxy : |φ x - φ y| ≤ K * |x - y| := by simpa [Real.dist_eq] using hφ.dist_le_mul x y
  rcases ht.eq_or_lt with rfl | ht <;> rcases hs.eq_or_lt with rfl | hs
  · simpa using hxy
  · have := abs_sub_hopfLax_le_initial_mul (x := y) hFin hφ hs
    rw [hopfLaxEvolution_zero, hopfLaxEvolution_of_ne_zero _ _ hs.ne', zero_sub, abs_neg,
      abs_of_pos hs]
    linarith [abs_sub_le (φ x) (φ y) (hopfLax H φ s y), abs_sub_comm (hopfLax H φ s y) (φ y)]
  · have := abs_sub_hopfLax_le_initial_mul (x := x) hFin hφ ht
    rw [hopfLaxEvolution_zero, hopfLaxEvolution_of_ne_zero _ _ ht.ne', sub_zero, abs_of_pos ht]
    linarith [abs_sub_le (hopfLax H φ t x) (φ x) (φ y)]
  · rw [hopfLaxEvolution_of_ne_zero _ _ ht.ne', hopfLaxEvolution_of_ne_zero _ _ hs.ne']
    exact abs_sub_hopfLax_le_lipschitz_spacetime hFin hφ ht hs

/-- Evans, §3.3.2, initial trace of the Hopf–Lax formula: for Lipschitz initial data,
`T_t φ(x) → φ(x)` as `t ↓ 0`.

This is the qualitative trace theorem obtained from the quantitative estimate
`|T_t φ(x) - φ(x)| ≤ C t`. -/
theorem tendsto_hopfLax_initial_right {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ ↦ hopfLax H φ t x) (𝓝[>] (0 : ℝ)) (𝓝 (φ x)) := by
  have hC := timeLipschitzConstant_nonneg H K
  rw [Metric.tendsto_nhdsWithin_nhds]
  refine fun ε hε ↦ ⟨ε / (timeLipschitzConstant H K + 1), by positivity, fun {t} ht hdist ↦ ?_⟩
  have ht : 0 < t := ht
  rw [Real.dist_eq, sub_zero, abs_of_pos ht, lt_div_iff₀ (by positivity)] at hdist
  rw [Real.dist_eq]
  linarith [abs_sub_hopfLax_le_initial_mul (x := x) hFin hφ ht]

/-- The zero-time patched Hopf–Lax profile is continuous from the right at the initial
time, pointwise in space. -/
theorem tendsto_hopfLaxEvolution_initial_right {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ ↦ hopfLaxEvolution H φ t x) (𝓝[>] (0 : ℝ)) (𝓝 (φ x)) := by
  refine (tendsto_hopfLax_initial_right hFin hφ x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hopfLaxEvolution_of_ne_zero H φ (ne_of_gt ht)).symm

end

end HopfLax1D
