/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Regularity
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Order
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Semigroup

/-!
# Comparison for the one-dimensional Hopf–Lax operator

The Hopf–Lax operator preserves pointwise order and commutes with addition
of constants. Combining those two properties shows that the evolution is
nonexpansive in the uniform distance: a pointwise distance bound on two
initial data is inherited at every point where the first Hopf–Lax infimum is
bounded below.

## Main results

* `hopfLax_mono_phi_of_lipschitz`, `dist_hopfLax_le_of_lipschitz`: for
  Lipschitz data the Hopf–Lax operator is order preserving and nonexpansive
  in the uniform distance; `hopfLaxEvolution_mono_phi_of_lipschitz` and
  `dist_hopfLaxEvolution_le_of_lipschitz` are the versions for the
  zero-time-patched evolution.
* `hopfLaxEvolution_const`, `hopfLaxEvolution_mem_Icc`: when `L ≥ 0` and
  `L(0) = 0`, constants are preserved, and for Lipschitz data two-sided
  bounds on the datum are inherited by the evolution.
* `hopfLaxEvolution_semigroup_of_lipschitz`,
  `hopfLaxEvolution_dynamic_programming_of_lipschitz`: the semigroup property
  `S(t + s) = S(t) S(s)` for `t, s ≥ 0`, and its dynamic-programming form at
  an intermediate time.
* `hopfLaxEvolution_le_hopfLaxEvolution_of_le_at_time`,
  `dist_hopfLaxEvolution_le_of_dist_at_time`: comparison and distance bounds
  available at an intermediate time propagate to later times.

The Hopf–Lax formula is (21) of Evans, §3.3.2(b), and the semigroup property is the functional
identity (22) of Lemma 1 there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4 and Lemma 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

/-- Spatial translation of the initial datum translates the closed-time
Hopf–Lax profile by the same amount. -/
theorem hopfLaxEvolution_comp_add_left (H φ : ℝ → ℝ) (a t x : ℝ) :
    hopfLaxEvolution H (fun y ↦ φ (a + y)) t x = hopfLaxEvolution H φ t (a + x) := by
  by_cases ht : t = 0
  · simp only [ht, hopfLaxEvolution_zero]
  · simpa only [hopfLaxEvolution, ite_eq_right ht] using hopfLax_comp_add_left H φ a t x

/-- Positive-time Hopf–Lax evolution preserves pointwise order when the
smaller initial datum is Lipschitz and the Legendre transform is finite. -/
theorem hopfLax_mono_phi_of_lipschitz {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) (hφψ : ∀ y, φ y ≤ ψ y) :
    hopfLax H φ t x ≤ hopfLax H ψ t x :=
  hopfLax_mono_phi (hopfLaxBddBelow_of_lipschitz hFin hφ ht) hφψ

/-- A pointwise distance bound between initial data is preserved by the
Hopf–Lax operator. -/
theorem dist_hopfLax_le_of_dist_le {H φ ψ : ℝ → ℝ} {t x C : ℝ} (hbb : HopfLaxBddBelow H φ t x)
    (hφψ : ∀ y, dist (φ y) (ψ y) ≤ C) :
    dist (hopfLax H φ t x) (hopfLax H ψ t x) ≤ C := by
  have hy (y : ℝ) := abs_le.mp (by simpa only [Real.dist_eq] using hφψ y : |φ y - ψ y| ≤ C)
  have hle (y : ℝ) : φ y ≤ ψ y + C := by linarith [hy y]
  have hge (y : ℝ) : ψ y ≤ φ y + C := by linarith [hy y]
  have hforward := hopfLax_le_of_phi_le_add_const hbb hle
  have hbackward := hopfLax_le_of_phi_le_add_const (hopfLax_bddBelow_of_le_add_const hbb hle) hge
  rw [Real.dist_eq]
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- For a Legendre-finite Hamiltonian and Lipschitz initial data, the
Hopf–Lax evolution preserves every pointwise uniform-distance bound at
positive times. -/
theorem dist_hopfLax_le_of_lipschitz {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {t x C : ℝ} (ht : 0 < t) (hφψ : ∀ y, dist (φ y) (ψ y) ≤ C) :
    dist (hopfLax H φ t x) (hopfLax H ψ t x) ≤ C :=
  dist_hopfLax_le_of_dist_le (hopfLaxBddBelow_of_lipschitz hFin hφ ht) hφψ

/-- The zero-time-patched Hopf–Lax evolution preserves pointwise order on
the closed time half-line. -/
theorem hopfLaxEvolution_mono_phi_of_lipschitz {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 ≤ t) (hφψ : ∀ y, φ y ≤ ψ y) :
    hopfLaxEvolution H φ t x ≤ hopfLaxEvolution H ψ t x := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [hopfLaxEvolution_zero] using hφψ x
  · simpa only [hopfLaxEvolution, ite_eq_right ht.ne'] using
      hopfLax_mono_phi_of_lipschitz hFin hφ ht hφψ

/-- The zero-time-patched Hopf–Lax evolution is nonexpansive in every
pointwise uniform-distance bound on the closed time half-line. -/
theorem dist_hopfLaxEvolution_le_of_lipschitz {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {t x C : ℝ} (ht : 0 ≤ t) (hφψ : ∀ y, dist (φ y) (ψ y) ≤ C) :
    dist (hopfLaxEvolution H φ t x) (hopfLaxEvolution H ψ t x) ≤ C := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [hopfLaxEvolution_zero] using hφψ x
  · simpa only [hopfLaxEvolution, ite_eq_right ht.ne'] using
      dist_hopfLax_le_of_lipschitz hFin hφ ht hφψ

/-- If the Lagrangian is nonnegative and vanishes at zero, positive-time
Hopf–Lax evolution fixes constant initial data. -/
theorem hopfLax_const {H : ℝ → ℝ} (hLnonneg : ∀ q, 0 ≤ legendreTransform H q)
    (hLzero : legendreTransform H 0 = 0) {c t x : ℝ} (ht : 0 < t) :
    hopfLax H (fun _ ↦ c) t x = c := by
  have hle (y : ℝ) : c ≤ hopfLaxIntegrand H (fun _ ↦ c) t x y :=
    le_add_of_nonneg_right (mul_nonneg ht.le (hLnonneg _))
  refine le_antisymm ?_ (le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 hle))
  simpa only [hopfLaxIntegrand, sub_self, zero_div, hLzero, mul_zero, add_zero] using
    hopfLax_le_integrand (y := x) ⟨c, Set.forall_mem_range.2 hle⟩

/-- Under the same normalization, the zero-time-patched Hopf–Lax evolution
fixes constants on the closed time half-line. -/
theorem hopfLaxEvolution_const {H : ℝ → ℝ} (hLnonneg : ∀ q, 0 ≤ legendreTransform H q)
    (hLzero : legendreTransform H 0 = 0) {c t x : ℝ} (ht : 0 ≤ t) :
    hopfLaxEvolution H (fun _ ↦ c) t x = c := by
  rcases ht.eq_or_lt with rfl | ht
  · exact hopfLaxEvolution_zero _ _ x
  · simpa only [hopfLaxEvolution, ite_eq_right ht.ne'] using
      hopfLax_const hLnonneg hLzero (c := c) (x := x) ht

/-- A constant lower barrier for the initial datum remains a lower barrier
for the closed-time Hopf–Lax evolution. -/
theorem const_le_hopfLaxEvolution_of_const_le {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hLnonneg : ∀ q, 0 ≤ legendreTransform H q) (hLzero : legendreTransform H 0 = 0) {lower t x : ℝ}
    (ht : 0 ≤ t) (hlower : ∀ y, lower ≤ φ y) :
    lower ≤ hopfLaxEvolution H φ t x := by
  rw [← hopfLaxEvolution_const hLnonneg hLzero (c := lower) (x := x) ht]
  exact hopfLaxEvolution_mono_phi_of_lipschitz hFin (LipschitzWith.const lower) ht hlower

/-- A constant upper barrier for Lipschitz initial data remains an upper
barrier for the closed-time Hopf–Lax evolution. -/
theorem hopfLaxEvolution_le_const_of_le_const {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hLnonneg : ∀ q, 0 ≤ legendreTransform H q) (hLzero : legendreTransform H 0 = 0) {K : NNReal}
    (hφ : LipschitzWith K φ) {upper t x : ℝ} (ht : 0 ≤ t) (hupper : ∀ y, φ y ≤ upper) :
    hopfLaxEvolution H φ t x ≤ upper := by
  rw [← hopfLaxEvolution_const hLnonneg hLzero (c := upper) (x := x) ht]
  exact hopfLaxEvolution_mono_phi_of_lipschitz hFin hφ ht hupper

/-- Closed-time Hopf–Lax evolution preserves every closed interval
containing the range of the initial datum. -/
theorem hopfLaxEvolution_mem_Icc {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hLnonneg : ∀ q, 0 ≤ legendreTransform H q) (hLzero : legendreTransform H 0 = 0) {K : NNReal}
    (hφ : LipschitzWith K φ) {lower upper t x : ℝ} (ht : 0 ≤ t)
    (hrange : ∀ y, φ y ∈ Set.Icc lower upper) :
    hopfLaxEvolution H φ t x ∈ Set.Icc lower upper :=
  ⟨const_le_hopfLaxEvolution_of_const_le hFin hLnonneg hLzero ht fun y ↦ (hrange y).1,
    hopfLaxEvolution_le_const_of_le_const hFin hLnonneg hLzero hφ ht fun y ↦ (hrange y).2⟩

/-- The closed-time Hopf–Lax evolution does not increase a pointwise
uniform bound on Lipschitz initial data. -/
theorem abs_hopfLaxEvolution_le {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hLnonneg : ∀ q, 0 ≤ legendreTransform H q) (hLzero : legendreTransform H 0 = 0) {K : NNReal}
    (hφ : LipschitzWith K φ) {C t x : ℝ} (ht : 0 ≤ t) (hbound : ∀ y, |φ y| ≤ C) :
    |hopfLaxEvolution H φ t x| ≤ C := by
  have hdist := dist_hopfLaxEvolution_le_of_lipschitz (ψ := fun _ : ℝ ↦ 0) (x := x) hFin hφ ht
    fun y ↦ by simpa only [Real.dist_eq, sub_zero] using hbound y
  rwa [hopfLaxEvolution_const hLnonneg hLzero ht, Real.dist_eq, sub_zero] at hdist

/-- Bounded Lipschitz initial data remain bounded under closed-time
Hopf–Lax evolution, with at most linear growth in time.

The estimate follows from the spacetime Lipschitz bound by comparing `T_t φ(x)` with its initial
value `φ(x)`. -/
theorem abs_hopfLaxEvolution_le_add_time {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {C t x : ℝ} (ht : 0 ≤ t) (hbound : ∀ y, |φ y| ≤ C) :
    |hopfLaxEvolution H φ t x| ≤ C + timeLipschitzConstant H K * t := by
  have htime : |hopfLaxEvolution H φ t x - φ x| ≤ timeLipschitzConstant H K * t := by
    simpa only [hopfLaxEvolution_zero, sub_self, abs_zero, mul_zero, zero_add, sub_zero,
      abs_of_nonneg ht] using abs_sub_hopfLaxEvolution_le_lipschitz_spacetime
        (t := t) (s := 0) (x := x) (y := x) hFin hφ ht le_rfl
  linarith [abs_sub_abs_le_abs_sub (hopfLaxEvolution H φ t x) (φ x), hbound x]

/-- If the Lagrangian vanishes at zero, the zero-displacement competitor
shows that closed-time Hopf–Lax evolution lies below its initial datum. -/
theorem hopfLaxEvolution_le_self_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hLzero : legendreTransform H 0 = 0) {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ}
    (ht : 0 ≤ t) :
    hopfLaxEvolution H φ t x ≤ φ x := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [hopfLaxEvolution_zero]
  · simpa only [hopfLaxEvolution, ite_eq_right ht.ne', hLzero, mul_zero, add_zero] using
      hopfLax_le_self (hopfLaxBddBelow_of_lipschitz hFin hφ (x := x) ht)

/-- On the closed time half-line, Hopf–Lax evolution commutes with adding a
constant to Lipschitz initial data. -/
theorem hopfLaxEvolution_add_const_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {c t x : ℝ} (ht : 0 ≤ t) :
    hopfLaxEvolution H (fun y ↦ φ y + c) t x = hopfLaxEvolution H φ t x + c := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [hopfLaxEvolution_zero]
  · simpa only [hopfLaxEvolution, ite_eq_right ht.ne'] using
      hopfLax_add_const (c := c) (hopfLaxBddBelow_of_lipschitz hFin hφ (x := x) ht)

/-- Closed-time Hopf–Lax evolution preserves asymmetric pointwise bounds
on the difference of two Lipschitz initial data. Thus the semigroup is
order-contracting modulo constants, not only nonexpansive for symmetric
distance bounds. -/
theorem hopfLaxEvolution_sub_mem_Icc_of_sub_mem_Icc {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H)
    {Kφ Kψ : NNReal} (hφ : LipschitzWith Kφ φ) (hψ : LipschitzWith Kψ ψ) {lower upper t x : ℝ}
    (ht : 0 ≤ t) (hbound : ∀ y, φ y - ψ y ∈ Set.Icc lower upper) :
    hopfLaxEvolution H φ t x - hopfLaxEvolution H ψ t x ∈ Set.Icc lower upper := by
  have hlower := hopfLaxEvolution_mono_phi_of_lipschitz (ψ := fun y ↦ φ y + -lower) (x := x)
    hFin hψ ht fun y ↦ by linarith [(hbound y).1]
  have hupper := hopfLaxEvolution_mono_phi_of_lipschitz (ψ := fun y ↦ ψ y + upper) (x := x)
    hFin hφ ht fun y ↦ by linarith [(hbound y).2]
  rw [hopfLaxEvolution_add_const_of_lipschitz hFin hφ ht] at hlower
  rw [hopfLaxEvolution_add_const_of_lipschitz hFin hψ ht] at hupper
  exact ⟨by linarith, by linarith⟩

/-- The zero-time-patched Hopf–Lax profile retains the spatial Lipschitz
constant of its initial datum at every nonnegative time. -/
theorem hopfLaxEvolution_lipschitzWith_space_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith K (fun x ↦ hopfLaxEvolution H φ t x) := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [hopfLaxEvolution_zero] using hφ
  · simpa only [hopfLaxEvolution, ite_eq_right ht.ne'] using
      hopfLax_lipschitzWith_space_of_lipschitz hFin hφ ht

/-- For Lipschitz initial data, the zero-time-patched Hopf–Lax operators
form a semigroup on the closed time half-line. -/
theorem hopfLaxEvolution_semigroup_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {t s x : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    hopfLaxEvolution H φ (t + s) x = hopfLaxEvolution H (fun z ↦ hopfLaxEvolution H φ s z) t x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [zero_add, hopfLaxEvolution_zero]
  rcases hs.eq_or_lt with rfl | hs
  · simp only [add_zero, hopfLaxEvolution_zero]
  simpa only [hopfLaxEvolution, ite_eq_right (add_pos ht hs).ne', ite_eq_right ht.ne',
    ite_eq_right hs.ne'] using hopfLax_semigroup (x := x) hFin ht hs
      (hopfLaxBddBelow_of_lipschitz hFin hφ (add_pos ht hs))
      (fun z ↦ hopfLaxBddBelow_of_lipschitz hFin hφ (x := z) hs)
      (hopfLaxBddBelow_of_lipschitz hFin (hopfLax_lipschitzWith_space_of_lipschitz hFin hφ hs) ht)

/-- Dynamic programming at an intermediate time `s ∈ [0, t]`: evolve first
for time `s`, then for the remaining time `t - s`. -/
theorem hopfLaxEvolution_dynamic_programming_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {s t x : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    hopfLaxEvolution H φ t x = hopfLaxEvolution H (fun z ↦ hopfLaxEvolution H φ s z) (t - s) x := by
  simpa only [sub_add_cancel] using
    hopfLaxEvolution_semigroup_of_lipschitz hFin hφ (sub_nonneg.mpr hst) hs (x := x)

/-- A pointwise comparison available at an intermediate time propagates to
every later time. -/
theorem hopfLaxEvolution_le_hopfLaxEvolution_of_le_at_time {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H)
    {Kφ Kψ : NNReal} (hφ : LipschitzWith Kφ φ) (hψ : LipschitzWith Kψ ψ) {s t x : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (hcompare : ∀ y, hopfLaxEvolution H φ s y ≤ hopfLaxEvolution H ψ s y) :
    hopfLaxEvolution H φ t x ≤ hopfLaxEvolution H ψ t x := by
  rw [hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hφ hs hst,
    hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hψ hs hst]
  exact hopfLaxEvolution_mono_phi_of_lipschitz
    hFin (hopfLaxEvolution_lipschitzWith_space_of_lipschitz hFin hφ hs)
    (sub_nonneg.mpr hst) hcompare

/-- A pointwise uniform-distance bound available at an intermediate time
propagates unchanged to every later time. -/
theorem dist_hopfLaxEvolution_le_of_dist_at_time {H φ ψ : ℝ → ℝ} (hFin : LegendreFinite H)
    {Kφ Kψ : NNReal} (hφ : LipschitzWith Kφ φ) (hψ : LipschitzWith Kψ ψ) {s t x C : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (hbound : ∀ y, dist (hopfLaxEvolution H φ s y) (hopfLaxEvolution H ψ s y) ≤ C) :
    dist (hopfLaxEvolution H φ t x) (hopfLaxEvolution H ψ t x) ≤ C := by
  rw [hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hφ hs hst,
    hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hψ hs hst]
  exact dist_hopfLaxEvolution_le_of_lipschitz
    hFin (hopfLaxEvolution_lipschitzWith_space_of_lipschitz hFin hφ hs) (sub_nonneg.mpr hst) hbound

/-- Asymmetric pointwise bounds on the difference of two Hopf–Lax
profiles at time `s` propagate unchanged to every later time `t`. -/
theorem hopfLaxEvolution_sub_mem_Icc_of_sub_mem_Icc_at_time {H φ ψ : ℝ → ℝ}
    (hFin : LegendreFinite H) {Kφ Kψ : NNReal} (hφ : LipschitzWith Kφ φ) (hψ : LipschitzWith Kψ ψ)
    {lower upper s t x : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hbound : ∀ y, hopfLaxEvolution H φ s y - hopfLaxEvolution H ψ s y ∈ Set.Icc lower upper) :
    hopfLaxEvolution H φ t x - hopfLaxEvolution H ψ t x ∈ Set.Icc lower upper := by
  rw [hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hφ hs hst,
    hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hψ hs hst]
  exact hopfLaxEvolution_sub_mem_Icc_of_sub_mem_Icc hFin
    (hopfLaxEvolution_lipschitzWith_space_of_lipschitz hFin hφ hs)
    (hopfLaxEvolution_lipschitzWith_space_of_lipschitz hFin hψ hs) (sub_nonneg.mpr hst) hbound

/-- When the Lagrangian vanishes at zero, closed-time Hopf–Lax evolution is
nonincreasing in time. -/
theorem hopfLaxEvolution_le_hopfLaxEvolution_of_le_time {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hLzero : legendreTransform H 0 = 0) {K : NNReal} (hφ : LipschitzWith K φ) {s t x : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    hopfLaxEvolution H φ t x ≤ hopfLaxEvolution H φ s x := by
  rw [hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hφ hs hst]
  exact hopfLaxEvolution_le_self_of_lipschitz hFin hLzero
    (hopfLaxEvolution_lipschitzWith_space_of_lipschitz hFin hφ hs) (sub_nonneg.mpr hst)

/-- For each spatial point, normalized Hopf–Lax evolution is antitone on
the closed time half-line. -/
theorem antitoneOn_hopfLaxEvolution_time {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    (hLzero : legendreTransform H 0 = 0) {K : NNReal} (hφ : LipschitzWith K φ) (x : ℝ) :
    AntitoneOn (fun t ↦ hopfLaxEvolution H φ t x) (Set.Ici 0) :=
  fun _ hs _ _ hst ↦ hopfLaxEvolution_le_hopfLaxEvolution_of_le_time hFin hLzero hφ hs hst

end HopfLax1D
