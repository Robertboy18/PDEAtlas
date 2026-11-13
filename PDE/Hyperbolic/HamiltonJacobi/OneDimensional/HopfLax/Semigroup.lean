/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Order

/-!
# Dynamic programming for the one-dimensional Hopf–Lax operator

We prove the one-step dynamic-programming inequality and the
positive-time semigroup identity, the functional identity (22) of Lemma 1 in Evans, §3.3.2(b).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Lemma 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

/-!
## One-step inequality (dynamic programming, ≤ direction)

This is the part of the semigroup property used in viscosity-subsolution proofs:
for any intermediate spatial point `z`,

`T_{t+s} φ (x) ≤ T_s φ (z) + t * L((x-z)/t)`.
-/

/-- A two-step Hopf–Lax value is bounded by the cost through any intermediate point. -/
theorem hopfLax_le_step {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {t s x z : ℝ} (ht : 0 < t)
    (hs : 0 < s) (hbb_ts : HopfLaxBddBelow H φ (t + s) x)
    (hbb_s : ∀ w : ℝ, HopfLaxBddBelow H φ s w) :
    hopfLax H φ (t + s) x ≤ hopfLax H φ s z + t * legendreTransform H ((x - z) / t) := by
  rw [← hopfLax_add_const (hbb_s z)]
  refine le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun y ↦
    (hopfLax_le_integrand (y := y) hbb_ts).trans ?_)
  have hL := legendreTransform_time_split_le hFin ht hs x y z
  simp only [hopfLaxIntegrand]
  linarith

/-- Positive-time Hopf–Lax evolution satisfies the dynamic-programming semigroup identity. -/
theorem hopfLax_semigroup {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {t s x : ℝ} (ht : 0 < t)
    (hs : 0 < s) (hbb_ts : HopfLaxBddBelow H φ (t + s) x) (hbb_s : ∀ z : ℝ, HopfLaxBddBelow H φ s z)
    (hbb_t : HopfLaxBddBelow H (fun z ↦ hopfLax H φ s z) t x) :
    hopfLax H φ (t + s) x = hopfLax H (fun z ↦ hopfLax H φ s z) t x := by
  have hts := add_pos ht hs
  refine le_antisymm (le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun z ↦
    hopfLax_le_step hFin ht hs hbb_ts hbb_s)) (le_csInf (Set.range_nonempty _)
      (Set.forall_mem_range.2 fun y ↦ ?_))
  have hz0y : (s / (t + s) * x + t / (t + s) * y - y) / s = (x - y) / (t + s) := by
    field_simp [hs.ne', hts.ne']
    ring
  have hxz0 : (x - (s / (t + s) * x + t / (t + s) * y)) / t = (x - y) / (t + s) := by
    field_simp [ht.ne', hts.ne']
    ring
  have h0 := hopfLax_le_integrand (y := s / (t + s) * x + t / (t + s) * y) hbb_t
  have h1 := hopfLax_le_integrand (y := y) (hbb_s (s / (t + s) * x + t / (t + s) * y))
  simp only [hopfLaxIntegrand, hz0y, hxz0] at h0 h1 ⊢
  linarith

end

end HopfLax1D
