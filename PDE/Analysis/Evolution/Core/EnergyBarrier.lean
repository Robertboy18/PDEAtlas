/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Energy bounds from a rate estimate on a sublevel

Suppose `e' ≤ K` holds at every time where `e ≤ R`, with `K ≥ 0`, and the
affine envelope satisfies `e(a) + K(b - a) < R`. Then `e(t) ≤ e(a) + K(t - a)`
on `[a, b]`. At a first time where `e` would reach `R`, the mean value
inequality contradicts the strict margin. No bound on `e'` is assumed where
`e > R`.
-/

@[expose] public section

open Set

namespace PDE.Analysis.Evolution

/-- If `e` has derivative `g` within `[a, b]`, `g t ≤ K` whenever `e t ≤ R`, and
`e(a) + K(b - a) < R` with `K ≥ 0`, then `e(t) ≤ e(a) + K(t - a)` on `[a, b]`.
The trajectory is not assumed to stay in the sublevel `e ≤ R`. -/
theorem le_affine_of_hasDerivWithinAt_le_on_sublevel
    {e g : ℝ → ℝ} {a b K R : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (he : ∀ t ∈ Icc a b, HasDerivWithinAt e (g t) (Icc a b) t)
    (hbound : ∀ t ∈ Icc a b, e t ≤ R → g t ≤ K)
    (hmargin : e a + K * (b - a) < R) :
    ∀ t ∈ Icc a b, e t ≤ e a + K * (t - a) := by
  have hcont : ContinuousOn e (Icc a b) :=
    HasDerivWithinAt.continuousOn he
  have ha : e a < R :=
    lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg hK (sub_nonneg.mpr hab)))
      hmargin
  have hestimate {c : ℝ} (hc : c ∈ Icc a b)
      (hbelow : ∀ s ∈ Icc a c, e s ≤ R) :
      e c ≤ e a + K * (c - a) := by
    have hsub : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hc.2
    have hderiv (s : ℝ) (hs : s ∈ interior (Icc a c)) :
        HasDerivAt e (g s) s :=
      ((he s (hsub (interior_subset hs))).mono hsub).hasDerivAt
        (mem_interior_iff_mem_nhds.mp hs)
    have hmv := (convex_Icc a c).image_sub_le_mul_sub_of_deriv_le
      (hcont.mono hsub)
      (fun s hs ↦ (hderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hderiv s hs).deriv ▸
        hbound s (hsub (interior_subset hs)) (hbelow s (interior_subset hs)))
      a (left_mem_Icc.mpr hc.1) c (right_mem_Icc.mpr hc.1) hc.1
    linarith
  have hbelow : ∀ t ∈ Icc a b, e t < R := by
    intro t ht
    by_contra hnot
    have het : R ≤ e t := le_of_not_gt hnot
    have hct : ContinuousOn e (Icc a t) :=
      hcont.mono (Icc_subset_Icc_right ht.2)
    have hhit : (Icc a t ∩ e ⁻¹' {R}).Nonempty := by
      obtain ⟨s, hs, hsE⟩ := intermediate_value_Icc ht.1 hct ⟨ha.le, het⟩
      exact ⟨s, hs, by simpa using hsE⟩
    have hclosed : IsClosed (Icc a t ∩ e ⁻¹' {R}) :=
      hct.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    obtain ⟨τ, hτ, hleast⟩ :=
      (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isLeast hhit
    have hτeq : e τ = R := by simpa using hτ.2
    have hτbelow : ∀ s ∈ Icc a τ, e s ≤ R := by
      intro s hs
      by_contra hsnot
      have hsabove : R < e s := lt_of_not_ge hsnot
      obtain ⟨y, hy, hyE⟩ :=
        intermediate_value_Icc hs.1
          (hct.mono (Icc_subset_Icc_right (hs.2.trans hτ.1.2)))
          ⟨ha.le, hsabove.le⟩
      have hyhit : y ∈ Icc a t ∩ e ⁻¹' {R} :=
        ⟨⟨hy.1, hy.2.trans (hs.2.trans hτ.1.2)⟩, by simpa using hyE⟩
      have hyτ : y = τ := le_antisymm (hy.2.trans hs.2) (hleast hyhit)
      have hsτ : s = τ := le_antisymm hs.2 (hyτ ▸ hy.2)
      exact hsabove.ne' (hsτ ▸ hτeq)
    have hτbound := hestimate ⟨hτ.1.1, hτ.1.2.trans ht.2⟩ hτbelow
    have htime := mul_le_mul_of_nonneg_left
      (sub_le_sub_right (hτ.1.2.trans ht.2) a) hK
    linarith
  intro t ht
  exact hestimate ht (fun s hs ↦
    (hbelow s ⟨hs.1, hs.2.trans ht.2⟩).le)

end PDE.Analysis.Evolution
