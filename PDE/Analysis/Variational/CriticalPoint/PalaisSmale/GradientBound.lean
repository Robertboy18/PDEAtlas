/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CriticalPoint.PalaisSmale.Basic

/-!
# A gradient gap around a noncritical level

If arbitrarily narrow energy bands around the level `c` contain points with arbitrarily small
gradients, these points form a Palais–Smale sequence. A strong subsequential limit is a
critical point at the level `c`. Thus absence of that critical value gives a uniform positive
gradient bound, without a lower bound on the energy or compactness of Hilbert balls. This is
step 1 of the proof of the deformation theorem in Evans, §8.5.1, Theorem 1, the estimate (4),
here on the closed band `|I x - c| ≤ ε`.

## Main results

* `PalaisSmale.exists_gradient_gap`: if `I` is `C¹`, satisfies the Palais–Smale condition
  and has no critical point at the level `c`, then for some `ε > 0` and `σ ∈ (0, 1)` we have
  `σ ≤ ‖∇ I x‖` whenever `|I x - c| ≤ ε`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(a), step 1 of the proof of Theorem 1
  (Deformation Theorem), (4)-(6), p. 503. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

open Filter Function Set
open scoped Topology

namespace PDE.Analysis.Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A noncritical level has a closed energy band on which the gradient is bounded
away from zero. The constants are chosen before the points in the band. -/
theorem PalaisSmale.exists_gradient_gap {I : H → ℝ} (hPS : PalaisSmale I)
    (hI : ContDiff ℝ 1 I) {c : ℝ}
    (hc : ∀ x, I x = c → ∇ I x ≠ 0) :
    ∃ ε > 0, ∃ σ ∈ Ioo (0 : ℝ) 1,
      ∀ x, |I x - c| ≤ ε → σ ≤ ‖∇ I x‖ := by
  have hband : ∃ ε > 0, ∀ x, |I x - c| ≤ ε → ε ≤ ‖∇ I x‖ := by
    by_contra! h
    choose u huE huG using fun n : ℕ ↦
      h (1 / ((n : ℝ) + 1)) (by positivity)
    have hzero : Tendsto (fun n ↦ I (u n) - c) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n ↦ by simpa only [Real.norm_eq_abs] using huE n)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have henergy : Tendsto (I ∘ u) atTop (𝓝 c) := by
      simpa only [Function.comp_def, sub_add_cancel, zero_add] using hzero.add_const c
    have hgradient : Tendsto (∇ I ∘ u) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n ↦ (huG n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨x, φ, hφ, hx⟩ := hPS.tendsto_subseq henergy.cauchySeq.isBounded_range hgradient
    have hxc : I x = c :=
      tendsto_nhds_unique (hI.continuous.continuousAt.tendsto.comp hx)
        (henergy.comp hφ.tendsto_atTop)
    have hxG : ∇ I x = 0 :=
      tendsto_nhds_unique ((continuous_gradient_of_contDiff hI).continuousAt.tendsto.comp hx)
        (hgradient.comp hφ.tendsto_atTop)
    exact hc x hxc hxG
  obtain ⟨ε, hε, hgap⟩ := hband
  refine ⟨ε, hε, min ε (1 / 2), ⟨lt_min hε (by norm_num), ?_⟩, ?_⟩
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro x hx
    exact (min_le_left _ _).trans (hgap x hx)

end PDE.Analysis.Variational
