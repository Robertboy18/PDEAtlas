/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient

/-!
# The Palais–Smale condition

A sequence with bounded real energies and gradients converging strongly to zero must
be precompact in the norm topology. This is a condition on raw sequences, without a
state bound or a weak-convergence replacement. In a complete Hilbert space,
precompactness can be expressed by compactness of the closure of the sequence's range.
`PalaisSmale` is the Palais–Smale compactness condition of Evans, §8.5.1(a), whose `I'[u]`
is the gradient `∇ I u`; his requirement `I ∈ C¹(H; ℝ)` is a separate hypothesis of the
theorems that use the condition.

## Main definitions

* `PalaisSmale`: every sequence with bounded energies and gradients tending to zero has a
  range with compact closure.

## Main results

* `PalaisSmale.tendsto_subseq`: such a sequence has a convergent subsequence.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(a), the definitions of `I'[u]` and of the
  Palais–Smale compactness condition, p. 502. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

open Filter Function Set
open scoped Topology

namespace PDE.Analysis.Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every sequence with bounded energies and gradient tending to zero is precompact. -/
def PalaisSmale (I : H → ℝ) : Prop :=
  ∀ u : ℕ → H, Bornology.IsBounded (range (I ∘ u)) →
    Tendsto (∇ I ∘ u) atTop (𝓝 0) → IsCompact (closure (range u))

/-- Palais–Smale supplies a strongly convergent subsequence of any such raw sequence. -/
theorem PalaisSmale.tendsto_subseq {I : H → ℝ} (hI : PalaisSmale I) {u : ℕ → H}
    (henergy : Bornology.IsBounded (range (I ∘ u)))
    (hgradient : Tendsto (∇ I ∘ u) atTop (𝓝 0)) :
    ∃ x : H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) := by
  obtain ⟨x, _, φ, hφ, hx⟩ :=
    (hI u henergy hgradient).tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  exact ⟨x, φ, hφ, hx⟩

end PDE.Analysis.Variational
