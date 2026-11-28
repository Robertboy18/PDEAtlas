/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.DecayAtInfinity
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.WholeSpaceRegularity
public import PDE.Analysis.Calculus.SymbolDecay.Global

/-!
# A decaying smooth background plus a smooth finite-energy field

In the self-similar constructions on `ℝ³`, a profile is a smooth field `W` that decays like
`|x|⁻¹`, with symbol decay of order `-1`, plus a smooth field `R` whose derivatives are all square
integrable. This module proves four bounds for such a sum: its derivatives of positive order are
square integrable, and all its derivatives are bounded, lie in `L⁴` and tend to zero at infinity.

## Main results

* `NavierStokes.Stationary.bounds_add_of_hasSymbolDecay` (all smooth `W` on `ℝ³` with symbol
  decay of order `-1`, all smooth `R` with every derivative in `L²`): the four bounds for
  `W + R`.

## How it works

Each bound holds for the two summands separately. For `W` it is a count of exponents: the `k`th
derivative is `O(|x|^{-1-k})`, which is bounded, tends to zero, lies in `L⁴`, and lies in `L²`
when `k ≥ 1` (`HasSymbolDecay.memLp_iteratedFDeriv`, `HasSymbolDecay.exists_bound_iteratedFDeriv`,
`HasSymbolDecay.tendsto_iteratedFDeriv_cocompact`). For `R` it is the Sobolev embedding of
`H²(ℝ³)` into bounded continuous functions, applied to every derivative
(`SobolevSpace.GraphSpace.exists_bound_iteratedFDeriv_euclidean_of_memLp_two`,
`memLp_four_iteratedFDeriv_euclidean_of_memLp_two`), together with the fact that a
square-integrable function with a bounded derivative tends to zero at infinity.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.2: the profile `Ũ` lies
  in `W^{∞,4}`, `Ũ` and `∇Ũ` are bounded and vanish at infinity, and only the boundedness of `Ũ`
  in the `C^k` norms is used. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public section

open MeasureTheory Filter SobolevSpace.GraphSpace
open PDE.Analysis (HasSymbolDecay)
open scoped ContDiff Topology

namespace NavierStokes.Stationary

/-- **A decaying background plus a finite-energy field.** Let `W` be smooth on `ℝ³` with symbol
decay of order `-1`, and let `R` be smooth with every derivative square integrable. Then the
derivatives of `W + R` of positive order are square integrable, and every derivative of `W + R`
is bounded, lies in `L⁴` and tends to zero at infinity. -/
theorem bounds_add_of_hasSymbolDecay {W R : ℝ^3 → ℝ^3} (hW : ContDiff ℝ ∞ W)
    (hWd : HasSymbolDecay (-1) W) (hR : ContDiff ℝ ∞ R)
    (hR2 : ∀ k, MemLp (iteratedFDeriv ℝ k R) 2 volume) :
    (∀ k, 1 ≤ k → MemLp (iteratedFDeriv ℝ k (W + R)) 2 volume) ∧
      (∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (W + R) x‖ ≤ C) ∧
      (∀ k, MemLp (iteratedFDeriv ℝ k (W + R)) 4 volume) ∧
      ∀ k, Tendsto (iteratedFDeriv ℝ k (W + R)) (cocompact (ℝ^3)) (𝓝 0) := by
  have hadd : ∀ k, iteratedFDeriv ℝ k (W + R) = iteratedFDeriv ℝ k W + iteratedFDeriv ℝ k R :=
    fun k ↦ iteratedFDeriv_add (hW.of_le (by exact_mod_cast le_top))
      (hR.of_le (by exact_mod_cast le_top))
  refine ⟨fun k hk ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · rw [hadd]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact (hWd.memLp_iteratedFDeriv hW k (by
      simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_ofNat]
      push_cast
      linarith)).add (hR2 k)
  · obtain ⟨C₁, h₁⟩ := hWd.exists_bound_iteratedFDeriv hW (k := k) (by omega)
    obtain ⟨C₂, h₂⟩ := exists_bound_iteratedFDeriv_euclidean_of_memLp_two hR (k := k)
      fun m _ ↦ hR2 m
    refine ⟨C₁ + C₂, fun x ↦ ?_⟩
    rw [hadd]
    exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))
  · rw [hadd]
    exact (hWd.memLp_iteratedFDeriv hW k (by
      simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_ofNat]
      push_cast
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).add
      (memLp_four_iteratedFDeriv_euclidean_of_memLp_two hR fun m _ ↦ hR2 m)
  · obtain ⟨C, hC⟩ := exists_bound_iteratedFDeriv_euclidean_of_memLp_two hR (k := k + 1)
      fun m _ ↦ hR2 m
    have hRk : Tendsto (iteratedFDeriv ℝ k R) (cocompact (ℝ^3)) (𝓝 0) :=
      (hR2 k).tendsto_cocompact_zero_of_norm_fderiv_le two_ne_zero ENNReal.ofNat_ne_top
        (hR.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k))
        fun x ↦ (norm_fderiv_iteratedFDeriv).trans_le (hC x)
    have h₀ := (hWd.tendsto_iteratedFDeriv_cocompact hW (k := k) (by omega)).add hRk
    rw [add_zero] at h₀
    rw [hadd]
    exact h₀

end NavierStokes.Stationary
