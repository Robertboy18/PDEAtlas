/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CriticalPoint.PalaisSmale.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Palais–Smale for compact perturbations of the identity

An energy estimate controls every sequence with bounded energies and vanishing
gradients. If the gradient is the identity minus a continuous map factoring
through a compact linear operator, this bound makes the entire sequence
precompact. Compactness is proved for the closure of its whole range, as required
by the Palais–Smale predicate. This abstracts step 4 of the proof of Evans, §8.5.2,
Theorem 3, where `I'[u] = u - K[f(u)]`, the energy estimate is the bound on `‖u_k‖²` that he
derives from (34) and (24), and the convergence `u_kj → u` in `L^{p+1}(U)`, from
`p + 1 < 2*`, gives (35).

## Main results

* `palaisSmale_of_compact_perturbation`: if `∇ I u = u - N (J u)` with `J` compact linear
  and `N` continuous, and `δ ‖u‖² ≤ I u + γ ‖∇ I u‖ ‖u‖` with `δ > 0` and `γ ≥ 0`, then `I`
  satisfies the Palais–Smale condition.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.2, step 4 of the proof of Theorem 3 (Existence),
  (31)-(35), pp. 509-510. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

open Filter Function Set
open scoped Topology

namespace PDE.Analysis.Variational

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A coercive energy-gradient estimate and a compact perturbation formula
imply the full Palais–Smale condition. -/
theorem palaisSmale_of_compact_perturbation
    {I : H → ℝ} (J : H →L[ℝ] X) (hJ : IsCompactOperator J)
    (N : X → H) (hN : Continuous N)
    (hgradient : ∀ u, ∇ I u = u - N (J u))
    {δ γ : ℝ} (hδ : 0 < δ) (hγ : 0 ≤ γ)
    (henergy : ∀ u, δ * ‖u‖ ^ 2 ≤ I u + γ * ‖∇ I u‖ * ‖u‖) :
    PalaisSmale I := by
  intro u hI hG
  obtain ⟨A, hA⟩ := hI.exists_norm_le
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hG).exists_norm_le
  have hu : Bornology.IsBounded (range u) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(|A| + γ * |B|) / δ + 1, ?_⟩
    rintro _ ⟨k, rfl⟩
    have hIk : I (u k) ≤ A := (le_abs_self _).trans (hA _ (mem_range_self k))
    have hGk : ‖∇ I (u k)‖ ≤ |B| :=
      (hB _ (mem_range_self k)).trans (le_abs_self B)
    have he : δ * ‖u k‖ ^ 2 ≤ A + γ * |B| * ‖u k‖ :=
      (henergy _).trans (add_le_add hIk
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGk hγ) (norm_nonneg _)))
    by_cases ht : ‖u k‖ ≤ 1
    · exact ht.trans (le_add_of_nonneg_left (by positivity))
    · have ht1 : 1 < ‖u k‖ := lt_of_not_ge ht
      have ht0 : 0 < ‖u k‖ := zero_lt_one.trans ht1
      have hAt : A ≤ |A| * ‖u k‖ := by
        nlinarith [le_abs_self A, abs_nonneg A]
      have hmul : (δ * ‖u k‖) * ‖u k‖ ≤ (|A| + γ * |B|) * ‖u k‖ := by
        nlinarith
      have hd : δ * ‖u k‖ ≤ |A| + γ * |B| :=
        (mul_le_mul_iff_left₀ ht0).mp hmul
      have hnorm : ‖u k‖ ≤ (|A| + γ * |B|) / δ :=
        (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hd)
      exact hnorm.trans (by linarith)
  have hK := (hJ.isCompact_closure_image_of_bounded hu).prod hG.isCompact_insert_range
  have hmap : Continuous (fun z : X × H ↦ N z.1 + z.2) :=
    (hN.comp continuous_fst).add continuous_snd
  have hcompact := hK.image hmap
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  rintro _ ⟨k, rfl⟩
  refine ⟨(J (u k), ∇ I (u k)), ⟨?_, ?_⟩, ?_⟩
  · exact subset_closure ⟨u k, mem_range_self k, rfl⟩
  · exact mem_insert_of_mem _ (mem_range_self k)
  · simp only [hgradient]
    abel

end PDE.Analysis.Variational
