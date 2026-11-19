/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Minmax for a complete family of weak eigenfunctions

Let `B` be a symmetric positive form on `V`, and let `j : V →L[ℝ] H` map its weak
eigenfunctions to a Hilbert basis of `H`. A finite set of low eigenmodes minimizes
the uniform Rayleigh bound among subspaces of the same dimension.

The basis need not be indexed by natural numbers. A finite set `s` contains the
selected low modes, and `k ∈ s` has the largest selected eigenvalue. The hypothesis
that every omitted eigenvalue is at least `lambda k` permits ties and therefore
counts multiplicities.

The proof first bounds finite spectral energy by the full energy. Parseval then
gives the lower bound on vectors orthogonal to the selected modes. Any subspace
of dimension `s.card` contains a nonzero vector orthogonal to `s.erase k`, by the
dimension bound on the kernel of its coordinate map.

The map `j` may have a kernel: positivity of the energy
excludes nonzero kernel vectors from subspaces with a finite Rayleigh bound.

`isLeast_eigenvalue_minmax` is the min-max form of the Courant–Fischer characterization: the
largest selected eigenvalue is the minimum, over subspaces `W` of dimension `s.card`, of the
largest Rayleigh quotient `B v v / ‖j v‖²` on `W`, attained by the span of the selected modes.
Evans, §6.6, Problem 13 (Courant minimax principle), asks for the max-min form
`λ_k = max_{S ∈ Σ_{k-1}} min_{u ∈ S^⊥, ‖u‖_{L²(U)} = 1} B[u, u]` for the `k`-th eigenvalue,
which we do not prove.

## Main results

* `energy_sum_weakEigenfunctions`: for weak eigenfunctions with orthonormal pivot images,
  `B (∑ c i • u i) (∑ c i • u i) = ∑ λ i (c i)²`.
* `mul_norm_sq_le_energy_of_orthogonal`: if every mode outside `s` has eigenvalue at least
  `r`, then `r ‖j v‖² ≤ B v v` whenever `j v` is orthogonal to the modes in `s`.
* `isLeast_eigenvalue_minmax`: the largest eigenvalue `λ k` of a finite set `s` of low modes
  is the least `r` for which some subspace of dimension `s.card` satisfies
  `B v v ≤ r ‖j v‖²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.6, Problem 13 (Courant minimax principle), p. 368.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

open scoped BigOperators InnerProductSpace

variable {ι V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The energy of a finite sum of weak eigenfunctions is the eigenvalue-weighted
sum of squared coefficients when their pivot images are orthonormal. -/
theorem energy_sum_weakEigenfunctions
    (B : V →L[ℝ] StrongDual ℝ V) (j : V →L[ℝ] H)
    (b : ι → H) (hb : Orthonormal ℝ b) (lambda : ι → ℝ) (u : ι → V)
    (hju : ∀ i, j (u i) = b i)
    (hweak : ∀ i v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ)
    (s : Finset ι) (c : ι → ℝ) :
    B (∑ i ∈ s, c i • u i) (∑ i ∈ s, c i • u i) =
      ∑ i ∈ s, lambda i * (c i) ^ 2 := by
  classical
  rw [map_sum B, sum_apply]
  simp only [map_smul, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [hweak]
  simp only [map_sum, map_smul, hju]
  rw [hb.inner_right_sum c hi]
  ring

/-- Removing any finite set of orthogonal weak eigenmodes leaves nonnegative
energy. Equivalently, their weighted squared coordinates are bounded by the full
energy. Completeness of the orthonormal family is not required. -/
theorem sum_eigenvalue_mul_inner_sq_le
    (B : V →L[ℝ] StrongDual ℝ V) (hnonneg : ∀ v, 0 ≤ B v v)
    (hsymm : ∀ v w, B v w = B w v) (j : V →L[ℝ] H)
    (b : ι → H) (hb : Orthonormal ℝ b) (lambda : ι → ℝ) (u : ι → V)
    (hju : ∀ i, j (u i) = b i)
    (hweak : ∀ i v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ)
    (s : Finset ι) (v : V) :
    ∑ i ∈ s, lambda i * ⟪b i, j v⟫_ℝ ^ 2 ≤ B v v := by
  classical
  let p : V := ∑ i ∈ s, ⟪b i, j v⟫_ℝ • u i
  have hpp : B p p = ∑ i ∈ s, lambda i * ⟪b i, j v⟫_ℝ ^ 2 :=
    energy_sum_weakEigenfunctions B j b hb lambda u hju hweak s _
  have hpv : B p v = ∑ i ∈ s, lambda i * ⟪b i, j v⟫_ℝ ^ 2 := by
    dsimp only [p]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hweak]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hrem := hnonneg (v - p)
  rw [map_sub B, sub_apply, map_sub, map_sub, hsymm v p, hpv, hpp] at hrem
  linarith

/-- If every mode outside `s` has eigenvalue at least `r`, the energy of any
vector whose pivot image is orthogonal to `s` is at least `r` times its squared
pivot norm. Parseval accounts for all omitted modes; `s` may be any set of modes. -/
theorem mul_norm_sq_le_energy_of_orthogonal
    (B : V →L[ℝ] StrongDual ℝ V) (hnonneg : ∀ v, 0 ≤ B v v)
    (hsymm : ∀ v w, B v w = B w v) (j : V →L[ℝ] H)
    (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (u : ι → V)
    (hju : ∀ i, j (u i) = b i)
    (hweak : ∀ i v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ)
    (s : Set ι) (r : ℝ) (hbound : ∀ i ∉ s, r ≤ lambda i)
    (v : V) (horth : ∀ i ∈ s, ⟪b i, j v⟫_ℝ = 0) :
    r * ‖j v‖ ^ 2 ≤ B v v := by
  classical
  have hsum : HasSum (fun i ↦ ⟪b i, j v⟫_ℝ ^ 2) (‖j v‖ ^ 2) := by
    convert! b.hasSum_inner_mul_inner (j v) (j v) using 1
    · ext i
      rw [real_inner_comm (b i) (j v), pow_two]
    · exact (real_inner_self_eq_norm_sq _).symm
  apply le_of_tendsto' (hsum.mul_left r)
  intro t
  calc
    ∑ i ∈ t, r * ⟪b i, j v⟫_ℝ ^ 2 ≤
        ∑ i ∈ t, lambda i * ⟪b i, j v⟫_ℝ ^ 2 := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      by_cases hi : i ∈ s
      · simp only [horth i hi, zero_pow two_ne_zero, mul_zero, le_refl]
      · exact mul_le_mul_of_nonneg_right (hbound i hi) (sq_nonneg _)
    _ ≤ B v v :=
      sum_eigenvalue_mul_inner_sq_le B hnonneg hsymm j b b.orthonormal
        lambda u hju hweak t v

/-- The largest eigenvalue in a finite set of low modes is the least uniform
Rayleigh bound achievable by a subspace of that dimension. Repeated eigenvalues
are allowed, and the index set may be finite or infinite.

The condition `B v v ≤ r * ‖j v‖²` includes zero vectors without division.
Strict positivity of `B` ensures that every nonzero vector in such a subspace
has nonzero pivot image, so this is the usual minmax Rayleigh characterization. -/
theorem isLeast_eigenvalue_minmax
    (B : V →L[ℝ] StrongDual ℝ V) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (hsymm : ∀ v w, B v w = B w v) (j : V →L[ℝ] H)
    (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (u : ι → V)
    (hju : ∀ i, j (u i) = b i)
    (hweak : ∀ i v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ)
    (s : Finset ι) (k : ι) (hk : k ∈ s)
    (hinside : ∀ i ∈ s, lambda i ≤ lambda k)
    (houtside : ∀ i ∉ s, lambda k ≤ lambda i) :
    IsLeast {r : ℝ | ∃ W : Submodule ℝ V,
      Module.finrank ℝ W = s.card ∧ ∀ v ∈ W, B v v ≤ r * ‖j v‖ ^ 2}
      (lambda k) := by
  classical
  have hnonneg (v : V) : 0 ≤ B v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos v hv).le
  have hulin : LinearIndependent ℝ u := by
    apply LinearIndependent.of_comp j.toLinearMap
    simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, hju] using
      b.orthonormal.linearIndependent
  constructor
  · refine ⟨Submodule.span ℝ (u '' (s : Set ι)), ?_, ?_⟩
    · rw [Set.image_eq_range]
      simpa only [Function.comp_def, Fintype.card_coe] using!
        finrank_span_eq_card (hulin.comp (fun i : s ↦ (i : ι)) Subtype.val_injective)
    · intro v hv
      obtain ⟨c, rfl⟩ :=
        (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).mp hv
      have hmass : ‖j (∑ i ∈ s, c i • u i)‖ ^ 2 = ∑ i ∈ s, (c i) ^ 2 := by
        simp only [map_sum, map_smul, hju]
        simpa only [real_inner_self_eq_norm_sq, conj_trivial, pow_two] using
          b.orthonormal.inner_sum c c s
      rw [energy_sum_weakEigenfunctions B j b b.orthonormal lambda u hju hweak, hmass,
        Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_right (hinside i hi) (sq_nonneg _)
  · rintro r ⟨W, hdim, hupper⟩
    have hdimpos : 0 < Module.finrank ℝ W := by
      rw [hdim]
      exact Finset.card_pos.mpr ⟨k, hk⟩
    have : FiniteDimensional ℝ W := FiniteDimensional.of_finrank_pos hdimpos
    let t := s.erase k
    let L : W →ₗ[ℝ] (t → ℝ) :=
      LinearMap.pi fun i ↦ ((innerSL ℝ (b i)).comp (j.comp W.subtypeL)).toLinearMap
    have hker : LinearMap.ker L ≠ ⊥ := by
      apply LinearMap.ker_ne_bot_of_finrank_lt
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hdim]
      exact Finset.card_erase_lt_of_mem hk
    obtain ⟨v, hvker, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have horth (i : ι) (hi : i ∈ t) : ⟪b i, j (v : V)⟫_ℝ = 0 :=
      congrFun (LinearMap.mem_ker.mp hvker) ⟨i, hi⟩
    have hbound (i : ι) (hi : i ∉ t) : lambda k ≤ lambda i := by
      by_cases hik : i = k
      · simp [hik]
      · exact houtside i fun his ↦ hi (Finset.mem_erase.mpr ⟨hik, his⟩)
    have hlower := mul_norm_sq_le_energy_of_orthogonal B hnonneg hsymm j
      b lambda u hju hweak (t : Set ι) (lambda k) (fun i hi ↦ hbound i (Finset.mem_coe.not.mp hi))
      (v : V) fun i hi ↦ horth i (Finset.mem_coe.mp hi)
    have hvne' : (v : V) ≠ 0 := by
      intro h
      exact hvne (Subtype.ext h)
    have hjvne : j (v : V) ≠ 0 := by
      intro h
      have hle := hupper v v.property
      rw [h, norm_zero, zero_pow two_ne_zero, mul_zero] at hle
      exact (not_le_of_gt (hpos v hvne')) hle
    exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hjvne))).mp
      (hlower.trans (hupper v v.property))

end PDE.Analysis.Variational
