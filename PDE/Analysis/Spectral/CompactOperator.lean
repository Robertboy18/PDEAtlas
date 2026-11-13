/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral accumulation for compact operators

A convergent sequence of distinct nonzero eigenvalues of a compact operator
converges to zero. Hence the eigenvalues of norm at least `ε > 0` are finitely many and the
nonzero eigenvalues are countable, the eigenvalue form of Evans, *Partial Differential
Equations*, 2nd ed., Appendix D.5, Theorem 6(iii).

## Main results

* `distinct_eigenvalues_tendsto_zero_of_pow_approx`: the general criterion described below.
* `distinct_eigenvalues_tendsto_zero`: distinct nonzero eigenvalues of a compact operator
  cannot converge to a nonzero scalar.
* `finite_eigenvalues_norm_ge`: finitely many eigenvalues have norm at least `ε > 0`.
* `countable_nonzero_eigenvalues`: the nonzero eigenvalues form a countable set.

## How it works

We follow the classical argument of step 3 of Evans's proof of Theorem 6, with Mathlib's
`riesz_lemma_of_norm_lt` in place of his orthogonal complements, and it gives a more general
criterion. Let
`μₙ → η` be distinct nonzero eigenvalues of `T`, and suppose that for every `ε > 0` some power
splits as `Tᵐ = A + K` with `K` compact and `‖A‖ ≤ ε ‖μₙ‖ᵐ` for all `n`. Eigenvectors for the
distinct eigenvalues generate a strictly increasing sequence of finite-dimensional subspaces
`Hₙ`, and `Tᵐ - μₙᵐ` maps `Hₙ₊₁` into `Hₙ`. Riesz's lemma selects vectors `uₙ ∈ Hₙ₊₁` of
bounded norm at distance at least `1` from `Hₙ`. If `η ≠ 0`, the vectors `μₙ⁻ᵐ K uₙ` are
uniformly separated once `ε` is small, but they have a convergent subsequence because `K` is
compact. For a compact operator take `m = 1`, `A = 0`. The same criterion covers compact
perturbations of operators whose powers decay faster than the eigenvalues.

## Implementation notes

The sequential results hold over every complete nontrivially normed field. Finiteness away
from zero and countability need compact closed scalar balls, as over the real or complex
numbers. No inner product or completeness of the vector space is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.5, Theorem 6(iii), and step 3 of its proof,
  p. 727. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped Topology

namespace PDE.Analysis

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Accumulation of eigenvalues.** Let `μ n` be distinct nonzero eigenvalues of `T` with
`μ n → η`. If for every `ε > 0` some power splits as `T ^ m = A + K` with `K` compact and
`‖A‖ ≤ ε ‖μ n‖ ^ m` for every `n`, then `η = 0`. -/
theorem distinct_eigenvalues_tendsto_zero_of_pow_approx [CompleteSpace 𝕜] (T : V →L[𝕜] V)
    (μ : ℕ → 𝕜) (hμinj : Injective μ) (hμne : ∀ n, μ n ≠ 0)
    (hμeig : ∀ n, Module.End.HasEigenvalue (T : Module.End 𝕜 V) (μ n))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (A K : V →L[𝕜] V),
      T ^ m = A + K ∧ IsCompactOperator K ∧ ∀ n, ‖A‖ ≤ ε * ‖μ n‖ ^ m)
    {η : 𝕜} (hμ : Tendsto μ atTop (𝓝 η)) : η = 0 := by
  by_contra hη
  choose w hw using fun n ↦ (hμeig n).exists_hasEigenvector
  have hwlin : LinearIndependent 𝕜 w :=
    Module.End.eigenvectors_linearIndependent' (T : Module.End 𝕜 V) μ hμinj w hw
  let H (n : ℕ) : Submodule 𝕜 V := Submodule.span 𝕜 (w '' (Finset.range n : Set ℕ))
  have hHmono {m n : ℕ} (hmn : m ≤ n) : H m ≤ H n :=
    Submodule.span_mono (image_mono (by simpa using Finset.range_mono hmn))
  have hHclosed (n : ℕ) : IsClosed (H n : Set V) := by
    let : FiniteDimensional 𝕜 (H n) :=
      FiniteDimensional.span_of_finite 𝕜 ((Finset.range n).finite_toSet.image w)
    exact (H n).closed_of_finiteDimensional
  have hwnext (n : ℕ) : w n ∈ H (n + 1) := Submodule.subset_span ⟨n, by simp, rfl⟩
  have hwnot (n : ℕ) : w n ∉ H n := hwlin.notMem_span_image (by simp)
  obtain ⟨c : 𝕜, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  let R : ℝ := ‖c‖ + 1
  have hR : ‖c‖ < R := by simp [R]
  have hR0 : 0 < R := by positivity
  have huExists (n : ℕ) :
      ∃ u : H (n + 1), ‖u‖ ≤ R ∧ ∀ y ∈ H n, 1 ≤ ‖(u : V) - y‖ := by
    let F : Submodule 𝕜 (H (n + 1)) := (H n).comap (H (n + 1)).subtype
    have hFclosed : IsClosed (F : Set (H (n + 1))) := (hHclosed n).preimage_val
    obtain ⟨u, huR, hufar⟩ :=
      riesz_lemma_of_norm_lt hc hR hFclosed ⟨⟨w n, hwnext n⟩, hwnot n⟩
    exact ⟨u, huR, fun y hy ↦ hufar ⟨y, hHmono (Nat.le_succ n) hy⟩ hy⟩
  choose u huR hufar using huExists
  have huH (n : ℕ) : (u n : V) ∈ H (n + 1) := (u n).property
  obtain ⟨m, A, Km, hTm, hKm, hA⟩ := happrox (1 / (4 * R)) (by positivity)
  have hmap (n : ℕ) {x : V} (hx : x ∈ H (n + 1)) : (T ^ m) x - μ n ^ m • x ∈ H n := by
    refine Submodule.span_induction (p := fun x _ ↦ (T ^ m) x - μ n ^ m • x ∈ H n)
      ?_ ?_ ?_ ?_ hx
    · rintro x ⟨i, hi, rfl⟩
      have hpow : (T ^ m) (w i) = μ i ^ m • w i := by
        rw [← ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_pow]
        exact (hw i).pow_apply m
      rw [hpow, ← sub_smul]
      rcases (Nat.lt_succ_iff.mp (by simpa using hi)).lt_or_eq with hin | rfl
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hin, rfl⟩)
      · simp
    · simp
    · intro x y _hx _hy hxmem hymem
      simpa [map_add, add_smul, add_sub_add_comm] using (H n).add_mem hxmem hymem
    · intro a x _hx hxmem
      simpa [map_smul, smul_sub, smul_smul, mul_comm] using (H n).smul_mem a hxmem
  let z (n : ℕ) : V := (μ n ^ m)⁻¹ • Km (u n : V)
  let e (n : ℕ) : V := (μ n ^ m)⁻¹ • A (u n : V)
  have hzT (n : ℕ) : z n + e n = (μ n ^ m)⁻¹ • (T ^ m) (u n : V) := by
    simp only [z, e, ← smul_add, hTm, add_apply]
    rw [add_comm]
  have he (n : ℕ) : ‖e n‖ ≤ 1 / 4 := by
    have hμm : 0 < ‖μ n‖ ^ m := pow_pos (norm_pos_iff.mpr (hμne n)) m
    calc ‖e n‖ = (‖μ n‖ ^ m)⁻¹ * ‖A (u n : V)‖ := by
          simp only [e, norm_smul, norm_inv, norm_pow]
      _ ≤ (‖μ n‖ ^ m)⁻¹ * (1 / (4 * R) * ‖μ n‖ ^ m * R) := by
          gcongr
          exact (A.le_opNorm _).trans (mul_le_mul (hA n) (huR n) (norm_nonneg _) (by positivity))
      _ = 1 / 4 := by field_simp
  have hsep {k n : ℕ} (hkn : k < n) : 1 / 2 ≤ ‖z n - z k‖ := by
    have hmem : (μ n ^ m)⁻¹ • (T ^ m) (u n : V) - (u n : V) ∈ H n := by
      have h := (H n).smul_mem (μ n ^ m)⁻¹ (hmap n (huH n))
      rwa [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero m (hμne n)), one_smul] at h
    have hk : z k + e k ∈ H n := by
      have h3 : (T ^ m) (u k : V) ∈ H (k + 1) := by
        simpa using (H (k + 1)).add_mem (hHmono (Nat.le_succ k) (hmap k (huH k)))
          ((H (k + 1)).smul_mem (μ k ^ m) (huH k))
      rw [hzT k]
      exact hHmono (Nat.succ_le_of_lt hkn) ((H (k + 1)).smul_mem _ h3)
    have hfar := hufar n _ ((H n).sub_mem hk hmem)
    have hid : (u n : V) - ((z k + e k) - ((μ n ^ m)⁻¹ • (T ^ m) (u n : V) - (u n : V))) =
        (z n - z k) + (e n - e k) := by
      rw [← hzT n]
      abel
    rw [hid] at hfar
    linarith [he n, he k, norm_add_le (z n - z k) (e n - e k), norm_sub_le (e n) (e k)]
  obtain ⟨Q, hQcompact, hQimage⟩ := hKm.image_closedBall_subset_compact R
  obtain ⟨y, -, ψ, hψ, hKuy⟩ := hQcompact.tendsto_subseq
    (x := fun n ↦ Km (u n : V))
    (fun n ↦ hQimage ⟨(u n : V), by simpa [Metric.mem_closedBall] using huR n, rfl⟩)
  have hinv : Tendsto (fun n ↦ (μ (ψ n) ^ m)⁻¹) atTop (𝓝 (η ^ m)⁻¹) :=
    ((hμ.comp hψ.tendsto_atTop).pow m).inv₀ (pow_ne_zero m hη)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 (hinv.smul hKuy).cauchySeq (1 / 2) (by norm_num)
  have hlt : ‖z (ψ (N + 1)) - z (ψ N)‖ < 1 / 2 := by
    simpa [dist_eq_norm_sub] using hN (N + 1)
  exact (not_le_of_gt hlt) (hsep (hψ (Nat.lt_succ_self N)))

/-- Distinct nonzero eigenvalues of a compact operator cannot converge to a
nonzero scalar. This is step 3 of Evans's proof of Appendix D.5, Theorem 6(iii). -/
theorem distinct_eigenvalues_tendsto_zero
    [CompleteSpace 𝕜]
    (K : V →L[𝕜] V) (hK : IsCompactOperator K)
    (μ : ℕ → 𝕜) (hμinj : Injective μ) (hμne : ∀ n, μ n ≠ 0)
    (hμeig : ∀ n, Module.End.HasEigenvalue (K : Module.End 𝕜 V) (μ n))
    {η : 𝕜} (hμ : Tendsto μ atTop (nhds η)) : η = 0 :=
  distinct_eigenvalues_tendsto_zero_of_pow_approx K μ hμinj hμne hμeig
    (fun _ hε ↦ ⟨1, 0, K, by rw [pow_one, zero_add], hK, fun _ ↦ by
      rw [norm_zero]
      exact mul_nonneg hε.le (by positivity)⟩) hμ

/-- Every eigenvalue of a bounded operator has norm at most the operator norm.
No completeness or compactness assumption is needed. -/
theorem norm_eigenvalue_le_norm
    (K : V →L[𝕜] V) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue (K : Module.End 𝕜 V) μ) : ‖μ‖ ≤ ‖K‖ := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx.2
  have hKx : K x = μ • x := by simpa using hx.apply_eq_smul
  have hle := K.le_opNorm x
  rw [hKx, norm_smul] at hle
  exact (mul_le_mul_iff_left₀ hxnorm).mp hle

section ProperField

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Finitely many eigenvalues away from zero.** A set `S` of eigenvalues of `T` of norm at
least `ε₀ > 0` is finite if for every `ε > 0` some power splits as `T ^ m = A + K` with `K`
compact and `‖A‖ ≤ ε ‖μ‖ ^ m` for every `μ ∈ S`. -/
theorem finite_eigenvalues_of_pow_approx (T : V →L[𝕜] V) {S : Set 𝕜} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hS : ∀ μ ∈ S, Module.End.HasEigenvalue (T : Module.End 𝕜 V) μ ∧ ε₀ ≤ ‖μ‖)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (A K : V →L[𝕜] V),
      T ^ m = A + K ∧ IsCompactOperator K ∧ ∀ μ ∈ S, ‖A‖ ≤ ε * ‖μ‖ ^ m) :
    S.Finite := by
  by_contra hSfinite
  let : Infinite S := Set.infinite_coe_iff.mpr (Set.not_finite.mp hSfinite)
  let e : ℕ ↪ S := Infinite.natEmbedding S
  have hball (n : ℕ) : (e n : 𝕜) ∈ Metric.closedBall (0 : 𝕜) ‖T‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_eigenvalue_le_norm T (hS _ (e n).2).1
  obtain ⟨η, -, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : 𝕜) ‖T‖).tendsto_subseq hball
  have hη : η = 0 := by
    refine distinct_eigenvalues_tendsto_zero_of_pow_approx T (fun n ↦ e (ψ n))
      ((Subtype.val_injective.comp e.injective).comp hψ.injective)
      (fun n ↦ norm_pos_iff.mp (hε₀.trans_le (hS _ (e (ψ n)).2).2))
      (fun n ↦ (hS _ (e (ψ n)).2).1) (fun ε hε ↦ ?_) hlim
    obtain ⟨m, A, K, hTm, hK, hA⟩ := happrox ε hε
    exact ⟨m, A, K, hTm, hK, fun n ↦ hA _ (e (ψ n)).2⟩
  have hbound : ε₀ ≤ ‖η‖ := ge_of_tendsto' hlim.norm fun n ↦ (hS _ (e (ψ n)).2).2
  rw [hη, norm_zero] at hbound
  exact (not_le_of_gt hε₀) hbound

/-- A compact operator has only finitely many eigenvalues whose norm is at
least a fixed positive threshold, provided closed scalar balls are compact.
This is the finite-away-from-zero form of Evans, Appendix D.5, Theorem 6(iii). -/
theorem finite_eigenvalues_norm_ge
    (K : V →L[𝕜] V) (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | Module.End.HasEigenvalue (K : Module.End 𝕜 V) μ ∧ ε ≤ ‖μ‖}.Finite :=
  finite_eigenvalues_of_pow_approx K hε (fun _ hμ ↦ hμ) fun _ hδ ↦
    ⟨1, 0, K, by rw [pow_one, zero_add], hK, fun _ _ ↦ by
      rw [norm_zero]
      exact mul_nonneg hδ.le (by positivity)⟩

/-- The nonzero eigenvalues of a compact operator form a countable set when
closed scalar balls are compact. Completeness of the vector space is not required. -/
theorem countable_nonzero_eigenvalues
    (K : V →L[𝕜] V) (hK : IsCompactOperator K) :
    {μ : 𝕜 | μ ≠ 0 ∧ Module.End.HasEigenvalue (K : Module.End 𝕜 V) μ}.Countable := by
  let S : ℕ → Set 𝕜 := fun n ↦
    {μ : 𝕜 | Module.End.HasEigenvalue (K : Module.End 𝕜 V) μ ∧
      1 / (n + 1 : ℝ) ≤ ‖μ‖}
  have hSfinite (n : ℕ) : (S n).Finite := by
    apply finite_eigenvalues_norm_ge K hK
    positivity
  have heq : {μ : 𝕜 | μ ≠ 0 ∧ Module.End.HasEigenvalue (K : Module.End 𝕜 V) μ} =
      ⋃ n, S n := by
    ext μ
    constructor
    · rintro ⟨hμne, hμeig⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hμne)
      exact Set.mem_iUnion.2 ⟨n, hμeig, hn.le⟩
    · intro hμ
      obtain ⟨n, hμeig, hn⟩ := Set.mem_iUnion.1 hμ
      refine ⟨?_, hμeig⟩
      intro hzero
      rw [hzero, norm_zero] at hn
      have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
      exact (not_le_of_gt hpos) hn
  rw [heq]
  exact Set.countable_iUnion fun n ↦ (hSfinite n).countable

end ProperField

end PDE.Analysis
