/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.BoundedApproximation

/-!
# Integrability of intermediate weak derivatives of bounded Sobolev functions

A bounded `H^k` function on Euclidean space has each weak derivative of order
`j ≤ k` in `L^{2k/j}`. At order zero this means `L∞`. There is no dimension
restriction. The proof transfers the compactly supported smooth interpolation
estimate along a bounded Sobolev approximation.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SobolevSpace.GagliardoNirenberg

/-- Convergence in `Lᵖ` gives a uniform bound on the norms of the approximants, for every
exponent: the quasi-triangle inequality `eLpNorm_add_le'` bounds the tail, and the limit has
finite seminorm because some difference `v N - g` has. -/
theorem exists_lpNorm_bound_of_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}
    {v : ℕ → X → ℝ} {g : X → ℝ} (hv : ∀ j, MemLp (v j) p μ)
    (hlim : Tendsto (fun j ↦ eLpNorm (v j - g) p μ) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, lpNorm (v j) p μ ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds zero_lt_one))
  have hg : eLpNorm g p μ < ∞ := by
    have h := eLpNorm_add_le' (μ := μ) (f := v N) (g := -(v N - g)) p
    rw [eLpNorm_neg, show v N + -(v N - g) = g by abel] at h
    exact h.trans_lt (ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top p)
      (ENNReal.add_lt_top.mpr ⟨memLp_iff.mp (hv N), (hN N le_rfl).trans ENNReal.one_lt_top⟩))
  set B : ℝ≥0∞ := ENNReal.LpAddConst p * (1 + eLpNorm g p μ)
  have hB : B < ∞ := ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top p)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hg⟩)
  have htail (j : ℕ) (hj : N ≤ j) : eLpNorm (v j) p μ ≤ B := by
    have h := eLpNorm_add_le' (μ := μ) (f := v j - g) (g := g) p
    rw [sub_add_cancel] at h
    refine h.trans ?_
    simp only [B]
    gcongr
    exact (hN j hj).le
  have hnonneg (j : ℕ) : 0 ≤ lpNorm (v j) p μ := ENNReal.toReal_nonneg
  refine ⟨B.toReal + ∑ j ∈ Finset.range N, lpNorm (v j) p μ,
    add_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun j _ ↦ hnonneg j), fun j ↦ ?_⟩
  rcases lt_or_ge j N with hj | hj
  · exact (Finset.single_le_sum (fun i _ ↦ hnonneg i) (Finset.mem_range.mpr hj)).trans
      (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  · exact (ENNReal.toReal_mono hB.ne (htail j hj)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hnonneg i))

variable {n : ℕ} [NeZero n]

/-- The top derivatives of bounded smooth Sobolev approximations have uniformly
bounded interpolation norms. Only convergence of the top derivatives is needed. -/
theorem exists_maxDerivativeLpNorm_bound {k : ℕ} (hk : 0 < k)
    {v : ℕ → ℝ^n → ℝ} (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    (hvc : ∀ j, HasCompactSupport (v j))
    (hlim : ∀ α : List (Fin n), α.length = k →
      ∃ g : ℝ^n → ℝ, MemLp g 2 volume ∧
        Tendsto (fun j ↦ eLpNorm (iteratedPartialDeriv α (v j) - g) 2 volume)
          atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, maxDerivativeLpNorm k k (v j) ≤ C := by
  classical
  have hb (α : Fin k → Fin n) :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ j, lpNorm (iteratedPartialDeriv (List.ofFn α) (v j)) 2 volume ≤ C := by
    obtain ⟨g, -, hlim⟩ := hlim (List.ofFn α) List.length_ofFn
    exact exists_lpNorm_bound_of_tendsto
      (fun j ↦ (PDE.contDiff_top_iteratedPartialDeriv (hv j) _).continuous
        |>.memLp_of_hasCompactSupport ((hvc j).iteratedPartialDeriv _)) hlim
  choose C hC hbound using hb
  let Cmax := Finset.univ.sup' Finset.univ_nonempty C
  refine ⟨Cmax, ?_, fun j ↦ ?_⟩
  · let α : Fin k → Fin n := fun _ ↦ 0
    exact (hC α).trans (Finset.le_sup' C (Finset.mem_univ α))
  · apply Finset.sup'_le
    intro α _
    rw [derivativeExponent_self hk]
    exact (hbound α j).trans (Finset.le_sup' C (Finset.mem_univ α))

/-- Every intermediate weak derivative of a bounded global `H^k` function has
the Gagliardo–Nirenberg exponent `2k/j`. The derivative is also retained in `L²`. -/
theorem exists_memLp_weakDerivative_of_bounded (k : ℕ)
    (u : GlobalSobolevSpace n k 2) {B : ℝ}
    (hB : ∀ᵐ x ∂volume, ‖u.toFun x‖ ≤ B)
    (α : List (Fin n)) (hα : α.length ≤ k) :
    ∃ g : ℝ^n → ℝ, MemLp g 2 volume ∧
      MemLp g (derivativeExponent k α.length) volume ∧
      HasWeakDerivativeOn univ α u.toFun g := by
  obtain ⟨v, hv, hvc, hvB, _, hlim⟩ :=
    exists_bounded_globalApproximation_Wkp (Approximation.standardMollifier n)
      2 (by norm_num) k u hB
  obtain ⟨g, hg, hwg, hvg⟩ := hlim α hα
  refine ⟨g, hg, ?_, hwg⟩
  by_cases hk : k = 0
  · subst k
    have hnil : α = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hα)
    subst α
    simp only [List.length_nil, derivativeExponent_zero]
    have hbound : ∀ j, eLpNorm (v j) ∞ volume ≤ ENNReal.ofReal B := by
      intro j
      rw [eLpNorm_exponent_top (hv j).continuous.aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (hvB j))
    refine lt_of_le_of_lt (b := ENNReal.ofReal B) ?_ ENNReal.ofReal_lt_top
    exact eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hbound)
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hvg)
      (fun j ↦ (hv j).continuous.aestronglyMeasurable)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    obtain ⟨C, hC, htop⟩ := exists_maxDerivativeLpNorm_bound hkpos hv hvc
      (fun β hβ ↦ by
        obtain ⟨g, hg, _, hlim⟩ := hlim β hβ.le
        exact ⟨g, hg, hlim⟩)
    obtain ⟨A, hA, hest⟩ := exists_constant_lpNorm_iteratedPartialDeriv_le (n := n) k
    have hbase (j : ℕ) : lpNorm (v j) ∞ volume ≤ max B 0 := by
      have he : eLpNorm (v j) ∞ volume ≤ ENNReal.ofReal (max B 0) := by
        rw [eLpNorm_exponent_top (hv j).continuous.aestronglyMeasurable]
        exact eLpNormEssSup_le_of_ae_bound
          (Eventually.of_forall fun x ↦ (hvB j x).trans (le_max_left _ _))
      simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal (le_max_right B 0)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    have hder (j : ℕ) :
        MemLp (iteratedPartialDeriv α (v j)) (derivativeExponent k α.length) volume :=
      (PDE.contDiff_top_iteratedPartialDeriv (hv j) α).continuous.memLp_of_hasCompactSupport
        ((hvc j).iteratedPartialDeriv α)
    have hbound (j : ℕ) :
        eLpNorm (iteratedPartialDeriv α (v j)) (derivativeExponent k α.length) volume ≤
          ENNReal.ofReal (A * (max B 0 + C)) := by
      rw [← ofReal_lpNorm (hder j)]
      apply ENNReal.ofReal_le_ofReal
      exact (hest (v j) ((hv j).of_le (by simp)) (hvc j) α hα).trans
        (mul_le_mul_of_nonneg_left (add_le_add (hbase j) (htop j)) (by linarith))
    refine lt_of_le_of_lt (b := ENNReal.ofReal (A * (max B 0 + C))) ?_
      ENNReal.ofReal_lt_top
    exact eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hbound)
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hvg)
      (fun j ↦ (hder j).aestronglyMeasurable)

end SobolevSpace.GagliardoNirenberg
