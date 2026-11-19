/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.StripMeasure

/-!
# Uniform decay of upper level-set measures

The successive strips are disjoint. Summing the strip estimate therefore
shows that the squared measure at the N-th level is at most a constant
divided by N. The level needed for a prescribed small measure is chosen
uniformly before the coefficients and the weak solution.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

private theorem level_measure_sq_le_of_strip_control
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (L : ℕ → ℝ) (hL : StrictMono L)
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ j : ℕ, μ.real {x | L (j + 1) ≤ f x} ^ 2 ≤
      C * μ.real {x | L j < f x ∧ f x < L (j + 1)}) (N : ℕ) :
    (N : ℝ) * μ.real {x | L N ≤ f x} ^ 2 ≤ C * μ.real univ := by
  let E (j : ℕ) := {x | L j < f x ∧ f x < L (j + 1)}
  have hE (j : ℕ) : MeasurableSet (E j) := by
    change MeasurableSet ({x | L j < f x} ∩ {x | f x < L (j + 1)})
    exact (measurableSet_lt measurable_const hf).inter (measurableSet_lt hf measurable_const)
  have hdisj : Pairwise (fun i j ↦ Disjoint (E i) (E j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hle := hL.monotone (Nat.succ_le_of_lt hij)
      exact (not_lt_of_ge hle) (hy.1.trans hx.2)
    · have hle := hL.monotone (Nat.succ_le_of_lt hji)
      exact (not_lt_of_ge hle) (hx.1.trans hy.2)
  have hsum : (∑ j ∈ Finset.range N, μ.real (E j)) ≤ μ.real univ :=
    sum_measureReal_le_measureReal_univ (fun j _ ↦ hE j)
      (fun i _ j _ hij ↦ hdisj hij)
  calc
    _ = ∑ _j ∈ Finset.range N, μ.real {x | L N ≤ f x} ^ 2 := by simp
    _ ≤ ∑ j ∈ Finset.range N, C * μ.real (E j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hmono : μ.real {x | L N ≤ f x} ≤ μ.real {x | L (j + 1) ≤ f x} :=
        measureReal_mono (fun x hx ↦
          (hL.monotone (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans hx)
      exact (pow_le_pow_left₀ measureReal_nonneg hmono 2).trans (hstep j)
    _ = C * ∑ j ∈ Finset.range N, μ.real (E j) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC

variable {n : ℕ} [Fact (0 < n)]

/-- The upper level-set measures of a weak solution decay at least
as `N⁻¹ᐟ²` along the levels `1 - 2⁻ᴺ`. The coefficient and solution bounds
determine the constant uniformly. -/
theorem exists_upper_level_measure_sq_mul_nat_le
    {α Λ m : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) 2)),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(ball (0 : ℝ^n) 2)), IsInteriorWeakDivergenceSolution a 0 u →
        (∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) 2), wkpBaseCoordinateCLM u x ≤ 1) →
        m ≤ (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | wkpBaseCoordinateCLM u x ≤ 0} →
      ∀ N : ℕ, (N : ℝ) * (volume.restrict (ball (0 : ℝ^n) 1)).real
        {x | 1 - (1 / 2 : ℝ) ^ N ≤ wkpBaseCoordinateCLM u x} ^ 2 ≤ C := by
  obtain ⟨P, hP, hstrip⟩ := exists_upper_level_measure_sq_le_strip_measure (n := n) hα hΛ hm
  let μ := volume.restrict (ball (0 : ℝ^n) 1)
  let : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (ball (0 : ℝ^n) 1)) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  refine ⟨P * μ.real univ + 1, by positivity, ?_⟩
  intro a haΛ ha u hu hupper hlower N
  let L (j : ℕ) := 1 - (1 / 2 : ℝ) ^ j
  have hL : StrictMono L := fun i j hij ↦
    sub_lt_sub_left (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hij) 1
  have hnext (j : ℕ) : (1 + L j) / 2 = L (j + 1) := by
    dsimp only [L]
    rw [pow_succ]
    ring
  have hstep (j : ℕ) : μ.real {x | L (j + 1) ≤ wkpBaseCoordinateCLM u x} ^ 2 ≤
      P * μ.real {x | L j < wkpBaseCoordinateCLM u x ∧
        wkpBaseCoordinateCLM u x < L (j + 1)} := by
    have hk : 0 ≤ L j := sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
    have hk1 : L j < 1 := sub_lt_self 1 (pow_pos (by norm_num) j)
    simpa only [hnext] using hstrip a haΛ ha u hu hupper hlower (L j) hk hk1
  exact (level_measure_sq_le_of_strip_control μ (wkpBaseCoordinateCLM u)
    (Lp.stronglyMeasurable _).measurable L hL hP.le hstep N).trans
      (le_add_of_nonneg_right zero_le_one)

/-- A prescribed small upper level-set measure is reached at a level strictly
below one, uniformly over all weak solutions with the same bounds. -/
theorem exists_upper_level_with_small_measure
    {α Λ m ε : ℝ} (hα : 0 < α) (hm : 0 < m) (hε : 0 < ε) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) 2)),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(ball (0 : ℝ^n) 2)), IsInteriorWeakDivergenceSolution a 0 u →
        (∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) 2), wkpBaseCoordinateCLM u x ≤ 1) →
        m ≤ (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | wkpBaseCoordinateCLM u x ≤ 0} →
        (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | k < wkpBaseCoordinateCLM u x} ≤ ε := by
  rcases lt_or_ge Λ 0 with hΛ | hΛ
  · exact ⟨0, le_rfl, zero_lt_one, fun a haΛ ↦ absurd
      ((norm_nonneg _).trans (haΛ ⟨0, Fact.out⟩ ⟨0, Fact.out⟩)) (not_le.mpr hΛ)⟩
  obtain ⟨C, hC, hdecay⟩ := exists_upper_level_measure_sq_mul_nat_le (n := n) hα hΛ hm
  let : IsFiniteMeasure (volume.restrict (ball (0 : ℝ^n) 1)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε ^ 2)
  have hNpos : (0 : ℝ) < N := (div_pos hC (sq_pos_of_pos hε)).trans hN
  refine ⟨1 - (1 / 2 : ℝ) ^ N,
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)),
    sub_lt_self 1 (pow_pos (by norm_num) N), ?_⟩
  intro a haΛ ha u hu hupper hlower
  have hd := hdecay a haΛ ha u hu hupper hlower N
  have hbound :
      (volume.restrict (ball (0 : ℝ^n) 1)).real
        {x | 1 - (1 / 2 : ℝ) ^ N ≤ wkpBaseCoordinateCLM u x} ≤ ε := by
    by_contra h
    have hlt := lt_of_not_ge h
    have hsq : ε ^ 2 <
        (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | 1 - (1 / 2 : ℝ) ^ N ≤ wkpBaseCoordinateCLM u x} ^ 2 :=
      (sq_lt_sq₀ hε.le measureReal_nonneg).mpr hlt
    have hc : C < (N : ℝ) * ε ^ 2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hN
    linarith [mul_lt_mul_of_pos_left hsq hNpos]
  have hsets : {x | 1 - (1 / 2 : ℝ) ^ N < wkpBaseCoordinateCLM u x} ⊆
      {x | 1 - (1 / 2 : ℝ) ^ N ≤ wkpBaseCoordinateCLM u x} := by
    intro x hx
    change 1 - (1 / 2 : ℝ) ^ N < wkpBaseCoordinateCLM u x at hx
    change 1 - (1 / 2 : ℝ) ^ N ≤ wkpBaseCoordinateCLM u x
    exact hx.le
  exact (measureReal_mono hsets).trans hbound

end SobolevSpace.GraphSpace
