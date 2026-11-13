/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.BallChain.TimeOrdered

/-!
# Uniform forward comparison on a compact set

Interior balls give uniform comparisons from nearby points to a fixed base
point, and from that base point to nearby points at later times. A finite
subcover bounds the resulting constants. The paths, time subdivisions and
constants are all chosen before the field.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A scale-independent local forward comparison implies a uniform
comparison at any two strictly ordered times on a compact interior set. -/
theorem exists_forward_comparison_constant_of_ballChain
    {U K : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {ℓ T L ρ κ A s t : ℝ}
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hκ : 0 < κ) (hA : 0 < A)
    (hs : ℓ < s) (hst : s < t) (ht : t ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ → ℝ,
      (∀ p ∈ U ×ˢ Ioc ℓ T, 0 ≤ u p.1 p.2) →
      (∀ (x y : E) (r a : ℝ), 0 < r → r ≤ ρ →
        closedBall x (L * r) ⊆ U → dist x y ≤ r → ℓ < a - 2 * r ^ 2 →
        a + κ * r ^ 2 ≤ T → u x a ≤ A * u y (a + κ * r ^ 2)) →
      ∀ x ∈ K, ∀ y ∈ K, u x s ≤ C * u y t := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · exact ⟨1, zero_lt_one, by simp⟩
  let base : U := ⟨b, hKU hb⟩
  let m := (s + t) / 2
  let a := (s + m) / 2
  let d := (m + t) / 2
  obtain ⟨hsm, hmt, hsa, ham, hmd, hdt⟩ :
      s < m ∧ m < t ∧ s < a ∧ a < m ∧ m < d ∧ d < t := by
    dsimp only [m, a, d]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  let admissible (u : E → ℝ → ℝ) : Prop :=
    ∀ (x y : E) (r v : ℝ), 0 < r → r ≤ ρ →
      closedBall x (L * r) ⊆ U → dist x y ≤ r → ℓ < v - 2 * r ^ 2 →
      v + κ * r ^ 2 ≤ T → u x v ≤ A * u y (v + κ * r ^ 2)
  have hradius (q : U) :
      ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧ closedBall q.1 ((L + 2) * R) ⊆ U := by
    simpa only [add_assoc, one_add_one_eq_two] using
      exists_ballChain_radius hU (by positivity : 0 ≤ L + 1) hρ q
  choose radius hr hcap hball using hradius
  have hleft (q : U) : ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ → ℝ,
      admissible u → ∀ z ∈ ball q.1 (radius q), u z s ≤ C * u b m := by
    obtain ⟨C, hC, hsegment⟩ := exists_forward_comparison_on_segment (U := U)
      hL hκ hA (hr q) (hcap q) hs hsa (ham.le.trans (hmt.le.trans ht))
    obtain ⟨D, hD, hpath⟩ := exists_forward_comparison_of_isPreconnected hU hconn
      hL hρ hκ hA q base (hs.trans hsa) ham (hmt.le.trans ht)
    refine ⟨C * D, mul_pos hC hD, fun u hu z hz ↦ ?_⟩
    have hzball : closedBall z ((L + 1) * radius q) ⊆ U := fun w hw ↦ hball q <| by
      rw [mem_closedBall] at hw ⊢
      linarith [dist_triangle w z q.1, mem_ball.1 hz]
    calc
      u z s ≤ C * u q.1 a := hsegment u hu _ _ hz.le hzball
      _ ≤ C * (D * u b m) := mul_le_mul_of_nonneg_left (hpath u hu) hC.le
      _ = C * D * u b m := (mul_assoc _ _ _).symm
  have hright (q : U) : ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ → ℝ,
      admissible u → ∀ z ∈ ball q.1 (radius q), u b m ≤ C * u z t := by
    obtain ⟨C, hC, hpath⟩ := exists_forward_comparison_of_isPreconnected hU hconn
      hL hρ hκ hA base q (hs.trans hsm) hmd (hdt.le.trans ht)
    obtain ⟨D, hD, hsegment⟩ := exists_forward_comparison_on_segment (U := U)
      hL hκ hA (hr q) (hcap q) (hs.trans (hsm.trans hmd)) hdt ht
    have hqball : closedBall q.1 ((L + 1) * radius q) ⊆ U :=
      (closedBall_subset_closedBall (by linarith [hr q])).trans (hball q)
    refine ⟨C * D, mul_pos hC hD, fun u hu z hz ↦ ?_⟩
    calc
      u b m ≤ C * u q.1 d := hpath u hu
      _ ≤ C * (D * u z t) :=
        mul_le_mul_of_nonneg_left (hsegment u hu _ _ (mem_ball'.1 hz).le hqball) hC.le
      _ = C * D * u z t := (mul_assoc _ _ _).symm
  choose left hleftpos hleftcompare using hleft
  choose right hrightpos hrightcompare using hright
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun q : U ↦ ball q.1 (radius q))
    (fun _ ↦ isOpen_ball) fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hKU hz⟩, mem_ball_self (hr _)⟩
  let M := 1 + ∑ q ∈ F, (left q + right q)
  have hnonneg (q : U) : 0 ≤ left q + right q := add_nonneg (hleftpos q).le (hrightpos q).le
  have hM : 0 < M := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun q _ ↦ hnonneg q)
  have hbound (q : U) (hq : q ∈ F) : left q ≤ M ∧ right q ≤ M := by
    have := Finset.single_le_sum (fun q _ ↦ hnonneg q) hq
    have := hleftpos q
    have := hrightpos q
    dsimp only [M]
    constructor <;> linarith
  refine ⟨M ^ 2, pow_pos hM 2, fun u hu0 hu x hx y hy ↦ ?_⟩
  obtain ⟨p, hpF, hxp⟩ := mem_iUnion₂.mp (hF hx)
  obtain ⟨q, hqF, hyq⟩ := mem_iUnion₂.mp (hF hy)
  calc
    u x s ≤ left p * (right q * u y t) := (hleftcompare p u hu x hxp).trans
      (mul_le_mul_of_nonneg_left (hrightcompare q u hu y hyq) (hleftpos p).le)
    _ = left p * right q * u y t := (mul_assoc _ _ _).symm
    _ ≤ M ^ 2 * u y t := mul_le_mul_of_nonneg_right
      (sq M ▸ mul_le_mul (hbound p hpF).1 (hbound q hqF).2 (hrightpos q).le hM.le)
      (hu0 (y, t) ⟨hKU hy, hs.trans hst, ht⟩)

end PDE.Analysis
