/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.DenseGrowth
import CAS.ExactTactic

/-!
# Growth from a dense child to its forward parent

The contact estimate turns a dense superlevel in an early box into a lower
bound on a later ball. Stationary barrier comparison retains a uniform
fraction of that bound throughout the forward extension of the parent.
The extension length is chosen so that its covering factor, multiplied by
the density threshold, is strictly less than one.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum BoxIntegral Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- Choose the time lag and extension length so that the delay is one squared
spatial radius and the density times the forward-cover factor is below one. -/
theorem exists_forward_parameters {δ ε : ℝ}
    (hδ₁ : δ < 1) (hε : 0 < ε) :
    ∃ lag m H : ℝ, ∃ _ : 0 < m,
      0 ≤ lag ∧ lag * (4 * ε) = 1 ∧
      δ * (1 + (lag + 1) / m) < 1 ∧ H = 4 * ε * (1 + lag + m) ∧ 0 < H := by
  let lag := 1 / (4 * ε)
  have hlag : 0 ≤ lag := by dsimp only [lag]; positivity
  have hlagtime : lag * (4 * ε) = 1 := by dsimp only [lag]; cas using hε.ne'
  let m := (lag + 1) / (1 - δ) + 1
  have hm : 0 < m := by dsimp only [m]; positivity
  have hmprod : (1 - δ) * m = (lag + 1) + (1 - δ) := by
    dsimp only [m]
    cas using (sub_pos.mpr hδ₁).ne'
  have hfactor : δ * (1 + (lag + 1) / m) < 1 := by
    have hδlag : δ * (lag + 1) ≤ lag + 1 :=
      mul_le_of_le_one_left (by positivity) hδ₁.le
    have hratio : δ * (lag + 1) / m < 1 - δ :=
      (div_lt_iff₀ hm).mpr (by linarith)
    calc
      _ = δ + δ * (lag + 1) / m := by cas
      _ < δ + (1 - δ) := add_lt_add_right hratio _
      _ = 1 := by cas
  refine ⟨lag, m, 4 * ε * (1 + lag + m), hm, hlag, hlagtime, hfactor, rfl, ?_⟩
  positivity

/-- A dense anisotropic child forces the whole forward extension of its parent
above a lower level. Every geometric and level constant depends only on the
dimension, ellipticity, trace bound, and drift bound. -/
theorem exists_forward_box_growth
    {α τ B : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) :
    ∃ M δ ε lag m H : ℝ, ∃ hm : 0 < m,
      2 ≤ M ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ 0 ≤ lag ∧
      δ * (1 + (lag + 1) / m) < 1 ∧ 0 < H ∧
      ∀ (J K : Box (Fin (n + 1))) (j : Fin (n + 1)),
        K ∈ Prepartition.splitCenterTwiceAt J j →
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          (∀ i, (K.face j).upper i - (K.face j).lower i = 2 * r) →
          K.upper j - K.lower j = ε * r ^ 2 →
          ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
            let R := 16 * ((n : ℝ) + 1)
            let z := euclideanBoxCenter (K.face j)
            let s := K.lower j
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)),
              (a p.1 p.2).PosSemidef) →
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)), ∀ v : ℝ^n,
              α * ‖v‖ ^ 2 ≤ ⟪v, (a p.1 p.2).toEuclideanLin v⟫) →
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)),
              (a p.1 p.2).trace ≤ τ) →
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)), ‖d p.1 p.2‖ ≤ B) →
            ∀ (u : ℝ^n → ℝ → ℝ) (ℓ : ℝ), 0 < ℓ →
              (∀ p ∈ closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * (1 + H)),
                ContDiffAt ℝ 2 (Function.uncurry u) p) →
              (∀ p ∈ closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * (1 + H)),
                0 ≤ u p.1 p.2) →
              (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)),
                0 ≤ matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2) →
              δ * volume.real (K : Set (Fin (n + 1) → ℝ)) <
                (volume.restrict {x : Fin (n + 1) → ℝ |
                  M * ℓ < u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)}).real K →
              ∀ x ∈ J.forwardExtension j lag m hm,
                ℓ < u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j) := by
  let R := 16 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hR : 0 < R := by dsimp only [R]; positivity
  have hshort : (1 : ℝ) < R ^ 2 / 8 := by dsimp only [R]; nlinarith
  obtain ⟨δ, ε, hδ, hδ₁, hε, hεquarter, hpersistent⟩ :=
    exists_box_persistent_growth (n := n) (by dsimp only [R]; nlinarith)
      hα hτ hB hshort
  obtain ⟨lag, m, H, hm, hlag, hlagtime, hfactor, hHdef, hH⟩ :=
    exists_forward_parameters hδ₁ hε
  obtain ⟨M, hM, hgrowth⟩ := hpersistent H hH
  refine ⟨M, δ, ε, lag, m, H, hm, hM, hδ, hδ₁, hε, hεquarter, hlag,
    hfactor, hH, ?_⟩
  intro J K j hK r hr hr₁ hside htime a d
  dsimp only
  intro ha hell htrace hdrift u ℓ hℓ hreg hnonneg hsuper hdense x hx
  have hxcyl := forwardExtension_subset_child_cylinder j hK hr.le hm
    hside htime hlagtime hHdef hx
  have hxball : WithLp.toLp 2 (fun i ↦ x (j.succAbove i)) ∈
      closedBall (euclideanBoxCenter (K.face j)) (r * (R / 2) / 2) := by
    convert hxcyl.1 using 1
    dsimp only [R]
    clear * - r n
    cas
  exact hgrowth K j r hr hr₁ hside htime a d ha hell htrace hdrift
    u ℓ hℓ hreg hnonneg hsuper hdense (x j) hxcyl.2 _ hxball

end ParabolicHarnack
