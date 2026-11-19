/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.BallChain
public import PDE.Elliptic.Classical.Harnack.Local.SignedPotential

/-!
# Compact propagation of the variable-coefficient Harnack comparison

The local estimate is combined with the shared interior-ball chain.
All radii, paths and constants are selected before the solution.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Uniform comparison on a compact subset of a connected open domain,
with bounded drift and an arbitrary signed bounded potential. -/
theorem exists_harnack_comparison_on_isCompact
    {U S : Set (ℝ^n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    {α τ B K : ℝ} (hα : 0 < α) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ),
      (∀ x ∈ U, (a x).PosSemidef) →
      (∀ x ∈ U, ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
      (∀ x ∈ U, (a x).trace ≤ τ) →
      (∀ x ∈ U, ‖b x‖ ≤ B) → (∀ x ∈ U, |c x| ≤ K) →
      ∀ u : ℝ^n → ℝ, (∀ x ∈ U, ContDiffAt ℝ 2 u x) →
      (∀ x ∈ U, 0 ≤ u x) → (∀ x ∈ U, matrixOperator a b c u x = 0) →
      ∀ x ∈ S, ∀ y ∈ S, u x ≤ C * u y := by
  obtain ⟨A, hA, hlocal⟩ := exists_signed_harnack_comparison (n := n) hα hB hK
  obtain ⟨C, hC, hchain⟩ := exists_comparison_constant_of_ballChain hU hconn hS hSU
    (L := 32 * ((n : ℝ) + 2)) (ρ := 1 / 2) (A := A)
    (by positivity) (by norm_num) hA
  refine ⟨C, hC, ?_⟩
  intro a b c ha hell htrace hdrift hpotential u hreg hnonneg hsol
  apply hchain u hnonneg
  intro x y hxy
  obtain ⟨r, hr, hr₁, hdist, _, hyball⟩ := hxy
  have hball : ball y.1 ((2 * r) * (16 * ((n : ℝ) + 2))) ⊆ U := by
    have heq : (2 * r) * (16 * ((n : ℝ) + 2)) = (32 * ((n : ℝ) + 2)) * r := by
      ring
    rw [heq]
    exact ball_subset_closedBall.trans hyball
  apply hlocal a b c y.1 (2 * r) (by positivity) (by linarith)
    (fun z hz ↦ ha z (hball hz)) (fun z hz ↦ hell z (hball hz))
    (fun z hz ↦ htrace z (hball hz)) (fun z hz ↦ hdrift z (hball hz))
    (fun z hz ↦ hpotential z (hball hz)) u
    (fun z hz ↦ hreg z (hball hz)) (fun z hz ↦ hnonneg z (hball hz))
    (fun z hz ↦ hsol z (hball hz))
  · simpa only [mem_closedBall, mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)]
      using hdist
  · exact mem_closedBall_self (by positivity)

/-- The comparison set may be connected while the ambient open set is disconnected.
Its compact closure lies in one open connected component. -/
theorem exists_harnack_comparison_on_closure
    {U V : Set (ℝ^n)} (hU : IsOpen U) (hV : IsPreconnected V)
    (hcompact : IsCompact (closure V)) (hVU : closure V ⊆ U)
    {α τ B K : ℝ} (hα : 0 < α) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ),
      (∀ x ∈ U, (a x).PosSemidef) →
      (∀ x ∈ U, ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
      (∀ x ∈ U, (a x).trace ≤ τ) →
      (∀ x ∈ U, ‖b x‖ ≤ B) → (∀ x ∈ U, |c x| ≤ K) →
      ∀ u : ℝ^n → ℝ, (∀ x ∈ U, ContDiffAt ℝ 2 u x) →
      (∀ x ∈ U, 0 ≤ u x) → (∀ x ∈ U, matrixOperator a b c u x = 0) →
      ∀ x ∈ closure V, ∀ y ∈ closure V, u x ≤ C * u y := by
  rcases (closure V).eq_empty_or_nonempty with hempty | ⟨z, hz⟩
  · exact ⟨1, zero_lt_one, by simp [hempty]⟩
  let W := connectedComponentIn U z
  have hWU : W ⊆ U := connectedComponentIn_subset _ _
  have hVW : closure V ⊆ W := hV.closure.subset_connectedComponentIn hz hVU
  obtain ⟨C, hC, hcompare⟩ := exists_harnack_comparison_on_isCompact
    (U := W) hU.connectedComponentIn isPreconnected_connectedComponentIn
    hcompact hVW hα hB hK
  refine ⟨C, hC, ?_⟩
  intro a b c ha hell htrace hdrift hpotential u hreg hnonneg hsol
  exact hcompare a b c (fun x hx ↦ ha x (hWU hx)) (fun x hx ↦ hell x (hWU hx))
    (fun x hx ↦ htrace x (hWU hx)) (fun x hx ↦ hdrift x (hWU hx))
    (fun x hx ↦ hpotential x (hWU hx)) u (fun x hx ↦ hreg x (hWU hx))
    (fun x hx ↦ hnonneg x (hWU hx)) (fun x hx ↦ hsol x (hWU hx))

end EllipticHarnack
