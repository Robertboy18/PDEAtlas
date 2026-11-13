/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Diagonal.Gradient.Lifespan
public import PDE.Analysis.Calculus.Jet.Pullback

/-!
# Compression excludes a global classical diagonal solution

A C² closure candidate on the forward half-space restricts to every finite
slab. Choosing the positive Riccati horizon as its terminal time contradicts the
strict finite-slab bound.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis

namespace PDE.Hyperbolic.Quasilinear.Diagonal

variable {B : Fin 2 → (Fin 2 → ℝ) → ℝ}

/-- Bounded initial data with a compressive component have no global
closure-C² solution of the genuinely nonlinear diagonal system. -/
theorem not_exists_global_of_compressive_slope (hB : ∀ i, ContDiff ℝ 1 (B i))
    (hgap : ∀ i z, B i z ≠ B i.rev z) (hpos : ∀ i z, 0 < fderiv ℝ (B i) z (Pi.single i 1))
    {g : ℝ → Fin 2 → ℝ} (hbounded : ∃ R : ℝ, ∀ x i, -R ≤ g x i ∧ g x i ≤ R) {i : Fin 2} {x₀ : ℝ}
    (hneg : deriv (fun x ↦ g x i) x₀ < 0) :
    ¬ ∃ v : ℝ × ℝ → Fin 2 → ℝ, Nonempty (ContinuousSecondJetOn v (Ioi (0 : ℝ) ×ˢ univ)) ∧
      (∀ x, v (0, x) = g x) ∧ (∀ p : ℝ × ℝ, 0 < p.1 → ∀ j, fderiv ℝ v p (1, B j (v p)) j = 0) := by
  rintro ⟨v, ⟨hv⟩, hinit, hpde⟩
  obtain ⟨R, hR⟩ := hbounded
  obtain ⟨κ, hκ, hbound⟩ := exists_uniform_lifespan_constants hB hgap hpos R
  let T := (κ i * (-deriv (fun x ↦ g x i) x₀))⁻¹
  have hT : 0 < T := inv_pos.mpr (mul_pos (hκ i) (neg_pos.mpr hneg))
  have hslab : Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) ⊆ Ioi 0 ×ˢ univ := fun _ hp ↦ ⟨hp.1.1, hp.2⟩
  exact (lt_irrefl T) (hbound g hR T hT v (hv.mono hslab) hinit
    (fun p hp j ↦ hpde p hp.1 j) i x₀ hneg)

end PDE.Hyperbolic.Quasilinear.Diagonal
