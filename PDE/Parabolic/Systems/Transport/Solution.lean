/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Equation.SpaceTime
public import PDE.Analysis.Normed.Operator.FiniteProduct
public import PDE.Analysis.Evolution.Time.WeakDerivative.Bochner

/-!
# Strong Sobolev solutions of matrix transport and diffusion

The state belongs to L²(H³), its weak time derivative belongs to
L²(H¹), and its H¹ representative is continuous on the closed time interval.
The equation uses every matrix entry and the weak spatial coordinates.
Only the equation and regularity define a solution. The predicate contains no
energy estimate and no identity specific to a construction.

The spatial equation is stated on a common iterated exceptional set. Joint
Sobolev representatives identify it with the equation for product measure.
The finite Hilbert product is Mathlib's `PiLp 2`, also for an empty target.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n m : ℕ}

/-- A strong Sobolev solution with its weak velocity and closed H¹ trace.
The matrix field and forcing are pointwise functions on time and space. -/
structure IsStrongTransportDiffusionSolution
    (ε a b : ℝ) (B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ)
    (f : Fin m → ℝ × ℝ^n → ℝ)
    (q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
    (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
      (volume.restrict (Ioc a b)))
    (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
      (volume.restrict (Ioc a b)))
    (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) : Prop where
  continuousOn : ContinuousOn z (Icc a b)
  initial_eq : z a = q
  representative : z =ᵐ[volume.restrict (Ioc a b)] fun t ↦
    ContinuousLinearMap.piLpMap 2
      (fun _ : Fin m ↦ lowerOrderCLM (by decide : 1 ≤ 3)) (U t)
  weakTimeDerivative : HasWeakTimeDerivativeOn (Ioo a b)
    (fun t ↦ ContinuousLinearMap.piLpMap 2
      (fun _ : Fin m ↦ lowerOrderCLM (by decide : 1 ≤ 3)) (U t)) G
  equation : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
    wkpBaseCoordinateCLM (G t p) x -
      ε * (∑ j, wkpCoordinateCLM
        ((pairDerivIndex n j j).castOrder (by decide : 2 ≤ 3)) (U t p) x) +
      (∑ j, ∑ q, B j (t, x) p q * wkpCoordinateCLM
        ((singleDerivIndex n j).castOrder (by decide : 1 ≤ 3)) (U t q) x) =
      f p (t, x)

end PDE.Parabolic.Systems
