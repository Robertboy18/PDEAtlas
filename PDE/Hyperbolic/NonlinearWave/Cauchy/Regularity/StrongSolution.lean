/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongEvolution

/-!
# Global strong energy solutions for H² × H¹ data

The global energy solution has a continuous derivative in H¹ × L² when the
initial displacement is H², the initial velocity is H¹, and the nonlinearity
is globally Lipschitz and C¹ with `f(0) = 0`. The derivative is constructed
from the data. Its initial value is `(v₀, Δu₀ - f(u₀))`, and its acceleration
satisfies the weak spatial equation at every nonnegative time.

The displacement is C² in time with values in L² on positive times, with the
appropriate right derivative at the initial endpoint. These conclusions require
neither bounded higher derivatives of `f` nor a bound on the solution's values.
They do not give a pointwise classical spatial solution in arbitrary dimension.
Higher spatial propagation and spatial embeddings are further steps.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert InnerProductSpace Laplacian ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution

variable {n : ℕ} {f : ℝ → ℝ} {L : NNReal}

/-- A global energy solution together with its continuous strong time derivative.
The first derivative component lifts velocity to H¹; the second is L² acceleration. -/
structure IsStrongEnergySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (u d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)) : Prop
    extends IsEnergySolution hf hf0 x u where
  right_derivative : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (d t) (Ici t) t
  derivative : ∀ t : ℝ, 0 < t → HasDerivAt u (d t) t
  inclusion_velocity : ∀ t : ℝ, 0 ≤ t → (energyTriple n).inclusion (d t).1 = (u t).2
  acceleration_eq : ∀ t : ℝ, 0 ≤ t →
    (energyTriple n).pivotToDual (d t).2 = acceleration hf hf0 (u t).1

/-- On H² displacement the weak acceleration is represented by `Δu - f(u)` in L². -/
theorem acceleration_h2 (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (u : W^{2,2}(ℝ^n)) :
    acceleration hf hf0 (lowerOrderCLM (by decide : 1 ≤ 2) u) =
      (energyTriple n).pivotToDual (Δ u - hf.compLp hf0 (wkpBaseCoordinateCLM u)) := by
  rw [← source_sub_massForm, massForm_h2, ← map_sub]
  congr 1
  change (wkpBaseCoordinateCLM u - hf.compLp hf0 (wkpBaseCoordinateCLM u)) -
    (wkpBaseCoordinateCLM u - Δ u) = _
  abel

/-- The strong derivative has the expected initial velocity and nonlinear acceleration. -/
theorem IsStrongEnergySolution.initial_derivative
    {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {u₀ : W^{2,2}(ℝ^n)} {v₀ : H¹(ℝ^n)}
    {u d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsStrongEnergySolution hf hf0
      (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀) u d) :
    d 0 = (v₀, Δ u₀ - hf.compLp hf0 (wkpBaseCoordinateCLM u₀)) := by
  apply Prod.ext
  · apply (energyTriple n).injective
    rw [h.inclusion_velocity 0 le_rfl, h.initial]
  · apply (energyTriple n).pivotToDual_injective
    rw [h.acceleration_eq 0 le_rfl, h.initial, acceleration_h2]

variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}
  {x : H¹(ℝ^n) × DerivLp n 2 univ}
  {u d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- L² acceleration satisfies the weak spatial PDE at every nonnegative time,
without integration in time or an assumed residual. -/
theorem IsStrongEnergySolution.pde
    (h : IsStrongEnergySolution hf hf0 x u d) {t : ℝ} (ht : 0 ≤ t) (w : H¹(ℝ^n)) :
    ⟪(d t).2, (energyTriple n).inclusion w⟫_ℝ + (∑ i : Fin n, ⟪(u t).1.val (singleDerivIndex n i),
      w.val (singleDerivIndex n i)⟫_ℝ) + ⟪hf.compLp hf0 ((energyTriple n).inclusion (u t).1),
      (energyTriple n).inclusion w⟫_ℝ = 0 := by
  have heq := congrArg (fun a : StrongDual ℝ H¹(ℝ^n) ↦ a w) (h.acceleration_eq t ht)
  rw [GelfandTriple.pivotToDual_apply, acceleration_apply] at heq
  rw [heq]
  abel

/-- A strong energy solution is C¹ as an energy-space curve on positive times. -/
theorem IsStrongEnergySolution.contDiffOn (h : IsStrongEnergySolution hf hf0 x u d) :
    ContDiffOn ℝ 1 u (Ioi 0) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun t ht ↦ (h.derivative t ht).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  exact d.continuous.continuousOn.congr fun t ht ↦ (h.derivative t ht).deriv

/-- The strong displacement has two continuous time derivatives in L².
The second derivative is the constructed acceleration. -/
theorem IsStrongEnergySolution.contDiffOn_displacement_two
    (h : IsStrongEnergySolution hf hf0 x u d) :
    ContDiffOn ℝ 2 (fun t ↦ (energyTriple n).inclusion (u t).1) (Ioi 0) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun t ht ↦ (h.hasDerivAt_displacement ht).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  exact h.contDiffOn.snd.congr fun t ht ↦ (h.hasDerivAt_displacement ht).deriv

/-- H² × H¹ data give a forward global strong energy solution for every C¹
globally Lipschitz scalar nonlinearity fixing zero. Uniqueness holds even among
the larger class of all energy solutions. -/
theorem exists_unique_strongEnergySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hreg : ContDiff ℝ 1 f) (u₀ : W^{2,2}(ℝ^n)) (v₀ : H¹(ℝ^n)) :
    ∃ u d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      IsStrongEnergySolution hf hf0
        (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀) u d ∧
      ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ,
        IsEnergySolution hf hf0
          (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀) v →
            EqOn u v (Ici 0) := by
  obtain ⟨u, hu, huniq⟩ := exists_unique_energySolution hf hf0
    (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀)
  obtain ⟨d, hright, hderiv, hvelocity, hacc⟩ := hu.exists_continuous_derivative hreg u₀ v₀
  exact ⟨u, d, ⟨hu, hright, hderiv, hvelocity, hacc⟩, huniq⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
