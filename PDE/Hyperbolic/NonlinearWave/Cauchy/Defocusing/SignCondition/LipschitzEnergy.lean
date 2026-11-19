/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.LipschitzPotential
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Uniqueness
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Lipschitz

/-!
# Energy waves for Lipschitz sign-preserving reactions

The scalar integral potential supplies the spatial hypotheses of the Cauchy construction. Thus every
H¹ × L² datum has an energy solution, with conserved physical energy and a full state bound growing
with time. The bound depends on the initial physical energy, not on the Lipschitz constant. For the
truncated reactions these are the solutions `uᵏ` of (4) and the energy identity (5) in steps 1-2 of
the proof of Theorem 1 of Evans, §12.3.1, which obtains `uᵏ` from Theorem 1 of §12.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.1, Theorem 1; §12.3.1, steps 1-2 of the proof
  of Theorem 1, equations (4)-(5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert InnerProductSpace Topology
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

variable {n : ℕ} {f : ℝ → ℝ} {K : NNReal}

/-- The massless physical energy: spatial gradient, velocity, and normalized
scalar potential. Its finiteness is proved before use for Lipschitz reactions. -/
def physicalEnergy (f : ℝ → ℝ) (z : H¹(ℝ^n) × DerivLp n 2 univ) : ℝ :=
  (1 / 2 : ℝ) * (gradientForm n z.1 z.1 + ‖z.2‖ ^ 2) +
    ∫ x, primitive f ((energyTriple n).inclusion z.1 x) ∂domainMeasure n univ

/-- A Lipschitz reaction satisfying the sign condition `0 ≤ z f(z)` defines a
`General.Nonlinearity` with nonnegative potential. -/
def lipschitzNonlinearity (hf : LipschitzWith K f) (hs : ∀ z, 0 ≤ z * f z) :
    General.Nonlinearity n where
  source := ⟨fun q ↦ hf.compLp (reaction_zero hf.continuous hs) ((energyTriple n).inclusion q),
    (hf.continuous_compLp (reaction_zero hf.continuous hs)).comp
      (energyTriple n).inclusion.continuous⟩
  source_lipschitzOn := fun _ _ ↦ ⟨_,
    ((hf.lipschitzWith_compLp (reaction_zero hf.continuous hs)).comp
      (energyTriple n).inclusion.lipschitzWith).lipschitzOnWith⟩
  potential := fun q ↦
    ∫ x, primitive f ((energyTriple n).inclusion q x) ∂domainMeasure n univ
  potential_nonneg := fun _ ↦ integral_nonneg fun _ ↦ primitive_nonneg hf.continuous hs _
  hasFDerivAt_potential := fun q ↦ hasFDerivAt_integral_lipschitz_potential
    (energyTriple n).inclusion hf (reaction_zero hf.continuous hs) q

/-- The energy of `lipschitzNonlinearity` is the physical energy. -/
@[simp] theorem energy_lipschitzNonlinearity (hf : LipschitzWith K f)
    (hs : ∀ z, 0 ≤ z * f z) (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    (lipschitzNonlinearity hf hs).energy z = physicalEnergy f z := rfl

/-- The equation of `lipschitzNonlinearity` is the scalar Cauchy equation;
its predicate includes continuity, both data, and both integrated PDE identities. -/
theorem isEnergySolution_lipschitzNonlinearity_iff (hf : LipschitzWith K f) (hs : ∀ z, 0 ≤ z * f z)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) (u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ) :
    (lipschitzNonlinearity hf hs).IsEnergySolution x u ↔
      Cauchy.IsEnergySolution hf (reaction_zero hf.continuous hs) x u := by
  constructor
  · exact fun h ↦ ⟨h.continuous, h.initial, h.displacement, h.velocity⟩
  · exact fun h ↦ ⟨h.continuous, h.initial, h.displacement, h.velocity⟩

/-- Global PDE solutions with conserved physical energy and finite-time
H¹ × L² bounds. The displacement has no asserted uniform bound for all time. -/
theorem exists_energySolution_of_lipschitz (hf : LipschitzWith K f)
    (hs : ∀ z, 0 ≤ z * f z) (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      Cauchy.IsEnergySolution hf (reaction_zero hf.continuous hs) x u ∧
      Filter.Tendsto u (𝓝[≥] (0 : ℝ)) (𝓝 x) ∧
      (∀ t : ℝ, 0 ≤ t → physicalEnergy f (u t) = physicalEnergy f x) ∧
      (∀ t : ℝ, 0 ≤ t →
        gradientForm n (u t).1 (u t).1 + ‖(u t).2‖ ^ 2 ≤ 2 * physicalEnergy f x) ∧
      (∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤
        ‖(energyTriple n).inclusion x.1‖ + (t + 1) * Real.sqrt (2 * physicalEnergy f x)) ∧
      ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ,
        Cauchy.IsEnergySolution hf (reaction_zero hf.continuous hs) x v →
          EqOn u v (Ici 0) := by
  let N := lipschitzNonlinearity (n := n) hf hs
  have hu := N.globalSolution_isEnergySolution x
  have hscalar := (isEnergySolution_lipschitzNonlinearity_iff hf hs x _).mp hu
  refine ⟨N.globalSolution x, hscalar, hu.tendsto_initial, ?_, ?_, ?_, ?_⟩
  · exact fun t ht ↦ N.energy_globalSolution x ht
  · intro t ht
    have h := N.gradient_velocity_le_energy (N.globalSolution x t)
    rwa [N.energy_globalSolution x ht] at h
  · exact fun t ht ↦ N.norm_globalSolution_le x ht
  · exact fun v hv ↦ hscalar.eqOn hv

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
