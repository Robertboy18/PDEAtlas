/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.LinearEnergy

/-!
# Nonnegative potentials on the whole-space wave energy space

A continuous L² source with Lipschitz bounds on H¹ balls and a nonnegative
pivot potential supplies a massless wave nonlinearity. These are spatial
properties. The mass-canceling force uses the whole-space semigroup.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General

open PDE.Analysis.Evolution Hyperbolic.Variational

/-- Spatial data for a massless wave with a nonnegative potential. -/
structure Nonlinearity (n : ℕ) where
  /-- The spatial source, defined on every H¹ displacement. -/
  source : C(H¹(ℝ^n), DerivLp n 2 univ)
  /-- A derived bound on each whole H¹ ball, sufficient for uniform local existence. -/
  source_lipschitzOn : ∀ R : ℝ, 0 < R →
    ∃ L : NNReal, LipschitzOnWith L source (Metric.closedBall 0 R)
  /-- The finite potential functional on the energy displacement space. -/
  potential : H¹(ℝ^n) → ℝ
  /-- The sign used to control gradient and velocity energy. -/
  potential_nonneg : ∀ q, 0 ≤ potential q
  /-- The source is the L² pivot gradient of the potential. -/
  hasFDerivAt_potential : ∀ q,
    HasFDerivAt potential ((innerSL ℝ (source q)).comp (energyTriple n).inclusion) q

namespace Nonlinearity

variable {n : ℕ} (N : Nonlinearity n)

/-- The L² force cancels the auxiliary mass and subtracts the defocusing source. -/
def force : C(H¹(ℝ^n) × DerivLp n 2 univ, DerivLp n 2 univ) :=
  ⟨fun z ↦ (energyTriple n).inclusion z.1 - N.source z.1,
    ((energyTriple n).inclusion.continuous.comp continuous_fst).sub
      (N.source.continuous.comp continuous_fst)⟩

/-- The first-order vector field paired with the constructed massive wave semigroup. -/
def vectorField : C(H¹(ℝ^n) × DerivLp n 2 univ, H¹(ℝ^n) × DerivLp n 2 univ) :=
  (ContinuousMap.const _ (0 : H¹(ℝ^n))).prodMk N.force

/-- The spatial source bounds give Lipschitz bounds on full state balls. -/
theorem vectorField_lipschitzOn_closedBall (R : ℝ) (hR : 0 < R) :
    ∃ L : NNReal, LipschitzOnWith L N.vectorField (Metric.closedBall 0 R) := by
  obtain ⟨L, hL⟩ := N.source_lipschitzOn R hR
  have hf := (energyTriple n).inclusion.lipschitzWith.lipschitzOnWith.sub hL
  have hmaps : MapsTo (Prod.fst : H¹(ℝ^n) × DerivLp n 2 univ → H¹(ℝ^n))
      (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact (norm_fst_le z).trans hz
  exact ⟨_, (LipschitzWith.const (0 : H¹(ℝ^n))).lipschitzOnWith.prodMk
    (hf.comp LipschitzWith.prod_fst.lipschitzOnWith hmaps)⟩

/-- Local Picard theory applies to every source in this spatial class. -/
theorem locallyLipschitz_vectorField : LocallyLipschitz N.vectorField :=
  StronglyContinuousSemigroup.locallyLipschitz_of_lipschitzOn_closedBall_zero
    N.vectorField_lipschitzOn_closedBall

/-- The potential of the mass-canceling force. -/
def forcePotential (q : H¹(ℝ^n)) : ℝ :=
  (1 / 2 : ℝ) * ‖(energyTriple n).inclusion q‖ ^ 2 - N.potential q

/-- The mass-canceling force is the pivot gradient of its potential. -/
theorem hasFDerivAt_forcePotential (q : H¹(ℝ^n)) (v : DerivLp n 2 univ) :
    HasFDerivAt N.forcePotential ((innerSL ℝ (N.force (q, v))).comp
      (energyTriple n).inclusion) q := by
  have h := (((energyTriple n).inclusion.hasFDerivAt.norm_sq).const_mul
    (1 / 2 : ℝ)).sub (N.hasFDerivAt_potential q)
  convert h using 1
  · rfl
  · ext w
    simp only [ContinuousLinearMap.comp_apply, sub_apply, smul_apply, innerSL_apply_apply,
      smul_eq_mul]
    simp [force, inner_sub_left]

/-- The physical massless energy on the full state space. -/
def energy (z : H¹(ℝ^n) × DerivLp n 2 univ) : ℝ :=
  (1 / 2 : ℝ) * (gradientForm n z.1 z.1 + ‖z.2‖ ^ 2) + N.potential z.1

/-- The auxiliary quadratic mass cancels from the conserved energy. -/
theorem energy_eq_quadratic_sub_potential (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    N.energy z = (1 / 2 : ℝ) * autonomousWaveEnergy (massForm n) z - N.forcePotential z.1 := by
  change 1 / 2 * (massForm n z.1 z.1 -
      ⟪(energyTriple n).inclusion z.1, (energyTriple n).inclusion z.1⟫_ℝ + ‖z.2‖ ^ 2) +
      N.potential z.1 = 1 / 2 * (massForm n z.1 z.1 + ‖z.2‖ ^ 2) -
      (1 / 2 * ‖(energyTriple n).inclusion z.1‖ ^ 2 - N.potential z.1)
  rw [real_inner_self_eq_norm_sq]
  ring

/-- Every finite mild solution conserves the physical energy; conservation is derived. -/
theorem energy_of_mildSolutionOn {x : H¹(ℝ^n) × DerivLp n 2 univ} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : (productSemigroup n).IsMildSolutionOn N.vectorField x τ u) (t : Icc (0 : ℝ) (τ : ℝ)) :
    N.energy (u t) = N.energy x := by
  simpa only [N.energy_eq_quadratic_sub_potential] using
    potential_energy_of_mildSolutionOn (productSemigroup n) (massForm n)
      massForm_symmetric productSemigroup_energy (energyTriple n).inclusion
      (fun f hf x t ht ↦ (productSemigroup_forced_integral hf x ht).1)
      N.force N.forcePotential N.hasFDerivAt_forcePotential hu t

end Nonlinearity
end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General
