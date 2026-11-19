/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Global

/-!
# Uniqueness from the integrated wave equation

Uniqueness for the linear energy equation identifies every trajectory continuous
in the energy norm with its variation-of-constants formula (`IsEnergySolutionOn.mild_eq`;
`IsEnergySolution.isMildSolutionOn` states it for `productSemigroup` in product coordinates).
Local source uniqueness then identifies it with the global constructor. The competing class
requires only the PDE, continuity, and initial data; conservation and bounds follow as
conclusions.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity

variable {n : ℕ} {N : Nonlinearity n}

open PDE.Analysis.Evolution

/-- A continuous energy trajectory restricted to a finite interval in product coordinates. -/
def solutionTrace (u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)) (τ : NNReal) :
    C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^n) × DerivLp n 2 univ) :=
  ⟨fun t ↦ u t, u.continuous.comp continuous_subtype_val⟩

/-- The integrated PDE implies the constructed mild equation in product coordinates: a forward
energy solution is a mild solution of `N.vectorField` for `productSemigroup n` on every positive
finite interval. This is `IsEnergySolutionOn.mild_eq` for the force `N.force`, carried from
`linearSemigroup n` to `productSemigroup n` by `productSemigroup_forced`. -/
theorem IsEnergySolution.isMildSolutionOn {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (h : N.IsEnergySolution x u) {τ : NNReal}
    (hτ : 0 < (τ : ℝ)) :
    (productSemigroup n).IsMildSolutionOn N.vectorField x τ (solutionTrace u τ) := by
  intro t
  have hf : Continuous fun s ↦ N.force (u s) := N.force.continuous.comp u.continuous
  have heq : u t = coordinates n ((linearSemigroup n).realOrbit ((coordinates n).symm x) t +
      (linearSemigroup n).duhamel (fun s ↦ (coordinates n).symm (0, N.force (u s))) t) :=
    (coordinates n).symm_apply_eq.mp (IsEnergySolutionOn.mild_eq (h.mono Icc_subset_Ici_self)
      N.force.continuous N.force_sub_massForm hτ t.property)
  rw [← productSemigroup_forced hf x t] at heq
  change (solutionTrace u τ) t = (productSemigroup n) (t : ℝ).toNNReal x +
    (productSemigroup n).duhamel (fun s ↦ (0, N.force (u s))) t at heq
  rw [heq]
  congr 1
  refine (productSemigroup n).duhamel_congr t.property.1 fun s hs ↦ ?_
  change (0, N.force (u s)) = N.vectorField (IccExtend τ.coe_nonneg (solutionTrace u τ) s)
  rw [IccExtend_of_mem τ.coe_nonneg (solutionTrace u τ) ⟨hs.1, hs.2.trans t.property.2⟩]
  rfl

/-- All forward energy solutions with the same data agree at every forward time. This is
`IsEnergySolutionOn.eqOn_Ici` for the locally Lipschitz vector field `N.vectorField`, written in
the coordinates of `EnergyState n`. -/
theorem IsEnergySolution.eqOn
    {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hu : N.IsEnergySolution x u) (hv : N.IsEnergySolution x v) : EqOn u v (Ici 0) := by
  let G : C(EnergyState n, EnergyState n) :=
    ⟨fun z ↦ (coordinates n).symm (N.vectorField (coordinates n z)),
      (coordinates n).symm.continuous.comp
        (N.vectorField.continuous.comp (coordinates n).continuous)⟩
  have hGL : LocallyLipschitz G :=
    (coordinates n).symm.toContinuousLinearMap.lipschitzWith.locallyLipschitz.comp
      (N.locallyLipschitz_vectorField.comp
        (coordinates n).toContinuousLinearMap.lipschitzWith.locallyLipschitz)
  exact IsEnergySolutionOn.eqOn_Ici (G := G) hu hv N.force.continuous N.force_sub_massForm
    (fun _ ↦ rfl) hGL

/-- Conservation follows for every competing energy solution. -/
theorem IsEnergySolution.energy_eq
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hu : N.IsEnergySolution x u) {t : ℝ} (ht : 0 ≤ t) : N.energy (u t) = N.energy x := by
  rw [hu.eqOn (N.globalSolution_isEnergySolution x) ht]
  exact N.energy_globalSolution x ht

/-- Global existence, physical energy conservation, and uniqueness among all
energy solutions of `uₜₜ − Δu + N(u) = 0` on ℝⁿ, for arbitrary H¹ × L² data. -/
theorem exists_unique_energySolution (N : Nonlinearity n) (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), N.IsEnergySolution x u ∧
      (∀ t : ℝ, 0 ≤ t → N.energy (u t) = N.energy x) ∧ ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ,
      N.IsEnergySolution x v → EqOn u v (Ici 0) :=
  ⟨N.globalSolution x, N.globalSolution_isEnergySolution x, fun _ ht ↦ N.energy_globalSolution x ht,
    fun _ hv ↦ (N.globalSolution_isEnergySolution x).eqOn hv⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity
