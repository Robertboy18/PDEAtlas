/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Form.Orbit
public import PDE.Analysis.Evolution.Semigroup.JointContinuity
public import PDE.Parabolic.Evolution.Semigroup.DirichletGenerator

/-!
# Construction of the `L²` Dirichlet heat semigroup

Hille-Yosida applied to the variational Dirichlet resolvents constructs a strongly continuous
contraction semigroup on `L²(Ω)` for every open set `Ω` (`semigroup`, `semigroup_isContraction`).
Its generator is the weak Dirichlet Laplacian, with equal domains (`generatorPMap_semigroup`).

Every `L²` datum is attained strongly at time zero, jointly in time and the datum
(`tendsto_semigroup_initial`). For initial data in the generator domain, the trajectory has a
continuous `H¹₀` representative (`solution`, `continuous_solution`) and, at every positive time, a
strong `L²` time derivative (`hasDerivAt_solution`). This derivative satisfies
`⟪uₜ,v⟫ + ∑ᵢ ⟪∂ᵢu,∂ᵢv⟫ = 0` for every `v ∈ H¹₀` (`solution_weak_heat_equation`), and hence the
distributional weak equation (`solution_isWeakPoissonSolution`).

For `L = -Δ` this is Evans's §7.4.3(a), Theorem 5. Evans assumes a bounded open set with smooth
boundary and takes `D(A) = H¹₀(U) ∩ H²(U)`, (25); we allow any open set and use the weak domain
(`mem_semigroup_generator_domain_iff`). Invariance of the domain, the `C¹` orbit and the time
derivative are Evans's §7.4.1, Theorem 1 and the remark after its proof (`semigroup_mem_domain`,
`contDiffOn_semigroup`, `hasDerivAt_solution`).

## How it works

Evans checks the hypotheses of the Hille-Yosida theorem for `A = -L` one at a time: the domain is
dense, `A` is closed by the `H²` estimate of §6.3.2, Theorem 4, `λ - A` is onto for `λ ≥ γ` by
§6.2.2, Theorem 3 and elliptic regularity, and testing the weak equation with `v = u` gives the
resolvent bound (32). We use no elliptic regularity. The generator is the form operator of
`dirichletForm` on the Gelfand triple `h10L2GelfandTriple`, its resolvent is the modified Helmholtz
solver, and `dirichletForm u u ≥ 0` gives the bound `1 / λ` (`hasContractionResolvent_generator`).
The construction `formSemigroup` needs only this resolvent condition and density, so the closedness
of the weak Laplacian is a consequence of generation, as in Evans's §7.4.1, Theorem 2(ii), and not
an input (`isClosed_generator`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.2, Theorem 3 (First Existence Theorem for weak
  solutions), p. 319; §6.3.2, Theorem 4 (Boundary H²-regularity), p. 334; §7.4.1, (4)-(7),
  pp. 434-435, Theorem 1 (Differential properties of semigroups) and the remark after its proof,
  pp. 435-436, and Theorem 2 (Properties of generators), p. 436; §7.4.2, Theorem 4 (Hille-Yosida
  Theorem), p. 439; §7.4.3(a), (24)-(32) and Theorem 5 (Second-order parabolic PDE as semigroups)
  and its proof, pp. 441-443.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace HeatEquation.Semigroup.Dirichlet

open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open Filter Set
open scoped Topology InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω)

local notation "L2" => DerivLp n 2 Ω

/-- The Dirichlet heat semigroup constructed from the variational resolvents. -/
def semigroup : StronglyContinuousSemigroup L2 :=
  (h10L2GelfandTriple hΩopen).formSemigroup dirichletForm dirichletForm_self_nonneg
    (isCoercive_dirichletForm_add_energyToDual hΩopen)

/-- The heat semigroup is contractive in the `L²` norm. -/
theorem semigroup_isContraction :
    (semigroup hΩopen).IsContraction :=
  (h10L2GelfandTriple hΩopen).formSemigroup_isContraction dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen)

/-- The heat semigroup's full generator is the constructed weak Dirichlet Laplacian. -/
theorem generatorPMap_semigroup :
    (semigroup hΩopen).generatorPMap = generator hΩopen :=
  (h10L2GelfandTriple hΩopen).generatorPMap_formSemigroup dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen)

/-- The weak Dirichlet Laplacian is closed in `L²`. -/
theorem isClosed_generator :
    (generator hΩopen).IsClosed := by
  rw [← generatorPMap_semigroup]
  exact (semigroup hΩopen).isClosed_generatorPMap

/-- The generator domain consists of the `H¹₀` functions whose distributional Laplacian
is in `L²`. -/
theorem mem_semigroup_generator_domain_iff (g : L2) :
    g ∈ (semigroup hΩopen).generatorPMap.domain ↔
      ∃ u : H¹₀(Ω), baseCoordCLM u = g ∧ ∃ f : L2, IsWeakPoissonSolution f u := by
  rw [generatorPMap_semigroup, mem_generator_domain_iff]

/-- Heat orbits preserve the weak Dirichlet Laplacian domain. -/
theorem semigroup_mem_domain (g : (generator hΩopen).domain) (t : NNReal) :
    semigroup hΩopen t g ∈ (generator hΩopen).domain :=
  (h10L2GelfandTriple hΩopen).formSemigroup_mem_domain dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen) g t

/-- Initial data in the generator domain produce `C¹` pivot-space orbits for positive time. -/
theorem contDiffOn_semigroup (g : (generator hΩopen).domain) :
    ContDiffOn ℝ 1 ((semigroup hΩopen).realOrbit g) (Ioi 0) := by
  let g' : (semigroup hΩopen).generatorPMap.domain :=
    ⟨g, by rw [generatorPMap_semigroup]; exact g.property⟩
  exact (semigroup hΩopen).contDiffOn_realOrbit_generatorPMap g'

/-- The initial value limit holds jointly in nonnegative time and the `L²` datum. -/
theorem tendsto_semigroup_initial (g : L2) :
    Tendsto (fun p : NNReal × L2 ↦ semigroup hΩopen p.1 p.2)
      (𝓝 (0, g)) (𝓝 g) := by
  simpa only [StronglyContinuousSemigroup.map_zero_apply] using
    (semigroup hΩopen).continuous_apply.tendsto (0, g)

/-- The continuous zero-boundary energy representative of a heat orbit from the domain. -/
def solution (g : (generator hΩopen).domain) : ℝ → H¹₀(Ω) :=
  (h10L2GelfandTriple hΩopen).formEnergyOrbit dirichletForm dirichletForm_self_nonneg
    (isCoercive_dirichletForm_add_energyToDual hΩopen) g

/-- The energy solution and the constructed `L²` semigroup orbit agree. -/
theorem baseCoordCLM_solution (g : (generator hΩopen).domain) (t : ℝ) :
    baseCoordCLM (solution hΩopen g t) = (semigroup hΩopen).realOrbit g t :=
  ((h10L2GelfandTriple hΩopen).formEnergyOrbit_spec dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen) g t).1

/-- The heat orbit is continuous in `H¹₀` for initial data in the operator domain. -/
theorem continuous_solution (g : (generator hΩopen).domain) :
    Continuous (solution hΩopen g) :=
  (h10L2GelfandTriple hΩopen).continuous_formEnergyOrbit dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen) g

/-- The energy representative attains the prescribed initial function. -/
theorem solution_initial (g : (generator hΩopen).domain) (u : H¹₀(Ω))
    (hu : baseCoordCLM u = g) :
    solution hΩopen g 0 = u := by
  apply baseCoordCLM_injective hΩopen
  rw [baseCoordCLM_solution, StronglyContinuousSemigroup.realOrbit_zero, hu]

/-- The heat solution has the strong `L²` derivative given by its generator. -/
theorem hasDerivAt_solution (g : (generator hΩopen).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ baseCoordCLM (solution hΩopen g s))
      ((semigroup hΩopen).realOrbit (generator hΩopen g) t) t :=
  (h10L2GelfandTriple hΩopen).hasDerivAt_inclusion_formEnergyOrbit dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen) g ht

/-- The time derivative of the orbit solves the homogeneous weak Dirichlet heat equation. -/
theorem solution_weak_heat_equation (g : (generator hΩopen).domain)
    {t : ℝ} (ht : 0 < t) (v : H¹₀(Ω)) :
    ⟪deriv (fun s ↦ baseCoordCLM (solution hΩopen g s)) t, baseCoordCLM v⟫_ℝ +
      ∑ i : Fin n, ⟪derivCoordCLM i (solution hΩopen g t), derivCoordCLM i v⟫_ℝ = 0 := by
  rw [← dirichletForm_apply]
  exact (h10L2GelfandTriple hΩopen).formEnergyOrbit_weakEquation dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen) g ht v

/-- The heat evolution also satisfies the distributional equation against compactly
supported tests. -/
theorem solution_isWeakPoissonSolution (g : (generator hΩopen).domain)
    {t : ℝ} (ht : 0 < t) :
    IsWeakPoissonSolution
      (-deriv (fun s ↦ baseCoordCLM (solution hΩopen g s)) t) (solution hΩopen g t) := by
  apply (dirichletForm_eq_neg_pivot_iff hΩopen _ _).1
  rw [(hasDerivAt_solution hΩopen g ht).deriv]
  exact ((h10L2GelfandTriple hΩopen).formEnergyOrbit_spec dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen) g t).2

end HeatEquation.Semigroup.Dirichlet
