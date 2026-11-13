/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Compatibility.Forcing
public import PDE.Parabolic.Regularity.Autonomous.Full.Smooth.Compatibility.InitialValues
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Compatibility
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ClassicalZero

/-!
# Identifying the classical and finite Sobolev compatibility recurrences

The initial traces and full spatial load are computed from the smooth data.
Finite parabolic compatibility then asks exactly for zero boundary values of
the recursively derived classical initial data.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical HigherOrder

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
variable {f : SpaceTime n → ℝ} {g : ℝ^n → ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)

/-- The finite Sobolev recurrence produces exactly the next classical initial value. -/
theorem initialDerivative_forcingJet [Fact (0 < n)] (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (m j : ℕ) :
    initialDerivative (P.load hopen hbounded) hopen hbounded hgraph hab
      (forcingJet hopen hbounded hab hf (m + 1) j)
      (forcingJet_hasWeakDerivatives hopen hbounded hab hf (m + 1) j)
      (initialSobolevValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg (2 * (m + 1) + 1) j) =
      initialSobolevValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg (2 * m + 1) (j + 1) := by
  rw [initialSobolevValue_succ, initialDerivative,
    trace_forcingJet hopen hbounded hgraph hab hf m j ⟨le_rfl, hab.le⟩,
    lowerOrder_initialSobolevValue,
    sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hf (2 * m + 1) j ⟨le_rfl, hab.le⟩]
  rfl

/-- A first-order zero-boundary realization also represents every higher
Sobolev realization of the same derived classical datum. -/
theorem initialSobolevValue_zeroBoundary (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {F : ℕ → ℝ^n → ℝ} (hF : ∀ j r, ContDiffUpToBoundary r (F j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (r j : ℕ)
    (hzero : ∃ z : H¹₀(Ω),
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hF hg 1 j) = baseCoordCLM z) :
    ∃ z : H¹₀(Ω),
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hF hg r j) =
        baseCoordCLM z := by
  obtain ⟨z, hz⟩ := hzero
  refine ⟨z, ?_⟩
  rw [← hz]
  apply Lp.ext
  exact ((initialValue_regular P hopen hbounded hF hg j r).toWkpSpaceOn_base_ae
    hopen hbounded 2).trans
      ((initialValue_regular P hopen hbounded hF hg j 1).toWkpSpaceOn_base_ae
        hopen hbounded 2).symm

/-- Zero boundary values of the derived initial data imply compatibility at
every finite order, including order zero. -/
theorem compatible_forcingJet_of_initial_zero [Fact (0 < n)] (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hzero : ∀ j, ∃ z : H¹₀(Ω),
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg 1 j) = baseCoordCLM z)
    (m j : ℕ) :
    Compatible (P.load hopen hbounded) hopen hbounded hgraph hab
      (forcingJet hopen hbounded hab hf m j)
      (forcingJet_hasWeakDerivatives hopen hbounded hab hf m j)
      (initialSobolevValue P hopen hbounded
        (initialForcingValue_regular hopen hbounded hab hf) hg (2 * m + 1) j) := by
  induction m generalizing j with
  | zero => exact hzero j
  | succ m ih =>
    refine ⟨initialSobolevValue_zeroBoundary P hopen hbounded _ hg _ j (hzero j), ?_⟩
    rw [initialDerivative_forcingJet]
    exact ih (j + 1)

/-- Pointwise zero boundary values give the `H¹₀` realization required by
finite parabolic compatibility. -/
theorem initialSobolevValue_zeroBoundary_of_eq_zero [Fact (0 < n)]
    (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {F : ℕ → ℝ^n → ℝ} (hF : ∀ j r, ContDiffUpToBoundary r (F j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (r j : ℕ)
    (hzero : ∀ x ∈ frontier Ω, initialBoundaryValue P hopen hbounded hF hg j x = 0) :
    ∃ z : H¹₀(Ω),
      wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hF hg r j) =
        baseCoordCLM z := by
  let h₀ := initialValue_regular P hopen hbounded hF hg j 0
  have h₁ : ContDiffUpToBoundary 1 h₀.continuousRepresentative Ω :=
    (initialValue_regular P hopen hbounded hF hg j 1).congr
      hopen h₀.continuousRepresentative_eqOn
  obtain ⟨z, hz, _⟩ := h₁.exists_H10_of_eq_zero_on_frontier hopen hbounded hgraph
    h₀.continuous_continuousRepresentative.continuousOn hzero
  refine ⟨z, MeasureTheory.Lp.ext ?_⟩
  filter_upwards [(initialValue_regular P hopen hbounded hF hg j r).toWkpSpaceOn_base_ae
    hopen hbounded 2, hz, ae_restrict_mem hopen.measurableSet] with x hx hz hxΩ
  exact hx.trans ((h₀.continuousRepresentative_eqOn hxΩ).symm.trans hz.symm)

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
