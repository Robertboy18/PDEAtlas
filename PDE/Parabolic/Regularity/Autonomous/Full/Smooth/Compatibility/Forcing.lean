/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing
public import PDE.Spaces.Sobolev.Evolution.Classical.Data

/-!
# Finite parabolic forcing data constructed from a smooth function

The finite forcing tuple `forcingJet` consists of the successive time
derivatives of one smooth function. Restriction preserves these derivatives,
and the mixed Sobolev trace theorem identifies the initial trace with the
classical slice. The derivative family and endpoint values are computed from
`f`, not assumed.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Evolution.Classical HigherOrder

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {f : SpaceTime n → ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)

/-- The initial value of the `j`-th time derivative of the forcing. -/
def initialForcingValue (hopen : IsOpen Ω) (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (j : ℕ) : ℝ^n → ℝ :=
  derivativeSlice hopen hf (List.replicate j 0) a

/-- All forcing initial values are smooth up to the spatial boundary. -/
theorem initialForcingValue_regular
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (j r : ℕ) :
    ContDiffUpToBoundary r (initialForcingValue hopen hf j) Ω :=
  derivativeSlice_regular hopen hbounded hab hf (List.replicate j 0) r ⟨le_rfl, hab.le⟩

/-- The finite forcing tuple starting at the `j`-th time derivative. -/
def forcingJet (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) : (m j : ℕ) → ForcingJet n Ω a b m
  | 0, j => sobolevTimeDerivative hopen hbounded hab hf 0 j
  | m + 1, j =>
      (sobolevTimeDerivative hopen hbounded hab hf (2 * (m + 1)) j,
        forcingJet hopen hbounded hab hf m (j + 1))

/-- The head is `sobolevTimeDerivative` at the required spatial order. -/
theorem head_forcingJet
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (m j : ℕ) :
    (forcingJet hopen hbounded hab hf m j).head =
      sobolevTimeDerivative hopen hbounded hab hf (2 * m) j := by
  cases m <;> rfl

/-- All finite forcing tuples have the same pivot-valued forcing class. -/
theorem headBase_forcingJet
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (m j : ℕ) :
    (forcingJet hopen hbounded hab hf m j).headBase =
      (forcingJet hopen hbounded hab hf 0 j).headBase := by
  simp only [ForcingJet.headBase, head_forcingJet]
  exact wkpBaseCoordinate_sobolevTimeDerivative_eq hopen hbounded hab hf (2 * m) 0 j

/-- Each entry of the finite tuple is the weak time derivative of the previous one. -/
theorem forcingJet_hasWeakDerivatives
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (m j : ℕ) :
    (forcingJet hopen hbounded hab hf m j).HasWeakDerivatives := by
  induction m generalizing j with
  | zero => trivial
  | succ m ih =>
    apply ForcingJet.HasWeakDerivatives.cons_of_base hopen _ (ih (j + 1))
    simpa only [head_forcingJet] using
      hasWeakTimeDerivativeOn_base_sobolevTimeDerivative hopen hbounded hab hf
        (2 * (m + 1)) (2 * m) j

/-- The trace constructed by finite parabolic regularity has the classical
value at every time, including the initial time. -/
theorem trace_forcingJet [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (m j : ℕ) :
    EqOn
      ((forcingJet hopen hbounded hab hf (m + 1) j).trace hopen hbounded hgraph hab
        (forcingJet_hasWeakDerivatives hopen hbounded hab hf (m + 1) j))
      (sobolevCurve hopen hbounded hab hf (2 * m + 1) j) (Icc a b) := by
  apply ForcingJet.trace_eqOn hopen hbounded hgraph hab _ _
    (continuousOn_sobolevCurve hopen hbounded hab hf (2 * m + 1) j)
  filter_upwards [sobolevTimeDerivative_ae hopen hbounded hab hf (2 * (m + 1)) j]
    with t ht
  change sobolevCurve hopen hbounded hab hf (2 * m + 1) j t =
    lowerOrderCLM _ (sobolevTimeDerivative hopen hbounded hab hf (2 * (m + 1)) j t)
  rw [ht, lowerOrder_sobolevCurve]

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
