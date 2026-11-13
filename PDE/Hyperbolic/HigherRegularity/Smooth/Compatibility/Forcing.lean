/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Compatibility.BoundaryValues
public import PDE.Spaces.Sobolev.Evolution.Classical.Data
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional

/-!
# Wave forcing jets from one smooth function

The canonical Sobolev derivatives of smooth spacetime data form every finite
decreasing wave forcing jet. The endpoint trace produced by the
Lions–Magenes construction is the canonical smooth forcing slice, so the
compatibility recurrence uses the initial derivatives of the forcing itself.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity.SmoothWave

open Filter MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Evolution.Classical PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {f : SpaceTime n → ℝ}
  (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))

/-- The forcing's adjacent Sobolev derivatives satisfy the wave jet's
identity Gelfand relation after one spatial restriction. -/
theorem forcing_derivative (m j : ℕ) :
    HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity (W^{m,2}(Ω)))
      (lowerOrderTimeLp (sobolevTimeDerivative hopen hbounded hab hf (m + 1) j))
      (rieszToDualLp (sobolevTimeDerivative hopen hbounded hab hf m (j + 1))) := by
  have hd := hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hf m j
  have h₀ := (sobolevTimeDerivative_ae hopen hbounded hab hf m j).filter_mono
    (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
  have h₁ := (sobolevTimeDerivative_ae hopen hbounded hab hf m (j + 1)).filter_mono
    (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
  have hweak := hd.congr_ae_restrict measurableSet_Ioo h₀.symm h₁.symm
  have hlower : lowerOrderTimeLp (sobolevTimeDerivative hopen hbounded hab hf (m + 1) j) =
      sobolevTimeDerivative hopen hbounded hab hf m j :=
    lowerOrder_sobolevTimeDerivative hopen hbounded hab hf (Nat.le_succ m) j
  rw [hlower]
  exact hweak.identity_hasGelfandWeakTimeDerivativeOn hab

/-- The finite decreasing chain of forcing derivatives. -/
def forcingJetCore : (m j : ℕ) →
    SobolevTimeJetCore n Ω a b m (sobolevTimeDerivative hopen hbounded hab hf m j)
  | 0, j => .zero (sobolevTimeDerivative hopen hbounded hab hf 0 j)
  | m + 1, j => .succ
      (sobolevTimeDerivative hopen hbounded hab hf (m + 1) j)
      (sobolevTimeDerivative hopen hbounded hab hf m (j + 1))
      (forcing_derivative hopen hbounded hab hf m j)
      (forcingJetCore m (j + 1))

/-- The finite forcing jet, constructed from the function and starting
with its `j`-th time derivative. -/
def forcingJet (m j : ℕ) : SobolevTimeJet n m Ω a b :=
  ⟨sobolevTimeDerivative hopen hbounded hab hf m j, forcingJetCore hopen hbounded hab hf m j⟩

/-- Differentiating a constructed jet drops its leading derivative. -/
theorem forcingJet_timeDerivative (m j : ℕ) :
    (forcingJet hopen hbounded hab hf (m + 1) j).timeDerivative =
      forcingJet hopen hbounded hab hf m (j + 1) :=
  rfl

/-- The canonical Sobolev trace agrees with the smooth forcing trace.
The terminal member of an order-zero jet does not require an endpoint trace. -/
theorem forcingJet_initialTrace (m j : ℕ) :
    (InitialTraceData.ofJet (forcingJet hopen hbounded hab hf (m + 1) j) hab).head =
      (forcingTrace_regular hopen hbounded hab hf j m).toWkpSpaceOn hopen hbounded 2 := by
  have heq := InitialTraceData.head_eq_of_continuousRepresentative
    (InitialTraceData.ofJet (forcingJet hopen hbounded hab hf (m + 1) j) hab)
    (sobolevCurve hopen hbounded hab hf m j)
    (continuousOn_sobolevCurve hopen hbounded hab hf m j) (by
      filter_upwards [sobolevTimeDerivative_ae hopen hbounded hab hf (m + 1) j] with t ht
      change sobolevCurve hopen hbounded hab hf m j t = lowerOrderCLM (Nat.le_succ m)
          (sobolevTimeDerivative hopen hbounded hab hf (m + 1) j t)
      rw [ht, lowerOrder_sobolevCurve]) hab
  rw [← heq, sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hf m j ⟨le_rfl, hab.le⟩]
  rfl

end Hyperbolic.HigherRegularity.SmoothWave
