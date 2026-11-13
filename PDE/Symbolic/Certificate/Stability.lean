/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Stability.FiniteTail
public import CAS.Certificate.Atlas.Residual

/-!
# Residual-certificate bridge for nonlinear stability

The symbolic layer produces residual certificates on parameter or spatial domains, while a
`ModulatedEnergyEstimate` of `PDE.Analysis.Stability` takes one residual vector with a norm
bound. Evaluating a certificate at a point of its domain gives both: the residual vector and
its error budget, which is nonnegative because the domain is nonempty.

`ResidualCert.toModulatedEnergyEstimate` and `ResidualAtlasCert.toModulatedEnergyEstimate`
build the estimate from the coercivity, nonlinear, and modulation bounds, which are explicit
hypotheses. `ResidualCert.toHeadTailModulatedEnergyEstimate` does the same from a
`HeadTailDissipativityEstimate` on a split state space.
-/

@[expose] public section

noncomputable section

namespace CAS.Certificate

open PDE.Analysis.Stability
open scoped RealInnerProductSpace

variable {α H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {domain : Set α}

namespace ResidualCert

omit [InnerProductSpace ℝ H] in
/-- Pointwise norm bound exposed by a residual certificate. -/
theorem norm_residual_le
    (certificate : ResidualCert α H domain)
    {point : α} (hpoint : point ∈ domain) :
    ‖certificate.residual point‖ ≤ certificate.eps := by
  simpa using certificate.sound point hpoint

/-- Construct a nonlinear energy estimate using a certified residual at one admitted point. -/
def toModulatedEnergyEstimate
    (certificate : ResidualCert α H domain)
    (point : α) (hpoint : point ∈ domain)
    (linear : H →L[ℝ] H)
    (nonlinear modulation : H → H)
    (decayRate : Set.Ioi (0 : ℝ))
    (nonlinearConstant modulationConstant : NNReal)
    (linear_pairing_le :
      ∀ perturbation,
        ⟪linear perturbation, perturbation⟫ ≤
          -decayRate * ‖perturbation‖ * ‖perturbation‖)
    (nonlinear_norm_le :
      ∀ perturbation,
        ‖nonlinear perturbation‖ ≤
          nonlinearConstant * ‖perturbation‖ * ‖perturbation‖)
    (modulation_norm_le :
      ∀ perturbation,
        ‖modulation perturbation‖ ≤
          modulationConstant * ‖perturbation‖) :
    ModulatedEnergyEstimate H where
  linear := linear
  nonlinear := nonlinear
  modulation := modulation
  residual := certificate.residual point
  decayRate := decayRate
  nonlinearConstant := nonlinearConstant
  modulationConstant := modulationConstant
  residualBound := ⟨certificate.eps, certificate.eps_nonneg ⟨point, hpoint⟩⟩
  linear_pairing_le := linear_pairing_le
  nonlinear_norm_le := nonlinear_norm_le
  modulation_norm_le := modulation_norm_le
  residual_norm_le := certificate.norm_residual_le hpoint

end ResidualCert

namespace ResidualAtlasCert

variable {ι : Type}

/-- A patchwise residual atlas feeds the same stability constructor after global assembly. -/
def toModulatedEnergyEstimate
    (certificate : ResidualAtlasCert α H ι domain)
    (point : α) (hpoint : point ∈ domain)
    (linear : H →L[ℝ] H)
    (nonlinear modulation : H → H)
    (decayRate : Set.Ioi (0 : ℝ))
    (nonlinearConstant modulationConstant : NNReal)
    (linear_pairing_le :
      ∀ perturbation,
        ⟪linear perturbation, perturbation⟫ ≤
          -decayRate * ‖perturbation‖ * ‖perturbation‖)
    (nonlinear_norm_le :
      ∀ perturbation,
        ‖nonlinear perturbation‖ ≤
          nonlinearConstant * ‖perturbation‖ * ‖perturbation‖)
    (modulation_norm_le :
      ∀ perturbation,
        ‖modulation perturbation‖ ≤
          modulationConstant * ‖perturbation‖) :
    ModulatedEnergyEstimate H :=
  certificate.toResidualCert.toModulatedEnergyEstimate
    point hpoint linear nonlinear modulation
    decayRate nonlinearConstant modulationConstant
    linear_pairing_le nonlinear_norm_le modulation_norm_le

end ResidualAtlasCert

variable {Head Tail : Type}
  [NormedAddCommGroup Head] [InnerProductSpace ℝ Head]
  [NormedAddCommGroup Tail] [InnerProductSpace ℝ Tail]

namespace ResidualCert

/-- Feed a certified residual directly into a closed finite-head/tail stability estimate. -/
def toHeadTailModulatedEnergyEstimate
    (certificate :
      ResidualCert α (SplitState Head Tail) domain)
    (point : α) (hpoint : point ∈ domain)
    (estimate : HeadTailDissipativityEstimate Head Tail)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdecay : 0 < estimate.combinedRate epsilon)
    (nonlinear modulation :
      SplitState Head Tail → SplitState Head Tail)
    (nonlinearConstant modulationConstant : NNReal)
    (nonlinear_norm_le :
      ∀ perturbation,
        ‖nonlinear perturbation‖ ≤
          nonlinearConstant * ‖perturbation‖ * ‖perturbation‖)
    (modulation_norm_le :
      ∀ perturbation,
        ‖modulation perturbation‖ ≤
          modulationConstant * ‖perturbation‖) :
    ModulatedEnergyEstimate (SplitState Head Tail) :=
  estimate.toModulatedEnergyEstimate
    hepsilon hdecay nonlinear modulation
    (certificate.residual point)
    nonlinearConstant modulationConstant
    ⟨certificate.eps, certificate.eps_nonneg ⟨point, hpoint⟩⟩
    nonlinear_norm_le modulation_norm_le
    (certificate.norm_residual_le hpoint)

end ResidualCert

end CAS.Certificate
