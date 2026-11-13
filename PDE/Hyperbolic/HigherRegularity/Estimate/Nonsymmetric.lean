/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Estimate.Symmetric

/-!
# Quantitative higher regularity for nonsymmetric wave operators

For a wave operator whose principal divergence-form part is symmetric and
uniformly elliptic, lower-order terms lead to a two-step spatial recurrence
after the Gårding shift. We define the corresponding level
majorant and show that the two top energy bounds and the two-step recurrence
bound Evans's finite Sobolev norm sum and its essential supremum.

The two-step recurrence is a hypothesis of the theorems here. The spatial `H^k → H^{k+2}`
solver of `PDE.Hyperbolic.HigherRegularity.DivergenceForm.NonsymmetricHigherOrder` bounds
the shift term by a norm of the same function it solves for, not of the neighboring level,
so it does not give the recurrence in this form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, estimate (64), and proof of Theorem 5,
  estimate (59).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace
open scoped ENNReal BigOperators

variable {n m : ℕ} {Omega : Set (ℝ^n)}
variable {t0 t1 : ℝ}

/--
The explicit two-step level recurrence behind the nonsymmetric version of
Evans estimate (64).

Level zero is the highest time derivative in `L²`; level one is the next
derivative in `H¹`. For `k ≥ 0` the majorant is defined by

`C_{k+2} = S_k (F_k + C_k + |μ| E_k C_{k+1})`.

Here `S_k` plays the role of the norm of the shifted `H^k → H^{k+2}` solver,
`F_k` of the pointwise forcing factor, and `E_k` of the norm of the restriction
from `H^{k+1}` to `H^k`. `solutionSobolevNormSum_le_of_nonsymmetricSpatialRecurrence`
takes the recurrence with these constants as a hypothesis.
-/
noncomputable def nonsymmetricLevelMajorant
    (velocityConstant displacementConstant shiftConstant : ℝ)
    (ellipticConstant forcingConstant restrictionConstant : ℕ → ℝ) : ℕ → ℝ
  | 0 => velocityConstant
  | 1 => displacementConstant
  | k + 2 =>
      ellipticConstant k * (forcingConstant k +
          nonsymmetricLevelMajorant velocityConstant displacementConstant shiftConstant
            ellipticConstant forcingConstant restrictionConstant k +
        shiftConstant * restrictionConstant k *
          nonsymmetricLevelMajorant velocityConstant displacementConstant shiftConstant
            ellipticConstant forcingConstant restrictionConstant (k + 1))

/-- Every level majorant is nonnegative when its structural constants are. -/
theorem nonsymmetricLevelMajorant_nonneg {velocityConstant displacementConstant shiftConstant : ℝ}
    {ellipticConstant forcingConstant restrictionConstant : ℕ → ℝ}
    (hvelocity : 0 ≤ velocityConstant) (hdisplacement : 0 ≤ displacementConstant)
    (hshift : 0 ≤ shiftConstant) (helliptic : ∀ k, 0 ≤ ellipticConstant k)
    (hforcing : ∀ k, 0 ≤ forcingConstant k) (hrestriction : ∀ k, 0 ≤ restrictionConstant k) :
    ∀ k, 0 ≤ nonsymmetricLevelMajorant velocityConstant displacementConstant shiftConstant
      ellipticConstant forcingConstant restrictionConstant k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => exact hvelocity
  | one => exact hdisplacement
  | more k h0 h1 =>
    exact mul_nonneg (helliptic k) (add_nonneg (add_nonneg (hforcing k) h0)
      (mul_nonneg (mul_nonneg hshift (hrestriction k)) h1))

/--
Evans, §7.2.3, estimate (64), for nonsymmetric operators, assuming the two-step spatial
recurrence.

Unlike `solutionSobolevNormSum_le_mul_dataBudget_of_levelBounds`, this theorem does
not assume a bound for every Sobolev level. Its hypotheses are:

* the two energy bounds for the top differentiated wave;
* the two-step elliptic recurrence `hspatialRecurrence`. The higher-order solver
  `exists_higher_with_norm_of_unshifted_full_weakSolution` bounds the shift term by a norm
  of the function it solves for rather than of the neighboring level, so it does not
  supply this hypothesis.

Two-step induction derives every level bound with `nonsymmetricLevelMajorant`; finite
summation then gives the norm sum in (64). The right-hand side is
`evansHigherRegularityDataBudget D`, so the constant is independent of the solution and of
the Galerkin dimension.
-/
theorem solutionSobolevNormSum_le_of_nonsymmetricSpatialRecurrence
    (D : WaveProblemData n m Omega t0 t1) (u : SobolevTimeJet n (m + 1) Omega t0 t1)
    (velocityConstant displacementConstant shiftConstant : ℝ)
    (ellipticConstant forcingConstant restrictionConstant : ℕ → ℝ)
    (hvelocityConstant : 0 ≤ velocityConstant) (hdisplacementConstant : 0 ≤ displacementConstant)
    (hshiftConstant : 0 ≤ shiftConstant) (hellipticConstant : ∀ k, 0 ≤ ellipticConstant k)
    (hforcingConstant : ∀ k, 0 ≤ forcingConstant k)
    (hrestrictionConstant : ∀ k, 0 ≤ restrictionConstant k)
    (hvelocity : ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative (0 : Fin (m + 2))).head t‖ ≤
        velocityConstant * evansHigherRegularityDataBudget D)
    (hdisplacement : ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative (⟨1, by omega⟩ : Fin (m + 2))).head t‖ ≤
        displacementConstant * evansHigherRegularityDataBudget D)
    (hspatialRecurrence : ∀ k : ℕ, (hk : k + 2 < m + 2) →
      ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
        ‖(u.iteratedTimeDerivative (⟨k + 2, hk⟩ : Fin (m + 2))).head t‖ ≤
          ellipticConstant k * (forcingConstant k * evansHigherRegularityDataBudget D +
            ‖(u.iteratedTimeDerivative (⟨k, by omega⟩ : Fin (m + 2))).head t‖ +
            shiftConstant * restrictionConstant k *
              ‖(u.iteratedTimeDerivative (⟨k + 1, by omega⟩ : Fin (m + 2))).head t‖)) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      solutionSobolevNormSum u t ≤
        (∑ r : Fin (m + 2), nonsymmetricLevelMajorant velocityConstant displacementConstant
          shiftConstant ellipticConstant forcingConstant restrictionConstant r.1) *
          evansHigherRegularityDataBudget D := by
  let budget := evansHigherRegularityDataBudget D
  let majorant : ℕ → ℝ := nonsymmetricLevelMajorant velocityConstant displacementConstant
    shiftConstant ellipticConstant forcingConstant restrictionConstant
  have _hmajorant : ∀ k, 0 ≤ majorant k := nonsymmetricLevelMajorant_nonneg hvelocityConstant
    hdisplacementConstant hshiftConstant hellipticConstant hforcingConstant hrestrictionConstant
  have hlevelNat : ∀ k : ℕ, (hk : k < m + 2) → ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative (⟨k, hk⟩ : Fin (m + 2))).head t‖ ≤ majorant k * budget := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => exact fun _ ↦ hvelocity
    | one => exact fun _ ↦ hdisplacement
    | more k h0 h1 =>
      intro hk
      filter_upwards [hspatialRecurrence k hk, h0 (by omega), h1 (by omega)] with t hstep h0 h1
      have := hellipticConstant k
      have := mul_nonneg hshiftConstant (hrestrictionConstant k)
      calc _ ≤ _ := hstep
        _ ≤ ellipticConstant k * (forcingConstant k * budget + majorant k * budget +
            shiftConstant * restrictionConstant k * (majorant (k + 1) * budget)) := by gcongr
        _ = majorant (k + 2) * budget := by
          simp only [majorant, nonsymmetricLevelMajorant]
          ring
  filter_upwards [solutionSobolevNormSum_le_sum_of_levelBounds u
    (fun r : Fin (m + 2) ↦ majorant r.1 * budget) fun r ↦ hlevelNat r.1 r.2] with t ht
  rwa [← Finset.sum_mul] at ht

/-- Essential-supremum form of `solutionSobolevNormSum_le_of_nonsymmetricSpatialRecurrence`:
the two top energy bounds and the two-step recurrence bound the essential supremum of the norm
sum in Evans (64). -/
theorem eLpNormEssSup_solutionSobolevNormSum_le_of_nonsymmetricSpatialRecurrence
    (D : WaveProblemData n m Omega t0 t1) (u : SobolevTimeJet n (m + 1) Omega t0 t1)
    (velocityConstant displacementConstant shiftConstant : ℝ)
    (ellipticConstant forcingConstant restrictionConstant : ℕ → ℝ)
    (hvelocityConstant : 0 ≤ velocityConstant) (hdisplacementConstant : 0 ≤ displacementConstant)
    (hshiftConstant : 0 ≤ shiftConstant) (hellipticConstant : ∀ k, 0 ≤ ellipticConstant k)
    (hforcingConstant : ∀ k, 0 ≤ forcingConstant k)
    (hrestrictionConstant : ∀ k, 0 ≤ restrictionConstant k)
    (hvelocity : ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative (0 : Fin (m + 2))).head t‖ ≤
        velocityConstant * evansHigherRegularityDataBudget D)
    (hdisplacement : ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative (⟨1, by omega⟩ : Fin (m + 2))).head t‖ ≤
        displacementConstant * evansHigherRegularityDataBudget D)
    (hspatialRecurrence : ∀ k : ℕ, (hk : k + 2 < m + 2) →
      ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
        ‖(u.iteratedTimeDerivative (⟨k + 2, hk⟩ : Fin (m + 2))).head t‖ ≤
          ellipticConstant k * (forcingConstant k * evansHigherRegularityDataBudget D +
            ‖(u.iteratedTimeDerivative (⟨k, by omega⟩ : Fin (m + 2))).head t‖ +
            shiftConstant * restrictionConstant k *
              ‖(u.iteratedTimeDerivative (⟨k + 1, by omega⟩ : Fin (m + 2))).head t‖)) :
    eLpNormEssSup (solutionSobolevNormSum u) (volume.restrict (Set.Ioc t0 t1)) ≤
      ENNReal.ofReal ((∑ r : Fin (m + 2), nonsymmetricLevelMajorant velocityConstant
        displacementConstant shiftConstant ellipticConstant forcingConstant restrictionConstant
          r.1) * evansHigherRegularityDataBudget D) := by
  refine eLpNormEssSup_le_of_ae_bound ?_
  filter_upwards [solutionSobolevNormSum_le_of_nonsymmetricSpatialRecurrence D u
    velocityConstant displacementConstant shiftConstant ellipticConstant forcingConstant
    restrictionConstant hvelocityConstant hdisplacementConstant hshiftConstant
    hellipticConstant hforcingConstant hrestrictionConstant hvelocity hdisplacement
    hspatialRecurrence] with t ht
  rwa [Real.norm_eq_abs, abs_of_nonneg (solutionSobolevNormSum_nonneg u t)]

end Hyperbolic.HigherRegularity
