/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.Quantities
import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.CoefficientEstimates
import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.EnergyIdentity
import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.LocalizedFields
import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.ScalarEstimates
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Uniform interior difference-quotient energy estimates

We assemble the interior `H²` energy estimate of Evans from the energy
identity, the coercivity and commutator bounds, and the scalar absorption
lemmas. For a weak solution `u ∈ H¹₀(Ω)` of `-∂ᵢ(aᵢⱼ ∂ⱼ u) = f` with
Lipschitz uniformly elliptic coefficients and a cutoff `η ∈ C_c^∞(Ω)`, the
localized second-difference energy `∑ⱼ ‖η Dₖʰ ∂ⱼ u‖²` is bounded by
quantities involving only `‖f‖`, `‖u‖_{H¹}`, the cutoff, the coefficients and
their Lipschitz constants, with no dependence on the step `h`. This is the
boundedness input for the weak compactness step in `H2Compactness`.

## Main results

* `localizedDifference_energy_le`: the estimate after absorbing the cutoff
  error and the coefficient commutator, with a free Young parameter `gamma`
  on the forcing term.
* `localizedDifference_uniform_energy_le`: choosing `gamma ‖η‖∞² < alpha`
  leaves the strictly positive coefficient `(alpha - gamma ‖η‖∞²)/2` on the
  second-difference energy.
* `localizedDifferenceBound`, `localizedDifference_uniform_fixed_energy_le`:
  the right-hand side written as a function of the data alone, with the base
  quotient `Dₖʰ u` bounded by `‖u‖` through the `L²` difference-quotient
  estimate.

## Implementation notes

The cutoff hypothesis is a support collar: a `δ`-thickening of the translated
support of `η` must stay inside `Ω`, which is what makes the signed backward
test admissible. The lower-order terms are shown to be monotone in the
base-quotient norm (`localizedDifference_lowerOrder_le_of_norm_le`) so that
the a priori bound `‖Dₖʰ u‖ ≤ ‖u‖` can be substituted.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, steps 4-6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology InnerProductSpace
open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem sum_two_scaled_squares
    (c : ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, 2 * (c * x i) ^ 2) =
      2 * c ^ 2 * ∑ i : Fin n, (x i) ^ 2 := by
  simp only [mul_pow, Finset.mul_sum, mul_assoc]

/-- Evans' localized energy estimate after absorbing the principal cutoff
error and the coefficient commutator.  All terms on the right are explicit
lower-order quantities except for the displayed `gamma`-weighted source
contribution, which is arranged in the next step by choosing `gamma` from
the cutoff norm and ellipticity constant. -/
theorem localizedDifference_energy_le
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω)
    {gamma : ℝ} (hgamma : 0 < gamma) :
    (alpha / 2) * localizedDifferenceEnergy η
        (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) ≤
      localizedDifferenceCutoffRemainder A η alpha
        (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) +
        localizedDifferenceCoefficientRemainder C η alpha
          (zeroExtendedGradient hΩopen.measurableSet u) +
        localizedDifferenceMixedRemainder C η (zeroExtendedGradient hΩopen.measurableSet u)
          (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) +
        localizedDifferenceSourceRemainder η ‖f‖ gamma
          (zeroExtendedBaseQuotient hΩopen.measurableSet k h u)
          (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) := by
  have hcoercive := translatedCoefficient_cutoff_energy_le A hA (coordinateStep k h) η
    (zeroExtendedGradientQuotient hΩopen.measurableSet k h u)
  have hbalance :=
    weakDivergence_restrictedGlobalCoefficients_energyBalance hΩopen A f u hu η hηΩ k hh hδ hshift
  have hcut := abs_le.1 (abs_translatedCoefficient_cutoffError_le_young A (coordinateStep k h) η
    (zeroExtendedGradientQuotient hΩopen.measurableSet k h u)
    (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) halpha)
  have hcoeff := abs_le.1 (abs_coefficientQuotient_squaredCutoff_le_young A a C ha hrep k hh
    (zeroExtendedGradient hΩopen.measurableSet u)
    (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) η halpha)
  have hmixed := abs_le.1 (abs_coefficientQuotient_cutoffError_le A a C ha hrep k hh
    (zeroExtendedGradient hΩopen.measurableSet u)
    (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) η)
  have hsource := abs_le.1 (abs_source_pairing_backwardLocalizedDifferenceH10_le_young hΩopen f η
    hηΩ k u hδ hshift hgamma)
  simp only [real_inner_self_eq_norm_sq] at hcoercive
  dsimp only [zeroExtendedGradient, zeroExtendedBaseQuotient, zeroExtendedGradientQuotient,
    localizedDifferenceEnergy, localizedDifferenceCutoffRemainder,
    localizedDifferenceCoefficientRemainder, localizedDifferenceMixedRemainder,
    localizedDifferenceSourceRemainder, localizedDifferencePrincipalEnergy,
    localizedDifferenceCutoffError, localizedDifferenceCoefficientError,
    localizedDifferenceMixedError] at hcoercive hbalance hcut hcoeff hmixed hsource ⊢
  linarith only [hcoercive, hbalance, hcut.1, hcoeff.1, hmixed.1, hsource.2]

/-- Uniform form of Evans' interior difference-quotient estimate.  The
condition `gamma * ‖η‖∞² < alpha` leaves a strictly positive coefficient on
the localized second-difference energy; every term on the right is lower
order and independent of the second difference quotients. -/
theorem localizedDifference_uniform_energy_le
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (habsorb : gamma *
      ‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ ^ 2 < alpha) :
    0 < localizedDifferenceWeight η alpha gamma ∧
      localizedDifferenceWeight η alpha gamma * localizedDifferenceEnergy η
        (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) ≤
      localizedDifferenceCutoffRemainder A η alpha
        (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) +
        localizedDifferenceCoefficientRemainder C η alpha
          (zeroExtendedGradient hΩopen.measurableSet u) +
        localizedDifferenceMixedRemainder C η (zeroExtendedGradient hΩopen.measurableSet u)
          (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) + ‖f‖ ^ 2 / gamma +
        (gamma / 4) * localizedDifferenceSourceLower η
          (zeroExtendedBaseQuotient hΩopen.measurableSet k h u) := by
  refine ⟨div_pos (sub_pos.2 habsorb) two_pos, absorb_weighted_source_energy
    ((localizedDifference_energy_le hΩopen A a C ha hrep halpha hA f u hu η hηΩ k hh hδ hshift
      hgamma).trans_eq ?_)⟩
  simp only [localizedDifferenceSourceRemainder, localizedDifferenceSourceLower,
    localizedDifferenceEnergy, Finset.sum_add_distrib]
  rw [sum_two_scaled_squares]
  ring

/-- Every lower-order term in the localized elliptic estimate is monotone in
the two base-quotient norms.  Thus a uniform bound `‖q₀‖ ≤ M` and the
multiplier estimate `‖q • q₀‖ ≤ ‖q‖ M` remove all dependence on the step
size. -/
theorem localizedDifference_lowerOrder_le_of_norm_le
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (C : Fin n → Fin n → NNReal)
    (q : DerivLp n ∞ Set.univ)
    (d0u : Fin n → DerivLp n 2 Set.univ)
    (dqη : Fin n → DerivLp n ∞ Set.univ)
    (fNorm alpha gamma : ℝ)
    (q0 : DerivLp n 2 Set.univ) (M : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 ≤ gamma)
    (hq0 : ‖q0‖ ≤ M) :
    (∑ j : Fin n,
        (∑ i : Fin n, 2 * ‖A i j‖ * ‖dqη i‖ * ‖q0‖) ^ 2 / alpha) +
      (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) * ‖q • d0u j‖) ^ 2 / alpha) +
      (∑ i : Fin n, ∑ j : Fin n,
        2 * (C i j : ℝ) * ‖q • d0u j‖ * ‖dqη i‖ * ‖q0‖) +
      fNorm ^ 2 / gamma + (gamma / 4) *
        ((‖q‖ * ‖q • q0‖) ^ 2 +
          ∑ i : Fin n, 2 * (2 * ‖q‖ * ‖dqη i‖ * ‖q0‖) ^ 2) ≤
    (∑ j : Fin n,
        (∑ i : Fin n, 2 * ‖A i j‖ * ‖dqη i‖ * M) ^ 2 / alpha) +
      (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) * ‖q • d0u j‖) ^ 2 / alpha) +
      (∑ i : Fin n, ∑ j : Fin n,
        2 * (C i j : ℝ) * ‖q • d0u j‖ * ‖dqη i‖ * M) +
      fNorm ^ 2 / gamma + (gamma / 4) *
        ((‖q‖ * (‖q‖ * M)) ^ 2 +
          ∑ i : Fin n, 2 * (2 * ‖q‖ * ‖dqη i‖ * M) ^ 2) := by
  have hqq0 : ‖q • q0‖ ≤ ‖q‖ * M :=
    (MeasureTheory.Lp.norm_smul_le q q0).trans
      (mul_le_mul_of_nonneg_left hq0 (norm_nonneg q))
  gcongr

/-- Step-size-independent right-hand side in Evans's interior `H²`
estimate.  It contains only the coefficients, cutoff, forcing, the first
derivatives of the zero extension, and an a priori bound `M` for the base
difference quotient. -/
noncomputable def localizedDifferenceBound
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (C : Fin n → Fin n → NNReal)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (d0u : Fin n → DerivLp n 2 Set.univ)
    (fNorm alpha gamma M : ℝ) : ℝ :=
  let q := testFunctionLpTop (n := n) (Ω := Set.univ) η
  (∑ j : Fin n,
      (∑ i : Fin n, 2 * ‖A i j‖ *
        ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * M) ^ 2 /
        alpha) +
    (∑ i : Fin n,
      (∑ j : Fin n, (C i j : ℝ) * ‖q • d0u j‖) ^ 2 / alpha) +
    (∑ i : Fin n, ∑ j : Fin n,
      2 * (C i j : ℝ) * ‖q • d0u j‖ *
        ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * M) +
    fNorm ^ 2 / gamma + (gamma / 4) *
      ((‖q‖ * (‖q‖ * M)) ^ 2 +
        ∑ i : Fin n, 2 *
          (2 * ‖q‖ *
            ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * M) ^ 2)

/-- Fully uniform localized energy estimate.  Unlike
`localizedDifference_uniform_energy_le`, the right-hand side does not
contain `h`: the global zero-extension quotient is bounded by `‖u‖`.
This is the exact boundedness input needed for weak compactness. -/
theorem localizedDifference_uniform_fixed_energy_le
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (habsorb : gamma *
      ‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ ^ 2 < alpha) :
    0 < localizedDifferenceWeight η alpha gamma ∧
      localizedDifferenceWeight η alpha gamma * localizedDifferenceEnergy η
        (zeroExtendedGradientQuotient hΩopen.measurableSet k h u) ≤
      localizedDifferenceBound A C η (zeroExtendedGradient hΩopen.measurableSet u)
        ‖f‖ alpha gamma ‖u‖ := by
  have hraw := localizedDifference_uniform_energy_le hΩopen A a C ha hrep halpha hA f u hu η hηΩ k
    hh hδ hshift hgamma habsorb
  exact ⟨hraw.1, hraw.2.trans (localizedDifference_lowerOrder_le_of_norm_le A C _ _
    (fun i ↦ partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i) ‖f‖ alpha gamma _ ‖u‖ halpha
    hgamma.le (differenceQuotientL2.zeroExtend_base_norm_le hΩopen.measurableSet k hh u))⟩

end SobolevSpace.GraphSpace
