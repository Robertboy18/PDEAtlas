/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.FiniteDifferences

/-!
# Coefficient estimates for interior difference quotients

Interior `H²` regularity is proved by testing `-∂ᵢ(aᵢⱼ ∂ⱼ u) = f` with
`v = -Dₖ⁻ʰ(η² Dₖʰ u)` for a cutoff `η ∈ C_c^∞(Ω)`. After discrete integration
by parts the principal term becomes

`∑ᵢⱼ ⟪(τₕ aᵢⱼ) Dₖʰ ∂ⱼ u, ∂ᵢ(η² Dₖʰ u)⟫ + ∑ᵢⱼ ⟪(Dₖʰ aᵢⱼ) ∂ⱼ u, ∂ᵢ(η² Dₖʰ u)⟫`.

We prove the estimates needed to absorb everything except the
coercive part `α ∑ⱼ ‖η Dₖʰ ∂ⱼ u‖²`: coercivity of the translated matrix
`τₕ A` (ellipticity is translation invariant), the cutoff error coming from
`∂ᵢ(η²) = 2η ∂ᵢη`, and the coefficient commutator `Dₖʰ aᵢⱼ`, which is
bounded in `L∞` by the Lipschitz constant of `aᵢⱼ` uniformly in `h ≠ 0`.

## Main results

* `aeUniformlyElliptic_translateLp`, `translatedCoefficient_energy_le`,
  `translatedCoefficient_cutoff_energy_le`: ellipticity of `τₕ A` and the
  resulting integrated coercivity, with one factor of `η` on each field.
* `abs_translatedCoefficient_cutoffError_le_young`: the derivative-of-cutoff
  error after Young's inequality, spending one quarter of the elliptic energy
  per differentiated component.
* `abs_coefficientQuotient_squaredCutoff_le_young`: the coefficient commutator
  against the `η²`-weighted field, absorbed the same way.
* `abs_coefficientQuotient_cutoffError_le`: the mixed commutator/cutoff error,
  a purely lower-order term.

## Implementation notes

All fields live on `ℝ^n` after zero extension, so the coefficients are `L∞`
classes on `Set.univ` and the Lipschitz functions `a i j` are separate data
agreeing with them almost everywhere. Matrix rows are summed before Young's
inequality is applied.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, step 4, (15)-(20).
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity),
  pp. 177-218.
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology InnerProductSpace
open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Uniform ellipticity is invariant under a common spatial translation of
all coefficient entries.  The almost-everywhere exceptional set is pulled
back through the measure-preserving Euclidean translation. -/
theorem aeUniformlyElliptic_translateLp
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (z : ℝ^n) :
    AEUniformlyElliptic (n := n) (Ω := Set.univ)
      (fun i j ↦ Rellich.translateLp ∞ z (A i j)) alpha := by
  refine ⟨hA.1, ?_⟩
  have hpres : MeasurePreserving (Rellich.translationContinuousMap z)
      (domainMeasure n Set.univ) (domainMeasure n Set.univ) :=
    Rellich.translationMeasurePreserving (n := n) z
  have hell :
      ∀ᵐ x ∂domainMeasure n Set.univ, ∀ ξ : Fin n → ℝ,
        alpha * ∑ i : Fin n, ξ i * ξ i ≤
          ∑ i : Fin n, ∑ j : Fin n, A i j (x + z) * ξ j * ξ i := by
    simpa [Function.comp_def, Rellich.translationContinuousMap] using
      hpres.quasiMeasurePreserving.tendsto_ae.eventually hA.2
  have hcoeff :
      ∀ᵐ x ∂domainMeasure n Set.univ, ∀ i j : Fin n,
        Rellich.translateLp ∞ z (A i j) x = A i j (x + z) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact Rellich.translateLp_apply_ae (n := n) ∞ z (A i j)
  filter_upwards [hell, hcoeff] with x hx hcx
  intro ξ
  simpa only [hcx] using hx ξ

/-- Integrated coercivity of the translated coefficient matrix on an
arbitrary global `L²` vector field. -/
theorem translatedCoefficient_energy_le
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (z : ℝ^n) (v : Fin n → DerivLp n 2 Set.univ) :
    alpha * ∑ i : Fin n, inner ℝ (v i) (v i) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          ((Rellich.translateLp ∞ z (A i j)) • v j) (v i) := by
  simpa only [multiplicationCoefficientOperator_apply] using
    aeUniformlyElliptic_energy_le
      (n := n) (Ω := Set.univ)
      (fun i j ↦ Rellich.translateLp ∞ z (A i j))
      (aeUniformlyElliptic_translateLp A hA z) v

/-- Cutoff-weighted coercivity for the translated principal part.  This is
the exact integrated inequality used after testing with
`-Dₖ⁻ʰ(η² Dₖʰu)`: one factor of `η` is moved to each differentiated field,
while the weak formulation retains the multiplier `η²`. -/
theorem translatedCoefficient_cutoff_energy_le
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (z : ℝ^n) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (v : Fin n → DerivLp n 2 Set.univ) :
    alpha * ∑ i : Fin n,
        inner ℝ
          (testFunctionLpTop (n := n) (Ω := Set.univ) η • v i)
          (testFunctionLpTop (n := n) (Ω := Set.univ) η • v i) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (Rellich.translateLp ∞ z (A i j) • v j)
          (testFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) • v i) := by
  let q := testFunctionLpTop (n := n) (Ω := Set.univ) η
  have hsq :
      testFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) =
        (q • q : DerivLp n ∞ Set.univ) := by
    simpa [q, squaredCutoff] using
      (testFunctionLpTop_mul (n := n) (Ω := Set.univ) η η)
  have hcoerc := translatedCoefficient_energy_le A hA z
    (fun i ↦ q • v i)
  refine hcoerc.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let a := Rellich.translateLp ∞ z (A i j)
  calc
    inner ℝ (a • (q • v j)) (q • v i) =
        inner ℝ (q • (a • v j)) (q • v i) := by
          rw [lpSMul_top_top_two_comm]
    _ = inner ℝ (a • v j) (q • (q • v i)) :=
      inner_lpSMul_left_eq_right q (a • v j) (q • v i)
    _ = inner ℝ (a • v j) ((q • q : DerivLp n ∞ Set.univ) • v i) := by
      rw [lpSMul_top_top_two_assoc]
    _ = inner ℝ
        (Rellich.translateLp ∞ z (A i j) • v j)
        (testFunctionLpTop (n := n) (Ω := Set.univ)
          (squaredCutoff η) • v i) := by
      rw [hsq]

/-- Matrix-level bound for the translated principal part paired with the
derivative-of-cutoff error.  The desired field remains localized by one
factor of `η`. -/
theorem abs_translatedCoefficient_cutoffError_le
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (z : ℝ^n) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (v : Fin n → DerivLp n 2 Set.univ) (u : DerivLp n 2 Set.univ) :
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Rellich.translateLp ∞ z (A i j) • v j)
          (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • u)| ≤
      ∑ i : Fin n, ∑ j : Fin n,
        2 * ‖A i j‖ *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v j‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖u‖ := by
  calc
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Rellich.translateLp ∞ z (A i j) • v j)
          (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • u)| ≤
        ∑ i : Fin n, |∑ j : Fin n,
          inner ℝ (Rellich.translateLp ∞ z (A i j) • v j)
            (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
              (squaredCutoff η) i • u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        |inner ℝ (Rellich.translateLp ∞ z (A i j) • v j)
          (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • u)| := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        2 * ‖A i j‖ *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v j‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖u‖ := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
        simpa only [Rellich.norm_translateLp] using
          (abs_inner_lpSMul_partialSquaredCutoff_le
            (Rellich.translateLp ∞ z (A i j)) η i (v j) u)

/-- Young-absorbed principal cutoff error, grouped by differentiated
component.  Grouping before applying Young's inequality is important: it
spends one quarter of the elliptic energy for each `v j`, rather than one
quarter for every matrix entry `A i j`. -/
theorem abs_translatedCoefficient_cutoffError_le_young
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (z : ℝ^n) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (v : Fin n → DerivLp n 2 Set.univ) (u : DerivLp n 2 Set.univ)
    {alpha : ℝ} (halpha : 0 < alpha) :
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Rellich.translateLp ∞ z (A i j) • v j)
          (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • u)| ≤
      (∑ j : Fin n,
        (∑ i : Fin n,
          2 * ‖A i j‖ *
            ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖u‖) ^ 2 /
          alpha) +
        (alpha / 4) * ∑ j : Fin n,
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v j‖ ^ 2 := by
  calc
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Rellich.translateLp ∞ z (A i j) • v j)
          (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • u)| ≤
        ∑ i : Fin n, ∑ j : Fin n,
          2 * ‖A i j‖ *
            ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v j‖ *
            ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖u‖ :=
      abs_translatedCoefficient_cutoffError_le A z η v u
    _ = ∑ j : Fin n,
        (∑ i : Fin n,
          2 * ‖A i j‖ *
            ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖u‖) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v j‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ ∑ j : Fin n,
        ((∑ i : Fin n,
          2 * ‖A i j‖ *
            ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖u‖) ^ 2 /
            alpha +
          (alpha / 4) *
            ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v j‖ ^ 2) := by
      exact Finset.sum_le_sum fun j _ ↦
        mul_le_sq_div_add_quarter halpha _ _
    _ = (∑ j : Fin n,
        (∑ i : Fin n,
          2 * ‖A i j‖ *
            ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖u‖) ^ 2 /
          alpha) +
        (alpha / 4) * ∑ j : Fin n,
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v j‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Matrix-level localized coefficient-commutator estimate.  Lipschitz
regularity of each representative gives a step-size-independent bound. -/
theorem abs_coefficientQuotient_squaredCutoff_le
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    (u v : Fin n → DerivLp n 2 Set.univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
          (testFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) • v i)| ≤
      ∑ i : Fin n, ∑ j : Fin n,
        (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖ *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v i‖ := by
  calc
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
          (testFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) • v i)| ≤
        ∑ i : Fin n, ∑ j : Fin n,
          |inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
            (testFunctionLpTop (n := n) (Ω := Set.univ)
              (squaredCutoff η) • v i)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖ *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v i‖ := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        (abs_inner_lpSMul_squaredCutoff_le
          (differenceQuotientLp ∞ k h (A i j)) η (u j) (v i)).trans <| by
            gcongr
            exact norm_differenceQuotientLp_top_le
              k (A i j) (a i j) (ha i j) (hrep i j) h hh

/-- Young-absorbed localized coefficient commutator.  The matrix row is
summed first, so exactly one quarter of the localized principal energy is
used for each output component. -/
theorem abs_coefficientQuotient_squaredCutoff_le_young
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    (u v : Fin n → DerivLp n 2 Set.univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    {alpha : ℝ} (halpha : 0 < alpha) :
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
          (testFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) • v i)| ≤
      (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖) ^ 2 /
            alpha) +
        (alpha / 4) * ∑ i : Fin n,
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v i‖ ^ 2 := by
  calc
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
          (testFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) • v i)| ≤
        ∑ i : Fin n, ∑ j : Fin n,
          (C i j : ℝ) *
            ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖ *
            ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v i‖ :=
      abs_coefficientQuotient_squaredCutoff_le
        A a C ha hrep k hh u v η
    _ = ∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin n,
        ((∑ j : Fin n, (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖) ^ 2 /
            alpha +
          (alpha / 4) *
            ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v i‖ ^ 2) := by
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_sq_div_add_quarter halpha _ _
    _ = (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖) ^ 2 /
            alpha) +
        (alpha / 4) * ∑ i : Fin n,
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • v i‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Mixed coefficient-commutator/cutoff-error estimate. -/
theorem abs_coefficientQuotient_cutoffError_le
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    (u : Fin n → DerivLp n 2 Set.univ) (q0 : DerivLp n 2 Set.univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
          (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • q0)| ≤
      ∑ i : Fin n, ∑ j : Fin n,
        2 * (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖q0‖ := by
  calc
    |∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
          (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i • q0)| ≤
        ∑ i : Fin n, ∑ j : Fin n,
          |inner ℝ (differenceQuotientLp ∞ k h (A i j) • u j)
            (partialTestFunctionLpTop (n := n) (Ω := Set.univ)
              (squaredCutoff η) i • q0)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        2 * (C i j : ℝ) *
          ‖testFunctionLpTop (n := n) (Ω := Set.univ) η • u j‖ *
          ‖partialTestFunctionLpTop (n := n) (Ω := Set.univ) η i‖ * ‖q0‖ := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        (abs_inner_lpSMul_partialSquaredCutoff_le
          (differenceQuotientLp ∞ k h (A i j)) η i (u j) q0).trans <| by
            gcongr
            exact norm_differenceQuotientLp_top_le
              k (A i j) (a i j) (ha i j) (hrep i j) h hh

end SobolevSpace.GraphSpace
