/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Pointwise
public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions
import PDE.Spaces.Sobolev.Compactness.Rellich.Topology -- shake: keep
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Operators -- shake: keep

/-!
# Coefficient commutators for difference quotients

In the difference-quotient proof of interior `H²` regularity for a divergence-form operator
`-∂ᵢ(aᵢⱼ ∂ⱼu)` (Evans, PDE, §6.3.1), the weak form is tested against `-D⁻ʰ(ζ² Dʰu)` and the
discrete product rule `Dʰ(a v) = a(· + h eₖ) Dʰv + (Dʰa) v` produces the commutator terms
`(Dʰaᵢⱼ) ∂ⱼu`. We realize those terms as bounded operators on `L²(ℝ^n)` and prove
the estimates that let them be absorbed into the principal energy.

For a Lipschitz coefficient `f` with constant `C`, the forward difference quotient
`Dᵢʰ f = (f(· + h eᵢ) - f)/h` is bounded by `C` uniformly in `h ≠ 0`, so it is a global `L^∞`
multiplier; multiplying an `L²` function `v` by it costs at most `C ‖v‖`. Summing over a
Lipschitz coefficient matrix and pairing with an `L²` vector field `w` gives a bound by
`(∑ Cᵢⱼ ‖vⱼ‖) ‖wᵢ‖`, and Young's inequality `AB ≤ A²/α + (α/4) B²` splits this into a term
controlled by the coefficient constants alone and one quarter of the energy `α ∑ ‖wᵢ‖²`.

## Main results

* `coefficientDifferenceLInf`, `norm_coefficientDifferenceLInf_le`: `Dᵢʰ f` as an element of
  `L^∞(ℝ^n)` with norm at most the Lipschitz constant.
* `coefficientCommutatorL2`, `norm_coefficientCommutatorL2_le`: the multiplier `v ↦ (Dᵢʰ f) v`
  on `L²` and its bound `C ‖v‖`.
* `norm_sum_coefficientCommutatorL2_le`, `abs_sum_inner_coefficientCommutatorL2_le`: row-wise
  and full matrix commutator estimates.
* `mul_le_sq_div_add_quarter`, `abs_sum_inner_coefficientCommutatorL2_le_young`: the Young
  inequality and the absorbed form of the commutator estimate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1, pp. 327-331, step 4 of the proof,
  pp. 329-330: the product rule (17) produces the terms with `D_k^h a^{ij}` in (18), and
  Cauchy's inequality with `ε` absorbs them into the lower bound (19) from ellipticity, giving
  (20).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace
open SobolevSpace.GraphSpace.Rellich

variable {n : ℕ}

/-- A Lipschitz coefficient difference quotient, bundled as a global
`L∞` multiplier. -/
noncomputable def coefficientDifferenceLInf
    (i : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0) :
    DerivLp n ∞ Set.univ := by
  have hcont : Continuous (forwardDifference i h f) := by
    unfold forwardDifference
    exact continuous_const.mul
      ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)
  have hm : MemLp (forwardDifference i h f) ∞ (domainMeasure n Set.univ) := by
    apply memLp_top_of_bound hcont.aestronglyMeasurable C
    exact Filter.Eventually.of_forall
      (norm_forwardDifference_le_of_lipschitz i f hf hh)
  exact hm.toLp (forwardDifference i h f)

/-- The bundled coefficient difference quotient agrees almost everywhere
with its pointwise formula. -/
theorem coefficientDifferenceLInf_apply_ae
    (i : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0) :
    ((coefficientDifferenceLInf i f hf h hh : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume] forwardDifference i h f := by
  have hcont : Continuous (forwardDifference i h f) := by
    unfold forwardDifference
    exact continuous_const.mul
      ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)
  have hm : MemLp (forwardDifference i h f) ∞ (domainMeasure n Set.univ) := by
    apply memLp_top_of_bound hcont.aestronglyMeasurable C
    exact Filter.Eventually.of_forall
      (norm_forwardDifference_le_of_lipschitz i f hf hh)
  simpa [coefficientDifferenceLInf, domainMeasure] using hm.coeFn_toLp

/-- The `L∞` norm of a coefficient difference quotient is bounded by the
coefficient's Lipschitz constant. -/
theorem norm_coefficientDifferenceLInf_le
    (i : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0) :
    ‖coefficientDifferenceLInf i f hf h hh‖ ≤ C := by
  let q := forwardDifference i h f
  have hcont : Continuous q := by
    dsimp [q]
    unfold forwardDifference
    exact continuous_const.mul
      ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous)
  have hqbound : ∀ᵐ x ∂(domainMeasure n Set.univ), ‖q x‖ ≤ (C : ℝ) :=
    Filter.Eventually.of_forall
      (norm_forwardDifference_le_of_lipschitz i f hf hh)
  have hm : MemLp q ∞ (domainMeasure n Set.univ) :=
    memLp_top_of_bound hcont.aestronglyMeasurable C hqbound
  rw [show coefficientDifferenceLInf i f hf h hh = hm.toLp q by
    rfl, MeasureTheory.Lp.norm_toLp]
  have help : eLpNorm q ∞ (domainMeasure n Set.univ) ≤ ENNReal.ofReal (C : ℝ) := by
    rw [eLpNorm_exponent_top hm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound hqbound
  calc
    ENNReal.toReal (eLpNorm q ∞ (domainMeasure n Set.univ))
        ≤ ENNReal.toReal (ENNReal.ofReal (C : ℝ)) :=
      ENNReal.toReal_mono (by simp) help
    _ = C := by simp

/-- The coefficient commutator term `(Dᵢʰ a) v` in Evans's localized
difference-quotient calculation. -/
noncomputable def coefficientCommutatorL2
    (i : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0)
    (v : DerivLp n 2 Set.univ) : DerivLp n 2 Set.univ :=
  coefficientDifferenceLInf i f hf h hh • v

/-- The coefficient commutator agrees almost everywhere with the pointwise
product of the coefficient difference quotient and the `L²` function. -/
theorem coefficientCommutatorL2_apply_ae
    (i : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0)
    (v : DerivLp n 2 Set.univ) :
    ((coefficientCommutatorL2 i f hf h hh v : DerivLp n 2 Set.univ) :
        ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
      fun x ↦ forwardDifference i h f x * v x := by
  change
    ((coefficientDifferenceLInf i f hf h hh • v : DerivLp n 2 Set.univ) :
        ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
      fun x ↦ forwardDifference i h f x * v x
  have hmul :
      ((coefficientDifferenceLInf i f hf h hh • v : DerivLp n 2 Set.univ) :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
        fun x ↦ coefficientDifferenceLInf i f hf h hh x * v x := by
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (r := (2 : ENNReal))
      (coefficientDifferenceLInf i f hf h hh) v] with x hx
    simpa only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using hx
  have hq := coefficientDifferenceLInf_apply_ae i f hf h hh
  have hmul' :
      ((coefficientDifferenceLInf i f hf h hh • v : DerivLp n 2 Set.univ) :
          ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
        fun x ↦ coefficientDifferenceLInf i f hf h hh x * v x := by
    simpa [domainMeasure] using hmul
  filter_upwards [hmul', hq] with x hmul hq
  rw [hmul, hq]

/-- Multiplying an `L²` function by the difference quotient of a `C`-Lipschitz coefficient costs
at most a factor `C`, uniformly in the step `h ≠ 0`. -/
theorem norm_coefficientCommutatorL2_le
    (i : Fin n) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (h : ℝ) (hh : h ≠ 0)
    (v : DerivLp n 2 Set.univ) :
    ‖coefficientCommutatorL2 i f hf h hh v‖ ≤ C * ‖v‖ := by
  calc
    ‖coefficientCommutatorL2 i f hf h hh v‖
        ≤ ‖coefficientDifferenceLInf i f hf h hh‖ * ‖v‖ := by
      exact MeasureTheory.Lp.norm_smul_le _ _
    _ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_coefficientDifferenceLInf_le i f hf h hh) (norm_nonneg v)

/-- Row-wise matrix commutator estimate used after differentiating
`aᵢⱼ ∂ⱼu` by a coordinate difference quotient. -/
theorem norm_sum_coefficientCommutatorL2_le
    (k row : Fin n) (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (h : ℝ) (hh : h ≠ 0) (v : Fin n → DerivLp n 2 Set.univ) :
    ‖∑ j : Fin n, coefficientCommutatorL2 k (a row j) (ha row j) h hh (v j)‖ ≤
      ∑ j : Fin n, (C row j : ℝ) * ‖v j‖ := by
  calc
    ‖∑ j : Fin n, coefficientCommutatorL2 k (a row j) (ha row j) h hh (v j)‖
        ≤ ∑ j : Fin n,
          ‖coefficientCommutatorL2 k (a row j) (ha row j) h hh (v j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin n, (C row j : ℝ) * ‖v j‖ := by
      exact Finset.sum_le_sum fun j _ ↦
        norm_coefficientCommutatorL2_le k (a row j) (ha row j) h hh (v j)

/-- Bound the complete coefficient-commutator pairing against an `L²`
vector field.  In the elliptic regularity proof, `v` is the original
gradient and `w` is its coordinate difference quotient. -/
theorem abs_sum_inner_coefficientCommutatorL2_le
    (k : Fin n) (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (h : ℝ) (hh : h ≠ 0)
    (v w : Fin n → DerivLp n 2 Set.univ) :
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            coefficientCommutatorL2 k (a i j) (ha i j) h hh (v j))
          (w i)| ≤
      ∑ i : Fin n, (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) * ‖w i‖ := by
  calc
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            coefficientCommutatorL2 k (a i j) (ha i j) h hh (v j))
          (w i)|
        ≤ ∑ i : Fin n,
          |inner ℝ
            (∑ j : Fin n,
              coefficientCommutatorL2 k (a i j) (ha i j) h hh (v j))
            (w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,
        ‖∑ j : Fin n,
          coefficientCommutatorL2 k (a i j) (ha i j) h hh (v j)‖ * ‖w i‖ := by
      exact Finset.sum_le_sum fun i _ ↦
        abs_real_inner_le_norm
          (∑ j : Fin n, coefficientCommutatorL2 k (a i j) (ha i j) h hh (v j))
          (w i)
    _ ≤ ∑ i : Fin n, (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) * ‖w i‖ := by
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right
          (norm_sum_coefficientCommutatorL2_le k i a C ha h hh v)
          (norm_nonneg (w i))

/-- Young's inequality in the normalization used to absorb one error term
into one quarter of an elliptic principal energy. -/
theorem mul_le_sq_div_add_quarter {alpha : ℝ} (halpha : 0 < alpha)
    (A B : ℝ) :
    A * B ≤ A ^ 2 / alpha + (alpha / 4) * B ^ 2 := by
  apply (mul_le_mul_iff_of_pos_right (show 0 < 4 * alpha by positivity)).mp
  field_simp
  nlinarith [sq_nonneg (2 * A - alpha * B)]

/-- Young-absorbed form of the complete coefficient commutator estimate: if each `a i j` is
`C i j`-Lipschitz, `h ≠ 0` and `α > 0`, then
`|∑ᵢ ⟪∑ⱼ (Dₖʰ aᵢⱼ) vⱼ, wᵢ⟫| ≤ ∑ᵢ (∑ⱼ Cᵢⱼ ‖vⱼ‖)² / α + (α / 4) ∑ᵢ ‖wᵢ‖²`. -/
theorem abs_sum_inner_coefficientCommutatorL2_le_young
    (k : Fin n) (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (h : ℝ) (hh : h ≠ 0)
    (v w : Fin n → DerivLp n 2 Set.univ)
    {alpha : ℝ} (halpha : 0 < alpha) :
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            coefficientCommutatorL2 k (a i j) (ha i j) h hh (v j))
          (w i)| ≤
      (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ^ 2 / alpha) +
      (alpha / 4) * ∑ i : Fin n, ‖w i‖ ^ 2 := by
  calc
    |∑ i : Fin n,
        inner ℝ
          (∑ j : Fin n,
            coefficientCommutatorL2 k (a i j) (ha i j) h hh (v j))
          (w i)|
        ≤ ∑ i : Fin n,
          (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) * ‖w i‖ :=
      abs_sum_inner_coefficientCommutatorL2_le k a C ha h hh v w
    _ ≤ ∑ i : Fin n,
        ((∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ^ 2 / alpha +
          (alpha / 4) * ‖w i‖ ^ 2) := by
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_sq_div_add_quarter halpha
          (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ‖w i‖
    _ = (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) * ‖v j‖) ^ 2 / alpha) +
        (alpha / 4) * ∑ i : Fin n, ‖w i‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
end SobolevSpace.GraphSpace.DifferenceQuotient
