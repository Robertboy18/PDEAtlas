/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Bounded linear dependence of the divergence form on its coefficients

An `L∞(Ω)` coefficient matrix defines a bounded form on `H¹₀(Ω)`. This construction is
itself a bounded linear map: with the maximum norm on matrices, its norm is at most
`n²`. Thus convergence or differentiation of coefficients in `L∞` transfers to the
associated operators from `H¹₀` to `H⁻¹`.

The construction below works on any two real normed spaces equipped with
norm-nonincreasing coordinate maps into `L²(Ω)`. Derivative coordinates give the
Sobolev realization; the same bounds also apply to finite-dimensional trial spaces.

No spatial regularity of the coefficients or boundary regularity of `Ω` is needed.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

variable (U V : Type*)
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (D : Fin n → U →L[ℝ] DerivLp n 2 Ω) (hD : ∀ i u, ‖D i u‖ ≤ ‖u‖)
  (E : Fin n → V →L[ℝ] DerivLp n 2 Ω) (hE : ∀ i v, ‖E i v‖ ≤ ‖v‖)

/-- Pairing a measurable coefficient matrix with norm-nonincreasing coordinate maps
gives a form of norm at most `n²` times the maximum essential supremum of its entries. -/
theorem norm_multiplicationCoeffFormOf_le
    (a : Fin n → Fin n → DerivLp n ∞ Ω) :
    ‖variableCoeffFormOf U V D hD E hE (multiplicationCoefficientOperator a)‖ ≤
      (n : ℝ) ^ 2 * ‖a‖ := by
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
        ‖multiplicationCoefficientOperator a i j‖) ≤ (n : ℝ) ^ 2 * ‖a‖ := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖a‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact (norm_mulLpLeft_le (p := 2) (a i j)).trans
          ((norm_le_pi_norm (a i) j).trans (norm_le_pi_norm a i))
      _ = (n : ℝ) ^ 2 * ‖a‖ := by simp [pow_two, mul_assoc]
  exact (norm_variableCoeffFormOf_le U V D hD E hE
    (multiplicationCoefficientOperator a)).trans hsum

/-- The bounded linear map from measurable `L∞` matrices to forms
`(u,v) ↦ ∑ᵢⱼ ⟪aᵢⱼ Dⱼu, Eᵢv⟫`. -/
def multiplicationCoeffFormCLMOf :
    (Fin n → Fin n → DerivLp n ∞ Ω) →L[ℝ] (U →L[ℝ] V →L[ℝ] ℝ) := by
  let L : (Fin n → Fin n → DerivLp n ∞ Ω) →ₗ[ℝ]
      (U →L[ℝ] V →L[ℝ] ℝ) :=
    { toFun := fun a ↦
        variableCoeffFormOf U V D hD E hE (multiplicationCoefficientOperator a)
      map_add' := by
        intro a b
        ext u v
        simp only [variableCoeffFormOf_apply, multiplicationCoefficientOperator_apply,
          Pi.add_apply, add_apply, Lp.smul_add, inner_add_left,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext u v
        simp only [variableCoeffFormOf_apply, multiplicationCoefficientOperator_apply,
          Pi.smul_apply, smul_apply, Lp.smul_assoc,
          real_inner_smul_left, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
  refine LinearMap.mkContinuous
    (E := Fin n → Fin n → DerivLp n ∞ Ω)
    (F := U →L[ℝ] V →L[ℝ] ℝ) L ((n : ℝ) ^ 2) ?_
  intro a
  exact norm_multiplicationCoeffFormOf_le U V D hD E hE a

/-- Evaluating the coefficient map recovers the form of the multiplication operators. -/
@[simp] theorem multiplicationCoeffFormCLMOf_apply
    (a : Fin n → Fin n → DerivLp n ∞ Ω) :
    multiplicationCoeffFormCLMOf U V D hD E hE a =
      variableCoeffFormOf U V D hD E hE (multiplicationCoefficientOperator a) :=
  rfl

/-- The coefficient-to-form map is `n²`-Lipschitz for the maximum `L∞` matrix norm. -/
theorem lipschitzWith_multiplicationCoeffFormCLMOf :
    LipschitzWith ((n : ℝ≥0) ^ 2) (multiplicationCoeffFormCLMOf U V D hD E hE) := by
  apply (lipschitzWith_iff_norm_sub_le
    (E := Fin n → Fin n → DerivLp n ∞ Ω) (F := U →L[ℝ] V →L[ℝ] ℝ)).mpr
  intro a b
  have hsub :
      multiplicationCoeffFormCLMOf U V D hD E hE (a - b) =
        multiplicationCoeffFormCLMOf U V D hD E hE a -
          multiplicationCoeffFormCLMOf U V D hD E hE b :=
    LinearMap.map_sub (R := ℝ) (S := ℝ)
      (M := Fin n → Fin n → DerivLp n ∞ Ω) (M₂ := U →L[ℝ] V →L[ℝ] ℝ)
      (multiplicationCoeffFormCLMOf U V D hD E hE).toLinearMap a b
  rw [← hsub]
  simpa only [NNReal.coe_pow, NNReal.coe_natCast, multiplicationCoeffFormCLMOf_apply] using
    norm_multiplicationCoeffFormOf_le U V D hD E hE (a - b)

/-- Differentiating a matrix in `L∞` differentiates its associated bounded form by
applying the same coefficient-to-form map to the matrix derivative. -/
theorem hasDerivAt_multiplicationCoeffFormOf
    {a : ℝ → Fin n → Fin n → DerivLp n ∞ Ω}
    {adot : Fin n → Fin n → DerivLp n ∞ Ω} {t : ℝ}
    (ha : HasDerivAt a adot t) :
    HasDerivAt
      (fun s ↦ variableCoeffFormOf U V D hD E hE (multiplicationCoefficientOperator (a s)))
      (variableCoeffFormOf U V D hD E hE (multiplicationCoefficientOperator adot)) t := by
  have hmap := ContinuousLinearMap.hasFDerivAt
    (𝕜 := ℝ) (E := Fin n → Fin n → DerivLp n ∞ Ω) (F := U →L[ℝ] V →L[ℝ] ℝ)
    (multiplicationCoeffFormCLMOf U V D hD E hE) (x := a t)
  exact HasFDerivAt.comp_hasDerivAt
    (E := U →L[ℝ] V →L[ℝ] ℝ) (F := Fin n → Fin n → DerivLp n ∞ Ω) t hmap ha

end SobolevSpace.GraphSpace
