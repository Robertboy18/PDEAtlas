/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import PDE.Spaces.Sobolev.Weighted.IntegrationByParts
public import PDE.Spaces.Sobolev.Weighted.InterpolationRecursion
public import Mathlib.Algebra.Order.Chebyshev
import PDE.Analysis.Evolution.Core.EnergyEstimate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Weighted interpolation of adjacent derivatives

We prove the estimates behind weighted interpolation between derivatives of adjacent orders. Write
`‖g‖_Φ = (∫ g² Φ)^(1/2)`. For nonnegative weights with `|Φmid| ≤ A0 √(Φprev Φnext)` and
`|Φmid'| ≤ A1 √(Φprev Φmid)` and a compactly supported `C²` function `u`,

  `∫ u'² Φmid ≤ A0 ‖u‖_Φprev ‖u''‖_Φnext + A1 ‖u‖_Φprev ‖u'‖_Φmid`

on the line, on the half line `r > 0` when `u 0 = 0`, and for `∂_r` and `∂_z` on the half plane
`r > 0`. For `η > 0` and `0 < θ < 1`, Young's inequality and absorption turn a bound
`X_mid² ≤ d A0 X_prev X_next + d A1 X_prev X_mid` into
`X_mid² ≤ η X_next² + weightedInterpolationStepConstant d A0 A1 η θ * X_prev²`. We also bound the
weighted integral of one Leibniz summand against a test function.

## Main results

* `weightedInterpolation_row_base_integral_real`, `weightedInterpolation_row_base_integral_Ioi`: the
  bound above on `ℝ`, and on `(0, ∞)` when `u 0 = 0`.
* `weightedInterpolation_row_base_integral_halfPlane_radial_rz`,
  `weightedInterpolation_row_base_integral_halfPlane_axial`: the bound for `∂_r` and for `∂_z` on
  the half plane, from hypotheses on each line, with the integrability and measurability of the
  weighted terms as hypotheses.
* `weightedInterpolationStep_from_base`: the absorption step, with constant
  `weightedInterpolationStepConstant d A0 A1 η θ`.
* `weightedInterpolation_oneStep_integral_real`:
  `∫ u'² Φmid ≤ η ∫ u''² Φnext + weightedInterpolationStepConstant 1 A0 A1 η θ * ∫ u² Φprev` on `ℝ`.
* `leibniz_multifactor_weighted_integral_bound`: if `|A| ≤ A∞`, `|Fᵢ| ≤ Bᵢ` and
  `|Wi| ≤ Q √(Wstar Wi)`, then `|∫ (c A ∏ Fᵢ) (star H Wi)| ≤ c A∞ (∏ Bᵢ) Q ‖star‖_Wstar ‖H‖_Wi`.

## How it works

The row estimates start from the identity `∫ u'² Φmid = -∫ u u'' Φmid - ∫ u u' Φmid'` of
`PDE.Spaces.Sobolev.Weighted.IntegrationByParts` (`weightedInterpolation_integral_identity_real` and
its half-line and half-plane versions), whose boundary terms vanish by compact support and, at
`r = 0`, by `u 0 = 0`. `weightedInterpolation_row_base_integral_measure` then bounds the two terms
on the right by the weighted Cauchy–Schwarz inequality
`MeasureTheory.weightedInterpolation_integral_term_cauchy_measure_of_ae`, after splitting the
weights by the comparison hypotheses. `weightedInterpolationYoung_first` and
`weightedInterpolationYoung_second` are Young's inequality with parameters `(1 - θ) η` and `θ`, from
`PDE.Analysis.Evolution.mul_le_sq_div_add_mul_sq_half`, and `weightedInterpolationStep_absorption`
moves `θ X_mid²` to the left and divides by `1 - θ`. The Leibniz bound is Hölder's inequality in
`L^∞ × L² × L²`: the coefficient and all factors but `star` are bounded pointwise, and `star` and
`H` are paired by the weighted Cauchy–Schwarz inequality. The argument is that of Propositions 3 and
10 of Duruisseaux, Ganeshram, George and Anandkumar, written for general weights.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix A, Proposition 3,
  (173)-(182), pp. 38-39, for the comparison constants (173), the constant (174), the integration by
  parts (177), the adjacent-weight bounds (178)-(179) and the Young steps (181)-(182), and Appendix
  B.5, Proposition 10, (281) and (284)-(285), pp. 55-56, for the Leibniz product bound.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology

namespace SobolevSpace.Weighted

/-- `d² A0² / (4 (1 - θ)² η) + d² A1² / (4 θ (1 - θ))`, the one-step interpolation constant for `d`
rows, comparison constants `A0` and `A1` and Young parameters `η` and `θ`. -/
def weightedInterpolationStepConstant (d A0 A1 η θ : ℝ) : ℝ :=
  (d ^ 2 * A0 ^ 2) / (4 * (1 - θ) ^ 2 * η) +
    (d ^ 2 * A1 ^ 2) / (4 * θ * (1 - θ))

/--
The one-step interpolation coefficient is nonnegative whenever the
Young parameters satisfy `0 < η` and `0 < θ < 1`.
-/
theorem weightedInterpolationStepConstant_nonneg
    {d A0 A1 η θ : ℝ} (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    0 ≤ weightedInterpolationStepConstant d A0 A1 η θ := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  unfold weightedInterpolationStepConstant
  positivity

/-- If `χ > 0`, `Φprev, Φnext ≥ 0` and `|w| ≤ A √Φprev √Φnext`, then
`|a b w| ≤ χ b² Φnext + (A² / (4χ)) a² Φprev`. -/
theorem weightedInterpolation_pointwise_young
    {a b w Φprev Φnext A χ : ℝ}
    (hχ : 0 < χ)
    (hprev : 0 ≤ Φprev) (hnext : 0 ≤ Φnext)
    (hw : |w| ≤ A * √Φprev * √Φnext) :
    |a * b * w| ≤
      χ * (b ^ 2 * Φnext) + (A ^ 2 / (4 * χ)) * (a ^ 2 * Φprev) := by
  have hab : 0 ≤ |a| * |b| := mul_nonneg (abs_nonneg a) (abs_nonneg b)
  have hweighted :
      |a| * |b| * |w| ≤
        |a| * |b| * (A * √Φprev * √Φnext) :=
    mul_le_mul_of_nonneg_left hw hab
  calc
    |a * b * w| = |a| * |b| * |w| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * |b| * (A * √Φprev * √Φnext) := hweighted
    _ = (A * |a| * √Φprev) * (|b| * √Φnext) := by ring
    _ ≤ χ * (|b| * √Φnext) ^ 2 +
          (A * |a| * √Φprev) ^ 2 / (4 * χ) :=
        (PDE.Analysis.Evolution.mul_le_sq_div_add_mul_sq_half
          (by positivity : (0 : ℝ) < 2 * χ)
          (A * |a| * √Φprev) (|b| * √Φnext)).trans_eq (by ring)
    _ = χ * (b ^ 2 * Φnext) +
          (A ^ 2 / (4 * χ)) * (a ^ 2 * Φprev) := by
        simp only [mul_pow, Real.sq_sqrt hprev, Real.sq_sqrt hnext, sq_abs]
        field_simp [hχ.ne']

/-- If `0 ≤ B i` and `|F i x| ≤ B i` for every `i` and `x`, then `|∏ i, F i x| ≤ ∏ i, B i`. -/
theorem abs_finset_prod_le_prod
    {ι α : Type*} [Fintype ι]
    (F : ι → α → ℝ) (B : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hF : ∀ i x, |F i x| ≤ B i) (x : α) :
    |∏ i, F i x| ≤ ∏ i, B i := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, abs_mul]
      exact mul_le_mul (hF i x) ih (abs_nonneg _) (hB i)

/-- A single finite multifactor Leibniz summand with its exact combinatorial
coefficient abstracted as `coeff`.
-/
def multifactorLeibnizSummand
    {α ι : Type*} [Fintype ι]
    (coeff : ℝ) (A : α → ℝ) (F : ι → α → ℝ) : α → ℝ :=
  fun x ↦ coeff * A x * ∏ i, F i x

/-- Let `coeff`, `Ainf`, `Q` and every `B i` be nonnegative, `|A| ≤ Ainf`, `|F i| ≤ B i`, and let
the weights `Wi`, `Wstar ≥ 0` satisfy `|Wi| ≤ Q √Wstar √Wi`. If `star √Wstar` and `H √Wi` are in
`L²(μ)` and `star H Wi` and the full integrand are integrable, then
`|∫ (coeff A ∏ i, F i) (star H Wi) dμ|` is at most
`coeff Ainf (∏ i, B i) Q (∫ star² Wstar dμ)^(1/2) (∫ H² Wi dμ)^(1/2)`. -/
theorem leibniz_multifactor_weighted_integral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Fintype ι]
    (coeff Ainf Q : ℝ) (A : α → ℝ) (F : ι → α → ℝ) (B : ι → ℝ)
    (star H Wi Wstar : α → ℝ)
    (hcoeff : 0 ≤ coeff) (hAinf : 0 ≤ Ainf) (hQ : 0 ≤ Q)
    (hB : ∀ i, 0 ≤ B i)
    (hAbound : ∀ x, |A x| ≤ Ainf)
    (hFbound : ∀ i x, |F i x| ≤ B i)
    (hWi : ∀ x, 0 ≤ Wi x) (hWstar : ∀ x, 0 ≤ Wstar x)
    (hcompare : ∀ x,
      |Wi x| ≤ Q * √(Wstar x) * √(Wi x))
    (hstar : MemLp (fun x ↦ star x * √(Wstar x)) 2 μ)
    (hH : MemLp (fun x ↦ H x * √(Wi x)) 2 μ)
    (hcore : Integrable (fun x ↦ star x * H x * Wi x) μ)
    (hfull : Integrable
      (fun x ↦ (coeff * A x * ∏ i, F i x) * (star x * H x * Wi x)) μ) :
    |∫ x, (coeff * A x * ∏ i, F i x) * (star x * H x * Wi x) ∂μ| ≤
      coeff * Ainf * (∏ i, B i) * Q *
        √(∫ x, star x ^ 2 * Wstar x ∂μ) *
        √(∫ x, H x ^ 2 * Wi x ∂μ) := by
  have hmult : ∀ x, |coeff * A x * ∏ i, F i x| ≤ coeff * Ainf * ∏ i, B i := fun x ↦ by
    rw [abs_mul, abs_mul, abs_of_nonneg hcoeff]
    have hprod := abs_finset_prod_le_prod F B hB hFbound x
    gcongr
    exact hAbound x
  have hcore_bound := MeasureTheory.weightedInterpolation_integral_abs_term_cauchy_measure
    hQ hWstar hWi hcompare hstar hH hcore
  have hprodB : 0 ≤ ∏ i, B i := Finset.prod_nonneg fun i _ ↦ hB i
  calc
    _ ≤ coeff * Ainf * (∏ i, B i) * ∫ x, |star x * H x * Wi x| ∂μ :=
      MeasureTheory.integral_bounded_multiplier_abs_le hmult hfull hcore
    _ ≤ coeff * Ainf * (∏ i, B i) * (Q * √(∫ x, star x ^ 2 * Wstar x ∂μ) *
          √(∫ x, H x ^ 2 * Wi x ∂μ)) := by gcongr
    _ = _ := by ring

/-- The case `B i = Kinf √(E i)` of `leibniz_multifactor_weighted_integral_bound`, for factors
bounded by a Sobolev embedding constant `Kinf` times the square root of an energy `E i`. -/
theorem whole_plane_product_multifactor_certificate
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Fintype ι]
    (coeff Ainf Q Kinf : ℝ) (A : α → ℝ) (F : ι → α → ℝ) (E : ι → ℝ)
    (star H Wi Wstar : α → ℝ)
    (hcoeff : 0 ≤ coeff) (hAinf : 0 ≤ Ainf) (hQ : 0 ≤ Q)
    (hKinf : 0 ≤ Kinf)
    (hAbound : ∀ x, |A x| ≤ Ainf)
    (hFbound : ∀ i x, |F i x| ≤ Kinf * √(E i))
    (hWi : ∀ x, 0 ≤ Wi x) (hWstar : ∀ x, 0 ≤ Wstar x)
    (hcompare : ∀ x,
      |Wi x| ≤ Q * √(Wstar x) * √(Wi x))
    (hstar : MemLp (fun x ↦ star x * √(Wstar x)) 2 μ)
    (hH : MemLp (fun x ↦ H x * √(Wi x)) 2 μ)
    (hcore : Integrable (fun x ↦ star x * H x * Wi x) μ)
    (hfull : Integrable
      (fun x ↦ (coeff * A x * ∏ i, F i x) * (star x * H x * Wi x)) μ) :
    |∫ x, (coeff * A x * ∏ i, F i x) * (star x * H x * Wi x) ∂μ| ≤
      coeff * Ainf * (∏ i, Kinf * √(E i)) * Q *
        √(∫ x, star x ^ 2 * Wstar x ∂μ) *
        √(∫ x, H x ^ 2 * Wi x ∂μ) :=
  leibniz_multifactor_weighted_integral_bound coeff Ainf Q A F (fun i ↦ Kinf * √(E i)) star H Wi
    Wstar hcoeff hAinf hQ (fun i ↦ mul_nonneg hKinf (Real.sqrt_nonneg (E i))) hAbound hFbound hWi
    hWstar hcompare hstar hH hcore hfull

/-- Let `A0, A1 ≥ 0`, let the weights be nonnegative with `|Φmid| ≤ A0 √Φprev √Φnext` and
`|dΦ| ≤ A1 √Φprev √Φmid` almost everywhere, let `u0² Φprev`, `u1² Φmid`, `u2² Φnext`, `u0 u2 Φmid`
and `u0 u1 dΦ` be integrable and `u0 √Φprev`, `u1 √Φmid`, `u2 √Φnext` a.e. strongly measurable. If
`∫ u1² Φmid = -∫ u0 u2 Φmid - ∫ u0 u1 dΦ`, then
`∫ u1² Φmid ≤ A0 ‖u0‖_Φprev ‖u2‖_Φnext + A1 ‖u0‖_Φprev ‖u1‖_Φmid`, where
`‖g‖_Φ = (∫ g² Φ dμ)^(1/2)`. -/
theorem weightedInterpolation_row_base_integral_measure_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u0 u1 u2 dΦ Φprev Φmid Φnext : α → ℝ} {A0 A1 : ℝ}
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ᵐ x ∂μ,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ᵐ x ∂μ,
      |dΦ x| ≤ A1 * √(Φprev x) * √(Φmid x))
    (hprev_int : Integrable (fun x ↦ u0 x ^ 2 * Φprev x) μ)
    (hmid_int : Integrable (fun x ↦ u1 x ^ 2 * Φmid x) μ)
    (hnext_int : Integrable (fun x ↦ u2 x ^ 2 * Φnext x) μ)
    (hterm0_int : Integrable (fun x ↦ u0 x * u2 x * Φmid x) μ)
    (hterm1_int : Integrable (fun x ↦ u0 x * u1 x * dΦ x) μ)
    (hprev_meas : AEStronglyMeasurable
      (fun x ↦ u0 x * √(Φprev x)) μ)
    (hmid_meas : AEStronglyMeasurable
      (fun x ↦ u1 x * √(Φmid x)) μ)
    (hnext_meas : AEStronglyMeasurable
      (fun x ↦ u2 x * √(Φnext x)) μ)
    (hid :
      (∫ x, u1 x ^ 2 * Φmid x ∂μ) =
        -(∫ x, u0 x * u2 x * Φmid x ∂μ) -
          (∫ x, u0 x * u1 x * dΦ x ∂μ)) :
    (∫ x, u1 x ^ 2 * Φmid x ∂μ) ≤
      A0 * √(∫ x, u0 x ^ 2 * Φprev x ∂μ) *
          √(∫ x, u2 x ^ 2 * Φnext x ∂μ) +
        A1 * √(∫ x, u0 x ^ 2 * Φprev x ∂μ) *
          √(∫ x, u1 x ^ 2 * Φmid x ∂μ) := by
  have hprevLp := memLp_mul_sqrt_of_aestronglyMeasurable_of_integrable_weighted_sq hprev_meas
    hprev_nonneg hprev_int
  exact hid.trans_le ((add_le_add (neg_le_abs _) (neg_le_abs _)).trans (add_le_add
    (weightedInterpolation_integral_term_cauchy_measure_of_ae hA0 hprev_nonneg hnext_nonneg
      hcompare0 hprevLp (memLp_mul_sqrt_of_aestronglyMeasurable_of_integrable_weighted_sq
        hnext_meas hnext_nonneg hnext_int) hterm0_int)
    (weightedInterpolation_integral_term_cauchy_measure_of_ae hA1 hprev_nonneg hmid_nonneg
      hcompare1 hprevLp (memLp_mul_sqrt_of_aestronglyMeasurable_of_integrable_weighted_sq
        hmid_meas hmid_nonneg hmid_int) hterm1_int)))

/-- `weightedInterpolation_row_base_integral_measure_of_ae` with the weight comparisons holding
everywhere. -/
theorem weightedInterpolation_row_base_integral_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u0 u1 u2 dΦ Φprev Φmid Φnext : α → ℝ} {A0 A1 : ℝ}
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ x,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ x,
      |dΦ x| ≤ A1 * √(Φprev x) * √(Φmid x))
    (hprev_int : Integrable (fun x ↦ u0 x ^ 2 * Φprev x) μ)
    (hmid_int : Integrable (fun x ↦ u1 x ^ 2 * Φmid x) μ)
    (hnext_int : Integrable (fun x ↦ u2 x ^ 2 * Φnext x) μ)
    (hterm0_int : Integrable (fun x ↦ u0 x * u2 x * Φmid x) μ)
    (hterm1_int : Integrable (fun x ↦ u0 x * u1 x * dΦ x) μ)
    (hprev_meas : AEStronglyMeasurable
      (fun x ↦ u0 x * √(Φprev x)) μ)
    (hmid_meas : AEStronglyMeasurable
      (fun x ↦ u1 x * √(Φmid x)) μ)
    (hnext_meas : AEStronglyMeasurable
      (fun x ↦ u2 x * √(Φnext x)) μ)
    (hid :
      (∫ x, u1 x ^ 2 * Φmid x ∂μ) =
        -(∫ x, u0 x * u2 x * Φmid x ∂μ) -
          (∫ x, u0 x * u1 x * dΦ x ∂μ)) :
    (∫ x, u1 x ^ 2 * Φmid x ∂μ) ≤
      A0 * √(∫ x, u0 x ^ 2 * Φprev x ∂μ) *
          √(∫ x, u2 x ^ 2 * Φnext x ∂μ) +
        A1 * √(∫ x, u0 x ^ 2 * Φprev x ∂μ) *
          √(∫ x, u1 x ^ 2 * Φmid x ∂μ) :=
  weightedInterpolation_row_base_integral_measure_of_ae hA0 hA1 hprev_nonneg hmid_nonneg
    hnext_nonneg (ae_of_all μ hcompare0) (ae_of_all μ hcompare1) hprev_int hmid_int hnext_int
    hterm0_int hterm1_int hprev_meas hmid_meas hnext_meas hid

/-- If `χ > 0`, `Φprev, Φnext ≥ 0`, `|w| ≤ A √Φprev √Φnext` and `a b w`, `a² Φprev` and `b² Φnext`
are integrable on `ℝ`, then `|∫ a b w| ≤ χ ∫ b² Φnext + (A² / (4χ)) ∫ a² Φprev`. -/
theorem weightedInterpolation_integral_term_young
    {a b w Φprev Φnext : ℝ → ℝ} {A χ : ℝ}
    (hχ : 0 < χ)
    (hterm_int : Integrable (fun x ↦ a x * b x * w x))
    (hprev_int : Integrable (fun x ↦ a x ^ 2 * Φprev x))
    (hnext_int : Integrable (fun x ↦ b x ^ 2 * Φnext x))
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare : ∀ x,
      |w x| ≤ A * √(Φprev x) * √(Φnext x)) :
    |∫ x : ℝ, a x * b x * w x| ≤
      χ * (∫ x : ℝ, b x ^ 2 * Φnext x) +
        (A ^ 2 / (4 * χ)) * ∫ x : ℝ, a x ^ 2 * Φprev x := by
  have h₁ := hnext_int.const_mul χ
  have h₂ := hprev_int.const_mul (A ^ 2 / (4 * χ))
  refine (abs_integral_le_integral_abs.trans (integral_mono hterm_int.abs (h₁.add h₂) fun x ↦
    weightedInterpolation_pointwise_young hχ (hprev_nonneg x) (hnext_nonneg x)
      (hcompare x))).trans_eq ?_
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add h₁ h₂]
  rfl

/-- For `η > 0` and `θ < 1`, `d A0 Xprev Xnext ≤ (1 - θ) η Xnext² + d² A0² / (4 (1 - θ) η) Xprev²`.
-/
theorem weightedInterpolationYoung_first
    {d A0 η θ Xprev Xnext : ℝ} (hη : 0 < η) (hθ1 : θ < 1) :
    d * A0 * Xprev * Xnext ≤
      (1 - θ) * η * Xnext ^ 2 +
        (d ^ 2 * A0 ^ 2) / (4 * (1 - θ) * η) * Xprev ^ 2 := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  have hχ : 0 < (1 - θ) * η := mul_pos h1θ hη
  calc
    d * A0 * Xprev * Xnext = (d * A0 * Xprev) * Xnext := by ring
    _ ≤ ((1 - θ) * η) * Xnext ^ 2 +
          (d * A0 * Xprev) ^ 2 / (4 * ((1 - θ) * η)) :=
        (PDE.Analysis.Evolution.mul_le_sq_div_add_mul_sq_half
          (by positivity : (0 : ℝ) < 2 * ((1 - θ) * η))
          (d * A0 * Xprev) Xnext).trans_eq (by ring)
    _ =
        (1 - θ) * η * Xnext ^ 2 +
          (d ^ 2 * A0 ^ 2) / (4 * (1 - θ) * η) * Xprev ^ 2 := by
        field_simp [hη.ne', h1θ.ne']

/-- For `θ > 0`, `d A1 Xprev Xmid ≤ θ Xmid² + d² A1² / (4θ) Xprev²`. -/
theorem weightedInterpolationYoung_second
    {d A1 θ Xprev Xmid : ℝ} (hθ0 : 0 < θ) :
    d * A1 * Xprev * Xmid ≤
      θ * Xmid ^ 2 + (d ^ 2 * A1 ^ 2) / (4 * θ) * Xprev ^ 2 := by
  calc
    d * A1 * Xprev * Xmid = (d * A1 * Xprev) * Xmid := by ring
    _ ≤ θ * Xmid ^ 2 + (d * A1 * Xprev) ^ 2 / (4 * θ) :=
        (PDE.Analysis.Evolution.mul_le_sq_div_add_mul_sq_half
          (by positivity : (0 : ℝ) < 2 * θ)
          (d * A1 * Xprev) Xmid).trans_eq (by ring)
    _ = θ * Xmid ^ 2 + (d ^ 2 * A1 ^ 2) / (4 * θ) * Xprev ^ 2 := by
        field_simp [hθ0.ne']

/-- For `η > 0` and `0 < θ < 1`, the bound `Xmid² ≤ d A0 Xprev Xnext + d A1 Xprev Xmid` and the
inequalities of `weightedInterpolationYoung_first` and `weightedInterpolationYoung_second` give
`Xmid² ≤ η Xnext² + weightedInterpolationStepConstant d A0 A1 η θ * Xprev²`. -/
theorem weightedInterpolationStep_absorption
    {d A0 A1 η θ Xprev Xmid Xnext : ℝ}
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hbase :
      Xmid ^ 2 ≤
        d * A0 * Xprev * Xnext + d * A1 * Xprev * Xmid)
    (hyoung0 :
      d * A0 * Xprev * Xnext ≤
        (1 - θ) * η * Xnext ^ 2 +
          (d ^ 2 * A0 ^ 2) / (4 * (1 - θ) * η) * Xprev ^ 2)
    (hyoung1 :
      d * A1 * Xprev * Xmid ≤
        θ * Xmid ^ 2 + (d ^ 2 * A1 ^ 2) / (4 * θ) * Xprev ^ 2) :
    Xmid ^ 2 ≤
      η * Xnext ^ 2 + weightedInterpolationStepConstant d A0 A1 η θ * Xprev ^ 2 := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  have hK : (1 - θ) * weightedInterpolationStepConstant d A0 A1 η θ =
      (d ^ 2 * A0 ^ 2) / (4 * (1 - θ) * η) + (d ^ 2 * A1 ^ 2) / (4 * θ) := by
    unfold weightedInterpolationStepConstant
    field_simp
  refine le_of_mul_le_mul_left ?_ h1θ
  linarith [congrArg (· * Xprev ^ 2) hK]

/-- For `η > 0` and `0 < θ < 1`, `Xmid² ≤ d A0 Xprev Xnext + d A1 Xprev Xmid` implies
`Xmid² ≤ η Xnext² + weightedInterpolationStepConstant d A0 A1 η θ * Xprev²`. -/
theorem weightedInterpolationStep_from_base
    {d A0 A1 η θ Xprev Xmid Xnext : ℝ}
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hbase :
      Xmid ^ 2 ≤
        d * A0 * Xprev * Xnext + d * A1 * Xprev * Xmid) :
    Xmid ^ 2 ≤
      η * Xnext ^ 2 + weightedInterpolationStepConstant d A0 A1 η θ * Xprev ^ 2 :=
  weightedInterpolationStep_absorption hη hθ0 hθ1 hbase
    (weightedInterpolationYoung_first hη hθ1)
    (weightedInterpolationYoung_second hθ0)

/-- For `η > 0` and `0 < θ < 1`,
`Emid ≤ (1 - θ) η Enext + A0² / (4 (1 - θ) η) Eprev + θ Emid + A1² / (4θ) Eprev` implies
`Emid ≤ η Enext + weightedInterpolationStepConstant 1 A0 A1 η θ * Eprev`. -/
theorem weightedInterpolationEnergy_absorption
    {Eprev Emid Enext A0 A1 η θ : ℝ}
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hbase :
      Emid ≤
        ((1 - θ) * η) * Enext + (A0 ^ 2 / (4 * ((1 - θ) * η))) * Eprev +
          (θ * Emid + (A1 ^ 2 / (4 * θ)) * Eprev)) :
    Emid ≤ η * Enext + weightedInterpolationStepConstant 1 A0 A1 η θ * Eprev := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  have hK : (1 - θ) * weightedInterpolationStepConstant 1 A0 A1 η θ =
      A0 ^ 2 / (4 * ((1 - θ) * η)) + A1 ^ 2 / (4 * θ) := by
    unfold weightedInterpolationStepConstant
    field_simp
  refine le_of_mul_le_mul_left ?_ h1θ
  linarith [congrArg (· * Eprev) hK]

/-- For `η > 0`, `0 < θ < 1` and nonnegative weights with `|Φmid| ≤ A0 √Φprev √Φnext` and
`|dΦ| ≤ A1 √Φprev √Φmid`, if `u0² Φprev`, `u1² Φmid`, `u2² Φnext`, `u0 u2 Φmid` and `u0 u1 dΦ` are
integrable on `ℝ` and `∫ u1² Φmid = -∫ u0 u2 Φmid - ∫ u0 u1 dΦ`, then
`∫ u1² Φmid ≤ η ∫ u2² Φnext + weightedInterpolationStepConstant 1 A0 A1 η θ * ∫ u0² Φprev`. -/
theorem weightedInterpolation_oneStep_integral_core
    {u0 u1 u2 dΦ Φprev Φmid Φnext : ℝ → ℝ} {A0 A1 η θ : ℝ}
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_int : Integrable (fun x ↦ u0 x ^ 2 * Φprev x))
    (hmid_int : Integrable (fun x ↦ u1 x ^ 2 * Φmid x))
    (hnext_int : Integrable (fun x ↦ u2 x ^ 2 * Φnext x))
    (hterm0_int : Integrable (fun x ↦ u0 x * u2 x * Φmid x))
    (hterm1_int : Integrable (fun x ↦ u0 x * u1 x * dΦ x))
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ x,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ x,
      |dΦ x| ≤ A1 * √(Φprev x) * √(Φmid x))
    (hid :
      (∫ x : ℝ, u1 x ^ 2 * Φmid x) =
        -(∫ x : ℝ, u0 x * u2 x * Φmid x) -
          (∫ x : ℝ, u0 x * u1 x * dΦ x)) :
    (∫ x : ℝ, u1 x ^ 2 * Φmid x) ≤
      η * (∫ x : ℝ, u2 x ^ 2 * Φnext x) +
        weightedInterpolationStepConstant 1 A0 A1 η θ *
          ∫ x : ℝ, u0 x ^ 2 * Φprev x := by
  exact weightedInterpolationEnergy_absorption hη hθ0 hθ1 (hid.trans_le
    ((add_le_add (neg_le_abs _) (neg_le_abs _)).trans (add_le_add
      (weightedInterpolation_integral_term_young (mul_pos (sub_pos.mpr hθ1) hη) hterm0_int
        hprev_int hnext_int hprev_nonneg hnext_nonneg hcompare0)
      (weightedInterpolation_integral_term_young hθ0 hterm1_int hprev_int hmid_int hprev_nonneg
        hmid_nonneg hcompare1))))

/-- The five weighted products of one interpolation step are integrable for a compactly supported
`C²` function and `C¹` weights. -/
private theorem integrable_interpolation_terms {u Φprev Φmid Φnext : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hΦprev : ContDiff ℝ 1 Φprev) (hΦmid : ContDiff ℝ 1 Φmid)
    (hΦnext : ContDiff ℝ 1 Φnext) (hcu : HasCompactSupport u) :
    Integrable (fun x ↦ u x ^ 2 * Φprev x) ∧ Integrable (fun x ↦ deriv u x ^ 2 * Φmid x) ∧
      Integrable (fun x ↦ deriv (deriv u) x ^ 2 * Φnext x) ∧
      Integrable (fun x ↦ u x * deriv (deriv u) x * Φmid x) ∧
      Integrable (fun x ↦ u x * deriv u x * deriv Φmid x) := by
  have hdu : ContDiff ℝ 1 (deriv u) := by simpa using (hu.deriv' : ContDiff ℝ 1 (deriv u))
  have hd2 := hdu.continuous_deriv le_rfl
  have hsq {f : ℝ → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (fun x ↦ f x ^ 2) :=
    hf.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  exact ⟨((hu.continuous.pow 2).mul hΦprev.continuous).integrable_of_hasCompactSupport
      (hsq hcu).mul_right,
    ((hdu.continuous.pow 2).mul hΦmid.continuous).integrable_of_hasCompactSupport
      (hsq hcu.deriv).mul_right,
    ((hd2.pow 2).mul hΦnext.continuous).integrable_of_hasCompactSupport
      (hsq hcu.deriv.deriv).mul_right,
    ((hu.continuous.mul hd2).mul hΦmid.continuous).integrable_of_hasCompactSupport
      hcu.mul_right.mul_right,
    ((hu.continuous.mul hdu.continuous).mul
      (hΦmid.continuous_deriv le_rfl)).integrable_of_hasCompactSupport hcu.mul_right.mul_right⟩

/-- Let `u` be `C²` with compact support and the weights `C¹` and nonnegative with
`|Φmid| ≤ A0 √Φprev √Φnext` and `|Φmid'| ≤ A1 √Φprev √Φmid`. Then for `η > 0` and `0 < θ < 1`,
`∫ u'² Φmid ≤ η ∫ u''² Φnext + weightedInterpolationStepConstant 1 A0 A1 η θ * ∫ u² Φprev` on `ℝ`.
-/
theorem weightedInterpolation_oneStep_integral_real
    {u Φprev Φmid Φnext : ℝ → ℝ} {A0 A1 η θ : ℝ}
    (hu : ContDiff ℝ 2 u)
    (hΦprev : ContDiff ℝ 1 Φprev)
    (hΦmid : ContDiff ℝ 1 Φmid)
    (hΦnext : ContDiff ℝ 1 Φnext)
    (hcu : HasCompactSupport u)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ x,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ x,
      |deriv Φmid x| ≤ A1 * √(Φprev x) * √(Φmid x)) :
    (∫ x : ℝ, deriv u x ^ 2 * Φmid x) ≤
      η * (∫ x : ℝ, deriv (deriv u) x ^ 2 * Φnext x) +
        weightedInterpolationStepConstant 1 A0 A1 η θ *
          ∫ x : ℝ, u x ^ 2 * Φprev x := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := integrable_interpolation_terms hu hΦprev hΦmid hΦnext hcu
  exact weightedInterpolation_oneStep_integral_core hη hθ0 hθ1 h₀ h₁ h₂ h₃ h₄ hprev_nonneg
    hmid_nonneg hnext_nonneg hcompare0 hcompare1
    (weightedInterpolation_integral_identity_real hu hΦmid hcu)

/-- Let `u` be `C²` with compact support, `A0, A1 ≥ 0`, and the weights `C¹` and nonnegative with
`|Φmid| ≤ A0 √Φprev √Φnext` and `|Φmid'| ≤ A1 √Φprev √Φmid`. Then on `ℝ`,
`∫ u'² Φmid ≤ A0 ‖u‖_Φprev ‖u''‖_Φnext + A1 ‖u‖_Φprev ‖u'‖_Φmid`, where `‖g‖_Φ = (∫ g² Φ)^(1/2)`. -/
theorem weightedInterpolation_row_base_integral_real
    {u Φprev Φmid Φnext : ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ContDiff ℝ 2 u)
    (hΦprev : ContDiff ℝ 1 Φprev)
    (hΦmid : ContDiff ℝ 1 Φmid)
    (hΦnext : ContDiff ℝ 1 Φnext)
    (hcu : HasCompactSupport u)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ x,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ x,
      |deriv Φmid x| ≤ A1 * √(Φprev x) * √(Φmid x)) :
    (∫ x : ℝ, deriv u x ^ 2 * Φmid x) ≤
      A0 * √(∫ x : ℝ, u x ^ 2 * Φprev x) *
          √(∫ x : ℝ, deriv (deriv u) x ^ 2 * Φnext x) +
        A1 * √(∫ x : ℝ, u x ^ 2 * Φprev x) *
          √(∫ x : ℝ, deriv u x ^ 2 * Φmid x) := by
  have hdu : ContDiff ℝ 1 (deriv u) := by simpa using (hu.deriv' : ContDiff ℝ 1 (deriv u))
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := integrable_interpolation_terms hu hΦprev hΦmid hΦnext hcu
  exact weightedInterpolation_row_base_integral_measure hA0 hA1 hprev_nonneg hmid_nonneg
    hnext_nonneg hcompare0 hcompare1 h₀ h₁ h₂ h₃ h₄
    (hu.continuous.mul (Real.continuous_sqrt.comp hΦprev.continuous)).aestronglyMeasurable
    (hdu.continuous.mul (Real.continuous_sqrt.comp hΦmid.continuous)).aestronglyMeasurable
    ((hdu.continuous_deriv le_rfl).mul
      (Real.continuous_sqrt.comp hΦnext.continuous)).aestronglyMeasurable
    (weightedInterpolation_integral_identity_real hu hΦmid hcu)

/-- The bound of `weightedInterpolation_row_base_integral_real` with all integrals over `(0, ∞)`,
when also `u 0 = 0`. -/
theorem weightedInterpolation_row_base_integral_Ioi
    {u Φprev Φmid Φnext : ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ContDiff ℝ 2 u)
    (hΦprev : ContDiff ℝ 1 Φprev)
    (hΦmid : ContDiff ℝ 1 Φmid)
    (hΦnext : ContDiff ℝ 1 Φnext)
    (hcu : HasCompactSupport u) (hu0 : u 0 = 0)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hmid_nonneg : ∀ x, 0 ≤ Φmid x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare0 : ∀ x,
      |Φmid x| ≤ A0 * √(Φprev x) * √(Φnext x))
    (hcompare1 : ∀ x,
      |deriv Φmid x| ≤ A1 * √(Φprev x) * √(Φmid x)) :
    (∫ x in Set.Ioi (0 : ℝ), deriv u x ^ 2 * Φmid x) ≤
      A0 * √(∫ x in Set.Ioi (0 : ℝ), u x ^ 2 * Φprev x) *
          √(∫ x in Set.Ioi (0 : ℝ),
            deriv (deriv u) x ^ 2 * Φnext x) +
        A1 * √(∫ x in Set.Ioi (0 : ℝ), u x ^ 2 * Φprev x) *
          √(∫ x in Set.Ioi (0 : ℝ), deriv u x ^ 2 * Φmid x) := by
  have hdu : ContDiff ℝ 1 (deriv u) := by simpa using (hu.deriv' : ContDiff ℝ 1 (deriv u))
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := integrable_interpolation_terms hu hΦprev hΦmid hΦnext hcu
  exact weightedInterpolation_row_base_integral_measure hA0 hA1 hprev_nonneg hmid_nonneg
    hnext_nonneg hcompare0 hcompare1 h₀.integrableOn h₁.integrableOn h₂.integrableOn
    h₃.integrableOn h₄.integrableOn
    (hu.continuous.mul (Real.continuous_sqrt.comp hΦprev.continuous)).aestronglyMeasurable
    (hdu.continuous.mul (Real.continuous_sqrt.comp hΦmid.continuous)).aestronglyMeasurable
    ((hdu.continuous_deriv le_rfl).mul
      (Real.continuous_sqrt.comp hΦnext.continuous)).aestronglyMeasurable
    (weightedInterpolation_integral_identity_Ioi hu hΦmid hcu hu0)

/-- The bound of `weightedInterpolation_row_base_integral_Ioi` for the radial derivative on the half
plane `r > 0`, with integrals for the product measure in the order `(z, r)`. For each `z`,
`r ↦ u r z` is `C²` with compact support and `u 0 z = 0` and `r ↦ Φmid r z` is `C¹`; the
integrability and measurability of the weighted terms are hypotheses. -/
theorem weightedInterpolation_row_base_integral_halfPlane_radial
    {u Φprev Φmid Φnext : ℝ → ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ∀ z, ContDiff ℝ 2 (fun r ↦ u r z))
    (hΦmid : ∀ z, ContDiff ℝ 1 (fun r ↦ Φmid r z))
    (hcu : ∀ z, HasCompactSupport (fun r ↦ u r z))
    (hu0 : ∀ z, u 0 z = 0)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * √(Φprev r z) * √(Φnext r z))
    (hcompare1 : ∀ r z,
      |deriv (fun s ↦ Φmid s z) r| ≤
        A1 * √(Φprev r z) * √(Φmid r z))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.2 p.1 ^ 2 * Φprev p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦
        deriv (fun r ↦ u r p.1) p.2 ^ 2 * Φmid p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun r ↦ u r p.1)) p.2 ^ 2 * Φnext p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦
        u p.2 p.1 * deriv (deriv (fun r ↦ u r p.1)) p.2 * Φmid p.2 p.1)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦
        u p.2 p.1 * deriv (fun r ↦ u r p.1) p.2 *
          deriv (fun r ↦ Φmid r p.1) p.2)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u p.2 p.1 * √(Φprev p.2 p.1))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (fun r ↦ u r p.1) p.2 * √(Φmid p.2 p.1))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun r ↦ u r p.1)) p.2 * √(Φnext p.2 p.1))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) :
    (∫ p : ℝ × ℝ,
      deriv (fun r ↦ u r p.1) p.2 ^ 2 * Φmid p.2 p.1
        ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) ≤
      A0 * √(∫ p : ℝ × ℝ, u p.2 p.1 ^ 2 * Φprev p.2 p.1
            ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) *
        √(∫ p : ℝ × ℝ,
            deriv (deriv (fun r ↦ u r p.1)) p.2 ^ 2 * Φnext p.2 p.1
              ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) +
      A1 * √(∫ p : ℝ × ℝ, u p.2 p.1 ^ 2 * Φprev p.2 p.1
            ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) *
        √(∫ p : ℝ × ℝ,
            deriv (fun r ↦ u r p.1) p.2 ^ 2 * Φmid p.2 p.1
              ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ))))) := by
  exact weightedInterpolation_row_base_integral_measure hA0 hA1 (fun p ↦ hprev_nonneg p.2 p.1)
    (fun p ↦ hmid_nonneg p.2 p.1) (fun p ↦ hnext_nonneg p.2 p.1) (fun p ↦ hcompare0 p.2 p.1)
    (fun p ↦ hcompare1 p.2 p.1) hprev_int hmid_int hnext_int hterm0_int hterm1_int hprev_meas
    hmid_meas hnext_meas
    (weightedInterpolation_integral_identity_halfPlane_radial hu hΦmid hcu hu0 hmid_int
      hterm0_int hterm1_int)

/-- `weightedInterpolation_row_base_integral_halfPlane_radial` with the coordinates in the order
`(r, z)`. -/
theorem weightedInterpolation_row_base_integral_halfPlane_radial_rz
    {u Φprev Φmid Φnext : ℝ → ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ∀ z, ContDiff ℝ 2 (fun r ↦ u r z))
    (hΦmid : ∀ z, ContDiff ℝ 1 (fun r ↦ Φmid r z))
    (hcu : ∀ z, HasCompactSupport (fun r ↦ u r z))
    (hu0 : ∀ z, u 0 z = 0)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * √(Φprev r z) * √(Φnext r z))
    (hcompare1 : ∀ r z,
      |deriv (fun s ↦ Φmid s z) r| ≤
        A1 * √(Φprev r z) * √(Φmid r z))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦
        deriv (fun r ↦ u r p.2) p.1 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun r ↦ u r p.2)) p.1 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (deriv (fun r ↦ u r p.2)) p.1 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (fun r ↦ u r p.2) p.1 *
          deriv (fun r ↦ Φmid r p.2) p.1)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * √(Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (fun r ↦ u r p.2) p.1 * √(Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun r ↦ u r p.2)) p.1 * √(Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∫ p : ℝ × ℝ,
      deriv (fun r ↦ u r p.2) p.1 ^ 2 * Φmid p.1 p.2
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) ≤
      A0 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) *
        √(∫ p : ℝ × ℝ,
            deriv (deriv (fun r ↦ u r p.2)) p.1 ^ 2 * Φnext p.1 p.2
              ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) +
      A1 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) *
        √(∫ p : ℝ × ℝ,
            deriv (fun r ↦ u r p.2) p.1 ^ 2 * Φmid p.1 p.2
              ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
  exact weightedInterpolation_row_base_integral_measure hA0 hA1 (fun p ↦ hprev_nonneg p.1 p.2)
    (fun p ↦ hmid_nonneg p.1 p.2) (fun p ↦ hnext_nonneg p.1 p.2) (fun p ↦ hcompare0 p.1 p.2)
    (fun p ↦ hcompare1 p.1 p.2) hprev_int hmid_int hnext_int hterm0_int hterm1_int hprev_meas
    hmid_meas hnext_meas
    (weightedInterpolation_integral_identity_halfPlane_radial_rz hu hΦmid hcu hu0 hmid_int
      hterm0_int hterm1_int)

/-- The bound of `weightedInterpolation_row_base_integral_real` for the axial derivative on the half
plane `r > 0`, with integrals for the product measure in the order `(r, z)`. For each `r`,
`z ↦ u r z` is `C²` with compact support and `z ↦ Φmid r z` is `C¹`; the integrability and
measurability of the weighted terms are hypotheses, and no condition at the axis is needed. -/
theorem weightedInterpolation_row_base_integral_halfPlane_axial
    {u Φprev Φmid Φnext : ℝ → ℝ → ℝ} {A0 A1 : ℝ}
    (hu : ∀ r, ContDiff ℝ 2 (fun z ↦ u r z))
    (hΦmid : ∀ r, ContDiff ℝ 1 (fun z ↦ Φmid r z))
    (hcu : ∀ r, HasCompactSupport (fun z ↦ u r z))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * √(Φprev r z) * √(Φnext r z))
    (hcompare1 : ∀ r z,
      |deriv (fun s ↦ Φmid r s) z| ≤
        A1 * √(Φprev r z) * √(Φmid r z))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦
        deriv (fun z ↦ u p.1 z) p.2 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun z ↦ u p.1 z)) p.2 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (deriv (fun z ↦ u p.1 z)) p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦
        u p.1 p.2 * deriv (fun z ↦ u p.1 z) p.2 *
          deriv (fun z ↦ Φmid p.1 z) p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ u p.1 p.2 * √(Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (fun z ↦ u p.1 z) p.2 * √(Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        deriv (deriv (fun z ↦ u p.1 z)) p.2 * √(Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∫ p : ℝ × ℝ,
      deriv (fun z ↦ u p.1 z) p.2 ^ 2 * Φmid p.1 p.2
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) ≤
      A0 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) *
        √(∫ p : ℝ × ℝ,
            deriv (deriv (fun z ↦ u p.1 z)) p.2 ^ 2 * Φnext p.1 p.2
              ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) +
      A1 * √(∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Φprev p.1 p.2
            ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) *
        √(∫ p : ℝ × ℝ,
            deriv (fun z ↦ u p.1 z) p.2 ^ 2 * Φmid p.1 p.2
              ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) := by
  exact weightedInterpolation_row_base_integral_measure hA0 hA1 (fun p ↦ hprev_nonneg p.1 p.2)
    (fun p ↦ hmid_nonneg p.1 p.2) (fun p ↦ hnext_nonneg p.1 p.2) (fun p ↦ hcompare0 p.1 p.2)
    (fun p ↦ hcompare1 p.1 p.2) hprev_int hmid_int hnext_int hterm0_int hterm1_int hprev_meas
    hmid_meas hnext_meas
    (weightedInterpolation_integral_identity_halfPlane_axial hu hΦmid hcu hmid_int hterm0_int
      hterm1_int)

end SobolevSpace.Weighted
