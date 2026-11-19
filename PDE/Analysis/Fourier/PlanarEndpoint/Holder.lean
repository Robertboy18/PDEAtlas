/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.PlanarEndpoint
import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import CAS.ExactTactic

/-!
# Hölder estimates from planar Fourier energy

The phase difference is bounded by `2 ‖x - y‖^γ ‖ξ‖^γ`. Cauchy–Schwarz
against `orderTwoHolderKernel γ = (1 + ‖ξ‖²)^((γ - 2)/2)` then bounds the
inverse Fourier difference by the order-two Bessel energy for `0 < γ < 1`.
The final theorem uses the Fourier transform of continuous integrable
data with integrable transform, in the `(2π)⁻²` inversion convention of
`PDE.Analysis.Fourier.PlanarEndpoint`.

The Fourier normalization is (218) of Duruisseaux, Ganeshram, George and Anandkumar. The
estimate follows from Fourier inversion, the phase increment bound, and Cauchy–Schwarz.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.1, (218), p. 45.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open LineDeriv
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap Topology

namespace PDE.Analysis.Fourier

/-- The `L²` kernel in the Fourier proof of
`H²(ℝ²) → C^{0,γ}(ℝ²)`.
-/
noncomputable def orderTwoHolderKernel (γ : ℝ) (ξ : (ℝ^2)) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ ((γ - 2) / 2)

/-- Fractional continuity of the unit complex phase.  The deliberately simple
constant `2` is uniform for every exponent in `(0,1]`.
-/
theorem norm_complex_exp_I_mul_sub_le_two_mul_rpow
    (γ a b : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤
      2 * |a - b| ^ γ := by
  have hnorm (c : ℝ) : ‖Complex.exp (Complex.I * c)‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hlinear :
      ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
    have heq : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
        Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * (a - b)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      ring_nf
    rw [heq, norm_mul, hnorm, one_mul]
    simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rcases le_total |a - b| 1 with hab | hab
  · exact hlinear.trans <| (Real.self_le_rpow_of_le_one (abs_nonneg _) hab hγ1).trans <|
      le_mul_of_one_le_left (by positivity) one_le_two
  · calc _ ≤ ‖Complex.exp (Complex.I * a)‖ + ‖Complex.exp (Complex.I * b)‖ := norm_sub_le _ _
      _ = 2 * 1 := by rw [hnorm, hnorm]; norm_num
      _ ≤ 2 * |a - b| ^ γ := by gcongr; exact Real.one_le_rpow hab hγ0.le

/-- Fourier phases on the profile plane are Hölder in the spatial variable,
with frequency growth `‖ξ‖^γ`.
-/
theorem norm_profile_fourier_phase_sub_le
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (x y ξ : (ℝ^2)) :
    ‖Complex.exp (Complex.I *
        ((x 0 * ξ 0 + x 1 * ξ 1 : ℝ) : ℂ)) -
        Complex.exp (Complex.I *
          ((y 0 * ξ 0 + y 1 * ξ 1 : ℝ) : ℂ))‖ ≤
      2 * ‖x - y‖ ^ γ * ‖ξ‖ ^ γ := by
  have hphase := norm_complex_exp_I_mul_sub_le_two_mul_rpow
    γ (x 0 * ξ 0 + x 1 * ξ 1) (y 0 * ξ 0 + y 1 * ξ 1)
    hγ0 hγ1
  have hinner :
      |(x 0 * ξ 0 + x 1 * ξ 1) - (y 0 * ξ 0 + y 1 * ξ 1)| ≤
        ‖x - y‖ * ‖ξ‖ := by
    rw [← PDE.Analysis.Fourier.point_inner_eq_coordinates,
      ← PDE.Analysis.Fourier.point_inner_eq_coordinates, ← inner_sub_left]
    exact abs_real_inner_le_norm (x - y) ξ
  have hrpow := Real.rpow_le_rpow (abs_nonneg _) hinner hγ0.le
  calc
    _ ≤ 2 * |(x 0 * ξ 0 + x 1 * ξ 1) -
        (y 0 * ξ 0 + y 1 * ξ 1)| ^ γ := hphase
    _ ≤ 2 * (‖x - y‖ * ‖ξ‖) ^ γ :=
      mul_le_mul_of_nonneg_left hrpow (by norm_num)
    _ = 2 * ‖x - y‖ ^ γ * ‖ξ‖ ^ γ := by
      rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      ring

/-- The Fourier Hölder kernel is square-integrable precisely in the range
needed here, `γ < 1`.
-/
theorem integrable_orderTwoHolderKernel_sq
    (γ : ℝ) (hγ1 : γ < 1) :
    Integrable (fun ξ : (ℝ^2) ↦ orderTwoHolderKernel γ ξ ^ 2) := by
  have hdim : (Module.finrank ℝ (ℝ^2) : ℝ) < 4 - 2 * γ := by
    norm_num [finrank_euclideanSpace_fin]
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (E := (ℝ^2)) (μ := volume) hdim).congr
    (Eventually.of_forall fun ξ ↦ ?_)
  dsimp only [orderTwoHolderKernel]
  cas

/-- The frequency factor from the phase difference splits into the square
integrable Hölder kernel and the order-two Bessel weight.
-/
theorem norm_rpow_le_orderTwoHolderKernel_mul
    (γ : ℝ) (hγ0 : 0 < γ) (ξ : (ℝ^2)) :
    ‖ξ‖ ^ γ ≤ orderTwoHolderKernel γ ξ * (1 + ‖ξ‖ ^ 2) := by
  have hbase : ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by linarith
  have hrpow := Real.rpow_le_rpow (sq_nonneg ‖ξ‖) hbase (by positivity : 0 ≤ γ / 2)
  have hleft : (‖ξ‖ ^ 2) ^ (γ / 2) = ‖ξ‖ ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
    congr 1
    ring
  have hright :
      (1 + ‖ξ‖ ^ 2) ^ (γ / 2) =
        orderTwoHolderKernel γ ξ * (1 + ‖ξ‖ ^ 2) := by
    calc
      (1 + ‖ξ‖ ^ 2) ^ (γ / 2) =
          (1 + ‖ξ‖ ^ 2) ^ ((γ - 2) / 2 + 1) := by
            congr 1
            ring
      _ = (1 + ‖ξ‖ ^ 2) ^ ((γ - 2) / 2) *
          (1 + ‖ξ‖ ^ 2) ^ (1 : ℝ) :=
            Real.rpow_add (by positivity) _ _
      _ = orderTwoHolderKernel γ ξ * (1 + ‖ξ‖ ^ 2) := by
            rw [Real.rpow_one]
            rfl
  rw [hleft, hright] at hrpow
  exact hrpow

/-- Cauchy–Schwarz estimate for the difference of two inverse Fourier
phases against order-two Bessel energy.
-/
theorem norm_integral_profile_fourier_phase_sub_le
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Fhat : (ℝ^2) → ℂ) (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun ξ : (ℝ^2) ↦
      (1 + ‖ξ‖ ^ 2) ^ 2 * ‖Fhat ξ‖ ^ 2))
    (x y : (ℝ^2)) :
    ‖∫ ξ : (ℝ^2),
        (Complex.exp (Complex.I *
            ((x 0 * ξ 0 + x 1 * ξ 1 : ℝ) : ℂ)) -
          Complex.exp (Complex.I *
            ((y 0 * ξ 0 + y 1 * ξ 1 : ℝ) : ℂ))) * Fhat ξ‖ ≤
      2 * ‖x - y‖ ^ γ *
        (√(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) *
          √(∫ ξ : (ℝ^2),
            (1 + ‖ξ‖ ^ 2) ^ 2 * ‖Fhat ξ‖ ^ 2)) := by
  let a : (ℝ^2) → ℝ := fun ξ ↦ orderTwoHolderKernel γ ξ
  let b : (ℝ^2) → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) * ‖Fhat ξ‖
  have haMeas : AEStronglyMeasurable a := ((continuous_const.add (continuous_norm.pow 2)).rpow_const
    fun ξ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne').aestronglyMeasurable
  have ha : MemLp a 2 := (memLp_two_iff_integrable_sq haMeas).2
    (by simpa [a] using integrable_orderTwoHolderKernel_sq γ hγ1)
  have hb : MemLp b 2 := (memLp_two_iff_integrable_sq
    ((by fun_prop : Continuous fun ξ : (ℝ^2) ↦ 1 + ‖ξ‖ ^ 2).aestronglyMeasurable.mul
      hFhat.norm)).2 (hEnergy.congr (.of_forall fun ξ ↦ by simp [mul_pow]))
  have habInt : Integrable (fun ξ ↦ a ξ * b ξ) := ha.integrable_mul hb
  have hpoint (ξ : (ℝ^2)) :
      ‖(Complex.exp (Complex.I * ((x 0 * ξ 0 + x 1 * ξ 1 : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((y 0 * ξ 0 + y 1 * ξ 1 : ℝ) : ℂ))) * Fhat ξ‖ ≤
        2 * ‖x - y‖ ^ γ * (a ξ * b ξ) := by
    have hk := norm_rpow_le_orderTwoHolderKernel_mul γ hγ0 ξ
    calc _ ≤ 2 * ‖x - y‖ ^ γ * ‖ξ‖ ^ γ * ‖Fhat ξ‖ := by
          rw [norm_mul]
          gcongr
          exact norm_profile_fourier_phase_sub_le γ hγ0 hγ1.le x y ξ
      _ ≤ 2 * ‖x - y‖ ^ γ * (orderTwoHolderKernel γ ξ * (1 + ‖ξ‖ ^ 2)) * ‖Fhat ξ‖ := by gcongr
      _ = 2 * ‖x - y‖ ^ γ * (a ξ * b ξ) := by simp only [a, b]; ring
  calc _ ≤ ∫ ξ, 2 * ‖x - y‖ ^ γ * (a ξ * b ξ) :=
        norm_integral_le_of_norm_le (habInt.const_mul _) (.of_forall hpoint)
    _ = 2 * ‖x - y‖ ^ γ * ∫ ξ, a ξ * b ξ := integral_const_mul _ _
    _ ≤ 2 * ‖x - y‖ ^ γ * (√(∫ ξ, a ξ ^ 2) * √(∫ ξ, b ξ ^ 2)) := by
      gcongr
      exact (integral_mono habInt habInt.abs fun ξ ↦ le_abs_self _).trans
        (integral_abs_mul_le_sqrt_integral_sq ha hb)
    _ = _ := by simp [a, b, mul_pow]

/-- Inverse Fourier functions with factor `(2π)⁻²` and order-two Bessel energy
are globally `γ`-Hölder for every `0 < γ < 1`.
-/
theorem angularFourier_orderTwo_holder
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (f : (ℝ^2) → ℂ) (hfcont : Continuous f) (hf : Integrable f)
    (hFourier : Integrable (𝓕 f))
    (hEnergy : Integrable (fun ξ : (ℝ^2) ↦
      (1 + ‖ξ‖ ^ 2) ^ 2 * ‖PDE.Analysis.Fourier.angularFourierTransform2D f ξ‖ ^ 2)) :
    ∀ x y : (ℝ^2),
      ‖f x - f y‖ ≤
        (1 / Real.pi) * √(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) *
          √(((2 * Real.pi) ^ 2)⁻¹ *
            ∫ ξ : (ℝ^2),
              (1 + ‖ξ‖ ^ 2) ^ 2 *
                ‖PDE.Analysis.Fourier.angularFourierTransform2D f ξ‖ ^ 2) *
          ‖x - y‖ ^ γ := by
  set Fhat : (ℝ^2) → ℂ := PDE.Analysis.Fourier.angularFourierTransform2D f
  have hFhatMeas : AEStronglyMeasurable Fhat :=
    ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      hf).comp (by fun_prop)).aestronglyMeasurable
  have hFhatInt : Integrable Fhat :=
    hFourier.comp_smul (inv_ne_zero (by positivity : (2 * Real.pi) ≠ 0))
  have hphaseInt (x : (ℝ^2)) : Integrable (fun ξ : (ℝ^2) ↦
      Complex.exp (Complex.I * ((x 0 * ξ 0 + x 1 * ξ 1 : ℝ) : ℂ)) * Fhat ξ) :=
    hFhatInt.mono (by fun_prop) (.of_forall fun ξ ↦ by
      rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul])
  set c : ℝ := ((2 * Real.pi) ^ 2)⁻¹ with hc_def
  have hc : 0 ≤ c := by positivity
  have hnormalization : 2 * c = (1 / Real.pi) * √c := by
    rw [hc_def, Real.sqrt_inv, Real.sqrt_sq (by positivity)]
    cas using Real.pi_pos.ne'
  intro x y
  rw [PDE.Analysis.Fourier.angularFourier_inversion2D f hf hFourier hfcont.continuousAt,
    PDE.Analysis.Fourier.angularFourier_inversion2D f hf hFourier hfcont.continuousAt, ← mul_sub]
  have hphase_eq (z : (ℝ^2)) :
      (fun ξ : (ℝ^2) ↦
          Complex.exp (Complex.I *
            (z 0 * ξ 0 + z 1 * ξ 1)) * PDE.Analysis.Fourier.angularFourierTransform2D f ξ) =
        (fun ξ : (ℝ^2) ↦
          Complex.exp (Complex.I *
            ((z 0 * ξ 0 + z 1 * ξ 1 : ℝ) : ℂ)) * Fhat ξ) := by
    funext ξ
    congr 2
    push_cast
    rfl
  rw [hphase_eq x, hphase_eq y, ← integral_sub (hphaseInt x) (hphaseInt y)]
  simp_rw [← sub_mul]
  rw [show (((2 * Real.pi : ℂ) ^ 2)⁻¹) = (c : ℂ) by rw [hc_def]; norm_cast, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc, Real.sqrt_mul hc]
  refine (mul_le_mul_of_nonneg_left (norm_integral_profile_fourier_phase_sub_le γ hγ0 hγ1 Fhat
    hFhatMeas hEnergy x y) hc).trans_eq ?_
  linear_combination (√(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) *
    √(∫ ξ : (ℝ^2), (1 + ‖ξ‖ ^ 2) ^ 2 * ‖Fhat ξ‖ ^ 2) * ‖x - y‖ ^ γ) * hnormalization

end PDE.Analysis.Fourier
