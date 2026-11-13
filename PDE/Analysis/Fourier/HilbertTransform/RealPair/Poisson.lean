/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair
public import PDE.Analysis.Fourier.HilbertTransform.SpectralBridge

/-!
# The Poisson kernel and its conjugate as a Hilbert pair

For `ε > 0` the conjugate Poisson kernel `x / (ε² + x²)` is the Hilbert transform of the Poisson
kernel `ε / (ε² + x²)` (`isHilbertPair_poisson`). They are the real and imaginary parts of
`i / (x + i ε)`, the boundary values of `i / (z + i ε)`, which is holomorphic in the upper half
plane. Explicit solutions of one-dimensional vorticity models with `u_x = Hω` are built from
this pair.

## How it works

Both kernels are inverse Fourier transforms of integrable functions in `L²`: the Poisson kernel
`ε / (π (ε² + x²))` of the Abel weight `exp (-2π ε |ξ|)` (`fourierInv_exp_neg_abs`), and the
conjugate kernel `x / (π (ε² + x²))` of the damped multiplier `-i sgn ξ exp (-2π ε |ξ|)`
(`fourierInv_hilbertAbelSymbol`). `fourierInv_eq_L2_ae` identifies these integrals with the `L²`
inverse transform, and on the Fourier side the Hilbert transform is multiplication by
`-i sgn ξ`. Multiplying by `π` removes the normalization.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics, Springer,
  2014, Chapter 5 (Singular Integrals of Convolution Type), pp. 313-417.
  <https://doi.org/10.1007/978-1-4939-1194-3_5>
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  Mathematical Series 32, Princeton University Press, 1971, Chapter II (Boundary Values of
  Harmonic Functions). <https://doi.org/10.1515/9781400883899>
-/

@[expose] public section

noncomputable section

open Filter FourierTransform MeasureTheory

namespace PDE.Analysis

/-- **The Hilbert transform of the Poisson kernel.** For `ε > 0` the conjugate Poisson kernel
`x / (ε² + x²)` is the Hilbert transform of the Poisson kernel `ε / (ε² + x²)`. -/
theorem isHilbertPair_poisson {ε : ℝ} (hε : 0 < ε) :
    IsHilbertPair (fun x ↦ ε / (ε ^ 2 + x ^ 2)) (fun x ↦ x / (ε ^ 2 + x ^ 2)) := by
  have ha : 0 < 2 * Real.pi * ε := by positivity
  have hgi : Integrable (fun ξ : ℝ ↦ (Real.exp (-(2 * Real.pi * ε) * |ξ|) : ℂ)) :=
    (integrable_hilbertAbelWeight ha).ofReal
  have hg2 : MemLp (fun ξ : ℝ ↦ (Real.exp (-(2 * Real.pi * ε) * |ξ|) : ℂ)) 2 volume := by
    have hr : MemLp (fun ξ : ℝ ↦ Real.exp (-(2 * Real.pi * ε) * |ξ|)) 2 volume := by
      refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
      refine (integrable_hilbertAbelWeight (by positivity : 0 < 2 * (2 * Real.pi * ε))).congr
        (Eventually.of_forall fun ξ ↦ ?_)
      dsimp only
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    exact hr.ofReal
  have hP : (fun x ↦ ((Real.pi⁻¹ * (ε / (ε ^ 2 + x ^ 2)) : ℝ) : ℂ)) =ᵐ[volume]
      (𝓕⁻ (hg2.toLp _) : ComplexL2) := by
    filter_upwards [fourierInv_eq_L2_ae hgi _ hg2.coeFn_toLp.symm] with x hx
    rw [← hx, fourierInv_exp_neg_abs hε x]
  have hQ : (fun x ↦ ((hilbertAbelKernel ε x : ℝ) : ℂ)) =ᵐ[volume]
      hilbertTransform (𝓕⁻ (hg2.toLp _)) := by
    rw [hilbertTransform_apply, fourier_fourierInv_eq]
    have hrep : hilbertAbelSymbol ε =ᵐ[volume] (hilbertMultiplier (hg2.toLp _) : ℝ → ℂ) := by
      filter_upwards [coe_hilbertMultiplier (hg2.toLp _), hg2.coeFn_toLp] with ξ h₁ h₂
      rw [h₁, h₂]
      rfl
    filter_upwards [fourierInv_eq_L2_ae (integrable_hilbertAbelSymbol hε) _ hrep] with x hx
    rw [← hx, fourierInv_hilbertAbelSymbol hε]
  have hpair := (show IsHilbertPair (fun x ↦ Real.pi⁻¹ * (ε / (ε ^ 2 + x ^ 2)))
    (hilbertAbelKernel ε) from ⟨_, hP, hQ⟩).const_mul Real.pi
  convert hpair using 1 <;> funext x <;> simp [hilbertAbelKernel, Real.pi_ne_zero]

end PDE.Analysis
