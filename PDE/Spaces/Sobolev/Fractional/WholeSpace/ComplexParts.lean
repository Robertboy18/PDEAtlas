/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Notation
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Real and imaginary parts in the Bessel scale

The real and imaginary parts are constructed through Mathlib's isometry with `L²`.
Their sum recovers the original complex element. At nonnegative order, their physical
representatives are the real and imaginary parts of the original function.
-/

@[expose] public section

noncomputable section

open MeasureTheory BesselPotentialSpace
open scoped BesselPotentialSpace Sobolev

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

/-- A real coordinate of the Bessel representative, embedded back into the real subspace. -/
def realCoordinateHs (L : ℂ →L[ℝ] ℝ) (u : H^{s}(ℝ^n)) : H^{s}(ℝ^n; ℝ) :=
  ⟨ofLp s (Complex.ofRealCLM.compLpL 2 volume (L.compLpL 2 volume (toLp u))), by
    rw [mem_HsRealSubmodule_iff]
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (L.compLpL 2 volume (toLp u))]
      with x hx
    simp only [toLp_ofLp, hx, Complex.ofRealCLM_apply, Complex.ofReal_im]⟩

/-- Taking a real coordinate has at most the norm of that coordinate functional. -/
theorem norm_realCoordinateHs_le (L : ℂ →L[ℝ] ℝ) (u : H^{s}(ℝ^n)) :
    ‖realCoordinateHs L u‖ ≤ ‖L‖ * ‖u‖ := by
  rw [← Submodule.norm_coe, ← norm_toLp_eq]
  simp only [realCoordinateHs, BesselPotentialSpace.toLp_ofLp]
  have hL := (L.compLpL 2 (volume : Measure (ℝ^n))).le_opNorm (toLp u)
  have hR := (Complex.ofRealCLM.compLpL 2 (volume : Measure (ℝ^n))).le_opNorm
    (L.compLpL 2 volume (toLp u))
  calc
    _ ≤ ‖Complex.ofRealCLM‖ * ‖L.compLpL 2 volume (toLp u)‖ :=
      hR.trans (mul_le_mul_of_nonneg_right Complex.ofRealCLM.norm_compLpL_le (norm_nonneg _))
    _ ≤ ‖L‖ * ‖u‖ := by
      rw [Complex.ofRealCLM_norm, one_mul]
      exact hL.trans (by
        simpa only [norm_toLp_eq] using
          mul_le_mul_of_nonneg_right L.norm_compLpL_le (norm_nonneg (toLp u)))

/-- The real part of an element of the complex Bessel scale. -/
def reHs (u : H^{s}(ℝ^n)) : H^{s}(ℝ^n; ℝ) := realCoordinateHs Complex.reCLM u

/-- The imaginary part of an element of the complex Bessel scale. -/
def imHs (u : H^{s}(ℝ^n)) : H^{s}(ℝ^n; ℝ) := realCoordinateHs Complex.imCLM u

theorem norm_reHs_le (u : H^{s}(ℝ^n)) : ‖reHs u‖ ≤ ‖u‖ := by
  simpa [reHs] using norm_realCoordinateHs_le Complex.reCLM u

theorem norm_imHs_le (u : H^{s}(ℝ^n)) : ‖imHs u‖ ≤ ‖u‖ := by
  simpa [imHs] using norm_realCoordinateHs_le Complex.imCLM u

/-- Real and imaginary parts recover the complex Sobolev element. -/
theorem reHs_add_I_smul_imHs (u : H^{s}(ℝ^n)) :
    (reHs u : H^{s}(ℝ^n)) + Complex.I • (imHs u : H^{s}(ℝ^n)) = u := by
  apply injective_toLp (ℝ^n) ℂ s 2
  simp only [toLp_add, toLp_smul]
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_add (toLp (reHs u).1) (Complex.I • toLp (imHs u).1),
      Lp.coeFn_smul Complex.I (toLp (imHs u).1),
      Complex.ofRealCLM.coeFn_compLpL (Complex.reCLM.compLpL 2 volume (toLp u)),
      Complex.ofRealCLM.coeFn_compLpL (Complex.imCLM.compLpL 2 volume (toLp u)),
      Complex.reCLM.coeFn_compLpL (toLp u),
      Complex.imCLM.coeFn_compLpL (toLp u)] with x hadd hsmul hre him hr hi
  rw [hadd, Pi.add_apply, hsmul]
  simp only [reHs, imHs, realCoordinateHs, BesselPotentialSpace.toLp_ofLp, Pi.smul_apply]
  rw [hre, him, hr, hi]
  simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [mul_comm]
  exact Complex.re_add_im _

/-- The physical real and imaginary representatives agree almost everywhere with their names. -/
theorem toL2Fun_reHs_imHs (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    (∀ᵐ x ∂volume, (toL2Fun hs (reHs u).1 x).re = (toL2Fun hs u x).re) ∧
      (∀ᵐ x ∂volume, (toL2Fun hs (imHs u).1 x).re = (toL2Fun hs u x).im) := by
  have heq := congrArg (toL2Fun hs) (reHs_add_I_smul_imHs u)
  rw [toL2Fun_add, toL2Fun_smul] at heq
  have hae : ∀ᵐ x ∂volume,
      toL2Fun hs (reHs u).1 x + Complex.I * toL2Fun hs (imHs u).1 x =
        toL2Fun hs u x := by
    filter_upwards [Lp.coeFn_add (toL2Fun hs (reHs u).1)
        (Complex.I • toL2Fun hs (imHs u).1),
      Lp.coeFn_smul Complex.I (toL2Fun hs (imHs u).1)] with x ha hm
    simpa only [heq, hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using ha.symm
  have hr := HsSpaceReal.isRealL2_toL2Fun hs (reHs u)
  have hi := HsSpaceReal.isRealL2_toL2Fun hs (imHs u)
  constructor
  · filter_upwards [hae, hi] with x hx hix
    simpa [hix] using congrArg Complex.re hx
  · filter_upwards [hae, hr] with x hx hrx
    simpa [hrx] using congrArg Complex.im hx

end SobolevSpace.Fractional
