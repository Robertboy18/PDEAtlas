/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.Reverse
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceL2

/-!
# Complexification of real whole-space Sobolev rows

The real L² coordinate model and the complex Lebesgue L² model are connected
by a bounded real-linear map. On a Sobolev base coordinate this map is the
complexification used by the integer Sobolev–Bessel equivalence. It is injective, and the
real L² inner product is the real part of the complexified inner product.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.GraphSpace
open scoped Sobolev

namespace SobolevSpace.Fractional

variable {n k : ℕ}

/-- Complexification of a real whole-space L² coordinate. -/
def complexifyL2CLM (n : ℕ) :
    DerivLp n 2 univ →L[ℝ] Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  Complex.ofRealCLM.compLpL 2 volume |>.comp
    (wholeSpaceL2Equiv.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Complexification preserves the literal value almost everywhere. -/
theorem complexifyL2CLM_ae (u : DerivLp n 2 univ) :
    (complexifyL2CLM n u : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (u x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (wholeSpaceL2Equiv u),
    wholeSpaceL2Equiv_ae u] with x hx hy
  exact hx.trans (congrArg Complex.ofReal hy)

/-- On the base coordinate, bounded complexification is the one used by
the integer Sobolev equivalence. -/
theorem complexifyL2CLM_base (U : W^{k,2}(ℝ^n)) :
    complexifyL2CLM n (wkpBaseCoordinateCLM U) = baseL2 U := by
  apply Lp.ext
  have hb : (baseL2 U : ℝ^n → ℂ) =ᵐ[volume]
      fun x ↦ (wkpBaseCoordinateCLM U x : ℂ) :=
    (memLp_coordFun U (baseIndex n k)).ofReal.coeFn_toLp
  exact (complexifyL2CLM_ae _).trans hb.symm

/-- Complexification of real whole-space L² functions is injective. -/
theorem complexifyL2CLM_injective : Function.Injective (complexifyL2CLM n) := by
  intro f g hfg
  apply Lp.ext
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [Lp.ext_iff.mp hfg, complexifyL2CLM_ae f, complexifyL2CLM_ae g]
    with x he hf hg
  exact Complex.ofReal_injective (hf.symm.trans (he.trans hg))

/-- The real `L²` pairing of real functions is the real part of their complexified pairing. -/
theorem inner_eq_re_inner_complexifyL2CLM (f g : DerivLp n 2 univ) :
    inner ℝ f g = (inner ℂ (complexifyL2CLM n f) (complexifyL2CLM n g)).re := by
  rw [L2.inner_def, L2.inner_def]
  have hc : (fun x ↦ inner ℂ ((complexifyL2CLM n f : ℝ^n → ℂ) x)
      ((complexifyL2CLM n g : ℝ^n → ℂ) x)) =ᵐ[volume] fun x ↦ ((f x * g x : ℝ) : ℂ) := by
    filter_upwards [complexifyL2CLM_ae f, complexifyL2CLM_ae g] with x hf hg
    rw [hf, hg]
    simp [RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae hc, integral_complex_ofReal, Complex.ofReal_re]
  simp only [domainMeasure, Measure.restrict_univ, RCLike.inner_apply, conj_trivial]
  congr 1
  funext x
  ring

/-- Forgetting higher derivatives keeps the complexified base function. -/
theorem baseL2_lowerOrderCLM {m : ℕ} (hkm : k ≤ m) (U : W^{m,2}(ℝ^n)) :
    baseL2 (lowerOrderCLM (n := n) (p := 2) (Ω := univ) hkm U) = baseL2 U := by
  rw [← complexifyL2CLM_base, ← complexifyL2CLM_base, wkpBaseCoordinateCLM_lowerOrderCLM]

end SobolevSpace.Fractional
