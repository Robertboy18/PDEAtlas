/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.On
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Multidimensional.KernelIntegrability
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Multidimensional.Estimate

/-!
# Morrey estimates as Hölder-space elements

The finite-exponent multidimensional Morrey estimate, stated in the completed
`HolderSpace.C0GammaOn` space. The analytic estimate is in
`Morrey.FiniteExponent.Multidimensional`; we bundle the exponent `1 - n / p`, the explicit
Hölder constant, and the bounded continuous function used by the Sobolev embedding
constructions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, (20), p. 280.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory
open scoped ENNReal

/-- The Hölder exponent `γ = 1 - n / p` of Morrey's inequality (Evans §5.6.2, Theorem 4), bundled
with the bounds `0 < γ ≤ 1`, for `0 < n < p < ∞`. -/
def finiteMorreyHolderExponent (n : ℕ) (p : ℝ)
    (hn : 0 < n) (hp : (n : ℝ) < p) : HolderSpace.Exponent :=
  ⟨(morreyExponent n (ENNReal.ofReal p)).toNNReal,
    Real.toNNReal_pos.mpr (morreyExponent_ofReal_pos hn hp),
    Real.toNNReal_le_one.mpr <| by
      unfold morreyExponent
      exact sub_le_self 1 <|
        div_nonneg (Nat.cast_nonneg n) ENNReal.toReal_nonneg⟩

/-- The underlying `ℝ≥0` value of the bundled exponent is `(1 - n/p).toNNReal`. -/
@[simp]
theorem finiteMorreyHolderExponent_coe (n : ℕ) (p : ℝ)
    (hn : 0 < n) (hp : (n : ℝ) < p) :
    (finiteMorreyHolderExponent n p hn hp : NNReal) =
      (morreyExponent n (ENNReal.ofReal p)).toNNReal :=
  rfl

/-- The finite-exponent Morrey coefficient before conversion from `ℝ≥0∞` to
`ℝ≥0`. -/
def finiteMorreyHolderConstantE (n : ℕ) (p q : ℝ)
    (u : ℝ^n → ℝ) : ENNReal :=
  2 * morreyBallAverageConstant n *
      morreyCenteredKernelConstant n q *
      (ENNReal.ofReal 2 ^
        morreyExponent n (ENNReal.ofReal p)) *
      eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume

/-- The explicit finite Hölder constant in the bundled Morrey theorem. -/
def finiteMorreyHolderConstant (n : ℕ) (p q : ℝ)
    (u : ℝ^n → ℝ) : NNReal :=
  (finiteMorreyHolderConstantE n p q u).toNNReal

/-- Compact support makes the explicit finite-exponent Morrey coefficient
finite. -/
theorem finiteMorreyHolderConstantE_ne_top
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    finiteMorreyHolderConstantE n p q u ≠ ∞ := by
  have hgradientMem :
      MemLp (fderiv ℝ u) (ENNReal.ofReal p) volume :=
    (hu.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport
      (hcompact.fderiv ℝ)
  have hgradientFinite :
      eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume ≠ ∞ :=
    hgradientMem.eLpNorm_ne_top
  have hgamma :
      0 ≤ morreyExponent n (ENNReal.ofReal p) :=
    (morreyExponent_ofReal_pos hn hp).le
  have haverageFinite : morreyBallAverageConstant n ≠ ∞ := by
    simp [morreyBallAverageConstant]
  have hq0 : 0 < q := hpq.symm.pos
  have hkernelFinite : morreyCenteredKernelConstant n q ≠ ∞ := by
    unfold morreyCenteredKernelConstant
    exact ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hq0.le) ENNReal.ofReal_ne_top
  have htwoFinite :
      ENNReal.ofReal 2 ^
          morreyExponent n (ENNReal.ofReal p) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hgamma ENNReal.ofReal_ne_top
  unfold finiteMorreyHolderConstantE
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by simp) haverageFinite)
        hkernelFinite)
      htwoFinite)
    hgradientFinite

/-- The multidimensional Morrey estimate: if `u` is `C¹` with compact support on `ℝ^n`,
`0 < n < p` and `q` is the conjugate exponent of `p`, then `u` is Hölder continuous with exponent
`1 - n / p` and constant `finiteMorreyHolderConstant n p q u`. -/
theorem holderWith_finiteMorrey
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    HolderWith (finiteMorreyHolderConstant n p q u)
      (finiteMorreyHolderExponent n p hn hp : NNReal) u := by
  intro x y
  have h :=
    enorm_sub_le_eLpNorm_fderiv_mul_rpow
      u hu hn hp hpq x y
  change
    ‖u y - u x‖ₑ ≤
      finiteMorreyHolderConstantE n p q u *
        ENNReal.ofReal ‖y - x‖ ^
          morreyExponent n (ENNReal.ofReal p)
    at h
  have hconstantFinite :=
    finiteMorreyHolderConstantE_ne_top
      u hu hcompact hn hp hpq
  have hgamma :
      0 ≤ morreyExponent n (ENNReal.ofReal p) :=
    (morreyExponent_ofReal_pos hn hp).le
  simpa [finiteMorreyHolderConstant, edist_dist, Real.dist_eq,
    Real.enorm_eq_ofReal_abs, abs_sub_comm, dist_eq_norm,
    norm_sub_rev, ENNReal.coe_toNNReal hconstantFinite,
    Real.coe_toNNReal _ hgamma] using h

/-- If `u` is `C¹` with compact support on `ℝ^n` and `0 < n < p`, then `u` is Hölder continuous
with exponent `1 - n / p`. -/
theorem memHolder_finiteMorrey
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    MemHolder (finiteMorreyHolderExponent n p hn hp : NNReal) u :=
  (holderWith_finiteMorrey u hu hcompact hn hp hpq).memHolder

/-- A compactly supported `C¹` function, bundled as an element of the
completed global `C^{0,1-n/p}` space. -/
def compactSupportToMorreyHolder
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    HolderSpace.C0GammaOn (ℝ^n)
      (finiteMorreyHolderExponent n p hn hp) where
  toBoundedContinuousFunction :=
    ofCompactSupport u hu.continuous hcompact
  memHolder := by
    change
      MemHolder (finiteMorreyHolderExponent n p hn hp : NNReal) u
    exact memHolder_finiteMorrey u hu hcompact hn hp hpq

/-- The bundled Hölder-space element evaluates pointwise to `u` itself. -/
@[simp]
theorem compactSupportToMorreyHolder_apply
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (x : ℝ^n) :
    compactSupportToMorreyHolder u hu hcompact hn hp hpq x = u x :=
  rfl

/-- The Hölder seminorm of `compactSupportToMorreyHolder u` is at most
`finiteMorreyHolderConstant n p q u`. -/
theorem holderSeminorm_compactSupportToMorreyHolder_le
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    (compactSupportToMorreyHolder
        u hu hcompact hn hp hpq).holderSeminorm ≤
      finiteMorreyHolderConstant n p q u :=
  (holderWith_finiteMorrey u hu hcompact hn hp hpq).nnholderNorm_le

end SobolevSpace
