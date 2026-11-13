/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Operators
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Plancherel

/-!
# The fractional Sobolev scales are nested, with norm-decreasing inclusions

For `t ≤ s` the inclusion `H^s(ℝ^n) ⊆ H^t(ℝ^n)` is norm-decreasing:
`‖u‖_{H^t} ≤ ‖u‖_{H^s}`.  This upgrades `SobolevSpace.Fractional.inclLinear`
from a linear map to a continuous linear map with operator norm at most one.

## Proof

On the Fourier side the `H^s` norm is `‖(1+‖ξ‖²)^(s/2) 𝓕 u‖_{L²}`
(`BesselPotentialSpace.norm_fourier_toLp_eq`).  Passing from order `s` to order `t` therefore
multiplies the Fourier representative by the symbol of order `t - s`, which is
bounded by one because `1 + ‖ξ‖² ≥ 1` and `(t - s)/2 ≤ 0`.  The bound is then
Mathlib's `Lp.norm_smul_le` for the `L^∞ · L²` action.

The one nontrivial step is `fourier_toLp_inclLinear`, which identifies the
order-`t` Fourier representative of `u` with the symbol times the order-`s` one.
It is proved by pushing both sides into `𝓢'`, where `smulLeftCLM` composition
and `Lp.toTemperedDistribution_smul_eq` apply, and then using injectivity of
`L² → 𝓢'`.

## Main results

* `SobolevSpace.Fractional.norm_besselSymbol_le_one`, `symbolLinf`: the Bessel
  symbol of nonpositive order is a bounded multiplier of `L^∞` norm at most one.
* `SobolevSpace.Fractional.fourier_toLp_inclLinear`: lowering the order multiplies
  the Fourier representative by the symbol of the difference.
* `SobolevSpace.Fractional.norm_inclLinear_le`, `inclCLM`, `norm_inclCLM_le_one`:
  the inclusion `H^s ⊆ H^t` is a contraction.
* `SobolevSpace.Fractional.laplacianSymbol_le_one`, `lineDerivSymbol_le`: the
  scalar symbol bounds used for the Laplacian and directional derivative in
  `Fractional.WholeSpace.OperatorBounds`.
-/

@[expose] public section

open TemperedDistribution MeasureTheory FourierTransform
open scoped BesselPotentialSpace ENNReal SchwartzMap

namespace SobolevSpace.Fractional

variable {n : ℕ} {r s t : ℝ}

open BesselPotentialSpace

/-! ## The Bessel symbol as a bounded multiplier -/

/-- The Bessel symbol `ξ ↦ (1 + ‖ξ‖²)^{r/2}` is continuous; the base is bounded below by one,
so the real power is continuous for every exponent. -/
theorem continuous_besselSymbol : Continuous (besselSymbol n r) := by
  unfold besselSymbol
  refine Complex.continuous_ofReal.comp (Continuous.rpow_const ?_ ?_)
  · fun_prop
  · intro x; exact Or.inl (by positivity)

/-- The Bessel symbol is smooth with polynomially bounded derivatives, so it acts as a
multiplier on Schwartz functions and tempered distributions. -/
theorem besselSymbol_hasTemperateGrowth :
    (besselSymbol n r).HasTemperateGrowth := by
  unfold besselSymbol; fun_prop

/-- For nonpositive order the Bessel symbol is bounded by one: `1 + ‖ξ‖² ≥ 1` and the
exponent `r/2` is nonpositive. -/
theorem norm_besselSymbol_le_one (hr : r ≤ 0) (x : ℝ^n) :
    ‖besselSymbol n r x‖ ≤ 1 := by
  unfold besselSymbol
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by have := sq_nonneg ‖x‖; linarith) (by linarith)

/-- Symbols multiply: order `t - s` times order `s` is order `t`. -/
theorem besselSymbol_mul_besselSymbol :
    besselSymbol n s * besselSymbol n (t - s) = besselSymbol n t := by
  funext x
  unfold besselSymbol
  simp only [Pi.mul_apply, ← Complex.ofReal_mul]
  rw [← Real.rpow_add (by positivity)]
  ring_nf

/-- The Bessel symbol of nonpositive order is an essentially bounded function. -/
theorem memLp_top_besselSymbol (hr : r ≤ 0) :
    MemLp (besselSymbol n r) ∞ (volume : Measure (ℝ^n)) := by
  refine memLp_top_of_bound continuous_besselSymbol.aestronglyMeasurable 1 ?_
  filter_upwards with x using norm_besselSymbol_le_one hr x

/-- The Bessel symbol of nonpositive order as an element of `L^∞`. -/
noncomputable def symbolLinf (n : ℕ) (r : ℝ) (hr : r ≤ 0) :
    Lp ℂ ∞ (volume : Measure (ℝ^n)) :=
  (memLp_top_besselSymbol (n := n) hr).toLp _

/-- The `L^∞` norm of the Bessel symbol of nonpositive order is at most one. -/
theorem norm_symbolLinf_le_one (hr : r ≤ 0) : ‖symbolLinf n r hr‖ ≤ 1 := by
  rw [symbolLinf, Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _),
    eLpNorm_exponent_top (memLp_top_besselSymbol (n := n) hr).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (by filter_upwards with x using norm_besselSymbol_le_one hr x)

/-! ## The inclusion is norm-decreasing -/

/-- Lowering the order multiplies the Fourier representative by the symbol of the
difference. -/
theorem fourier_toLp_inclLinear (h : t ≤ s) (u : H^{s}(ℝ^n)) :
    𝓕 (toLp (inclLinear n h u)) = symbolLinf n (t - s) (sub_nonpos.mpr h) • 𝓕 (toLp u) := by
  refine (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) ?_
  have hts : t - s ≤ 0 := sub_nonpos.mpr h
  have hL : (Lp.toTemperedDistribution (𝓕 (toLp (inclLinear n h u))) : 𝓢'(ℝ^n, ℂ))
      = smulLeftCLM ℂ (besselSymbol n t) (𝓕 (toDistr u)) := by
    rw [← smulLeftCLM_fourier_toDist, toDistr_inclLinear]
  have hR : (Lp.toTemperedDistribution
        (symbolLinf n (t - s) hts • 𝓕 (toLp u)) : 𝓢'(ℝ^n, ℂ))
      = smulLeftCLM ℂ (besselSymbol n t) (𝓕 (toDistr u)) := by
    rw [symbolLinf, MeasureTheory.Lp.toTemperedDistribution_smul_eq
        besselSymbol_hasTemperateGrowth (memLp_top_besselSymbol hts),
      ← smulLeftCLM_fourier_toDist, smulLeftCLM_smulLeftCLM_apply
        besselSymbol_hasTemperateGrowth besselSymbol_hasTemperateGrowth,
      besselSymbol_mul_besselSymbol]
  exact hL.trans hR.symm

/-- The fractional scales are nested with norm-decreasing inclusions. -/
theorem norm_inclLinear_le (h : t ≤ s) (u : H^{s}(ℝ^n)) :
    ‖inclLinear n h u‖ ≤ ‖u‖ := by
  rw [← norm_fourier_toLp_eq, ← norm_fourier_toLp_eq,
    fourier_toLp_inclLinear h u]
  refine (Lp.norm_smul_le _ _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _)
    (norm_symbolLinf_le_one (n := n) (r := t - s) (sub_nonpos.mpr h))

/-- The inclusion `H^s ⊆ H^t` for `t ≤ s` as a continuous linear map of operator
norm at most one. -/
noncomputable def inclCLM (n : ℕ) (h : t ≤ s) : H^{s}(ℝ^n) →L[ℂ] H^{t}(ℝ^n) :=
  { inclLinear n h with
    cont := by
      refine AddMonoidHomClass.continuous_of_bound (inclLinear n h) 1 ?_
      intro u
      simpa using norm_inclLinear_le h u }

/-- `inclCLM` evaluates to `inclLinear`. -/
@[simp] theorem inclCLM_apply (h : t ≤ s) (u : H^{s}(ℝ^n)) :
    inclCLM n h u = inclLinear n h u := rfl

/-- The symbol equals one at the origin, so the bound `≤ 1` above is attained by
the multiplier.  The operator norm of `inclCLM` is in fact exactly `1` for every
`t ≤ s`; only `≤ 1` is proved here, since the lower bound needs a family
concentrating near `ξ = 0`. -/
@[simp] theorem besselSymbol_zero_eq_one : besselSymbol n r 0 = 1 := by
  unfold besselSymbol
  simp

/-- The inclusion `H^s → H^t`, `t ≤ s`, has operator norm at most one. -/
theorem norm_inclCLM_le_one (h : t ≤ s) : ‖inclCLM n h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa using norm_inclLinear_le h u

/-! ## Symbol bounds for the derivative and Laplacian

These are the reduced-symbol bounds used by
`Fractional.WholeSpace.OperatorBounds`, where they yield
the operator bounds for `lineDerivLinear` and `laplacianLinear`.

Mathlib supplies the two identities that make these the relevant symbols:
`besselPotential_neg_two_laplacian_eq` gives
`(1 - (2π)^{-2} Δ)^{-1} Δ f = -(2π)² · M_h f` with
`h ξ = ‖ξ‖²(1+‖ξ‖²)^{-1}`, and
`besselPotential_neg_one_lineDerivOp_eq` gives the analogue for `∂_{m}` with
symbol `⟨ξ,m⟩(1+‖ξ‖²)^{-1/2}`.

Given these, the remaining route is the one used above for the inclusion:
compose symbols, move the bounded multiplier to the `L²` side, and apply
`Lp.norm_smul_le`.  The extra step compared with the inclusion is that the
multiplier must be transported through the `L²` Fourier transform and its
inverse, since these symbols are not themselves Bessel symbols. -/

/-- The reduced Laplacian symbol is bounded by one. -/
theorem laplacianSymbol_le_one (x : ℝ^n) :
    ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ) ≤ 1 := by
  rw [Real.rpow_neg_one, mul_inv_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖x‖]

/-- The reduced Laplacian symbol `‖ξ‖² (1 + ‖ξ‖²)^{-1}` is nonnegative. -/
theorem laplacianSymbol_nonneg (x : ℝ^n) :
    0 ≤ ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ) := by positivity

/-- The reduced first-order symbol is bounded by `‖m‖`, by Cauchy–Schwarz. -/
theorem lineDerivSymbol_le (m x : ℝ^n) :
    |inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ≤ ‖m‖ := by
  have hcs : |inner ℝ x m| ≤ ‖x‖ * ‖m‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x m
  have hpos : (0 : ℝ) < (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hx : ‖x‖ * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) ≤ 1 := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg (by positivity),
      mul_inv_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _), one_mul]
    have h1 : ‖x‖ ^ 2 ≤ ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) 2,
        ← Real.rpow_mul (by positivity)]
      norm_num
    nlinarith [Real.rpow_pos_of_pos (show (0:ℝ) < 1 + ‖x‖ ^ 2 by positivity) (1 / 2 : ℝ),
      norm_nonneg x]
  calc |inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)|
      = |inner ℝ x m| * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) := by
        rw [abs_mul, abs_of_pos hpos]
    _ ≤ (‖x‖ * ‖m‖) * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcs hpos.le
    _ = (‖x‖ * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) * ‖m‖ := by ring
    _ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg m)
    _ = ‖m‖ := one_mul _

end SobolevSpace.Fractional
