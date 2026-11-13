/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Operators
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Plancherel
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Embedding

/-!
# Operator bounds for the derivative and Laplacian on `H^s`

`Fractional.WholeSpace.Embedding` shows the inclusion
`H^s ⊆ H^t` is norm-decreasing.  We do the same for the two
differential operators, upgrading `lineDerivLinear` and `laplacianLinear` from
linear maps to continuous linear maps:

* `‖∂_{m} u‖_{H^{s-1}} ≤ 2π‖m‖ · ‖u‖_{H^s}`
* `‖Δ u‖_{H^{s-2}} ≤ (2π)² · ‖u‖_{H^s}`

The constants are not `1`, unlike the inclusion: they come from Mathlib's Fourier
convention, in which `∂_{m}` has symbol `2πi⟪ξ,m⟫` and `Δ` has symbol `-4π²‖ξ‖²`. This is the
convention with `e^{-2πi⟪x,ξ⟫}` in the kernel, as in Stein and Weiss, Chapter I. Evans, PDE,
§5.8.5, uses the convention of his §4.3, in which `(D^α u)^ = (iy)^α û`, and characterizes
`H^k(ℝ^n)` by the weight `1 + |y|^k` (Theorem 8).

## Main results

* `SobolevSpace.Fractional.fourier_toLp_laplacianLinear`,
  `SobolevSpace.Fractional.norm_laplacianLinear_le`, `laplacianCLM`,
  `norm_laplacianCLM_le`: `Δ : H^s → H^{s-2}` is bounded with norm at most `(2π)²`.
* `SobolevSpace.Fractional.fourier_toLp_lineDerivLinear`,
  `SobolevSpace.Fractional.norm_lineDerivLinear_le`, `lineDerivCLM`,
  `norm_lineDerivCLM_le`: `∂_m : H^s → H^{s-1}` is bounded with norm at most
  `2π‖m‖`.

## Implementation notes

We follow the same template as the inclusion bound.  On the Fourier side the operator
becomes multiplication by a reduced symbol, `⟪ξ,m⟫(1+‖ξ‖²)^{-1/2}` for the
derivative and `‖ξ‖²(1+‖ξ‖²)^{-1}` for the Laplacian, which is bounded (by `‖m‖`
and by `1` respectively, proved in `Fractional.WholeSpace.Embedding`).  Multiplication by a
bounded symbol acts continuously on `L²`, with operator norm at most its
uniform bound; `Lp.norm_smul_le` supplies the estimate.

No transport through the `L²` Fourier transform and its inverse is needed: the
lemma `smulLeftCLM_fourier_toDist` performs that transport and can be rewritten in
either direction.

Mathlib's `laplacian_eq_fourierMultiplierCLM` produces a real scalar, but
there is no `FourierSMul ℝ 𝓢'(ℝ^n, ℂ)` instance, only the complex one.  The
complex Fourier map's `map_smul_of_tower` moves this real scalar through the
transform.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298, the characterization of
  `H^k(ℝ^n)` by the Fourier transform, with `(D^α u)^ = (iy)^α û`, (21), in step 1 of the proof, and
  the definition of `H^s(ℝ^n)` for `s > 0` on p. 298.
  <https://doi.org/10.1090/gsm/019>
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press, 1971, Chapter I, The Fourier Transform, pp. 1-36, for the convention with
  `e^{-2πi⟪x,ξ⟫}` in the kernel.
  <https://doi.org/10.1515/9781400883899>
-/

@[expose] public section

open TemperedDistribution MeasureTheory FourierTransform
open scoped BesselPotentialSpace ENNReal SchwartzMap Real LineDeriv Laplacian

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

open BesselPotentialSpace

/-! ## Scalar bookkeeping -/

/-- `|2πi| = 2π`. -/
theorem norm_two_pi_I : ‖(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
  simp [abs_of_pos Real.pi_pos]

/-- Fourier transform of the distributional Laplacian: `𝓕(Δv) = -(2π)² ‖ξ‖² · 𝓕v` in Mathlib's
convention. The continuous linear Fourier map also preserves real scalar multiplication. -/
theorem fourier_laplacian_eq (v : 𝓢'(ℝ^n, ℂ)) :
    𝓕 (Δ v) = (-(2 * π) ^ 2 : ℝ) •
      smulLeftCLM ℂ (fun x : ℝ^n ↦ (Complex.ofReal (‖x‖ ^ 2))) (𝓕 v) := by
  rw [laplacian_eq_fourierMultiplierCLM, ← fourierCLM_apply (R := ℂ),
    (fourierCLM ℂ 𝓢'(ℝ^n, ℂ)).map_smul_of_tower, fourierCLM_apply,
    fourierMultiplierCLM_apply, fourier_fourierInv_eq]

/-! ## The reduced Laplacian symbol as an `L^∞` multiplier -/

/-- The bounded Fourier symbol `|ξ|² / (1 + |ξ|²)` used to lower Sobolev order by two. -/
noncomputable def lapSymbol (n : ℕ) : ℝ^n → ℂ :=
  fun x ↦ ((‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ) : ℝ) : ℂ)

/-- The reduced Laplacian symbol has temperate growth. -/
theorem lapSymbol_hasTemperateGrowth : (lapSymbol n).HasTemperateGrowth := by
  unfold lapSymbol; fun_prop

/-- The reduced Laplacian symbol is bounded by one, since `‖ξ‖² ≤ 1 + ‖ξ‖²`. -/
theorem norm_lapSymbol_le_one (x : ℝ^n) : ‖lapSymbol n x‖ ≤ 1 := by
  rw [lapSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (laplacianSymbol_nonneg x)]
  exact laplacianSymbol_le_one x

/-- The reduced Laplacian symbol is essentially bounded. -/
theorem memLp_top_lapSymbol : MemLp (lapSymbol n) ∞ (volume : Measure (ℝ^n)) := by
  refine memLp_top_of_bound
    (lapSymbol_hasTemperateGrowth.1.continuous.aestronglyMeasurable) 1 ?_
  filter_upwards with x using norm_lapSymbol_le_one x

/-- The `L^∞` class of the reduced Laplacian symbol. -/
noncomputable def lapSymbolLinf (n : ℕ) : Lp ℂ ∞ (volume : Measure (ℝ^n)) :=
  (memLp_top_lapSymbol (n := n)).toLp _

/-- The `L^∞` norm of the reduced Laplacian symbol is at most one. -/
theorem norm_lapSymbolLinf_le_one : ‖lapSymbolLinf n‖ ≤ 1 := by
  rw [lapSymbolLinf, Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _),
    eLpNorm_exponent_top (memLp_top_lapSymbol (n := n)).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (by filter_upwards with x using norm_lapSymbol_le_one x)

/-- Symbol factorisation for the Laplacian:
`‖ξ‖² (1+‖ξ‖²)^{(s-2)/2} = (1+‖ξ‖²)^{s/2} · lapSymbol ξ`. This moves the order-`(s-2)` Bessel
weight of `Δu` onto the order-`s` weight of `u`, at the price of a bounded factor. -/
theorem sq_mul_besselSymbol :
    (fun x : ℝ^n ↦ (Complex.ofReal (‖x‖ ^ 2))) * besselSymbol n (s - 2)
      = besselSymbol n s * lapSymbol n := by
  funext x
  simp only [Pi.mul_apply, besselSymbol, lapSymbol, ← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [show (s - 2) / 2 = s / 2 + (-1 : ℝ) by ring, Real.rpow_add (by positivity)]
  ring

/-! ## The Laplacian is bounded `H^s → H^{s-2}` -/

/-- The Fourier representative of `Δu ∈ H^{s-2}` is `-(2π)²` times the reduced Laplacian
symbol times the Fourier representative of `u`. -/
theorem fourier_toLp_laplacianLinear (u : H^{s}(ℝ^n)) :
    𝓕 (toLp (laplacianLinear n s u))
      = (-(2 * π) ^ 2 : ℝ) • (lapSymbolLinf n • 𝓕 (toLp u)) := by
  refine (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) ?_
  have hL : (Lp.toTemperedDistribution (𝓕 (toLp (laplacianLinear n s u))) : 𝓢'(ℝ^n, ℂ))
      = (-(2 * π) ^ 2 : ℝ) •
        smulLeftCLM ℂ ((fun x : ℝ^n ↦ (Complex.ofReal (‖x‖ ^ 2))) * besselSymbol n (s - 2))
          (𝓕 (toDistr u)) := by
    rw [← smulLeftCLM_fourier_toDist, toDistr_laplacianLinear, fourier_laplacian_eq,
      (smulLeftCLM ℂ (besselSymbol n (s - 2))).map_smul_of_tower,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) besselSymbol_hasTemperateGrowth]
  have hR : (Lp.toTemperedDistribution
        ((-(2 * π) ^ 2 : ℝ) • (lapSymbolLinf n • 𝓕 (toLp u))) : 𝓢'(ℝ^n, ℂ))
      = (-(2 * π) ^ 2 : ℝ) •
        smulLeftCLM ℂ (besselSymbol n s * lapSymbol n) (𝓕 (toDistr u)) := by
    rw [← Lp.toTemperedDistributionCLM_apply,
      (Lp.toTemperedDistributionCLM ℂ volume 2).map_smul_of_tower,
      Lp.toTemperedDistributionCLM_apply, lapSymbolLinf,
      MeasureTheory.Lp.toTemperedDistribution_smul_eq
        lapSymbol_hasTemperateGrowth memLp_top_lapSymbol,
      ← smulLeftCLM_fourier_toDist,
      smulLeftCLM_smulLeftCLM_apply besselSymbol_hasTemperateGrowth
        lapSymbol_hasTemperateGrowth]
  rw [sq_mul_besselSymbol] at hL
  exact hL.trans hR.symm

/-- `‖Δu‖_{H^{s-2}} ≤ (2π)² ‖u‖_{H^s}`. The constant is the modulus of the prefactor in the
symbol `-4π²‖ξ‖²` of `Δ`; the remaining factor `‖ξ‖²/(1+‖ξ‖²)` is bounded by one. -/
theorem norm_laplacianLinear_le (u : H^{s}(ℝ^n)) :
    ‖laplacianLinear n s u‖ ≤ (2 * π) ^ 2 * ‖u‖ := by
  rw [← norm_fourier_toLp_eq, ← norm_fourier_toLp_eq, fourier_toLp_laplacianLinear,
    norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π) ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Lp.norm_smul_le _ _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) norm_lapSymbolLinf_le_one

/-- The Laplacian `H^s → H^{s-2}` as a continuous linear map. -/
noncomputable def laplacianCLM (n : ℕ) (s : ℝ) : H^{s}(ℝ^n) →L[ℂ] H^{s - 2}(ℝ^n) :=
  { laplacianLinear n s with
    cont := by
      refine AddMonoidHomClass.continuous_of_bound (laplacianLinear n s) ((2 * π) ^ 2) ?_
      intro u
      simpa using norm_laplacianLinear_le u }

/-- `laplacianCLM` evaluates to `laplacianLinear`. -/
@[simp] theorem laplacianCLM_apply (u : H^{s}(ℝ^n)) :
    laplacianCLM n s u = laplacianLinear n s u := rfl

/-- The Laplacian `H^s → H^{s-2}` has operator norm at most `(2π)²`. -/
theorem norm_laplacianCLM_le : ‖laplacianCLM n s‖ ≤ (2 * π) ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ by
    simpa using norm_laplacianLinear_le u

/-! ## The reduced first-order symbol as an `L^∞` multiplier -/

/-- The bounded Fourier symbol `⟪ξ, m⟫ / sqrt (1 + |ξ|²)` for differentiation along `m`. -/
noncomputable def lineSymbol (n : ℕ) (m : ℝ^n) : ℝ^n → ℂ :=
  fun x ↦ ((inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)

/-- The reduced first-order symbol has temperate growth. -/
theorem lineSymbol_hasTemperateGrowth (m : ℝ^n) : (lineSymbol n m).HasTemperateGrowth := by
  unfold lineSymbol; fun_prop

/-- The reduced first-order symbol is bounded by `‖m‖`: Cauchy–Schwarz and
`‖ξ‖ ≤ (1 + ‖ξ‖²)^{1/2}`. -/
theorem norm_lineSymbol_le (m x : ℝ^n) : ‖lineSymbol n m x‖ ≤ ‖m‖ := by
  rw [lineSymbol, Complex.norm_real, Real.norm_eq_abs]
  exact lineDerivSymbol_le m x

/-- The reduced first-order symbol is essentially bounded. -/
theorem memLp_top_lineSymbol (m : ℝ^n) :
    MemLp (lineSymbol n m) ∞ (volume : Measure (ℝ^n)) := by
  refine memLp_top_of_bound
    ((lineSymbol_hasTemperateGrowth m).1.continuous.aestronglyMeasurable) ‖m‖ ?_
  filter_upwards with x using norm_lineSymbol_le m x

/-- The `L^∞` class of the reduced directional-derivative symbol. -/
noncomputable def lineSymbolLinf (n : ℕ) (m : ℝ^n) : Lp ℂ ∞ (volume : Measure (ℝ^n)) :=
  (memLp_top_lineSymbol m).toLp _

/-- The `L^∞` norm of the reduced first-order symbol is at most `‖m‖`. -/
theorem norm_lineSymbolLinf_le (m : ℝ^n) : ‖lineSymbolLinf n m‖ ≤ ‖m‖ := by
  rw [lineSymbolLinf, Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg m) ?_
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _),
    eLpNorm_exponent_top (memLp_top_lineSymbol m).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound
    (by filter_upwards with x using norm_lineSymbol_le m x)

/-- Symbol factorisation for the directional derivative:
`⟪ξ,m⟫ (1+‖ξ‖²)^{(s-1)/2} = (1+‖ξ‖²)^{s/2} · lineSymbol m ξ`. -/
theorem inner_mul_besselSymbol (m : ℝ^n) :
    (fun x : ℝ^n ↦ ((inner ℝ x m : ℝ) : ℂ)) * besselSymbol n (s - 1)
      = besselSymbol n s * lineSymbol n m := by
  funext x
  simp only [Pi.mul_apply, besselSymbol, lineSymbol, ← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [show (s - 1) / 2 = s / 2 + (-1 / 2 : ℝ) by ring, Real.rpow_add (by positivity)]
  ring

/-! ## The directional derivative is bounded `H^s → H^{s-1}` -/

/-- The Fourier representative of `∂_m u ∈ H^{s-1}` is `2πi` times the reduced first-order
symbol times the Fourier representative of `u`. -/
theorem fourier_toLp_lineDerivLinear (m : ℝ^n) (u : H^{s}(ℝ^n)) :
    𝓕 (toLp (lineDerivLinear n s m u))
      = (2 * π * Complex.I) • (lineSymbolLinf n m • 𝓕 (toLp u)) := by
  refine (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) ?_
  have hL : (Lp.toTemperedDistribution (𝓕 (toLp (lineDerivLinear n s m u))) : 𝓢'(ℝ^n, ℂ))
      = (2 * π * Complex.I) •
        smulLeftCLM ℂ ((fun x : ℝ^n ↦ ((inner ℝ x m : ℝ) : ℂ)) * besselSymbol n (s - 1))
          (𝓕 (toDistr u)) := by
    rw [← smulLeftCLM_fourier_toDist, toDistr_lineDerivLinear, fourier_lineDerivOp_eq,
      map_smul, smulLeftCLM_smulLeftCLM_apply (by fun_prop) besselSymbol_hasTemperateGrowth]
  have hR : (Lp.toTemperedDistribution
        ((2 * π * Complex.I) • (lineSymbolLinf n m • 𝓕 (toLp u))) : 𝓢'(ℝ^n, ℂ))
      = (2 * π * Complex.I) •
        smulLeftCLM ℂ (besselSymbol n s * lineSymbol n m) (𝓕 (toDistr u)) := by
    rw [← Lp.toTemperedDistributionCLM_apply,
      (Lp.toTemperedDistributionCLM ℂ volume 2).map_smul,
      Lp.toTemperedDistributionCLM_apply, lineSymbolLinf,
      MeasureTheory.Lp.toTemperedDistribution_smul_eq
        (lineSymbol_hasTemperateGrowth m) (memLp_top_lineSymbol m),
      ← smulLeftCLM_fourier_toDist,
      smulLeftCLM_smulLeftCLM_apply besselSymbol_hasTemperateGrowth
        (lineSymbol_hasTemperateGrowth m)]
  rw [inner_mul_besselSymbol] at hL
  exact hL.trans hR.symm

/-- `‖∂_m u‖_{H^{s-1}} ≤ 2π‖m‖ ‖u‖_{H^s}`. The factor `2π` is the modulus of the prefactor in
the symbol `2πi⟪ξ,m⟫` of `∂_m`; the factor `‖m‖` is the bound on the reduced symbol. -/
theorem norm_lineDerivLinear_le (m : ℝ^n) (u : H^{s}(ℝ^n)) :
    ‖lineDerivLinear n s m u‖ ≤ 2 * π * ‖m‖ * ‖u‖ := by
  have h1 : ‖lineSymbolLinf n m • 𝓕 (toLp u)‖ ≤ ‖m‖ * ‖𝓕 (toLp u)‖ :=
    (Lp.norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_lineSymbolLinf_le m) (norm_nonneg _))
  have h2 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [← norm_fourier_toLp_eq, ← norm_fourier_toLp_eq, fourier_toLp_lineDerivLinear,
    norm_smul, norm_two_pi_I]
  calc 2 * π * ‖lineSymbolLinf n m • 𝓕 (toLp u)‖
      ≤ 2 * π * (‖m‖ * ‖𝓕 (toLp u)‖) := mul_le_mul_of_nonneg_left h1 h2
    _ = 2 * π * ‖m‖ * ‖𝓕 (toLp u)‖ := by ring

/-- The directional derivative `H^s → H^{s-1}` as a continuous linear map. -/
noncomputable def lineDerivCLM (n : ℕ) (s : ℝ) (m : ℝ^n) :
    H^{s}(ℝ^n) →L[ℂ] H^{s - 1}(ℝ^n) :=
  { lineDerivLinear n s m with
    cont := by
      refine AddMonoidHomClass.continuous_of_bound (lineDerivLinear n s m) (2 * π * ‖m‖) ?_
      intro u
      simpa using norm_lineDerivLinear_le m u }

/-- `lineDerivCLM` evaluates to `lineDerivLinear`. -/
@[simp] theorem lineDerivCLM_apply (m : ℝ^n) (u : H^{s}(ℝ^n)) :
    lineDerivCLM n s m u = lineDerivLinear n s m u := rfl

/-- The directional derivative `∂_m : H^s → H^{s-1}` has operator norm at most `2π‖m‖`. -/
theorem norm_lineDerivCLM_le (m : ℝ^n) : ‖lineDerivCLM n s m‖ ≤ 2 * π * ‖m‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ by
    simpa using norm_lineDerivLinear_le m u

end SobolevSpace.Fractional
