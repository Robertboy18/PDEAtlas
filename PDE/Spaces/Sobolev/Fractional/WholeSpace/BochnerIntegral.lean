/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.SeminormSupremum
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Energy

/-!
# The Sobolev norm of a Bochner integral in `L²`

Minkowski's inequality for the Bessel energy: for every real `σ`, every measure `μ` and every
function `g` with values in the finite families of `L²(ℝⁿ)` functions,
`E_σ(∫ g dμ)^{1/2} ≤ ∫ E_σ(g)^{1/2} dμ`, that is `‖∫ g‖_{H^σ} ≤ ∫ ‖g‖_{H^σ}`. A Duhamel integral
`∫ S(t - s) G(s) ds` is such a Bochner integral in `L²`, and this is how a smoothing bound for
each `S(t - s) G(s)` becomes regularity of the integral. Nothing is assumed about `g`: it need
not be measurable with values in `H^σ`, and no jointly measurable representative is chosen.
This is the difference with `ENNReal.eLpNorm_lintegral_le`, which is for jointly measurable
functions of two variables. If `g` is not Bochner integrable in `L²`, its integral is zero by
convention and the inequality says nothing.

## Main results

* `besselEnergy_eq_iSup_setLIntegral`: the energy is the supremum over `N` of
  `∫_{|ξ| ≤ N} (1 + |ξ|²)^σ ∑ⱼ |f̂ⱼ|²`.
* `ballMultiplier`, `eNorm_ballMultiplier_sq`: the frequency cut-off to `|ξ| ≤ N` with the
  weight of order `σ`, a bounded operator from the families of `L²` functions into their Hilbert
  sum, whose norm squared is the part of the energy in the ball.
* `besselEnergy_integral_le`: Minkowski's inequality above, for all measures and all `g`.
* `besselEnergy_integral_comp_le`: the same for `Φ(∫ g)`, with a bounded real-linear map `Φ` from a
  Banach space into the families.

## How it works

The energy of order `σ` is the increasing limit of its parts in the frequency balls `|ξ| ≤ N`.
The part in a ball is the square of the `L²` norm of a Fourier multiplier with a bounded symbol,
the Bessel symbol cut off outside the ball, and a bounded operator commutes with the Bochner
integral. So the energy is a supremum of squares of continuous seminorms on `L²`; Minkowski's
inequality holds for each seminorm and passes to the supremum
(`PDE.Analysis.rpow_half_integral_le_of_eq_iSup`).
The same supremum gives the lower semicontinuity of the energy under weak convergence in `L²`,
which is not stated here.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform
open PDE.Analysis.Fourier
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-! ## The energy in a frequency ball -/

/-- The Bessel symbol of order `σ` cut off outside the ball `|ξ| ≤ N` is essentially bounded:
it is continuous on a compact set. -/
theorem memLp_top_indicator_besselSymbol (σ : ℝ) (N : ℕ) :
    MemLp ((Metric.closedBall (0 : ℝ^n) N).indicator (besselSymbol n σ)) ∞ volume := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ^n) (N : ℝ)).exists_bound_of_continuousOn
    (continuous_besselSymbol (n := n) (r := σ)).continuousOn
  refine memLp_top_of_bound
    ((continuous_besselSymbol (n := n) (r := σ)).aestronglyMeasurable.indicator
      measurableSet_closedBall) C (Filter.Eventually.of_forall fun ξ ↦ ?_)
  by_cases hξ : ξ ∈ Metric.closedBall (0 : ℝ^n) (N : ℝ)
  · rw [Set.indicator_of_mem hξ]
    exact hC ξ hξ
  · rw [Set.indicator_of_notMem hξ, norm_zero]
    exact (norm_nonneg _).trans (hC 0 (Metric.mem_closedBall_self N.cast_nonneg))

/-- The Bessel symbol `(1 + |ξ|²)^{σ/2}` on the frequency ball `|ξ| ≤ N`, zero outside, as an
element of `L^∞`. -/
def ballSymbol (n : ℕ) (σ : ℝ) (N : ℕ) : Lp ℂ ∞ (volume : Measure (ℝ^n)) :=
  (memLp_top_indicator_besselSymbol (n := n) σ N).toLp _

/-- The part of the energy of order `σ` in the ball `|ξ| ≤ N` is the energy of order zero, that
is the square of the `L²` norm, of the multiplier with the cut-off Bessel symbol. -/
theorem besselEnergy_zero_fourierMultiplierL2_ballSymbol (σ : ℝ) (N : ℕ)
    (g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy 0 (fun j ↦ fourierMultiplierL2 (ballSymbol n σ N) (g j)) =
      ∫⁻ ξ in Metric.closedBall (0 : ℝ^n) N,
        (besselWeight n σ ξ : ℝ≥0∞) * fourierDensity g ξ := by
  have hm : ∀ᵐ ξ : ℝ^n, ballSymbol n σ N ξ =
      (Metric.closedBall (0 : ℝ^n) N).indicator (besselSymbol n σ) ξ :=
    MemLp.coeFn_toLp (memLp_top_indicator_besselSymbol (n := n) σ N)
  rw [besselEnergy_fourierMultiplierL2, ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_congr_ae ?_
  filter_upwards [hm] with ξ hξ
  rw [coe_besselWeight_zero, one_mul, hξ]
  by_cases h : ξ ∈ Metric.closedBall (0 : ℝ^n) (N : ℝ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, enorm_besselSymbol_sq, coe_besselWeight]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, eNorm_zero]
    simp

/-- **The energy is the supremum of its parts in the frequency balls**:
`E_σ(g) = sup_N ∫_{|ξ| ≤ N} (1 + |ξ|²)^σ ∑ⱼ |ĝⱼ(ξ)|² dξ`. The balls increase to the whole
space. -/
theorem besselEnergy_eq_iSup_setLIntegral (σ : ℝ) (g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ g = ⨆ N : ℕ, ∫⁻ ξ in Metric.closedBall (0 : ℝ^n) N,
      (besselWeight n σ ξ : ℝ≥0∞) * fourierDensity g ξ := by
  rw [← setLIntegral_iUnion_of_directed _ (directed_of_isDirected_le fun a b h ↦
    Metric.closedBall_subset_closedBall (Nat.cast_le.2 h)), Metric.iUnion_closedBall_nat,
    Measure.restrict_univ]
  rfl

/-- The frequency cut-off `|ξ| ≤ N` of a family with the weight of order `σ`, as a bounded
operator from the families of `L²` functions into their Hilbert sum. -/
def ballMultiplier (ι : Type*) [Fintype ι] (n : ℕ) (σ : ℝ) (N : ℕ) :
    (ι → Lp ℂ 2 (volume : Measure (ℝ^n))) →L[ℂ]
      PiLp 2 (fun _ : ι ↦ Lp ℂ 2 (volume : Measure (ℝ^n))) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : ι ↦ Lp ℂ 2 (volume : Measure (ℝ^n)))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun j ↦
      fourierMultiplierL2 (ballSymbol n σ N) ∘L ContinuousLinearMap.proj j

/-- The square of the norm of the cut-off is the part of the energy in the ball. -/
theorem eNorm_ballMultiplier_sq (σ : ℝ) (N : ℕ) (g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    ‖ballMultiplier ι n σ N g‖ₑ ^ 2 = ∫⁻ ξ in Metric.closedBall (0 : ℝ^n) N,
      (besselWeight n σ ξ : ℝ≥0∞) * fourierDensity g ξ := by
  rw [← besselEnergy_zero_fourierMultiplierL2_ballSymbol, besselEnergy_zero, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
    ENNReal.ofReal_sum_of_nonneg fun j _ ↦ sq_nonneg _]
  rfl

/-! ## Minkowski's inequality -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Minkowski's inequality for the Sobolev norm of a Bochner integral.** For every real `σ`,
every measure `μ` and every function `g` with values in the finite families of `L²(ℝⁿ)`
functions,

`E_σ(∫ g dμ)^{1/2} ≤ ∫ E_σ(g)^{1/2} dμ`,

that is `‖∫ g‖_{H^σ} ≤ ∫ ‖g‖_{H^σ}`. The integral on the left is the Bochner integral in `L²`;
the one on the right is the lower integral, and it may be infinite. Nothing is assumed about the
measurability of `g` in `H^σ`. The energy is a supremum of squares of continuous seminorms on
`L²` (`besselEnergy_eq_iSup_setLIntegral`, `eNorm_ballMultiplier_sq`). -/
theorem besselEnergy_integral_le (σ : ℝ) (g : α → ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (∫ a, g a ∂μ) ^ (1 / 2 : ℝ) ≤
      ∫⁻ a, besselEnergy σ (g a) ^ (1 / 2 : ℝ) ∂μ :=
  PDE.Analysis.rpow_half_integral_le_of_eq_iSup (fun N ↦ ballMultiplier ι n σ N)
    (fun f ↦ by
      rw [besselEnergy_eq_iSup_setLIntegral]
      simp only [eNorm_ballMultiplier_sq]) g

/-- **Minkowski's inequality for the Sobolev norm, through a bounded operator**: for a bounded
real-linear map `Φ` from a Banach space `X` to the finite families of `L²(ℝⁿ)` functions and
every `g : α → X`, `E_σ(Φ(∫ g))^{1/2} ≤ ∫ E_σ(Φ(g))^{1/2}`. -/
theorem besselEnergy_integral_comp_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (σ : ℝ) (Φ : X →L[ℝ] ι → Lp ℂ 2 (volume : Measure (ℝ^n))) (g : α → X) :
    besselEnergy σ (Φ (∫ a, g a ∂μ)) ^ (1 / 2 : ℝ) ≤
      ∫⁻ a, besselEnergy σ (Φ (g a)) ^ (1 / 2 : ℝ) ∂μ := by
  by_cases hg : Integrable g μ
  · rw [← Φ.integral_comp_comm hg]
    exact besselEnergy_integral_le σ _
  · have h0 : besselEnergy σ (0 : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) = 0 :=
      besselEnergy_fun_zero σ
    rw [integral_undef hg, map_zero, h0, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le

end SobolevSpace.Fractional
