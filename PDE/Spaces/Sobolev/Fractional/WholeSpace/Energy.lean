/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import PDE.Analysis.Fourier.L2Multiplier
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.BesselComparison
public import PDE.Analysis.Interpolation.WeightedL2

/-!
# Sobolev energies of real order on `L²`, and their interpolation

For a finite family `f` of functions in `L²(ℝⁿ)` and a real order `σ`, the energy
`E_σ(f) = ∑ⱼ ∫ (1 + |ξ|²)^σ |f̂ⱼ(ξ)|² dξ` is a number in `[0, ∞]`. For `σ ≥ 0` the functions of
finite energy are exactly the `L²` representatives of the Bessel potential space `H^σ(ℝⁿ)`, and
the energy is the square of its norm. The order is a real parameter of one functional on one
fixed space, so statements about different orders compare without casts, and a bound may have
an infinite side. The second half of the module is interpolation: if an additive operator has
`E_{b₀}(Tf) ≤ M₀ E_{a₀}(f)` and `E_{b₁}(Tf) ≤ M₁ E_{a₁}(f)` for all `f`, then
`E_{(1-θ)b₀+θb₁}(Tf) ≤ M₀^{1-θ} M₁^θ E_{(1-θ)a₀+θa₁}(f)` for `0 < θ < 1`. This turns estimates at
integer orders into estimates at all real orders. Negative orders are allowed in every
statement except the two comparisons with `H^σ(ℝⁿ)`. For `σ < 0` the energy is still defined,
but only on `L²`, which is a proper part of `H^σ`.

## Main results

* `besselEnergy`: the energy of order `σ` of a finite family of `L²` functions, with
  `besselEnergy_zero` (Plancherel: `E_0(f) = ∑ⱼ ‖fⱼ‖²`), `besselEnergy_mono` (the energy grows with
  the order), `besselEnergy_eq_sum` (it adds over the members) and `besselEnergy_eq_zero_iff`.
* `besselEnergy_le_rpow_mul_rpow`: `E_{(1-θ)a+θb} ≤ E_a^{1-θ} E_b^θ` for `0 ≤ θ ≤ 1`.
* `besselEnergy_toL2Fun`, `exists_toL2Fun_eq_of_besselEnergy_lt_top`: for `σ ≥ 0` the `L²`
  representative of `u ∈ H^σ(ℝⁿ)` has energy `‖u‖²`, and every `L²` function of finite energy is
  such a representative.
* `besselEnergy_fourierMultiplierL2`, `besselEnergy_fourierMultiplierL2_le`: for `m ∈ L^∞`,
  `E_σ(m(D) g) = ∫ (1 + |ξ|²)^σ |m|² ∑ⱼ |ĝⱼ|²`, so `E_σ(m(D) g) ≤ ‖m‖_∞² E_σ(g)`.
* `besselEnergy_add_add_besselEnergy_sub`: the parallelogram law
  `E_σ(f + g) + E_σ(f - g) = 2 (E_σ(f) + E_σ(g))`; `besselEnergy_smul`: `E_σ(c f) = |c|² E_σ(f)`.
* `besselEnergy_interpolation`: the interpolated bound above, for all additive maps between
  finite families of `L²` functions, all real orders and all constants `M₀`, `M₁ ≥ 0`.
* `besselEnergy_interpolation_of_split`: the same bound for every family of fields that admits
  the splitting, for instance real vector fields.

## How it works

The interpolation is the real method, `PDE.Analysis.Interpolation.lintegral_rpow_mul_le`. The two
hypotheses are weighted `L²` bounds for the densities `|f̂|²` and `|(Tf)^|²`, and the splitting
that the method asks for is a Fourier multiplier: `f = f₀ + f₁` with `f̂₁ = f̂ / (1 + q ρ)`,
`ρ = (1 + |ξ|²)^{a₁ - a₀}`. Its symbol is real, even and nowhere zero, which is what keeps the
pieces of a real field real. No density argument is used: the hypotheses are inequalities in
`[0, ∞]` for every `f ∈ L²`. If `M₀ = 0`, then `Tf` has energy zero, so it is zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298, and the definition of
  `H^s(ℝ^n)` for `s > 0` on p. 298, with the weight `1 + |y|^s` in place of `(1 + |y|²)^{s/2}`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform BesselPotentialSpace
open PDE.Analysis.Interpolation PDE.Analysis.Fourier
open scoped ENNReal NNReal BesselPotentialSpace

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-! ## The weight -/

/-- The weight `(1 + |ξ|²)^σ`. -/
def besselWeight (n : ℕ) (σ : ℝ) (ξ : ℝ^n) : ℝ≥0 := ((1 + ‖ξ‖ ^ 2) ^ σ).toNNReal

/-- The weight is measurable. -/
theorem measurable_besselWeight (σ : ℝ) : Measurable (besselWeight n σ) :=
  measurable_real_toNNReal.comp
    ((measurable_const.add (measurable_norm.pow_const 2)).pow_const σ)

/-- The weight in `[0, ∞]`. -/
theorem coe_besselWeight (σ : ℝ) (ξ : ℝ^n) :
    (besselWeight n σ ξ : ℝ≥0∞) = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ σ) := rfl

/-- The weight of order zero is one. -/
theorem coe_besselWeight_zero (ξ : ℝ^n) : (besselWeight n 0 ξ : ℝ≥0∞) = 1 := by
  rw [coe_besselWeight, Real.rpow_zero, ENNReal.ofReal_one]

/-- `(1 + |ξ|²)^{a+b} = (1 + |ξ|²)^a (1 + |ξ|²)^b`. -/
theorem besselWeight_add (a b : ℝ) (ξ : ℝ^n) :
    besselWeight n (a + b) ξ = besselWeight n a ξ * besselWeight n b ξ := by
  have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [besselWeight, besselWeight, besselWeight, Real.rpow_add hpos,
    Real.toNNReal_mul (Real.rpow_nonneg hpos.le _)]

/-- `((1 + |ξ|²)^a)^θ = (1 + |ξ|²)^{aθ}`. -/
theorem coe_besselWeight_rpow (a θ : ℝ) (ξ : ℝ^n) :
    (besselWeight n a ξ : ℝ≥0∞) ^ θ = besselWeight n (a * θ) ξ := by
  have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [coe_besselWeight, coe_besselWeight,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hpos a), ← Real.rpow_mul hpos.le]

/-- The weight grows with the order. -/
theorem besselWeight_mono {σ τ : ℝ} (h : σ ≤ τ) (ξ : ℝ^n) :
    besselWeight n σ ξ ≤ besselWeight n τ ξ :=
  Real.toNNReal_le_toNNReal
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) h)

/-! ## The energy -/

section Energy

variable {ι : Type*} [Fintype ι]

/-- The density `∑ⱼ |f̂ⱼ(ξ)|²` of a finite family of `L²` functions. -/
def fourierDensity (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) (ξ : ℝ^n) : ℝ≥0∞ :=
  ∑ j, ‖(𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2

/-- The density is measurable. -/
theorem measurable_fourierDensity (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    Measurable (fourierDensity f) :=
  Finset.measurable_fun_sum _ fun j _ ↦
    ((Lp.stronglyMeasurable (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n)))).eNorm).pow_const 2

/-- **The Sobolev energy of order `σ`** of a finite family `f` of `L²` functions:
`E_σ(f) = ∑ⱼ ∫ (1 + |ξ|²)^σ |f̂ⱼ(ξ)|² dξ`, in `[0, ∞]`. For `σ ≥ 0` the family is in `H^σ` exactly
when the energy is finite, and then the energy is the square of the norm
(`besselEnergy_toL2Fun`, `exists_toL2Fun_eq_of_besselEnergy_lt_top`). -/
def besselEnergy (σ : ℝ) (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ≥0∞ :=
  ∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * fourierDensity f ξ

/-- The energy of one function: `E_σ(g) = ∫ (1 + |ξ|²)^σ |ĝ(ξ)|² dξ`. -/
theorem besselEnergy_unit_eq_lintegral (σ : ℝ) (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (fun _ : Unit ↦ g) =
      ∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * ‖(𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := by
  simp only [besselEnergy, fourierDensity, Finset.univ_unique, Finset.sum_singleton]

/-- The energy grows with the order. -/
theorem besselEnergy_mono {σ τ : ℝ} (h : σ ≤ τ) (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ f ≤ besselEnergy τ f :=
  lintegral_mono fun ξ ↦ mul_le_mul' (ENNReal.coe_le_coe.2 (besselWeight_mono h ξ)) le_rfl

/-- **Plancherel.** The energy of order zero is `∑ⱼ ‖fⱼ‖²`. -/
theorem besselEnergy_zero (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy 0 f = ∑ j, ENNReal.ofReal (‖f j‖ ^ 2) := by
  simp only [besselEnergy, coe_besselWeight_zero, one_mul, fourierDensity]
  rw [lintegral_finsetSum _ fun j _ ↦
    ((Lp.stronglyMeasurable (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n)))).eNorm).pow_const 2]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))))
  have h3 : ∫⁻ ξ, ‖(𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 =
      eLpNorm (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))) 2 volume ^ 2 := by
    simpa [ENNReal.rpow_two] using h2.symm
  rw [h3, ENNReal.ofReal_pow (norm_nonneg _), ← Lp.norm_fourier_eq, Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_ne_top]

/-- **The energies are logarithmically convex in the order**:
`E_{(1-θ)a+θb}(f) ≤ E_a(f)^{1-θ} E_b(f)^θ` for `0 ≤ θ ≤ 1`. This is Hölder's inequality. -/
theorem besselEnergy_le_rpow_mul_rpow (a b : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy ((1 - θ) * a + θ * b) f ≤ besselEnergy a f ^ (1 - θ) * besselEnergy b f ^ θ := by
  have hma : AEMeasurable (fun ξ : ℝ^n ↦ (besselWeight n a ξ : ℝ≥0∞) * fourierDensity f ξ) :=
    ((measurable_coe_nnreal_ennreal.comp (measurable_besselWeight a)).mul
      (measurable_fourierDensity f)).aemeasurable
  have hmb : AEMeasurable (fun ξ : ℝ^n ↦ (besselWeight n b ξ : ℝ≥0∞) * fourierDensity f ξ) :=
    ((measurable_coe_nnreal_ennreal.comp (measurable_besselWeight b)).mul
      (measurable_fourierDensity f)).aemeasurable
  have h1θ : 0 ≤ 1 - θ := by linarith
  refine le_trans (le_of_eq ?_) (ENNReal.lintegral_mul_norm_pow_le hma hmb h1θ hθ0 (by ring))
  refine lintegral_congr fun ξ ↦ ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ, ENNReal.mul_rpow_of_nonneg _ _ hθ0,
    coe_besselWeight_rpow, coe_besselWeight_rpow, mul_mul_mul_comm, ← ENNReal.coe_mul,
    ← besselWeight_add, ← ENNReal.rpow_add_of_nonneg _ _ h1θ hθ0, sub_add_cancel,
    ENNReal.rpow_one, mul_comm a, mul_comm b]

end Energy

/-- **The energy is the Bessel norm.** For `s ≥ 0` and `u ∈ H^s(ℝⁿ)`, the energy of order `s`
of the `L²` representative of `u` is `‖u‖²`. -/
theorem besselEnergy_toL2Fun {s : ℝ} (hs : 0 ≤ s) (u : H^{s}(ℝ^n)) :
    besselEnergy s (fun _ : Unit ↦ toL2Fun hs u) = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [norm_sq_eq_lintegral hs u]
  simp [besselEnergy, fourierDensity, coe_besselWeight]

/-! ## Families and single functions -/

/-- **The energy of a family is the sum of the energies of its members.** -/
theorem besselEnergy_eq_sum {ι : Type*} [Fintype ι] (σ : ℝ)
    (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ f = ∑ j, besselEnergy σ (fun _ : Unit ↦ f j) := by
  simp only [besselEnergy, fourierDensity, Finset.univ_unique, Finset.sum_singleton,
    Finset.mul_sum]
  exact lintegral_finsetSum _ fun j _ ↦
    (measurable_coe_nnreal_ennreal.comp (measurable_besselWeight σ)).mul
      (((Lp.stronglyMeasurable (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n)))).eNorm).pow_const 2)

/-- The energy of one function is the square of the `L²` norm of its transform times the Bessel
symbol. -/
theorem besselEnergy_unit (σ : ℝ) (g : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (fun _ : Unit ↦ g) = eLpNorm (fun ξ ↦ besselSymbol n σ ξ *
      (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume ^ 2 := by
  have hm : AEStronglyMeasurable (fun ξ ↦ besselSymbol n σ ξ *
      (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) volume :=
    continuous_besselSymbol.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hm
  have h3 : eLpNorm (fun ξ ↦ besselSymbol n σ ξ *
      (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume ^ 2 =
        ∫⁻ ξ, ‖besselSymbol n σ ξ * (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := by
    simpa [ENNReal.rpow_two] using h2
  rw [h3, besselEnergy_unit_eq_lintegral]
  refine lintegral_congr fun ξ ↦ ?_
  rw [eNorm_mul, mul_pow, enorm_besselSymbol_sq, coe_besselWeight]

open TemperedDistribution in
open scoped SchwartzMap in
/-- **Every `L²` function of finite energy of order `σ ≥ 0` is the representative of an element
of `H^σ(ℝⁿ)`.** If `g ∈ L²(ℝⁿ)` and `∫ (1 + |ξ|²)^σ |ĝ|² < ∞`, there is `u ∈ H^σ(ℝⁿ)` whose `L²`
representative is `g`. With `besselEnergy_toL2Fun` this identifies the functions of finite energy
with the Bessel potential space. The energy is the square of the `L²` norm of
`(1 + |ξ|²)^{σ/2} ĝ`, and its finiteness is the criterion `memSobolev_iff_memLp_besselWeight` for
the distribution of `g`. -/
theorem exists_toL2Fun_eq_of_besselEnergy_lt_top {σ : ℝ} (hσ : 0 ≤ σ)
    (g : Lp ℂ 2 (volume : Measure (ℝ^n))) (h : besselEnergy σ (fun _ : Unit ↦ g) < ⊤) :
    ∃ u : H^{σ}(ℝ^n), toL2Fun hσ u = g := by
  rw [besselEnergy_unit] at h
  have hfin : eLpNorm (fun ξ ↦ besselSymbol n σ ξ *
      (𝓕 g : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ) 2 volume < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  have hs : MemSobolev σ 2 ((g : Lp ℂ 2 volume) : 𝓢'(ℝ^n, ℂ)) :=
    (memSobolev_iff_memLp_besselWeight σ g).mpr hfin
  refine ⟨hs.toBesselPotentialSpace, ?_⟩
  apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
  change ((toL2Fun hσ hs.toBesselPotentialSpace : Lp ℂ 2 volume) : 𝓢'(ℝ^n, ℂ)) =
    ((g : Lp ℂ 2 volume) : 𝓢'(ℝ^n, ℂ))
  rw [← toDistr_eq_toL2Fun]
  exact hs.toBesselPotentialSpace_toDistr

/-- **The energy of a Fourier multiplier**: for every real `σ`, every `m ∈ L^∞` and every finite
family `g` of `L²` functions, `E_σ(m(D) g) = ∫ (1 + |ξ|²)^σ |m(ξ)|² ∑ⱼ |ĝⱼ(ξ)|² dξ`. The
transform of `m(D) g` is `m ĝ`. -/
theorem besselEnergy_fourierMultiplierL2 {ι : Type*} [Fintype ι] (σ : ℝ)
    (m : Lp ℂ ∞ (volume : Measure (ℝ^n))) (g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (fun j ↦ fourierMultiplierL2 m (g j)) =
      ∫⁻ ξ, (besselWeight n σ ξ : ℝ≥0∞) * (‖m ξ‖ₑ ^ 2 * fourierDensity g ξ) := by
  have hF (j : ι) : ∀ᵐ ξ : ℝ^n,
      ‖(𝓕 (fourierMultiplierL2 m (g j)) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 =
        ‖m ξ‖ₑ ^ 2 * ‖(𝓕 (g j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := by
    rw [fourierMultiplierL2_apply, fourier_fourierInv_eq]
    filter_upwards [Lp.coeFn_lpSMul (r := 2) m
      (𝓕 (g j) : Lp ℂ 2 (volume : Measure (ℝ^n)))] with ξ h1
    rw [h1, Pi.smul_apply', smul_eq_mul, eNorm_mul, mul_pow]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hF] with ξ hξ
  simp only [fourierDensity, hξ, Finset.mul_sum]

/-- **A bounded Fourier multiplier does not change the order**: for every real `σ`, every
`m ∈ L^∞` and every finite family `g` of `L²` functions, `E_σ(m(D) g) ≤ ‖m‖_∞² E_σ(g)`. -/
theorem besselEnergy_fourierMultiplierL2_le {ι : Type*} [Fintype ι] (σ : ℝ)
    (m : Lp ℂ ∞ (volume : Measure (ℝ^n))) (g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (fun j ↦ fourierMultiplierL2 m (g j)) ≤ ‖m‖ₑ ^ 2 * besselEnergy σ g := by
  have hm : ∀ᵐ ξ : ℝ^n, ‖m ξ‖ₑ ≤ ‖m‖ₑ := by
    rw [Lp.eNorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable m)]
    exact ae_le_eLpNormEssSup
  rw [besselEnergy_fourierMultiplierL2, besselEnergy, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono_ae ?_
  filter_upwards [hm] with ξ hξ
  exact (mul_le_mul' le_rfl (mul_le_mul' (pow_le_pow_left₀ zero_le hξ 2) le_rfl)).trans_eq
    (mul_left_comm _ _ _)

/-- The energy is homogeneous of degree two: `E_σ(c f) = |c|² E_σ(f)`. -/
theorem besselEnergy_smul {ι : Type*} [Fintype ι] (σ : ℝ) (c : ℂ)
    (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (c • f) = ‖c‖ₑ ^ 2 * besselEnergy σ f := by
  have hF (j : ι) : ∀ᵐ ξ : ℝ^n,
      ‖(𝓕 ((c • f) j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 =
        ‖c‖ₑ ^ 2 * ‖(𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 := by
    have h : (𝓕 ((c • f) j) : Lp ℂ 2 (volume : Measure (ℝ^n))) = c • 𝓕 (f j) :=
      map_smul (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) c (f j)
    rw [h]
    filter_upwards [Lp.coeFn_smul c (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n)))] with ξ hξ
    rw [hξ, Pi.smul_apply, smul_eq_mul, eNorm_mul, mul_pow]
  rw [besselEnergy, besselEnergy, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hF] with ξ hξ
  simp only [fourierDensity, hξ, ← Finset.mul_sum]
  ring

/-- The zero family has energy zero: `besselEnergy_smul` at `c = 0`. -/
theorem besselEnergy_fun_zero {ι : Type*} [Fintype ι] (σ : ℝ) :
    besselEnergy σ (fun _ : ι ↦ (0 : Lp ℂ 2 (volume : Measure (ℝ^n)))) = 0 := by
  have h := besselEnergy_smul σ 0 (fun _ : ι ↦ (0 : Lp ℂ 2 (volume : Measure (ℝ^n))))
  rw [eNorm_zero, zero_pow two_ne_zero, zero_mul, zero_smul] at h
  exact h

/-- The energy does not see the sign, `E_σ(-f) = E_σ(f)`: `besselEnergy_smul` at `c = -1`. -/
theorem besselEnergy_neg {ι : Type*} [Fintype ι] (σ : ℝ)
    (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) : besselEnergy σ (-f) = besselEnergy σ f := by
  have h := besselEnergy_smul σ (-1) f
  rwa [neg_one_smul, eNorm_neg, ← ofReal_norm, norm_one, ENNReal.ofReal_one, one_pow,
    one_mul] at h

/-- **A family has energy zero exactly when it is zero**, for every real order: the weight is
positive, so the transforms vanish almost everywhere. -/
theorem besselEnergy_eq_zero_iff {ι : Type*} [Fintype ι] {σ : ℝ}
    {f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))} : besselEnergy σ f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; exact besselEnergy_fun_zero σ⟩
  have hm : Measurable fun ξ ↦ (besselWeight n σ ξ : ℝ≥0∞) * fourierDensity f ξ :=
    (measurable_coe_nnreal_ennreal.comp (measurable_besselWeight σ)).mul
      (measurable_fourierDensity f)
  have hρ : ∀ᵐ ξ : ℝ^n, fourierDensity f ξ = 0 := by
    filter_upwards [(lintegral_eq_zero_iff hm).1 h] with ξ hξ
    have hξ' : (besselWeight n σ ξ : ℝ≥0∞) * fourierDensity f ξ = 0 := hξ
    have hw : (besselWeight n σ ξ : ℝ≥0∞) ≠ 0 := by
      rw [coe_besselWeight]
      exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (by positivity) σ)).ne'
    exact (mul_eq_zero.1 hξ').resolve_left hw
  have h0 : besselEnergy 0 f = 0 := by
    rw [besselEnergy]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hρ] with ξ hξ
    rw [hξ, mul_zero]
  rw [besselEnergy_zero] at h0
  funext j
  have hj := Finset.sum_eq_zero_iff.1 h0 j (Finset.mem_univ j)
  rw [ENNReal.ofReal_eq_zero] at hj
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm hj (sq_nonneg _)))

/-- The parallelogram law for the modulus of complex numbers, in `[0, ∞]`. -/
theorem eNorm_add_sq_add_eNorm_sub_sq (a b : ℂ) :
    ‖a + b‖ₑ ^ 2 + ‖a - b‖ₑ ^ 2 = 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
  have h := parallelogram_law_with_norm ℝ a b
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact congrArg ENNReal.ofReal h

/-- **The parallelogram law for the energy**: `E_σ(f + g) + E_σ(f - g) = 2 (E_σ(f) + E_σ(g))`,
for all families, of finite energy or not. The energy is the square of a Hilbert norm. -/
theorem besselEnergy_add_add_besselEnergy_sub {ι : Type*} [Fintype ι] (σ : ℝ)
    (f g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (f + g) + besselEnergy σ (f - g) =
      2 * (besselEnergy σ f + besselEnergy σ g) := by
  have hm (h : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
      Measurable fun ξ ↦ (besselWeight n σ ξ : ℝ≥0∞) * fourierDensity h ξ :=
    (measurable_coe_nnreal_ennreal.comp (measurable_besselWeight σ)).mul
      (measurable_fourierDensity h)
  have hF (j : ι) : ∀ᵐ ξ : ℝ^n,
      ‖(𝓕 ((f + g) j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 +
        ‖(𝓕 ((f - g) j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 =
      2 * (‖(𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2 +
        ‖(𝓕 (g j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ‖ₑ ^ 2) := by
    have h1 : (𝓕 ((f + g) j) : Lp ℂ 2 (volume : Measure (ℝ^n))) = 𝓕 (f j) + 𝓕 (g j) :=
      map_add (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) (f j) (g j)
    have h2 : (𝓕 ((f - g) j) : Lp ℂ 2 (volume : Measure (ℝ^n))) = 𝓕 (f j) - 𝓕 (g j) :=
      map_sub (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) (f j) (g j)
    rw [h1, h2]
    filter_upwards [Lp.coeFn_add (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))) (𝓕 (g j)),
      Lp.coeFn_sub (𝓕 (f j) : Lp ℂ 2 (volume : Measure (ℝ^n))) (𝓕 (g j))] with ξ h3 h4
    rw [h3, h4, Pi.add_apply, Pi.sub_apply, eNorm_add_sq_add_eNorm_sub_sq]
  rw [besselEnergy, besselEnergy, besselEnergy, besselEnergy, ← lintegral_add_left (hm _),
    ← lintegral_add_left (hm _), ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hF] with ξ hξ
  simp only [fourierDensity]
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun j _ ↦ hξ j, ← Finset.mul_sum]
  ring

/-- **The energy of a sum**: `E_σ(f + g) ≤ 2 (E_σ(f) + E_σ(g))`, from the parallelogram law. -/
theorem besselEnergy_add_le {ι : Type*} [Fintype ι] (σ : ℝ)
    (f g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (f + g) ≤ 2 * (besselEnergy σ f + besselEnergy σ g) :=
  le_self_add.trans_eq (besselEnergy_add_add_besselEnergy_sub σ f g)

/-- **The energy of a difference**: `E_σ(f - g) ≤ 2 (E_σ(f) + E_σ(g))`. -/
theorem besselEnergy_sub_le {ι : Type*} [Fintype ι] (σ : ℝ)
    (f g : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy σ (f - g) ≤ 2 * (besselEnergy σ f + besselEnergy σ g) :=
  le_add_self.trans_eq (besselEnergy_add_add_besselEnergy_sub σ f g)

/-! ## Interpolation -/

section Interpolation

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The elementary inequality behind the splitting: `l/(1+l) |a + b|² ≤ |a|² + l |b|²`. -/
theorem kFrac_mul_eNorm_add_sq_le {G : Type*} [NormedAddCommGroup G] (l : ℝ≥0) (a b : G) :
    (kFrac l : ℝ≥0∞) * ‖a + b‖ₑ ^ 2 ≤ ‖a‖ₑ ^ 2 + l * ‖b‖ₑ ^ 2 := by
  have hreal : (kFrac l : ℝ) * ‖a + b‖ ^ 2 ≤ ‖a‖ ^ 2 + l * ‖b‖ ^ 2 := by
    have hl : (0 : ℝ) ≤ l := l.coe_nonneg
    have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    have h2 : (kFrac l : ℝ) = l / (1 + l) := by simp [kFrac]
    rw [h2, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖a‖ - l * ‖b‖), norm_nonneg a, norm_nonneg b,
      mul_le_mul_of_nonneg_left h1 hl]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal (p := kFrac l),
    ← ENNReal.ofReal_coe_nnreal (p := l), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), ← ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The symbol `1 / (1 + q (1 + |ξ|²)^d)` of the splitting. -/
private def splitSymbol (n : ℕ) (q : ℝ≥0) (d : ℝ) (ξ : ℝ^n) : ℝ≥0 :=
  (1 + q * besselWeight n d ξ)⁻¹

/-- One minus the symbol of the splitting is `l / (1 + l)` at `l = q (1 + |ξ|²)^d`. -/
private theorem one_sub_splitSymbol (q : ℝ≥0) (d : ℝ) (ξ : ℝ^n) :
    (1 : ℝ) - splitSymbol n q d ξ = kFrac (q * besselWeight n d ξ) := by
  have hne : (1 + (q : ℝ) * (besselWeight n d ξ : ℝ)) ≠ 0 := by positivity
  simp only [kFrac, splitSymbol]
  push_cast
  field_simp
  ring

/-- The modulus of a nonnegative real number, as a complex number. -/
private theorem eNorm_coe_nnreal (r : ℝ≥0) : ‖(((r : ℝ≥0) : ℝ) : ℂ)‖ₑ = r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]

/-- The symbol of the splitting is bounded by one, so it is an element of `L^∞`. -/
private theorem exists_splitSymbol (q : ℝ≥0) (d : ℝ) :
    ∃ m : Lp ℂ ∞ (volume : Measure (ℝ^n)),
      (m : ℝ^n → ℂ) =ᵐ[volume] fun ξ ↦ ((splitSymbol n q d ξ : ℝ) : ℂ) := by
  have hcm : Measurable fun ξ : ℝ^n ↦ ((splitSymbol n q d ξ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp
      (measurable_const.add ((measurable_besselWeight d).const_mul q)).inv)
  have hmem : MemLp (fun ξ : ℝ^n ↦ ((splitSymbol n q d ξ : ℝ) : ℂ)) ∞ volume :=
    memLp_top_of_bound hcm.aestronglyMeasurable 1 (Eventually.of_forall fun ξ ↦ by
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      have h : splitSymbol n q d ξ ≤ 1 :=
        inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))
      exact_mod_cast h)
  exact ⟨hmem.toLp _, hmem.coeFn_toLp⟩

/-- The symbol of the splitting is even, real and nowhere zero. -/
private theorem splitSymbol_props (q : ℝ≥0) (d : ℝ) :
    (∀ ξ : ℝ^n, ((splitSymbol n q d (-ξ) : ℝ) : ℂ) = ((splitSymbol n q d ξ : ℝ) : ℂ)) ∧
      (∀ ξ : ℝ^n, (starRingEnd ℂ) ((splitSymbol n q d ξ : ℝ) : ℂ) =
        ((splitSymbol n q d ξ : ℝ) : ℂ)) ∧
      ∀ ξ : ℝ^n, ((splitSymbol n q d ξ : ℝ) : ℂ) ≠ 0 := by
  refine ⟨fun ξ ↦ ?_, fun ξ ↦ Complex.conj_ofReal _, fun ξ ↦ ?_⟩
  · simp only [splitSymbol, besselWeight, norm_neg]
  · have h : splitSymbol n q d ξ ≠ 0 := inv_ne_zero (by positivity)
    exact_mod_cast h

/-- **Interpolation between Sobolev orders, for a family of fields that admits the splitting.**
Let `Φ x` and `Ψ x` be finite families of `L²` functions indexed by `x : X`, with
`E_{b₀}(Ψ x) ≤ M₀ E_{a₀}(Φ x)` and `E_{b₁}(Ψ x) ≤ M₁ E_{a₁}(Φ x)` for all `x`. Suppose
that for every `x` and every real, even, nowhere vanishing bounded symbol `m` there are `x₀` and
`x₁` such that `Φ x₁` is the Fourier multiplier `m` applied to `Φ x`, `Φ x₀ = Φ x - Φ x₁`, and
`Ψ x = Ψ x₀ + Ψ x₁`. Then, for `0 < θ < 1`,
`E_{(1-θ)b₀+θb₁}(Ψ x) ≤ M₀^{1-θ} M₁^θ E_{(1-θ)a₀+θa₁}(Φ x)`.

With `Φ` the identity and `Ψ = T` additive this is `besselEnergy_interpolation`. The general form
serves real fields: there `X` is a space of real vector fields, `Φ` complexifies the components,
and the splitting stays real because the symbol is real and even. -/
theorem besselEnergy_interpolation_of_split {X : Type*}
    {Φ : X → ι → Lp ℂ 2 (volume : Measure (ℝ^n))} {Ψ : X → κ → Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hsplit : ∀ (x : X) (m : Lp ℂ ∞ (volume : Measure (ℝ^n))) (M : ℝ^n → ℂ),
      ⇑m =ᵐ[volume] M → (∀ ξ, M (-ξ) = M ξ) → (∀ ξ, (starRingEnd ℂ) (M ξ) = M ξ) →
      (∀ ξ, M ξ ≠ 0) → ∃ x₀ x₁ : X, (∀ j, Φ x₁ j = fourierMultiplierL2 m (Φ x j)) ∧
        (∀ j, Φ x₀ j = Φ x j - fourierMultiplierL2 m (Φ x j)) ∧
        ∀ k, Ψ x k = Ψ x₀ k + Ψ x₁ k)
    {a₀ a₁ b₀ b₁ : ℝ} {M₀ M₁ : ℝ≥0}
    (h0 : ∀ x, besselEnergy b₀ (Ψ x) ≤ M₀ * besselEnergy a₀ (Φ x))
    (h1 : ∀ x, besselEnergy b₁ (Ψ x) ≤ M₁ * besselEnergy a₁ (Φ x))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (x : X) :
    besselEnergy ((1 - θ) * b₀ + θ * b₁) (Ψ x) ≤
      (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * besselEnergy ((1 - θ) * a₀ + θ * a₁) (Φ x) := by
  -- for `M₀ = 0` the family `Ψ x` is zero
  rcases eq_or_ne M₀ 0 with rfl | hM₀
  · have hz : besselEnergy b₀ (Ψ x) = 0 := by
      have h := h0 x
      rwa [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
    have hT0 : besselEnergy ((1 - θ) * b₀ + θ * b₁) (Ψ x) = 0 :=
      besselEnergy_eq_zero_iff.2 (besselEnergy_eq_zero_iff.1 hz)
    rw [hT0]
    exact zero_le
  -- the weights of the interpolated orders
  have hw (c d : ℝ) (ξ : ℝ^n) (D : ℝ≥0∞) : (besselWeight n (d - c) ξ : ℝ≥0∞) ^ θ *
      ((besselWeight n c ξ : ℝ≥0∞) * D) = (besselWeight n ((1 - θ) * c + θ * d) ξ : ℝ≥0∞) * D := by
    rw [coe_besselWeight_rpow, ← mul_assoc, ← ENNReal.coe_mul, ← besselWeight_add]
    congr 3
    ring
  have hw1 (c d : ℝ) (ξ : ℝ^n) (D : ℝ≥0∞) : (besselWeight n c ξ : ℝ≥0∞) *
      (besselWeight n (d - c) ξ : ℝ≥0∞) * D = (besselWeight n d ξ : ℝ≥0∞) * D := by
    rw [← ENNReal.coe_mul, ← besselWeight_add]
    congr 3
    ring
  have key := lintegral_rpow_mul_le (μ := (volume : Measure (ℝ^n)))
    (ν := (volume : Measure (ℝ^n)))
    (e := fun x : X ↦ fourierDensity (Φ x)) (g := fun x : X ↦ fourierDensity (Ψ x))
    (w₀ := besselWeight n a₀) (ρ := besselWeight n (a₁ - a₀)) (v₀ := besselWeight n b₀)
    (r := besselWeight n (b₁ - b₀)) (M₀ := M₀) (M₁ := M₁)
    (fun x ↦ measurable_fourierDensity (Φ x)) (fun x ↦ measurable_fourierDensity (Ψ x))
    (measurable_besselWeight _) (measurable_besselWeight _) (measurable_besselWeight _)
    (measurable_besselWeight _) hM₀ h0
    (fun x ↦ by simpa only [hw1, besselEnergy] using h1 x) ?_ hθ0 hθ1 x
  · simpa only [hw, besselEnergy] using key
  -- the splitting
  intro x q
  obtain ⟨m, hm⟩ := exists_splitSymbol (n := n) q (a₁ - a₀)
  obtain ⟨heven, hreal, hne⟩ := splitSymbol_props (n := n) q (a₁ - a₀)
  obtain ⟨x₀, x₁, hx₁, hx₀, hΨ⟩ := hsplit x m _ hm heven hreal hne
  have hF₁ (j : ι) : ((𝓕 (Φ x₁ j) : Lp ℂ 2 (volume : Measure (ℝ^n))) :
      ℝ^n → ℂ) =ᵐ[volume] fun ξ ↦ ((splitSymbol n q (a₁ - a₀) ξ : ℝ) : ℂ) *
        (𝓕 (Φ x j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ := by
    have h : (𝓕 (Φ x₁ j) : Lp ℂ 2 (volume : Measure (ℝ^n))) =
        m • (𝓕 (Φ x j) : Lp ℂ 2 (volume : Measure (ℝ^n))) := by
      rw [hx₁, fourierMultiplierL2_apply, fourier_fourierInv_eq]
    rw [h]
    filter_upwards [Lp.coeFn_lpSMul (r := 2) m (𝓕 (Φ x j) : Lp ℂ 2 (volume : Measure (ℝ^n))),
      hm] with ξ h1 h2
    rw [h1, Pi.smul_apply', h2, smul_eq_mul]
  have hF₀ (j : ι) : ((𝓕 (Φ x₀ j) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
      fun ξ ↦ ((kFrac (q * besselWeight n (a₁ - a₀) ξ) : ℝ) : ℂ) *
        (𝓕 (Φ x j) : Lp ℂ 2 (volume : Measure (ℝ^n))) ξ := by
    have h : (𝓕 (Φ x₀ j) : Lp ℂ 2 (volume : Measure (ℝ^n))) =
        (𝓕 (Φ x j) : Lp ℂ 2 (volume : Measure (ℝ^n))) - 𝓕 (Φ x₁ j) := by
      rw [hx₀, hx₁]
      exact map_sub (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) _ _
    rw [h]
    filter_upwards [Lp.coeFn_sub (𝓕 (Φ x j) : Lp ℂ 2 (volume : Measure (ℝ^n)))
      (𝓕 (Φ x₁ j)), hF₁ j] with ξ h1 h2
    rw [h1, Pi.sub_apply, h2, ← one_sub_splitSymbol]
    push_cast
    ring
  refine ⟨x₀, x₁, ?_, ?_, ?_⟩
  · -- the density of the first piece
    filter_upwards [ae_all_iff.2 hF₀] with ξ hξ
    refine le_of_eq ?_
    simp only [fourierDensity, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hξ j, eNorm_mul, mul_pow, eNorm_coe_nnreal, ENNReal.coe_pow]
  · -- the density of the second piece
    filter_upwards [ae_all_iff.2 hF₁] with ξ hξ
    refine le_of_eq ?_
    simp only [fourierDensity, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hξ j, eNorm_mul, mul_pow, eNorm_coe_nnreal, ENNReal.coe_pow]
    rfl
  · -- the target side
    have hF (k : κ) : ((𝓕 (Ψ x k) : Lp ℂ 2 (volume : Measure (ℝ^n))) : ℝ^n → ℂ) =ᵐ[volume]
        fun η ↦ (𝓕 (Ψ x₀ k) : Lp ℂ 2 (volume : Measure (ℝ^n))) η +
          (𝓕 (Ψ x₁ k) : Lp ℂ 2 (volume : Measure (ℝ^n))) η := by
      have h : (𝓕 (Ψ x k) : Lp ℂ 2 (volume : Measure (ℝ^n))) =
          (𝓕 (Ψ x₀ k) : Lp ℂ 2 (volume : Measure (ℝ^n))) + 𝓕 (Ψ x₁ k) := by
        rw [hΨ]
        exact map_add (Lp.fourierTransformₗᵢ (ℝ^n) ℂ) _ _
      rw [h]
      exact Lp.coeFn_add _ _
    filter_upwards [ae_all_iff.2 hF] with η hη l
    simp only [fourierDensity, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [hη k]
    exact kFrac_mul_eNorm_add_sq_le l _ _

/-- **Interpolation between Sobolev orders.** Let `T` be an additive map between finite
families of `L²` functions with `E_{b₀}(Tf) ≤ M₀ E_{a₀}(f)` and `E_{b₁}(Tf) ≤ M₁ E_{a₁}(f)` for
all `f`. Then, for `0 < θ < 1`,
`E_{(1-θ)b₀+θb₁}(Tf) ≤ M₀^{1-θ} M₁^θ E_{(1-θ)a₀+θa₁}(f)`.

Both sides may be infinite; the statement says in particular that `T` maps the intermediate
space into the intermediate space. No density argument is used: the two hypotheses are
inequalities in `[0, ∞]` for every `f ∈ L²`. The proof is the real method
(`PDE.Analysis.Interpolation.lintegral_rpow_mul_le`); the splitting `f = f₀ + f₁` is the Fourier
multiplier with the symbol `1 / (1 + q (1 + |ξ|²)^{a₁ - a₀})`. -/
theorem besselEnergy_interpolation
    {T : (ι → Lp ℂ 2 (volume : Measure (ℝ^n))) → κ → Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hT : ∀ f g, T (f + g) = T f + T g) {a₀ a₁ b₀ b₁ : ℝ} {M₀ M₁ : ℝ≥0}
    (h0 : ∀ f, besselEnergy b₀ (T f) ≤ M₀ * besselEnergy a₀ f)
    (h1 : ∀ f, besselEnergy b₁ (T f) ≤ M₁ * besselEnergy a₁ f)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (f : ι → Lp ℂ 2 (volume : Measure (ℝ^n))) :
    besselEnergy ((1 - θ) * b₀ + θ * b₁) (T f) ≤
      (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * besselEnergy ((1 - θ) * a₀ + θ * a₁) f := by
  refine besselEnergy_interpolation_of_split (Φ := fun f ↦ f) (Ψ := T)
    (fun f m M _ _ _ _ ↦ ⟨fun j ↦ f j - fourierMultiplierL2 m (f j),
      fun j ↦ fourierMultiplierL2 m (f j), fun _ ↦ rfl, fun _ ↦ rfl, fun k ↦ ?_⟩)
    h0 h1 hθ0 hθ1 f
  have hsum : f = (fun j ↦ f j - fourierMultiplierL2 m (f j)) +
      fun j ↦ fourierMultiplierL2 m (f j) := by
    funext j
    simp
  conv_lhs => rw [hsum, hT]
  rfl

end Interpolation

end SobolevSpace.Fractional
