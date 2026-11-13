/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Mollification in finite `Lᵖ` spaces

Two facts about convolution with the scaled mollifier `ρ_ε` on `ℝ^n`, for `1 ≤ p < ∞` and
functions valued in a real Banach space `X`.

The first is the contraction bound `‖ρ_ε ⋆ f‖_{Lᵖ} ≤ ‖f‖_{Lᵖ}`. It is the case `‖ρ_ε‖_{L¹} = 1`
of Young's inequality with exponents `1` and `p`, but we prove it directly: since `ρ_ε` is
nonnegative with mass one it defines a probability measure `ν_ε`. Comparing the `L¹` and `Lᵖ`
norms on this probability space gives the pointwise bound
`‖(ρ_ε ⋆ f)(x)‖^p ≤ ∫ ‖f(x - y)‖^p dν_ε(y)`, and Tonelli together with translation invariance of
Lebesgue measure integrates this to the claim.

The second is the approximate-identity property `‖ρ_ε ⋆ f - f‖_{Lᵖ} → 0` for every
`f ∈ Lᵖ` as the positive real parameter `ε` tends to zero. This follows from the
continuous compactly supported case
(`mollifyVector_converges_Lp_of_continuous_compactSupport` in `Mollification.Core`) by the usual
`δ/3` argument: approximate `f` in `Lᵖ` by `g ∈ C_c`, and control `ρ_ε ⋆ (f - g)` with the
contraction bound. Evans, PDE, Appendix C.5, Theorem 7(iv), proves both on `L^p_loc`: the
contraction is (5) in step 4 of that proof, obtained by Hölder's inequality against `η_ε`, and
the convergence is step 5, by approximation with continuous functions. Evans uses them for
the Sobolev approximation theorems of §5.3.

## Main results

* `MollifyLp.eLpNorm_mollifyVector_le`, `MollifyLp.eLpNorm_mollify_le`: the `Lᵖ` contraction for
  Banach-valued and real-valued mollification.
* `mollifyVector_converges_Lp`, `mollify_converges_Lp`: `Lᵖ` convergence of `ρ_{ε_m} ⋆ f` to `f`
  for `f ∈ Lᵖ`, `1 ≤ p < ∞`.
* `tendsto_eLpNorm_mollifyVector_sub`, `tendsto_eLpNorm_mollify_sub`: convergence along
  `nhdsWithin 0 (Ioi 0)`, without choosing a sequence of scales.
* `tendsto_eLpNorm_mollify_indicator_sub_on_subset`: convergence of the mollified zero extension
  on every measurable subset of the original domain.

## Implementation notes

The finiteness hypothesis `p ≠ ∞` is needed in both results: the contraction proof writes the
`Lᵖ` norm as a `p`-th power integral, and `C_c` is not dense in `L^∞`. The auxiliary probability
measure `ν_ε = volume.withDensity (ofReal ∘ ρ_ε)` and the Jensen step are private to the
`MollifyLp` namespace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.5, Theorem 7, pp. 713-715, steps 4 and 5 of the proof,
  p. 715, and §5.3.1, Theorem 1, pp. 264-265.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 4, for convolution, Young's inequality and approximation by mollifiers.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Convolution Pointwise Topology

namespace Approximation

variable {n : ℕ}

/-!
### `L^p`-boundedness / contraction for mollification

For `1 ≤ p < ∞`, convolution by a nonnegative compactly supported kernel of integral `1` is a
contraction on `L^p`.
-/
namespace MollifyLp

open MeasureTheory

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private noncomputable def ρMeasure (μ : Mollifier n) (ε : ℝ) : Measure (ℝ^n) :=
  (volume : Measure (ℝ^n)).withDensity fun x ↦ ENNReal.ofReal (scaled μ ε x)

private theorem ρMeasure_isProbability (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    IsProbabilityMeasure (ρMeasure (n := n) μ ε) := by
  classical
  have hcs : HasCompactSupport (scaled μ ε) := scaled_hasCompactSupport (μ := μ) (ε := ε) hε
  have hcont : Continuous (scaled μ ε) := (scaled_contDiff (μ := μ) (ε := ε)).continuous
  have hint : Integrable (scaled μ ε) (volume : Measure (ℝ^n)) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hnonneg : 0 ≤ᵐ[volume] scaled μ ε :=
    ae_of_all _ fun x ↦ scaled_nonneg (μ := μ) (ε := ε) hε x
  have hlin :
      (∫⁻ x, ENNReal.ofReal (scaled μ ε x) ∂ (volume : Measure (ℝ^n))) =
        ENNReal.ofReal (∫ x, scaled μ ε x ∂ (volume : Measure (ℝ^n))) := by
    simpa using (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
  refine ⟨?_⟩
  simp [ρMeasure, withDensity_apply, hlin, scaled_integral_one (μ := μ) (ε := ε) hε]

private theorem mollifyVector_eq_integral_ρMeasure
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (f : ℝ^n → X) (x : ℝ^n) :
    mollifyVector μ ε f x = ∫ y, f (x - y) ∂ (ρMeasure (n := n) μ ε) := by
  have hmeas : AEMeasurable (fun y ↦ ENNReal.ofReal (scaled μ ε y)) (volume : Measure (ℝ^n)) :=
    (scaled_contDiff (μ := μ)).continuous.measurable.ennreal_ofReal.aemeasurable
  have htoReal (y : ℝ^n) : (ENNReal.ofReal (scaled μ ε y)).toReal = scaled μ ε y :=
    ENNReal.toReal_ofReal (scaled_nonneg (μ := μ) hε y)
  rw [ρMeasure, integral_withDensity_eq_integral_toReal_smul₀ hmeas
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp [mollifyVector, MeasureTheory.convolution, htoReal]

/-- The `Lᵖ` contraction bound `‖ρ_ε ⋆ f‖_{Lᵖ} ≤ ‖f‖_{Lᵖ}` for `1 ≤ p < ∞` and Banach-valued
`f ∈ Lᵖ`. This is Young's inequality with an `L¹`-normalized kernel, proved via Jensen's
inequality through exponent comparison for the probability measure with density `ρ_ε`, then
Tonelli and translation invariance of Lebesgue measure. -/
theorem eLpNorm_mollifyVector_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    {f : ℝ^n → X} (hf : MemLp f p (volume : Measure (ℝ^n))) :
    eLpNorm (mollifyVector μ ε f) p (volume : Measure (ℝ^n)) ≤
      eLpNorm f p (volume : Measure (ℝ^n)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  let ν : Measure (ℝ^n) := ρMeasure (n := n) μ ε
  have : IsProbabilityMeasure ν := ρMeasure_isProbability μ hε
  -- On a probability space, the integral norm is bounded by every `Lᵖ` norm, `p ≥ 1`.
  have hpoint (x : ℝ^n) :
      ‖mollifyVector μ ε f x‖ₑ ^ p.toReal ≤ ∫⁻ y, ‖f (x - y)‖ₑ ^ p.toReal ∂ν := by
    have hmp : MeasurePreserving (fun y : ℝ^n ↦ x - y) volume volume := by
      simpa [sub_eq_add_neg, Function.comp_def] using
        (measurePreserving_add_left volume x).comp (Measure.measurePreserving_neg volume)
    have hfν : AEStronglyMeasurable (fun y ↦ f (x - y)) ν :=
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [mollifyVector_eq_integral_ρMeasure μ hε]
    have hnorm : ‖∫ y, f (x - y) ∂ν‖ₑ ≤ eLpNorm (fun y ↦ f (x - y)) p ν :=
      (enorm_integral_le_lintegral_enorm _).trans
        (lintegral_enorm_le_eLpNorm_one.trans (eLpNorm_le_eLpNorm_of_exponent_le hp1))
    have hpow := ENNReal.rpow_le_rpow hnorm hp_pos.le
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hfν,
      ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp_pos.ne', ENNReal.rpow_one] at hpow
  -- Tonelli and translation invariance remove the probability average.
  have hlin : (∫⁻ x, ‖mollifyVector μ ε f x‖ₑ ^ p.toReal ∂volume) ≤
      ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume := by
    calc
      _ ≤ ∫⁻ x, ∫⁻ y, ‖f (x - y)‖ₑ ^ p.toReal ∂ν ∂volume := lintegral_mono hpoint
      _ = ∫⁻ y, ∫⁻ x, ‖f (x - y)‖ₑ ^ p.toReal ∂volume ∂ν := by
        apply lintegral_lintegral_swap
        exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub (μ := volume) (ν := ν))).enorm.pow_const _
      _ = ∫⁻ y, ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume ∂ν := by
        exact lintegral_congr fun y ↦ lintegral_sub_right_eq_self (fun x ↦ ‖f x‖ₑ ^ p.toReal) y
      _ = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume := by simp
  have hmollMeas : AEStronglyMeasurable (mollifyVector μ ε f) volume :=
    (mollifyVector_contDiff_of_pos μ hε f
      (hf.locallyIntegrable hp1)).continuous.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hmollMeas,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf.aestronglyMeasurable]
  exact ENNReal.rpow_le_rpow hlin (by positivity)

/-- Scalar mollification is the real-valued specialization of the
Banach-valued contraction theorem. -/
theorem eLpNorm_mollify_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    {f : ℝ^n → ℝ} (hf : MemLp f p (volume : Measure (ℝ^n))) :
    eLpNorm (mollify μ ε f) p (volume : Measure (ℝ^n)) ≤
      eLpNorm f p (volume : Measure (ℝ^n)) := by
  simpa [mollify, mollifyVector] using
    (eLpNorm_mollifyVector_le (n := n) (p := p) μ hε hp hf)

end MollifyLp

/-- Mollifiers are an approximate identity on `Lᵖ(ℝ^n; X)` for `1 ≤ p < ∞`: if `ε_m → 0⁺` and
`f ∈ Lᵖ`, then `‖ρ_{ε_m} ⋆ f - f‖_{Lᵖ} → 0`. The proof approximates `f` in `Lᵖ` by a continuous
compactly supported `g`, applies `mollifyVector_converges_Lp_of_continuous_compactSupport` to `g`,
and controls the two error terms `ρ_ε ⋆ (f - g)` and `f - g` by the contraction bound
`eLpNorm_mollifyVector_le`. -/
theorem mollifyVector_converges_Lp
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    [CompleteSpace X]
    (μ : Mollifier n) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ^n → X} :
    ∀ ε : ℕ → ℝ,
      (∀ m, 0 < ε m) →
      Filter.Tendsto ε Filter.atTop (𝓝 0) →
      MemLp f p volume →
      Filter.Tendsto
        (fun m ↦
          eLpNorm (fun x ↦ mollifyVector μ (ε m) f x - f x) p volume)
        Filter.atTop (𝓝 0) := by
  intro ε hεpos hε0 hfLp
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ ↦ ?_
  have hδ3 : 0 < δ / 3 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  -- Approximate `f` in `Lᵖ` by a continuous compactly supported `g`.
  obtain ⟨g, hg_cs, hfg, hg_cont, hgLp⟩ :=
    hfLp.exists_hasCompactSupport_eLpNorm_sub_le (μ := volume) hp hδ3.ne'
  filter_upwards [ENNReal.tendsto_nhds_zero.1
    (mollifyVector_converges_Lp_of_continuous_compactSupport (μ := μ) (p := p) hp
      (hf_cont := hg_cont) (hf_cs := hg_cs) ε hεpos hε0) _ hδ3] with m hmg
  -- The contraction bound controls `ρ_ε ⋆ f - ρ_ε ⋆ g = ρ_ε ⋆ (f - g)`.
  have hA : eLpNorm (mollifyVector μ (ε m) f - mollifyVector μ (ε m) g) p volume ≤ δ / 3 := by
    rw [← mollifyVector_sub_of_pos μ f g (hfLp.locallyIntegrable hp1)
      (hgLp.locallyIntegrable hp1)]
    exact (MollifyLp.eLpNorm_mollifyVector_le μ (hεpos m) hp (hfLp.sub hgLp)).trans hfg
  have hC : eLpNorm (g - f) p volume ≤ δ / 3 := by rwa [eLpNorm_sub_comm]
  calc eLpNorm (fun x ↦ mollifyVector μ (ε m) f x - f x) p volume
      = eLpNorm ((mollifyVector μ (ε m) f - mollifyVector μ (ε m) g) +
          ((fun x ↦ mollifyVector μ (ε m) g x - g x) + (g - f))) p volume := by
        congr 1
        ext x
        simp only [Pi.add_apply, Pi.sub_apply]
        abel
    _ ≤ δ / 3 + (δ / 3 + δ / 3) := (eLpNorm_add_le hp1).trans
        (add_le_add hA ((eLpNorm_add_le hp1).trans (add_le_add hmg hC)))
    _ = δ := by rw [← add_assoc, ENNReal.add_thirds]

/-- Banach-valued mollification converges in `Lᵖ` as the positive real scale tends to zero.
The sequential approximate-identity theorem determines this limit because the scale filter
is countably generated. -/
theorem tendsto_eLpNorm_mollifyVector_sub
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    [CompleteSpace X]
    (μ : Mollifier n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ^n → X} (hf : MemLp f p volume) :
    Filter.Tendsto
      (fun ε ↦ eLpNorm (fun x ↦ mollifyVector μ ε f x - f x) p volume)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  apply Filter.tendsto_iff_seq_tendsto.2
  intro ε hε
  -- Repair the finite prefix outside the positive scales before using the sequence theorem.
  let η : ℕ → ℝ := fun m ↦ if 0 < ε m then ε m else 1
  have hηpos (m : ℕ) : 0 < η m := by
    dsimp [η]
    split_ifs with hm
    · exact hm
    · exact zero_lt_one
  have hηε : η =ᶠ[Filter.atTop] ε := by
    filter_upwards [hε.eventually self_mem_nhdsWithin] with m hm
    exact ite_eq_left hm
  have hη0 : Filter.Tendsto η Filter.atTop (𝓝 0) :=
    (hε.mono_right nhdsWithin_le_nhds).congr' hηε.symm
  apply (mollifyVector_converges_Lp μ p hp η hηpos hη0 hf).congr'
  filter_upwards [hηε] with m hm
  simp only [Function.comp_apply, hm]

/-- Scalar mollification converges in `Lᵖ` along all positive real scales tending to zero. -/
theorem tendsto_eLpNorm_mollify_sub
    (μ : Mollifier n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ^n → ℝ} (hf : MemLp f p volume) :
    Filter.Tendsto
      (fun ε ↦ eLpNorm (fun x ↦ mollify μ ε f x - f x) p volume)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  simpa [mollify, mollifyVector] using tendsto_eLpNorm_mollifyVector_sub μ hp hf

/-- Real-valued `L^p` convergence is the scalar specialization of the
Banach-valued approximate-identity theorem. -/
theorem mollify_converges_Lp (μ : Mollifier n) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) {f : ℝ^n → ℝ} :
    ∀ ε : ℕ → ℝ,
      (∀ m, 0 < ε m) →
      Filter.Tendsto ε Filter.atTop (𝓝 0) →
      MemLp f p volume →
      Filter.Tendsto
        (fun m ↦
          eLpNorm (fun x ↦ mollify μ (ε m) f x - f x) p
            volume)
        Filter.atTop (𝓝 0) := by
  intro ε hεpos hε0 hf
  simpa [mollify, mollifyVector] using
    (mollifyVector_converges_Lp (n := n) μ p hp ε hεpos hε0 hf)

/-- Mollifying the zero extension of an `Lᵖ(Ω)` function converges to the original function
on every measurable subset of `Ω`, as the positive real scale tends to zero. -/
theorem tendsto_eLpNorm_mollify_indicator_sub_on_subset
    (μ : Mollifier n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {Ω K : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {f : ℝ^n → ℝ} (hf : MemLp f p (volume.restrict Ω)) :
    Filter.Tendsto
      (fun ε ↦ eLpNorm (fun x ↦ mollify μ ε (Ω.indicator f) x - f x) p
        (volume.restrict K)) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have hfΩ : MemLp (Ω.indicator f) p volume :=
    (memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2 hf
  have hconv := tendsto_eLpNorm_mollify_sub μ hp hfΩ
  have heq : Ω.indicator f =ᵐ[volume.restrict K] f := by
    apply ae_restrict_of_forall_mem hK
    intro x hx
    exact Set.indicator_of_mem (hKΩ hx) f
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
  · exact fun _ ↦ bot_le
  · intro ε
    calc
      _ = eLpNorm (fun x ↦ mollify μ ε (Ω.indicator f) x - Ω.indicator f x) p
          (volume.restrict K) := by
            apply eLpNorm_congr_ae
            filter_upwards [heq] with x hx
            rw [hx]
      _ ≤ _ := eLpNorm_restrict_le _ _ _ _

/-- Mollifying the zero extension of an `Lᵖ(Ω)` function converges to the original
function on every measurable subset of `Ω`. -/
theorem mollify_indicator_converges_Lp_on_subset
    (μ : Mollifier n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {Ω K : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {f : ℝ^n → ℝ} (hf : MemLp f p (volume.restrict Ω))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m) (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ mollify μ (ε m) (Ω.indicator f) x - f x) p
        (volume.restrict K)) Filter.atTop (𝓝 0) :=
  (tendsto_eLpNorm_mollify_indicator_sub_on_subset μ hp hΩ hK hKΩ hf).comp
    (tendsto_nhdsWithin_iff.2 ⟨hε0, Filter.Eventually.of_forall hεpos⟩)

end Approximation

end SobolevSpace
