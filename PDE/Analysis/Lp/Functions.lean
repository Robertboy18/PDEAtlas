/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Separation.CompletelyRegular
public import PDE.Analysis.ENNReal.Basic
public import PDE.Analysis.LinearAlgebra.InnerProduct
public import PDE.Analysis.MeasureTheory.Integrability
public import PDE.Analysis.MeasureTheory.Lp.L2Pairing
public import PDE.Analysis.MeasureTheory.LpNorm
public import PDE.Analysis.MeasureTheory.Measurability

set_option linter.style.header false

/-!
# Functions in `L^p`

The lemmas state membership in `L^p` for products, sums and limits, bound `eLpNorm` by interpolation
or by a pointwise bound, and relate the norm of `Lp` to an integral. The proofs use Hölder's
inequality (`MemLp.mul`) and the lemmas of Mathlib on `eLpNorm`.

## Main results

* `PDE.Analysis.sq_eLpNorm_two`: For an almost everywhere strongly measurable `f : γ → F` with
  values in a normed group, the square of the `L²` seminorm is the lower integral of the squared
  extended norm: `eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ`.
* `PDE.Analysis.lintegral_enorm_sq_Lp`: For `f` in `Lp F 2 μ`, with `F` a normed group, the lower
  integral of the squared pointwise extended norm is the squared extended norm of `f`:
  `∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ = ‖f‖ₑ ^ 2`.
* `PDE.Analysis.memLp_two_of_bounded_Ioc_two_pi`: A function `w : ℝ → ℝ` that is almost everywhere
  strongly measurable for Lebesgue measure restricted to `Ioc 0 (2 * π)` and satisfies `|w θ| ≤ C`
  for all `θ` is in `L²` of this interval: `MemLp w 2 (volume.restrict (Ioc 0 (2 * π)))`.
* `PDE.Analysis.memLp_two_bounded_mul_Ioc_two_pi`: On `Ioc 0 (2 * π)` with Lebesgue measure: if
  `w : ℝ → ℝ` is almost everywhere strongly measurable with `|w θ| ≤ C` for all `θ`, and `g : ℝ → ℝ`
  satisfies `MemLp g 2`, then the product `θ ↦ w θ * g θ` satisfies `MemLp _ 2`.
* `PDE.Analysis.memLp_two_bounded_mul_haarAddCircle`: On the circle `AddCircle T` (`0 < T`) with its
  Haar probability measure, if `F : AddCircle T → ℂ` is almost everywhere strongly measurable and
  `‖F t‖ ≤ C` for all `t`, then for every `Y` in `Lp ℂ 2` the product `t ↦ F t * Y t` satisfies
  `MemLp _ 2`.
* `PDE.Analysis.ofReal_norm_sq_Lp_eq_lintegral_enorm`: For `f` in `Lp E 2 μ`, with `E` a normed
  group, the squared norm of `f` is the lower integral of the squared pointwise extended norm:
  `ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ`.
* `PDE.Analysis.eLpNorm_top_le_of_weak_limit`: An `L∞` bound passes to weak limits: let `E` be a
  real Hilbert space, `L : E →L[ℝ] Lp F 2 μ` a continuous linear map, and `u n` a sequence in `E`
  such that `inner ℝ (u n) y` tends to `inner ℝ u₀ y` for every `y`. If `eLpNorm (L (u n)) ⊤ μ ≤ C`
  for all `n`, then `eLpNorm (L u₀) ⊤ μ ≤ C`. The set of points of `E` with this bound is convex and
  closed, so it contains weak limits of its sequences.
* `PDE.Analysis.eventually_memLp_of_tendsto_eLpNorm_sub`: Let `f n : α → ℝ` be functions and let
  `f₀ : α → ℝ` satisfy `MemLp f₀ 2 μ`. If `eLpNorm (f n - f₀) 2 μ` tends to `0` as `n` tends to
  infinity, then `MemLp (f n) 2 μ` holds for all large `n`.

There are 26 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Real ComplexConjugate
open scoped ENNReal

namespace PDE.Analysis

/-- For every `C : ℝ≥0∞` and every real normed space `F`, the set of `g` in `Lp F 2 μ` with
`eLpNorm g ⊤ μ ≤ C` is convex. The proof uses the triangle inequality and the homogeneity of the
`L∞` seminorm. -/
theorem convex_setOf_eLpNorm_top_le {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F]
    [NormedSpace ℝ F] (C : ℝ≥0∞) : Convex ℝ {g : Lp F 2 μ | eLpNorm g ⊤ μ ≤ C} := by
  intro g hg h hh a b ha hb hab
  have hg' : eLpNorm g ⊤ μ ≤ C := hg
  have hh' : eLpNorm h ⊤ μ ≤ C := hh
  change eLpNorm (⇑(a • g + b • h)) ⊤ μ ≤ C
  rw [eLpNorm_congr_ae (Lp.coeFn_add _ _)]
  refine (eLpNorm_add_le le_top).trans ?_
  rw [eLpNorm_congr_ae (Lp.coeFn_smul a g), eLpNorm_congr_ae (Lp.coeFn_smul b h),
    eLpNorm_const_smul, eLpNorm_const_smul]
  calc ‖a‖ₑ * eLpNorm g ⊤ μ + ‖b‖ₑ * eLpNorm h ⊤ μ ≤ ‖a‖ₑ * C + ‖b‖ₑ * C := by gcongr
    _ = (‖a‖ₑ + ‖b‖ₑ) * C := by ring
    _ = C := by
      rw [Real.eNorm_of_nonneg ha, Real.eNorm_of_nonneg hb, ← ENNReal.ofReal_add ha hb, hab,
        ENNReal.ofReal_one, one_mul]

/-- For an almost everywhere strongly measurable `f : α → E` with values in a normed group, the `L²`
seminorm is the square root of the lower integral of the squared norm:
`eLpNorm f 2 μ = (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ)`. -/
theorem eLpNorm_two_eq_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : α → E) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  congr 1
  refine lintegral_congr fun a ↦ ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
  norm_num

/-- Let `f n : α → ℝ` be functions and let `f₀ : α → ℝ`
satisfy `MemLp f₀ 2 μ`. If `eLpNorm (f n - f₀) 2 μ` tends to `0` as `n` tends to infinity, then
`MemLp (f n) 2 μ` holds for all large `n`. -/
theorem eventually_memLp_of_tendsto_eLpNorm_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (f₀ : α → ℝ) (hf₀ : MemLp f₀ 2 μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, MemLp (f n) 2 μ := by
  filter_upwards [hfc.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with n hn
  have h : MemLp (f n - f₀ + f₀) 2 μ := MemLp.add (memLp_iff.2 hn) hf₀
  rwa [sub_add_cancel] at h

/-- For `0 < T` and `f g` in `Lp ℂ 2` of the circle `AddCircle T` with its Haar probability measure,
the inner product is the integral of `conj f * g`:
`inner ℂ f g = ∫ t, conj (f t) * g t ∂haarAddCircle`. -/
theorem inner_haarAddCircle_eq_integral_conj_mul {T : ℝ} [hT : Fact (0 < T)]
    (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    inner ℂ f g = ∫ t, conj (f t) * g t ∂AddCircle.haarAddCircle := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  simp only [RCLike.inner_apply]
  ring

/-- For a pointwise nonnegative, almost everywhere strongly measurable `φ : α → ℝ`, the lower
integral of `ENNReal.ofReal (φ x ^ 2)` is the square of the `L²` seminorm:
`∫⁻ x, ENNReal.ofReal (φ x ^ 2) ∂μ = eLpNorm φ 2 μ ^ 2`. The proof is
`eLpNorm_nnreal_pow_eq_lintegral` at `p = 2`, with `‖φ x‖ₑ ^ 2` rewritten as
`ENNReal.ofReal (φ x ^ 2)`. -/
theorem lintegral_ofReal_sq_eq_sq_eLpNorm_two {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (φ : α → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (hm : AEStronglyMeasurable φ μ) :
    ∫⁻ x, ENNReal.ofReal (φ x ^ 2) ∂μ = eLpNorm φ 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := φ) (p := 2) two_ne_zero hm
  have h2 : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2] at h
  have h3 : ((2 : NNReal) : ℝ≥0∞) = 2 := by norm_num
  rw [h3] at h
  rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num, h]
  refine lintegral_congr fun x ↦ ?_
  rw [Real.eNorm_of_nonneg (hφ x), ENNReal.ofReal_pow (hφ x), ← ENNReal.rpow_natCast]
  norm_num

/-- For a measure `μ` on `ℝ × ℝ` and `f : ℝ × ℝ → ℂ`, if `MemLp f ⊤ μ` then the complex conjugate
`p ↦ conj (f p)` satisfies `MemLp _ ⊤ μ`. -/
theorem memLp_top_conj {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ) : MemLp
    (fun p ↦ (starRingEnd ℂ) (f p)) ⊤ μ :=
  hf.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (ae_of_all _ fun p ↦ by simp)

/-- For a measure `μ` on `ℝ × ℝ`, a decidable proposition `P` and `f g : ℝ × ℝ → ℂ` with
`MemLp f ⊤ μ` and `MemLp g ⊤ μ`, the function `p ↦ if P then f p else g p` satisfies `MemLp _ ⊤ μ`.
The proposition `P` does not depend on the point `p`. -/
theorem memLp_top_ite {μ : Measure (ℝ × ℝ)} {P : Prop} [Decidable P] {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (fun p ↦ if P then f p else g p) ⊤ μ := by
  by_cases h : P
  · simpa [h] using hf
  · simpa [h] using hg

/-- For a measure `μ` on `ℝ × ℝ` and `f g : ℝ × ℝ → ℂ`, if `MemLp f ⊤ μ` and `MemLp g ⊤ μ` then
`MemLp (fun p ↦ f p * g p) ⊤ μ`. This is `MemLp.fun_mul` applied to two functions in `L∞`. -/
theorem memLp_top_mul {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ)
    (hg : MemLp g ⊤ μ) :
    MemLp (fun p ↦ f p * g p) ⊤ μ := hf.fun_mul hg

/-- For a measure `μ` on `ℝ × ℝ` and `f₀ f₁ f₂ : ℝ × ℝ → ℂ` with `MemLp f₀ ⊤ μ`, `MemLp f₁ ⊤ μ` and
`MemLp f₂ ⊤ μ`, every component of the vector `![f₀ p, f₁ p, f₂ p]` is in `L∞`: for each
`a : Fin 3`, `MemLp (fun p ↦ ![f₀ p, f₁ p, f₂ p] a) ⊤ μ`. -/
theorem memLp_top_vec3_apply {μ : Measure (ℝ × ℝ)} {f₀ f₁ f₂ : ℝ × ℝ → ℂ} (h₀ : MemLp f₀ ⊤ μ)
    (h₁ : MemLp f₁ ⊤ μ) (h₂ : MemLp f₂ ⊤ μ) (a : Fin 3) :
    MemLp (fun p ↦ (![f₀ p, f₁ p, f₂ p] : Fin 3 → ℂ) a) ⊤ μ := by
  fin_cases a
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂

/-- A continuous `h : ℝ → ℂ` is in `L²` of `Ioc (-π) π` for Lebesgue measure:
`MemLp h 2 (volume.restrict (Ioc (-π) π))`. The proof bounds `h` on the compact interval
`Icc (-π) π`. -/
theorem memLp_two_Ioc_pi_of_continuous (h : ℝ → ℂ) (hc : Continuous h) :
    MemLp h 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_bound_of_continuousOn
      hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx ↦ hC x (Ioc_subset_Icc_self hx)))

/-- A `2 * π`-periodic `f : ℝ → ℝ` that is in `L²` of `Ioo (-π) π` is in `L²` of `Ioc 0 (2 * π)`:
`MemLp f 2 (volume.restrict (Ioo (-π) π))` implies `MemLp f 2 (volume.restrict (Ioc 0 (2 * π)))`.
The proof moves the interval integrability of `f` and of `‖f‖ ^ 2` from the period `Ioc (-π) π` to
the period `Ioc 0 (2 * π)`. -/
theorem memLp_two_Ioc_two_pi_of_periodic {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π))
    (h : MemLp f 2 (volume.restrict (Ioo (-π) π))) : MemLp f 2 (volume.restrict (Ioc 0 (2 * π))) :=
        by
  have h' : MemLp f 2 (volume.restrict (Ioc (-π) π)) := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h
  have hi1 : IntegrableOn f (Ioc (-π) π) := h'.integrable (by norm_num)
  have hi2 : IntegrableOn (fun θ ↦ ‖f θ‖ ^ 2) (Ioc (-π) π) :=
      (memLp_two_iff_integrable_sq_norm h'.aestronglyMeasurable).1 h'
  have hle : -π ≤ -π + 2 * π := by linarith [pi_pos]
  have e : -π + 2 * π = π := by ring
  have j1 : IntervalIntegrable f volume (-π) (-π + 2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 (by rw [e]; exact hi1)
  have j2 : IntervalIntegrable (fun θ ↦ ‖f θ‖ ^ 2) volume (-π) (-π + 2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 (by rw [e]; exact hi2)
  have hper2 : Function.Periodic (fun θ ↦ ‖f θ‖ ^ 2) (2 * π) := fun θ ↦ by simp only [hper θ]
  have k1 := hper.intervalIntegrable two_pi_pos.ne' j1 0 (2 * π)
  have k2 := hper2.intervalIntegrable two_pi_pos.ne' j2 0 (2 * π)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le] at k1 k2
  exact (memLp_two_iff_integrable_sq_norm k1.aestronglyMeasurable).2 k2

/-- On `Ioc 0 (2 * π)` with Lebesgue measure: if `w : ℝ → ℝ` is almost everywhere strongly
measurable with `|w θ| ≤ C` for all `θ`, and `g : ℝ → ℝ` satisfies `MemLp g 2`, then the product
`θ ↦ w θ * g θ` satisfies `MemLp _ 2`. -/
theorem memLp_two_bounded_mul_Ioc_two_pi {w : ℝ → ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict (Set.Ioc 0 (2 * π))))
    {C : ℝ} (hC : ∀ θ, |w θ| ≤ C) {g : ℝ → ℝ} (hg : MemLp g 2
        (volume.restrict (Set.Ioc 0 (2 * π)))) :
    MemLp (fun θ ↦ w θ * g θ) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  refine (hg.const_mul C).of_le (hw.mul hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun θ ↦ ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hC θ).trans (le_abs_self C)) (abs_nonneg _)

/-- On the circle `AddCircle T` (`0 < T`) with its Haar probability measure, if
`F : AddCircle T → ℂ` is almost everywhere strongly measurable and `‖F t‖ ≤ C` for all `t`, then for
every `Y` in `Lp ℂ 2` the product `t ↦ F t * Y t` satisfies `MemLp _ 2`. -/
theorem memLp_two_bounded_mul_haarAddCircle {T : ℝ} [hT : Fact (0 < T)] (F : AddCircle T → ℂ)
    (hF : AEStronglyMeasurable F AddCircle.haarAddCircle)
    (C : ℝ) (hC : ∀ t, ‖F t‖ ≤ C) (Y : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    MemLp (fun t ↦ F t * Y t) 2 AddCircle.haarAddCircle :=
  (Lp.memLp Y).of_le_mul (hF.mul (Lp.memLp Y).aestronglyMeasurable) (ae_of_all _ fun t ↦ by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _))

/-- Let `μ` be a measure on `ℝ`, let `Y : ℝ → E` take values in a normed group with `MemLp Y 2 μ`,
and let `φ : ℝ → E → ℂ` be jointly continuous with `‖φ θ e‖ ≤ ‖e‖` for all `θ` and `e`. Then
`θ ↦ φ θ (Y θ)` satisfies `MemLp _ 2 μ`. -/
theorem memLp_two_comp_of_norm_le {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ} {Y : ℝ → E}
    (hY : MemLp Y 2 μ)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun w : ℝ × E ↦ φ w.1 w.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    MemLp (fun θ ↦ φ θ (Y θ)) 2 μ :=
  hY.of_le (hφc.comp_aestronglyMeasurable (measurable_id.aestronglyMeasurable.prodMk
      hY.aestronglyMeasurable))
    (ae_of_all _ fun θ ↦ hφb θ (Y θ))

/-- A function `w : ℝ → ℝ` that is almost everywhere strongly measurable for Lebesgue measure
restricted to `Ioc 0 (2 * π)` and satisfies `|w θ| ≤ C` for all `θ` is in `L²` of this interval:
`MemLp w 2 (volume.restrict (Ioc 0 (2 * π)))`. -/
theorem memLp_two_of_bounded_Ioc_two_pi {w : ℝ → ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict (Set.Ioc 0 (2 * π))))
    {C : ℝ} (hC : ∀ θ, |w θ| ≤ C) : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact MemLp.of_bound hw C (Filter.Eventually.of_forall fun θ ↦ by
    simpa [Real.norm_eq_abs] using hC θ)

/-- If `a` in `Lp E 2 μ` and `b` in `Lp F 2 μ` have the same pointwise norm almost everywhere,
`‖a t‖ = ‖b t‖`, then they have the same `L²` norm: `‖a‖ = ‖b‖`. The normed groups `E` and `F` may
be different. -/
theorem norm_Lp_eq_of_ae_norm_eq {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (a : Lp E 2 μ) (b : Lp F 2 μ)
    (h : ∀ᵐ t ∂μ, ‖(a : α → E) t‖ = ‖(b : α → F) t‖) : ‖a‖ = ‖b‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable a) (Lp.aestronglyMeasurable b) h]

/-- On a probability space the `L²` norm is at most the `L∞` norm: for a continuous linear map
`A : E →L[ℝ] F` between real normed spaces and `u` in `Lp E 2 μ` with
`eLpNorm (fun a ↦ A (u a)) ⊤ μ < ⊤`, `‖A.compLpL 2 μ u‖ ≤ (eLpNorm (fun a ↦ A (u a)) ⊤ μ).toReal`.
-/
theorem norm_compLpL_le_toReal_eLpNorm_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (u : Lp E 2 μ) (h : eLpNorm (fun a ↦ A (u a)) ⊤ μ < ⊤) :
    ‖A.compLpL 2 μ u‖ ≤ (eLpNorm (fun a ↦ A (u a)) ⊤ μ).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousLinearMap.coeFn_compLpL A u)]
  exact ENNReal.toReal_mono h.ne (eLpNorm_le_eLpNorm_of_exponent_le le_top)

/-- For `F` in `Lp E 2 μ`, with `E` a real inner product space, the norm of `F` is the square root
of the integral of the squared pointwise norm, written with real powers:
`(∫ t, ‖F t‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖F‖`. -/
theorem rpow_integral_norm_rpow_two_Lp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (F : Lp E 2 μ) :
    (∫ t, ‖F t‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = ‖F‖ := by
  simp_rw [Real.rpow_two]
  rw [MeasureTheory.L2.integral_norm_sq_eq_norm_sq, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (norm_nonneg _)]

/-- Dominated convergence in `L²`: let `u n` and `v` be in `Lp E 2 μ` and let `b : α → ℝ` be
integrable. If `u n x` tends to `v x` for almost every `x` and, for every `n`,
`‖u n x - v x‖ ^ 2 ≤ b x` for almost every `x`, then `u n` tends to `v` in `Lp E 2 μ`. The proof
writes `‖u n - v‖` as the square root of `∫ x, ‖u n x - v x‖ ^ 2 ∂μ` and applies the dominated
convergence theorem to this integral. -/
theorem tendsto_Lp_two_of_dominated {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ) (b : α → ℝ) (hbi : Integrable b μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖(u n : α → E) x - (v : α → E) x‖ ^ 2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ (u n : α → E) x) atTop (𝓝 ((v : α → E) x))) :
    Tendsto u atTop (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖u n - v‖ =
      (∫ x, ‖((u n - v : Lp E 2 μ) : α → E) x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    intro n
    rw [Lp.norm_def, (Lp.memLp (u n - v)).eLpNorm_eq_integral_rpow_norm two_ne_zero
      ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal]
    exact Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _
  have hs : ∀ᵐ x ∂μ, ∀ n, ((u n - v : Lp E 2 μ) : α → E) x = (u n : α → E) x - (v : α → E) x :=
    ae_all_iff.2 fun n ↦ Lp.coeFn_sub (u n) v
  have hint : Tendsto (fun n ↦ ∫ x, ‖((u n - v : Lp E 2 μ) : α → E) x‖ ^ (2 : ℝ) ∂μ) atTop
      (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence b (fun n ↦ ?_) hbi (fun n ↦ ?_) ?_
    · exact ((Lp.aestronglyMeasurable (u n - v)).norm.aemeasurable.pow_const
          (2 : ℝ)).aestronglyMeasurable
    · filter_upwards [hb n, hs] with x hx hsx
      rw [hsx n, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_two]
      exact hx
    · filter_upwards [hs, hlim] with x hsx hl
      have h1 : Tendsto (fun n ↦ (u n : α → E) x - (v : α → E) x) atTop (𝓝 0) := by
        have := hl.sub_const ((v : α → E) x)
        rwa [sub_self] at this
      have h2 := (tendsto_norm_zero.comp h1).rpow_const (p := (2 : ℝ)) (Or.inr (by norm_num))
      rw [Real.zero_rpow two_ne_zero] at h2
      refine h2.congr fun n ↦ ?_
      simp only [Function.comp_apply, hsx n]
  rw [integral_zero] at hint
  have h3 := hint.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h3
  exact h3.congr fun n ↦ (hnorm n).symm

/-- Let `f n, f₀ : α → ℝ` with `hf₀ : MemLp f₀ 2 μ`, and let `F n` in `Lp ℝ 2 μ` be the class of
`f n` whenever `MemLp (f n) 2 μ` holds. If `MemLp (f n) 2 μ` holds for all large `n` and
`eLpNorm (f n - f₀) 2 μ` tends to `0`, then `F n` tends to `hf₀.toLp f₀` in `Lp ℝ 2 μ`. -/
theorem tendsto_toLp_of_tendsto_eLpNorm_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (f₀ : α → ℝ) (hf₀ : MemLp f₀ 2 μ) (F : ℕ → Lp ℝ 2 μ)
    (hF : ∀ n (h : MemLp (f n) 2 μ), F n = h.toLp (f n)) (hm : ∀ᶠ n in atTop, MemLp (f n) 2 μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 (hf₀.toLp f₀)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm F f₀ hf₀]
  refine hfc.congr' ?_
  filter_upwards [hm] with n hn
  rw [hF n hn]
  exact eLpNorm_congr_ae (hn.coeFn_toLp.sub EventuallyEq.rfl).symm

/-- On `Ioc 0 (2 * π)` with Lebesgue measure: if `g : ℝ → ℝ` satisfies `MemLp g 2`, and `w : ℝ → ℝ`
is almost everywhere strongly measurable with `|w θ| ≤ C` for all `θ`, then the product
`θ ↦ g θ * w θ`, with the bounded factor on the right, satisfies `MemLp _ 2`. -/
theorem memLp_two_mul_bounded_Ioc_two_pi {w g : ℝ → ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict (Set.Ioc 0 (2 * π))))
    {C : ℝ} (hC : ∀ θ, |w θ| ≤ C) (hg : MemLp g 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    MemLp (fun θ ↦ g θ * w θ) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have e : (fun θ ↦ g θ * w θ) = fun θ ↦ w θ * g θ := funext fun θ ↦ mul_comm _ _
  rw [e]
  exact memLp_two_bounded_mul_Ioc_two_pi hw hC hg

/-- An almost everywhere strongly measurable `f : α → E`, with values in a normed group, such that
`∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ < ⊤` satisfies `MemLp f 2 μ`. -/
theorem memLp_two_of_lintegral_lt_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ < ⊤) : MemLp f 2 μ :=
  memLp_iff.2 (by
    rw [eLpNorm_two_eq_lintegral f hf]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne)

/-- Let `f n` and `f₀` be almost everywhere strongly measurable functions `α → E` with values in a
normed group. If `∫⁻ a, ENNReal.ofReal (‖f n a - f₀ a‖ ^ 2) ∂μ` tends to `0` as `n` tends to
infinity, then `eLpNorm (f n - f₀) 2 μ` tends to `0`. -/
theorem tendsto_eLpNorm_sub_of_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : ℕ → α → E) (f₀ : α → E)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hf₀ : AEStronglyMeasurable f₀ μ)
    (h : Tendsto (fun n ↦ ∫⁻ a, ENNReal.ofReal (‖f n a - f₀ a‖ ^ 2) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0) := by
  have h1 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
  exact h1.congr fun n ↦ (eLpNorm_two_eq_lintegral (f n - f₀) ((hf n).sub hf₀)).symm

/-- For every `C : ℝ≥0∞`, the set of `g` in `L²(μ)`, with values in a real normed space, with
`eLpNorm g ⊤ μ ≤ C` (essential supremum norm at most `C`) is closed in `L²(μ)`. A convergent
sequence has a subsequence that converges almost everywhere, and the essential supremum norm of
the limit is at most the lower limit of the norms. -/
theorem isClosed_setOf_eLpNorm_top_le {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F]
    [NormedSpace ℝ F] (C : ℝ≥0∞) : IsClosed {g : Lp F 2 μ | eLpNorm g ⊤ μ ≤ C} := by
  refine IsSeqClosed.isClosed fun g g₀ hg hlim ↦ ?_
  have h1 : Tendsto (fun n ↦ eLpNorm (⇑(g n) - ⇑g₀) 2 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' g g₀).1 hlim
  have h2 : TendstoInMeasure μ (fun n ↦ ⇑(g n)) atTop ⇑g₀ :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero h1
  obtain ⟨ns, -, hns⟩ := h2.exists_seq_tendsto_ae
  have h3 := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ⊤)
    (fun i ↦ Lp.aestronglyMeasurable (g (ns i))) (⇑g₀) (Lp.aestronglyMeasurable g₀) hns
  change eLpNorm (⇑g₀) ⊤ μ ≤ C
  exact h3.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun i ↦ hg (ns i)))

/-- An `L∞` bound passes to weak limits: let `E` be a real Hilbert space, `L : E →L[ℝ] Lp F 2 μ` a
continuous linear map, and `u n` a sequence in `E` such that `inner ℝ (u n) y` tends to
`inner ℝ u₀ y` for every `y`. If `eLpNorm (L (u n)) ⊤ μ ≤ C` for all `n`, then
`eLpNorm (L u₀) ⊤ μ ≤ C`. The set of points of `E` with this bound is convex and closed, so it
contains weak limits of its sequences. -/
theorem eLpNorm_top_le_of_weak_limit {α F E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (L : E →L[ℝ] Lp F 2 μ) (C : ℝ≥0∞) (u : ℕ → E) (u₀ : E)
    (hw : ∀ y, Tendsto (fun n ↦ inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (hu : ∀ n, eLpNorm (L (u n)) ⊤ μ ≤ C) : eLpNorm (L u₀) ⊤ μ ≤ C :=
  mem_of_weak_limit (L ⁻¹' {g : Lp F 2 μ | eLpNorm g ⊤ μ ≤ C})
    ((convex_setOf_eLpNorm_top_le C).linear_preimage L.toLinearMap)
        ((isClosed_setOf_eLpNorm_top_le C).preimage L.continuous)
    u hu u₀ hw

/-- For three continuous linear maps `A j : E →L[ℝ] F` (`j : Fin 3`) between real inner product
spaces and `u` in `Lp E 2 μ`, `∫ t, ∑ j, ‖A j (u t)‖ ^ 2 ∂μ = ∑ j, ‖(A j).compLpL 2 μ u‖ ^ 2`. The
proof exchanges the integral with the finite sum and writes each squared `L²` norm as the integral
of the squared pointwise norm. -/
theorem integral_sum_norm_sq_compLpL_fin_three {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : Fin 3 → E →L[ℝ] F) (u : Lp E 2 μ) :
    ∫ t, ∑ j : Fin 3, ‖A j (u t)‖ ^ 2 ∂μ = ∑ j : Fin 3, ‖(A j).compLpL 2 μ u‖ ^ 2 := by
  have hi : ∀ j, (fun t ↦ ‖A j (u t)‖ ^ 2) =ᵐ[μ] (fun t ↦ ‖(A j).compLpL 2 μ u t‖ ^ 2) :=
    fun j ↦ (ContinuousLinearMap.coeFn_compLpL (A j) u).mono fun t ht ↦ by dsimp only; rw [ht]
  rw [integral_finsetSum _ fun j _ ↦ (integrable_norm_sq_Lp_two _).congr (hi j).symm]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
    exact integral_congr_ae (hi j)

/-- For an almost everywhere strongly measurable `f : γ → F` with values in a normed group, the
square of the `L²` seminorm is the lower integral of the squared extended norm:
`eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ`. -/
theorem sq_eLpNorm_two {F : Type*} [NormedAddCommGroup F] {γ : Type*} [MeasurableSpace γ]
    (f : γ → F) (μ : Measure γ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- Strong convergence of uniformly bounded operators passes to `L²`: let `E` be a real inner
product space, `A a : E →L[ℝ] E` for real `a`, `B : E →L[ℝ] E`, and `l` a countably generated filter
on `ℝ`. If `A a y` tends to `B y` along `l` for every `y` and `‖A a‖ ≤ C` eventually along `l`, then
for every `h` in `Lp E 2 μ`, `compLpL 2 μ (A a) h` tends to `compLpL 2 μ B h` along `l`. The proof
applies dominated convergence to `∫ t, ‖A a (h t) - B (h t)‖ ^ 2 ∂μ` with the bound
`(C + ‖B‖) ^ 2 * ‖h t‖ ^ 2`. -/
theorem tendsto_compLpL_of_tendsto_of_norm_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {l : Filter ℝ} [l.IsCountablyGenerated] {A : ℝ → E →L[ℝ] E}
    {B : E →L[ℝ] E} {C : ℝ} (hA : ∀ y, Tendsto (fun a ↦ A a y) l (𝓝 (B y)))
    (hC : ∀ᶠ a in l, ‖A a‖ ≤ C) (h : Lp E 2 μ) :
    Tendsto (fun a ↦ ContinuousLinearMap.compLpL 2 μ (A a) h) l
      (𝓝 (ContinuousLinearMap.compLpL 2 μ B h)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ a, ‖ContinuousLinearMap.compLpL 2 μ (A a) h -
      ContinuousLinearMap.compLpL 2 μ B h‖ ^ 2 =
      ∫ t, ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 ∂μ := by
    intro a
    refine (MeasureTheory.Lp.norm_sq_eq_integral_norm_sq _).trans (integral_congr_ae ?_)
    filter_upwards [Lp.coeFn_sub (ContinuousLinearMap.compLpL 2 μ (A a) h)
        (ContinuousLinearMap.compLpL 2 μ B h),
      (A a).coeFn_compLpL h, B.coeFn_compLpL h] with t hs ha hb
    exact congrArg (fun v : E ↦ ‖v‖ ^ 2) (hs.trans (congrArg₂ (· - ·) ha hb))
  have hint : Integrable (fun t ↦ ‖(h : α → E) t‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable h)).1 (Lp.memLp h)
  have hlim : Tendsto (fun a ↦ ∫ t, ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 ∂μ)
      l (𝓝 (∫ _t, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ (C + ‖B‖) ^ 2 * ‖(h : α → E) t‖ ^ 2) ?_ ?_ (hint.const_mul _) ?_
    · exact Eventually.of_forall fun a ↦
        ((((A a).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h)).sub
          (B.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h))).norm.pow 2)
    · filter_upwards [hC] with a ha
      refine Eventually.of_forall fun t ↦ ?_
      have hle : ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ≤
          (C + ‖B‖) * ‖(h : α → E) t‖ := by
        calc _ ≤ ‖A a ((h : α → E) t)‖ + ‖B ((h : α → E) t)‖ := norm_sub_le _ _
          _ ≤ C * ‖(h : α → E) t‖ + ‖B‖ * ‖(h : α → E) t‖ :=
              add_le_add ((A a).le_of_opNorm_le ha _) (B.le_opNorm _)
          _ = (C + ‖B‖) * ‖(h : α → E) t‖ := by ring
      have hsq : ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 ≤
          ((C + ‖B‖) * ‖(h : α → E) t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      calc ‖‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2‖ =
            ‖A a ((h : α → E) t) - B ((h : α → E) t)‖ ^ 2 := by
              simp only [norm_pow, norm_norm]
        _ ≤ ((C + ‖B‖) * ‖(h : α → E) t‖) ^ 2 := hsq
        _ = (C + ‖B‖) ^ 2 * ‖(h : α → E) t‖ ^ 2 := mul_pow _ _ _
    · refine Eventually.of_forall fun t ↦ ?_
      have := ((tendsto_iff_norm_sub_tendsto_zero.1 (hA ((h : α → E) t))).pow 2)
      have e0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [e0] at this
      exact this
  rw [integral_zero] at hlim
  have h2 := Tendsto.congr (fun a ↦ (heq a).symm) hlim
  have h3 := Tendsto.congr (fun a ↦ Real.sqrt_sq (norm_nonneg _)) h2.sqrt
  rw [Real.sqrt_zero] at h3
  exact h3

/-- Let `μ`, `ν` be s-finite measures on `α`, `β`, with `ν` separable, and let `F` be a second
countable normed group. If `g : α × β → F` is almost everywhere strongly measurable for `μ.prod ν`
and `∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ ≠ ⊤`, then there is `c` in `Lp (Lp F 2 ν) 2 μ` with
`c a =ᵐ[ν] fun y ↦ g (a, y)` for almost every `a` and
`‖c‖ ^ 2 = (∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ).toReal`. The proof takes the slices of a strongly
measurable version of `g`, which are in `L²` for almost every `a`, and checks the measurability of
the resulting map into `Lp F 2 ν` through its distances to a dense sequence. -/
theorem exists_Lp_Lp_of_lintegral_ne_top {α : Type*} {β : Type*} {F : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup F] [SecondCountableTopology F] {μ : Measure α}
    {ν : Measure β} [SFinite μ]
    [SFinite ν] [IsSeparable ν] {g : α × β → F} (hg : AEStronglyMeasurable g (μ.prod ν))
    (hfin : ∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ ≠ ⊤) :
    ∃ c : Lp (Lp F 2 ν) 2 μ, (∀ᵐ a ∂μ, (c a : β → F) =ᵐ[ν] fun y ↦ g (a, y)) ∧
      ‖c‖ ^ 2 = (∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ).toReal := by
  classical
  set g' := hg.mk g
  have hg'm : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have hslice : ∀ a, StronglyMeasurable fun y ↦ g' (a, y) := fun a ↦
    hg'm.comp_measurable measurable_prodMk_left
  have hgg : ∀ᵐ a ∂μ, ∀ᵐ y ∂ν, g' (a, y) = g (a, y) :=
    Measure.ae_ae_of_ae_prod (hg.ae_eq_mk.mono fun z hz ↦ hz.symm)
  let I : α → ℝ≥0∞ := fun a ↦ ∫⁻ y, ‖g' (a, y)‖ₑ ^ 2 ∂ν
  have hIm : Measurable I := (hg'm.eNorm.pow_const 2).lintegral_prod_right'
  have hII : ∫⁻ a, I a ∂μ = ∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ :=
    lintegral_congr_ae (hgg.mono fun a ha ↦ lintegral_congr_ae (ha.mono fun y hy ↦ by
      simp only [hy]))
  have hIfin : ∀ᵐ a ∂μ, I a < ⊤ := ae_lt_top hIm (hII ▸ hfin)
  have hsq : ∀ a, eLpNorm (fun y ↦ g' (a, y)) 2 ν ^ 2 = I a := fun a ↦
    sq_eLpNorm_two _ _ (hslice a).aestronglyMeasurable
  have hmem : ∀ a, I a < ⊤ → MemLp (fun y ↦ g' (a, y)) 2 ν := by
    intro a ha
    refine memLp_iff.2 (lt_top_iff_ne_top.2 fun htop ↦ ?_)
    rw [← hsq a, htop] at ha
    simp at ha
  let u : α → Lp F 2 ν := fun a ↦ if h : I a < ⊤ then (hmem a h).toLp _ else 0
  borelize (↥(Lp F 2 ν))
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp F 2 ν) := Lp.SecondCountableTopology
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq (Lp F 2 ν)
  have hum : Measurable u := by
    refine measurable_of_dist_dense hD fun k ↦ ?_
    have he : (fun a ↦ dist (u a) (D k)) = fun a ↦ if I a < ⊤ then
        (eLpNorm (fun y ↦ g' (a, y) - (D k : β → F) y) 2 ν).toReal else dist 0 (D k) := by
      funext a
      by_cases ha : I a < ⊤
      · simp only [u, dite_eq_left ha, ite_eq_left ha]
        rw [Lp.dist_def]
        congr 1
        exact eLpNorm_congr_ae ((hmem a ha).coeFn_toLp.sub EventuallyEq.rfl)
      · simp only [u, dite_eq_right ha, ite_eq_right ha]
    rw [he]
    refine Measurable.ite (measurableSet_lt hIm measurable_const) ?_ measurable_const
    have hH : StronglyMeasurable fun z : α × β ↦ g' z - (D k : β → F) z.2 :=
      hg'm.sub ((Lp.stronglyMeasurable (D k)).comp_measurable measurable_snd)
    exact (measurable_eLpNorm_two_slice (ν := ν) hH).ennreal_toReal
  have hnorm : ∀ᵐ a ∂μ, ‖u a‖ₑ ^ 2 = I a := by
    filter_upwards [hIfin] with a ha
    simp only [u, dite_eq_left ha]
    rw [Lp.eNorm_def, eLpNorm_congr_ae (hmem a ha).coeFn_toLp, hsq]
  have hu2 : eLpNorm u 2 μ ^ 2 = ∫⁻ a, ∫⁻ y, ‖g (a, y)‖ₑ ^ 2 ∂ν ∂μ := by
    rw [sq_eLpNorm_two _ _ hum.aestronglyMeasurable, lintegral_congr_ae hnorm, hII]
  have humem : MemLp u 2 μ := by
    refine memLp_iff.2 (lt_top_iff_ne_top.2 fun htop ↦ hfin ?_)
    rw [← hu2, htop]
    simp
  refine ⟨humem.toLp u, ?_, ?_⟩
  · filter_upwards [humem.coeFn_toLp, hIfin, hgg] with a h1 h2 h3
    rw [h1]
    simp only [u, dite_eq_left h2]
    exact (hmem a h2).coeFn_toLp.trans h3
  · rw [Lp.norm_toLp, ← ENNReal.toReal_pow, hu2]

/-- For `f` in `Lp F 2 μ`, with `F` a normed group, the lower integral of the squared pointwise
extended norm is the squared extended norm of `f`: `∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ = ‖f‖ₑ ^ 2`. -/
theorem lintegral_enorm_sq_Lp {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : Type*}
    [NormedAddCommGroup F] (f : Lp F 2 μ) : ∫⁻ y, ‖(f : α → F) y‖ₑ ^ 2 ∂μ = ‖f‖ₑ ^ 2 := by
  rw [Lp.eNorm_def, sq_eLpNorm_two _ _ (Lp.aestronglyMeasurable f)]

/-- For `f` in `Lp E 2 μ`, with `E` a normed group, the squared norm of `f` is the lower integral of
the squared pointwise extended norm: `ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ`. -/
theorem ofReal_norm_sq_Lp_eq_lintegral_enorm {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E]
    (f : Lp E 2 μ) : ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ a, ‖(f : α → E) a‖ₑ ^ 2 ∂μ := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    sq_eLpNorm_two _ _ (Lp.aestronglyMeasurable f)]

/-- For `f : α → E`, with `E` a normed group, and `hf : MemLp f 2 μ`, the squared norm of the class
`hf.toLp f` is the lower integral of the squared pointwise norm of `f`:
`ENNReal.ofReal (‖hf.toLp f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ`. -/
theorem ofReal_norm_toLp_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (hf : MemLp f 2 μ) :
    ENNReal.ofReal (‖hf.toLp f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [Lp.norm_toLp, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top hf.eLpNorm_ne_top),
    sq_eLpNorm_two _ _ hf.aestronglyMeasurable]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- For `f g` in `Lp F 2 μ` and functions `a b : α → F` that agree almost everywhere with `f` and
`g`, the lower integral of the squared pointwise distance of `a` and `b` is the squared `L²`
distance of `f` and `g`: `∫⁻ t, ENNReal.ofReal (‖a t - b t‖ ^ 2) ∂μ = ENNReal.ofReal (‖f - g‖ ^ 2)`.
-/
theorem lintegral_sq_norm_sub_of_ae_eq {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F]
    (f g : Lp F 2 μ) (a b : α → F) (ha : (f : α → F) =ᵐ[μ] a) (hb : (g : α → F) =ᵐ[μ] b) :
    ∫⁻ t, ENNReal.ofReal (‖a t - b t‖ ^ 2) ∂μ = ENNReal.ofReal (‖f - g‖ ^ 2) := by
  rw [ofReal_norm_sq_Lp_eq_lintegral_enorm (f - g)]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g, ha, hb] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  exact ofReal_norm_sq_eq_eNorm_sq _

/-- For `g` in `L²(μ)` with values in a normed group `E`,
`∫⁻ a, ENNReal.ofReal (‖g a‖ ^ 2) ∂μ = ENNReal.ofReal (‖g‖ ^ 2)`. This is
`MeasureTheory.Lp.lintegral_nnnorm_sq_eq_norm_sq_of_ae_eq` of this library for the representative
`g` itself, with the integrand written `ENNReal.ofReal (‖g a‖ ^ 2)` in place of `‖g a‖₊ ^ 2`. -/
theorem lintegral_ofReal_norm_sq_Lp {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E]
    (g : Lp E 2 μ) :
    ∫⁻ a, ENNReal.ofReal (‖(g : α → E) a‖ ^ 2) ∂μ = ENNReal.ofReal (‖g‖ ^ 2) := by
  simpa [ENNReal.ofReal_pow, ofReal_norm, eNorm_eq_nnNorm] using
    Lp.lintegral_nnnorm_sq_eq_norm_sq_of_ae_eq g (ae_eq_refl _)

end PDE.Analysis
