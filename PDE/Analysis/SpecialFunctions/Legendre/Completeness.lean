/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.Orthogonality
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Polynomial
import PDE.Analysis.Spectral.OrthogonalFamily
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Completeness of the Legendre functions in `L²((0, π), sin θ dθ)`

On the polar-angle interval `(0, π)` with the measure `sin θ dθ`, the Legendre functions
`P_l (cos θ)` and the associated functions `sin θ · P_l' (cos θ)`, `l ≥ 1`, are complete
orthogonal systems, with squared norms `2 / (2l + 1)` and `2 l (l + 1) / (2l + 1)`.

Completeness rests on one moment lemma. If `f` is integrable for `sin θ dθ` and
`∫ q (cos θ) f (θ) sin θ dθ = 0` for every polynomial `q`, then `f = 0` almost everywhere: the
Weierstrass theorem approximates `g ∘ arccos` uniformly on `[-1, 1]` by polynomials for every
continuous `g`, so `f` integrates every smooth compactly supported function to zero. Since the
Legendre polynomials span all polynomials, a function orthogonal to every `P_l (cos θ)` has
vanishing moments. For the associated family the same holds for `sin θ · f`, because the
derivatives `P_1', P_2', …` span all polynomials as well, and `sin θ > 0` on `(0, π)`.

The normalized families are Hilbert bases, so every element of the space is the sum of its
Legendre series.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open CAS.Analysis.SpecialFunctions
open MeasureTheory Polynomial Set PDE.Analysis.Spectral
open scoped ENNReal RealInnerProductSpace

/-- The measure `sin θ dθ` on the polar-angle interval `(0, π)`. -/
def polarAngleMeasure : Measure ℝ :=
  (volume.restrict (Ioo 0 Real.pi)).withDensity fun θ ↦ ENNReal.ofReal (Real.sin θ)

/-- The measure `sin θ dθ` on `(0, π)` is finite. -/
instance : IsFiniteMeasure polarAngleMeasure :=
  isFiniteMeasure_withDensity_ofReal
    (Real.continuous_sin.integrableOn_Icc.mono_set Ioo_subset_Icc_self).hasFiniteIntegral

/-- The total mass of `sin θ dθ` on `(0, π)` is `2`. -/
theorem polarAngleMeasure_univ : polarAngleMeasure univ = 2 := by
  have hint : ∫ θ in Ioo 0 Real.pi, Real.sin θ = 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le,
      integral_sin, Real.cos_zero, Real.cos_pi]
    norm_num
  rw [polarAngleMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (Real.continuous_sin.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      ((ae_restrict_mem measurableSet_Ioo).mono fun θ hθ ↦
        Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le),
    hint, ENNReal.ofReal_ofNat]

/-- Almost every polar angle lies in `(0, π)`. -/
theorem ae_mem_Ioo_polarAngleMeasure : ∀ᵐ θ ∂polarAngleMeasure, θ ∈ Ioo 0 Real.pi :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

/-- Integrals for `sin θ dθ` on `(0, π)` are interval integrals with the weight `sin θ`. -/
theorem integral_polarAngleMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ θ, f θ ∂polarAngleMeasure = ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ • f θ := by
  rw [polarAngleMeasure, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable fun θ : ℝ ↦ ENNReal.ofReal (Real.sin θ))
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
  simp only [ENNReal.toReal_ofReal (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le)]

/-- Real integrals for `sin θ dθ` on `(0, π)`. -/
theorem integral_polarAngleMeasure_eq (f : ℝ → ℝ) :
    ∫ θ, f θ ∂polarAngleMeasure = ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ := by
  rw [integral_polarAngleMeasure]
  simp only [smul_eq_mul, mul_comm]

/-- Integrals for `sin θ dθ` on `(0, π)` are invariant under the reflection `θ ↦ π - θ`. -/
theorem integral_polarAngleMeasure_comp_pi_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ θ, f (Real.pi - θ) ∂polarAngleMeasure = ∫ θ, f θ ∂polarAngleMeasure := by
  rw [integral_polarAngleMeasure, integral_polarAngleMeasure]
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi)
    (fun θ ↦ Real.sin (Real.pi - θ) • f (Real.pi - θ)) Real.pi
  simp only [sub_sub_cancel, Real.sin_pi_sub, sub_self, sub_zero] at h
  exact h.symm

/-- The measure of a measurable set `t` is the integral of `sin θ` over `(0, π) ∩ t`. -/
theorem polarAngleMeasure_apply {t : Set ℝ} (ht : MeasurableSet t) :
    polarAngleMeasure t =
      ∫⁻ θ, (Ioo 0 Real.pi ∩ t).indicator (fun θ ↦ ENNReal.ofReal (Real.sin θ)) θ := by
  rw [polarAngleMeasure, withDensity_apply _ ht, Measure.restrict_restrict ht, Set.inter_comm,
    lintegral_indicator (measurableSet_Ioo.inter ht)]

/-- The reflection `θ ↦ π - θ` preserves `sin θ dθ` on `(0, π)`. -/
theorem measurePreserving_pi_sub_polarAngleMeasure :
    MeasurePreserving (fun θ ↦ Real.pi - θ) polarAngleMeasure polarAngleMeasure := by
  have hvol : MeasurePreserving (fun θ : ℝ ↦ Real.pi - θ) volume volume :=
    volume.measurePreserving_sub_left Real.pi
  have hmeas : Measurable fun θ : ℝ ↦ Real.pi - θ := by fun_prop
  refine ⟨hmeas, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hmeas hs, polarAngleMeasure_apply (hmeas hs),
    polarAngleMeasure_apply hs, ← hvol.lintegral_comp
      ((by fun_prop : Measurable fun θ : ℝ ↦ ENNReal.ofReal (Real.sin θ)).indicator
        (measurableSet_Ioo.inter hs))]
  refine lintegral_congr fun θ ↦ ?_
  have hIoo : θ ∈ Ioo 0 Real.pi ↔ Real.pi - θ ∈ Ioo 0 Real.pi := by
    simp only [mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases h : θ ∈ Ioo 0 Real.pi ∩ (fun θ ↦ Real.pi - θ) ⁻¹' s
  · have h' : Real.pi - θ ∈ Ioo 0 Real.pi ∩ s := ⟨hIoo.mp h.1, h.2⟩
    rw [indicator_of_mem h, indicator_of_mem h', Real.sin_pi_sub]
  · have h' : Real.pi - θ ∉ Ioo 0 Real.pi ∩ s := fun h' ↦ h ⟨hIoo.mpr h'.1, h'.2⟩
    rw [indicator_of_notMem h, indicator_of_notMem h']

/-- A function continuous on `[0, π]` is essentially bounded for `sin θ dθ`. -/
theorem exists_ae_bound_polarAngleMeasure {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 Real.pi)) : ∃ C, ∀ᵐ θ ∂polarAngleMeasure, ‖f θ‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨C, ae_mem_Ioo_polarAngleMeasure.mono fun θ hθ ↦ hC θ (Ioo_subset_Icc_self hθ)⟩

/-- A continuous function lies in every `Lᵖ` space of `sin θ dθ` on `(0, π)`. -/
theorem memLp_polarAngleMeasure {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p polarAngleMeasure := by
  obtain ⟨C, hC⟩ := exists_ae_bound_polarAngleMeasure hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C hC

/-- The product of a continuous function and an integrable function is integrable for
`sin θ dθ` on `(0, π)`. -/
theorem integrable_polarAngleMeasure_mul {φ f : ℝ → ℝ} (hφ : Continuous φ)
    (hf : Integrable f polarAngleMeasure) :
    Integrable (fun θ ↦ φ θ * f θ) polarAngleMeasure := by
  obtain ⟨C, hC⟩ := exists_ae_bound_polarAngleMeasure hφ.continuousOn
  exact hf.bdd_mul hφ.aestronglyMeasurable hC

/-- The inner product in `L²((0, π), sin θ dθ)` of a function and an element. -/
theorem inner_toLp_polarAngleMeasure {g : ℝ → ℝ} (hg : MemLp g 2 polarAngleMeasure)
    (f : Lp ℝ 2 polarAngleMeasure) :
    ⟪hg.toLp g, f⟫ = ∫ θ, g θ * f θ ∂polarAngleMeasure := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with θ hθ
  rw [RCLike.inner_apply, conj_trivial, hθ, mul_comm]

/-- The moment lemma: an integrable function for `sin θ dθ` on `(0, π)` whose moments against
every polynomial in `cos θ` vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_integral_eval_cos_mul_eq_zero {f : ℝ → ℝ}
    (hf : Integrable f polarAngleMeasure)
    (h : ∀ q : ℝ[X], ∫ θ, q.eval (Real.cos θ) * f θ ∂polarAngleMeasure = 0) :
    f =ᵐ[polarAngleMeasure] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable fun g hg _ ↦ ?_
  simp only [smul_eq_mul]
  have hgc : Continuous g := hg.continuous
  have hbound (δ : ℝ) (hδ : 0 < δ) :
      |∫ θ, g θ * f θ ∂polarAngleMeasure| ≤ δ * ∫ θ, |f θ| ∂polarAngleMeasure := by
    obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (g ∘ Real.arccos)
      (hgc.comp Real.continuous_arccos).continuousOn δ hδ
    have hq' : ∀ᵐ θ ∂polarAngleMeasure, |g θ - q.eval (Real.cos θ)| ≤ δ := by
      filter_upwards [ae_mem_Ioo_polarAngleMeasure] with θ hθ
      have h₁ := hq (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
      rw [Function.comp_apply, Real.arccos_cos hθ.1.le hθ.2.le, abs_sub_comm] at h₁
      exact h₁.le
    have hgi := integrable_polarAngleMeasure_mul hgc hf
    have hqi : Integrable (fun θ ↦ q.eval (Real.cos θ) * f θ) polarAngleMeasure :=
      integrable_polarAngleMeasure_mul (q.continuous.comp Real.continuous_cos) hf
    calc |∫ θ, g θ * f θ ∂polarAngleMeasure|
        = |∫ θ, (g θ - q.eval (Real.cos θ)) * f θ ∂polarAngleMeasure| := by
          simp only [sub_mul]
          rw [integral_sub hgi hqi, h q, sub_zero]
      _ ≤ ∫ θ, δ * |f θ| ∂polarAngleMeasure := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le (hf.abs.const_mul δ) ?_
          filter_upwards [hq'] with θ hθ
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
      _ = δ * ∫ θ, |f θ| ∂polarAngleMeasure := integral_const_mul δ _
  have hA : 0 ≤ ∫ θ, |f θ| ∂polarAngleMeasure := integral_nonneg fun _ ↦ abs_nonneg _
  refine abs_nonpos_iff.mp (le_of_forall_pos_lt_add fun ε hε ↦ ?_)
  have hδ : 0 < ε / (∫ θ, |f θ| ∂polarAngleMeasure + 1) := by positivity
  calc |∫ θ, g θ * f θ ∂polarAngleMeasure|
      ≤ ε / (∫ θ, |f θ| ∂polarAngleMeasure + 1) * ∫ θ, |f θ| ∂polarAngleMeasure :=
        hbound _ hδ
    _ < 0 + ε := by
        rw [zero_add, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- A polynomial in `cos θ` lies in every `Lᵖ` space of `sin θ dθ` on `(0, π)`. -/
theorem memLp_eval_cos (q : ℝ[X]) (p : ℝ≥0∞) :
    MemLp (fun θ ↦ q.eval (Real.cos θ)) p polarAngleMeasure :=
  memLp_polarAngleMeasure (by fun_prop) p

/-- The product of `sin θ` and a polynomial in `cos θ` lies in every `Lᵖ` space of
`sin θ dθ` on `(0, π)`. -/
theorem memLp_sin_mul_eval_cos (q : ℝ[X]) (p : ℝ≥0∞) :
    MemLp (fun θ ↦ Real.sin θ * q.eval (Real.cos θ)) p polarAngleMeasure :=
  memLp_polarAngleMeasure (by fun_prop) p

/-- Polynomials in `cos θ` as elements of `L²((0, π), sin θ dθ)`. -/
def cosPolynomialLp : ℝ[X] →ₗ[ℝ] Lp ℝ 2 polarAngleMeasure where
  toFun q := (memLp_eval_cos q 2).toLp fun θ ↦ q.eval (Real.cos θ)
  map_add' q r := by
    rw [← MemLp.toLp_add]
    congr 1
    funext θ
    simp only [eval_add, Pi.add_apply]
  map_smul' c q := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1
    funext θ
    simp only [eval_smul, smul_eq_mul, Pi.smul_apply]

/-- The element `cosPolynomialLp q` is represented by `θ ↦ q (cos θ)`. -/
theorem coeFn_cosPolynomialLp (q : ℝ[X]) :
    cosPolynomialLp q =ᵐ[polarAngleMeasure] fun θ ↦ q.eval (Real.cos θ) :=
  (memLp_eval_cos q 2).coeFn_toLp

/-- The inner product of `q (cos θ)` with an element `f` is the moment
`∫ q (cos θ) f (θ) sin θ dθ`. -/
theorem inner_cosPolynomialLp (q : ℝ[X]) (f : Lp ℝ 2 polarAngleMeasure) :
    ⟪cosPolynomialLp q, f⟫ = ∫ θ, q.eval (Real.cos θ) * f θ ∂polarAngleMeasure :=
  inner_toLp_polarAngleMeasure (memLp_eval_cos q 2) f

/-- Polynomials in `cos θ`, multiplied by `sin θ`, as elements of `L²((0, π), sin θ dθ)`. -/
def sinCosPolynomialLp : ℝ[X] →ₗ[ℝ] Lp ℝ 2 polarAngleMeasure where
  toFun q := (memLp_sin_mul_eval_cos q 2).toLp fun θ ↦ Real.sin θ * q.eval (Real.cos θ)
  map_add' q r := by
    rw [← MemLp.toLp_add]
    congr 1
    funext θ
    simp only [eval_add, mul_add, Pi.add_apply]
  map_smul' c q := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1
    funext θ
    simp only [eval_smul, smul_eq_mul, Pi.smul_apply]
    ring

/-- The element `sinCosPolynomialLp q` is represented by `θ ↦ sin θ · q (cos θ)`. -/
theorem coeFn_sinCosPolynomialLp (q : ℝ[X]) :
    sinCosPolynomialLp q =ᵐ[polarAngleMeasure] fun θ ↦ Real.sin θ * q.eval (Real.cos θ) :=
  (memLp_sin_mul_eval_cos q 2).coeFn_toLp

/-- The inner product of `sin θ · q (cos θ)` with an element `f`. -/
theorem inner_sinCosPolynomialLp (q : ℝ[X]) (f : Lp ℝ 2 polarAngleMeasure) :
    ⟪sinCosPolynomialLp q, f⟫ =
      ∫ θ, Real.sin θ * q.eval (Real.cos θ) * f θ ∂polarAngleMeasure :=
  inner_toLp_polarAngleMeasure (memLp_sin_mul_eval_cos q 2) f

/-- The Legendre function `θ ↦ P_l (cos θ)` in `L²((0, π), sin θ dθ)`. -/
def legendreLp (l : ℕ) : Lp ℝ 2 polarAngleMeasure :=
  cosPolynomialLp (legendre l)

/-- The associated Legendre function `θ ↦ sin θ · P_l' (cos θ)` in `L²((0, π), sin θ dθ)`; it
vanishes for `l = 0`. -/
def associatedLegendreLp (l : ℕ) : Lp ℝ 2 polarAngleMeasure :=
  sinCosPolynomialLp (derivative (legendre l))

/-- Orthogonality of `P_l (cos θ)` for `sin θ dθ` on `(0, π)`, with squared norms
`2 / (2l + 1)`. -/
theorem integral_legendre_mul_legendre_polarAngleMeasure (l m : ℕ) :
    ∫ θ, (legendre l).eval (Real.cos θ) * (legendre m).eval (Real.cos θ) ∂polarAngleMeasure =
      if l = m then 2 / (2 * (l : ℝ) + 1) else 0 := by
  rw [← integral_legendre_mul_legendre, ← integral_comp_cos_mul_sin
      (g := fun x ↦ (legendre l).eval x * (legendre m).eval x) (by fun_prop),
    integral_polarAngleMeasure_eq]

/-- Orthogonality of `sin θ · P_l' (cos θ)` for `sin θ dθ` on `(0, π)`, with squared norms
`2 l (l + 1) / (2l + 1)`. -/
theorem integral_sin_mul_derivative_legendre_polarAngleMeasure (l m : ℕ) :
    ∫ θ, Real.sin θ * (derivative (legendre l)).eval (Real.cos θ) *
        (Real.sin θ * (derivative (legendre m)).eval (Real.cos θ)) ∂polarAngleMeasure =
      if l = m then 2 * (l : ℝ) * (l + 1) / (2 * l + 1) else 0 := by
  rw [← integral_one_sub_sq_mul_derivative_legendre_mul, ← integral_comp_cos_mul_sin
      (g := fun x ↦ (1 - x ^ 2) * (derivative (legendre l)).eval x *
        (derivative (legendre m)).eval x) (by fun_prop),
    integral_polarAngleMeasure_eq]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  rw [← Real.sin_sq_add_cos_sq θ]
  ring

/-- The Legendre functions are orthogonal with squared norms `2 / (2l + 1)`. -/
theorem inner_legendreLp (l m : ℕ) :
    ⟪legendreLp l, legendreLp m⟫ = if l = m then 2 / (2 * (l : ℝ) + 1) else 0 := by
  rw [← integral_legendre_mul_legendre_polarAngleMeasure, legendreLp, inner_cosPolynomialLp]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cosPolynomialLp (legendre m)] with θ hθ
  rw [legendreLp, hθ]

/-- The associated Legendre functions are orthogonal with squared norms
`2 l (l + 1) / (2l + 1)`. -/
theorem inner_associatedLegendreLp (l m : ℕ) :
    ⟪associatedLegendreLp l, associatedLegendreLp m⟫ =
      if l = m then 2 * (l : ℝ) * (l + 1) / (2 * l + 1) else 0 := by
  rw [← integral_sin_mul_derivative_legendre_polarAngleMeasure, associatedLegendreLp,
    inner_sinCosPolynomialLp]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_sinCosPolynomialLp (derivative (legendre m))] with θ hθ
  rw [associatedLegendreLp, hθ]

/-- Every polynomial in `cos θ` lies in the span of the Legendre functions. -/
theorem cosPolynomialLp_mem_span_legendreLp (q : ℝ[X]) :
    cosPolynomialLp q ∈ Submodule.span ℝ (range legendreLp) := by
  have hq : q ∈ Submodule.span ℝ (range legendre) := span_legendre ▸ Submodule.mem_top
  have h := Submodule.mem_map_of_mem (f := cosPolynomialLp) hq
  rwa [Submodule.map_span, ← range_comp] at h

/-- Every product of `sin θ` and a polynomial in `cos θ` lies in the span of the associated
Legendre functions of degree at least one. -/
theorem sinCosPolynomialLp_mem_span_associatedLegendreLp (q : ℝ[X]) :
    sinCosPolynomialLp q ∈ Submodule.span ℝ (range fun l ↦ associatedLegendreLp (l + 1)) := by
  have hq : q ∈ Submodule.span ℝ (range fun l ↦ derivative (legendre (l + 1))) :=
    span_derivative_legendre ▸ Submodule.mem_top
  have h := Submodule.mem_map_of_mem (f := sinCosPolynomialLp) hq
  rwa [Submodule.map_span, ← range_comp] at h

/-- **Completeness of the Legendre functions.** The functions `P_l (cos θ)` span a dense
subspace of `L²((0, π), sin θ dθ)`. -/
theorem legendre_complete :
    (Submodule.span ℝ (range legendreLp)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine ae_eq_zero_of_integral_eval_cos_mul_eq_zero ((Lp.memLp f).integrable one_le_two)
    fun q ↦ ?_
  rw [← inner_cosPolynomialLp]
  exact hf _ (cosPolynomialLp_mem_span_legendreLp q)

/-- **Completeness of the associated Legendre functions.** The functions
`sin θ · P_l' (cos θ)`, `l ≥ 1`, span a dense subspace of `L²((0, π), sin θ dθ)`. -/
theorem associatedLegendre_complete :
    (Submodule.span ℝ (range fun l ↦ associatedLegendreLp (l + 1))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hsf : (fun θ ↦ Real.sin θ * f θ) =ᵐ[polarAngleMeasure] 0 := by
    refine ae_eq_zero_of_integral_eval_cos_mul_eq_zero
      (integrable_polarAngleMeasure_mul Real.continuous_sin
        ((Lp.memLp f).integrable one_le_two)) fun q ↦ ?_
    have h := hf _ (sinCosPolynomialLp_mem_span_associatedLegendreLp q)
    rw [inner_sinCosPolynomialLp] at h
    rw [← h]
    congr 1
    funext θ
    ring
  filter_upwards [hsf, ae_mem_Ioo_polarAngleMeasure] with θ h₁ h₂
  exact (mul_eq_zero.mp h₁).resolve_left (Real.sin_pos_of_pos_of_lt_pi h₂.1 h₂.2).ne'

/-- Lebesgue measure on `(0, π)` is absolutely continuous with respect to `sin θ dθ`, so the two
measures have the same null sets. -/
theorem volume_restrict_Ioo_absolutelyContinuous :
    volume.restrict (Ioo 0 Real.pi) ≪ polarAngleMeasure :=
  withDensity_absolutelyContinuous'
    (by fun_prop : Measurable fun θ : ℝ ↦ ENNReal.ofReal (Real.sin θ)).aemeasurable
    ((ae_restrict_mem measurableSet_Ioo).mono fun θ hθ ↦
      ENNReal.ofReal_pos.mpr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) |>.ne')

/-- **Completeness of the Legendre functions**, pointwise form: a function that is square
integrable for `sin θ dθ` on `(0, π)` and orthogonal to every `P_l (cos θ)` vanishes almost
everywhere on `(0, π)`. -/
theorem ae_eq_zero_of_forall_integral_legendre_mul_eq_zero {f : ℝ → ℝ}
    (hf : MemLp f 2 polarAngleMeasure)
    (h : ∀ l, ∫ θ in (0 : ℝ)..Real.pi, (legendre l).eval (Real.cos θ) * f θ * Real.sin θ = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo 0 Real.pi), f θ = 0 := by
  have hzero : hf.toLp f = 0 := by
    refine eq_zero_of_forall_inner_eq_zero_of_dense legendre_complete fun l ↦ ?_
    rw [legendreLp, inner_cosPolynomialLp, ← h l, ← integral_polarAngleMeasure_eq]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  have hf0 : f =ᵐ[polarAngleMeasure] 0 :=
    hf.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  exact volume_restrict_Ioo_absolutelyContinuous.ae_le hf0

end PDE.Analysis.SpecialFunctions
