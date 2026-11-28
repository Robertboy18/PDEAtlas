/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.ConvexLowerSemicontinuity
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.DirectMethod
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Sobolev
import PDE.Analysis.WeakSequentialBoundedness
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Minimization of coupled extended energies in affine Sobolev classes

Finite products of the zero-boundary graph spaces are reflexive and
separable. Matrix coercivity bounds their finite affine energy sublevels.
The all-infinite case is included by the extended direct method.

The density is measurable in the point, continuous in the value and convex in the gradient
matrix; it need not be differentiable. The set is bounded and measurable, with no assumption on
its boundary: along fields `g + w_j` with weakly convergent zero-boundary corrections `w_j` the
values converge strongly in `Lᵖ`
(`RellichKondrachov.tendsto_vectorWkpValueCLM_add_vectorWkp0SubtypeL`) and the gradients
weakly, and `lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient`, along
subsequences that converge almost everywhere, gives the lower semicontinuity that
`exists_minimizer_vectorWkpLIntegral_prescribed_boundary_of_zeroBoundary_weak_lsc` needs.

The earlier form of this module cited the existence theorem of Evans, §8.2.4(a), Theorem 5,
for coupled systems. The statement here is for the affine class of a Sobolev boundary datum,
with a density that is not assumed smooth and a set whose boundary is not assumed regular. The
book was not opened for this form.

## Main results

All are for every number of components, every positive dimension, every bounded measurable set,
every exponent `1 < p < ∞` and every boundary datum in `W^{1,p}`.

* `exists_minimizer_vectorWkpLIntegral_prescribed_boundary`: a minimizer of the nonnegative
  extended integral of `F + b`, for a measurable lower bound `c |Du|ᵖ - b(x) ≤ F`.
* `exists_minimizer_vectorWkpIntegral_prescribed_boundary`: for integrable `b`, the same field
  minimizes the signed extended energy of `F`.
* `integrable_vectorWkp_density`, `integrable_vectorWkp_density_of_le`: under the growth bound
  `|F| ≤ a(x) + D |(u, Du)|ᵖ` (in the maximum norm of the pair), or the two one-sided bounds
  of the next theorem, the density is integrable on every Sobolev field.
* `exists_minimizer_integral_vectorWkp_prescribed_boundary`: under the upper bound
  `F ≤ a(x) + D |(u, Du)|ᵖ` a field minimizes the ordinary integral `∫ F(x, u, Du)`.

## Relations

* The second theorem is the first through `PDE.Analysis.lowerBoundedIntegral_le_iff`, and the
  fourth is the second through `vectorWkpIntegral_eq_integral`.
* `integral_firstVariation_eq_zero_of_vectorWkpLIntegral_le` gives the weak Euler–Lagrange
  system at these minimizers when the density is differentiable with conjugate growth.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(a), Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Topology Sobolev

namespace PDE.CalculusOfVariations

/-- Every prescribed affine finite Sobolev class has a minimizer for a coupled extended energy
whose density is continuous in the value, convex in the full gradient and coercive in the
gradient with exponent `1 < p < ∞`, on a bounded measurable set of positive dimension. The
number of components is arbitrary. No derivative of the density, no finite-energy competitor,
no upper growth bound and no boundary regularity is assumed. On an open set the class
`u - g ∈ W₀^{1,p}` in each component is the class of the boundary datum `g`. -/
theorem exists_minimizer_vectorWkpLIntegral_prescribed_boundary
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(m * n),
      Continuous (fun s : ℝ^m ↦ F x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun z : ℝ^(m * n) ↦ F x (s, z)))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
      (∀ i, u i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) ∧
      ∀ v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
        (∀ i, v i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) →
        vectorWkpLIntegral F b u ≤ vectorWkpLIntegral F b v := by
  have hclosed : IsSeqClosed (toWeakSpace ℝ
      (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) '' univ) := by
    rw [image_univ_of_surjective (toWeakSpace ℝ _).surjective]
    exact isClosed_univ.isSeqClosed
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let q := ENNReal.conjExponent (p : ℝ≥0∞)
  have : ENNReal.HolderConjugate (p : ℝ≥0∞) q := inferInstance
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q (p : ℝ≥0∞)⟩
  have hpE : 1 < (p : ℝ≥0∞) := by exact_mod_cast hp
  have hq_top : q ≠ ∞ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q (p : ℝ≥0∞)).mpr hpE).ne
  have hlower' : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n), -b x ≤ F x z := by
    filter_upwards [hlower] with x hx
    intro z
    have hnonneg := mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg z.2) (p : ℝ))
    have h := hx z.1 z.2
    linarith
  suffices hlsc : ∀ {w : ℕ → Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω)}
      {wLimit : Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω)},
      Tendsto (fun j ↦ toWeakSpace ℝ (Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω)) (w j)) atTop
        (𝓝 (toWeakSpace ℝ (Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω)) wLimit)) →
      vectorWkpLIntegral F b (g + RellichKondrachov.vectorWkp0SubtypeL wLimit) ≤
        liminf (fun j ↦ vectorWkpLIntegral F b
          (g + RellichKondrachov.vectorWkp0SubtypeL (w j))) atTop by
    obtain ⟨u, _, hu, hmin⟩ :=
      exists_minimizer_vectorWkpLIntegral_prescribed_boundary_of_zeroBoundary_weak_lsc
        hbounded hp hc hlower g hlsc hclosed (mem_univ _)
    exact ⟨u, hu, fun v hv ↦ hmin v (mem_univ _) hv⟩
  -- lower semicontinuity along weakly convergent zero-boundary corrections
  intro w wLimit hw
  let G : (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) →L[ℝ] Lp (ℝ^(m * n)) p (domainMeasure n Ω) :=
    vectorWkpGradientCLM
  have hvalue := RellichKondrachov.tendsto_vectorWkpValueCLM_add_vectorWkp0SubtypeL
    hΩ hbounded ENNReal.coe_ne_top g hw
  have hgradient : Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^(m * n)) p (domainMeasure n Ω))
      (G (g + RellichKondrachov.vectorWkp0SubtypeL (w j)))) atTop
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^(m * n)) p (domainMeasure n Ω))
        (G (g + RellichKondrachov.vectorWkp0SubtypeL wLimit)))) :=
    (WeakSpace.map G).continuous.continuousAt.tendsto.comp
      (RellichKondrachov.tendsto_weak_add_vectorWkp0SubtypeL g hw)
  -- strong convergence of the values gives almost-everywhere convergence along subsequences
  simpa only [vectorWkpLIntegral, Pi.neg_apply, sub_neg_eq_add] using
    le_liminf_of_tendsto_Lp_of_forall_subseq_ae
      (J := fun j ↦ ∫⁻ x, ENNReal.ofReal (F x
        (vectorWkpValueCLM (g + RellichKondrachov.vectorWkp0SubtypeL (w j)) x,
          G (g + RellichKondrachov.vectorWkp0SubtypeL (w j)) x) - (-b) x) ∂domainMeasure n Ω)
      hvalue fun φ hφ hae ↦
      lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient
        (p := (p : ℝ≥0∞)) (q := q) hq_top hF hb.neg hFcont hconvex hlower'
        (fun j ↦ (Lp.stronglyMeasurable (vectorWkpValueCLM
          (g + RellichKondrachov.vectorWkp0SubtypeL (w (φ j))))).measurable)
        (Lp.stronglyMeasurable (vectorWkpValueCLM
          (g + RellichKondrachov.vectorWkp0SubtypeL wLimit))).measurable hae
        (hgradient.comp hφ)

/-- For an integrable lower bound, the minimizer of the shifted nonnegative integral minimizes
the signed extended energy `vectorWkpIntegral F`, the difference of the integrals of the
positive and the negative part of `F(x, u, Du)`. The hypotheses are those of
`exists_minimizer_vectorWkpLIntegral_prescribed_boundary`, with `b` integrable. The energy may
be `+∞` on some or all competitors. -/
theorem exists_minimizer_vectorWkpIntegral_prescribed_boundary
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Integrable b (domainMeasure n Ω))
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(m * n),
      Continuous (fun s : ℝ^m ↦ F x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun z : ℝ^(m * n) ↦ F x (s, z)))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
      (∀ i, u i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) ∧
      ∀ v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
        (∀ i, v i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) →
        vectorWkpIntegral F u ≤ vectorWkpIntegral F v := by
  -- a measurable representative of the lower bound
  let b' := hb.aestronglyMeasurable.mk b
  have hbb' : b =ᵐ[domainMeasure n Ω] b' := hb.aestronglyMeasurable.ae_eq_mk
  have hlower' : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b' x ≤ F x (s, z) := by
    filter_upwards [hlower, hbb'] with x hx hxb
    rw [← hxb]
    exact hx
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_vectorWkpLIntegral_prescribed_boundary hΩ hbounded hp
    hF hb.aestronglyMeasurable.stronglyMeasurable_mk.measurable hFcont hconvex hc hlower' g
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  have hmeas (w : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) : AEStronglyMeasurable
      (fun x ↦ F x (vectorWkpValueCLM w x, ∇ w x)) (domainMeasure n Ω) :=
    (hF.comp (measurable_id.prodMk
      ((Lp.stronglyMeasurable (vectorWkpValueCLM w)).measurable.prodMk
        (Lp.stronglyMeasurable (∇ w)).measurable))).aestronglyMeasurable
  have hlow (w : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) : ∀ᵐ x ∂domainMeasure n Ω,
      -b' x ≤ F x (vectorWkpValueCLM w x, ∇ w x) := by
    filter_upwards [hlower'] with x hx
    have h := hx (vectorWkpValueCLM w x) (∇ w x)
    have hnonneg := mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg (∇ w x)) (p : ℝ))
    linarith
  exact (PDE.Analysis.lowerBoundedIntegral_le_iff (hmeas u) (hmeas v) (hb.congr hbb')
    (hlow u) (hlow v)).mpr (hmin v hv)

/-- A jointly measurable density with an integrable `p`-growth bound in the pair of the value
and the gradient is integrable on every Sobolev system, for `1 ≤ p < ∞`. The norm of the pair
is the maximum of the two Euclidean norms. -/
theorem integrable_vectorWkp_density
    {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {a : ℝ^n → ℝ} {D : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : Integrable a (domainMeasure n Ω))
    (hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ z, ‖F x z‖ ≤ a x + D * ‖z‖ ^ p.toReal)
    (u : Fin m → W^{1,p}(Ω)) :
    Integrable (fun x ↦ F x (vectorWkpValueCLM u x, ∇ u x)) (domainMeasure n Ω) :=
  (memLp_prod_iff.mpr
    ⟨Lp.memLp (vectorWkpValueCLM u), Lp.memLp (∇ u)⟩).integrable_comp_of_norm_rpow_le
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp_top hF ha hgrowth

/-- A jointly measurable density between `c |Du|ᵖ - b(x)` with `c ≥ 0` and
`a(x) + D |(u, Du)|ᵖ`, for integrable `a` and `b`, is integrable on every Sobolev system. The
two one-sided bounds give the two-sided bound of `integrable_vectorWkp_density`. -/
theorem integrable_vectorWkp_density_of_le
    {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {a b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F))
    (ha : Integrable a (domainMeasure n Ω)) (hb : Integrable b (domainMeasure n Ω))
    {c D : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (hupper : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n),
      F x z ≤ a x + D * ‖z‖ ^ (p : ℝ))
    (u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    Integrable (fun x ↦ F x (vectorWkpValueCLM u x, ∇ u x)) (domainMeasure n Ω) := by
  have hgrowth : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n),
      ‖F x z‖ ≤ (|a x| + |b x|) + |D| * ‖z‖ ^ ((p : ℝ≥0∞).toReal) := by
    filter_upwards [hlower, hupper] with x hl hu z
    have h1 : c * ‖z.2‖ ^ (p : ℝ) - b x ≤ F x z := hl z.1 z.2
    have h2 := hu z
    have h3 := mul_nonneg hc (Real.rpow_nonneg (norm_nonneg z.2) (p : ℝ))
    have h4 : D * ‖z‖ ^ (p : ℝ) ≤ |D| * ‖z‖ ^ (p : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self D) (Real.rpow_nonneg (norm_nonneg z) _)
    have h5 := mul_nonneg (abs_nonneg D) (Real.rpow_nonneg (norm_nonneg z) (p : ℝ))
    rw [ENNReal.coe_toReal, Real.norm_eq_abs, abs_le]
    constructor
    · linarith [le_abs_self (b x), abs_nonneg (a x)]
    · linarith [le_abs_self (a x), abs_nonneg (b x)]
  exact integrable_vectorWkp_density ENNReal.coe_ne_top hF (ha.abs.add hb.abs) hgrowth u

/-- Under an upper bound `F ≤ a(x) + D |(u, Du)|ᵖ` with `a` integrable, the density is
integrable on every Sobolev system and the minimizer of
`exists_minimizer_vectorWkpIntegral_prescribed_boundary` minimizes the ordinary integral
`∫ F(x, u, Du)` in the class of the boundary datum. The density is measurable, continuous in
the value, convex in the gradient and bounded below by `c |Du|ᵖ - b(x)` with `b` integrable;
it need not be differentiable. -/
theorem exists_minimizer_integral_vectorWkp_prescribed_boundary
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {a b : ℝ^n → ℝ}
    (hF : Measurable (Function.uncurry F))
    (ha : Integrable a (domainMeasure n Ω)) (hb : Integrable b (domainMeasure n Ω))
    (hFcont : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^(m * n),
      Continuous (fun s : ℝ^m ↦ F x (s, z)))
    (hconvex : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^m,
      ConvexOn ℝ univ (fun z : ℝ^(m * n) ↦ F x (s, z)))
    {c D : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (hupper : ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n),
      F x z ≤ a x + D * ‖z‖ ^ (p : ℝ))
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
      (∀ i, u i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) ∧
      ∀ v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
        (∀ i, v i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) →
        (∫ x, F x (vectorWkpValueCLM u x, ∇ u x) ∂domainMeasure n Ω) ≤
          ∫ x, F x (vectorWkpValueCLM v x, ∇ v x) ∂domainMeasure n Ω := by
  have hint (w : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :=
    integrable_vectorWkp_density_of_le hF ha hb hc.le hlower hupper w
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_vectorWkpIntegral_prescribed_boundary hΩ hbounded hp
    hF hb hFcont hconvex hc hlower g
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  have h := hmin v hv
  rw [vectorWkpIntegral_eq_integral (hint u), vectorWkpIntegral_eq_integral (hint v)] at h
  exact EReal.coe_le_coe_iff.mp h

end PDE.CalculusOfVariations
