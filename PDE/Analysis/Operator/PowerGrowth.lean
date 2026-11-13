/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Superposition
public import PDE.Analysis.MeasureTheory.LpNorm
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak flux operators with power growth

For conjugate exponents `p, q`, a measurable flux with growth
`h(x) + C * ‖z‖^(p-1)`, where `h ∈ Lᵠ`, pairs integrably with `Lᵖ` fields.
The input exponent is finite; the conjugate exponent may be infinity when `p = 1`.
Composing this pairing with a continuous linear map `D : X → Lᵖ` gives an operator
from `X` to its continuous dual.

Pointwise monotonicity passes to the operator. Right continuity at zero of the
pointwise pairings along lines gives the corresponding hemicontinuity by dominated
convergence. A pointwise power lower bound also passes to the integral pairing,
using the norm identity from `LpNorm`. The measure is arbitrary, and the flux
need not have a potential.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Analysis.Operator

variable {α E X : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- A flux of conjugate power growth pairs integrably with every `Lᵖ`
test field. The real inner product here is on the values of the fields;
the `Lᵖ` space itself need not be Hilbert. -/
theorem integrable_inner_flux_of_rpow_growth
    (hp_top : p ≠ ∞) (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    {u v : α → E} (hu : MemLp u p μ) (hv : MemLp v p μ) :
    Integrable (fun x ↦ inner ℝ (a x (u x)) (v x)) μ := by
  have hflux := hu.comp_of_norm_rpow_sub_one_le hp_top hmeas hh hgrowth
  refine (hflux.norm.integrable_mul hv.norm).mono'
    (hflux.aestronglyMeasurable.inner hv.aestronglyMeasurable) ?_
  exact ae_of_all μ fun x ↦ norm_inner_le_norm _ _

/-- The weak operator induced by a power-growth flux and a continuous
linear field map. Hölder pairs the `Lᵠ` flux with `D v ∈ Lᵖ`.
Taking `D` to be a Sobolev gradient gives the usual divergence-form
operator with weak Dirichlet tests. -/
def pGrowthFluxOperator (D : X →L[ℝ] Lp E p μ)
    (hp_top : p ≠ ∞) (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (u : X) : StrongDual ℝ X :=
  (((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).lpPairing μ q p)
    (Lp.superposition a
      (fun z : Lp E p μ ↦
        (Lp.memLp z).comp_of_norm_rpow_sub_one_le hp_top hmeas hh hgrowth)
      (D u))).comp D

/-- Evaluating the weak operator gives the integral of the
pointwise flux pairing; its integrability follows from power growth. -/
theorem pGrowthFluxOperator_apply (D : X →L[ℝ] Lp E p μ)
    (hp_top : p ≠ ∞) (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (u v : X) :
    pGrowthFluxOperator D hp_top a hmeas hh hgrowth u v =
      ∫ x, inner ℝ (a x (D u x)) (D v x) ∂μ := by
  unfold pGrowthFluxOperator
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_superposition a
    (fun z : Lp E p μ ↦
      (Lp.memLp z).comp_of_norm_rpow_sub_one_le hp_top hmeas hh hgrowth)
    (D u)] with x hx
  change inner ℝ _ _ = _
  rw [hx]

/-- Pointwise monotonicity of a power-growth flux passes to its weak
operator for any continuous linear field map. -/
theorem pGrowthFluxOperator_monotone (D : X →L[ℝ] Lp E p μ)
    (hp_top : p ≠ ∞) (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w))
    (u v : X) :
    0 ≤ (pGrowthFluxOperator D hp_top a hmeas hh hgrowth u -
      pGrowthFluxOperator D hp_top a hmeas hh hgrowth v) (u - v) := by
  rw [sub_apply, pGrowthFluxOperator_apply, pGrowthFluxOperator_apply,
    ← integral_sub
      (integrable_inner_flux_of_rpow_growth hp_top a hmeas hh hgrowth
        (Lp.memLp (D u)) (Lp.memLp (D (u - v))))
      (integrable_inner_flux_of_rpow_growth hp_top a hmeas hh hgrowth
        (Lp.memLp (D v)) (Lp.memLp (D (u - v))))]
  apply integral_nonneg_of_ae
  have hsub : D (u - v) =ᵐ[μ] fun x ↦ D u x - D v x := by
    rw [map_sub]
    exact Lp.coeFn_sub (D u) (D v)
  filter_upwards [hmono, hsub] with x hx hsubx
  rw [hsubx, ← inner_sub_left]
  exact hx _ _

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Pointwise one-sided hemicontinuity passes under the integral for
a flux with conjugate power growth. Hölder gives the dominating
function on each line segment for finite `p ≥ 1`, including `p = 1`, `q = ∞`. -/
theorem continuousWithinAt_integral_inner_flux_of_rpow_growth
    (hp_top : p ≠ ∞)
    (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : E, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    (u v : Lp E p μ) :
    ContinuousWithinAt
      (fun t : ℝ ↦ ∫ x, inner ℝ (a x (u x + t • v x)) (v x) ∂μ)
      (Ici 0) 0 := by
  have hpexp : 0 ≤ p.toReal - 1 := by
    simpa only [
      ENNReal.toReal_sub_of_le (ENNReal.HolderConjugate.one_le p q) hp_top,
      ENNReal.toReal_one] using
      (ENNReal.toReal_nonneg : 0 ≤ (p - 1).toReal)
  let B (x : α) :=
    (‖h x‖ + |C| * (‖u x‖ + ‖v x‖) ^ (p.toReal - 1)) * ‖v x‖
  have hB : Integrable B μ :=
    (Lp.memLp u).integrable_rpow_growth_bound (Lp.memLp v) hp_top hh C
  have hline (t : ℝ) : MemLp (fun x ↦ u x + t • v x) p μ :=
    (Lp.memLp u).add ((Lp.memLp v).const_smul t)
  have hmeasline : ∀ᶠ t : ℝ in 𝓝[Ici 0] 0,
      AEStronglyMeasurable (fun x ↦ inner ℝ (a x (u x + t • v x)) (v x)) μ :=
    Eventually.of_forall fun t ↦
      (integrable_inner_flux_of_rpow_growth hp_top a hmeas hh hgrowth
        (hline t) (Lp.memLp v)).aestronglyMeasurable
  have hdom : ∀ᶠ t : ℝ in 𝓝[Ici 0] 0, ∀ᵐ x ∂μ,
      ‖inner ℝ (a x (u x + t • v x)) (v x)‖ ≤ B x := by
    have htlt : ∀ᶠ t : ℝ in 𝓝[Ici 0] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, htlt] with t ht0 ht1
    filter_upwards [hgrowth] with x hx
    have hnorm : ‖u x + t • v x‖ ≤ ‖u x‖ + ‖v x‖ := by
      calc
        ‖u x + t • v x‖ ≤ ‖u x‖ + ‖t • v x‖ := norm_add_le _ _
        _ ≤ ‖u x‖ + ‖v x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          nlinarith [norm_nonneg (v x)]
    have hflux : ‖a x (u x + t • v x)‖ ≤
        ‖h x‖ + |C| * (‖u x‖ + ‖v x‖) ^ (p.toReal - 1) := by
      calc
        ‖a x (u x + t • v x)‖ ≤
            h x + C * ‖u x + t • v x‖ ^ (p.toReal - 1) := hx _
        _ ≤ ‖h x‖ + |C| * ‖u x + t • v x‖ ^ (p.toReal - 1) :=
          add_le_add (by simpa only [Real.norm_eq_abs] using le_abs_self (h x))
            (mul_le_mul_of_nonneg_right (le_abs_self C)
              (Real.rpow_nonneg (norm_nonneg _) _))
        _ ≤ ‖h x‖ + |C| * (‖u x‖ + ‖v x‖) ^ (p.toReal - 1) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hnorm hpexp) (abs_nonneg C))
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hflux (norm_nonneg _))
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun t : ℝ ↦ inner ℝ (a x (u x + t • v x)) (v x))
        (𝓝[Ici 0] 0) (𝓝 (inner ℝ (a x (u x)) (v x))) := by
    filter_upwards [hhemi] with x hx
    simpa only [ContinuousWithinAt, zero_smul, add_zero] using hx (u x) (v x)
  simpa only [ContinuousWithinAt, zero_smul, add_zero] using
    tendsto_integral_filter_of_dominated_convergence B hmeasline hdom hB hlim

/-- A power-growth flux gives a hemicontinuous weak operator under the
pointwise one-sided hemicontinuity hypothesis. The domination estimate
is derived from growth rather than assumed for the integrated operator. -/
theorem pGrowthFluxOperator_hemicontinuous (D : X →L[ℝ] Lp E p μ)
    (hp_top : p ≠ ∞)
    (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : E, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    (u v : X) :
    ContinuousWithinAt
      (fun t : ℝ ↦ pGrowthFluxOperator D hp_top a hmeas hh hgrowth (u + t • v) v)
      (Ici 0) 0 := by
  have heq (t : ℝ) :
      pGrowthFluxOperator D hp_top a hmeas hh hgrowth (u + t • v) v =
        ∫ x, inner ℝ (a x (D u x + t • D v x)) (D v x) ∂μ := by
    rw [pGrowthFluxOperator_apply]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (D u) (t • D v), Lp.coeFn_smul t (D v)]
      with x hadd hsmul
    simp only [map_add, map_smul, hadd, Pi.add_apply, hsmul, Pi.smul_apply]
  simp_rw [heq]
  exact continuousWithinAt_integral_inner_flux_of_rpow_growth
    hp_top a hmeas hh hgrowth hhemi (D u) (D v)

end PDE.Analysis.Operator

namespace PDE.Analysis.Operator

variable {α E X : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- A pointwise power lower bound for the flux pairing gives the same
bound in the `Lᵖ` norm of the field. Both sides are integrable
functions before their integrals are compared. -/
theorem pGrowthFluxOperator_lower_bound (D : X →L[ℝ] Lp E p μ)
    (hp_top : p ≠ ∞) (a : α → E → E) {h : α → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    {b : α → ℝ} {c : ℝ} (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ p.toReal - b x ≤ inner ℝ (a x z) z)
    (u : X) :
    c * ‖D u‖ ^ p.toReal - (∫ x, b x ∂μ) ≤
      pGrowthFluxOperator D hp_top a hmeas hh hgrowth u u := by
  have hp_zero := ENNReal.HolderConjugate.ne_zero p q
  have hint := (Lp.memLp (D u)).integrable_norm_rpow hp_zero hp_top
  rw [pGrowthFluxOperator_apply]
  calc
    c * ‖D u‖ ^ p.toReal - (∫ x, b x ∂μ) =
        ∫ x, c * ‖D u x‖ ^ p.toReal - b x ∂μ := by
      rw [integral_sub (hint.const_mul c) hb, integral_const_mul,
        ← Lp.norm_rpow_eq_integral hp_zero hp_top (D u)]
    _ ≤ ∫ x, inner ℝ (a x (D u x)) (D u x) ∂μ :=
      integral_mono_ae ((hint.const_mul c).sub hb)
        (integrable_inner_flux_of_rpow_growth hp_top a hmeas hh hgrowth
          (Lp.memLp (D u)) (Lp.memLp (D u)))
        (hlower.mono fun x hx ↦ hx (D u x))

end PDE.Analysis.Operator
