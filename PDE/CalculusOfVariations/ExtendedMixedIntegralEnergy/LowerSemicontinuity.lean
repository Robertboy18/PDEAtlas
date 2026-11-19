/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.SupportingFields
public import PDE.CalculusOfVariations.DirectMethod

/-!
# Mixed integral energies without an upper growth bound

The density is convex and differentiable in the gradient variable. For each fixed gradient,
the density and its gradient derivative are continuous in the value variable almost
everywhere. The lower bound is needed only at the limiting pair of fields. This
allows a density on lifted variables whose lower bound holds on the constraint
graph, without imposing that bound at independent lifted arguments. The displayed
nonnegative Lebesgue integral is allowed to be infinite. No upper growth estimate is used.

The first result assumes almost-everywhere convergence of the values. The second derives
this convergence along a subsequence from strong `Lʳ` convergence, after selecting a sequence
on which the energy tends to its liminf. Both use bounded weak `Lᵖ` convergence of the
gradients. The conjugate exponent `q` must be finite for dominated convergence of the
truncated supporting fields; the value exponent `r` need not equal `p`.

The argument is that of the proof of Evans, §8.2.2, Theorem 1 (weak lower semicontinuity):
integrate the convexity inequality on sets where everything is bounded (Evans takes Egoroff
sets), then exhaust the domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.CalculusOfVariations

variable {α E H : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

omit [BorelSpace E] in
/-- On a finite measure space, a mixed integral energy is lower semicontinuous under
almost-everywhere convergence of the values and bounded weak `Lᵖ` convergence of the gradients.
The conjugate exponent `q` is finite. Convexity and differentiability are required only in
the gradient variable; continuity of the density and supporting field in the value variable
supplies their pointwise limits.

The bound by `b` is required only at the limiting pair. Neither the energy nor the
supporting field is assumed globally integrable. If the same bound holds along the
sequence and `b` is integrable, these are the usual energies shifted by a finite,
field-independent quantity. -/
theorem lintegral_le_liminf_of_tendsto_ae_weak_of_convex_gradient
    (hq_top : q ≠ ∞)
    {F : α → E × H → ℝ} {D : α → E × H → H} {b : α → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂μ, ∀ z : H, Continuous (fun s : E ↦ F x (s, z)))
    (hDcont : ∀ᵐ x ∂μ, ∀ z : H, Continuous (fun s : E ↦ D x (s, z)))
    (hconvex : ∀ᵐ x ∂μ, ∀ s : E, ConvexOn ℝ univ (fun z : H ↦ F x (s, z)))
    (hderiv : ∀ᵐ x ∂μ, ∀ (s : E) (z : H),
      HasFDerivAt (fun w : H ↦ F x (s, w)) (innerSL ℝ (D x (s, z))) z)
    {u : ℕ → α → E} {uLimit : α → E}
    (hu_meas : ∀ j, Measurable (u j)) (huLimit_meas : Measurable uLimit)
    (hu : ∀ᵐ x ∂μ, Tendsto (fun j ↦ u j x) atTop (𝓝 (uLimit x)))
    {g : ℕ → Lp H p μ} {gLimit : Lp H p μ}
    (hg : Tendsto (fun j ↦ toWeakSpace ℝ (Lp H p μ) (g j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp H p μ) gLimit)))
    (hlower : ∀ᵐ x ∂μ, b x ≤ F x (uLimit x, gLimit x))
    (R : ℝ) (hgR : ∀ j, ‖g j‖ ≤ R) :
    (∫⁻ x, ENNReal.ofReal (F x (uLimit x, gLimit x) - b x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (F x (u j x, g j x) - b x) ∂μ) atTop := by
  have hpair {v : α → E} (hv : Measurable v) :
      Measurable (fun x ↦ (x, (v x, gLimit x))) :=
    measurable_id.prodMk (hv.prodMk (Lp.stronglyMeasurable gLimit).measurable)
  refine lintegral_le_liminf_of_tendsto_supports_ae hq_top
    (a := fun j x ↦ F x (u j x, gLimit x) - b x)
    (aLimit := fun x ↦ F x (uLimit x, gLimit x) - b x)
    (d := fun j x ↦ D x (u j x, gLimit x))
    (dLimit := fun x ↦ D x (uLimit x, gLimit x))
    (e := fun j x ↦ F x (u j x, g j x) - b x)
    (fun j ↦ ((hF.comp (hpair (hu_meas j))).sub hb).stronglyMeasurable)
    ((hF.comp (hpair huLimit_meas)).sub hb).stronglyMeasurable
    (fun j ↦ (hD.comp (hpair (hu_meas j))).stronglyMeasurable)
    (hD.comp (hpair huLimit_meas)).stronglyMeasurable ?_ ?_ ?_ hg R hgR ?_
  · filter_upwards [hFcont, hu] with x hFx hux
    exact ((hFx (gLimit x)).continuousAt.tendsto.comp hux).sub tendsto_const_nhds
  · filter_upwards [hDcont, hu] with x hDx hux
    exact (hDx (gLimit x)).continuousAt.tendsto.comp hux
  · filter_upwards [hlower] with x hx
    exact sub_nonneg.mpr hx
  · intro j
    filter_upwards [hconvex, hderiv] with x hcx hdx
    have hs := PDE.Analysis.fderiv_apply_sub_le_sub_of_convex (hcx (u j x))
      (hdx (u j x) (gLimit x)) (g j x) (mem_univ _) (mem_univ _)
    rw [innerSL_apply_apply] at hs
    linarith

/-- A mixed convex-gradient energy is sequentially lower semicontinuous under strong
`Lʳ` convergence of the values and bounded weak `Lᵖ` convergence of the gradients, on a
finite measure space. The energy may be infinite and no global upper growth assumption
is imposed on either the density or its gradient derivative.

The finite conjugate exponent `q` is used only after truncating the supporting fields.
In particular, `1 < p < ∞` is covered. The bound by `b` is needed only at the limiting
pair. If it also holds along the sequence, an integrable `b` gives a finite shift
of the original, extended-valued energies. -/
theorem lintegral_le_liminf_of_tendsto_strong_weak_of_convex_gradient
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hq_top : q ≠ ∞)
    {F : α → E × H → ℝ} {D : α → E × H → H} {b : α → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂μ, ∀ z : H, Continuous (fun s : E ↦ F x (s, z)))
    (hDcont : ∀ᵐ x ∂μ, ∀ z : H, Continuous (fun s : E ↦ D x (s, z)))
    (hconvex : ∀ᵐ x ∂μ, ∀ s : E, ConvexOn ℝ univ (fun z : H ↦ F x (s, z)))
    (hderiv : ∀ᵐ x ∂μ, ∀ (s : E) (z : H),
      HasFDerivAt (fun w : H ↦ F x (s, w)) (innerSL ℝ (D x (s, z))) z)
    {u : ℕ → Lp E r μ} {uLimit : Lp E r μ}
    (hu : Tendsto u atTop (𝓝 uLimit))
    {g : ℕ → Lp H p μ} {gLimit : Lp H p μ}
    (hg : Tendsto (fun j ↦ toWeakSpace ℝ (Lp H p μ) (g j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp H p μ) gLimit)))
    (hlower : ∀ᵐ x ∂μ, b x ≤ F x (uLimit x, gLimit x))
    (R : ℝ) (hgR : ∀ j, ‖g j‖ ≤ R) :
    (∫⁻ x, ENNReal.ofReal (F x (uLimit x, gLimit x) - b x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (F x (u j x, g j x) - b x) ∂μ) atTop := by
  let J (j : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (F x (u j x, g j x) - b x) ∂μ
  obtain ⟨ns, henergy, hns⟩ : ∃ ns : ℕ → ℕ,
      Tendsto (J ∘ ns) atTop (𝓝 (liminf J atTop)) ∧ Tendsto ns atTop atTop :=
    exists_seq_tendsto_liminf
  obtain ⟨ms, hms, hu_ae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hu.comp hns)).exists_seq_tendsto_ae
  have hweak : Tendsto
      (fun j ↦ toWeakSpace ℝ (Lp H p μ) (g (ns (ms j)))) atTop
      (𝓝 (toWeakSpace ℝ (Lp H p μ) gLimit)) :=
    hg.comp (hns.comp hms.tendsto_atTop)
  have hlocal := lintegral_le_liminf_of_tendsto_ae_weak_of_convex_gradient hq_top
    hF hD hb hFcont hDcont hconvex hderiv
    (fun j ↦ (Lp.stronglyMeasurable (u (ns (ms j)))).measurable)
    (Lp.stronglyMeasurable uLimit).measurable hu_ae
    hweak hlower R (fun j ↦ hgR (ns (ms j)))
  have henergy' : Tendsto (fun j ↦ J (ns (ms j))) atTop (𝓝 (liminf J atTop)) :=
    henergy.comp hms.tendsto_atTop
  change (∫⁻ x, ENNReal.ofReal (F x (uLimit x, gLimit x) - b x) ∂μ) ≤
    liminf J atTop
  exact hlocal.trans_eq henergy'.liminf_eq

end PDE.CalculusOfVariations
