/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.PowerGrowthContinuity
public import PDE.Analysis.Variational.StrongWeakLowerSemicontinuity
public import PDE.CalculusOfVariations.DirectMethod
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Integral energies with strong values and weak gradients

Consider `J(u, g) = ∫ x, F x (u x, g x) ∂μ`, with convexity only in `g`.
For `1 < p < ∞`, the two fields belong to `Lᵖ`. A `p`-growth bound makes
the density integrable and its integral continuous in the strong topology.
A continuous gradient derivative with `(p-1)`-growth gives a supporting
field in the conjugate space `Lᵠ`, varying strongly with `u` at fixed `g`.

At the limiting gradient, the integrated supporting inequality reads
`J(uᵢ, g) + ⟪D(uᵢ, g), gᵢ - g⟫ ≤ J(uᵢ, gᵢ)`.
The first term converges by continuity of integral energies. Hölder pairing
and bounded weak convergence make the second term tend to zero. Thus every
eventual upper energy bound passes to the limit.

This is the convexity step (23)-(25) in the proof of Evans, §8.2.2, Theorem 1,
under finite-power growth: the growth bounds let us pass to the limit on the
whole domain, where Evans restricts to large sets given by Egoroff's theorem.
Joint measurability, continuity in both field variables, and the derivative
growth bound are explicit. No convexity in the value variable is assumed. The
measure may be infinite: the density offset is in `L¹`, and the derivative
offset is in `Lᵠ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, proof of Theorem 1, (23)-(25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.CalculusOfVariations

variable {α E H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- An eventual upper bound for a convex-gradient integral energy passes to
a limit with strong `Lᵖ` convergence of the values and bounded weak `Lᵖ`
convergence of the gradients, for `1 < p < ∞`.

The density and its inner-product gradient derivative are jointly measurable
and continuous in both field variables almost everywhere. Their respective
growth bounds prove integrability of the density and membership of the
supporting field in the conjugate space `Lᵠ`. Continuity of both induced maps
is derived from these bounds.

The product norm is `max ‖s‖ ‖g‖`. The explicit bound on the weakly
convergent family accommodates arbitrary filters. Neither finite measure
nor completeness of the value spaces is required. -/
theorem integral_le_of_tendsto_strong_weak_of_convex_gradient
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_one : 1 < p) (hp_top : p ≠ ∞)
    {F : α → E × H → ℝ} {D : α → E × H → H}
    (hF : Measurable (Function.uncurry F))
    (hD : Measurable (Function.uncurry D))
    (hFcont : ∀ᵐ x ∂μ, Continuous (F x))
    (hDcont : ∀ᵐ x ∂μ, Continuous (D x))
    (hconvex : ∀ᵐ x ∂μ, ∀ s : E, ConvexOn ℝ univ (fun g : H ↦ F x (s, g)))
    (hderiv : ∀ᵐ x ∂μ, ∀ (s : E) (g : H),
      HasFDerivAt (fun z : H ↦ F x (s, z)) (innerSL ℝ (D x (s, g))) g)
    {a b : α → ℝ} {C L : ℝ} (ha : Integrable a μ) (hb : MemLp b q μ)
    (hFgrowth : ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ a x + C * ‖z‖ ^ p.toReal)
    (hDgrowth : ∀ᵐ x ∂μ, ∀ z, ‖D x z‖ ≤ b x + L * ‖z‖ ^ (p.toReal - 1))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → Lp E p μ} {uLimit : Lp E p μ}
    (hu : Tendsto u l (𝓝 uLimit))
    {g : ι → Lp H p μ} {gLimit : Lp H p μ}
    (hg : Tendsto (fun i ↦ toWeakSpace ℝ (Lp H p μ) (g i)) l
      (𝓝 (toWeakSpace ℝ (Lp H p μ) gLimit)))
    (R : ℝ) (hgR : ∀ i, ‖g i‖ ≤ R)
    {c : ℝ} (hbound : ∀ᶠ i in l, (∫ x, F x (u i x, g i x) ∂μ) ≤ c) :
    (∫ x, F x (uLimit x, gLimit x) ∂μ) ≤ c := by
  let left : Lp E p μ →L[ℝ] Lp (E × H) p μ :=
    (ContinuousLinearMap.inl ℝ E H).compLpL p μ
  let right : Lp H p μ →L[ℝ] Lp (E × H) p μ :=
    (ContinuousLinearMap.inr ℝ E H).compLpL p μ
  let pair (v : Lp E p μ) (z : Lp H p μ) : Lp (E × H) p μ := left v + right z
  have hpair (v : Lp E p μ) (z : Lp H p μ) :
      pair v z =ᵐ[μ] fun x ↦ (v x, z x) := by
    filter_upwards [Lp.coeFn_add (left v) (right z),
      (ContinuousLinearMap.inl ℝ E H).coeFn_compLpL v,
      (ContinuousLinearMap.inr ℝ E H).coeFn_compLpL z] with x hadd hl hr
    calc
      pair v z x = left v x + right z x := hadd
      _ = (v x, 0) + (0, z x) := congrArg₂ (· + ·) hl hr
      _ = (v x, z x) := Prod.ext (add_zero _) (zero_add _)
  have hpaircont (z : Lp H p μ) : Continuous (fun v : Lp E p μ ↦ pair v z) :=
    left.continuous.add continuous_const
  let J (v : Lp E p μ) (z : Lp H p μ) : ℝ := ∫ x, F x (v x, z x) ∂μ
  have hJint (v : Lp E p μ) (z : Lp H p μ) :
      Integrable (fun x ↦ F x (v x, z x)) μ := by
    have hint : Integrable (fun x ↦ F x (pair v z x)) μ :=
      (Lp.memLp (pair v z)).integrable_comp_of_norm_rpow_le
        (zero_lt_one.trans hp_one).ne' hp_top hF ha
        (by simpa only [Real.norm_eq_abs] using hFgrowth)
    exact hint.congr ((hpair v z).mono fun x hx ↦ congrArg (F x) hx)
  have hJcont (z : Lp H p μ) : Continuous (fun v : Lp E p μ ↦ J v z) := by
    refine ((continuous_integral_Lp_of_rpow_growth hp_top hF hFcont ha hFgrowth).comp
      (hpaircont z)).congr ?_
    intro v
    exact integral_congr_ae ((hpair v z).mono fun x hx ↦ congrArg (F x) hx)
  have hDmem (z : Lp (E × H) p μ) : MemLp (fun x ↦ D x (z x)) q μ :=
    (Lp.memLp z).comp_of_norm_rpow_sub_one_le hp_top hD hb hDgrowth
  let V (v : Lp E p μ) (z : Lp H p μ) : Lp H q μ :=
    Lp.superposition D hDmem (pair v z)
  have hV (v : Lp E p μ) (z : Lp H p μ) :
      V v z =ᵐ[μ] fun x ↦ D x (v x, z x) :=
    (Lp.coeFn_superposition D hDmem (pair v z)).trans
      ((hpair v z).mono fun x hx ↦ congrArg (D x) hx)
  have hVcont (z : Lp H p μ) : Continuous (fun v : Lp E p μ ↦ V v z) :=
    (Lp.continuous_superposition_of_conjugate_growth hp_one hp_top
      hD hDcont hb hDgrowth).comp (hpaircont z)
  let P : Lp H q μ →L[ℝ] Lp H p μ →L[ℝ] ℝ :=
    (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).lpPairing μ q p
  have hwork (v : Lp H q μ) (w : Lp H p μ) :
      Integrable (fun x ↦ inner ℝ (v x) (w x)) μ :=
    memLp_one_iff_integrable.mp
      ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp v) (Lp.memLp w))
  have hsupport (v : Lp E p μ) (z w : Lp H p μ) :
      J v z + P (V v z) (w - z) ≤ J v w := by
    calc
      J v z + P (V v z) (w - z) =
          ∫ x, F x (v x, z x) + inner ℝ (V v z x) ((w - z) x) ∂μ := by
        change J v z + (innerSL ℝ).lpPairing μ q p (V v z) (w - z) = _
        rw [ContinuousLinearMap.lpPairing_eq_integral]
        exact (integral_add (hJint v z) (hwork (V v z) (w - z))).symm
      _ ≤ J v w := by
        refine integral_mono_ae ((hJint v z).add (hwork (V v z) (w - z)))
          (hJint v w) ?_
        filter_upwards [hconvex, hderiv, hV v z, Lp.coeFn_sub w z]
          with x hcx hdx hVx hsub
        have hs := PDE.Analysis.fderiv_apply_sub_le_sub_of_convex (hcx (v x))
          (hdx (v x) (z x)) (w x) (mem_univ _) (mem_univ _)
        rw [innerSL_apply_apply] at hs
        change F x (v x, z x) + inner ℝ (V v z x) ((w - z) x) ≤ F x (v x, w x)
        rw [hVx, hsub, Pi.sub_apply]
        linarith
  exact PDE.Analysis.le_of_tendsto_strong_weak_of_supporting_functionals
    hu hg R hgR J (fun v z ↦ P (V v z)) (hJcont gLimit).continuousAt
    ((P.continuous.comp (hVcont gLimit)).continuousAt) hsupport hbound

end PDE.CalculusOfVariations
