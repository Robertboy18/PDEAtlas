/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strongly continuous operator actions

A family of operators that is continuous at every fixed vector and locally bounded
in operator norm acts jointly continuously on time and vector. Continuity in
operator norm is not needed; this covers strongly continuous semigroups and
families built from dilations.

For a moving vector `u(t)`, split the difference quotient of `A(t)u(t)` into the
change of the operator at the fixed vector `u(x)` and the operator applied to the
difference quotient of `u`. Joint continuity of the action passes the second term
to its limit. This product rule therefore applies to strongly continuous semigroups
whose generators need not be bounded.

A uniform bound also carries strong continuity and norm bounds from a dense set to the whole
space. Perturbation series for semigroups use this: their terms are defined first on the domain
of the generator, which is dense, and then extended by a uniform bound.

## Main results

* `continuous_apply_prod_of_eventually_norm_le`, `continuous_apply_prod_of_norm_le`: strong
  continuity and a locally uniform, or uniform, operator bound make `(t, x) ↦ L t x` jointly
  continuous.
* `hasDerivWithinAt_clm_apply_of_continuousAt`: the product rule for `t ↦ A t (u t)` from joint
  continuity and the derivative at the fixed vector.
* `continuous_family_of_denseRange`: a uniformly bounded family of operators that is strongly
  continuous on a dense range is strongly continuous.
* `norm_le_of_denseRange`: a bound `‖V (e z)‖ ≤ κ ‖e z‖` on a dense range gives `‖V‖ ≤ κ`.
* `continuous_family_pow_apply`: the powers `(i, y) ↦ (F i)ᵏ y` of a uniformly bounded, strongly
  continuous family are jointly continuous.

## How it works

The uniform bound `‖F i‖ ≤ N` makes the family equicontinuous:
`‖F i y - F i₀ y‖ ≤ 2 N ‖y - e z‖ + ‖F i (e z) - F i₀ (e z)‖`, and `e z` can be taken as close to
`y` as we like. A bound `‖V y‖ ≤ κ ‖y‖` has continuous sides, so it passes from the range of `e` to
its closure. The powers follow by induction from `continuous_apply_prod_of_norm_le`, which is the
case of the first power.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE.Analysis

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Strong continuity and a locally uniform operator bound give joint continuity of
the action `(t, x) ↦ L t x`. -/
theorem continuous_apply_prod_of_eventually_norm_le {X : Type*} [TopologicalSpace X]
    {L : X → E →L[𝕜] F} (hL : ∀ x, Continuous fun t ↦ L t x)
    (hbdd : ∀ t₀, ∃ C, ∀ᶠ t in 𝓝 t₀, ‖L t‖ ≤ C) :
    Continuous fun p : X × E ↦ L p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨C, hC⟩ := hbdd p.1
  change Tendsto (fun q : X × E ↦ L q.1 q.2) (𝓝 p) (𝓝 (L p.1 p.2))
  have hsmall : Tendsto (fun q : X × E ↦ L q.1 (q.2 - p.2)) (𝓝 p) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun q : X × E ↦ C * ‖q.2 - p.2‖) ?_ ?_
    · filter_upwards [continuous_fst.continuousAt.eventually hC] with q hq
      exact (L q.1).le_of_opNorm_le hq _
    · have hcont : Continuous (fun q : X × E ↦ C * ‖q.2 - p.2‖) :=
        (continuous_snd.sub continuous_const).norm.const_mul C
      simpa only [sub_self, norm_zero, mul_zero] using hcont.tendsto p
  have horbit : Tendsto (fun q : X × E ↦ L q.1 p.2) (𝓝 p) (𝓝 (L p.1 p.2)) :=
    (hL p.2).continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
  simpa only [map_sub, sub_add_cancel, zero_add] using hsmall.add horbit

/-- Strong continuity and a uniform operator bound give joint continuity of the
action `(t, x) ↦ L t x`. -/
theorem continuous_apply_prod_of_norm_le {X : Type*} [TopologicalSpace X]
    {L : X → E →L[𝕜] F} {C : ℝ} (hL : ∀ x, Continuous fun t ↦ L t x)
    (hLC : ∀ t, ‖L t‖ ≤ C) :
    Continuous fun p : X × E ↦ L p.1 p.2 :=
  continuous_apply_prod_of_eventually_norm_le hL fun _ ↦ ⟨C, Eventually.of_forall hLC⟩

/-- Differentiate an operator action using joint continuity and the derivative at
the fixed vector, without requiring an operator-norm derivative. -/
theorem hasDerivWithinAt_clm_apply_of_continuousAt
    {A : 𝕜 → E →L[𝕜] F} {u : 𝕜 → E} {u' : E} {v : F} {s : Set 𝕜} {x : 𝕜}
    (hA : ContinuousAt (fun p : 𝕜 × E ↦ A p.1 p.2) (x, u'))
    (hfixed : HasDerivWithinAt (fun t ↦ A t (u x)) v s x)
    (hu : HasDerivWithinAt u u' s x) :
    HasDerivWithinAt (fun t ↦ A t (u t)) (v + A x u') s x := by
  have htime : Tendsto (fun t : 𝕜 ↦ t) (𝓝[s \ {x}] x) (𝓝 x) :=
    nhdsWithin_le_nhds
  have hmoving := hA.tendsto.comp
    (htime.prodMk_nhds (hasDerivWithinAt_iff_tendsto_slope.mp hu))
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  refine ((hasDerivWithinAt_iff_tendsto_slope.mp hfixed).add hmoving).congr'
    (Eventually.of_forall fun t ↦ ?_)
  change (t - x)⁻¹ • (A t (u x) - A x (u x)) +
    A t ((t - x)⁻¹ • (u t - u x)) =
      (t - x)⁻¹ • (A t (u t) - A x (u x))
  rw [map_smul, map_sub]
  module

section DenseRange

variable {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [TopologicalSpace ι]

/-- **Strong continuity from a dense set.** A uniformly bounded family of operators that is
strongly continuous on a dense range is strongly continuous: `‖F i y - F i₀ y‖` is at most
`2 N ‖y - e z‖ + ‖F i (e z) - F i₀ (e z)‖`. -/
theorem continuous_family_of_denseRange {Z : Type*} {e : Z → X} (he : DenseRange e)
    {F : ι → X →L[𝕜] Y} {N : ℝ} (hb : ∀ i, ‖F i‖ ≤ N) (hc : ∀ z, Continuous fun i ↦ F i (e z))
    (y : X) : Continuous fun i ↦ F i y := by
  refine continuous_iff_continuousAt.mpr fun i₀ ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hN : 0 < |N| + 1 := by positivity
  obtain ⟨z, hz⟩ := he.exists_dist_lt y (div_pos hε (mul_pos three_pos hN))
  have hb' : ∀ j, ‖F j (y - e z)‖ ≤ ε / 3 := fun j ↦
    calc ‖F j (y - e z)‖ ≤ |N| * (ε / (3 * (|N| + 1))) :=
        ((F j).le_opNorm _).trans (mul_le_mul ((hb j).trans (le_abs_self N))
          (by rw [← dist_eq_norm]; exact hz.le) (norm_nonneg _) (abs_nonneg N))
      _ = ε / 3 * (|N| / (|N| + 1)) := by field_simp
      _ ≤ ε / 3 * 1 := by
          gcongr
          exact (div_le_one hN).mpr (by linarith)
      _ = ε / 3 := mul_one _
  filter_upwards [Metric.tendsto_nhds.mp ((hc z).tendsto i₀) (ε / 3) (by positivity)] with i hi
  rw [dist_eq_norm] at hi ⊢
  have e1 : F i y - F i₀ y = F i (y - e z) + (F i (e z) - F i₀ (e z)) - F i₀ (y - e z) := by
    simp only [map_sub]
    abel
  rw [e1]
  have h1 := hb' i
  have h2 := hb' i₀
  calc ‖F i (y - e z) + (F i (e z) - F i₀ (e z)) - F i₀ (y - e z)‖
      ≤ ‖F i (y - e z)‖ + ‖F i (e z) - F i₀ (e z)‖ + ‖F i₀ (y - e z)‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ < ε := by linarith

/-- A bound on a dense range bounds the operator norm: if `‖V (e z)‖ ≤ κ ‖e z‖` for all `z` and
the range of `e` is dense, then `‖V‖ ≤ κ`. -/
theorem norm_le_of_denseRange {Z : Type*} {e : Z → X} (he : DenseRange e) {V : X →L[𝕜] Y}
    {κ : ℝ} (hκ : 0 ≤ κ) (h : ∀ z, ‖V (e z)‖ ≤ κ * ‖e z‖) : ‖V‖ ≤ κ :=
  V.opNorm_le_bound hκ fun y ↦ he.induction_on (p := fun y ↦ ‖V y‖ ≤ κ * ‖y‖) y
    (isClosed_le (by fun_prop) (by fun_prop)) h

/-- The powers of a uniformly bounded, strongly continuous family of operators are jointly
continuous. The first power is `continuous_apply_prod_of_norm_le`, and the induction composes
with it. -/
theorem continuous_family_pow_apply {F : ι → X →L[𝕜] X} {N : ℝ} (hb : ∀ i, ‖F i‖ ≤ N)
    (hc : ∀ y, Continuous fun i ↦ F i y) (k : ℕ) :
    Continuous fun p : ι × X ↦ (F p.1 ^ k) p.2 := by
  induction k with
  | zero => simpa using continuous_snd
  | succ k ih =>
    have h : Continuous fun p : ι × X ↦ (F p.1 ^ k) (F p.1 p.2) :=
      ih.comp (continuous_fst.prodMk (continuous_apply_prod_of_norm_le hc hb))
    simpa [pow_succ] using h

end DenseRange

end PDE.Analysis
