/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.DirectMethod
public import PDE.CalculusOfVariations.IntegralEnergy
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Reflexivity
public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent
import PDE.Analysis.MeasureTheory.Lp.Superposition
import PDE.Analysis.Operator.Coercivity
import Mathlib.Analysis.Convex.Continuous

/-!
# Convex gradient energies at finite Sobolev exponents

Let `J(u) = ∫ F(x, Du(x))` on the closure of compactly supported smooth functions
in `W¹ᵖ`. If the density is measurable, convex in the gradient, and satisfies

`c |z|ᵖ - b(x) ≤ F(x,z) ≤ a(x) + C |z|ᵖ`,

with integrable offsets and `c > 0`, the direct method gives a minimizer for
every `1 < p < ∞` on a bounded domain of positive dimension.

Three results do the work. The weak gradient maps the Sobolev
space into vector-valued `Lp`; the convex integral theorem gives weak lower
semicontinuity there; and bounded-domain Poincaré controls the full Sobolev norm.
Reflexivity comes from the closed derivative graph and its supported-core closure.
All density integrals are proved integrable before their values are compared.

No boundary regularity is needed. On open domains the supported-core closure
is the usual space `W¹ᵖ₀`. The density here depends on position and gradient;
dependence on the value of the field requires a separate compactness argument.

Here `∇ u` is the weak gradient in `Lp`; `∇ u x` evaluates its chosen
representative. Identities between these representatives are used almost everywhere.

Compare Evans, §8.2.2, Theorem 2, with `q = p` and zero boundary data: there the Lagrangian is
smooth, may depend on the value, and has no upper growth bound, and the constant `β` of the
coercivity inequality (4) plays the role of `b`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 2 (Existence of minimizer), p. 470.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev ENNReal NNReal Topology

namespace PDE.CalculusOfVariations

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0}
  [Fact (1 ≤ (p : ℝ≥0∞))]

local notation "μ" => domainMeasure n Ω
local notation "V" => W₀^{1,p}(Ω)

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- Two-sided power growth bounds the absolute value of the density by the sum of the
absolute offsets and a multiple of the gradient's `p`th power. -/
theorem abs_density_le_of_rpow_bounds
    {F : ℝ^n → ℝ^n → ℝ} {a b : ℝ^n → ℝ} {c C : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ F x z)
    (hupper : ∀ᵐ x ∂μ, ∀ z, F x z ≤ a x + C * ‖z‖ ^ (p : ℝ)) :
    ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ (|a x| + |b x|) + C * ‖z‖ ^ (p : ℝ) := by
  filter_upwards [hlower, hupper] with x hx hy
  intro z
  have hcz := mul_nonneg hc (Real.rpow_nonneg (norm_nonneg z) (p : ℝ))
  have hCz := mul_nonneg hC (Real.rpow_nonneg (norm_nonneg z) (p : ℝ))
  apply abs_le.2
  constructor
  · linarith [hx z, le_abs_self (b x), abs_nonneg (a x)]
  · linarith [hy z, le_abs_self (a x), abs_nonneg (b x)]

/-- Two-sided power growth with integrable offsets makes the gradient density
integrable for every field at that Sobolev exponent. The domain need not be
bounded or open, and convexity is not needed for this step. -/
theorem integrable_wkpGradient_density_of_rpow_bounds
    {F : ℝ^n → ℝ^n → ℝ} {a b : ℝ^n → ℝ} {c C : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ F x z)
    (hupper : ∀ᵐ x ∂μ, ∀ z, F x z ≤ a x + C * ‖z‖ ^ (p : ℝ))
    (u : W^{1,p}(Ω)) :
    Integrable (fun x ↦ F x (∇ u x)) μ := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : 1 ≤ (p : ℝ≥0∞))).ne'
  apply (Lp.memLp (∇ u)).integrable_comp_of_norm_rpow_le
    hp0 ENNReal.coe_ne_top hF (ha.abs.add hb.abs)
  simpa only [Pi.add_apply, ENNReal.coe_toReal, Real.norm_eq_abs] using
    abs_density_le_of_rpow_bounds hc hC hlower hupper

/-- A measurable density, convex in its gradient variable almost everywhere,
attains its minimum on `W¹ᵖ₀` under two-sided `p` growth, for `1 < p < ∞`.
The positive lower coefficient and bounded-domain Poincaré give coercivity.
Weak lower semicontinuity and Sobolev reflexivity are derived, not assumed. -/
theorem exists_minimizer_wkpGradientIntegral
    (hp : 1 < p) (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    {F : ℝ^n → ℝ^n → ℝ} {a b : ℝ^n → ℝ} {c C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ F x z)
    (hupper : ∀ᵐ x ∂μ, ∀ z, F x z ≤ a x + C * ‖z‖ ^ (p : ℝ)) :
    ∃ u : V, ∀ v : V,
      (∫ x, F x (∇ (u : W^{1,p}(Ω)) x) ∂μ) ≤
        ∫ x, F x (∇ (v : W^{1,p}(Ω)) x) ∂μ := by
  let sobolevNormedGroup : NormedAddCommGroup V :=
    Submodule.normedAddCommGroup
      (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  let sobolevNormedSpace :
      @NormedSpace ℝ V inferInstance sobolevNormedGroup.toSeminormedAddCommGroup :=
    Submodule.normedSpace
      (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  let D : V →L[ℝ] Lp (ℝ^n) p μ :=
    (wkpGradientCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)).comp
      (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
        (Ω := Ω)).toSubmodule.subtypeL
  let J : V → ℝ := fun u ↦ ∫ x, F x (D u x) ∂μ
  have hpE : 1 < (p : ℝ≥0∞) := by exact_mod_cast hp
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans hpE).ne'
  have hFint (u : V) : Integrable (fun x ↦ F x (D u x)) μ :=
    integrable_wkpGradient_density_of_rpow_bounds hF ha hb hc.le hC hlower hupper u
  have hcont : ∀ᵐ x ∂μ, Continuous (F x) :=
    hconvex.mono fun x hx ↦ continuousOn_univ.mp (hx.continuousOn isOpen_univ)
  have hweak : LowerSemicontinuous
      (fun w : WeakSpace ℝ V ↦ J ((toWeakSpace ℝ V).symm w)) := by
    refine @lowerSemicontinuous_weakSpace_integral_Lp_comp_of_growth
      (ℝ^n) (ℝ^n) inferInstance μ inferInstance inferInstance
      (p : ℝ≥0∞) V sobolevNormedGroup sobolevNormedSpace
      inferInstance inferInstance inferInstance D ENNReal.coe_ne_top F _ _ C
      hF hcont hconvex (ha.abs.add hb.abs) hb.neg ?_ ?_
    · filter_upwards [hlower] with x hx
      intro z
      change -b x ≤ F x z
      linarith [hx z, mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg z) (p : ℝ))]
    · simpa only [Pi.add_apply, ENNReal.coe_toReal] using
        abs_density_le_of_rpow_bounds hc.le hC hlower hupper
  have hgradient (u : V) :
      c * ‖D u‖ ^ (p : ℝ) - (∫ x, b x ∂μ) ≤ J u := by
    have hint : Integrable (fun x ↦ ‖D u x‖ ^ (p : ℝ)) μ := by
      simpa only [ENNReal.coe_toReal] using
        (Lp.memLp (D u)).integrable_norm_rpow hp0 ENNReal.coe_ne_top
    calc
      _ = ∫ x, c * ‖D u x‖ ^ (p : ℝ) - b x ∂μ := by
        rw [integral_sub (hint.const_mul c) hb, integral_const_mul]
        congr 1
        congr 1
        simpa only [ENNReal.coe_toReal] using
          Lp.norm_rpow_eq_integral hp0 ENNReal.coe_ne_top (D u)
      _ ≤ J u := integral_mono_ae ((hint.const_mul c).sub hb) (hFint u)
        (hlower.mono fun x hx ↦ hx (D u x))
  obtain ⟨K, hK, hKbound⟩ :=
    exists_pos_mul_norm_rpow_le_norm_wkpGradientCLM_rpow hn hΩ hp.le
  have hk : 0 < c * K := mul_pos hc hK
  have hbound (u : V) :
      (c * K) * ‖u‖ ^ (p : ℝ) - (∫ x, b x ∂μ) ≤ J u := by
    have hscaled : (c * K) * ‖u‖ ^ (p : ℝ) ≤ c * ‖D u‖ ^ (p : ℝ) := by
      calc
        _ = c * (K * ‖u‖ ^ (p : ℝ)) := mul_assoc _ _ _
        _ ≤ c * ‖∇ (u : W^{1,p}(Ω))‖ ^ (p : ℝ) :=
          mul_le_mul_of_nonneg_left (hKbound u) hc.le
        _ = _ := rfl
    exact (sub_le_sub_right hscaled _).trans (hgradient u)
  obtain ⟨R, _, hR⟩ :=
    @PDE.Analysis.exists_radius_mul_norm_le_of_rpow_lower_bound
      V sobolevNormedGroup.toSeminormedAddCommGroup J
      (p : ℝ) (c * K) (∫ x, b x ∂μ) hpR hk hbound 1
  have hcoercive : Tendsto J (Bornology.cobounded V) atTop := by
    refine tendsto_atTop.2 fun B ↦ ?_
    filter_upwards [@eventually_cobounded_le_norm V
      sobolevNormedGroup.toSeminormedAddCommGroup.toSeminormedAddGroup
      (max R B)] with u hu
    have hJu : ‖u‖ ≤ J u := by
      simpa only [one_mul] using hR u ((le_max_left _ _).trans hu)
    exact ((le_max_right _ _).trans hu).trans hJu
  have : IsFiniteMeasure μ := isFiniteMeasure_domainMeasure_of_isBounded hΩ
  have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V) :=
    Wkp0SpaceOn.surjective_inclusionInDoubleDual
      (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) hpE ENNReal.coe_ne_top
  obtain ⟨u, _, hu⟩ :=
    @exists_isMinOn_of_weak_lowerSemicontinuousOn_of_coercive
      V sobolevNormedGroup sobolevNormedSpace hreflexive J
      univ (by simp) ⟨0, mem_univ _⟩
      (hweak.lowerSemicontinuousOn _)
      (by simpa only [Filter.principal_univ, inf_top_eq] using hcoercive)
  exact ⟨u, fun v ↦ hu (mem_univ v)⟩

end PDE.CalculusOfVariations
