/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Monotone.FiniteExponent.Existence

/-!
# Monotone reactions at finite Sobolev exponents

For `1 < p < ∞`, a coercive monotone flux and a continuous monotone reaction give
a weak solution of `-div a(x, Du) + g(x, u) = ℓ` for every continuous dual load.
Both coefficients have `(p-1)` growth with conjugate-integrable offsets.

The gradient and base-coordinate maps each induce a dual-valued operator through
the same power-growth construction. Hölder gives the pairings, and dominated
convergence gives hemicontinuity. The reaction need not vanish at zero: monotonicity
bounds its negative contribution by the fixed dual norm of its value at zero.
The superlinear flux lower bound absorbs this linear term.

The solution belongs to the supported-core closure on any bounded set in positive
dimension. On an open set this is the usual zero-boundary `W^{1,p}` space.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal Sobolev Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal}
  [Fact (1 ≤ (p : ℝ≥0∞))]

local notation "μ" => domainMeasure n Ω
local notation "q" => ENNReal.conjExponent (p : ℝ≥0∞)
local notation "V" => W₀^{1,p}(Ω)
local notation "D" => wkpGradientCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)
local notation "Q" =>
  wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)

/-- Conjugate power growth makes the reaction pairing integrable for any two
finite-exponent Sobolev functions. Neither zero boundary data nor boundedness of
the domain is needed for this Hölder estimate. -/
theorem integrable_wkpNemytskii_test
    (g : ℝ^n → ℝ → ℝ) {h : ℝ^n → ℝ} {C : ℝ}
    (hgmeas : Measurable (Function.uncurry g)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h x + C * ‖s‖ ^ ((p : ℝ) - 1))
    (u v : W^{1,p}(Ω)) :
    Integrable (fun x ↦ g x (Q u x) * Q v x) μ :=
  ((Lp.memLp (Q u)).comp_of_norm_rpow_sub_one_le
    ENNReal.coe_ne_top hgmeas hh hgrowth).integrable_mul (Lp.memLp (Q v))

/-- A monotone coercive flux and a continuous monotone reaction of conjugate
power growth admit a zero-boundary weak solution for every continuous dual load.
There is no sign or vanishing condition on `g(x,0)`, no potential assumption, and
no boundary regularity assumption. The operator is built from the coefficients;
its monotonicity, hemicontinuity and coercivity are proved below. -/
theorem exists_weak_solution_of_monotone_wkpGradientFlux_reaction
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    (g : ℝ^n → ℝ → ℝ) {h₀ : ℝ^n → ℝ} {C₀ : ℝ}
    (hgmeas : Measurable (Function.uncurry g)) (hh₀ : MemLp h₀ q μ)
    (hggrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h₀ x + C₀ * ‖s‖ ^ ((p : ℝ) - 1))
    (hgcont : ∀ᵐ x ∂μ, Continuous (g x))
    (hgmono : ∀ᵐ x ∂μ, Monotone (g x))
    (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v : V,
      (∫ x, inner ℝ (a x (∇ (u : W^{1,p}(Ω)) x)) (∇ (v : W^{1,p}(Ω)) x) ∂μ) +
        (∫ x, g x (Q (u : W^{1,p}(Ω)) x) * Q (v : W^{1,p}(Ω)) x ∂μ) = ℓ v := by
  -- Cache the inherited normed structure and its projection for dual-norm estimates.
  let : NormedAddCommGroup V := inferInstance
  let : SeminormedAddCommGroup V :=
    (inferInstance : NormedAddCommGroup V).toSeminormedAddCommGroup
  let : NormedSpace ℝ V := inferInstance
  let G : V →L[ℝ] Lp (ℝ^n) p μ :=
    (D).comp (wkp0SubmoduleOn (n := n) (k := 1)
      (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule.subtypeL
  let P : V →L[ℝ] Lp ℝ p μ :=
    (Q).comp (wkp0SubmoduleOn (n := n) (k := 1)
      (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule.subtypeL
  let A : V → StrongDual ℝ V :=
    wkpGradientFluxOperator ENNReal.coe_ne_top a hmeas hh hgrowth
  let B : V → StrongDual ℝ V :=
    PDE.Analysis.Operator.pGrowthFluxOperator (X := V)
      P ENNReal.coe_ne_top g hgmeas hh₀ hggrowth
  have hgmono' : ∀ᵐ x ∂μ, ∀ z w : ℝ, 0 ≤ inner ℝ (g x z - g x w) (z - w) :=
    hgmono.mono fun x hx z w ↦ by
      rw [Real.inner_apply]
      exact (hx.monovary monotone_id).sub_mul_sub_nonneg w z
  have hghemi : ∀ᵐ x ∂μ, ∀ z w : ℝ, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (g x (z + t • w)) w) (Ici 0) 0 :=
    hgcont.mono fun x hx z w ↦ ((hx.comp (continuous_const.add
      (continuous_id.smul continuous_const))).inner continuous_const).continuousWithinAt
  have hAmono (u v : V) : 0 ≤ (A u - A v) (u - v) :=
    PDE.Analysis.Operator.pGrowthFluxOperator_monotone (X := V)
      G ENNReal.coe_ne_top a hmeas hh hgrowth hmono u v
  have hBmono (u v : V) : 0 ≤ (B u - B v) (u - v) :=
    PDE.Analysis.Operator.pGrowthFluxOperator_monotone (X := V)
      P ENNReal.coe_ne_top g hgmeas hh₀ hggrowth hgmono' u v
  have hBbound (u : V) : -‖B 0‖ * ‖u‖ ≤ B u u := by
    have hz := hBmono u 0
    simp only [sub_zero, sub_apply] at hz
    linarith [(B 0).le_opNorm u, neg_abs_le (B 0 u), Real.norm_eq_abs (B 0 u)]
  let T (u : V) : StrongDual ℝ V := A u + B u
  have hTmono (u v : V) : 0 ≤ (T u - T v) (u - v) := by
    have := add_nonneg (hAmono u v) (hBmono u v)
    simp only [T, sub_apply, add_apply] at this ⊢
    linarith
  have hThemi (u v : V) : ContinuousWithinAt (fun t : ℝ ↦ T (u + t • v) v) (Ici 0) 0 :=
    (PDE.Analysis.Operator.pGrowthFluxOperator_hemicontinuous (X := V)
      G ENNReal.coe_ne_top a hmeas hh hgrowth hhemi u v).add
    (PDE.Analysis.Operator.pGrowthFluxOperator_hemicontinuous (X := V)
      P ENNReal.coe_ne_top g hgmeas hh₀ hggrowth hghemi u v)
  have hcoercive : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : V, R ≤ ‖u‖ → M * ‖u‖ ≤ T u u := by
    intro M _
    obtain ⟨R, hR, hbound⟩ := wkpGradientFluxOperator_coercive
      hp a hmeas hh hgrowth hn hΩ hc hb hlower (M + ‖B 0‖)
    refine ⟨R, hR, fun u hu ↦ ?_⟩
    change M * ‖u‖ ≤ A u u + B u u
    linarith [hbound u hu, hBbound u]
  obtain ⟨u, hu⟩ :=
    PDE.Analysis.Operator.surjective_of_monotone_of_hemicontinuous_of_coercive (E := V)
      (Wkp0SpaceOn.surjective_inclusionInDoubleDual (n := n) (k := 1) (p := (p : ℝ≥0∞))
        (Ω := Ω) (by exact_mod_cast hp) ENNReal.coe_ne_top) T hTmono hThemi hcoercive ℓ
  refine ⟨u, fun v ↦ ?_⟩
  have heq : A u v + B u v = ℓ v := congrArg (fun f : StrongDual ℝ V ↦ f v) hu
  rw [wkpGradientFluxOperator_apply ENNReal.coe_ne_top a hmeas hh hgrowth u v,
    PDE.Analysis.Operator.pGrowthFluxOperator_apply (X := V)
      P ENNReal.coe_ne_top g hgmeas hh₀ hggrowth u v] at heq
  simpa only [Real.inner_apply, P, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] using heq

end SobolevSpace.GraphSpace
