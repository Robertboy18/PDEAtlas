/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.Minty
public import PDE.Elliptic.Variational.PowerGrowth
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Reflexivity

/-!
# Monotone Dirichlet equations at finite Sobolev exponents

For `1 < p < ∞`, a measurable monotone flux with `(p-1)` growth and a positive
`p`-power pairing lower bound has a weak solution for every continuous dual load.
Pointwise one-sided hemicontinuity passes to the integral operator by dominated
convergence. Bounded-domain Poincaré derives coercivity in the full Sobolev norm.

Real `Lp` reflexivity, finite products, and closed-subspace transfer supply
reflexivity of the supported-core Sobolev closure. Browder–Minty then
applies to the weak flux operator. Forcing terms in the conjugate `Lq`
space give the usual integral right-hand side through Hölder and the base-coordinate map.

The supported-core graph space is used on arbitrary bounded sets. On open sets
this is the standard weak Dirichlet equation; no boundary regularity is needed.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal Topology Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal}
  [Fact (1 ≤ (p : ℝ≥0∞))]

local notation "μ" => domainMeasure n Ω
local notation "q" => ENNReal.conjExponent (p : ℝ≥0∞)
local notation "V" => W₀^{1,p}(Ω)

/-- A monotone flux of `(p-1)` growth with a positive `p`-power pairing
lower bound has a weak Dirichlet solution for every continuous dual load.
Pointwise right hemicontinuity suffices; no potential or strict monotonicity
is required. Reflexivity and operator coercivity follow from `1 < p < ∞`,
boundedness of the domain, and the stated growth conditions.

The flux pairing is integrable for every trial and test field by
`integrable_inner_wkpGradientFlux`. -/
theorem exists_weak_solution_of_monotone_wkpGradientFlux
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v : V,
      (∫ x, inner ℝ
        (a x (∇ (u : W^{1,p}(Ω)) x))
        (∇ (v : W^{1,p}(Ω)) x) ∂μ) = ℓ v := by
  -- Keep the generic operators on the same inherited Sobolev structures.
  let : NormedAddCommGroup V := inferInstance
  let : NormedSpace ℝ V := inferInstance
  have hpE : 1 < (p : ℝ≥0∞) := by exact_mod_cast hp
  let D : V →L[ℝ] Lp (ℝ^n) p μ :=
    (wkpGradientCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)).comp
      (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
        (Ω := Ω)).toSubmodule.subtypeL
  let A : V → StrongDual ℝ V :=
    wkpGradientFluxOperator ENNReal.coe_ne_top a hmeas hh hgrowth
  have hmonoA : ∀ u v : V, 0 ≤ (A u - A v) (u - v) := by
    intro u v
    exact PDE.Analysis.Operator.pGrowthFluxOperator_monotone (X := V)
      D ENNReal.coe_ne_top a hmeas hh hgrowth hmono u v
  have hhemiA : ∀ u v : V, ContinuousWithinAt
      (fun t : ℝ ↦ A (u + t • v) v) (Ici 0) 0 := by
    intro u v
    exact PDE.Analysis.Operator.pGrowthFluxOperator_hemicontinuous (X := V)
      D ENNReal.coe_ne_top a hmeas hh hgrowth hhemi u v
  have hcoercive : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : V, R ≤ ‖u‖ → M * ‖u‖ ≤ A u u := by
    intro M _
    exact wkpGradientFluxOperator_coercive
      hp a hmeas hh hgrowth hn hΩ hc hb hlower M
  have hreflexive :
      Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V) :=
    Wkp0SpaceOn.surjective_inclusionInDoubleDual
      (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω) hpE ENNReal.coe_ne_top
  obtain ⟨u, hu⟩ :=
    PDE.Analysis.Operator.surjective_of_monotone_of_hemicontinuous_of_coercive (E := V)
      hreflexive A hmonoA hhemiA hcoercive ℓ
  refine ⟨u, fun v ↦ ?_⟩
  rw [← wkpGradientFluxOperator_apply ENNReal.coe_ne_top a hmeas hh hgrowth u v]
  exact congrArg (fun f : StrongDual ℝ V ↦ f v) hu

/-- A forcing term in `Lᵠ` gives a weak solution of
`-div a(x, Du) = f` with zero Sobolev boundary data. Hölder constructs the
continuous load from `f ∈ Lᵠ`; the right-hand integral uses the original
representative of `f`, and the test function is its order-zero Sobolev coordinate. -/
theorem exists_weak_solution_of_monotone_wkpGradientFlux_of_memLp
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    {f : ℝ^n → ℝ} (hf : MemLp f q μ) :
    ∃ u : V, ∀ v : V,
      (∫ x, inner ℝ
        (a x (∇ (u : W^{1,p}(Ω)) x))
        (∇ (v : W^{1,p}(Ω)) x) ∂μ) =
      ∫ x, f x * wkpBaseCoordinateCLM (v : W^{1,p}(Ω)) x ∂μ := by
  let B : V →L[ℝ] Lp ℝ p μ :=
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).comp
      (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
        (Ω := Ω)).toSubmodule.subtypeL
  let ℓ : StrongDual ℝ V :=
    (((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q (p : ℝ≥0∞))
      (hf.toLp f)).comp B
  obtain ⟨u, hu⟩ := exists_weak_solution_of_monotone_wkpGradientFlux
    hp a hmeas hh hgrowth hn hΩ hmono hhemi hc hb hlower ℓ
  refine ⟨u, fun v ↦ (hu v).trans ?_⟩
  change (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q (p : ℝ≥0∞)
      (hf.toLp f) (B v) = ∫ x, f x * B v x ∂μ
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  change (hf.toLp f) x * B v x = f x * B v x
  rw [hx]

end SobolevSpace.GraphSpace
