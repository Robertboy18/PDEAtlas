/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Constraints.Minimizer
public import PDE.CalculusOfVariations.Constraints.Multiplier
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Composition.CriticalValues
import PDE.CalculusOfVariations.SecondVariation

/-!
# Multipliers for nonlinear Dirichlet constraints

Every minimizer of the Dirichlet energy under a smooth integral constraint
has a Lagrange multiplier. The constraint derivative may vanish: localized
primitives and Poincaré then show that zero is feasible, so the minimizer is
zero. Otherwise the strict Fréchet derivatives give the multiplier
by Mathlib's Lagrange multiplier theorem.

The conclusion is the weak equation `-Δu = lam * g(u)`, tested against
every element of `H¹₀`. The growth condition is linear on `g`, with no restriction
on `G(0)` or `g(0)`, and no global Lipschitz condition on `g`.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis.Variational PDE.CalculusOfVariations

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "dΩ" => domainMeasure n Ω

/-- The strict first variation of the unforced Dirichlet energy is its
bilinear form. -/
theorem dirichletEnergy_zero_hasStrictFDerivAt (u : H¹₀(Ω)) :
    HasStrictFDerivAt (dirichletEnergy (n := n) (Ω := Ω) 0) (dirichletForm u) u := by
  have h := @quadraticEnergy_hasStrictFDerivAt H¹₀(Ω) inferInstance inferInstance
    dirichletForm dirichletForm_symm (loadFunctional (n := n) (Ω := Ω) 0) u
  change HasStrictFDerivAt (energy dirichletForm (loadFunctional 0)) (dirichletForm u) u
  simpa only [loadFunctional_zero, sub_zero] using h

/-- A degenerate constrained Dirichlet minimizer is zero. Localized primitives
prove that zero lies on the same constraint level; no nondegeneracy assumption
or division by the volume of the domain is used. -/
theorem integralConstraint_minimizer_eq_zero_of_deriv_ae_eq_zero
    (hn : 0 < n) (hΩ : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    {G g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hd : ∀ s, HasDerivAt G (g s) s) {a : ℝ} {u : H¹₀(Ω)}
    (hu : integralConstraint G u = a)
    (hmin : IsMinOn (dirichletEnergy 0) {v : H¹₀(Ω) | integralConstraint G v = a} u)
    (hcritical : (fun x ↦ g (baseCoordCLM u x)) =ᵐ[dΩ] 0) :
    u = 0 := by
  have hpotential : (fun x ↦ G (baseCoordCLM u x)) =ᵐ[dΩ] fun _ ↦ G 0 :=
    potential_ae_eq_at_zero_of_deriv_ae_eq_zero hn hΩ hΩb
      (by norm_num : (1 : NNReal) ≤ 2) hg hd u hcritical
  have hJ : integralConstraint G u = integralConstraint (n := n) (Ω := Ω) G 0 := by
    rw [integralConstraint_zero]
    calc
      _ = ∫ _ : ℝ^n, G 0 ∂dΩ := integral_congr_ae hpotential
      _ = _ := by simp
  have hzero : integralConstraint (n := n) (Ω := Ω) G 0 = a := hJ.symm.trans hu
  have hw : IsWeakSolution (dirichletForm (n := n) (Ω := Ω)) (loadFunctional 0) 0 := by
    intro v
    simp
  have henergy : dirichletEnergy (n := n) (Ω := Ω) 0 u = dirichletEnergy 0 0 :=
    le_antisymm (hmin hzero) (hw.energy_le dirichletForm_symm dirichletForm_self_nonneg u)
  exact hw.eq_of_energy_eq (dirichletForm_isCoercive hn hΩb) dirichletForm_symm henergy

/-- In the degenerate branch, every scalar is a multiplier. This includes
nonconstant constraint potentials whose derivative vanishes along the minimizer. -/
theorem integralConstraint_minimizer_weak_eq_of_deriv_ae_eq_zero
    (hn : 0 < n) (hΩ : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    {G g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hd : ∀ s, HasDerivAt G (g s) s) {a : ℝ} {u : H¹₀(Ω)}
    (hu : integralConstraint G u = a)
    (hmin : IsMinOn (dirichletEnergy 0) {v : H¹₀(Ω) | integralConstraint G v = a} u)
    (hcritical : (fun x ↦ g (baseCoordCLM u x)) =ᵐ[dΩ] 0) (lam : ℝ) (v : H¹₀(Ω)) :
    dirichletForm u v = lam * ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂dΩ := by
  have hu0 := integralConstraint_minimizer_eq_zero_of_deriv_ae_eq_zero
    hn hΩ hΩb hg hd hu hmin hcritical
  have hint : (∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂dΩ) = 0 := by
    calc
      _ = ∫ _ : ℝ^n, (0 : ℝ) ∂dΩ := integral_congr_ae (hcritical.mono fun x hx ↦ by
        change g (baseCoordCLM u x) = 0 at hx
        rw [hx, zero_mul])
      _ = 0 := integral_zero _ _
  rw [hint, mul_zero, hu0, map_zero, zero_apply]

/-- Every constrained minimizer has a weak-equation multiplier,
including the case of a zero constraint derivative. The test space is all
of `H¹₀`, and both integrands use its weak coordinates. -/
theorem exists_multiplier_of_isMinOn_dirichletEnergy_integralConstraint
    (hn : 0 < n) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {G g : ℝ → ℝ} {C : ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hd : ∀ s, HasDerivAt G (g s) s)
    (hgrowth : ∀ s, |g s| ≤ C * (1 + |s|)) {a : ℝ} {u : H¹₀(Ω)}
    (hu : integralConstraint G u = a)
    (hmin : IsMinOn (dirichletEnergy 0) {v : H¹₀(Ω) | integralConstraint G v = a} u) :
    ∃ lam : ℝ, ∀ v : H¹₀(Ω),
      (∫ x, inner ℝ (∇ (u : H¹(Ω)) x) (∇ (v : H¹(Ω)) x) ∂dΩ) =
        lam * ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂dΩ := by
  let : IsFiniteMeasure (domainMeasure n Ω) :=
    ⟨by simpa [domainMeasure] using hΩb.measure_lt_top (μ := volume)⟩
  by_cases hdeg : fderiv ℝ (integralConstraint G) u = 0
  · have hc := (integralConstraint_fderiv_eq_zero_iff hΩ hd hg.continuous hgrowth u).mp hdeg
    refine ⟨0, fun v ↦ ?_⟩
    rw [← dirichletForm_eq_integral_gradient]
    exact integralConstraint_minimizer_weak_eq_of_deriv_ae_eq_zero
      hn hΩ.measurableSet hΩb hg hd hu hmin hc 0 v
  · have hJraw := integralConstraint_hasStrictFDerivAt hd hg.continuous hgrowth u
    have hJ : HasStrictFDerivAt (integralConstraint G)
        (fderiv ℝ (integralConstraint G) u) u := by
      rw [hJraw.hasFDerivAt.fderiv]
      exact hJraw
    have hextr : IsLocalExtrOn (dirichletEnergy (n := n) (Ω := Ω) 0)
        {v : H¹₀(Ω) | integralConstraint G v = integralConstraint G u} u := by
      rw [hu]
      exact Or.inl hmin.isLocalMinOn
    obtain ⟨lam, hlam⟩ := exists_multiplier_of_hasStrictFDerivAt
      hextr (dirichletEnergy_zero_hasStrictFDerivAt u) hJ hdeg
    refine ⟨lam, fun v ↦ ?_⟩
    rw [← dirichletForm_eq_integral_gradient, hlam]
    simpa only [smul_apply, smul_eq_mul] using
      congrArg (lam * ·) (integralConstraint_fderiv_apply hd hg.continuous hgrowth u v)

/-- A smooth potential with linearly growing derivative admits a
constrained Dirichlet minimizer and a multiplier whenever the zero level is
nonempty. -/
theorem exists_minimizer_multiplier_integralConstraint
    (hn : 0 < n) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {C : ℝ}
    (hgrowth : ∀ s, |deriv G s| ≤ C * (1 + |s|))
    (hne : {u : H¹₀(Ω) | integralConstraint G u = 0}.Nonempty) :
    ∃ (u : H¹₀(Ω)) (lam : ℝ), integralConstraint G u = 0 ∧
      IsMinOn (dirichletEnergy 0) {v : H¹₀(Ω) | integralConstraint G v = 0} u ∧
      ∀ v : H¹₀(Ω),
        (∫ x, inner ℝ (∇ (u : H¹(Ω)) x) (∇ (v : H¹(Ω)) x) ∂dΩ) =
          lam * ∫ x, deriv G (baseCoordCLM u x) * baseCoordCLM v x ∂dΩ := by
  have hdiff := (contDiff_infty_iff_deriv.mp hG).1
  have hg := (contDiff_infty_iff_deriv.mp hG).2
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_dirichletEnergy_integralConstraint
    hn hΩ hΩb (fun s ↦ (hdiff s).hasDerivAt) hgrowth hne
  obtain ⟨lam, hlam⟩ := exists_multiplier_of_isMinOn_dirichletEnergy_integralConstraint
    hn hΩ hΩb hg (fun s ↦ (hdiff s).hasDerivAt) hgrowth hu hmin
  exact ⟨u, lam, hu, hmin, hlam⟩

/-- The distributional form of the constrained minimizer equation uses the
smooth test function and its classical partial derivatives. -/
theorem exists_multiplier_testFunction_of_isMinOn_integralConstraint
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {G g : ℝ → ℝ} {C : ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hd : ∀ s, HasDerivAt G (g s) s)
    (hgrowth : ∀ s, |g s| ≤ C * (1 + |s|)) {a : ℝ} {u : H¹₀(Ω)}
    (hu : integralConstraint G u = a)
    (hmin : IsMinOn (dirichletEnergy 0) {v : H¹₀(Ω) | integralConstraint G v = a} u) :
    ∃ lam : ℝ, ∀ φ : TestFunctionOn n Ω,
      (∑ i : Fin n, ∫ x, derivCoordCLM i u x * (∂[i] φ.1.toFun) x ∂dΩ) =
        lam * ∫ x, g (baseCoordCLM u x) * φ.1.toFun x ∂dΩ := by
  -- In dimension zero both sides vanish for the multiplier `0`.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun φ ↦ by simp⟩
  obtain ⟨lam, hlam⟩ := exists_multiplier_of_isMinOn_dirichletEnergy_integralConstraint
    hn hΩ hΩb hg hd hgrowth hu hmin
  refine ⟨lam, fun φ ↦ ?_⟩
  rw [← dirichletForm_testFunction_eq_integral, dirichletForm_eq_integral_gradient,
    hlam]
  congr 1
  apply integral_congr_ae
  filter_upwards [baseCoordCLM_testFunction_apply_ae φ] with x hx
  rw [hx]

end SobolevSpace.GraphSpace
