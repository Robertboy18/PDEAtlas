/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.SubSupersolution.Iteration

/-!
# Semilinear elliptic equations between weak barriers

Let `L` be a uniformly elliptic divergence-form operator with real bounded
measurable coefficients, including drift and zeroth-order terms. Ordered
weak lower and upper solutions in `H¹₀(Ω)` enclose a weak solution of
`Lu = f(u)` on a bounded measurable set. On open sets this is the usual
homogeneous Dirichlet problem.

A continuous reaction with linear growth suffices if adding a linear
function makes it increasing. This is a lower one-sided slope condition.
The barriers need only belong to `H¹₀`, and the nonlinear load is proved
to lie in `L²`. Globally Lipschitz reactions are a special case.
Reactions Lipschitz on a scalar interval containing both barriers also
satisfy the local one-sided slope condition below.
No zero-offset condition, coefficient symmetry, boundary regularity, or
smallness of the reaction's slope is required.

On a bounded scalar interval containing the barriers, continuity and a lower
one-sided slope bound suffice without a global growth assumption. Projecting
the shifted reaction onto that interval gives the required extension.

Choose a mass shift above both the Gårding threshold and the scalar shift.
The Lax–Milgram solver for `L + mu` preserves order by weak comparison.
The shifted reaction is increasing, so the weak barrier inequalities make
the interval invariant. Linear growth gives an `L²` bound on the loads.
The continuous-superposition theorem and Rellich compactness then
give a fixed point by monotone iteration. Continuity of the solver gives
convergence in `H¹₀`. Canceling the mass terms recovers the original equation.

The boundary condition here is the measurable-domain zero-boundary one.
The geometric signed-trace version is in `SubSupersolution.BoundaryTrace`.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open PDE.Analysis.Variational
open scoped ENNReal InnerProductSpace NNReal Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω
local notation "L2" => DerivLp n 2 Ω

/-- A continuous reaction with linear growth and a monotone scalar shift
has a weak solution between ordered zero-boundary weak barriers.
The shift condition is a lower one-sided slope bound on the reaction; it does not
require a two-sided Lipschitz bound. The nonlinear source is proved to belong to `L²`,
and the same solution satisfies the original equation against every `H¹₀` test.
The growth constants and the scalar shift may be any real numbers satisfying the bounds. -/
theorem exists_weak_solution_between_barriers_of_continuous_of_monotone_shift
    (hΩ : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (g : ℝ → ℝ) (hg : Continuous g) {A C M : ℝ}
    (hgrowth : ∀ s, ‖g s‖ ≤ A + C * ‖s‖)
    (hmono : Monotone (fun s ↦ g s + M * s))
    (lower upper : H¹₀(Ω))
    (hlr : ∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM upper x)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) lower v ≤
      ∫ x, g (baseCoordCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, g (baseCoordCLM upper x) * baseCoordCLM v x ∂μ) ≤
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ baseCoordCLM upper x) ∧
      MemLp (fun x ↦ g (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω),
        fullDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u v =
        ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  apply exists_weak_solution_of_shifted_interval_invariant hΩ hΩbounded a b c hA hbc
    g hg hgrowth hmono (baseCoordCLM lower) (baseCoordCLM upper) hlr
  · intro mu hshift _ f hf u hu
    apply AEEqFun.coeFn_le.mp
    apply base_le_ae_of_isWeakSolution_shiftedDivergenceForm hΩ a b c hA hbc hshift
      _ (loadFunctional f) lower u (fun _ ↦ rfl) hu
    intro v hv
    rw [shiftedDivergenceForm_apply, loadFunctional_eq_integral_add_mass g _ _ _ hf]
    exact add_le_add_left (hlower v hv) _
  · intro mu hshift _ f hf u hu
    apply AEEqFun.coeFn_le.mp
    apply base_le_ae_of_isWeakSolution_shiftedDivergenceForm hΩ a b c hA hbc hshift
      (loadFunctional f) _ u upper hu (fun _ ↦ rfl)
    intro v hv
    rw [shiftedDivergenceForm_apply, loadFunctional_eq_integral_add_mass g _ _ _ hf]
    exact add_le_add_left (hupper v hv) _

/-- Ordered zero-boundary weak barriers enclose a solution of `Lu = g(u)`
for every globally Lipschitz scalar `g`. The equation is tested against all
of `H¹₀`; the nonlinear source belongs to `L²`, so each displayed pairing
is an integrable function. No small-Lipschitz or zero-offset assumption is needed. -/
theorem exists_weak_solution_between_barriers_of_lipschitz
    (hΩ : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (g : ℝ → ℝ) {K : ℝ≥0} (hg : LipschitzWith K g)
    (lower upper : H¹₀(Ω))
    (hlr : ∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM upper x)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) lower v ≤
      ∫ x, g (baseCoordCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, g (baseCoordCLM upper x) * baseCoordCLM v x ∂μ) ≤
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ baseCoordCLM upper x) ∧
      MemLp (fun x ↦ g (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω),
        fullDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u v =
        ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  have hgrowth (s : ℝ) : ‖g s‖ ≤ ‖g 0‖ + (K : ℝ) * ‖s‖ := by
    have hdiff : ‖g s - g 0‖ ≤ (K : ℝ) * ‖s‖ := by
      simpa only [sub_zero] using hg.norm_sub_le s 0
    calc
      ‖g s‖ = ‖(g s - g 0) + g 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖g s - g 0‖ + ‖g 0‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖s‖ + ‖g 0‖ := add_le_add hdiff le_rfl
      _ = ‖g 0‖ + (K : ℝ) * ‖s‖ := add_comm _ _
  exact exists_weak_solution_between_barriers_of_continuous_of_monotone_shift
    hΩ hΩbounded a b c hA hbc g hg.continuous hgrowth
    (monotone_add_mass hg le_rfl) lower upper hlr hlower hupper

/-- A continuous reaction on a compact interval has a global extension with
linear growth and the same monotone shift. Project the shifted reaction onto
the interval and then subtract the linear term. For an empty interval, the
negative linear term alone gives an extension. -/
theorem exists_linear_growth_extension_of_monotoneOn_shift
    (f : ℝ → ℝ) {left right M : ℝ}
    (hf : ContinuousOn f (Icc left right))
    (hmono : MonotoneOn (fun s ↦ f s + M * s) (Icc left right)) :
    ∃ (g : ℝ → ℝ) (A : ℝ),
      Continuous g ∧ EqOn f g (Icc left right) ∧
      (∀ s, ‖g s‖ ≤ A + |M| * ‖s‖) ∧
      Monotone (fun s ↦ g s + M * s) := by
  by_cases hab : left ≤ right
  · let H (s : ℝ) : ℝ := f s + M * s
    have hH : ContinuousOn H (Icc left right) :=
      hf.add (continuous_const.mul continuous_id).continuousOn
    obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
    let P : ℝ → Icc left right := projIcc left right hab
    let g (s : ℝ) : ℝ := H (P s) - M * s
    have hcomp : Continuous (fun s ↦ H (P s)) :=
      hH.domRestrict.comp continuous_projIcc
    refine ⟨g, A, hcomp.sub (continuous_const.mul continuous_id), ?_, ?_, ?_⟩
    · intro s hs
      change f s = H (P s) - M * s
      have hP : (P s : ℝ) = s := congrArg Subtype.val (projIcc_of_mem hab hs)
      rw [hP]
      exact (add_sub_cancel_right (f s) (M * s)).symm
    · intro s
      calc
        ‖g s‖ ≤ ‖H (P s)‖ + ‖M * s‖ := norm_sub_le _ _
        _ ≤ A + ‖M * s‖ := add_le_add (hA _ (P s).property) le_rfl
        _ = A + |M| * ‖s‖ := by rw [norm_mul, Real.norm_eq_abs]
    · intro s t hst
      change (H (P s) - M * s) + M * s ≤ (H (P t) - M * t) + M * t
      rw [sub_add_cancel, sub_add_cancel]
      exact hmono (P s).property (P t).property (monotone_projIcc hab hst)
  · refine ⟨(fun s ↦ -(M * s)), 0,
      (continuous_const.mul continuous_id).neg, ?_, ?_, ?_⟩
    · intro s hs
      exact (hab (hs.1.trans hs.2)).elim
    · intro s
      simp only [norm_neg, norm_mul, Real.norm_eq_abs, zero_add, le_rfl]
    · intro s t _
      change -(M * s) + M * s ≤ -(M * t) + M * t
      simp only [neg_add_cancel, le_rfl]

/-- Continuity and a lower one-sided slope bound on a bounded scalar interval
give a weak solution between ordered zero-boundary barriers taking values there.
The reaction is unrestricted outside the interval, and no global growth bound
is assumed. Compactness bounds its shifted extension, whose solution has an
`L²` nonlinear source and satisfies the original equation against every `H¹₀` test.
The endpoints need not be ordered: the barrier hypotheses already handle an
empty interval, including domains of zero measure. -/
theorem exists_weak_solution_between_barriers_of_continuousOn_of_monotone_shift
    (hΩ : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (f : ℝ → ℝ) {left right M : ℝ}
    (hf : ContinuousOn f (Icc left right))
    (hmono : MonotoneOn (fun s ↦ f s + M * s) (Icc left right))
    (lower upper : H¹₀(Ω))
    (hlr : ∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM upper x)
    (hleft : ∀ᵐ x ∂μ, left ≤ baseCoordCLM lower x)
    (hright : ∀ᵐ x ∂μ, baseCoordCLM upper x ≤ right)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) lower v ≤
      ∫ x, f (baseCoordCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, f (baseCoordCLM upper x) * baseCoordCLM v x ∂μ) ≤
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ baseCoordCLM upper x) ∧
      MemLp (fun x ↦ f (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω),
        fullDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u v =
        ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  obtain ⟨g, A, hg, hfg, hgrowth, hgmono⟩ :=
    exists_linear_growth_extension_of_monotoneOn_shift f hf hmono
  have hlo : (fun x ↦ f (baseCoordCLM lower x)) =ᵐ[μ]
      fun x ↦ g (baseCoordCLM lower x) := by
    filter_upwards [hleft, hlr, hright] with x hx hxy hy
    exact hfg ⟨hx, hxy.trans hy⟩
  have hup : (fun x ↦ f (baseCoordCLM upper x)) =ᵐ[μ]
      fun x ↦ g (baseCoordCLM upper x) := by
    filter_upwards [hleft, hlr, hright] with x hx hxy hy
    exact hfg ⟨hx.trans hxy, hy⟩
  obtain ⟨u, hlu, huu, hmem, heq⟩ :=
    exists_weak_solution_between_barriers_of_continuous_of_monotone_shift hΩ hΩbounded
      a b c hA hbc g hg hgrowth hgmono lower upper hlr
      (fun v hv ↦ (hlower v hv).trans_eq
        (integral_congr_ae (hlo.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx)))
      (fun v hv ↦ (integral_congr_ae
        (hup.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx)).symm.trans_le
          (hupper v hv))
  have hu : (fun x ↦ f (baseCoordCLM u x)) =ᵐ[μ]
      fun x ↦ g (baseCoordCLM u x) := by
    filter_upwards [hleft, hlu, huu, hright] with x hx hl hu hy
    exact hfg ⟨hx.trans hl, hu.trans hy⟩
  refine ⟨u, hlu, huu, MemLp.ae_eq hu.symm hmem, fun v ↦ ?_⟩
  exact (heq v).trans (integral_congr_ae
    (hu.symm.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx))

/-- If the reaction is Lipschitz only on a scalar interval containing both
weak barriers, a solution still exists between them. Values of the reaction
outside that interval are unrestricted. Both barriers belong to `H¹₀`;
their pointwise bounds are almost everywhere for the domain measure. -/
theorem exists_weak_solution_between_barriers_of_lipschitzOn
    (hΩ : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (f : ℝ → ℝ) {K : ℝ≥0} {left right : ℝ}
    (hf : LipschitzOnWith K f (Icc left right))
    (lower upper : H¹₀(Ω))
    (hlr : ∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM upper x)
    (hleft : ∀ᵐ x ∂μ, left ≤ baseCoordCLM lower x)
    (hright : ∀ᵐ x ∂μ, baseCoordCLM upper x ≤ right)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) lower v ≤
      ∫ x, f (baseCoordCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, f (baseCoordCLM upper x) * baseCoordCLM v x ∂μ) ≤
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, baseCoordCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ baseCoordCLM upper x) ∧
      MemLp (fun x ↦ f (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω),
        fullDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u v =
        ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  have hmono : MonotoneOn (fun s ↦ f s + (K : ℝ) * s) (Icc left right) := by
    intro s hs t ht hst
    have h := hf.le_add_mul hs ht
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] at h
    nlinarith
  exact exists_weak_solution_between_barriers_of_continuousOn_of_monotone_shift
    hΩ hΩbounded a b c hA hbc f hf.continuousOn hmono lower upper
    hlr hleft hright hlower hupper

end PDE.Elliptic.Semilinear
