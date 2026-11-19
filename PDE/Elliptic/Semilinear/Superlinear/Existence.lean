/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Superlinear.Potential
public import PDE.Elliptic.Semilinear.DirichletNemytskii
import PDE.Analysis.Variational.IntegralPotential.MountainPass
import PDE.Analysis.Variational.CoerciveHilbertSpace
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Subcritical.ZeroTrace
import PDE.Spaces.Sobolev.Variational.Spaces.SupportedFunctions

/-!
# Nonzero superlinear Dirichlet solutions

The scalar hypotheses and the geometry of a nonempty bounded open domain produce
a nonzero `H¹₀` solution of `-Δu = f(u)`. The proof uses the equivalent
Dirichlet Hilbert norm, compact subcritical inclusion, and a supported smooth bump.
All analytic and mountain-pass hypotheses are derived from these data.

For `n > 2` the exponent satisfies the usual strict critical bound. In dimensions
one and two every finite real exponent greater than one is allowed. No smoothness
of the boundary is needed.

## Reference

Evans, *Partial Differential Equations*, §8.5.2, Theorem 3. The `C¹` scalar
assumption and bounded open domain suffice for the weak-solution conclusion;
nonemptiness is explicit because the solution is required to be nonzero.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Variational
open scoped ENNReal
open PDE.Analysis (primitive primitive_zero hasDerivAt_primitive)

namespace PDE.Elliptic.Semilinear.Superlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : ℝ → ℝ} {p C γ a A : ℝ}

private theorem potentialExponent_subcritical
    (hsub : 2 < n → p < ((n : ℝ) + 2) / ((n : ℝ) - 2)) :
    2 < n → p + 1 < 2 * (n : ℝ) / ((n : ℝ) - 2) := by
  intro hn
  have hnR : (2 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 2 := by linarith
  have hb := (lt_div_iff₀ hden).mp (hsub hn)
  apply (lt_div_iff₀ hden).mpr
  nlinarith

namespace Hypotheses

/-- Superlinear subcritical scalar data yield a nonzero weak solution on
every nonempty bounded open domain of positive dimension. The nonlinear pairing
is integrable against every `H¹₀` test, even when `f(u)` is not in `L²`. -/
theorem exists_nonzero_weak_solution
    (h : Hypotheses f p C γ a A)
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty)
    (hsub : 2 < n → p < ((n : ℝ) + 2) / ((n : ℝ) - 2)) :
    ∃ u : H¹₀(Ω), u ≠ 0 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ -f z) 0 u := by
  let : IsFiniteMeasure (domainMeasure n Ω) :=
    ⟨by simpa [domainMeasure] using hbounded.measure_lt_top (μ := volume)⟩
  have hp2 : 2 < p + 1 := by linarith [h.one_lt]
  have hp0 : 0 ≤ p + 1 := by linarith
  let q := ENNReal.ofReal (p + 1)
  have hqreal : q.toReal = p + 1 := ENNReal.toReal_ofReal hp0
  have hq : 1 < q := ENNReal.one_lt_ofReal.mpr (by linarith)
  have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  let r := ENNReal.conjExponent q
  have hcrit := potentialExponent_subcritical hsub
  let B := dirichletForm (n := n) (Ω := Ω)
  have hB : IsCoercive B := dirichletForm_isCoercive hn hbounded
  have hsymm : ∀ u v, B u v = B v u := dirichletForm_symm
  let H := WithCoerciveForm B hB hsymm
  let e : H ≃L[ℝ] H¹₀(Ω) :=
    WithCoerciveForm.continuousLinearEquiv B hB hsymm
  let E : H¹₀(Ω) →L[ℝ] Lp ℝ q (domainMeasure n Ω) :=
    h10LpEmbedding hn hΩ.measurableSet hp2.le (fun hn ↦ (hcrit hn).le)
  let J : H →L[ℝ] Lp ℝ q (domainMeasure n Ω) := E.comp e.toContinuousLinearMap
  have hJcompact : IsCompactOperator J :=
    (h10LpEmbedding_isCompactOperator hn hΩ.measurableSet hbounded hp2.le hcrit).comp_clm
      e.toContinuousLinearMap
  have hJae (u : H) : (J u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] baseCoordCLM (e u) :=
    h10LpEmbedding_ae hn hΩ.measurableSet hp2.le (fun hn ↦ (hcrit hn).le) (e u)
  obtain ⟨φ, hφ⟩ := exists_testFunction_baseCoord_ne_zero hΩ hne
  have hnonzero : ∃ w : H, J w ≠ 0 := by
    refine ⟨e.symm (testFunctionToH10 φ), fun hz ↦ hφ (Lp.ext ?_)⟩
    have heq := (hJae (e.symm (testFunctionToH10 φ))).symm
    rwa [e.apply_symm_apply, hz] at heq
  have hd := hasDerivAt_primitive h.contDiff.continuous
  have hupper : ∀ z, |primitive f z| ≤ A * |z| ^ q.toReal := by
    simpa only [hqreal] using h.primitive_upper
  have hlower : ∀ z, a * |z| ^ q.toReal ≤ primitive f z := by
    intro z
    simpa only [hqreal, abs_of_nonneg (h.primitive_nonneg z)] using h.primitive_lower z
  have hg : ∀ z, |f z| ≤ C * (1 + |z| ^ (q.toReal - 1)) := by
    simpa only [hqreal, add_sub_cancel_right] using h.reaction_bound
  have hdf : ∀ z, ‖deriv f z‖ ≤ C * (1 + ‖z‖ ^ (q.toReal - 2)) := by
    have hexp : q.toReal - 2 = p - 1 := by rw [hqreal]; ring
    simpa only [Real.norm_eq_abs, hexp] using h.deriv_bound
  obtain ⟨u, hu, hcritical⟩ :=
    IntegralPotential.exists_nonzero_criticalPoint (q := r) J hJcompact
      (by simpa only [hqreal] using hp2) hd h.contDiff.continuous (primitive_zero _)
      h.lower_pos h.upper_pos.le hupper hlower hg h.hasDerivAt hdf
      h.gamma_pos.le h.gamma_lt_half h.primitive_le hnonzero
  have hG : ∀ z, |primitive f z| ≤ 0 + A * |z| ^ q.toReal := by
    simpa only [zero_add] using hupper
  have hprod (v : H¹₀(Ω)) : (fun x ↦ f (J u x) * J (e.symm v) x) =ᵐ[domainMeasure n Ω]
      fun x ↦ f (baseCoordCLM (e u) x) * baseCoordCLM v x := by
    filter_upwards [hJae u, hJae (e.symm v)] with x hx hv
    rw [hx, hv, e.apply_symm_apply]
  have hpair (v : H¹₀(Ω)) :
      Integrable (fun x ↦ f (baseCoordCLM (e u) x) * baseCoordCLM v x)
        (domainMeasure n Ω) :=
    ((memLp_comp_of_conjugate_growth (q := r) h.contDiff.continuous hg
      (J u)).integrable_mul (Lp.memLp (J (e.symm v)))).congr (hprod v)
  have heq (v : H¹₀(Ω)) :
      dirichletForm (e u) v =
        ∫ x, f (baseCoordCLM (e u) x) * baseCoordCLM v x ∂domainMeasure n Ω := by
    have hc := IntegralPotential.inner_eq_integral_of_gradient_eq_zero (q := r)
      J hq hqtop hd h.contDiff.continuous hG hg hcritical (e.symm v)
    have hinner : inner ℝ u (e.symm v) = dirichletForm (e u) v := by
      change B (e u) (e (e.symm v)) = _
      rw [e.apply_symm_apply]
    rw [hinner] at hc
    exact hc.trans (integral_congr_ae (hprod v))
  refine ⟨e u, fun hz ↦ hu (e.injective (by simpa using hz)),
    (isDirichletSemilinearWeakSolution_neg_zero_iff (fun _ ↦ f) (e u)).mpr ?_⟩
  intro v
  refine ⟨hpair v, ?_⟩
  rw [← dirichletForm_eq_integral_gradient]
  exact heq v

/-- In dimensions above two, the literal strict critical-exponent hypothesis
gives the nonzero solution in Evans's theorem. -/
theorem exists_nonzero_weak_solution_of_subcritical
    (h : Hypotheses f p C γ a A)
    (hn : 2 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (hsub : p < ((n : ℝ) + 2) / ((n : ℝ) - 2)) :
    ∃ u : H¹₀(Ω), u ≠ 0 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ -f z) 0 u :=
  h.exists_nonzero_weak_solution (lt_trans (by decide : 0 < 2) hn)
    hΩ hbounded hne (fun _ ↦ hsub)

/-- The low-dimensional extension: for `n = 1` or `n = 2`, every finite real
exponent greater than one is allowed. No critical-exponent division is used. -/
theorem exists_nonzero_weak_solution_lowDimension
    (h : Hypotheses f p C γ a A)
    (hn : 0 < n) (hn2 : n ≤ 2)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    ∃ u : H¹₀(Ω), u ≠ 0 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ -f z) 0 u :=
  h.exists_nonzero_weak_solution hn hΩ hbounded hne
    (fun hn3 ↦ (not_lt_of_ge hn2 hn3).elim)

/-- The constructed nonzero solution satisfies the literal integral-gradient
equation against every test, with both integrands integrable. -/
theorem exists_nonzero_integral_solution
    (h : Hypotheses f p C γ a A)
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty)
    (hsub : 2 < n → p < ((n : ℝ) + 2) / ((n : ℝ) - 2)) :
    ∃ u : H¹₀(Ω), u ≠ 0 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ -f z) 0 u ∧
      ∀ v : H¹₀(Ω),
        Integrable (fun x ↦ f (baseCoordCLM u x) * baseCoordCLM v x)
          (domainMeasure n Ω) ∧
        Integrable (fun x ↦ inner ℝ (∇ (u : H¹(Ω)) x) (∇ (v : H¹(Ω)) x))
          (domainMeasure n Ω) ∧
        (∫ x, inner ℝ (∇ (u : H¹(Ω)) x) (∇ (v : H¹(Ω)) x) ∂domainMeasure n Ω) =
          ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂domainMeasure n Ω := by
  obtain ⟨u, hnonzero, hu⟩ := h.exists_nonzero_weak_solution hn hΩ hbounded hne hsub
  refine ⟨u, hnonzero, hu, fun v ↦ ?_⟩
  have hv := (isDirichletSemilinearWeakSolution_neg_zero_iff (fun _ ↦ f) u).mp hu v
  exact ⟨hv.1, integrable_inner_gradient u v, hv.2⟩

end Hypotheses

end PDE.Elliptic.Semilinear.Superlinear
