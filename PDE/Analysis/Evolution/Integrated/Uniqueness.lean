/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Core.Gronwall
import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# Uniqueness of integrated weak solutions

Two integrated weak solutions `u₁, u₂ ∈ L²(a, b; V)` of `u' + B(t) u = ℓ` with the same
initial datum `uInit ∈ H` coincide as `L²` classes, provided the form satisfies a Gårding
lower bound `θ ‖w‖_V² ≤ B(t)(w, w) + γ ‖i w‖_H²` with `θ ≥ 0`. The difference `w = u₁ - u₂`
is a homogeneous integrated weak solution with zero initial trace
(`IsGelfandIntegratedWeakSolution.sub_same_data`); the Lions–Magenes theorem gives it an
`H`-continuous representative with `w(a) = 0` and the energy identity
`‖w(t)‖_H² = 2 ∫ₐᵗ g(w)`, where `g = -B(·) w` is the weak derivative. The Gårding bound
turns this into `e(t) ≤ 2γ ∫ₐᵗ e(s) ds` for `e(t) = ‖w(t)‖_H²`, and the scalar integral
Grönwall inequality forces `e ≡ 0`. Hence `i(w t) = 0` for a.e. `t`, and injectivity of
the inclusion gives `w = 0` in `L²(a, b; V)`.

Evans proves uniqueness the same way (§7.1.2, Theorem 4): he tests the equation with the
solution, computes `d/dt ½ ‖u‖²` by §5.9.2, Theorem 3, and applies Grönwall's inequality.
Here the Gårding bound is a hypothesis; for a uniformly parabolic operator with bounded
coefficients it is the inequality `β ‖u‖²_{H¹₀} ≤ B[u, u; t] + γ ‖u‖²_{L²}` of Evans
§7.1.2, (22).

## Main results

* `IsGelfandIntegratedWeakSolution.unique_of_garding`: uniqueness under the Gårding bound
  (`0 ≤ θ`, any real `γ`).
* `IsGelfandIntegratedWeakSolution.unique`: the special case `γ = 0`, `θ = 0`, i.e.
  pointwise nonnegativity of `B(t)`.
* `IsGelfandIntegratedWeakSolution.iff_eq_of_solution`: given one solution `uRef`, a
  trajectory is a solution with the same data iff it equals `uRef`; this is how constructed
  solutions are identified.

## Implementation notes

Only `θ ≥ 0` is required, not `θ > 0`: the energy-space term `θ ∫ ‖w‖_V²` is simply
dropped from the inequality. The Borel-measurability instances on `V` and `V*` and the
completeness of `H` are inherited from the Lions–Magenes regularity theorem in
`PDE.Analysis.Evolution.Integrated.Regularity`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 4 and its proof, and the inequality (22) in
  the proof of Theorem 2. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Uniqueness of integrated weak solutions under a
Gårding lower bound.

The hypothesis

`theta ‖v‖_V² ≤ B(t)(v,v) + gamma ‖v‖_H²`

is the abstract form of the estimate (22) that Evans uses for parabolic operators
with lower-order terms (§7.1.2). For the difference `w` of two solutions, the
Lions–Magenes identity yields

`e(t) ≤ 2 gamma ∫ₐᵗ e(s) ds`,

where `e(t) = ‖w(t)‖_H²`.  The scalar integral Grönwall lemma in
`PDE.Analysis.Evolution` then forces `e = 0`. This avoids the stronger,
generally false requirement that the unshifted form itself be nonnegative. -/
theorem IsGelfandIntegratedWeakSolution.unique_of_garding
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    {theta gamma : ℝ} (htheta : 0 ≤ theta)
    (hGarding : ∀ t ∈ Set.Icc a b, ∀ v : V,
      theta * ‖v‖ ^ 2 ≤
        B t v v + gamma * ‖T.inclusion v‖ ^ 2)
    (h₁ : IsGelfandIntegratedWeakSolution T B ell u₁ uInit)
    (h₂ : IsGelfandIntegratedWeakSolution T B ell u₂ uInit)
    (hab : a < b) :
    u₁ = u₂ := by
  have hw : IsGelfandIntegratedWeakSolution T B 0 (u₁ - u₂) 0 :=
    h₁.sub_same_data hBmeas MB hBbound h₂
  obtain ⟨g, E, -, hEa, hgres⟩ :=
    hw.exists_continuousPivotEvolutionOn_initial hBmeas MB hBbound continuousOn_const hab
  have hsub {t : ℝ} (ht : t ∈ Icc a b) : Icc a t ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Icc_subset_Icc_right ht.2
  have hEae {t : ℝ} (ht : t ∈ Icc a b) : E.representative =ᵐ[volume.restrict (Ioc a t)]
      fun r ↦ T.inclusion ((u₁ - u₂) r) :=
    E.ae_eq_inclusion.filter_mono
      (ae_mono (Measure.restrict_mono_set _ (Ioc_subset_Icc_self.trans (hsub ht))))
  have heContinuous : ContinuousOn (fun t ↦ ‖E.representative t‖ ^ 2) (Icc a b) := by
    rw [← uIcc_of_le hab.le]
    exact (E.continuousOn.norm.pow 2).congr fun _ _ ↦ rfl
  have heIntegral : ∀ t ∈ Icc a b, ‖E.representative t‖ ^ 2 ≤
      2 * gamma * ∫ s in a..t, ‖E.representative s‖ ^ 2 := by
    intro t ht
    have hmeasure : volume.restrict (Ioc a t) ≤ volume.restrict (Ioc a b) :=
      Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)
    have hpairIntegral : ∫ r in Ioc a t, g r ((u₁ - u₂) r) ≤
        gamma * ∫ r in Ioc a t, ‖E.representative r‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_mono_ae ((integrable_dual_pairing g _).mono_measure hmeasure)
        (((heContinuous.mono (Icc_subset_Icc_right ht.2)).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self).const_mul gamma) ?_
      filter_upwards [hgres.filter_mono (ae_mono hmeasure), hEae ht,
        ae_restrict_mem measurableSet_Ioc] with r hgr hEr hr
      rw [hgr, hEr, sub_apply]
      change (0 : ℝ) - _ ≤ _
      linarith [hGarding r ⟨hr.1.le, hr.2.trans ht.2⟩ ((u₁ - u₂) r),
        mul_nonneg htheta (sq_nonneg ‖(u₁ - u₂) r‖)]
    have henergy := E.energyIdentity a t left_mem_uIcc (hsub ht ⟨ht.1, le_rfl⟩)
    rw [hEa, norm_zero, intervalIntegral.integral_of_le ht.1] at henergy
    rw [intervalIntegral.integral_of_le ht.1, mul_assoc]
    linarith
  have heZero := eq_zero_on_of_nonneg_le_mul_intervalIntegral hab.le heContinuous
    (fun t _ ↦ sq_nonneg _) heIntegral
  refine sub_eq_zero.mp (Lp.ext ?_)
  filter_upwards [hEae ⟨hab.le, le_rfl⟩, ae_restrict_mem measurableSet_Ioc,
    Lp.coeFn_zero V 2 _] with t hEt ht hzero
  rw [hzero]
  apply T.injective
  rw [← hEt, Pi.zero_apply, map_zero]
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (heZero t ⟨ht.1.le, ht.2⟩))

/-- Uniqueness of integrated weak solutions when the
time-dependent form is nonnegative. This is the energy-method uniqueness
argument: the difference of two solutions has zero forcing and zero initial
trace.  It is the zero-shift specialization of
`IsGelfandIntegratedWeakSolution.unique_of_garding`. -/
theorem IsGelfandIntegratedWeakSolution.unique
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u₁ u₂ : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hBnonneg : ∀ t ∈ Set.Icc a b, ∀ w : V, 0 ≤ B t w w)
    (h₁ : IsGelfandIntegratedWeakSolution T B ell u₁ uInit)
    (h₂ : IsGelfandIntegratedWeakSolution T B ell u₂ uInit)
    (hab : a < b) :
    u₁ = u₂ := by
  exact h₁.unique_of_garding hBmeas MB hBbound (theta := 0) (gamma := 0) le_rfl
    (fun t ht w ↦ by simpa using hBnonneg t ht w) h₂ hab

/--
Reference-solution form of uniqueness.

Once one integrated weak solution has been constructed, the same hypotheses
turn the solution predicate into the equality predicate.  To prove another
candidate is the same solution, it suffices to prove it satisfies the same
integrated weak formulation with the same initial trace.
-/
theorem IsGelfandIntegratedWeakSolution.iff_eq_of_solution
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u uRef : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hBnonneg : ∀ t ∈ Set.Icc a b, ∀ w : V, 0 ≤ B t w w)
    (href : IsGelfandIntegratedWeakSolution T B ell uRef uInit)
    (hab : a < b) :
    IsGelfandIntegratedWeakSolution T B ell u uInit ↔ u = uRef := by
  exact ⟨fun hu ↦ hu.unique hBmeas MB hBbound hBnonneg href hab, fun h ↦ h ▸ href⟩

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
