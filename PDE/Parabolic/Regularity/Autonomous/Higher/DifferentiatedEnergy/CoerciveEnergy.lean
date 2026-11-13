/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.Integrated.EnergyBounds
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Coercive energy bounds for differentiated parabolic equations

The abstract energy estimate for a coercive autonomous evolution equation `u' + A u = ℓ` in a
Gelfand triple `V ⊂ H ⊂ V*`. If `θ ‖w‖²_V ≤ ⟪A w, w⟫` for all `w ∈ V`, then a weak solution
with `u ∈ L²(t₀, t₁; V)` and `ℓ ∈ L²(t₀, t₁; V*)` has a continuous `H`-valued representative
satisfying, for every `t ∈ [t₀, t₁]`,

`½ ‖u(t)‖²_H + (θ/2) ∫_{t₀}^{t} ‖u‖²_V ≤ ½ ‖u(t₀)‖²_H + (1/(2θ)) ∫_{t₀}^{t} ‖ℓ‖²_{V*}`.

This is the usual computation: pair the equation with `u`, use `d/dt ‖u‖²_H = 2⟪u', u⟫` for the
continuous representative (the Lions-Magenes calculus lemma; Evans proves it for
`H¹₀ ⊂ L² ⊂ H⁻¹` in §5.9.2, Theorem 3), apply coercivity to `⟪A u, u⟫`, and split `⟪ℓ, u⟫` by
Young's inequality with weight `θ`. In the parabolic regularity argument the equation is the one
satisfied by `uₜ`, so the estimate yields `uₜ ∈ L^∞(t₀, t₁; L²(Ω)) ∩ L²(t₀, t₁; H¹₀(Ω))`, which
is part of Evans's improved regularity theorem (§7.1.3, Theorem 5(ii)).

## Main results

* `exists_continuous_pivot_with_coercive_energy`: the weak time derivative, the continuous
  pivot representative, and the energy inequality above at every time of the closed interval.
* `norm_representative_le_of_coercive_energy`: dropping the dissipation term gives the pointwise
  bound `‖u(t)‖_H ≤ √(‖u(t₀)‖² + ‖ℓ‖²_{L²(V*)} / θ)` on `[t₀, t₁]`.
* `integral_norm_sq_le_of_coercive_energy`: dropping the endpoint term gives
  `∫ ‖u‖²_V ≤ (‖u(t₀)‖² + ‖ℓ‖²_{L²(V*)} / θ) / θ`.
* `exists_continuous_pivot_with_coercive_bounds`: the three conclusions tied to one
  representative.

## Implementation notes

`norm_le_sqrt_of_energy_inequality` and `state_integral_le_energy_budget_div` are real-number
inequalities with no analytic content: they discard a nonnegative term from the energy
inequality. The continuous representative comes from
`IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial_L2`; the Borel
structures on `V` and `V*` used there are chosen inside the proof and are not hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3 (More calculus), pp. 303-304; §7.1.2,
  Theorem 2 (Energy estimates), pp. 376-378; §7.1.3, Theorem 5 (Improved regularity), p. 382,
  and step 4 of its proof, (50)-(51), p. 384.
  <https://doi.org/10.1090/gsm/019>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*, Vol. I,
  Springer, 1972, Chapter 1 (Hilbert Theory of Trace and Interpolation Spaces), for the
  continuity of `u` in `H` when `u ∈ L²(V)` and `u' ∈ L²(V*)`.
  <https://doi.org/10.1007/978-3-642-65161-8_1>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Parabolic.DivergenceFormHeat
namespace AutonomousRegularity
namespace CoerciveEnergy

open PDE.Analysis.Evolution
open scoped ENNReal InnerProductSpace

attribute [local instance 101] secondCountableTopologyEither_of_left

/-- The squared `L²` norm on an initial subinterval is bounded by the squared
norm on the whole time interval. -/
theorem interval_integral_norm_sq_le_norm_sq
    {E : Type*} [NormedAddCommGroup E] {a b t : ℝ}
    (f : Lp E 2 (volume.restrict (Set.Ioc a b)))
    (ht : t ∈ Set.Icc a b) :
    (∫ s in a..t, ‖(f : ℝ → E) s‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le ht.1,
    MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  apply integral_mono_measure
    ((volume : Measure ℝ).restrict_mono_set
      (Set.Ioc_subset_Ioc_right ht.2))
  · exact Filter.Eventually.of_forall fun s ↦
      sq_nonneg ‖(f : ℝ → E) s‖
  · exact (MeasureTheory.Lp.memLp f).integrable_norm_pow (by norm_num)

/-- Dropping the nonnegative dissipation term from a coercive energy
inequality gives the corresponding pointwise state bound. -/
theorem norm_le_sqrt_of_energy_inequality
    (coercivityConstant stateNorm initialNorm stateIntegral
      forcingIntegral forcingNorm : ℝ)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hStateNorm : 0 ≤ stateNorm) (hStateIntegral : 0 ≤ stateIntegral)
    (hforcing : forcingIntegral ≤ forcingNorm ^ 2)
    (henergy :
      (1 / 2 : ℝ) * stateNorm ^ 2 +
          (coercivityConstant / 2) * stateIntegral ≤
        (1 / 2 : ℝ) * initialNorm ^ 2 +
          (1 / (2 * coercivityConstant)) * forcingIntegral) :
    stateNorm ≤
      Real.sqrt
        (initialNorm ^ 2 + (1 / coercivityConstant) * forcingNorm ^ 2) := by
  have hforce :
      (1 / (2 * coercivityConstant)) * forcingIntegral ≤
        (1 / (2 * coercivityConstant)) * forcingNorm ^ 2 :=
    mul_le_mul_of_nonneg_left hforcing (by positivity)
  have hdrop :
      (1 / 2 : ℝ) * stateNorm ^ 2 ≤
        (1 / 2 : ℝ) * initialNorm ^ 2 +
          (1 / (2 * coercivityConstant)) * forcingNorm ^ 2 := by
    calc
      (1 / 2 : ℝ) * stateNorm ^ 2 ≤
          (1 / 2 : ℝ) * stateNorm ^ 2 +
            (coercivityConstant / 2) * stateIntegral := by
        exact le_add_of_nonneg_right
          (mul_nonneg (by positivity) hStateIntegral)
      _ ≤ (1 / 2 : ℝ) * initialNorm ^ 2 +
            (1 / (2 * coercivityConstant)) * forcingIntegral := henergy
      _ ≤ (1 / 2 : ℝ) * initialNorm ^ 2 +
            (1 / (2 * coercivityConstant)) * forcingNorm ^ 2 :=
        add_le_add_right hforce _
  have hsq :
      stateNorm ^ 2 ≤
        initialNorm ^ 2 + (1 / coercivityConstant) * forcingNorm ^ 2 := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hdrop (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp [ne_of_gt hCoercivityConstant] at hscaled
    rw [show
      initialNorm ^ 2 + 1 / coercivityConstant * forcingNorm ^ 2 =
        (initialNorm ^ 2 * coercivityConstant + forcingNorm ^ 2) /
          coercivityConstant by
          field_simp [ne_of_gt hCoercivityConstant]]
    exact (le_div_iff₀ hCoercivityConstant).2 hscaled
  apply (sq_le_sq₀ hStateNorm (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity :
    0 ≤ initialNorm ^ 2 + (1 / coercivityConstant) * forcingNorm ^ 2)]
  exact hsq

/-- Dropping the nonnegative endpoint energy gives the integrated
dissipation bound associated with a coercive energy inequality. -/
theorem state_integral_le_energy_budget_div
    (coercivityConstant endpointNorm initialNorm stateIntegral
      forcingIntegral forcingNorm : ℝ)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hforcing : forcingIntegral ≤ forcingNorm ^ 2)
    (henergy :
      (1 / 2 : ℝ) * endpointNorm ^ 2 +
          (coercivityConstant / 2) * stateIntegral ≤
        (1 / 2 : ℝ) * initialNorm ^ 2 +
          (1 / (2 * coercivityConstant)) * forcingIntegral) :
    stateIntegral ≤
      (initialNorm ^ 2 + (1 / coercivityConstant) * forcingNorm ^ 2) /
        coercivityConstant := by
  have hforce :
      (1 / (2 * coercivityConstant)) * forcingIntegral ≤
        (1 / (2 * coercivityConstant)) * forcingNorm ^ 2 :=
    mul_le_mul_of_nonneg_left hforcing (by positivity)
  have hdrop :
      (coercivityConstant / 2) * stateIntegral ≤
        (1 / 2 : ℝ) * initialNorm ^ 2 +
          (1 / (2 * coercivityConstant)) * forcingNorm ^ 2 := by
    calc
      (coercivityConstant / 2) * stateIntegral ≤
          (1 / 2 : ℝ) * endpointNorm ^ 2 +
            (coercivityConstant / 2) * stateIntegral := by
        exact le_add_of_nonneg_left
          (mul_nonneg (by positivity) (sq_nonneg _))
      _ ≤ (1 / 2 : ℝ) * initialNorm ^ 2 +
            (1 / (2 * coercivityConstant)) * forcingIntegral := henergy
      _ ≤ (1 / 2 : ℝ) * initialNorm ^ 2 +
            (1 / (2 * coercivityConstant)) * forcingNorm ^ 2 :=
        add_le_add_right hforce _
  apply (le_div_iff₀ hCoercivityConstant).2
  have hscaled :=
    mul_le_mul_of_nonneg_left hdrop (show (0 : ℝ) ≤ 2 by norm_num)
  field_simp [ne_of_gt hCoercivityConstant] at hscaled
  rw [show
    initialNorm ^ 2 + 1 / coercivityConstant * forcingNorm ^ 2 =
      (initialNorm ^ 2 * coercivityConstant + forcingNorm ^ 2) /
        coercivityConstant by
        field_simp [ne_of_gt hCoercivityConstant]]
  apply (le_div_iff₀ hCoercivityConstant).2
  nlinarith [hscaled]

/-- A weak solution for a coercive equation has a continuous pivot
representative satisfying the standard energy inequality. -/
theorem exists_continuous_pivot_with_coercive_energy
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (T : GelfandTriple (V := V) (H := H))
    (Aop : V →L[ℝ] StrongDual ℝ V)
    (ellDot : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (ut : Lp V 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : H)
    (hutEvolution :
      IsGelfandIntegratedWeakSolution T (fun _ ↦ Aop)
        (fun t ↦ ellDot t) ut utInit)
    (coercivityConstant : ℝ)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hcoercive :
      ∀ w : V, coercivityConstant * ‖w‖ ^ 2 ≤ Aop w w) :
    ∃ (utt : Lp (StrongDual ℝ V) 2
          (volume.restrict (Set.Ioc t₀ t₁)))
      (Eut : ContinuousPivotEvolutionOn T
        (fun t ↦ (ut : ℝ → V) t) (fun t ↦ utt t) t₀ t₁),
      HasGelfandWeakTimeDerivativeOn T ut utt ∧
      ∀ t ∈ Set.Icc t₀ t₁,
        (1 / 2 : ℝ) * ‖Eut.representative t‖ ^ 2 +
            (coercivityConstant / 2) *
              ∫ s in t₀..t, ‖(ut : ℝ → V) s‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖utInit‖ ^ 2 +
            (1 / (2 * coercivityConstant)) *
              ∫ s in t₀..t,
                ‖(ellDot : ℝ → StrongDual ℝ V) s‖ ^ 2 := by
  -- Endpoint regularity uses the Borel structures of the two norm topologies.
  borelize V (StrongDual ℝ V)
  have hAmeas : AEStronglyMeasurable (fun _ : ℝ ↦ Aop)
      (volume.restrict (Set.Ioc t₀ t₁)) :=
    aestronglyMeasurable_const
  have hAbound : ∀ᵐ _t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ‖Aop‖ ≤ ‖Aop‖ :=
    Filter.Eventually.of_forall fun _ ↦ le_rfl
  obtain ⟨utt, Eut, huttWeak, hEutInitial, huttResidual⟩ :=
    IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial_L2
      (fun v ↦ hAmeas.apply_continuousLinearMap v) ‖Aop‖ hAbound hutEvolution ht
  refine ⟨utt, Eut, huttWeak, ?_⟩
  exact Eut.coercive_energy_bound_L2 hEutInitial huttResidual
    hCoercivityConstant (fun _ _ w ↦ hcoercive w) ht.le

/--
The continuous pivot representative satisfies the pointwise estimate obtained
by dropping the nonnegative dissipation term from a coercive energy inequality.

Since the energy inequality holds at every time of the closed interval, so
does the bound: it holds on all of `Icc t₀ t₁`, not only almost everywhere.
-/
theorem norm_representative_le_of_coercive_energy
    {V H F : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup H] [NormedAddCommGroup F]
    {t₀ t₁ coercivityConstant : ℝ}
    (ut : Lp V 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (ellDot : Lp F 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : H)
    (utRep : ℝ → H)
    (hCoercivityConstant : 0 < coercivityConstant)
    (henergy :
      ∀ t ∈ Set.Icc t₀ t₁,
        (1 / 2 : ℝ) * ‖utRep t‖ ^ 2 +
            (coercivityConstant / 2) * ∫ s in t₀..t,
              ‖(ut : ℝ → V) s‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖utInit‖ ^ 2 +
            (1 / (2 * coercivityConstant)) *
              ∫ s in t₀..t,
                ‖(ellDot : ℝ → F) s‖ ^ 2) :
    ∀ t ∈ Set.Icc t₀ t₁,
      ‖utRep t‖ ≤
        Real.sqrt
          (‖utInit‖ ^ 2 + (1 / coercivityConstant) * ‖ellDot‖ ^ 2) := by
  let energyBudget :=
    ‖utInit‖ ^ 2 + (1 / coercivityConstant) * ‖ellDot‖ ^ 2
  intro t htt
  have hprefix :
      (∫ s in t₀..t,
        ‖(ellDot : ℝ → F) s‖ ^ 2) ≤ ‖ellDot‖ ^ 2 :=
    interval_integral_norm_sq_le_norm_sq ellDot htt
  have hutIntegralNonneg :
      0 ≤ ∫ s in t₀..t, ‖(ut : ℝ → V) s‖ ^ 2 :=
    intervalIntegral.integral_nonneg htt.1
      (fun s _ ↦ sq_nonneg ‖(ut : ℝ → V) s‖)
  simpa only [energyBudget] using
    norm_le_sqrt_of_energy_inequality
      coercivityConstant ‖utRep t‖ ‖utInit‖
      (∫ s in t₀..t, ‖(ut : ℝ → V) s‖ ^ 2)
      (∫ s in t₀..t, ‖(ellDot : ℝ → F) s‖ ^ 2)
      ‖ellDot‖ hCoercivityConstant (norm_nonneg _) hutIntegralNonneg
      hprefix (henergy t htt)

/--
The integrated energy norm is bounded by the coercive budget divided by the
coercivity constant. This is the dissipation estimate at the terminal time.
-/
theorem integral_norm_sq_le_of_coercive_energy
    {V H F : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup H] [NormedAddCommGroup F]
    {t₀ t₁ coercivityConstant : ℝ} (ht : t₀ < t₁)
    (ut : Lp V 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (ellDot : Lp F 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : H)
    (utRep : ℝ → H)
    (hCoercivityConstant : 0 < coercivityConstant)
    (henergy :
      ∀ t ∈ Set.Icc t₀ t₁,
        (1 / 2 : ℝ) * ‖utRep t‖ ^ 2 +
            (coercivityConstant / 2) * ∫ s in t₀..t,
              ‖(ut : ℝ → V) s‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖utInit‖ ^ 2 +
            (1 / (2 * coercivityConstant)) *
              ∫ s in t₀..t, ‖(ellDot : ℝ → F) s‖ ^ 2) :
    (∫ t, ‖(ut : ℝ → V) t‖ ^ 2
      ∂(volume.restrict (Set.Ioc t₀ t₁))) ≤
        (‖utInit‖ ^ 2 + (1 / coercivityConstant) * ‖ellDot‖ ^ 2) /
          coercivityConstant := by
  have hprefix :
      (∫ s in t₀..t₁, ‖(ellDot : ℝ → F) s‖ ^ 2) ≤ ‖ellDot‖ ^ 2 :=
    interval_integral_norm_sq_le_norm_sq ellDot ⟨ht.le, le_rfl⟩
  rw [← intervalIntegral.integral_of_le ht.le]
  exact
    state_integral_le_energy_budget_div
      coercivityConstant ‖utRep t₁‖ ‖utInit‖
      (∫ s in t₀..t₁, ‖(ut : ℝ → V) s‖ ^ 2)
      (∫ s in t₀..t₁, ‖(ellDot : ℝ → F) s‖ ^ 2)
      ‖ellDot‖ hCoercivityConstant hprefix
      (henergy t₁ ⟨ht.le, le_rfl⟩)

/--
A coercive autonomous evolution has a weak derivative, a continuous pivot
representative with a pointwise bound throughout the closed time interval, and
an integrated energy bound, all for the same representatives.
-/
theorem exists_continuous_pivot_with_coercive_bounds
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (T : GelfandTriple (V := V) (H := H))
    (Aop : V →L[ℝ] StrongDual ℝ V)
    (ellDot : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (ut : Lp V 2 (volume.restrict (Set.Ioc t₀ t₁)))
    (utInit : H)
    (hutEvolution :
      IsGelfandIntegratedWeakSolution T (fun _ ↦ Aop)
        (fun t ↦ ellDot t) ut utInit)
    (coercivityConstant : ℝ)
    (hCoercivityConstant : 0 < coercivityConstant)
    (hcoercive :
      ∀ w : V, coercivityConstant * ‖w‖ ^ 2 ≤ Aop w w) :
    ∃ (utt : Lp (StrongDual ℝ V) 2
          (volume.restrict (Set.Ioc t₀ t₁)))
      (Eut : ContinuousPivotEvolutionOn T
        (fun t ↦ (ut : ℝ → V) t) (fun t ↦ utt t) t₀ t₁),
      HasGelfandWeakTimeDerivativeOn T ut utt ∧
      (∀ t ∈ Set.Icc t₀ t₁,
        ‖Eut.representative t‖ ≤
          Real.sqrt
            (‖utInit‖ ^ 2 +
              (1 / coercivityConstant) * ‖ellDot‖ ^ 2)) ∧
      (∫ t, ‖(ut : ℝ → V) t‖ ^ 2
        ∂(volume.restrict (Set.Ioc t₀ t₁))) ≤
          (‖utInit‖ ^ 2 +
            (1 / coercivityConstant) * ‖ellDot‖ ^ 2) /
              coercivityConstant := by
  obtain ⟨utt, Eut, huttWeak, henergy⟩ :=
    exists_continuous_pivot_with_coercive_energy
      ht T Aop ellDot ut utInit hutEvolution
      coercivityConstant hCoercivityConstant hcoercive
  have hrepBound :=
    norm_representative_le_of_coercive_energy
      (V := V) (H := H) (F := StrongDual ℝ V)
      ut ellDot utInit Eut.representative
      hCoercivityConstant henergy
  have hutEnergyBound :=
    integral_norm_sq_le_of_coercive_energy
      (V := V) (H := H) (F := StrongDual ℝ V)
      ht ut ellDot utInit Eut.representative
      hCoercivityConstant henergy
  exact ⟨utt, Eut, huttWeak, hrepBound, hutEnergyBound⟩

end CoerciveEnergy
end AutonomousRegularity
end PDE.Parabolic.DivergenceFormHeat
