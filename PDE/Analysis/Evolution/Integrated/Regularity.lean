/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.Integrated.TimeDependentForm
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.InitialTrace
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval

/-!
# Time regularity of integrated weak solutions

An integrated weak solution `u ∈ L²(a, b; V)` of `u' + B(t) u = ℓ` with initial datum
`uInit ∈ H` (`IsGelfandIntegratedWeakSolution`) is defined by testing against products
`τ(t) v` with `τ : TimeTest a b`, so a priori it has no time derivative and no value at
any particular time. We recover both. Restricting the defining identity to tests
with `τ a = 0` shows that the residual `ℓ - B(·)u`, which lies in `L²(a, b; V*)` when `B`
is measurable and bounded, is the Gelfand weak time derivative of `u`. The Lions–Magenes
theorem (`PDE.Analysis.Evolution.LionsMagenes`) then produces an `H`-continuous
representative on `[a, b]` with the integrated derivative and the exact energy identity.
Finally, testing the integrated equation against the affine hat `t ↦ (b - t)/(b - a)`,
which equals one at `a`, identifies the left trace of that representative with `uInit`.

This is the passage from `u ∈ L²(0, T; H¹₀), u' ∈ L²(0, T; H⁻¹)` to
`u ∈ C([0, T]; L²)` with `u(0) = g` in the proof of Evans §7.1.2, Theorem 3, which rests on
§5.9.2, Theorem 3 for such pairs `u, u'`. Here it is carried out in an abstract Gelfand
triple.

## Main results

* `IsGelfandIntegratedWeakSolution.hasWeakTimeDerivative_residual`: the residual
  `gelfandResidualLp B ℓ u` is a weak time derivative of `u`.
* `IsGelfandIntegratedWeakSolution.ae_weak_equation`: any weak derivative `g` of `u`
  satisfies `g(t) + B(t) u(t) = ℓ(t)` for a.e. `t`, by uniqueness of `L²(V*)` weak
  derivatives.
* `HasGelfandWeakTimeDerivativeOn.norm_le_of_integrated_solution`: the bound
  `‖g‖_{L²(V*)} ≤ ‖ℓ‖ + M_B ‖u‖`.
* `IsGelfandIntegratedWeakSolution.exists_continuous_representativeOn`,
  `exists_continuousPivotEvolutionOnOpen`, `exists_continuousPivotEvolutionOn`: the
  Lions–Magenes representative on compact subintervals, on the open interval, and on the
  closed interval `[a, b]`, for continuous forcing.
* `IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial_L2`: for
  `ℓ ∈ L²(a, b; V*)`, a closed-interval representative `E` with `E a = uInit` and
  `g = ℓ - B(·)u` a.e.
* `IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial`: the
  continuous-forcing specialisation.

## Implementation notes

Continuity of `ℓ` on `[a, b]` serves only to make it an `L²` class, so the
continuous-forcing theorems follow from the `_L2` ones. The endpoint theorems require
`MeasurableSpace` and `BorelSpace` instances on both `V` and `StrongDual ℝ V`; they may be
chosen locally.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3, and §7.1.2, proof of Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [CompleteSpace V] in
/-- Tested against `v` and a time test `τ`, the residual `ℓ - B(·)u` integrates to the forcing
term minus the form term. -/
private theorem integral_gelfandResidualLp_mul {a b : ℝ} {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Set.Ioc a b)))
    (MB : ℝ) (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (v : V) (τ : TimeTest a b) :
    (∫ t, gelfandResidualLp B ell u hBmeas MB hBbound t v * τ.toLp t
        ∂(volume.restrict (Set.Ioc a b))) =
      (∫ t, ell t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) -
        ∫ t, B t (u t) v * τ.toLp t ∂(volume.restrict (Set.Ioc a b)) := by
  rw [← integral_sub (integrable_dualTimeTest v τ.toLp ell)
    (integrable_timeDependentBilinearTimeTest B v τ.toLp hBmeas MB hBbound u)]
  refine integral_congr_ae ?_
  filter_upwards [gelfandResidualLp_apply_ae B ell u hBmeas MB hBbound] with t ht
  rw [ht, sub_apply, sub_mul]

omit [CompleteSpace V] in
/-- An integrated Gelfand weak solution has the residual `ℓ - B(·)u ∈ L²(a, b; V*)` as
Gelfand weak time derivative. -/
theorem IsGelfandIntegratedWeakSolution.hasWeakTimeDerivative_residual
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hu : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit) :
    HasGelfandWeakTimeDerivativeOn T u
      (gelfandResidualLp B ell u hBmeas MB hBbound) := by
  intro v τ hτa
  have heq := hu.equation v τ
  rw [hτa, mul_zero, add_zero] at heq
  rw [integral_gelfandResidualLp_mul]
  linarith

/--
Any identified weak time derivative of an integrated solution satisfies the
evolution equation almost everywhere:
`g(t) + B(t)u(t) = ell(t)` in `V*`.

The integrated formulation first identifies the canonical residual
`ell - B u` as a weak derivative. Uniqueness of `L²(V*)` weak derivatives
then identifies an arbitrary supplied derivative `g` with that residual.
-/
theorem IsGelfandIntegratedWeakSolution.ae_weak_equation
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hu : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit)
    (hg : HasGelfandWeakTimeDerivativeOn T u g) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      g t + B t (u t) = ell t := by
  have hresidualDerivative :=
    hu.hasWeakTimeDerivative_residual hBmeas MB hBbound
  have hresidual :
      g = gelfandResidualLp B ell u hBmeas MB hBbound :=
    hg.eq hresidualDerivative
  have hresidualCoe :
      (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)]
        fun t ↦ ell t - B t (u t) := by
    rw [hresidual]
    exact gelfandResidualLp_apply_ae B ell u hBmeas MB hBbound
  filter_upwards [hresidualCoe] with t ht
  exact eq_sub_iff_add_eq.mp ht

/-- A weak derivative of an integrated solution inherits the quantitative
bound for the canonical residual `ell - B(·)u`. -/
theorem HasGelfandWeakTimeDerivativeOn.norm_le_of_integrated_solution
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (hg : HasGelfandWeakTimeDerivativeOn T u g)
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hu : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit) :
    ‖g‖ ≤ ‖ell‖ + MB * ‖u‖ := by
  have hresidual :=
    hu.hasWeakTimeDerivative_residual hBmeas MB hBbound
  rw [hg.eq hresidual]
  exact norm_gelfandResidualLp_le B ell u hBmeas MB hBbound

omit [CompleteSpace V] in
/-- For forcing continuous on `[a, b]`, an integrated weak solution has a Gelfand weak
time derivative in `L²(a, b; V*)`. -/
theorem IsGelfandIntegratedWeakSolution.exists_weakTimeDerivative_of_continuous_forcing
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hell : ContinuousOn ell (Set.Icc a b))
    (hu : IsGelfandIntegratedWeakSolution T B ell u uInit) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      HasGelfandWeakTimeDerivativeOn T u g := by
  let ellMem : MemLp ell 2 (volume.restrict (Set.Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hell
  let ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)) :=
    ellMem.toLp ell
  have hellAE : (ellLp : ℝ → StrongDual ℝ V) =ᵐ[
      volume.restrict (Set.Ioc a b)] ell :=
    ellMem.coeFn_toLp
  have huLp : IsGelfandIntegratedWeakSolution T B (fun t ↦ ellLp t) u uInit :=
    hu.congr_forcing_ae hellAE.symm
  exact ⟨gelfandResidualLp B ellLp u hBmeas MB hBbound,
    huLp.hasWeakTimeDerivative_residual hBmeas MB hBbound⟩

/-- Time regularity of an integrated nonautonomous weak solution.  The weak
equation first identifies `u_t = ell - B(t)u` as an `L²(V*)` trajectory; the
finite-interval Lions–Magenes theorem then supplies an `H`-continuous
representative and the energy identity on every compact subinterval `[c, d]` of
`(a,b)` (Evans, 2nd ed., §7.1.2). -/
theorem IsGelfandIntegratedWeakSolution.exists_continuous_representativeOn
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b c d : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hell : ContinuousOn ell (Set.Icc a b))
    (hu : IsGelfandIntegratedWeakSolution T B ell u uInit)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      HasGelfandWeakTimeDerivativeOn T u g ∧
      Nonempty (ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) c d) := by
  obtain ⟨g, hg⟩ := hu.exists_weakTimeDerivative_of_continuous_forcing
    hBmeas MB hBbound hell
  exact ⟨g, hg, hg.hasWeakTimeDerivativeOn.exists_continuous_representativeOn hac hcd hdb⟩

/-- Open-interval time regularity for an integrated nonautonomous weak
solution.  In addition to identifying the `L²(V*)` derivative, this returns
one compatible `H`-continuous representative on the entire interior time
interval, with its integrated derivative and energy law. -/
theorem IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOnOpen
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hell : ContinuousOn ell (Set.Icc a b))
    (hu : IsGelfandIntegratedWeakSolution T B ell u uInit) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      HasGelfandWeakTimeDerivativeOn T u g ∧
      Nonempty (ContinuousPivotEvolutionOnOpen T
        (fun t ↦ u t) (fun t ↦ g t) a b) := by
  obtain ⟨g, hg⟩ := hu.exists_weakTimeDerivative_of_continuous_forcing
    hBmeas MB hBbound hell
  exact ⟨g, hg,
    hg.hasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen hu.interval_nonempty⟩

/-- Closed-interval time regularity for an integrated nonautonomous weak
solution with forcing continuous on `[a, b]`: `u` has a Gelfand weak derivative
`g ∈ L²(a, b; V*)` and a representative in `C([a,b];H)` satisfying the integrated
derivative and the exact energy identity up to both endpoints. By `ae_weak_equation`,
`g = ell - B(t)u` a.e. -/
theorem IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hell : ContinuousOn ell (Set.Icc a b))
    (hu : IsGelfandIntegratedWeakSolution T B ell u uInit) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      HasGelfandWeakTimeDerivativeOn T u g ∧
      Nonempty (ContinuousPivotEvolutionOn T
        (fun t ↦ u t) (fun t ↦ g t) a b) := by
  obtain ⟨g, hg, Eopen⟩ := hu.exists_continuousPivotEvolutionOnOpen
    hBmeas MB hBbound hell
  obtain ⟨Eopen⟩ := Eopen
  exact ⟨g, hg, Eopen.toContinuousPivotEvolutionOn T hu.interval_nonempty
    (MeasureTheory.Lp.memLp u) (MeasureTheory.Lp.memLp g)⟩

/-- Time regularity of an integrated weak solution with forcing `ell ∈ L²(a,b;V*)`: there
is a weak derivative `g` with `g = ell - B(·)u` a.e. and a representative `E` in
`C([a,b];H)` with `E a = uInit`.

The finite-interval Lions–Magenes theorem supplies `E`. Testing the integrated weak
equation with the affine initial-endpoint test identifies the left trace of `E` with
the prescribed initial datum. -/
theorem IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial_L2
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hu : IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit)
    (hab : a < b) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b,
        HasGelfandWeakTimeDerivativeOn T u g ∧
        E.representative a = uInit ∧
        (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)]
          fun t ↦ ell t - B t (u t) := by
  let g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)) :=
    gelfandResidualLp B ell u hBmeas MB hBbound
  have hgweak : HasGelfandWeakTimeDerivativeOn T u g :=
    hu.hasWeakTimeDerivative_residual hBmeas MB hBbound
  obtain ⟨Eopen⟩ := hgweak.hasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen hab
  obtain ⟨E⟩ := Eopen.toContinuousPivotEvolutionOn T hab (Lp.memLp u) (Lp.memLp g)
  refine ⟨g, E, hgweak, ?_, gelfandResidualLp_apply_ae B ell u hBmeas MB hBbound⟩
  refine T.pivotToDual_injective (ContinuousLinearMap.ext fun v ↦ ?_)
  let τ : TimeTest a b := TimeTest.initialHat a b
  let μab := volume.restrict (Set.Ioc a b)
  have hEae : E.representative =ᵐ[μab] fun t ↦ T.inclusion (u t) :=
    ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_uIcc)
      E.ae_eq_inclusion
  have hτae : (τ.toLp : ℝ → ℝ) =ᵐ[μab] τ.toFun := τ.memLp.coeFn_toLp
  have hdτae : (τ.derivToLp : ℝ → ℝ) =ᵐ[μab] τ.derivFun := τ.derivMemLp.coeFn_toLp
  have htime :
      (∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.derivToLp t ∂μab) =
      ∫ t, inner ℝ (E.representative t) (T.inclusion v) * τ.derivFun t ∂μab :=
    integral_congr_ae <| by
      filter_upwards [hEae, hdτae] with t hEt hdt
      rw [hEt, hdt]
  have hgtest : (∫ t, g t v * τ.toLp t ∂μab) = ∫ t, g t v * τ.toFun t ∂μab :=
    integral_congr_ae <| hτae.mono fun t ht ↦ by simp only [ht]
  have hresInt : (∫ t, g t v * τ.toLp t ∂μab) =
      (∫ t, ell t v * τ.toLp t ∂μab) - ∫ t, B t (u t) v * τ.toLp t ∂μab :=
    integral_gelfandResidualLp_mul hBmeas MB hBbound v τ
  have hboundary := E.initialHat_boundary_identity T hab v
  simp only [intervalIntegral.integral_of_le hab.le] at hboundary
  rw [← htime, ← hgtest, hresInt] at hboundary
  have hsolution := hu.equation v τ
  change T.pivotToDual (E.representative a) v = T.pivotToDual uInit v
  simp only [GelfandTriple.pivotToDual_apply]
  dsimp only [τ] at hsolution hboundary
  rw [TimeTest.initialHat_initial hab] at hsolution
  linarith

/-- `exists_continuousPivotEvolutionOn_initial_L2` for forcing continuous on `[a, b]`,
which is then a Bochner `L²` class. -/
theorem IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))} {uInit : H}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ MB)
    (hell : ContinuousOn ell (Set.Icc a b))
    (hu : IsGelfandIntegratedWeakSolution T B ell u uInit)
    (hab : a < b) :
    ∃ g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b,
        HasGelfandWeakTimeDerivativeOn T u g ∧
        E.representative a = uInit ∧
        (g : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)]
          fun t ↦ ell t - B t (u t) := by
  let ellMem : MemLp ell 2 (volume.restrict (Set.Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hell
  have hellAE : (ellMem.toLp ell : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Set.Ioc a b)] ell :=
    ellMem.coeFn_toLp
  obtain ⟨g, E, hgweak, hEa, hresidual⟩ := (hu.congr_forcing_ae hellAE.symm
    ).exists_continuousPivotEvolutionOn_initial_L2 hBmeas MB hBbound hab
  refine ⟨g, E, hgweak, hEa, ?_⟩
  filter_upwards [hresidual, hellAE] with t hres hellt
  rw [hres, hellt]

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
