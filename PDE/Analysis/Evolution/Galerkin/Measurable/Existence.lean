/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.Galerkin.Existence
import PDE.Analysis.Evolution.Galerkin.Measurable.Caratheodory
import PDE.Analysis.Evolution.Galerkin.Measurable.WeakLimit
import PDE.Analysis.Evolution.Integrated.EnergyBounds
import PDE.Analysis.Evolution.Integrated.Uniqueness

/-!
# Weak-solution existence from measurable Galerkin approximations

Let `V ↪ H` be a Gelfand triple with trial spaces whose projections are uniformly stable and
eventually dense in `V`. Let `B(t) : V → V*` be bounded and measurable in time on `[a, b]`,
with a Gårding inequality `θ ‖w‖²_V ≤ B(t)(w, w) + γ ‖i w‖²_H` for some `θ > 0`. For every
load `ℓ ∈ L²(a, b; V*)` and every `uInit ∈ H` there is exactly one integrated weak solution
of `u' + B(t) u = ℓ` with initial value `uInit`. It has a weak time derivative in
`L²(a, b; V*)` and a representative continuous into `H` that satisfies the energy estimate.

## Main results

* `IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin`: existence for coercive
  forms and bounded measurable loads.
* `IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_L2`: existence and
  uniqueness for coercive forms and loads in `L²(a, b; V*)`.
* `IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_garding_L2`: the same
  under a Gårding inequality.
* `IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin_garding_L2_full`: the
  solution together with its derivative, continuous representative and energy estimate.

## How it works

This is Evans's existence and uniqueness theorem (§7.1.2, Theorems 1 to 4) for an abstract
Gelfand triple. As in Evans, whose coefficients are only in `L^∞`, the form is merely
measurable in time, so the Galerkin systems are Carathéodory ODEs;
`AEGelfandGalerkinApproximation.exists_sequence` solves them inside
`exists_of_measurable_galerkin`, and the weak limit is taken as in
`IsGelfandIntegratedWeakSolution.exists_of_ae_approximations`. Evans keeps the Gårding
inequality inside the energy estimate. We instead add `γ` times the pivot inner product
(`gardingShiftForm`), solve the coercive problem with load `e^{-γ(t - a)} ℓ`, and multiply the
solution by `e^{γ(t - a)}` (`IsGelfandIntegratedWeakSolution.of_exponential_gardingShift`).
Uniqueness is `IsGelfandIntegratedWeakSolution.unique_of_garding`, from the Lions–Magenes
energy identity and Grönwall's inequality.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1 (the definition of weak solution) and §7.1.2,
  Theorems 1-4. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

section GalerkinCaratheodory

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/--
Existence of integrated weak solutions for bounded measurable nonautonomous
forms and bounded measurable forcing.

Finite-dimensional Carathéodory solutions are constructed internally, their
uniform energy estimates provide weak compactness in `L²(a,b;V)`, and the
projected integrated equations identify the limit as a weak solution. The
statement assumes measurability only on the finite time interval.
-/
theorem IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (hell : AEStronglyMeasurable ell (volume.restrict (Set.Icc a b)))
    (MB Mell : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hell_bound : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) :
    ∃ uLimit : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B ell uLimit uInit := by
  let u₀ : ∀ n, S n := fun n ↦ (P n).projection uInit
  obtain ⟨G⟩ :=
    AEGelfandGalerkinApproximation.exists_sequence
      T S hfinite B ell hab.le hC hB hell MB Mell
      hB_bound hell_bound hcoercive u₀
  have hIocIcc :
      volume.restrict (Set.Ioc a b) ≤
        volume.restrict (Set.Icc a b) :=
    (volume : Measure ℝ).restrict_mono_set Set.Ioc_subset_Icc_self
  have hBmeasIoc :
      ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)) :=
    fun v ↦ (hB v).mono_measure hIocIcc
  have hellMeasIoc :
      AEStronglyMeasurable ell (volume.restrict (Set.Ioc a b)) :=
    hell.mono_measure hIocIcc
  have hBboundAE :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ (MB : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB_bound t (Set.Ioc_subset_Icc_self ht)
  have hellBoundAE :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖ell t‖ ≤ (Mell : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hell_bound t (Set.Ioc_subset_Icc_self ht)
  have hellMem :
      MemLp ell 2 (volume.restrict (Set.Ioc a b)) :=
    MemLp.of_bound hellMeasIoc (Mell : ℝ) hellBoundAE
  apply IsGelfandIntegratedWeakSolution.exists_of_ae_approximations
    (M := (Mell : ℝ)) (MB := (MB : ℝ))
    T S P hdenseEnergy B ell hab hC MB.2
    hBmeasIoc hBboundAE hellMem uInit
  simpa only [u₀] using G

/--
Existence and uniqueness for a measurable coercive form and an
arbitrary Bochner `L²(a,b;V*)` forcing.

Bounded continuous dual-valued loads are dense in Bochner `L²`. For each
such load, `exists_of_measurable_galerkin` supplies the Galerkin limit for a form `B`
measurable in time. `existsUnique_of_boundedContinuous_forcing` then uses coercive continuous
dependence to pass to the prescribed `L²` forcing.
-/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_L2
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b C : ℝ}
    (ell : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (hC : 0 < C)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (MB : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (uInit : H) :
    ∃! u : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit := by
  have hIocIcc :
      volume.restrict (Set.Ioc a b) ≤
        volume.restrict (Set.Icc a b) :=
    (volume : Measure ℝ).restrict_mono_set Set.Ioc_subset_Icc_self
  have hBmeasIoc :
      ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)) :=
    fun v ↦ (hB v).mono_measure hIocIcc
  have hBboundAE :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ (MB : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB_bound t (Set.Ioc_subset_Icc_self ht)
  apply
    IsGelfandIntegratedWeakSolution.existsUnique_of_boundedContinuous_forcing
      T B ell hab hC hBmeasIoc MB hBboundAE hcoercive uInit
  intro f
  have hfMeas :
      AEStronglyMeasurable f (volume.restrict (Set.Icc a b)) :=
    f.continuous.aestronglyMeasurable.restrict
  apply IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin
    T S hfinite P hdenseEnergy
    B f hab hC hB hfMeas MB ‖f‖₊ hB_bound
  · intro t _ht
    simpa using f.norm_coe_le_norm t
  · exact hcoercive

/--
Existence and uniqueness for a measurable form satisfying the
Gårding lower bound

`theta ‖v‖_V² ≤ B(t)(v,v) + gamma ‖Jv‖_H²`.

The mass-shifted form is measurable and uniformly coercive.
`existsUnique_of_measurable_galerkin_L2` solves the exponentially rescaled problem, and the
weak exponential change of variables returns the solution of the original equation.
Uniqueness uses the Lions–Magenes energy identity and Grönwall's inequality.
-/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_garding_L2
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b theta gamma : ℝ}
    (ell : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (htheta : 0 < theta)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (MB : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hGarding : ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤
        B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (uInit : H) :
    ∃! u : Lp V 2 (volume.restrict (Set.Ioc a b)),
      IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit := by
  let μab := volume.restrict (Set.Ioc a b)
  let Bshift : ℝ → V →L[ℝ] StrongDual ℝ V :=
    gardingShiftForm T B gamma
  let ellShift : Lp (StrongDual ℝ V) 2 μab :=
    exponentialMulLp (-gamma) ell
  let MBshift : NNReal :=
    MB + ‖gamma‖₊ * ‖T.energyToDual‖₊
  have hBshiftMeas :
      ∀ v, AEStronglyMeasurable (fun t ↦ Bshift t v)
      (volume.restrict (Set.Icc a b)) :=
    aestronglyMeasurable_gardingShiftForm T hB
  have hBshiftNorm : ∀ t ∈ Set.Icc a b, ‖Bshift t‖ ≤ MBshift := by
    intro t ht
    calc
      ‖Bshift t‖ ≤ ‖B t‖ + ‖gamma‖ * ‖T.energyToDual‖ :=
        norm_gardingShiftForm_le T B gamma t
      _ ≤ (MB : ℝ) + ‖gamma‖ * ‖T.energyToDual‖ := by
        gcongr
        exact hB_bound t ht
      _ = (MBshift : ℝ) := by simp [MBshift]
  have hBshiftCoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤ Bshift t w w :=
    gardingShiftForm_coercive T B hGarding
  obtain ⟨w, hw, _hwUnique⟩ :=
    IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_L2
      T S hfinite P hdenseEnergy
      Bshift ellShift hab htheta hBshiftMeas MBshift
      hBshiftNorm hBshiftCoercive uInit
  let u : Lp V 2 μab := exponentialMulLp gamma w
  have hIocIcc :
      volume.restrict (Set.Ioc a b) ≤
        volume.restrict (Set.Icc a b) :=
    (volume : Measure ℝ).restrict_mono_set Set.Ioc_subset_Icc_self
  have hBmeasIoc :
      ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)) :=
    fun v ↦ (hB v).mono_measure hIocIcc
  have hBboundAE :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ (MB : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB_bound t (Set.Ioc_subset_Icc_self ht)
  have hu : IsGelfandIntegratedWeakSolution T B
      (fun t ↦ ell t) u uInit :=
    hw.of_exponential_gardingShift
      hBmeasIoc (MB : ℝ) hBboundAE
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact hv.unique_of_garding hBmeasIoc (MB : ℝ) hBboundAE
    htheta.le hGarding hu hab

/--
The full initial-value theorem for a measurable form satisfying a
Gårding inequality and an arbitrary forcing in `L²(a,b;V*)`.

`existsUnique_of_measurable_galerkin_garding_L2` constructs the unique Bochner class solving
the integrated weak equation. This theorem adds the data that Evans uses to define the
parabolic weak solution and its a priori theory:

* the weak time derivative belongs to `L²(a,b;V*)`;
* `u_t = ell - B(·)u` almost everywhere;
* the state has a representative continuous from `[a,b]` into the pivot
  Hilbert space `H`, with left trace equal to `uInit`;
* the representative satisfies the Gårding energy estimate on every prefix
  `[a,t]`.

Thus the measurable Galerkin construction produces a weak solution in the sense of
Evans §7.1.1, with the continuity into `H` that Evans obtains from §5.9.2, Theorem 3.
-/
theorem IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin_garding_L2_full
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : NNReal} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b theta gamma : ℝ}
    (ell : Lp (StrongDual ℝ V) 2
      (volume.restrict (Set.Ioc a b)))
    (hab : a < b) (htheta : 0 < theta)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (MB : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hGarding : ∀ t ∈ Set.Icc a b, ∀ w : V,
      theta * ‖w‖ ^ 2 ≤
        B t w w + gamma * ‖T.inclusion w‖ ^ 2)
    (uInit : H) :
    ∃ u : Lp V 2 (volume.restrict (Set.Ioc a b)),
      ∃ g : Lp (StrongDual ℝ V) 2
        (volume.restrict (Set.Ioc a b)),
        ∃ E : ContinuousPivotEvolutionOn T
          (fun t ↦ u t) (fun t ↦ g t) a b,
          IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) u uInit ∧
          (∀ v : Lp V 2 (volume.restrict (Set.Ioc a b)),
            IsGelfandIntegratedWeakSolution T B (fun t ↦ ell t) v uInit →
              v = u) ∧
          HasGelfandWeakTimeDerivativeOn T u g ∧
          E.representative a = uInit ∧
          (g : ℝ → StrongDual ℝ V) =ᵐ[
            volume.restrict (Set.Ioc a b)]
              (fun t ↦ ell t - B t (u t)) ∧
          ∀ t ∈ Set.Icc a b,
            (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
                (theta / 2) * (∫ s in a..t, ‖u s‖ ^ 2) ≤
              (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
                (1 / (2 * theta)) * (∫ s in a..t, ‖ell s‖ ^ 2) +
                gamma * (∫ s in a..t, ‖E.representative s‖ ^ 2) := by
  obtain ⟨u, hu, huUnique⟩ :=
    IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_garding_L2
      T S hfinite P hdenseEnergy B ell hab htheta hB MB
      hB_bound hGarding uInit
  have hIocIcc :
      volume.restrict (Set.Ioc a b) ≤
        volume.restrict (Set.Icc a b) :=
    (volume : Measure ℝ).restrict_mono_set Set.Ioc_subset_Icc_self
  have hBmeasIoc :
      ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Ioc a b)) :=
    fun v ↦ (hB v).mono_measure hIocIcc
  have hBboundAE :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖B t‖ ≤ (MB : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB_bound t (Set.Ioc_subset_Icc_self ht)
  obtain ⟨g, E, hgweak, htrace, hresidual, henergy⟩ :=
    hu.exists_continuousPivotEvolutionOn_with_garding_bound_L2
      hBmeasIoc (MB : ℝ) hBboundAE htheta hGarding hab
  exact ⟨u, g, E, hu, huUnique, hgweak, htrace, hresidual, henergy⟩

end GalerkinCaratheodory

end PDE.Analysis.Evolution
