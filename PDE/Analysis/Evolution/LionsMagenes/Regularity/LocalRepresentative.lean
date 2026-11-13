/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import PDE.Analysis.Evolution.LionsMagenes.Basic.RegularizedEnergy
import PDE.Analysis.Evolution.Time.WeakDerivative.Localization

/-!
# Local representatives of weak Gelfand evolutions

The global Lions–Magenes theorem is stated for trajectories on the whole
time line: `u ∈ L²(ℝ; V)` with weak derivative `g ∈ L²(ℝ; V*)` has a continuous `H`-valued
representative satisfying the integrated derivative and the energy identity
(`ContinuousPivotEvolution`). We transfer that result to a finite interval.
Given `u ∈ L²(a, b; V)` whose energy map has distributional derivative
`g ∈ L²(a, b; V*)` and a smooth cutoff `χ` supported in `(a, b)`, the
product `χ u` is a global `L²(V)` trajectory whose weak derivative is the Leibniz
expression `χ g + χ' J u`, with `J = T.energyToDual`. The global theorem applies to
`χ u`. If moreover `χ = 1` near a compact subinterval `[c, d] ⊆ (a, b)`, then on `[c, d]`
the cutoff is invisible: the continuous representative of `χ u` is a continuous
representative of `u` itself, with the original derivative `g` and the original energy
identity.

This is the interior part of the theorem that `u ∈ L²(0, T; V)`, `u' ∈ L²(0, T; V*)`
implies `u ∈ C([0, T]; H)`, which Evans proves for `H¹₀ ⊂ L² ⊂ H⁻¹` (§5.9.2,
Theorem 3(i)). Reaching the
endpoints `a`, `b` themselves requires the reflection arguments of
`PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity`.

## Main results

* `memLp_two_cutoff_smul_of_tsupport_subset`: multiplying a restricted `L²` function by
  a bounded cutoff supported inside the restriction set gives a global `L²` function.
* `cutoffGelfandDerivative`, `memLp_two_cutoffGelfandDerivative`: the weak Leibniz
  derivative `χ g + χ' J u` and its `L²` membership.
* `exists_smooth_cutoff_Icc_tsupport_Ioo`: a `C^∞` cutoff equal to `1` near `[c, d]` with
  support in `(a, b)`, whenever `a < c ≤ d < b`.
* `HasWeakTimeDerivativeOn.exists_continuous_cutoff_representative`: the global
  Lions–Magenes theorem applied to `χ u`.
* `HasWeakTimeDerivativeOn.exists_continuous_representativeOn_of_cutoff`,
  `exists_continuous_representativeOn`: a `ContinuousPivotEvolutionOn` for `u` on
  `[c, d]`, first for a given cutoff and then with the cutoff constructed automatically.

## Implementation notes

The Leibniz identity for `χ u` is proved at the level of the generic Banach-valued weak
derivative (`HasWeakTimeDerivativeOn`). Smooth compactly supported scalar tests
suffice; the stronger integrated-test formulation implies this hypothesis through
`HasGelfandWeakTimeDerivativeOn.hasWeakTimeDerivativeOn`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3. <https://doi.org/10.1090/gsm/019>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*,
  Vol. I, Springer, 1972, Chapter 1 (Hilbert theory of trace and interpolation spaces).
  <https://doi.org/10.1007/978-3-642-65161-8>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section GelfandWeakTimeDerivative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A restricted Bochner `L²` function multiplied by a bounded scalar cutoff
whose topological support lies in the restriction set defines a global
Bochner `L²` function.  This removes any dependence on the arbitrary values
of an `Lp` representative outside the restricted measure. -/
theorem memLp_two_cutoff_smul_of_tsupport_subset
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {S : Set ℝ} (hS : MeasurableSet S)
    (f : ℝ → X) (hf : MemLp f 2 (volume.restrict S))
    (χ : ℝ → ℝ) (hχ : MemLp χ ⊤ (volume : Measure ℝ))
    (hχsupp : closure (Function.support χ) ⊆ S) :
    MemLp (fun t ↦ χ t • f t) 2 (volume : Measure ℝ) := by
  have hχRestrict : MemLp χ ⊤ (volume.restrict S) :=
    hχ.mono_measure Measure.restrict_le_self
  have hproductRestrict :
      MemLp (fun t ↦ χ t • f t) 2 (volume.restrict S) := by
    change MemLp (χ • f) 2 (volume.restrict S)
    exact hχRestrict.smul hf
  have hindicator :
      S.indicator (fun t ↦ χ t • f t) = fun t ↦ χ t • f t := by
    apply Set.indicator_eq_self.2
    intro t ht
    have hχt : t ∈ Function.support χ := by
      intro hzero
      exact ht (by simp [hzero])
    exact hχsupp (subset_closure hχt)
  have hglobalIndicator :
      MemLp (S.indicator (fun t ↦ χ t • f t)) 2
        (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict hS.nullMeasurableSet).2 hproductRestrict
  rwa [hindicator] at hglobalIndicator

/-- Distributional derivative of a cutoff Gelfand trajectory, as prescribed
by the weak Leibniz rule. -/
noncomputable def cutoffGelfandDerivative
    (T : GelfandTriple (V := V) (H := H))
    (χ : ℝ → ℝ) (u : ℝ → V) (g : ℝ → StrongDual ℝ V) :
    ℝ → StrongDual ℝ V :=
  fun t ↦ χ t • g t + deriv χ t • T.energyToDual (u t)

/-- The cutoff Gelfand derivative is globally `L²` once its two Leibniz
terms are globally `L²`. -/
theorem memLp_two_cutoffGelfandDerivative
    (T : GelfandTriple (V := V) (H := H))
    (χ : ℝ → ℝ) (u : ℝ → V) (g : ℝ → StrongDual ℝ V)
    (h₁ : MemLp (fun t ↦ χ t • g t) 2 (volume : Measure ℝ))
    (h₂ : MemLp (fun t ↦ deriv χ t • T.energyToDual (u t)) 2
      (volume : Measure ℝ)) :
    MemLp (cutoffGelfandDerivative T χ u g) 2 (volume : Measure ℝ) := by
  let dualNormed : NormedAddCommGroup (StrongDual ℝ V) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := V) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedAddCommGroup (StrongDual ℝ V) := dualNormed
  unfold cutoffGelfandDerivative
  change MemLp
    ((fun t ↦ χ t • g t) + fun t ↦ deriv χ t • T.energyToDual (u t))
    2 (volume : Measure ℝ)
  exact MemLp.add (ε := StrongDual ℝ V)
    (f := fun t ↦ χ t • g t)
    (g := fun t ↦ deriv χ t • T.energyToDual (u t)) h₁ h₂

/-- A compact interval strictly contained in `(a,b)` admits a smooth cutoff
which is identically one on a neighborhood of every point of that interval
and whose topological support is contained in `(a,b)`. -/
theorem exists_smooth_cutoff_Icc_tsupport_Ioo
    {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      closure (Function.support χ) ⊆ Set.Ioo a b ∧
      ∀ t ∈ Set.Icc c d, χ =ᶠ[nhds t] (1 : ℝ → ℝ) := by
  let δ : ℝ := min (c - a) (b - d) / 3
  let m : ℝ := (c + d) / 2
  let r : ℝ := (d - c) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith
  let ψ : ContDiffBump m := {
    rIn := r + δ
    rOut := r + 2 * δ
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith
  }
  refine ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ?_, ?_⟩
  · change tsupport (ψ : ℝ → ℝ) ⊆ Set.Ioo a b
    rw [ψ.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hx
    have hleft : 3 * δ ≤ c - a := by
      dsimp [δ]
      have := min_le_left (c - a) (b - d)
      linarith
    have hright : 3 * δ ≤ b - d := by
      dsimp [δ]
      have := min_le_right (c - a) (b - d)
      linarith
    rw [abs_le] at hx
    constructor <;> dsimp [ψ, m, r] at hx ⊢ <;> linarith
  · intro t ht
    apply ψ.eventuallyEq_one_of_mem_ball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rcases ht with ⟨hct, htd⟩
    dsimp [ψ, m, r]
    constructor <;> linarith

/-- Localized Lions–Magenes regularity for a weak Gelfand evolution.
A smooth cutoff compactly supported in `(a,b)` gives a global trajectory `χ u`
with weak derivative `χ g + χ' J u`, where `J = T.energyToDual`. The global theorem
gives this cutoff trajectory an `H`-continuous representative, its integrated dual
derivative, and the exact energy identity. The results below recover the original
trajectory on compact subintervals where `χ = 1` on a neighborhood; endpoint completion
uses the reflection construction in `EndpointRegularity`. -/
theorem HasWeakTimeDerivativeOn.exists_continuous_cutoff_representative
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (hχsupp : closure (Function.support χ) ⊆ Set.Ioo a b) :
    Nonempty (ContinuousPivotEvolution T
      (fun s ↦ χ s • u s)
      (cutoffGelfandDerivative T χ (fun s ↦ u s) (fun s ↦ g s))) := by
  let uχ : ℝ → V := fun t ↦ χ t • u t
  let gχ : ℝ → StrongDual ℝ V :=
    cutoffGelfandDerivative T χ (fun t ↦ u t) (fun t ↦ g t)
  have hχTop : MemLp χ ⊤ (volume : Measure ℝ) :=
    hχ.continuous.memLp_top_of_hasCompactSupport hχcompact
      (volume : Measure ℝ)
  have hχIoc : closure (Function.support χ) ⊆ Set.Ioc a b :=
    hχsupp.trans Set.Ioo_subset_Ioc_self
  have huχ : MemLp uχ 2 (volume : Measure ℝ) := by
    exact memLp_two_cutoff_smul_of_tsupport_subset measurableSet_Ioc
      (fun t ↦ u t) (MeasureTheory.Lp.memLp u) χ hχTop hχIoc
  have hgχ₁ : MemLp (fun t ↦ χ t • g t) 2
      (volume : Measure ℝ) := by
    exact memLp_two_cutoff_smul_of_tsupport_subset measurableSet_Ioc
      (fun t ↦ g t) (MeasureTheory.Lp.memLp g) χ hχTop hχIoc
  have hdχ : ContDiff ℝ (⊤ : ℕ∞) (deriv χ) :=
    (contDiff_infty_iff_deriv.mp hχ).2
  have hdχcompact : HasCompactSupport (deriv χ) := hχcompact.deriv
  have hdχTop : MemLp (deriv χ) ⊤ (volume : Measure ℝ) :=
    hdχ.continuous.memLp_top_of_hasCompactSupport hdχcompact
      (volume : Measure ℝ)
  have hdχIoc : closure (Function.support (deriv χ)) ⊆ Set.Ioc a b :=
    tsupport_deriv_subset.trans hχIoc
  have huDualRestrict : MemLp (fun t ↦ T.energyToDual (u t)) 2
      (volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.Lp.memLp u).continuousLinearMap_comp T.energyToDual
  have hgχ₂ : MemLp
      (fun t ↦ deriv χ t • T.energyToDual (u t)) 2
      (volume : Measure ℝ) := by
    exact memLp_two_cutoff_smul_of_tsupport_subset measurableSet_Ioc
      (fun t ↦ T.energyToDual (u t)) huDualRestrict
      (deriv χ) hdχTop hdχIoc
  have hgχ : MemLp gχ 2 (volume : Measure ℝ) := by
    exact memLp_two_cutoffGelfandDerivative T χ
      (fun t ↦ u t) (fun t ↦ g t) hgχ₁ hgχ₂
  have hweakRaw :=
    (h.smul_contDiff_global
      χ hχ hχcompact hχsupp)
  have hweak : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn Set.univ
      (T.energyToDual ∘ uχ) gχ := by
    change PDE.Analysis.Evolution.HasWeakTimeDerivativeOn Set.univ
      (fun t ↦ T.energyToDual (χ t • u t))
      (fun t ↦ χ t • g t + deriv χ t • T.energyToDual (u t))
    simpa only [map_smul] using hweakRaw
  exact nonempty_continuousPivotEvolution T huχ hgχ hweak

/-- Interior Lions–Magenes theorem on a compact subinterval.  If the cutoff
is identically one near `[[c,d]]`, the global representative obtained after
localization is a continuous representative of the *original* trajectory on
that interval.  The cutoff and its derivative disappear from both the weak
fundamental theorem of calculus and the energy identity.

This is the local chart used to pass from the global regularization theorem
to the finite-interval statement of Evans §5.9.2, Theorem 3. -/
theorem HasWeakTimeDerivativeOn.exists_continuous_representativeOn_of_cutoff
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b c d : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t))
    (hcd : c ≤ d)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (hχsupp : closure (Function.support χ) ⊆ Set.Ioo a b)
    (hχone : ∀ t ∈ Set.Icc c d, χ =ᶠ[nhds t] (1 : ℝ → ℝ)) :
    Nonempty (ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) c d) := by
  obtain ⟨E⟩ := h.exists_continuous_cutoff_representative
    χ hχ hχcompact hχsupp
  have hχvalue : ∀ t ∈ Set.uIcc c d, χ t = 1 := by
    intro t ht
    exact (hχone t (by simpa [Set.uIcc_of_le hcd] using ht)).eq_of_nhds
  have hχderiv : ∀ t ∈ Set.uIcc c d, deriv χ t = 0 := by
    intro t ht
    have hlocal := hχone t (by simpa [Set.uIcc_of_le hcd] using ht)
    simpa using hlocal.deriv_eq
  have huEq : Set.EqOn
      (fun t ↦ χ t • u t) (fun t ↦ u t) (Set.uIcc c d) := by
    intro t ht
    simp [hχvalue t ht]
  have hgEq : Set.EqOn
      (cutoffGelfandDerivative T χ (fun t ↦ u t) (fun t ↦ g t))
      (fun t ↦ g t) (Set.uIcc c d) := by
    intro t ht
    simp [cutoffGelfandDerivative, hχvalue t ht, hχderiv t ht]
  have hae : E.representative =ᵐ[volume.restrict (Set.uIcc c d)]
      fun t ↦ T.inclusion (u t) := by
    refine E.ae_eq_inclusion.restrict.trans ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIcc] with t ht
    exact congrArg T.inclusion (huEq ht)
  have hIntegrated : HasIntegratedDualDerivativeOn T E.representative
      (fun t ↦ g t) c d := by
    have hcut := E.integratedDerivative c d
    refine {
      intervalIntegrable := hcut.intervalIntegrable.congr
        (fun t ht ↦ hgEq (Set.uIoc_subset_uIcc ht))
      eq_add_integral := ?_
    }
    intro t ht
    have hprimitive : dualPrimitive
        (cutoffGelfandDerivative T χ (fun r ↦ u r) (fun r ↦ g r)) c t =
        dualPrimitive (fun r ↦ g r) c t := by
      unfold dualPrimitive
      apply intervalIntegral.integral_congr_ae
      filter_upwards with r
      intro hr
      exact hgEq (Set.uIcc_subset_uIcc_left ht
        (Set.uIoc_subset_uIcc hr))
    rw [← hprimitive]
    exact hcut.eq_add_integral t ht
  refine ⟨{
    representative := E.representative
    continuousOn := E.continuous.continuousOn
    ae_eq_inclusion := hae
    integratedDerivative := hIntegrated
    energyIdentity := ?_
  }⟩
  intro s t hs ht
  have hpairing :
      (∫ r in s..t,
        cutoffGelfandDerivative T χ (fun q ↦ u q) (fun q ↦ g q) r
          (χ r • u r)) =
      ∫ r in s..t, g r (u r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r
    intro hr
    have hr' : r ∈ Set.uIcc c d :=
      Set.uIcc_subset_uIcc hs ht (Set.uIoc_subset_uIcc hr)
    rw [hgEq hr', hχvalue r hr', one_smul]
  rw [← hpairing]
  exact E.energyIdentity s t

/-- Finite-interval Lions–Magenes regularity on every compact subinterval of
`(a,b)`.  A weak Gelfand trajectory in `L²(a,b;V)` with derivative in
`L²(a,b;V*)` has an `H`-continuous representative on `[[c,d]]`, the expected
integrated dual derivative, and the exact energy identity.  The localization
cutoff is constructed automatically from `a < c ≤ d < b`.

This is the interior finite-time form of the abstract version of Evans §5.9.2,
Theorem 3(i): `u ∈ L²(0, T; V)`, `u' ∈ L²(0, T; V*)` gives `u ∈ C([0, T]; H)`;
the endpoints of `(a, b)` are reached in the `EndpointRegularity` files. -/
theorem HasWeakTimeDerivativeOn.exists_continuous_representativeOn
    [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    {a b c d : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b))}
    (h : HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ g t))
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    Nonempty (ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) c d) := by
  obtain ⟨χ, hχ, hχcompact, hχsupp, hχone⟩ :=
    exists_smooth_cutoff_Icc_tsupport_Ioo hac hcd hdb
  exact h.exists_continuous_representativeOn_of_cutoff hcd
    χ hχ hχcompact hχsupp hχone

end GelfandWeakTimeDerivative

end PDE.Analysis.Evolution
