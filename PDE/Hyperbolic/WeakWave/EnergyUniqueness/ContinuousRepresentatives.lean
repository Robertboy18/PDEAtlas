/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# Continuous representatives of weak waves

A weak wave `(u, velocity, acceleration)` in the energy class
`L²(a, b; V) × L²(a, b; H) × L²(a, b; V*)` has two derivative relations, `u' = J* velocity` and
`(J* velocity)' = acceleration`, each of the Lions-Magenes type "`f ∈ L²(V)`, `f' ∈ L²(V*)`".
The Lions-Magenes theorem then gives continuous `H`-valued representatives with the energy
identity `‖f(t)‖²_H - ‖f(s)‖²_H = 2 ∫ₛᵗ ⟨f'(r), f(r)⟩ dr`. We construct those
representatives for a weak wave, including at the initial endpoint `a`, where they take the
prescribed initial traces `J q₀` and `p₀`. This is the regularity statement
`u ∈ C([0, T]; L²)`, `u' ∈ C([0, T]; H⁻¹)` of the Remark in Evans, §7.2.1, in abstract form.

The velocity lives in the pivot space `H`, whose derivative is only `V*`-valued, so it does not
fit the triple `V ↪ H ↪ V*` directly. The device used is Riesz transport: the functional
`J* velocity(t) ∈ V*` has a Riesz representative in `V`, and the identity triple `V ↪ V ↪ V*`
applies to that `L²(a, b; V)` class with derivative `acceleration`.

## Main results

* `rieszVelocityLp`, `rieszVelocityLp_apply_ae`, `rieszVelocityLp_pairing_ae`: the Riesz
  transported velocity in `L²(a, b; V)` and its almost-everywhere description; pairing it
  with `w ∈ V` recovers `⟪velocity(t), J w⟫_H`.
* `exists_continuousRieszVelocityEvolution`: a continuous `V`-valued representative of the
  Riesz velocity on `[a, b]` with derivative `acceleration` and initial value the Riesz
  representative of `J* p₀`.
* `exists_continuousDisplacementEvolution`: a continuous `H`-valued representative of the
  displacement on `[a, b]` with derivative `J* velocity` and initial value `J q₀`.
* `continuousRieszVelocity_eq_zero_at_of_displacement_eq_zero`: if the continuous displacement
  vanishes on `[d, c]` with `d < c`, the continuous Riesz velocity vanishes at `c`. This is
  the trace step of the restart argument in the uniqueness proof.

## Implementation notes

No pointwise value of an arbitrary `Lp` representative is ever evaluated. Endpoint statements
refer to the continuous representatives stored in `ContinuousPivotEvolutionOn`, and the
almost-everywhere link between the two velocity descriptions is upgraded to the endpoint by
continuity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorems 2 and 3, and §7.2.1 (the Remark after
  the definition of a weak solution).
  <https://doi.org/10.1090/gsm/019>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*, Vol. I,
  Springer, 1972, Chapter 1.
  <https://doi.org/10.1007/978-3-642-65161-8_1>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}
/--
The velocity, represented in the energy Hilbert space by Riesz transport.

The weak-wave velocity naturally belongs to the pivot space `H`, but its
time derivative belongs to `V*`.  The canonical functional
`T.pivotToDual (velocity t)` therefore has a Riesz representative in `V`.
Viewing that representative in `L²(a,b;V)` lets the identity Gelfand
triple `V ↪ V` recover its continuous time trace.
-/
noncomputable def rieszVelocityLp
    {μ : Measure ℝ}
    [CompleteSpace V]
    (T : GelfandTriple (V := V) (H := H))
    (velocity : Lp H 2 μ) :
    Lp V 2 μ :=
  PDE.Analysis.Evolution.rieszFromDualLp
    (T.pivotToDual.compLpL 2 μ velocity)

/-- Pointwise description of `rieszVelocityLp`, valid almost everywhere. -/
theorem rieszVelocityLp_apply_ae {μ : Measure ℝ} [CompleteSpace V]
    (T : GelfandTriple (V := V) (H := H)) (velocity : Lp H 2 μ) :
    (rieszVelocityLp T velocity : ℝ → V) =ᵐ[μ] fun t ↦
      (InnerProductSpace.toDual ℝ V).symm (T.pivotToDual (velocity t)) := by
  have hRiesz := PDE.Analysis.Evolution.rieszFromDualLp_apply_ae
      (T.pivotToDual.compLpL 2 μ velocity)
  have hDual := T.pivotToDual.coeFn_compLpL velocity
  filter_upwards [hRiesz, hDual] with t hRieszT hDualT
  change PDE.Analysis.Evolution.rieszFromDualLp (T.pivotToDual.compLpL 2 μ velocity) t =
      (InnerProductSpace.toDual ℝ V).symm (T.pivotToDual (velocity t))
  rw [hRieszT, hDualT]

/--
The Riesz velocity has exactly the original pivot pairing against every
energy-space test vector.
-/
theorem rieszVelocityLp_pairing_ae {μ : Measure ℝ} [CompleteSpace V]
    (T : GelfandTriple (V := V) (H := H)) (velocity : Lp H 2 μ) (w : V) :
    (fun t ↦ inner ℝ (rieszVelocityLp T velocity t) w) =ᵐ[μ]
      fun t ↦ inner ℝ (velocity t) (T.inclusion w) := by
  filter_upwards [rieszVelocityLp_apply_ae T velocity] with t ht
  rw [ht, InnerProductSpace.toDual_symm_apply, GelfandTriple.pivotToDual_apply]

/--
The weak velocity possesses a canonical continuous Riesz representative on
the closed time interval, with the prescribed initial velocity and
integrated derivative equal to the wave acceleration.

This is the endpoint continuity needed in Evans, §7.2.2.  The pivot velocity
itself need not be `V`-valued.  Instead the theorem represents the
functional `w ↦ ⟪velocity(t), Jw⟫_H` by a vector of `V`, applies the identity
Gelfand triple, and transports the initial trace through the Riesz
isomorphism.  Thus no endpoint value of the original `Lp H` representative
is ever used.
-/
theorem exists_continuousRieszVelocityEvolution [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) :
    ∃ E : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
        (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b,
      HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity V)
          (rieszVelocityLp T velocity) acceleration ∧
        E.representative a = (InnerProductSpace.toDual ℝ V).symm (T.pivotToDual p₀) := by
  have hsolution : IsGelfandIntegratedWeakSolution (GelfandTriple.identity V)
      (fun _ ↦ 0) (fun t ↦ acceleration t) (rieszVelocityLp T velocity)
      ((InnerProductSpace.toDual ℝ V).symm (T.pivotToDual p₀)) := by
    refine ⟨h.interval_nonempty, by simp, fun w τ ↦ integrable_dualTimeTest w τ.toLp acceleration,
      fun w τ ↦ ?_⟩
    simp only [GelfandTriple.identity_inclusion_apply, zero_apply, zero_mul, integral_zero,
      add_zero, InnerProductSpace.toDual_symm_apply, GelfandTriple.pivotToDual_apply]
    rw [integral_congr_ae (by
      filter_upwards [rieszVelocityLp_pairing_ae T velocity w] with t ht
      rw [ht] : (fun t ↦ inner ℝ (rieszVelocityLp T velocity t) w * τ.derivToLp t)
        =ᵐ[volume.restrict (Set.Ioc a b)] _)]
    exact h.velocityIdentity w τ
  obtain ⟨g, E, hweak, hinitial, hg⟩ := hsolution.exists_continuousPivotEvolutionOn_initial_L2
    (fun v ↦ (aestronglyMeasurable_const (b := (0 : V →L[ℝ] StrongDual ℝ V))
      (μ := volume.restrict (Set.Ioc a b))).apply_continuousLinearMap v) 0
    (.of_forall fun _ ↦ (norm_zero (E := V →L[ℝ] StrongDual ℝ V)).le) h.interval_nonempty
  obtain rfl : g = acceleration := Lp.ext (hg.mono fun t ht ↦ by simpa using ht)
  exact ⟨E, hweak, hinitial⟩

/--
The weak displacement together with the pivot velocity forms an
endpoint-inclusive Lions-Magenes evolution.

The derivative stored in the evolution is the canonical `L²(V*)` image of
the pivot velocity.  Consequently its energy identity is exactly

`‖u_H(t)‖² - ‖u_H(s)‖²
  = 2 ∫ₛᵗ ⟪velocity(r), J u(r)⟫_H dr`.

This stronger form underlies
`exists_displacementContinuousRepresentative`; stating it separately
avoids reconstructing the displacement energy law in every hyperbolic
argument.
-/
theorem exists_continuousDisplacementEvolution [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    [CompleteSpace H] (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) :
    ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ u t)
        (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b,
      E.representative a = T.inclusion q₀ := by
  obtain ⟨g, E, -, hinitial, hg⟩ := (h.displacementIdentity.congr_forcing_ae
    (T.pivotToDual.coeFn_compLpL (p := 2) (μ := volume.restrict (Set.Ioc a b))
      velocity).symm).exists_continuousPivotEvolutionOn_initial_L2
    (fun v ↦ (aestronglyMeasurable_const (b := (0 : V →L[ℝ] StrongDual ℝ V))
      (μ := volume.restrict (Set.Ioc a b))).apply_continuousLinearMap v) 0
    (.of_forall fun _ ↦ (norm_zero (E := V →L[ℝ] StrongDual ℝ V)).le) h.interval_nonempty
  obtain rfl : g = T.pivotToDual.compLpL 2 _ velocity :=
    Lp.ext (hg.mono fun t ht ↦ by simpa using ht)
  exact ⟨E, hinitial⟩

/-- Any continuous pivot representative of the original weak displacement
takes the prescribed initial position. -/
theorem continuousDisplacement_eq_initial [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    [CompleteSpace H] (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀)
    {q : ℝ → H} (hq : ContinuousOn q (Icc a b))
    (hae : q =ᵐ[volume.restrict (Ioc a b)] fun t ↦ T.inclusion (u t)) :
    q a = T.inclusion q₀ := by
  obtain ⟨E, hE⟩ := h.exists_continuousDisplacementEvolution
  have hab := h.interval_nonempty
  have hEae := E.ae_eq_inclusion
  have hcont := E.continuousOn
  rw [uIcc_of_le hab.le] at hEae hcont
  exact (Measure.eqOn_Icc_of_ae_eq volume hab.ne
    (Filter.EventuallyEq.trans ((ae_restrict_congr_set Ioc_ae_eq_Icc).1 hae) hEae.symm) hq hcont
    (left_mem_Icc.2 hab.le)).trans hE

/-- A continuous representative of the original pivot velocity takes the
prescribed initial velocity. Its trace is identified through the injective Riesz transport. -/
theorem continuousVelocity_eq_initial [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)] [CompleteSpace V]
    (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) {p : ℝ → H}
    (hp : ContinuousOn p (Icc a b)) (hae : p =ᵐ[volume.restrict (Ioc a b)] velocity) :
    p a = p₀ := by
  obtain ⟨E, _, hE⟩ := h.exists_continuousRieszVelocityEvolution
  have hab := h.interval_nonempty
  have hEae := E.ae_eq_inclusion
  have hcont := E.continuousOn
  rw [uIcc_of_le hab.le] at hEae hcont
  have heq : (fun t ↦ (InnerProductSpace.toDual ℝ V).symm (T.pivotToDual (p t)))
      =ᵐ[volume.restrict (Icc a b)] E.representative := by
    filter_upwards [(ae_restrict_congr_set Ioc_ae_eq_Icc).1 hae,
      (ae_restrict_congr_set Ioc_ae_eq_Icc).1 (rieszVelocityLp_apply_ae T velocity), hEae]
      with t ht hr hEt
    rw [hEt, GelfandTriple.identity_inclusion_apply, hr, ht]
  exact T.pivotToDual_injective ((InnerProductSpace.toDual ℝ V).symm.injective
    ((Measure.eqOn_Icc_of_ae_eq volume hab.ne heq
      ((InnerProductSpace.toDual ℝ V).symm.continuous.comp_continuousOn
        (T.pivotToDual.continuous.comp_continuousOn hp)) hcont (left_mem_Icc.2 hab.le)).trans hE))

/--
Vanishing displacement on a nondegenerate time interval forces the canonical
velocity trace to vanish at the right endpoint.

This is the trace step in Evans's restart argument.  The displacement
evolution differentiates in `V*` to the pivot image of the weak velocity.
If its continuous representative is identically zero on `[d,c]`, the
Lions-Magenes derivative-uniqueness theorem therefore makes that pivot
velocity zero almost everywhere on the interval.  The continuous Riesz
velocity representative agrees almost everywhere with the same functional,
so continuity upgrades the conclusion to the endpoint value `c`.

No value of an arbitrary `Lp` representative is evaluated at `c`.
-/
theorem continuousRieszVelocity_eq_zero_at_of_displacement_eq_zero [CompleteSpace V] (hab : a < b)
    {d c : ℝ} (hd : d ∈ Set.Icc a b) (hdc : d < c) (hc : c ∈ Set.Icc a b)
    (Edisplacement : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    (Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
      (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b)
    (hzero : ∀ t ∈ Set.Icc d c, Edisplacement.representative t = 0) :
    Evelocity.representative c = 0 := by
  have hIoc : Set.Ioo d c ⊆ Set.Ioc a b := fun t ht ↦ ⟨hd.1.trans_lt ht.1, ht.2.le.trans hc.2⟩
  have hUIcc : Set.Icc d c ⊆ Set.uIcc a b := fun t ht ↦ by
    rw [Set.uIcc_of_le hab.le]
    exact ⟨hd.1.trans ht.1, ht.2.trans hc.2⟩
  have hvelocityZeroIoo : Evelocity.representative =ᵐ[volume.restrict (Set.Ioo d c)]
      (fun _ ↦ (0 : V)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Icc_self.trans hUIcc)
        Evelocity.ae_eq_inclusion,
      ae_restrict_of_ae_restrict_of_subset hIoc (rieszVelocityLp_apply_ae T velocity),
      ae_restrict_of_ae_restrict_of_subset hIoc (T.pivotToDual.coeFn_compLpL velocity),
      ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self
        (Edisplacement.integratedDerivative_ae_eq_zero_of_representative_eq_zero hdc
          (Set.Icc_subset_uIcc hd) (Set.Icc_subset_uIcc hc) hzero)] with t hE hriesz hdual hzeroDual
    rw [hE, GelfandTriple.identity_inclusion_apply, hriesz, ← hdual, hzeroDual, map_zero]
  exact Measure.eqOn_Icc_of_ae_eq volume hdc.ne
    ((ae_restrict_congr_set Ioo_ae_eq_Icc).1 hvelocityZeroIoo)
    (Evelocity.continuousOn.mono hUIcc) continuousOn_const (Set.right_mem_Icc.mpr hdc.le)

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
