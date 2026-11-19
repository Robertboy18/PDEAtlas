/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.BackwardPrimitive
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.BackwardIntegration

/-!
# Homogeneous backward identities for weak waves

For a weak wave `u` of the homogeneous equation `u'' + B(t) u = 0` with zero initial
displacement and velocity, testing against the backward primitive `v(t) = ∫ₜ^σ u(r) dr` and
integrating by parts gives Evans's identity

`½ ‖u_H(σ)‖²_H + ∫ₐ^σ B(t)(u(t), v(t)) dt = 0`,

where `u_H` is the continuous `H`-valued representative of the displacement. This is the exact
identity at the start of the uniqueness proof in Evans, §7.2.2; the coercive estimate that
follows from it after splitting `B = A + R` is in `BackwardEstimate`.

The identity is stated on an arbitrary subinterval `[c, σ] ⊆ [a, b]` under the hypothesis
that both continuous traces vanish at `c`. The weak wave and its two representatives stay
defined on the whole of `[a, b]`; only the base point of the test moves. This is what allows
the uniqueness argument to restart from each partition point without constructing a new weak
solution on the shorter interval.

## Main results

* `homogeneous_backward_identity_on_subinterval`: the identity on `[c, σ]` for fixed continuous
  displacement and Riesz velocity evolutions with zero traces at `c`.
* `exists_continuousDisplacementEvolution_with_homogeneous_backward_identity`: the
  endpoint-inclusive form on `[a, σ]` for a zero-data homogeneous weak wave, producing the
  continuous displacement evolution together with the identity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, equation (39).
  <https://doi.org/10.1090/gsm/019>
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
Evans's homogeneous backward-test identity on an arbitrary restarted
subinterval.

The weak wave itself is still defined on `[a,b]`, and the two canonical
Lions-Magenes representatives are fixed once on that whole interval.
Given `c ≤ σ` in `[a,b]`, zero displacement and velocity traces at `c`
yield

`1/2 ‖u_H(σ)‖² + ∫_c^σ B(t)(u(t), ∫_t^σ u(r) dr) dt = 0`.

This is equation (39) of Evans, §7.2.2, with the initial time translated from `a` to `c`.
It is how the uniqueness argument restarts on `[c, σ]`: no new `Lp` solution is
constructed and no new representatives are chosen on the shorter interval.
-/
theorem homogeneous_backward_identity_on_subinterval [CompleteSpace V]
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (Edisplacement : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    (Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
      (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b)
    {c σ : ℝ} (hc : c ∈ Set.Icc a b) (hσ : σ ∈ Set.Icc a b) (hcσ : c ≤ σ)
    (hdisplacementC : Edisplacement.representative c = 0)
    (hvelocityC : Evelocity.representative c = 0) :
    (1 / 2 : ℝ) * ‖Edisplacement.representative σ‖ ^ 2 +
        ∫ t in c..σ, B t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t) = 0 := by
  have hsub : uIoc c σ ⊆ Ioc a b := by
    rw [uIoc_of_le hcσ]
    exact Ioc_subset_Ioc hc.1 hσ.2
  have hmeasure := (volume : Measure ℝ).restrict_mono_set hsub
  have hpairing : (fun t ↦ T.pivotToDual.compLpL 2 _ velocity t (u t))
      =ᵐ[volume.restrict (uIoc c σ)] fun t ↦ inner ℝ (Evelocity.representative t) (u t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
        (T.pivotToDual.coeFn_compLpL velocity),
      ae_restrict_of_ae_restrict_of_subset (hsub.trans (Ioc_subset_Icc_self.trans
        Icc_subset_uIcc)) Evelocity.ae_eq_inclusion,
      ae_restrict_of_ae_restrict_of_subset hsub (rieszVelocityLp_apply_ae T velocity)]
      with t hdual hrep hriesz
    rw [hdual, hrep, GelfandTriple.identity_inclusion_apply, hriesz,
      InnerProductSpace.toDual_symm_apply]
  have hacc : IntervalIntegrable
      (fun t ↦ acceleration t (backwardTimePrimitive (fun r ↦ u r) σ t)) volume c σ :=
    intervalIntegrable_iff.2 (((integrable_dual_pairing acceleration
      (backwardTimePrimitiveLp u hab.le σ hσ)).mono_measure hmeasure).congr (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
          (backwardTimePrimitiveLp_apply_ae u hab.le σ hσ)] with t ht
        rw [ht]))
  have hparts := backwardPrimitive_integrationByParts Evelocity hab
    (intervalIntegrable_coeFn_L2_restrict_Ioc u hab.le) hσ c σ hc hσ
  rw [intervalIntegral.integral_sub hacc (intervalIntegrable_iff.2
      (((integrable_dual_pairing _ u).mono_measure hmeasure).congr hpairing)),
    intervalIntegral.integral_congr_ae_restrict (g := fun t ↦
      -B t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h.equationAE,
          ae_restrict_of_ae_restrict_of_subset hsub (Lp.coeFn_zero (StrongDual ℝ V) 2 _)]
          with t heq hzero
        rw [hzero] at heq
        rw [eq_neg_of_add_eq_zero_left heq, neg_apply]), intervalIntegral.integral_neg] at hparts
  have henergy := Edisplacement.energyIdentity c σ (Icc_subset_uIcc hc) (Icc_subset_uIcc hσ)
  rw [intervalIntegral.integral_congr_ae_restrict hpairing, hdisplacementC] at henergy
  simp only [hvelocityC, backwardTimePrimitive_terminal, inner_zero_left, inner_zero_right,
    sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hparts henergy
  linarith

/--
Exact backward-test identity for a homogeneous zero-data weak wave.

Let `u` solve `uₜₜ + B(t)u = 0` with zero displacement and velocity traces.
For every `σ ∈ [a,b]`, Evans's test

`v(t) = ∫ₜ^σ u(r) dr`

gives

`1/2 ‖u_H(σ)‖² + ∫ₐ^σ B(t)(u(t),v(t)) dt = 0`,

where `u_H` is the canonical continuous pivot representative. This is the
abstract version of equation (39) in the proof of Evans, §7.2.2, Theorem 4, with the first
term integrated and `u_H` at the endpoint `σ`. The coercive estimate (40) follows from it by
splitting `B = A + R` and applying the nonautonomous quadratic-form chain rule, in
`BackwardEstimate`.
-/
theorem exists_continuousDisplacementEvolution_with_homogeneous_backward_identity
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace (StrongDual ℝ V)]
    [BorelSpace (StrongDual ℝ V)] [CompleteSpace V] [CompleteSpace H]
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b) {σ : ℝ}
    (hσ : σ ∈ Set.Icc a b) :
    ∃ E : ContinuousPivotEvolutionOn T (fun t ↦ u t)
        (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b,
      E.representative a = 0 ∧
        (1 / 2 : ℝ) * ‖E.representative σ‖ ^ 2 +
            ∫ t in a..σ, B t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t) = 0 := by
  obtain ⟨Edisplacement, hdisplacementInitial⟩ := h.exists_continuousDisplacementEvolution
  obtain ⟨Evelocity, -, hvelocityInitial⟩ := h.exists_continuousRieszVelocityEvolution
  have hdisplacementZero : Edisplacement.representative a = 0 := by
    simpa using hdisplacementInitial
  exact ⟨Edisplacement, hdisplacementZero, h.homogeneous_backward_identity_on_subinterval hab
    Edisplacement Evelocity ⟨le_rfl, hab.le⟩ hσ hσ.1 hdisplacementZero
    (by rw [hvelocityInitial]; simp)⟩

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
