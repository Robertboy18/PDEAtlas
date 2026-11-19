/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives

/-!
# The integrated velocity of a weak wave

The initial velocity in the weak time identity determines the constant of integration
in the dual-valued fundamental theorem. The resulting identity applies to every weak
solution, without additional continuity of its pivot velocity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational.IsGelfandWeakWaveSolution

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell acceleration : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
  {u : Lp V 2 (volume.restrict (Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Ioc a b))}
  {q₀ : V} {p₀ : H}

/-- The weak velocity is its prescribed initial value plus the integral of the
acceleration, after the canonical embedding into the dual energy space. -/
theorem pivotVelocity_eq_initial_add_integral_ae
    (h : IsGelfandWeakWaveSolution T B ell u velocity acceleration q₀ p₀) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), T.pivotToDual (velocity t) = T.pivotToDual p₀ + ∫ s in a..t,
      acceleration s := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ V) := borel (StrongDual ℝ V)
  let : BorelSpace (StrongDual ℝ V) := ⟨rfl⟩
  obtain ⟨E, _, hEa⟩ := h.exists_continuousRieszVelocityEvolution
  have hE : E.representative =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ rieszVelocityLp T velocity t := by
    have hsub : volume.restrict (Ioc a b) ≤ volume.restrict (uIcc a b) :=
      volume.restrict_mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc)
    simpa only [GelfandTriple.identity_inclusion_apply] using
      E.ae_eq_inclusion.filter_mono (ae_mono hsub)
  have hR (x : V) :
      (GelfandTriple.identity V).pivotToDual x = InnerProductSpace.toDual ℝ V x := by
    ext y
    rfl
  filter_upwards [hE, rieszVelocityLp_apply_ae T velocity,
    ae_restrict_mem measurableSet_Ioc] with t ht hrt hab
  have hFTC := E.integratedDerivative.eq_add_integral t (Icc_subset_uIcc (Ioc_subset_Icc_self hab))
  rw [ht, hrt, hEa, hR, hR, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply] at hFTC
  exact hFTC

end Hyperbolic.Variational.IsGelfandWeakWaveSolution
