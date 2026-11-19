/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Bounded

/-!
# Constructing the original Sobolev time trace

A distributional derivative in L² gives a continuous representative up to both
endpoints. An L∞ bound on that derivative makes the representative Lipschitz.
No continuous representative is assumed. Uniqueness on the closed interval ensures
that its endpoint is the Sobolev trace, independent of all chosen representatives.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

/-- Construct the unique continuous time representative from the ordinary weak
derivative. An essential bound produces its Lipschitz constant. -/
theorem exists_unique_lipschitz_representative_of_memLp_top
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {a b : ℝ} (hab : a < b) {u : ℝ → X}
    {v : Lp X 2 (volume.restrict (Ioc a b))}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u (fun t ↦ v t))
    (hv : MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b))) :
    ∃ (Q : ℝ → X) (K : ℝ≥0), Continuous Q ∧
      LipschitzOnWith K Q (Icc a b) ∧
      u =ᵐ[volume.restrict (Ioc a b)] Q ∧
      HasWeakTimeDerivativeOn (Ioo a b) Q (fun t ↦ v t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), ‖v t‖ ≤ K) ∧
      ∀ w : ℝ → X, ContinuousOn w (Icc a b) →
        w =ᵐ[volume.restrict (Ioc a b)] u → EqOn w Q (Icc a b) := by
  have hvintoc : IntegrableOn (fun t ↦ v t) (Ioc a b) :=
    (Lp.memLp v).integrable (by norm_num)
  have hvint := hvintoc.mono_set Ioo_subset_Ioc_self
  obtain ⟨Q, hQ, huQ, _⟩ := hweak.exists_continuous_representative_Icc hab hvint
  have hweakQ := hweak.congr_ae_restrict measurableSet_Ioo huQ EventuallyEq.rfl
  have huQ' : u =ᵐ[volume.restrict (Ioc a b)] Q := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at huQ
  obtain ⟨K, hK⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    ((eLpNorm_exponent_top hv.aestronglyMeasurable).symm ▸ hv.eLpNorm_lt_top)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖v t‖ ≤ (K : ℝ) := by
    filter_upwards [hK.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    exact_mod_cast ht
  refine ⟨Q, K, hQ, hweakQ.lipschitzOnWith_of_weaklyContinuousOn hab
    (fun ell ↦ (ell.continuous.comp hQ).continuousOn) hbound, huQ', hweakQ, hbound, ?_⟩
  intro w hw hwu
  apply Measure.eqOn_Icc_of_ae_eq volume hab.ne ?_ hw hQ.continuousOn
  exact (ae_restrict_congr_set Ioc_ae_eq_Icc).1 (hwu.trans huQ')

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
