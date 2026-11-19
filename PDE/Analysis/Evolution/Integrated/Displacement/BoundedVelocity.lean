/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional
public import PDE.Analysis.Evolution.Integrated.Regularity
public import PDE.Analysis.Evolution.Time.WeakDerivative.Bounded

/-!
# A bounded velocity fixes the displacement trace

The existing integrated displacement identity supplies the initial value as well as
an actual continuous representative. Its pivot-valued derivative is the prescribed
velocity. An essential bound on that velocity gives a Lipschitz trace without a
separate continuity or trace-modulus premise. No acceleration equation is used.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal ENNReal

namespace PDE.Analysis.Evolution

/-- An integrated displacement with an essentially bounded pivot velocity admits
an endpoint-inclusive Lipschitz representative with that same weak derivative. -/
theorem IsGelfandIntegratedWeakSolution.exists_lipschitz_displacement
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {q : Lp V 2 (volume.restrict (Ioc a b))}
    {v : Lp H 2 (volume.restrict (Ioc a b))} {q₀ : H}
    (hq : IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (v t)) q q₀)
    (hv : MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b))) :
    ∃ (Q : ℝ → H) (K : ℝ≥0),
      LipschitzOnWith K Q (Icc a b) ∧ Q a = q₀ ∧
      Q =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ T.inclusion (q t)) ∧
      HasWeakTimeDerivativeOn (Ioo a b) Q (fun t ↦ v t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), ‖v t‖ ≤ K) := by
  let d := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) v
  have hd : (d : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)]
      (fun t ↦ T.pivotToDual (v t)) := T.pivotToDual.coeFn_compLpL v
  have hi := hq.congr_forcing_ae hd.symm
  have hm (z : V) : AEStronglyMeasurable
      (fun _ : ℝ ↦ (0 : V →L[ℝ] StrongDual ℝ V) z)
      (volume.restrict (Ioc a b)) := aestronglyMeasurable_const
  have hb : ∀ᵐ _t ∂volume.restrict (Ioc a b),
      ‖(0 : V →L[ℝ] StrongDual ℝ V)‖ ≤ (0 : ℝ) :=
    Eventually.of_forall fun _ ↦ by rw [ContinuousLinearMap.opNorm_zero]
  obtain ⟨g, E, hg, hinit, hge⟩ :=
    hi.exists_continuousPivotEvolutionOn_initial_L2 hm 0 hb hq.interval_nonempty
  have heq : g = d := by
    apply Lp.ext
    filter_upwards [hge] with t ht
    simpa using ht
  subst g
  have hQcont : ContinuousOn E.representative (Icc a b) := by
    simpa only [uIcc_of_le hq.interval_nonempty.le] using E.continuousOn
  have hQae : E.representative =ᵐ[volume.restrict (Ioc a b)]
      (fun t ↦ T.inclusion (q t)) := by
    have h := E.ae_eq_inclusion
    rw [uIcc_of_le hq.interval_nonempty.le] at h
    exact h.filter_mono (ae_mono (volume.restrict_mono_set Ioc_subset_Icc_self))
  have hweak := hg.pivot_hasWeakTimeDerivativeOn.congr_ae_restrict measurableSet_Ioo
    (hQae.symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
    EventuallyEq.rfl
  obtain ⟨K, hK⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    ((eLpNorm_exponent_top hv.aestronglyMeasurable).symm ▸ hv.eLpNorm_lt_top)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖v t‖ ≤ (K : ℝ) := by
    filter_upwards [hK.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    exact_mod_cast ht
  refine ⟨E.representative, K, ?_, hinit, hQae, hweak, hbound⟩
  exact hweak.lipschitzOnWith_of_weaklyContinuousOn hq.interval_nonempty
    (fun ell ↦ ell.continuous.comp_continuousOn hQcont) hbound

end PDE.Analysis.Evolution
