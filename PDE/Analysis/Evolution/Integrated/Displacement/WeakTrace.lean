/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional
public import PDE.Analysis.Evolution.Integrated.WeakEquation
public import PDE.Analysis.Evolution.Time.WeakDerivative.Bounded

/-!
# Ordinary weak displacement derivatives give endpoint time tests

The original weakly continuous trace and the bounded pivot derivative determine
an actual Lipschitz representative. Distributional time derivatives then imply
the existing integrated displacement predicate, including every endpoint time test.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Analysis.Evolution

/-- The ordinary weak derivative and original weak trace imply the integrated
identity. Neither strong continuity nor a trace modulus is an extra hypothesis. -/
theorem HasWeakTimeDerivativeOn.integrated_displacement_of_weak_trace
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {a b : ℝ} (hab : a < b) {T : GelfandTriple (V := V) (H := H)}
    {q : Lp V 2 (volume.restrict (Ioc a b))}
    {v : Lp H 2 (volume.restrict (Ioc a b))} {w : ℝ → H}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ T.inclusion (q t)) (fun t ↦ v t))
    (hw : ∀ ell : StrongDual ℝ H, ContinuousOn (fun t ↦ ell (w t)) (Icc a b))
    (hwae : w =ᵐ[volume.restrict (Ioc a b)] fun t ↦ T.inclusion (q t))
    (hv : MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b))) :
    IsGelfandIntegratedWeakSolution T (fun _ ↦ 0)
      (fun t ↦ T.pivotToDual (v t)) q (w a) := by
  let : MeasurableSpace H := borel _
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ H) := borel _
  let : BorelSpace (StrongDual ℝ H) := ⟨rfl⟩
  let Q := T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) q
  have hQ : (Q : ℝ → H) =ᵐ[volume.restrict (Ioc a b)]
      (fun t ↦ T.inclusion (q t)) := T.inclusion.coeFn_compLpL q
  have hweakQ := hweak.congr_ae_restrict measurableSet_Ioo
    (hQ.symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
    EventuallyEq.rfl
  have hweakW := hweak.congr_ae_restrict measurableSet_Ioo
    (hwae.symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
    EventuallyEq.rfl
  obtain ⟨K, hK⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    ((eLpNorm_exponent_top hv.aestronglyMeasurable).symm ▸ hv.eLpNorm_lt_top)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖v t‖ ≤ (K : ℝ) := by
    filter_upwards [hK.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    exact_mod_cast ht
  have hwcont := (hweakW.lipschitzOnWith_of_weaklyContinuousOn hab hw hbound).continuousOn
  have hG := hweakQ.identity_hasGelfandWeakTimeDerivativeOn hab
  have hI := hG.integrated_solution_of_ae_equation hab (B := fun _ ↦ 0)
    (ell := rieszToDualLp v) hwcont (hwae.trans hQ.symm)
    (fun _ ↦ aestronglyMeasurable_const) 0
    (.of_forall fun _ ↦ by rw [ContinuousLinearMap.opNorm_zero])
    (.of_forall fun _ ↦ by simp)
  have hforce (z : V) (τ : TimeTest a b) :
      (fun t ↦ rieszToDualLp v t (T.inclusion z) * τ.toLp t)
        =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ T.pivotToDual (v t) z * τ.toLp t) := by
    filter_upwards [rieszToDualLp_apply_ae v] with t ht
    rw [ht]
    rfl
  refine ⟨hab, fun _ _ ↦ by simp, ?_, ?_⟩
  · intro z τ
    exact (hI.integrable_forcing (T.inclusion z) τ).congr (hforce z τ)
  · intro z τ
    have hi := hI.equation (T.inclusion z) τ
    have htime : (∫ t in Ioc a b, inner ℝ (Q t) (T.inclusion z) * τ.derivToLp t) =
        ∫ t in Ioc a b, inner ℝ (T.inclusion (q t)) (T.inclusion z) * τ.derivToLp t := by
      apply integral_congr_ae
      filter_upwards [hQ] with t ht
      rw [ht]
    simpa only [GelfandTriple.identity_inclusion_apply, zero_apply, zero_mul, integral_zero,
      add_zero, htime, integral_congr_ae (hforce z τ)] using hi

end PDE.Analysis.Evolution
