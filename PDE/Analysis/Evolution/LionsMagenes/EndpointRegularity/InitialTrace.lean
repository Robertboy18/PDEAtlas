/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Initial-trace identity for endpoint-regular evolutions

Testing an endpoint-inclusive integrated derivative with the affine initial
hat recovers the left endpoint pairing. This trace calculation identifies
prescribed initial data in weak evolution equations.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section InitialTrace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [CompleteSpace V] in
/-- Endpoint integration by parts for every admissible scalar time test. -/
theorem ContinuousPivotEvolutionOn.timeTest_boundary_identity
    {T : GelfandTriple (V := V) (H := H)} {a b : ℝ}
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOn T u g a b) (hab : a ≤ b)
    (v : V) (τ : TimeTest a b) :
    -(∫ t in a..b, inner ℝ (E.representative t) (T.inclusion v) * τ.derivFun t) =
      (∫ t in a..b, g t v * τ.toFun t) +
        inner ℝ (E.representative a) (T.inclusion v) * τ.toFun a := by
  let q : ℝ → ℝ := fun t ↦ g t v
  let F : ℝ → ℝ := fun t ↦
    inner ℝ (E.representative a) (T.inclusion v) + ∫ r in a..t, q r
  let ev : StrongDual ℝ V →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ) v
  have hq : IntervalIntegrable q volume a b :=
    ⟨ev.integrable_comp E.integratedDerivative.intervalIntegrable.1,
      ev.integrable_comp E.integratedDerivative.intervalIntegrable.2⟩
  have hF_eq (t : ℝ) (ht : t ∈ uIcc a b) :
      F t = inner ℝ (E.representative t) (T.inclusion v) :=
    (E.integratedDerivative.pairing_eq_add_integral v ht).symm
  have hprim := hq.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ ↦ inner ℝ (E.representative a) (T.inclusion v)) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F a b := hconst.add hprim
  have hFderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt F (q t) t := by
    filter_upwards [hq.ae_hasDerivAt_integral.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioc] with t ht htI
    have htIcc : t ∈ uIcc a b := by
      simpa only [uIcc_of_le hab] using (show t ∈ Icc a b from ⟨htI.1.le, htI.2⟩)
    exact (ht htIcc a left_mem_uIcc).const_add _
  have hp := τ.integrationByParts_inner hab (1 : ℝ) hFAC hFderiv
  simp only [Real.inner_apply, mul_one] at hp
  have hleft : (∫ t in a..b, F t * τ.derivFun t) =
      ∫ t in a..b, inner ℝ (E.representative t) (T.inclusion v) * τ.derivFun t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change F t * τ.derivFun t = _
    rw [hF_eq t ht]
  rw [hleft, hF_eq a left_mem_uIcc] at hp
  exact hp

omit [CompleteSpace V] in
/-- The affine endpoint test recovers the initial pivot pairing. -/
theorem ContinuousPivotEvolutionOn.initialHat_boundary_identity
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOn T u g a b) (hab : a < b) (v : V) :
    -(∫ t in a..b,
        inner ℝ (E.representative t) (T.inclusion v) *
          (TimeTest.initialHat a b).derivFun t) =
      (∫ t in a..b, g t v * (TimeTest.initialHat a b).toFun t) +
        inner ℝ (E.representative a) (T.inclusion v) := by
  simpa only [TimeTest.initialHat_initial hab, mul_one] using
    E.timeTest_boundary_identity hab.le v (TimeTest.initialHat a b)

end InitialTrace

end PDE.Analysis.Evolution
