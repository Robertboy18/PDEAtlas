/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Duhamel

/-!
# Fundamental solutions on closed time intervals

For `B` continuous on `[a, b]`, `fundamentalSolutionIcc` is a fundamental solution
on `[a, b]`, with derivatives taken within the interval and initial time any
`t₀ ∈ [a, b]`. It is the whole-line solution for the coefficient extended by its
endpoint values, restricted to `[a, b]`. For forcing `f` continuous on `[a, b]`, the
variation-of-constants solution solves `u' = B(t) u + f(t)` within `[a, b]` and
equals `U(t, s) x + ∫ₛᵗ U(t, r) f(r) dr` for all `s, t ∈ [a, b]`. Two functions
continuous on `[a, b]` that solve the equation on `(a, b)` and agree at `a` agree
on `[a, b]`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- Construct inverse fundamental paths from a coefficient continuous on a closed interval.
The initial time may be either endpoint or any interior point. -/
def fundamentalSolutionIcc {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {B : ℝ → A} {a b : ℝ} (hB : ContinuousOn B (Icc a b)) (t₀ : Icc a b) :
    FundamentalSolution B t₀ (Icc a b) :=
  let C : C(Icc a b, A) := ⟨fun t ↦ B t, continuousOn_iff_continuous_domRestrict.mp hB⟩
  ((fundamentalSolutionOn C t₀).restrict (subset_univ (Icc a b))).congr
    (fun _ ht ↦ IccExtend_of_mem _ C ht)

namespace FundamentalSolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {B : ℝ → E →L[ℝ] E} {t₀ a b : ℝ} (S : FundamentalSolution B t₀ (Icc a b))

/-- Variation of constants solves the forced equation throughout a closed interval,
using a right derivative at the left endpoint and a left derivative at the right.
The forcing only needs continuity on the interval. -/
theorem hasDerivWithinAt_solution {f : ℝ → E} (hf : ContinuousOn f (Icc a b))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasDerivWithinAt (S.solution f s x)
      (B t (S.solution f s x t) + f t) (Icc a b) t := by
  have hq : ContinuousOn (fun r ↦ S.backward r (f r)) (Icc a b) :=
    S.continuousOn_backward.clm_apply hf
  have hinterval : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht
  have hint : IntervalIntegrable (fun r ↦ S.backward r (f r)) volume s t :=
    (hq.mono hinterval).intervalIntegrable
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hprim := (intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc a b) (t := Icc a b) hint
    (hq.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hq t ht)).const_add
      (S.backward s x)
  convert! (S.forward_hasDerivWithinAt t ht).clm_apply hprim using 1
  simp only [solution, mul_apply_eq_comp,
    ← mul_apply_eq_comp (S.forward t) (S.backward t),
    S.forward_mul_backward t ht]
  rfl

/-- On a closed time interval, variation of constants equals the propagator formula
for any two endpoints, in either time direction. -/
theorem solution_eq_propagator_add_integral_on {f : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    S.solution f s x t =
      S.propagator t s x + ∫ r in s..t, S.propagator t r (f r) := by
  have hq : IntervalIntegrable (fun r ↦ S.backward r (f r)) volume s t :=
    ((S.continuousOn_backward.clm_apply hf).mono (uIcc_subset_Icc hs ht)).intervalIntegrable
  simp only [solution, propagator, mul_apply_eq_comp, map_add]
  rw [(S.forward t).intervalIntegral_comp_comm hq]

include S in
/-- Classical solutions on a closed interval are unique from their left endpoint data:
two functions continuous on `[a, b]` that solve `u' = B(t) u + f(t)` on `(a, b)` and
agree at `a` agree on `[a, b]`. -/
theorem eqOn_of_hasDerivWithinAt {u v f : ℝ → E}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hf : ContinuousOn f (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivWithinAt u (B t (u t) + f t) (Icc a b) t)
    (hdv : ∀ t ∈ Ioo a b, HasDerivWithinAt v (B t (v t) + f t) (Icc a b) t)
    (hinit : u a = v a) : EqOn u v (Icc a b) := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hsub' : Ioo a t ⊆ Ioo a b := Ioo_subset_Ioo le_rfl ht.2
  have hu' := S.eq_solution_of_hasDerivWithinAt_of_subset ht.1 hsub
    (hu.mono hsub) (hf.mono hsub) (fun r hr ↦ (hdu r (hsub' hr)).mono hsub)
  have hv' := S.eq_solution_of_hasDerivWithinAt_of_subset ht.1 hsub
    (hv.mono hsub) (hf.mono hsub) (fun r hr ↦ (hdv r (hsub' hr)).mono hsub)
  rw [hu', hv', hinit]

end FundamentalSolution

end PDE.Analysis.Evolution
