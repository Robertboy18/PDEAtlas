/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Analysis.Evolution.LionsMagenes.Basic.Primitives
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic.Positivity.Finset

/-!
# Integrated dual derivatives on Gelfand triples

We define the endpoint-inclusive integral representation of a dual time
derivative and derive continuity of the canonical dual representative,
scalar pairing formulas, subinterval restriction, and the almost-everywhere
strong derivative of the dual representative.

For the image of `u` in `V*`, the representation is the formula
`u(t) = u(s) + ∫_s^t u'(τ) dτ` of Evans, §5.9.2, Theorem 2(ii), with `X = V*`, and its
continuity is part (i) of that theorem. Evans derives both from the weak derivative by
mollification; here the integral representation is the definition, and the almost-everywhere
derivative comes from Mathlib's Lebesgue differentiation theorem,
`IntervalIntegrable.ae_hasDerivAt_integral`.

## Main definitions

* `HasIntegratedDualDerivativeOn T u g a b`: `g` is integrable and the image of `u` in `V*` is
  its integral primitive on `[[a, b]]`, endpoints included.

## Main results

* `HasIntegratedDualDerivativeOn.continuousOn_pivotToDual`: the `V*` representative is
  continuous.
* `HasIntegratedDualDerivativeOn.pairing_eq_add_integral`,
  `HasIntegratedDualDerivativeOn.pairing_sub_eq_integral`: the scalar identities against a
  fixed `v ∈ V`.
* `HasIntegratedDualDerivativeOn.norm_pivotToDual_sub_le`: the bound on increments.
* `HasIntegratedDualDerivativeOn.subinterval`: restriction to a subinterval.
* `HasIntegratedDualDerivativeOn.ae_hasDerivAt_pivotToDual`: the `V*` representative has
  derivative `g` almost everywhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 2 (Calculus in an abstract space),
  p. 302. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped InnerProductSpace Interval Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A trajectory has integrated dual derivative `g` on `[[a,b]]` when its
canonical image in `V*` is an integral primitive of `g`.  This formulation
contains endpoint values and is invariant under changes of `g` on null sets. -/
structure HasIntegratedDualDerivativeOn
    (T : GelfandTriple (V := V) (H := H))
    (u : ℝ → H) (g : ℝ → StrongDual ℝ V) (a b : ℝ) : Prop where
  /-- The dual derivative is Bochner integrable on the time interval. -/
  intervalIntegrable : IntervalIntegrable g volume a b
  /-- Integral representation in `V*`, including both endpoints. -/
  eq_add_integral : ∀ t ∈ uIcc a b,
    T.pivotToDual (u t) = T.pivotToDual (u a) + dualPrimitive g a t

namespace HasIntegratedDualDerivativeOn

variable {T : GelfandTriple (V := V) (H := H)}
  {u : ℝ → H} {g : ℝ → StrongDual ℝ V} {a b : ℝ}

/-- The canonical `V*` representative is continuous.  This is the first
time-regularity conclusion in the Lions–Magenes argument. -/
theorem continuousOn_pivotToDual
    (h : HasIntegratedDualDerivativeOn T u g a b) :
    ContinuousOn (fun t ↦ T.pivotToDual (u t)) (uIcc a b) := by
  have hcontinuous : ContinuousOn
      (fun t ↦ T.pivotToDual (u a) + dualPrimitive g a t) (uIcc a b) :=
    continuousOn_const.add (continuousOn_dualPrimitive h.intervalIntegrable)
  apply hcontinuous.congr
  intro t ht
  exact h.eq_add_integral t ht

/-- Weak fundamental theorem of calculus: every fixed `v ∈ V` sees an
ordinary scalar integral identity. -/
theorem pairing_eq_add_integral
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (v : V) {t : ℝ} (ht : t ∈ uIcc a b) :
    inner ℝ (u t) (T.inclusion v) =
      inner ℝ (u a) (T.inclusion v) + ∫ s in a..t, g s v := by
  have heq := DFunLike.congr_fun (h.eq_add_integral t ht) v
  rw [add_apply, GelfandTriple.pivotToDual_apply,
    dualPrimitive_apply
      (h.intervalIntegrable.mono_set (uIcc_subset_uIcc_left ht))] at heq
  exact heq

/-- Two-time weak fundamental theorem of calculus. -/
theorem pairing_sub_eq_integral
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (v : V) {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) :
    inner ℝ (u t) (T.inclusion v) - inner ℝ (u s) (T.inclusion v) =
      ∫ r in s..t, g r v := by
  have has := h.intervalIntegrable.mono_set (uIcc_subset_uIcc_left hs)
  have hat := h.intervalIntegrable.mono_set (uIcc_subset_uIcc_left ht)
  have hst := h.intervalIntegrable.mono_set (uIcc_subset_uIcc hs ht)
  have hp := congrArg (fun q : StrongDual ℝ V ↦ q v)
    (dualPrimitive_sub has hst)
  change dualPrimitive g a t v - dualPrimitive g a s v =
    (∫ r in s..t, g r) v at hp
  rw [dualPrimitive_apply hat, dualPrimitive_apply has,
    ContinuousLinearMap.intervalIntegral_apply hst v] at hp
  rw [pairing_eq_add_integral h v ht, pairing_eq_add_integral h v hs]
  linarith

/-- Norm control of the dual-valued increments. -/
theorem norm_pivotToDual_sub_le
    (h : HasIntegratedDualDerivativeOn T u g a b)
    {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) (hst : s ≤ t) :
    ‖T.pivotToDual (u t) - T.pivotToDual (u s)‖ ≤
      ∫ r in s..t, ‖g r‖ := by
  rw [h.eq_add_integral t ht, h.eq_add_integral s hs]
  have has := h.intervalIntegrable.mono_set (uIcc_subset_uIcc_left hs)
  have hstInt := h.intervalIntegrable.mono_set (uIcc_subset_uIcc hs ht)
  convert norm_dualPrimitive_sub_le has hstInt hst using 1
  abel_nf

/-- Restriction of an integrated dual derivative to any subinterval whose
endpoints lie in the original interval. -/
theorem subinterval
    (h : HasIntegratedDualDerivativeOn T u g a b)
    {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) :
    HasIntegratedDualDerivativeOn T u g s t := by
  have hstSubset : uIcc s t ⊆ uIcc a b := uIcc_subset_uIcc hs ht
  refine {
    intervalIntegrable := h.intervalIntegrable.mono_set hstSubset
    eq_add_integral := ?_
  }
  intro r hr
  have hsr : r ∈ uIcc a b := hstSubset hr
  have has : IntervalIntegrable g volume a s :=
    h.intervalIntegrable.mono_set (uIcc_subset_uIcc_left hs)
  have hsrInt : IntervalIntegrable g volume s r :=
    h.intervalIntegrable.mono_set (uIcc_subset_uIcc hs hsr)
  have hprim : dualPrimitive g a r - dualPrimitive g a s =
      dualPrimitive g s r := by
    simpa only [dualPrimitive] using dualPrimitive_sub has hsrInt
  rw [h.eq_add_integral r hsr, h.eq_add_integral s hs]
  rw [← hprim]
  abel

/--
The canonical dual representative of an integrated Gelfand evolution has
the prescribed strong derivative almost everywhere.

If

`J* u(t) = J* u(a) + ∫ₐᵗ g(r) dr`,

then Banach-valued Lebesgue differentiation gives

`d/dt (J* u(t)) = g(t)`

for almost every `t ∈ (a,b]`.  The right endpoint is immaterial
measure-theoretically; the proof transfers the derivative from the Bochner
primitive on the open interval, where the integral representation holds in a
whole neighbourhood.  Hyperbolic integration by parts uses this
endpoint-compatible strong representative.
-/
theorem ae_hasDerivAt_pivotToDual
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (hab : a < b) :
    ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt (fun s ↦ T.pivotToDual (u s)) (g t) t := by
  have hprimitive :=
    IntervalIntegrable.ae_hasDerivAt_integral
      h.intervalIntegrable
  have hb : ∀ᵐ t ∂volume, t ≠ b := by
    simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hprimitive, hb] with t ht htb
  intro htIoc
  have htIoo : t ∈ Ioo a b :=
    ⟨htIoc.1, lt_of_le_of_ne htIoc.2 htb⟩
  have htIcc : t ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact ⟨htIoc.1.le, htIoc.2⟩
  have hprimDeriv :
      HasDerivAt
        (fun s ↦ T.pivotToDual (u a) + dualPrimitive g a s)
        (g t) t := by
    have hintDeriv :
        HasDerivAt (dualPrimitive g a) (g t) t := by
      change HasDerivAt (fun y ↦ ∫ s in a..y, g s) (g t) t
      exact ht htIcc a left_mem_uIcc
    change HasDerivAt
      ((fun _ : ℝ ↦ T.pivotToDual (u a)) + dualPrimitive g a) (g t) t
    simpa only [zero_add] using
      (hasDerivAt_const t (T.pivotToDual (u a))).add hintDeriv
  apply hprimDeriv.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with s hs
  have hsIcc : s ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact ⟨hs.1.le, hs.2.le⟩
  exact h.eq_add_integral s hsIcc

end HasIntegratedDualDerivativeOn

end PDE.Analysis.Evolution
