/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.PivotDerivative
public import PDE.Analysis.Evolution.LionsMagenes.Basic.IntegratedDerivative
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Continuity of integrated Gelfand evolutions

Continuity and uniqueness consequences of an integrated dual derivative: the
dense-range weak-to-strong continuity argument, energy-representation criteria,
and the lifting of pivot-represented dual derivatives to Bochner integral and
almost-everywhere derivative formulas.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped InnerProductSpace Interval Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Continuity of pairings against the dense energy space extends to every
pivot-space test vector, provided the trajectory has the uniform energy bound
available in the Lions–Magenes argument. -/
theorem continuousOn_inner_of_denseRange
    (T : GelfandTriple (V := V) (H := H))
    {w : ℝ → H} {S : Set ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ t ∈ S, ‖w t‖ ≤ M)
    (htest : ∀ v : V,
      ContinuousOn (fun t ↦ inner ℝ (w t) (T.inclusion v)) S)
    (z : H) :
    ContinuousOn (fun t ↦ inner ℝ (w t) z) S := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hden : 0 < 4 * (M + 1) := by positivity
  obtain ⟨v, hv⟩ := T.denseRange.exists_dist_lt z (div_pos hε hden)
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousWithinAt_iff.mp (htest v t ht) (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxt
  have hmid := hcont hx hxt
  have hxerr :
      dist (inner ℝ (w x) z) (inner ℝ (w x) (T.inclusion v)) ≤
        M * dist z (T.inclusion v) := by
    rw [dist_eq_norm, ← inner_sub_right]
    calc
      ‖inner ℝ (w x) (z - T.inclusion v)‖ ≤
          ‖w x‖ * ‖z - T.inclusion v‖ := norm_inner_le_norm _ _
      _ ≤ M * dist z (T.inclusion v) := by
        rw [dist_eq_norm]
        gcongr
        exact hbound x hx
  have hterr :
      dist (inner ℝ (w t) (T.inclusion v)) (inner ℝ (w t) z) ≤
        M * dist z (T.inclusion v) := by
    rw [dist_eq_norm, ← inner_sub_right]
    calc
      ‖inner ℝ (w t) (T.inclusion v - z)‖ ≤
          ‖w t‖ * ‖T.inclusion v - z‖ := norm_inner_le_norm _ _
      _ ≤ M * dist z (T.inclusion v) := by
        rw [dist_comm, dist_eq_norm]
        gcongr
        exact hbound t ht
  have happrox : 2 * M * dist z (T.inclusion v) < ε / 2 := by
    have hscaled : (4 * (M + 1)) * dist z (T.inclusion v) < ε := by
      simpa [mul_comm] using (lt_div_iff₀ hden).mp hv
    have hd : 0 ≤ dist z (T.inclusion v) := dist_nonneg
    nlinarith
  calc
    dist (inner ℝ (w x) z) (inner ℝ (w t) z) ≤
        dist (inner ℝ (w x) z) (inner ℝ (w x) (T.inclusion v)) +
          dist (inner ℝ (w x) (T.inclusion v)) (inner ℝ (w t) z) :=
      dist_triangle _ _ _
    _ ≤ dist (inner ℝ (w x) z) (inner ℝ (w x) (T.inclusion v)) +
          (dist (inner ℝ (w x) (T.inclusion v))
              (inner ℝ (w t) (T.inclusion v)) +
            dist (inner ℝ (w t) (T.inclusion v)) (inner ℝ (w t) z)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by nlinarith

/-- In a real Hilbert space, weak continuity together with norm continuity
implies strong continuity. -/
theorem continuousOn_of_norm_of_inner
    {w : ℝ → H} {S : Set ℝ}
    (hnorm : ContinuousOn (fun t ↦ ‖w t‖) S)
    (hpair : ∀ z : H, ContinuousOn (fun t ↦ inner ℝ (w t) z) S) :
    ContinuousOn w S := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hsqcont : ContinuousWithinAt (fun x ↦ ‖w x - w t‖ ^ 2) S t := by
    have hright : ContinuousWithinAt
        (fun x ↦ ‖w x‖ ^ 2 - 2 * inner ℝ (w x) (w t) + ‖w t‖ ^ 2) S t :=
      ((hnorm t ht).pow 2).sub ((hpair (w t) t ht).const_mul 2) |>.add
        continuousWithinAt_const
    apply hright.congr_of_eventuallyEq
    · filter_upwards with x
      exact norm_sub_sq_real (w x) (w t)
    · exact norm_sub_sq_real (w t) (w t)
  have hsqzero : ‖w t - w t‖ ^ 2 = 0 := by simp
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousWithinAt_iff.mp hsqcont (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxt
  have hsquare := hclose hx hxt
  rw [hsqzero, Real.dist_0_eq_abs] at hsquare
  rw [dist_eq_norm]
  have hnonneg : 0 ≤ ‖w x - w t‖ := norm_nonneg _
  have habs : |‖w x - w t‖ ^ 2| = ‖w x - w t‖ ^ 2 :=
    abs_of_nonneg (sq_nonneg _)
  rw [habs] at hsquare
  nlinarith

omit [InnerProductSpace ℝ H] in
/-- Continuity of the squared energy is enough to obtain continuity of the
norm.  This is the form produced directly by the Lions–Magenes identity. -/
theorem continuousOn_norm_of_sq
    {w : ℝ → H} {S : Set ℝ}
    (hsq : ContinuousOn (fun t ↦ ‖w t‖ ^ 2) S) :
    ContinuousOn (fun t ↦ ‖w t‖) S := by
  have hsqrt : ContinuousOn (fun t ↦ √(‖w t‖ ^ 2)) S :=
    hsq.sqrt
  apply hsqrt.congr
  intro t _
  exact (Real.sqrt_sq (norm_nonneg (w t))).symm

namespace HasIntegratedDualDerivativeOn

variable {T : GelfandTriple (V := V) (H := H)}
  {u : ℝ → H} {g : ℝ → StrongDual ℝ V} {a b : ℝ}

/-- Once the energy norm is known to be continuous, an integrated dual
derivative has a strongly continuous `H`-valued representative.
The uniform `H` bound needed to extend dense test pairings is obtained
internally from compactness of the time interval. -/
theorem continuousOn_of_norm
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (hnorm : ContinuousOn (fun t ↦ ‖u t‖) (uIcc a b)) :
    ContinuousOn u (uIcc a b) := by
  obtain ⟨M, hMbound⟩ := isCompact_uIcc.bddAbove_image hnorm
  have hbound : ∀ t ∈ uIcc a b, ‖u t‖ ≤ M := by
    intro t ht
    exact hMbound ⟨t, ht, rfl⟩
  have hM : 0 ≤ M :=
    (norm_nonneg (u a)).trans (hbound a left_mem_uIcc)
  have htest (v : V) :
      ContinuousOn (fun t ↦ inner ℝ (u t) (T.inclusion v)) (uIcc a b) := by
    have hcomp :=
      (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
        h.continuousOn_pivotToDual
    apply hcomp.congr
    intro t _ht
    exact GelfandTriple.pivotToDual_apply T (u t) v
  exact continuousOn_of_norm_of_inner hnorm
    (continuousOn_inner_of_denseRange T hM hbound htest)

/-- Squared-energy continuity is the exact hypothesis needed after proving
the nonsmooth energy identity. -/
theorem continuousOn_of_energy_sq
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (hsq : ContinuousOn (fun t ↦ ‖u t‖ ^ 2) (uIcc a b)) :
    ContinuousOn u (uIcc a b) :=
  h.continuousOn_of_norm (continuousOn_norm_of_sq hsq)

/-- The scalar energy representation produced by the time-mollification
limit upgrades the canonical weakly continuous trajectory to a strongly
continuous `H`-valued representative. Evans gets continuity directly, from the
uniform convergence of the mollified trajectories (§5.9.2, proof of Theorem 3,
estimate (11)); here the analytic work goes into proving the displayed
representation with `q(t) = g(t)(u(t))`. -/
theorem continuousOn_of_energy_representation
    (h : HasIntegratedDualDerivativeOn T u g a b)
    {q : ℝ → ℝ} (hq : IntervalIntegrable q volume a b)
    (henergy : ∀ t ∈ uIcc a b,
      ‖u t‖ ^ 2 = ‖u a‖ ^ 2 + 2 * ∫ r in a..t, q r) :
    ContinuousOn u (uIcc a b) := by
  have hprimitive : ContinuousOn (fun t ↦ ∫ r in a..t, q r)
      (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hq left_mem_uIcc
  have hrhs : ContinuousOn
      (fun t ↦ ‖u a‖ ^ 2 + 2 * ∫ r in a..t, q r) (uIcc a b) :=
    continuousOn_const.add (continuousOn_const.mul hprimitive)
  have hsq : ContinuousOn (fun t ↦ ‖u t‖ ^ 2) (uIcc a b) := by
    exact hrhs.congr fun t ht ↦ henergy t ht
  exact h.continuousOn_of_energy_sq hsq

omit [InnerProductSpace ℝ H] in
/-- A one-basepoint energy representation contains the usual two-time
energy identity.  This algebraic conversion is useful after the limiting
argument has identified the energy primitive. -/
theorem energy_sub_eq_integral_of_representation
    {q : ℝ → ℝ} (hq : IntervalIntegrable q volume a b)
    (henergy : ∀ t ∈ uIcc a b,
      ‖u t‖ ^ 2 = ‖u a‖ ^ 2 + 2 * ∫ r in a..t, q r)
    {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) :
    ‖u t‖ ^ 2 - ‖u s‖ ^ 2 = 2 * ∫ r in s..t, q r := by
  have has : IntervalIntegrable q volume a s :=
    hq.mono_set (uIcc_subset_uIcc_left hs)
  have hst : IntervalIntegrable q volume s t :=
    hq.mono_set (uIcc_subset_uIcc hs ht)
  rw [henergy t ht, henergy s hs]
  rw [← intervalIntegral.integral_add_adjacent_intervals has hst]
  ring

/--
If the `V*` derivative is represented almost everywhere by an integrable
`H`-valued velocity, the dual integral identity lifts through the injective
pivot embedding to the corresponding Bochner integral identity in `H`.

The almost-everywhere hypothesis suits Bochner-space data: changing either
derivative representative on a null set does not change its interval
integral.
-/
theorem eq_add_integral_of_ae_pivotDerivative
    [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (duH : ℝ → H) (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ᵐ t ∂volume.restrict (uIoc a b),
      RepresentsPivotDerivative T (g t) (duH t)) :
    ∀ t ∈ uIcc a b, u t = u a + ∫ r in a..t, duH r := by
  intro t ht
  apply T.pivotToDual_injective
  have hduHt := hduH.mono_set (uIcc_subset_uIcc_left ht)
  have hrepOn :
      ∀ᵐ r ∂volume.restrict (uIoc a t),
        RepresentsPivotDerivative T (g r) (duH r) :=
    hrep.filter_mono <| MeasureTheory.ae_mono <|
      (volume : Measure ℝ).restrict_mono_set
        (uIoc_subset_uIoc_of_uIcc_subset_uIcc
          (uIcc_subset_uIcc_left ht))
  have hrepInt : (∫ r in a..t, g r) =
      ∫ r in a..t, T.pivotToDual (duH r) := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hrepOn] with r hr
    apply ContinuousLinearMap.ext
    intro v
    exact hr v
  calc
    T.pivotToDual (u t) =
        T.pivotToDual (u a) + ∫ r in a..t, g r := h.eq_add_integral t ht
    _ = T.pivotToDual (u a) +
        ∫ r in a..t, T.pivotToDual (duH r) := by rw [hrepInt]
    _ = T.pivotToDual (u a) + T.pivotToDual (∫ r in a..t, duH r) := by
      rw [T.pivotToDual.intervalIntegral_comp_comm hduHt]
    _ = T.pivotToDual (u a + ∫ r in a..t, duH r) := by
      rw [map_add]

/-- Pointwise pivot representation specializes the null-set-invariant
Bochner integral identity. -/
theorem eq_add_integral_of_pivotDerivative
    [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (duH : ℝ → H) (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ t ∈ uIcc a b, RepresentsPivotDerivative T (g t) (duH t)) :
    ∀ t ∈ uIcc a b, u t = u a + ∫ r in a..t, duH r := by
  apply h.eq_add_integral_of_ae_pivotDerivative duH hduH
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact hrep t (uIoc_subset_uIcc ht)

/-- An almost-everywhere pivot representation produces an absolutely
continuous pivot-space trajectory. -/
theorem absolutelyContinuousOnInterval_of_ae_pivotDerivative
    [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (duH : ℝ → H) (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ᵐ t ∂volume.restrict (uIoc a b),
      RepresentsPivotDerivative T (g t) (duH t)) :
    AbsolutelyContinuousOnInterval u a b :=
  absolutelyContinuousOnInterval_of_eq_add_integral hduH
    (h.eq_add_integral_of_ae_pivotDerivative duH hduH hrep)

/-- Consequently, a pivot-representable integrated dual derivative produces
an absolutely continuous pivot-space trajectory.  This is the strong
derivative case of the Lions–Magenes time-regularity mechanism. -/
theorem absolutelyContinuousOnInterval_of_pivotDerivative
    [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (duH : ℝ → H) (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ t ∈ uIcc a b, RepresentsPivotDerivative T (g t) (duH t)) :
    AbsolutelyContinuousOnInterval u a b :=
  absolutelyContinuousOnInterval_of_eq_add_integral hduH
    (h.eq_add_integral_of_pivotDerivative duH hduH hrep)

/-- The pivot-representable case has a strongly continuous `H`-valued
representative, so both endpoint values are traces, not only values of an
almost-everywhere equivalence class. -/
theorem continuousOn_of_pivotDerivative
    [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (duH : ℝ → H) (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ t ∈ uIcc a b, RepresentsPivotDerivative T (g t) (duH t)) :
    ContinuousOn u (uIcc a b) :=
  (h.absolutelyContinuousOnInterval_of_pivotDerivative duH hduH hrep).continuousOn

/--
An integrated dual derivative represented almost everywhere by an integrable
pivot-space trajectory is the strong derivative of the pivot trajectory
almost everywhere.

This is the vector-valued fundamental theorem of calculus applied to the
Bochner representation supplied by
`eq_add_integral_of_ae_pivotDerivative`.
-/
theorem ae_hasDerivAt_of_ae_pivotDerivative
    [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (hab : a < b)
    (duH : ℝ → H) (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ᵐ t ∂volume.restrict (uIoc a b),
      RepresentsPivotDerivative T (g t) (duH t)) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (duH t) t := by
  have hprimitive :=
    IntervalIntegrable.ae_hasDerivAt_integral hduH
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
      HasDerivAt (fun s ↦ u a + ∫ r in a..s, duH r) (duH t) t := by
    have hintDeriv :
      HasDerivAt (fun s ↦ ∫ r in a..s, duH r) (duH t) t := by
      simpa using ht htIcc a left_mem_uIcc
    change HasDerivAt
      ((fun _ : ℝ ↦ u a) + fun s ↦ ∫ r in a..s, duH r) (duH t) t
    simpa only [zero_add] using (hasDerivAt_const t (u a)).add hintDeriv
  apply hprimDeriv.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds htIoo.1 htIoo.2] with s hs
  have hsIcc : s ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact ⟨hs.1.le, hs.2.le⟩
  exact h.eq_add_integral_of_ae_pivotDerivative duH hduH hrep s hsIcc

/-- Pointwise pivot representation specializes the almost-everywhere strong
derivative theorem. -/
theorem ae_hasDerivAt_of_pivotDerivative
    [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn T u g a b)
    (hab : a < b)
    (duH : ℝ → H) (hduH : IntervalIntegrable duH volume a b)
    (hrep : ∀ t ∈ uIcc a b, RepresentsPivotDerivative T (g t) (duH t)) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (duH t) t := by
  apply h.ae_hasDerivAt_of_ae_pivotDerivative hab duH hduH
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact hrep t (uIoc_subset_uIcc ht)

/-- An integrated dual derivative and one endpoint determine the entire
pivot-space trajectory.  This is the endpoint uniqueness principle used when
the Galerkin limit is identified with its prescribed initial trace. -/
theorem eqOn_of_same_initial
    {u₁ u₂ : ℝ → H}
    (h₁ : HasIntegratedDualDerivativeOn T u₁ g a b)
    (h₂ : HasIntegratedDualDerivativeOn T u₂ g a b)
    (hinit : u₁ a = u₂ a) :
    Set.EqOn u₁ u₂ (uIcc a b) := by
  intro t ht
  apply T.pivotToDual_injective
  rw [h₁.eq_add_integral t ht, h₂.eq_add_integral t ht, hinit]

end HasIntegratedDualDerivativeOn

end PDE.Analysis.Evolution
