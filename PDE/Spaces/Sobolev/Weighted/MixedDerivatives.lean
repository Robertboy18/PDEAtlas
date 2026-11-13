/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.MixedDerivatives.Basic

/-!
# Weighted interpolation of planar mixed derivatives

We bound the weighted norms of the planar mixed derivatives of one order by those of the two
neighbouring orders. On the half plane `{(r, z) : r > 0}` the row `mixedDerivative2D j a f` is
`∂_r^a ∂_z^(j-a) f`, `weightedMixedDerivativeEnergy2D j a Φ f` is the integral of its square against
the weight `Φ`, and `weightedMixedDerivativeSum2D j Φ f` is the sum over the `j + 1` rows of the
square roots of these integrals, that is `X_j(f) = ∑_a ‖∂_r^a ∂_z^(j-a) f‖_{L²(Φ)}` when they are
finite. If nonnegative weights satisfy `|Φmid| ≤ A0 √(Φprev Φnext)` and `|∂Φmid| ≤ A1 √(Φprev Φmid)`
for the derivatives in `r` and in `z`, then for `η > 0` and `0 < θ < 1`

  `X_{n+1}(f)² ≤ η X_{n+2}(f)² + K X_n(f)²`

where `K = weightedInterpolationStepConstant (n + 2) A0 A1 η θ`.
`weightedInterpolation_twoDimensional_halfPlane` proves this when the rows of order `n` are `C²` and
compactly supported along the lines on which they are differentiated and vanish on the axis `r = 0`,
with the integrability of the weighted squares and cross terms as hypotheses;
`weightedInterpolation_twoDimensional_halfPlane_of_continuous_compactSupport` derives the
integrability from continuity and compact support.
`weightedInterpolation_twoDimensional_halfPlane_of_tendsto` drops compact support and the axis
condition and asks instead for `C²` regularity on `r > 0`, weighted `L²` membership of the rows and
vanishing limits of the boundary products.

## How it works

Each row of middle order `n + 1` is paired with a row of order `n` and a row of order `n + 2`
(`weightedInterpolationPredecessorIndex2D`, `weightedInterpolationSuccessorIndex2D`): the all-axial
row is treated in `z` against `∂_z^n f`, and a row with `a > 0` radial derivatives is treated in `r`
against the order-`n` row with `a - 1` of them. Because `mixedDerivative2D` applies the axial
derivatives first, the identities `derivY_mixedDerivative_zero` and `derivX_mixedDerivative_succ`
that move between these rows hold by unfolding, and mixed partials are never commuted. For each row
the integration by parts and weighted Cauchy–Schwarz estimate of
`PDE.Spaces.Sobolev.Weighted.DerivativeInterpolation.Basic` gives `M ≤ A0 √P √N + A1 √P √M`
(`weightedInterpolation_mixedDerivative_axial_row`,
`weightedInterpolation_mixedDerivative_radial_row`); in `r` the boundary term at the axis is removed
by the vanishing of the order-`n` row there. `weightedInterpolation_mixedIndex_row_aggregation` sums
the rows: injectivity of the successor map bounds the successor terms by `X_{n+2}`, Mathlib's
`sq_sum_le_card_mul_sum_sq` gives the factor `n + 2`, and Young's inequality with absorption of the
middle term (`weightedInterpolationStep_from_base`) gives `K`. In the noncompact version we extend
the weights by zero to `r ≤ 0`, which leaves the half-plane integrals unchanged, and use the limit
forms `interpolation_row_axial_of_tendsto_of_ae` and `interpolation_row_radial_of_tendsto_of_ae` of
the row estimate. The argument is the proof (177)-(182) of Proposition 3 in Appendix A of
Duruisseaux, Ganeshram, George and Anandkumar, which uses only the comparison constants (173), so we
state it for general weights; the explicit predecessor and successor maps are ours.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix A, Proposition 3,
  (172)-(182), pp. 38-39, for the one-step weighted interpolation inequality (176), with the
  comparison constants (173) and the constant (174), which is
  `weightedInterpolationStepConstant (j + 1) A0 A1 η θ` for the middle order `j`.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology
open PDE.Analysis (derivX derivY)

namespace SobolevSpace.Weighted

/-- The integral over the half plane `r > 0` of the square of the row `mixedDerivative2D j a f`
times the weight `Φ`. It is a squared weighted `L²` norm when `Φ ≥ 0` and the integrand is
integrable; for a nonintegrable integrand the integral is `0`. -/
def weightedMixedDerivativeEnergy2D
    (j : ℕ) (a : Fin (j + 1)) (Φ f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    mixedDerivative2D j a f p.1 p.2 ^ 2 * Φ p.1 p.2
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)

/-- The sum over the `j + 1` rows of order `j` of the square roots of
`weightedMixedDerivativeEnergy2D j a Φ f`. When these integrals are finite and `Φ ≥ 0` it is
`X_j(f) = ∑_{|α| = j} ‖D^α f‖_{L²(Φ)}` on the half plane. -/
def weightedMixedDerivativeSum2D
    (j : ℕ) (Φ f : ℝ → ℝ → ℝ) : ℝ :=
  ∑ a : Fin (j + 1), Real.sqrt (weightedMixedDerivativeEnergy2D j a Φ f)

/--
For an order-`j` two-dimensional derivative indexed by its radial exponent,
choose the order-`j-1` predecessor used in integration by parts.  The all-axial
row stays at radial exponent zero; every other row loses one radial derivative.
-/
def weightedInterpolationPredecessorIndex2D (j : ℕ) [NeZero j] :
    Fin (j + 1) → Fin j :=
  Fin.cases 0 (fun a ↦ a)

/--
The corresponding order-`j+1` successor after differentiating twice in the
chosen coordinate.  The all-axial row stays at exponent zero; a row with
positive radial exponent gains one radial derivative.
-/
def weightedInterpolationSuccessorIndex2D (j : ℕ) :
    Fin (j + 1) → Fin (j + 2) :=
  Fin.cases 0 (fun a ↦ ⟨a.val + 2, by omega⟩)

/-- Distinct order-`j` rows have distinct chosen order-`j+1` successors. -/
theorem weightedInterpolationSuccessorIndex2D_injective (j : ℕ) :
    Function.Injective (weightedInterpolationSuccessorIndex2D j) := by
  intro a b hab
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    simp_all [weightedInterpolationSuccessorIndex2D, Fin.ext_iff]

/-- Summation of row estimates over the `j + 1` rows of one order. Suppose `M ≥ 0`, `A0, A1 ≥ 0`,
`η > 0`, `0 < θ < 1`, and every middle row `i` satisfies
`M i ≤ A0 √(P i') √(N i'') + A1 √(P i') √(M i)`, where `i'` and `i''` are its predecessor and
successor rows. Then `(∑ √M)² ≤ η (∑ √N)² + K (∑ √P)²` with
`K = weightedInterpolationStepConstant (j + 1) A0 A1 η θ`; the factor `j + 1` is the number of
middle rows. -/
theorem weightedInterpolation_twoDimensional_order_aggregation
    (j : ℕ) [NeZero j]
    (P : Fin j → ℝ) (M : Fin (j + 1) → ℝ) (N : Fin (j + 2) → ℝ)
    {A0 A1 η θ : ℝ}
    (hM : ∀ i, 0 ≤ M i)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hrow : ∀ i,
      M i ≤
        A0 * Real.sqrt
            (P (weightedInterpolationPredecessorIndex2D j i)) *
          Real.sqrt (N (weightedInterpolationSuccessorIndex2D j i)) +
        A1 * Real.sqrt
            (P (weightedInterpolationPredecessorIndex2D j i)) *
          Real.sqrt (M i)) :
    (∑ i, Real.sqrt (M i)) ^ 2 ≤
      η * (∑ i, Real.sqrt (N i)) ^ 2 +
        weightedInterpolationStepConstant (j + 1 : ℕ) A0 A1 η θ *
          (∑ i, Real.sqrt (P i)) ^ 2 := by
  simpa using
    (weightedInterpolation_mixedIndex_row_aggregation
      (weightedInterpolationPredecessorIndex2D j)
      (weightedInterpolationSuccessorIndex2D j)
      (weightedInterpolationSuccessorIndex2D_injective j)
      P M N hM hA0 hA1 hη hθ0 hθ1 hrow)

/-- The one-step inequality `X_{n+1}(f)² ≤ η X_{n+2}(f)² + K X_n(f)²` with
`K = weightedInterpolationStepConstant (n + 2) A0 A1 η θ`, assuming the row inequality for the
all-axial row (`haxial`) and for every row with positive radial exponent (`hradial`), nonnegative
middle energies, `A0, A1 ≥ 0`, `η > 0` and `0 < θ < 1`. -/
theorem weightedInterpolation_twoDimensional_from_coordinate_rows
    (n : ℕ) (f Φprev Φmid Φnext : ℝ → ℝ → ℝ)
    {A0 A1 η θ : ℝ}
    (hM : ∀ a : Fin (n + 2),
      0 ≤ weightedMixedDerivativeEnergy2D (n + 1) a Φmid f)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (haxial :
      weightedMixedDerivativeEnergy2D (n + 1) 0 Φmid f ≤
        A0 * Real.sqrt (weightedMixedDerivativeEnergy2D n 0 Φprev f) *
          Real.sqrt (weightedMixedDerivativeEnergy2D (n + 2) 0 Φnext f) +
        A1 * Real.sqrt (weightedMixedDerivativeEnergy2D n 0 Φprev f) *
          Real.sqrt (weightedMixedDerivativeEnergy2D (n + 1) 0 Φmid f))
    (hradial : ∀ a : Fin (n + 1),
      weightedMixedDerivativeEnergy2D (n + 1) a.succ Φmid f ≤
        A0 * Real.sqrt (weightedMixedDerivativeEnergy2D n a Φprev f) *
          Real.sqrt
            (weightedMixedDerivativeEnergy2D (n + 2) a.succ.succ Φnext f) +
        A1 * Real.sqrt (weightedMixedDerivativeEnergy2D n a Φprev f) *
          Real.sqrt
            (weightedMixedDerivativeEnergy2D (n + 1) a.succ Φmid f)) :
    weightedMixedDerivativeSum2D (n + 1) Φmid f ^ 2 ≤
      η * weightedMixedDerivativeSum2D (n + 2) Φnext f ^ 2 +
        weightedInterpolationStepConstant (n + 2 : ℕ) A0 A1 η θ *
          weightedMixedDerivativeSum2D n Φprev f ^ 2 := by
  simpa [weightedMixedDerivativeSum2D, add_assoc] using
    weightedInterpolation_twoDimensional_order_aggregation (n + 1)
      (weightedMixedDerivativeEnergy2D n · Φprev f)
      (weightedMixedDerivativeEnergy2D (n + 1) · Φmid f)
      (weightedMixedDerivativeEnergy2D (n + 2) · Φnext f) hM hA0 hA1 hη hθ0 hθ1
      fun i ↦ Fin.cases haxial hradial i

/-- The row inequality for the all-axial row of order `n + 1`, by integration by parts in `z` on
each line `r = const` against `∂_z^n f`. The hypotheses: `∂_z^n f` is `C²` and compactly supported
in `z`, `Φmid` is `C¹` in `z`, the weights are nonnegative and satisfy `|Φmid| ≤ A0 √Φprev √Φnext`
and `|∂_z Φmid| ≤ A1 √Φprev √Φmid`, and the weighted squares and cross terms are integrable and the
weighted rows measurable on the half plane. -/
theorem weightedInterpolation_mixedDerivative_axial_row
    (n : ℕ) (f Φprev Φmid Φnext : ℝ → ℝ → ℝ) {A0 A1 : ℝ}
    (hu : ∀ r, ContDiff ℝ 2
      (fun z ↦ mixedDerivative2D n 0 f r z))
    (hΦmid : ∀ r, ContDiff ℝ 1 (fun z ↦ Φmid r z))
    (hcu : ∀ r, HasCompactSupport
      (fun z ↦ mixedDerivative2D n 0 f r z))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * Real.sqrt (Φprev r z) * Real.sqrt (Φnext r z))
    (hcompare1 : ∀ r z,
      |derivY Φmid r z| ≤
        A1 * Real.sqrt (Φprev r z) * Real.sqrt (Φmid r z))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n 0 f p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 1) 0 f p.1 p.2 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 2) 0 f p.1 p.2 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n 0 f p.1 p.2 *
          derivY (derivY (mixedDerivative2D n 0 f))
            p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n 0 f p.1 p.2 *
          derivY (mixedDerivative2D n 0 f) p.1 p.2 *
          derivY Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n 0 f p.1 p.2 * Real.sqrt (Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 1) 0 f p.1 p.2 * Real.sqrt (Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 2) 0 f p.1 p.2 * Real.sqrt (Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    weightedMixedDerivativeEnergy2D (n + 1) 0 Φmid f ≤
      A0 * Real.sqrt (weightedMixedDerivativeEnergy2D n 0 Φprev f) *
          Real.sqrt (weightedMixedDerivativeEnergy2D (n + 2) 0 Φnext f) +
        A1 * Real.sqrt (weightedMixedDerivativeEnergy2D n 0 Φprev f) *
          Real.sqrt (weightedMixedDerivativeEnergy2D (n + 1) 0 Φmid f) := by
  simp only [← derivY_mixedDerivative_zero n f, ← derivY_sq_mixedDerivative_zero n f,
    weightedMixedDerivativeEnergy2D] at hmid_int hnext_int hmid_meas hnext_meas ⊢
  exact weightedInterpolation_row_base_integral_halfPlane_axial hu hΦmid hcu hA0 hA1
    hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1 hprev_int hmid_int hnext_int
    hterm0_int hterm1_int hprev_meas hmid_meas hnext_meas

/-- The row inequality for the row of order `n + 1` with radial exponent `a + 1`, by integration by
parts in `r` on each line `z = const` against the order-`n` row with radial exponent `a`. That row
is assumed `C²` and compactly supported in `r` and zero at `r = 0`; the other hypotheses are those
of `weightedInterpolation_mixedDerivative_axial_row` with `∂_r Φmid` in place of `∂_z Φmid`. -/
theorem weightedInterpolation_mixedDerivative_radial_row
    (n : ℕ) (a : Fin (n + 1))
    (f Φprev Φmid Φnext : ℝ → ℝ → ℝ) {A0 A1 : ℝ}
    (hu : ∀ z, ContDiff ℝ 2
      (fun r ↦ mixedDerivative2D n a f r z))
    (hΦmid : ∀ z, ContDiff ℝ 1 (fun r ↦ Φmid r z))
    (hcu : ∀ z, HasCompactSupport
      (fun r ↦ mixedDerivative2D n a f r z))
    (hu0 : ∀ z, mixedDerivative2D n a f 0 z = 0)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * Real.sqrt (Φprev r z) * Real.sqrt (Φnext r z))
    (hcompare1 : ∀ r z,
      |derivX Φmid r z| ≤
        A1 * Real.sqrt (Φprev r z) * Real.sqrt (Φmid r z))
    (hprev_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 1) a.succ f p.1 p.2 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 2) a.succ.succ f p.1 p.2 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm0_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 *
          derivX (derivX (mixedDerivative2D n a f))
            p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hterm1_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 *
          derivX (mixedDerivative2D n a f) p.1 p.2 *
          derivX Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hprev_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 * Real.sqrt (Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 1) a.succ f p.1 p.2 * Real.sqrt (Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 2) a.succ.succ f p.1 p.2 *
          Real.sqrt (Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    weightedMixedDerivativeEnergy2D (n + 1) a.succ Φmid f ≤
      A0 * Real.sqrt (weightedMixedDerivativeEnergy2D n a Φprev f) *
          Real.sqrt
            (weightedMixedDerivativeEnergy2D (n + 2) a.succ.succ Φnext f) +
        A1 * Real.sqrt (weightedMixedDerivativeEnergy2D n a Φprev f) *
          Real.sqrt
            (weightedMixedDerivativeEnergy2D (n + 1) a.succ Φmid f) := by
  simp only [← derivX_mixedDerivative_succ n a f, ← derivX_sq_mixedDerivative_succ n a f,
    weightedMixedDerivativeEnergy2D] at hmid_int hnext_int hmid_meas hnext_meas ⊢
  exact weightedInterpolation_row_base_integral_halfPlane_radial_rz hu hΦmid hcu hu0 hA0 hA1
    hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1 hprev_int hmid_int hnext_int
    hterm0_int hterm1_int hprev_meas hmid_meas hnext_meas

/--
Weighted interpolation on the half plane for the mixed derivatives of `f` of order `n + 1`:
`X_{n+1}(f)² ≤ η X_{n+2}(f)² + K X_n(f)²` with
`K = weightedInterpolationStepConstant (n + 2) A0 A1 η θ`. The hypotheses: the all-axial order-`n`
row is `C²` and compactly supported in `z`, every order-`n` row is `C²` and compactly supported in
`r`, `Φmid` is `C¹` in `r` and in `z`, the weights are nonnegative and satisfy `hcompare0`,
`hcompare1_axial` and `hcompare1_radial`, and the weighted squares and cross terms are integrable
and the weighted rows measurable on the half plane. No row inequality is assumed.

The hypothesis `hradial_axis` requires every order-`n` row, including the
pure-axial row `∂_z^n f`, to vanish on the axis `r = 0`.  This restricts the
theorem to data all of whose order-`n` rows have zero axis trace: at `n = 0`
to functions vanishing on the axis, as odd profiles do, and for `n ≥ 1` it
excludes even profiles whose even-exponent rows need not
vanish there.
-/
theorem weightedInterpolation_twoDimensional_halfPlane
    (n : ℕ) (f Φprev Φmid Φnext : ℝ → ℝ → ℝ)
    {A0 A1 η θ : ℝ}
    (haxial_smooth : ∀ r, ContDiff ℝ 2
      (fun z ↦ mixedDerivative2D n 0 f r z))
    (hradial_smooth : ∀ a : Fin (n + 1), ∀ z, ContDiff ℝ 2
      (fun r ↦ mixedDerivative2D n a f r z))
    (hΦmid_axial : ∀ r, ContDiff ℝ 1 (fun z ↦ Φmid r z))
    (hΦmid_radial : ∀ z, ContDiff ℝ 1 (fun r ↦ Φmid r z))
    (haxial_compact : ∀ r, HasCompactSupport
      (fun z ↦ mixedDerivative2D n 0 f r z))
    (hradial_compact : ∀ a : Fin (n + 1), ∀ z, HasCompactSupport
      (fun r ↦ mixedDerivative2D n a f r z))
    (hradial_axis : ∀ a : Fin (n + 1), ∀ z,
      mixedDerivative2D n a f 0 z = 0)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * Real.sqrt (Φprev r z) * Real.sqrt (Φnext r z))
    (hcompare1_axial : ∀ r z,
      |derivY Φmid r z| ≤
        A1 * Real.sqrt (Φprev r z) * Real.sqrt (Φmid r z))
    (hcompare1_radial : ∀ r z,
      |derivX Φmid r z| ≤
        A1 * Real.sqrt (Φprev r z) * Real.sqrt (Φmid r z))
    (hprev_int : ∀ a : Fin (n + 1), Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 ^ 2 * Φprev p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_int : ∀ a : Fin (n + 2), Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 1) a f p.1 p.2 ^ 2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_int : ∀ a : Fin (n + 3), Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 2) a f p.1 p.2 ^ 2 * Φnext p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (haxial_term0_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n 0 f p.1 p.2 *
          derivY (derivY (mixedDerivative2D n 0 f))
            p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (haxial_term1_int : Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n 0 f p.1 p.2 *
          derivY (mixedDerivative2D n 0 f) p.1 p.2 *
          derivY Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hradial_term0_int : ∀ a : Fin (n + 1), Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 *
          derivX (derivX (mixedDerivative2D n a f))
            p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hradial_term1_int : ∀ a : Fin (n + 1), Integrable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 *
          derivX (mixedDerivative2D n a f) p.1 p.2 *
          derivX Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hprev_meas : ∀ a : Fin (n + 1), AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D n a f p.1 p.2 * Real.sqrt (Φprev p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid_meas : ∀ a : Fin (n + 2), AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 1) a f p.1 p.2 * Real.sqrt (Φmid p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext_meas : ∀ a : Fin (n + 3), AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦
        mixedDerivative2D (n + 2) a f p.1 p.2 * Real.sqrt (Φnext p.1 p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    weightedMixedDerivativeSum2D (n + 1) Φmid f ^ 2 ≤
      η * weightedMixedDerivativeSum2D (n + 2) Φnext f ^ 2 +
        weightedInterpolationStepConstant (n + 2 : ℕ) A0 A1 η θ *
          weightedMixedDerivativeSum2D n Φprev f ^ 2 :=
  weightedInterpolation_twoDimensional_from_coordinate_rows n f Φprev Φmid Φnext
    (fun _ ↦ integral_nonneg fun p ↦ mul_nonneg (sq_nonneg _) (hmid_nonneg p.1 p.2))
    hA0 hA1 hη hθ0 hθ1
    (weightedInterpolation_mixedDerivative_axial_row n f Φprev Φmid Φnext haxial_smooth
      hΦmid_axial haxial_compact hA0 hA1 hprev_nonneg hmid_nonneg hnext_nonneg hcompare0
      hcompare1_axial (hprev_int 0) (hmid_int 0) (hnext_int 0) haxial_term0_int
      haxial_term1_int (hprev_meas 0) (hmid_meas 0) (hnext_meas 0))
    fun a ↦ weightedInterpolation_mixedDerivative_radial_row n a f Φprev Φmid Φnext
      (hradial_smooth a) hΦmid_radial (hradial_compact a) (hradial_axis a) hA0 hA1
      hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1_radial (hprev_int a)
      (hmid_int a.succ) (hnext_int a.succ.succ) (hradial_term0_int a) (hradial_term1_int a)
      (hprev_meas a) (hmid_meas a.succ) (hnext_meas a.succ.succ)

/--
The conclusion of `weightedInterpolation_twoDimensional_halfPlane` with its integrability and
measurability hypotheses replaced by continuity and compact support on the plane of the rows of
orders `n`, `n + 1` and `n + 2`, and continuity of the three weights and of the first derivatives of
`Φmid` in `r` and in `z`. The axis condition `hradial_axis` on every order-`n` row is kept, with the
same restriction on the admissible data.
-/
theorem weightedInterpolation_twoDimensional_halfPlane_of_continuous_compactSupport
    (n : ℕ) (f Φprev Φmid Φnext : ℝ → ℝ → ℝ)
    {A0 A1 η θ : ℝ}
    (haxial_smooth : ∀ r, ContDiff ℝ 2
      (fun z ↦ mixedDerivative2D n 0 f r z))
    (hradial_smooth : ∀ a : Fin (n + 1), ∀ z, ContDiff ℝ 2
      (fun r ↦ mixedDerivative2D n a f r z))
    (hΦmid_axial : ∀ r, ContDiff ℝ 1 (fun z ↦ Φmid r z))
    (hΦmid_radial : ∀ z, ContDiff ℝ 1 (fun r ↦ Φmid r z))
    (haxial_compact : ∀ r, HasCompactSupport
      (fun z ↦ mixedDerivative2D n 0 f r z))
    (hradial_compact : ∀ a : Fin (n + 1), ∀ z, HasCompactSupport
      (fun r ↦ mixedDerivative2D n a f r z))
    (hradial_axis : ∀ a : Fin (n + 1), ∀ z,
      mixedDerivative2D n a f 0 z = 0)
    (hprev_cont : ∀ a : Fin (n + 1), Continuous
      (fun p : ℝ × ℝ ↦ mixedDerivative2D n a f p.1 p.2))
    (hmid_cont : ∀ a : Fin (n + 2), Continuous
      (fun p : ℝ × ℝ ↦ mixedDerivative2D (n + 1) a f p.1 p.2))
    (hnext_cont : ∀ a : Fin (n + 3), Continuous
      (fun p : ℝ × ℝ ↦ mixedDerivative2D (n + 2) a f p.1 p.2))
    (hprev_cs : ∀ a : Fin (n + 1), HasCompactSupport
      (fun p : ℝ × ℝ ↦ mixedDerivative2D n a f p.1 p.2))
    (hmid_cs : ∀ a : Fin (n + 2), HasCompactSupport
      (fun p : ℝ × ℝ ↦ mixedDerivative2D (n + 1) a f p.1 p.2))
    (hnext_cs : ∀ a : Fin (n + 3), HasCompactSupport
      (fun p : ℝ × ℝ ↦ mixedDerivative2D (n + 2) a f p.1 p.2))
    (hΦprev_cont : Continuous (fun p : ℝ × ℝ ↦ Φprev p.1 p.2))
    (hΦmid_cont : Continuous (fun p : ℝ × ℝ ↦ Φmid p.1 p.2))
    (hΦnext_cont : Continuous (fun p : ℝ × ℝ ↦ Φnext p.1 p.2))
    (hdΦmid_axial_cont : Continuous
      (fun p : ℝ × ℝ ↦ derivY Φmid p.1 p.2))
    (hdΦmid_radial_cont : Continuous
      (fun p : ℝ × ℝ ↦ derivX Φmid p.1 p.2))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ r z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ r z,
      |Φmid r z| ≤
        A0 * Real.sqrt (Φprev r z) * Real.sqrt (Φnext r z))
    (hcompare1_axial : ∀ r z,
      |derivY Φmid r z| ≤
        A1 * Real.sqrt (Φprev r z) * Real.sqrt (Φmid r z))
    (hcompare1_radial : ∀ r z,
      |derivX Φmid r z| ≤
        A1 * Real.sqrt (Φprev r z) * Real.sqrt (Φmid r z)) :
    weightedMixedDerivativeSum2D (n + 1) Φmid f ^ 2 ≤
      η * weightedMixedDerivativeSum2D (n + 2) Φnext f ^ 2 +
        weightedInterpolationStepConstant (n + 2 : ℕ) A0 A1 η θ *
          weightedMixedDerivativeSum2D n Φprev f ^ 2 := by
  have hsq {g Φ : ℝ × ℝ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g)
      (hΦ : Continuous Φ) : Integrable (fun p ↦ g p ^ 2 * Φ p)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    ((hg.pow 2).mul hΦ).integrable_of_hasCompactSupport
      (hcs.mono fun p hp h0 ↦ hp (by simp [h0]))
  have hcross {g h Φ : ℝ × ℝ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g)
      (hh : Continuous h) (hΦ : Continuous Φ) : Integrable (fun p ↦ g p * h p * Φ p)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    ((hg.mul hh).mul hΦ).integrable_of_hasCompactSupport hcs.mul_right.mul_right
  exact weightedInterpolation_twoDimensional_halfPlane n f Φprev Φmid Φnext haxial_smooth
    hradial_smooth hΦmid_axial hΦmid_radial haxial_compact hradial_compact hradial_axis hA0 hA1
    hη hθ0 hθ1 hprev_nonneg hmid_nonneg hnext_nonneg hcompare0 hcompare1_axial
    hcompare1_radial (fun a ↦ hsq (hprev_cont a) (hprev_cs a) hΦprev_cont)
    (fun a ↦ hsq (hmid_cont a) (hmid_cs a) hΦmid_cont)
    (fun a ↦ hsq (hnext_cont a) (hnext_cs a) hΦnext_cont)
    (hcross (hprev_cont 0) (hprev_cs 0) (derivY_sq_mixedDerivative_zero n f ▸ hnext_cont 0)
      hΦmid_cont)
    (hcross (hprev_cont 0) (hprev_cs 0) (derivY_mixedDerivative_zero n f ▸ hmid_cont 0)
      hdΦmid_axial_cont)
    (fun a ↦ hcross (hprev_cont a) (hprev_cs a)
      (derivX_sq_mixedDerivative_succ n a f ▸ hnext_cont a.succ.succ) hΦmid_cont)
    (fun a ↦ hcross (hprev_cont a) (hprev_cs a)
      (derivX_mixedDerivative_succ n a f ▸ hmid_cont a.succ) hdΦmid_radial_cont)
    (fun a ↦ ((hprev_cont a).mul hΦprev_cont.sqrt).aestronglyMeasurable)
    (fun a ↦ ((hmid_cont a).mul hΦmid_cont.sqrt).aestronglyMeasurable)
    (fun a ↦ ((hnext_cont a).mul hΦnext_cont.sqrt).aestronglyMeasurable)

/-- At a differentiability point, an axial derivative advances the all-axial row. -/
theorem hasDerivAt_mixedDerivative2D_axial
    (n : ℕ) (f : ℝ → ℝ → ℝ) {r z : ℝ}
    (h : DifferentiableAt ℝ (mixedDerivative2D n 0 f r) z) :
    HasDerivAt (mixedDerivative2D n 0 f r) (mixedDerivative2D (n + 1) 0 f r z) z :=
  h.hasDerivAt.congr_deriv (congr_fun₂ (derivY_mixedDerivative_zero n f) r z)

/-- Local C² regularity of the all-axial predecessor identifies the derivative
of its successor row. Only regularity along this axial slice is required. -/
theorem hasDerivAt_mixedDerivative2D_axial_succ_of_contDiffAt
    (n : ℕ) (f : ℝ → ℝ → ℝ) {r z : ℝ}
    (h : ContDiffAt ℝ 2 (mixedDerivative2D n 0 f r) z) :
    HasDerivAt (mixedDerivative2D (n + 1) 0 f r)
      (mixedDerivative2D (n + 2) 0 f r z) z := by
  rw [← derivY_mixedDerivative_zero, ← derivY_sq_mixedDerivative_zero]
  exact (h.derivWithin (m := 1) (by norm_num)).differentiableAt_one.hasDerivAt

/-- At a differentiability point, a radial derivative advances the radial index. -/
theorem hasDerivAt_mixedDerivative2D_radial
    (n : ℕ) (a : Fin (n + 1)) (f : ℝ → ℝ → ℝ) {r z : ℝ}
    (h : DifferentiableAt ℝ (fun s ↦ mixedDerivative2D n a f s z) r) :
    HasDerivAt (fun s ↦ mixedDerivative2D n a f s z)
      (mixedDerivative2D (n + 1) a.succ f r z) r :=
  h.hasDerivAt.congr_deriv (congr_fun₂ (derivX_mixedDerivative_succ n a f) r z)

/-- Local C² regularity of a radial predecessor identifies the derivative of
its successor row, without commuting mixed partial derivatives. -/
theorem hasDerivAt_mixedDerivative2D_radial_succ_of_contDiffAt
    (n : ℕ) (a : Fin (n + 1)) (f : ℝ → ℝ → ℝ) {r z : ℝ}
    (h : ContDiffAt ℝ 2 (fun s ↦ mixedDerivative2D n a f s z) r) :
    HasDerivAt (fun s ↦ mixedDerivative2D (n + 1) a.succ f s z)
      (mixedDerivative2D (n + 2) a.succ.succ f r z) r := by
  rw [← derivX_mixedDerivative_succ, ← derivX_sq_mixedDerivative_succ]
  exact (h.derivWithin (m := 1) (by norm_num)).differentiableAt_one.hasDerivAt

/-- Noncompact interpolation for all mixed derivatives of middle order `n + 1`.

The pure-axial row uses axial integration by parts; every positive-radial row
uses radial integration by parts with its order-`n` predecessor. The
successor identities identify both derivatives without commuting
mixed partials. Local C² regularity is required only along these predecessor
slices in `r > 0`, and the middle weight is differentiable there.

Weighted L² membership supplies the three square integrabilities and weighted
measurabilities. The cross-term integrabilities and the two endpoint limits
of each boundary product remain explicit. Neither compact support, a zero
value trace on the axis, nor any row inequality is assumed.

Weight comparisons hold almost everywhere for the open-half-plane product
measure. Zero extension supplies globally nonnegative weights to the Cauchy
estimate without imposing conditions at the singular origin. The conclusion
is one adjacent-order interpolation step. -/
theorem weightedInterpolation_twoDimensional_halfPlane_of_tendsto
    (n : ℕ) (f Φprev Φmid Φnext : ℝ → ℝ → ℝ)
    {A0 A1 η θ : ℝ}
    (haxial_smooth : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ z,
      ContDiffAt ℝ 2 (mixedDerivative2D n 0 f r) z)
    (hradial_smooth : ∀ a : Fin (n + 1), ∀ᵐ z ∂volume, ∀ r ∈ Set.Ioi (0 : ℝ),
      ContDiffAt ℝ 2 (fun s ↦ mixedDerivative2D n a f s z) r)
    (hΦmid_axial : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ z,
      DifferentiableAt ℝ (Φmid r) z)
    (hΦmid_radial : ∀ᵐ z ∂volume, ∀ r ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun s ↦ Φmid s z) r)
    (haxial_bot : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Tendsto (fun z ↦ mixedDerivative2D n 0 f r z *
        mixedDerivative2D (n + 1) 0 f r z * Φmid r z) atBot (𝓝 0))
    (haxial_top : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Tendsto (fun z ↦ mixedDerivative2D n 0 f r z *
        mixedDerivative2D (n + 1) 0 f r z * Φmid r z) atTop (𝓝 0))
    (hradial_zero : ∀ a : Fin (n + 1), ∀ᵐ z ∂volume,
      Tendsto (fun r ↦ mixedDerivative2D n a f r z *
        mixedDerivative2D (n + 1) a.succ f r z * Φmid r z) (𝓝[>] 0) (𝓝 0))
    (hradial_top : ∀ a : Fin (n + 1), ∀ᵐ z ∂volume,
      Tendsto (fun r ↦ mixedDerivative2D n a f r z *
        mixedDerivative2D (n + 1) a.succ f r z * Φmid r z) atTop (𝓝 0))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hprev_nonneg : ∀ r, 0 < r → ∀ z, 0 ≤ Φprev r z)
    (hmid_nonneg : ∀ r, 0 < r → ∀ z, 0 ≤ Φmid r z)
    (hnext_nonneg : ∀ r, 0 < r → ∀ z, 0 ≤ Φnext r z)
    (hcompare0 : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume),
      |Φmid p.1 p.2| ≤ A0 * Real.sqrt (Φprev p.1 p.2) * Real.sqrt (Φnext p.1 p.2))
    (hcompare1_axial : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume),
      |derivY Φmid p.1 p.2| ≤
        A1 * Real.sqrt (Φprev p.1 p.2) * Real.sqrt (Φmid p.1 p.2))
    (hcompare1_radial : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume),
      |derivX Φmid p.1 p.2| ≤
        A1 * Real.sqrt (Φprev p.1 p.2) * Real.sqrt (Φmid p.1 p.2))
    (hprev : ∀ a : Fin (n + 1), MemLp
      (fun p : ℝ × ℝ ↦ mixedDerivative2D n a f p.1 p.2 * Real.sqrt (Φprev p.1 p.2))
      2 ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hmid : ∀ a : Fin (n + 2), MemLp
      (fun p : ℝ × ℝ ↦ mixedDerivative2D (n + 1) a f p.1 p.2 *
        Real.sqrt (Φmid p.1 p.2))
      2 ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hnext : ∀ a : Fin (n + 3), MemLp
      (fun p : ℝ × ℝ ↦ mixedDerivative2D (n + 2) a f p.1 p.2 *
        Real.sqrt (Φnext p.1 p.2))
      2 ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (haxial_term0_int : Integrable
      (fun p : ℝ × ℝ ↦ mixedDerivative2D n 0 f p.1 p.2 *
        mixedDerivative2D (n + 2) 0 f p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (haxial_term1_int : Integrable
      (fun p : ℝ × ℝ ↦ mixedDerivative2D n 0 f p.1 p.2 *
        mixedDerivative2D (n + 1) 0 f p.1 p.2 * derivY Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hradial_term0_int : ∀ a : Fin (n + 1), Integrable
      (fun p : ℝ × ℝ ↦ mixedDerivative2D n a f p.1 p.2 *
        mixedDerivative2D (n + 2) a.succ.succ f p.1 p.2 * Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume))
    (hradial_term1_int : ∀ a : Fin (n + 1), Integrable
      (fun p : ℝ × ℝ ↦ mixedDerivative2D n a f p.1 p.2 *
        mixedDerivative2D (n + 1) a.succ f p.1 p.2 * derivX Φmid p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    weightedMixedDerivativeSum2D (n + 1) Φmid f ^ 2 ≤
      η * weightedMixedDerivativeSum2D (n + 2) Φnext f ^ 2 +
        weightedInterpolationStepConstant (n + 2 : ℕ) A0 A1 η θ *
          weightedMixedDerivativeSum2D n Φprev f ^ 2 := by
  let ν : Measure (ℝ × ℝ) := (volume.restrict (Set.Ioi (0 : ℝ))).prod volume
  let W (Φ : ℝ → ℝ → ℝ) (r z : ℝ) := if 0 < r then Φ r z else 0
  have hr : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 < r := ae_restrict_mem measurableSet_Ioi
  have hp : ∀ᵐ p : ℝ × ℝ ∂ν, 0 < p.1 := Measure.quasiMeasurePreserving_fst.ae hr
  have hW (g : ℝ × ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) :
      (fun p ↦ g p * W Φ p.1 p.2) =ᵐ[ν] fun p ↦ g p * Φ p.1 p.2 :=
    hp.mono fun p hp ↦ by simp only [W, ite_eq_left hp]
  have hWnonneg (Φ : ℝ → ℝ → ℝ) (hΦ : ∀ r, 0 < r → ∀ z, 0 ≤ Φ r z) (r z : ℝ) :
      0 ≤ W Φ r z := by
    dsimp only [W]
    split_ifs with hr
    exacts [hΦ r hr z, le_rfl]
  have hWcompare (B : ℝ) (Ψ Φ0 Φ1 : ℝ → ℝ → ℝ)
      (h : ∀ᵐ p : ℝ × ℝ ∂ν, |Ψ p.1 p.2| ≤ B * √(Φ0 p.1 p.2) * √(Φ1 p.1 p.2)) :
      ∀ᵐ p : ℝ × ℝ ∂ν, |W Ψ p.1 p.2| ≤ B * √(W Φ0 p.1 p.2) * √(W Φ1 p.1 p.2) := by
    filter_upwards [hp, h] with p hp hb
    simpa only [W, ite_eq_left hp] using hb
  have hsq_int (g Φ : ℝ → ℝ → ℝ) (hΦ : ∀ r, 0 < r → ∀ z, 0 ≤ Φ r z)
      (hg : MemLp (fun p : ℝ × ℝ ↦ g p.1 p.2 * √(Φ p.1 p.2)) 2 ν) :
      Integrable (fun p : ℝ × ℝ ↦ g p.1 p.2 ^ 2 * W Φ p.1 p.2) ν :=
    hg.integrable_sq.congr <| hp.mono fun p hp ↦ by
      simp only [W, ite_eq_left hp, mul_pow, Real.sq_sqrt (hΦ p.1 hp p.2)]
  have hmeas (g Φ : ℝ → ℝ → ℝ) (hg : MemLp (fun p : ℝ × ℝ ↦ g p.1 p.2 * √(Φ p.1 p.2)) 2 ν) :
      AEStronglyMeasurable (fun p : ℝ × ℝ ↦ g p.1 p.2 * √(W Φ p.1 p.2)) ν :=
    hg.aestronglyMeasurable.congr <| hp.mono fun p hp ↦ by simp only [W, ite_eq_left hp]
  have henergy (j : ℕ) (a : Fin (j + 1)) (Φ : ℝ → ℝ → ℝ) :
      (∫ p : ℝ × ℝ, mixedDerivative2D j a f p.1 p.2 ^ 2 * W Φ p.1 p.2 ∂ν) =
        weightedMixedDerivativeEnergy2D j a Φ f :=
    integral_congr_ae (hW _ Φ)
  dsimp only [ν] at henergy
  have haxial := interpolation_row_axial_of_tendsto_of_ae
    (haxial_smooth.mono fun r hreg z ↦
      hasDerivAt_mixedDerivative2D_axial n f ((hreg z).differentiableAt (by norm_num)))
    (haxial_smooth.mono fun r hreg z ↦
      hasDerivAt_mixedDerivative2D_axial_succ_of_contDiffAt n f (hreg z))
    ((hr.and hΦmid_axial).mono fun r h z ↦ by
      simpa only [W, ite_eq_left h.1, derivY] using (h.2 z).hasDerivAt)
    ((hr.and haxial_bot).mono fun r h ↦ by simpa only [W, ite_eq_left h.1] using h.2)
    ((hr.and haxial_top).mono fun r h ↦ by simpa only [W, ite_eq_left h.1] using h.2)
    hA0 hA1 (hWnonneg Φprev hprev_nonneg) (hWnonneg Φmid hmid_nonneg)
    (hWnonneg Φnext hnext_nonneg) (hWcompare A0 Φmid Φprev Φnext hcompare0)
    (hWcompare A1 (derivY Φmid) Φprev Φmid hcompare1_axial)
    (hsq_int _ _ hprev_nonneg (hprev 0)) (hsq_int _ _ hmid_nonneg (hmid 0))
    (hsq_int _ _ hnext_nonneg (hnext 0)) (haxial_term0_int.congr (hW _ Φmid).symm)
    (haxial_term1_int.congr (hW _ _).symm) (hmeas _ _ (hprev 0)) (hmeas _ _ (hmid 0))
    (hmeas _ _ (hnext 0))
  have hW_radial : ∀ᵐ z, ∀ r ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s ↦ W Φmid s z) (W (derivX Φmid) r z) r :=
    hΦmid_radial.mono fun z hreg r (hr : 0 < r) ↦ by
      simpa only [W, ite_eq_left hr, derivX] using (hreg r hr).hasDerivAt.congr_of_eventuallyEq
        (f₁ := fun s ↦ W Φmid s z) ((lt_mem_nhds hr).mono fun s hs ↦ ite_eq_left hs)
  have hW_zero (a : Fin (n + 1)) : ∀ᵐ z, Tendsto (fun r ↦ mixedDerivative2D n a f r z *
      mixedDerivative2D (n + 1) a.succ f r z * W Φmid r z) (𝓝[>] 0) (𝓝 0) :=
    (hradial_zero a).mono fun z h ↦ h.congr' <|
      eventually_mem_nhdsWithin.mono fun r (hr : 0 < r) ↦ by simp only [W, ite_eq_left hr]
  have hW_top (a : Fin (n + 1)) : ∀ᵐ z, Tendsto (fun r ↦ mixedDerivative2D n a f r z *
      mixedDerivative2D (n + 1) a.succ f r z * W Φmid r z) atTop (𝓝 0) :=
    (hradial_top a).mono fun z h ↦ h.congr' <|
      (eventually_gt_atTop 0).mono fun r hr ↦ by simp only [W, ite_eq_left hr]
  have hradial (a : Fin (n + 1)) := interpolation_row_radial_of_tendsto_of_ae
    ((hradial_smooth a).mono fun z hreg r hr ↦
      hasDerivAt_mixedDerivative2D_radial n a f ((hreg r hr).differentiableAt (by norm_num)))
    ((hradial_smooth a).mono fun z hreg r hr ↦
      hasDerivAt_mixedDerivative2D_radial_succ_of_contDiffAt n a f (hreg r hr))
    hW_radial (hW_zero a) (hW_top a) hA0 hA1 (hWnonneg Φprev hprev_nonneg)
    (hWnonneg Φmid hmid_nonneg) (hWnonneg Φnext hnext_nonneg)
    (hWcompare A0 Φmid Φprev Φnext hcompare0)
    (hWcompare A1 (derivX Φmid) Φprev Φmid hcompare1_radial)
    (hsq_int _ _ hprev_nonneg (hprev a)) (hsq_int _ _ hmid_nonneg (hmid a.succ))
    (hsq_int _ _ hnext_nonneg (hnext a.succ.succ))
    ((hradial_term0_int a).congr (hW _ Φmid).symm) ((hradial_term1_int a).congr (hW _ _).symm)
    (hmeas _ _ (hprev a)) (hmeas _ _ (hmid a.succ)) (hmeas _ _ (hnext a.succ.succ))
  exact weightedInterpolation_twoDimensional_from_coordinate_rows n f Φprev Φmid Φnext
    (fun _ ↦ integral_nonneg_of_ae <| hp.mono fun p hp ↦
      mul_nonneg (sq_nonneg _) (hmid_nonneg p.1 hp p.2))
    hA0 hA1 hη hθ0 hθ1 (by simpa only [henergy] using haxial)
    fun a ↦ by simpa only [henergy] using hradial a

end SobolevSpace.Weighted
