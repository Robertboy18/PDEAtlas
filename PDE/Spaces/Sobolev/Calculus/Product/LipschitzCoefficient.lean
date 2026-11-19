/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.Analysis.Calculus.Rademacher
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Lipschitz Sobolev coefficients

A globally Lipschitz function `f : ℝ^n → ℝ` belongs to `W^{1,∞}`. Its line derivatives
`x ↦ lineDeriv ℝ f x eᵢ` are bounded by the Lipschitz constant (`norm_lineDeriv_le_of_lipschitz`),
and the integration by parts formula `LipschitzWith.integral_lineDeriv_mul_eq`, which Mathlib proves
on the way to Rademacher's theorem, identifies each of them as the weak partial derivative `∂ᵢ f`.
We state that fact in the graph-space model of `W^{1,∞}(Ω)`: given an `L^∞` class `F` on a
measurable set `Ω` and a Lipschitz representative `f` of it, `w1TopOfLipschitzRepresentative` is the
element of `WkpSpaceOn n 1 ∞ Ω` whose base coordinate is `F` and whose derivative coordinates are
the line derivatives of `f`.

For the reciprocal of a coefficient bounded below, the function
`positiveReciprocal δ r = (max δ r)⁻¹` agrees with `r⁻¹` on `[δ, ∞)`, is bounded by `δ⁻¹`,
and is Lipschitz with constant `δ⁻²`, so composing it with a Lipschitz `f` again gives a
Lipschitz function and hence a `W^{1,∞}` coefficient `positiveReciprocalW1Top`. This is how
`1/a` is formed for a Lipschitz elliptic coefficient `a ≥ δ > 0` in the interior `H²`
regularity theory, where Lipschitz leading coefficients are the standard hypothesis.

Evans, PDE, §5.8.2, Theorem 4, proves that a Lipschitz function on `ℝ^n` is in `W^{1,∞}` by
extracting a weak limit of the difference quotients `D_i^{-h} u`, which are bounded by `Lip(u)`
(step 2, (12), p. 294). The weak derivative is identified with the pointwise gradient only later,
through Theorem 5 of §5.8.3 and Rademacher's theorem (Theorem 6, p. 296). We obtain the pointwise
line derivative as the weak derivative at once, from Mathlib's formula.

## Main results

* `LipschitzWith.hasWeakDerivativeOn_lipschitzWeakCoord`: on `ℝ^n`, the line derivative of a
  Lipschitz `f` in the direction `eᵢ` is a weak partial derivative of `f`.
* `w1TopOfLipschitzRepresentative`, `w1TopOfLipschitzRepresentative_base_ae`: the
  `W^{1,∞}(Ω)` coefficient with base coordinate `F`.
* `lipschitzWith_positiveReciprocal`: `positiveReciprocal δ` is `δ⁻²`-Lipschitz for `δ > 0`.
* `positiveReciprocalW1Top`, `positiveReciprocalW1Top_base_ae`: the clipped reciprocal of a
  Lipschitz field as a `W^{1,∞}(Ω)` coefficient.

## Implementation notes

The weak-derivative identity is proved on all of `ℝ^n` from Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq` and then restricted to `Ω`; this is why only
`MeasurableSet Ω` is assumed rather than openness. The `L^∞` class `F` and the function `f`
are kept separate so that a coefficient handed over as an `Lp` element can be upgraded to
`W^{1,∞}` as soon as one of its representatives is Lipschitz.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2, Theorem 4, pp. 294-295, the characterization of
  `W^{1,∞}(U)` by Lipschitz continuity on bounded `C¹` domains, and the Remark on p. 295 for the
  local version on any open set; §5.8.3, Theorems 5 and 6, pp. 295-296, differentiability almost
  everywhere and Rademacher's theorem.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8, Generalized Solutions and Regularity,
  pp. 177-218, for interior `W^{2,2}` regularity under Lipschitz leading coefficients.
  <https://doi.org/10.1007/978-3-642-61798-0>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-! ## A globally Lipschitz reciprocal above a positive threshold -/

/-- The reciprocal clipped away from zero.  On `r ≥ δ` this is exactly
`r⁻¹`, while its global definition is bounded and Lipschitz when `δ > 0`. -/
def positiveReciprocal (δ r : ℝ) : ℝ :=
  (max δ r)⁻¹

/-- A concrete Lipschitz constant for the reciprocal clipped at `δ`. -/
def positiveReciprocalLipConst (δ : ℝ) : NNReal :=
  ⟨(δ ^ 2)⁻¹, inv_nonneg.mpr (sq_nonneg δ)⟩

/-- Above the threshold the clipped reciprocal is the reciprocal: `positiveReciprocal δ r =
r⁻¹` whenever `δ ≤ r`. -/
theorem positiveReciprocal_eq_inv {δ r : ℝ} (hr : δ ≤ r) :
    positiveReciprocal δ r = r⁻¹ := by
  simp [positiveReciprocal, max_eq_right hr]

/-- For `δ > 0` the clipped reciprocal is bounded by `δ⁻¹` at every point, since
`max δ r ≥ δ`. -/
theorem abs_positiveReciprocal_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    |positiveReciprocal δ r| ≤ δ⁻¹ := by
  rw [positiveReciprocal, abs_inv,
    abs_of_pos (hδ.trans_le (le_max_left δ r))]
  exact (inv_le_inv₀
    (hδ.trans_le (le_max_left δ r)) hδ).2 (le_max_left δ r)

/-- Quantitative global Lipschitz bound for the clipped reciprocal. -/
theorem lipschitzWith_positiveReciprocal {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (positiveReciprocalLipConst δ) (positiveReciprocal δ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let X := max δ x
  let Y := max δ y
  have hX : δ ≤ X := le_max_left _ _
  have hY : δ ≤ Y := le_max_left _ _
  have hXpos : 0 < X := hδ.trans_le hX
  have hYpos : 0 < Y := hδ.trans_le hY
  have hnum : |Y - X| ≤ |y - x| := by
    simpa [X, Y, max_comm] using abs_max_sub_max_le_abs y x δ
  have hden : δ ^ 2 ≤ |X * Y| := by
    rw [abs_of_pos (mul_pos hXpos hYpos)]
    nlinarith
  have hdenpos : 0 < |X * Y| := abs_pos.mpr (mul_ne_zero hXpos.ne' hYpos.ne')
  have hinvden : |X * Y|⁻¹ ≤ (δ ^ 2)⁻¹ := by
    exact (inv_le_inv₀ hdenpos (sq_pos_of_pos hδ)).2 hden
  change |X⁻¹ - Y⁻¹| ≤ (δ ^ 2)⁻¹ * |x - y|
  rw [inv_sub_inv hXpos.ne' hYpos.ne', abs_div]
  calc
    |Y - X| / |X * Y| = |Y - X| * |X * Y|⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ |y - x| * (δ ^ 2)⁻¹ :=
      mul_le_mul hnum hinvden (inv_nonneg.mpr (abs_nonneg _)) (abs_nonneg _)
    _ = (δ ^ 2)⁻¹ * |x - y| := by
      rw [abs_sub_comm]
      ring

/-- The clipped reciprocal of a Lipschitz representative is globally
bounded and therefore defines an `L∞` class on every measurable domain. -/
theorem memLp_positiveReciprocal_comp
    {δ : ℝ} (hδ : 0 < δ) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) :
    MemLp (fun x ↦ positiveReciprocal δ (f x)) ∞
      (domainMeasure n Ω) := by
  have hcont : Continuous (fun x ↦ positiveReciprocal δ (f x)) :=
    (lipschitzWith_positiveReciprocal hδ).continuous.comp hf.continuous
  apply memLp_top_of_bound hcont.aestronglyMeasurable δ⁻¹
  filter_upwards with x
  simpa [Real.norm_eq_abs] using abs_positiveReciprocal_le hδ (f x)

/-- The `L∞` class represented by the clipped reciprocal of a Lipschitz
function. -/
noncomputable def positiveReciprocalLp
    {δ : ℝ} (hδ : 0 < δ) (f : ℝ^n → ℝ) (C : NNReal)
    (hf : LipschitzWith C f) : DerivLp n ∞ Ω :=
  (memLp_positiveReciprocal_comp (Ω := Ω) hδ f hf).toLp
    (fun x ↦ positiveReciprocal δ (f x))

/-- The `L∞` class `positiveReciprocalLp` is represented almost everywhere
by the clipped reciprocal of the original Lipschitz function. -/
theorem positiveReciprocalLp_apply_ae
    {δ : ℝ} (hδ : 0 < δ) (f : ℝ^n → ℝ) (C : NNReal)
    (hf : LipschitzWith C f) :
    (positiveReciprocalLp (Ω := Ω) hδ f C hf : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ positiveReciprocal δ (f x) := by
  exact (memLp_positiveReciprocal_comp (Ω := Ω) hδ f hf).coeFn_toLp

/-- The line derivative of `f` in the direction of the `i`-th basis vector `eᵢ`. -/
def lipschitzWeakCoord (f : ℝ^n → ℝ) (i : Fin n) : ℝ^n → ℝ :=
  fun x ↦ lineDeriv ℝ f x (EuclideanSpace.single i (1 : ℝ))

/-- If `f : ℝ^n → ℝ` is Lipschitz, its line derivative `lipschitzWeakCoord f i` in the direction
`eᵢ` is the weak partial derivative `∂ᵢ f` on `ℝ^n`. -/
theorem LipschitzWith.hasWeakDerivativeOn_lipschitzWeakCoord
    {C : NNReal} {f : ℝ^n → ℝ} (hf : LipschitzWith C f)
    (i : Fin n) :
    HasWeakDerivativeOn (n := n) Set.univ [i] f
      (lipschitzWeakCoord (n := n) f i) := by
  let e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  have hgLp : MemLp (lipschitzWeakCoord (n := n) f i) ∞
      (domainMeasure n (Set.univ : Set (ℝ^n))) := by
    refine memLp_top_of_bound ?_ (C * ‖e‖) ?_
    · change AEStronglyMeasurable
        (fun x : ℝ^n ↦ lineDeriv ℝ f x e)
        (domainMeasure n (Set.univ : Set (ℝ^n)))
      exact aestronglyMeasurable_lineDeriv hf.continuous
        (domainMeasure n (Set.univ : Set (ℝ^n)))
    · exact .of_forall fun _x ↦ by
        simpa only [lipschitzWeakCoord, e] using
          (norm_lineDeriv_le_of_lipschitz ℝ hf)
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn Set.univ,
    memLp_locallyIntegrableOn_domain hgLp le_top, ?_⟩
  intro φ _hφ
  obtain ⟨D, hφLip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      φ.hasCompactSupport φ.contDiff (by simp)
  have hline := hf.integral_lineDeriv_mul_eq
    (μ := (volume : Measure (ℝ^n))) hφLip φ.hasCompactSupport e
  have hsmooth (x : ℝ^n) :
      lineDeriv ℝ φ.toFun x (-e) =
        -(∂[i] φ.toFun) x := by
    change lineDeriv ℝ (fun y ↦ φ y) x (-e) =
      -(∂[i] (fun y ↦ φ y)) x
    rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    simp [e, partialDeriv]
  have hline' :
      (∫ x, lipschitzWeakCoord (n := n) f i x * φ.toFun x
          ∂(volume : Measure (ℝ^n))) =
        -(∫ x, f x * (∂[i] φ.toFun) x
          ∂(volume : Measure (ℝ^n))) := by
    have hline0 :
        (∫ x, lineDeriv ℝ f x e * φ.toFun x
            ∂(volume : Measure (ℝ^n))) =
          ∫ x, lineDeriv ℝ φ.toFun x (-e) * f x
            ∂(volume : Measure (ℝ^n)) := by
      change
        (∫ x, lineDeriv ℝ f x e * φ.toFun x ∂(volume : Measure (ℝ^n))) =
          ∫ x, lineDeriv ℝ φ.toFun x (-e) * f x ∂(volume : Measure (ℝ^n)) at hline
      exact hline
    rw [show (∫ x, lipschitzWeakCoord (n := n) f i x * φ.toFun x
          ∂(volume : Measure (ℝ^n))) =
        ∫ x, lineDeriv ℝ f x e * φ.toFun x
          ∂(volume : Measure (ℝ^n)) by rfl,
      hline0]
    simp_rw [hsmooth]
    calc
      (∫ x, -(∂[i] φ.toFun) x * f x
          ∂(volume : Measure (ℝ^n))) =
          ∫ x, -(f x * (∂[i] φ.toFun) x)
            ∂(volume : Measure (ℝ^n)) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = -(∫ x, f x * (∂[i] φ.toFun) x
          ∂(volume : Measure (ℝ^n))) := MeasureTheory.integral_neg _
  have hfinal :
      (∫ x, f x * (∂[i] φ.toFun) x
          ∂(volume : Measure (ℝ^n))) =
        -(∫ x, lipschitzWeakCoord (n := n) f i x * φ.toFun x
          ∂(volume : Measure (ℝ^n))) := by
    linarith [hline']
  simpa [domainMeasure, iteratedPartialDeriv] using hfinal

/-- Certified first-order rows for a Lipschitz representative of an `L∞`
class. -/
def lipschitzRepresentativeRows
    (F : DerivLp n ∞ Ω) (f : ℝ^n → ℝ) :
    DerivIndex n 1 → ℝ^n → ℝ :=
  firstOrderRows (F : ℝ^n → ℝ) (lipschitzWeakCoord (n := n) f)

/-- The base row of the Lipschitz representative rows is the `L^∞` class `F` itself. -/
@[simp]
theorem lipschitzRepresentativeRows_base
    (F : DerivLp n ∞ Ω) (f : ℝ^n → ℝ) :
    lipschitzRepresentativeRows F f (baseIndex n 1) =
      (F : ℝ^n → ℝ) := by
  simp [lipschitzRepresentativeRows]

/-- Every row is in `L^∞(Ω)`: the base row because `F` is an `L^∞` class, and each derivative
row because the line derivatives of a `C`-Lipschitz function are bounded by `C`. -/
theorem lipschitzRepresentativeRows_memLp
    (F : DerivLp n ∞ Ω) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f) (r : DerivIndex n 1) :
    MemLp (lipschitzRepresentativeRows F f r) ∞
      (domainMeasure n Ω) := by
  have hdLp (i : Fin n) : MemLp (lipschitzWeakCoord (n := n) f i) ∞
      (domainMeasure n Ω) := by
    change MemLp
      (fun x : ℝ^n ↦ lineDeriv ℝ f x (EuclideanSpace.single i (1 : ℝ)))
      ∞ (volume.restrict Ω)
    exact
      (hf.memLp_lineDeriv (μ := (volume : Measure (ℝ^n)))
        (EuclideanSpace.single i (1 : ℝ))).mono_measure Measure.restrict_le_self
  rcases r.eq_baseIndex_or_eq_singleDerivIndex with hr | ⟨i, hr⟩
  · subst r
    simpa [lipschitzRepresentativeRows] using MeasureTheory.Lp.memLp F
  · subst r
    simpa [lipschitzRepresentativeRows] using hdLp i

/-- Each row is the weak derivative of `F` for its index. The line derivative of `f` is a weak
partial derivative of `f` on `ℝ^n`; this restricts to the measurable set `Ω`, and the a.e.
equality `F = f` on `Ω` transfers it to `F`. The base row is trivially the order-zero weak
derivative of `F`. -/
theorem lipschitzRepresentativeRows_weak
    (hΩmeas : MeasurableSet Ω)
    (F : DerivLp n ∞ Ω) (f : ℝ^n → ℝ) {C : NNReal}
    (hf : LipschitzWith C f)
    (hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f)
    (r : DerivIndex n 1) :
    HasWeakDerivativeOn (n := n) Ω r.toList (F : ℝ^n → ℝ)
      (lipschitzRepresentativeRows F f r) := by
  have hweak (i : Fin n) : HasWeakDerivativeOn (n := n) Ω [i]
      (F : ℝ^n → ℝ) (lipschitzWeakCoord (n := n) f i) := by
    have hglobal := LipschitzWith.hasWeakDerivativeOn_lipschitzWeakCoord
      (n := n) hf i
    have hlocal := hglobal.mono (n := n) (Ω' := Ω)
      hΩmeas (subset_univ Ω)
    exact (hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := Ω) (α := [i]) hF Filter.EventuallyEq.rfl).2
        hlocal
  rcases r.eq_baseIndex_or_eq_singleDerivIndex with hr | ⟨i, hr⟩
  · subst r
    have hloc := memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp F) le_top
    simpa [lipschitzRepresentativeRows, iteratedPartialDeriv] using
      (show HasWeakDerivativeOn (n := n) Ω []
          (F : ℝ^n → ℝ) (F : ℝ^n → ℝ) from
        hasWeakDerivativeOn_nil hloc)
  · subst r
    simpa [lipschitzRepresentativeRows] using hweak i

/-- A Lipschitz representative of an `L∞` class canonically determines a
`W^{1,∞}` coefficient.  This is how a Lipschitz elliptic coefficient
enters the interior `H²` regularity theory as a `W^{1,∞}` multiplier. -/
noncomputable def w1TopOfLipschitzRepresentative
    (hΩmeas : MeasurableSet Ω)
    (F : DerivLp n ∞ Ω) (f : ℝ^n → ℝ) (C : NNReal)
    (hf : LipschitzWith C f)
    (hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f) :
    W^{1,∞}(Ω) :=
  mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := (∞ : ℝ≥0∞)) (Ω := Ω)
    (F : ℝ^n → ℝ) (lipschitzRepresentativeRows F f)
    (lipschitzRepresentativeRows_base F f)
    (lipschitzRepresentativeRows_memLp F f hf)
    (lipschitzRepresentativeRows_weak hΩmeas F f hf hF)

/-- The base coordinate of this `W^{1,∞}` coefficient is `F` almost everywhere on
`Ω`. -/
theorem w1TopOfLipschitzRepresentative_base_ae
    (hΩmeas : MeasurableSet Ω)
    (F : DerivLp n ∞ Ω) (f : ℝ^n → ℝ) (C : NNReal)
    (hf : LipschitzWith C f)
    (hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f) :
    ((((w1TopOfLipschitzRepresentative hΩmeas F f C hf hF :
        WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω) :
      ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω] (F : ℝ^n → ℝ) := by
  simpa [w1TopOfLipschitzRepresentative,
    lipschitzRepresentativeRows] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := (∞ : ℝ≥0∞)) (Ω := Ω)
      (f := (F : ℝ^n → ℝ))
      (d := lipschitzRepresentativeRows F f)
      (hbase := lipschitzRepresentativeRows_base F f)
      (hmem := lipschitzRepresentativeRows_memLp F f hf)
      (hweak := lipschitzRepresentativeRows_weak hΩmeas F f hf hF)
      (a := baseIndex n 1)

/-- The canonical `W^{1,∞}` coefficient given by the clipped reciprocal of a globally
Lipschitz scalar field. -/
noncomputable def positiveReciprocalW1Top
    (hΩmeas : MeasurableSet Ω) {δ : ℝ} (hδ : 0 < δ)
    (f : ℝ^n → ℝ) (C : NNReal) (hf : LipschitzWith C f) :
    W^{1,∞}(Ω) :=
  w1TopOfLipschitzRepresentative hΩmeas
    (positiveReciprocalLp (Ω := Ω) hδ f C hf)
    (fun x ↦ positiveReciprocal δ (f x))
    (positiveReciprocalLipConst δ * C)
    ((lipschitzWith_positiveReciprocal hδ).comp hf)
    (positiveReciprocalLp_apply_ae (Ω := Ω) hδ f C hf)

/-- The base coordinate of `positiveReciprocalW1Top` is the clipped reciprocal
`x ↦ (max δ (f x))⁻¹` almost everywhere on `Ω`. The clipped reciprocal equals `1 / f x`
at every point where `f x ≥ δ`. -/
theorem positiveReciprocalW1Top_base_ae
    (hΩmeas : MeasurableSet Ω) {δ : ℝ} (hδ : 0 < δ)
    (f : ℝ^n → ℝ) (C : NNReal) (hf : LipschitzWith C f) :
    (((positiveReciprocalW1Top hΩmeas hδ f C hf :
        WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω) :
      ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ positiveReciprocal δ (f x) := by
  have hbase := w1TopOfLipschitzRepresentative_base_ae hΩmeas
    (positiveReciprocalLp (Ω := Ω) hδ f C hf)
    (fun x ↦ positiveReciprocal δ (f x))
    (positiveReciprocalLipConst δ * C)
    ((lipschitzWith_positiveReciprocal hδ).comp hf)
    (positiveReciprocalLp_apply_ae (Ω := Ω) hδ f C hf)
  exact hbase.trans (positiveReciprocalLp_apply_ae (Ω := Ω) hδ f C hf)

end SobolevSpace.GraphSpace
