/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Truncation
import PDE.Analysis.Calculus.SmoothTruncation
import PDE.Analysis.MeasureTheory.DominatedLp
import PDE.Spaces.Sobolev.Calculus.Composition.AbsoluteValue
import PDE.Spaces.Sobolev.GraphSpace.Topology.Convergence
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Closure
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Analysis.Calculus.AbsoluteValue

/-!
# Interval truncation in finite-exponent Sobolev spaces

We prove the weak chain rule for interval truncation on global
real-valued `W^{1,p}(ℝ^n)` spaces with finite exponent. On an infinite-measure
domain, the interval must contain zero so that the pointwise clamp preserves
global `Lᵖ` integrability.

Smooth zero-preserving truncations supply the approximation. Dominated
`Lᵖ` convergence and closedness of weak derivatives give the sign-difference
formula, while the arbitrary-level Stampacchia theorem sharpens it to

`∂ᵢ T_[a,b](u) = 1_{a < u < b} ∂ᵢu`

almost everywhere. Truncation is then an operation on the completed Sobolev
graph space.

This is the truncation lemma for `W^{1,p}` (Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Chapter 7, for `u⁺`; the clamp
`T_[a,b](u) = min (max u a) b` is built from shifted positive parts), sharpened by the level-set
theorem `∇u = 0` a.e. on `{u = c}`, which is what allows the derivative to be written with the
open-interval indicator `1_{a < u < b}` rather than a sign-difference coefficient that is ambiguous
on the level sets.

## Main results

* `hasWeakDerivativeOn_centeredIntervalTruncation`,
  `hasWeakDerivativeOn_intervalTruncation`: the weak chain rule for the centered clamp
  `T_[a,b] - T_[a,b](0)` and, when `a ≤ 0 ≤ b`, for the clamp itself.
* `centeredIntervalTruncation`, `intervalTruncation`: the corresponding operations on
  `W^{1,p}(ℝ^n)`, with `_base_ae`, `_derivative_ae` and `_derivative_indicator_ae` lemmas
  describing their coordinates almost everywhere.
* `tendsto_intervalTruncation_zero`: clamping to a shrinking interval about zero converges
  strongly to zero in every finite exponent. This supplies support-preserving approximations
  without assuming smoothness of the boundary.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7, Sobolev Spaces, pp. 144-176, for the
  truncation lemma in `W^{1,p}` and the vanishing of `Du` a.e. on level sets.
  <https://doi.org/10.1007/978-3-642-61798-0>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.10, Problem 18, p. 308, the exercise, for bounded `U`,
  that `u⁺, u⁻ ∈ W^{1,p}(U)` with the expected derivatives and that `Du = 0` a.e. on `{u = 0}`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set Function ENNReal
open scoped Topology Sobolev

private theorem aestronglyMeasurable_intervalTruncationSlope_comp
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {u : α → ℝ} (hu : AEStronglyMeasurable u μ)
    (a b : ℝ) :
    AEStronglyMeasurable
      (fun x ↦
        ((SignType.sign (u x - a) : ℝ) -
          (SignType.sign (u x - b) : ℝ)) / 2) μ :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun k ↦ (PDE.Analysis.Calculus.continuous_smoothIntervalTruncationSlope
      (Nat.one_div_pos_of_nat (n := k)) a b).comp_aestronglyMeasurable hu)
    (.of_forall fun x ↦
      PDE.Analysis.Calculus.tendsto_smoothIntervalTruncationSlope_of_tendsto_zero
        tendsto_one_div_add_atTop_nhds_zero_nat a b (u x))

/-- A multiplier bounded by one keeps a function in `Lᵖ`. -/
private theorem memLp_mul_of_abs_le_one {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p : ℝ≥0∞} {s f : α → ℝ} (hs : AEStronglyMeasurable s μ) (h1 : ∀ x, |s x| ≤ 1)
    (hf : MemLp f p μ) :
    MemLp (fun x ↦ s x * f x) p μ :=
  hf.of_le_mul (c := 1) (hs.mul hf.aestronglyMeasurable) (.of_forall fun x ↦ by
    rw [norm_mul, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 x))

/-- Centered interval truncation obeys the weak Sobolev chain rule in every
finite exponent. -/
theorem hasWeakDerivativeOn_centeredIntervalTruncation
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    let u : ℝ^n → ℝ :=
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p) (Ω := Set.univ) U :
          ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      (wkpCoordinateCLM
        (n := n) (p := p) (Ω := Set.univ)
        (singleDerivIndex n i) U : ℝ^n → ℝ)
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (fun x ↦
        PDE.Analysis.Calculus.centeredIntervalTruncation a b (u x))
      (fun x ↦
        (((SignType.sign (u x - a) : ℝ) -
          (SignType.sign (u x - b) : ℝ)) / 2) * du x) := by
  intro u du
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := Nat.one_div_pos_of_nat
  have hεzero : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have huMem : MemLp u p (domainMeasure n Set.univ) :=
    Lp.memLp (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Set.univ) U)
  have hduMem : MemLp du p (domainMeasure n Set.univ) :=
    Lp.memLp (wkpCoordinateCLM (n := n) (p := p) (Ω := Set.univ) (singleDerivIndex n i) U)
  have hslopeMeas (k : ℕ) : AEStronglyMeasurable
      (fun x ↦ PDE.Analysis.Calculus.smoothIntervalTruncationSlope (ε k) a b (u x))
      (domainMeasure n Set.univ) :=
    (PDE.Analysis.Calculus.continuous_smoothIntervalTruncationSlope (hεpos k) a b
      ).comp_aestronglyMeasurable huMem.aestronglyMeasurable
  have hslopeLimitMeas :=
    aestronglyMeasurable_intervalTruncationSlope_comp huMem.aestronglyMeasurable a b
  have hfSeqMem (k : ℕ) := (PDE.Analysis.Calculus.lipschitzWith_smoothIntervalTruncation
    (hεpos k) a b).comp_memLp (PDE.Analysis.Calculus.smoothIntervalTruncation_zero (ε k) a b) huMem
  have htargetMem := (PDE.Analysis.Calculus.lipschitzWith_centeredIntervalTruncation hab
    ).comp_memLp (PDE.Analysis.Calculus.centeredIntervalTruncation_zero a b) huMem
  -- the smooth truncations and their derivatives converge in `Lᵖ` by dominated convergence
  have hfSeqTendsto := tendsto_Lp_of_tendsto_ae_of_ae_norm_le Fact.out hp_top
    (fun k ↦ (hfSeqMem k).aestronglyMeasurable) htargetMem huMem
    (fun k ↦ .of_forall fun x ↦
      PDE.Analysis.Calculus.abs_smoothIntervalTruncation_le (hεpos k) a b (u x))
    (.of_forall fun x ↦
      PDE.Analysis.Calculus.tendsto_smoothIntervalTruncation_centered_of_tendsto_zero
        (.of_forall fun k ↦ (hεpos k).le) hεzero a b (u x))
  have hgSeqTendsto := tendsto_eLpNorm_mul_of_tendsto_ae_of_tendsto_eLpNorm Fact.out hp_top
    hslopeMeas hslopeLimitMeas (fun _ ↦ hduMem) hduMem
    (fun k ↦ .of_forall fun x ↦
      PDE.Analysis.Calculus.abs_smoothIntervalTruncationSlope_le_one (hεpos k) a b (u x))
    (.of_forall fun x ↦ PDE.Analysis.Calculus.abs_sign_sub_sign_div_two_le_one a b (u x))
    (.of_forall fun x ↦
      PDE.Analysis.Calculus.tendsto_smoothIntervalTruncationSlope_of_tendsto_zero
        hεzero a b (u x))
    (by simp)
  exact WeakChangeOfVariables.hasWeakDerivativeOn_of_tendsto_eLpNorm hfSeqMem
    (fun k ↦ memLp_mul_of_abs_le_one (hslopeMeas k) (fun x ↦
      PDE.Analysis.Calculus.abs_smoothIntervalTruncationSlope_le_one (hεpos k) a b (u x)) hduMem)
    htargetMem (memLp_mul_of_abs_le_one hslopeLimitMeas
      (fun x ↦ PDE.Analysis.Calculus.abs_sign_sub_sign_div_two_le_one a b (u x)) hduMem)
    (fun k ↦ hasWeakDerivativeOn_comp_of_hasDerivAt
      (PDE.Analysis.Calculus.hasDerivAt_smoothIntervalTruncation (hεpos k) a b)
      (PDE.Analysis.Calculus.smoothIntervalTruncation_zero (ε k) a b)
      (PDE.Analysis.Calculus.abs_smoothIntervalTruncationSlope_le_one (hεpos k) a b) U i)
    hfSeqTendsto hgSeqTendsto

/-- Interval truncation obeys the weak Sobolev chain rule in every finite
exponent when the truncation interval contains zero. -/
theorem hasWeakDerivativeOn_intervalTruncation
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    let u : ℝ^n → ℝ :=
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p) (Ω := Set.univ) U :
          ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      (wkpCoordinateCLM
        (n := n) (p := p) (Ω := Set.univ)
        (singleDerivIndex n i) U : ℝ^n → ℝ)
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (fun x ↦ PDE.Analysis.Calculus.intervalTruncation a b (u x))
      (fun x ↦
        (((SignType.sign (u x - a) : ℝ) -
          (SignType.sign (u x - b) : ℝ)) / 2) * du x) := by
  simpa [
    PDE.Analysis.Calculus.centeredIntervalTruncation_eq_intervalTruncation
      ha hb] using
    hasWeakDerivativeOn_centeredIntervalTruncation
      hp_top (ha.trans hb) U i

/-- The base function of centered interval truncation: the truncation applied
to the base coordinate representative of `U`. -/
abbrev centeredIntervalTruncationBase
    {n : ℕ} {p : ℝ≥0∞}
    (a b : ℝ) (U : W^{1,p}(ℝ^n)) :
    ℝ^n → ℝ :=
  PDE.Analysis.Calculus.centeredIntervalTruncation a b ∘
    ((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)

/-- The coordinate rows of centered interval truncation: the base row is the
truncated representative and the `i`th derivative row is the slope times
`∂ᵢu`. -/
def centeredIntervalTruncationRows
    {n : ℕ} {p : ℝ≥0∞}
    (a b : ℝ) (U : W^{1,p}(ℝ^n))
    (d : DerivIndex n 1) :
    ℝ^n → ℝ :=
  firstOrderRows (centeredIntervalTruncationBase a b U)
    (fun i x ↦
        (((SignType.sign
            ((((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) - a) : ℝ) -
          (SignType.sign
            ((((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) - b) : ℝ)) / 2) *
          ((U : WkpAmbientOn n 1 p Set.univ)
            (singleDerivIndex n i) : ℝ^n → ℝ) x)
    d

/-- The base row of `centeredIntervalTruncationRows` is
`centeredIntervalTruncationBase`. -/
theorem centeredIntervalTruncationRows_base
    {n : ℕ} {p : ℝ≥0∞}
    (a b : ℝ) (U : W^{1,p}(ℝ^n)) :
    centeredIntervalTruncationRows a b U (baseIndex n 1) =
      centeredIntervalTruncationBase a b U := by
  simp [centeredIntervalTruncationRows]

/-- Every row of `centeredIntervalTruncationRows` lies in `Lp`. -/
theorem centeredIntervalTruncationRows_memLp
    {n : ℕ} {p : ℝ≥0∞}
    {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(ℝ^n)) (d : DerivIndex n 1) :
    MemLp (centeredIntervalTruncationRows a b U d)
      p (domainMeasure n Set.univ) := by
  rcases d.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa [centeredIntervalTruncationRows] using
      (PDE.Analysis.Calculus.lipschitzWith_centeredIntervalTruncation hab).comp_memLp
        (PDE.Analysis.Calculus.centeredIntervalTruncation_zero a b)
        (Lp.memLp ((U : WkpAmbientOn n 1 p Set.univ) (baseIndex n 1)))
  · rw [centeredIntervalTruncationRows, firstOrderRows_singleDerivIndex]
    exact memLp_mul_of_abs_le_one
      (aestronglyMeasurable_intervalTruncationSlope_comp (Lp.memLp _).aestronglyMeasurable a b)
      (fun x ↦ PDE.Analysis.Calculus.abs_sign_sub_sign_div_two_le_one a b _) (Lp.memLp _)

/-- Each row of `centeredIntervalTruncationRows` is the corresponding weak
derivative of `centeredIntervalTruncationBase` on the whole space. -/
theorem centeredIntervalTruncationRows_weak
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(ℝ^n)) (d : DerivIndex n 1) :
    HasWeakDerivativeOn (n := n) Set.univ d.toList
      (centeredIntervalTruncationBase a b U)
      (centeredIntervalTruncationRows a b U d) := by
  rcases d.eq_baseIndex_or_eq_singleDerivIndex with hd | ⟨i, hd⟩
  · subst d
    have hloc :=
      memLp_locallyIntegrableOn_domain
        (centeredIntervalTruncationRows_memLp hab U (baseIndex n 1))
        (Fact.out : (1 : ℝ≥0∞) ≤ p)
    have hloc' :
        LocallyIntegrableOn (centeredIntervalTruncationBase a b U)
          Set.univ (volume : Measure (ℝ^n)) := by
      simpa [centeredIntervalTruncationRows] using hloc
    simpa [centeredIntervalTruncationRows, iteratedPartialDeriv] using
      (show HasWeakDerivativeOn (n := n) Set.univ []
        (centeredIntervalTruncationBase a b U)
        (centeredIntervalTruncationBase a b U) from
        hasWeakDerivativeOn_nil hloc')
  · subst d
    rw [singleDerivIndex_toList]
    refine (hasWeakDerivativeOn_congr_ae (.of_forall fun _ ↦ rfl) (.of_forall fun x ↦ ?_)).2
      (hasWeakDerivativeOn_centeredIntervalTruncation hp_top hab U i)
    simp [centeredIntervalTruncationRows]

/-- Centered interval truncation as an operation on global finite-exponent
`W^{1,p}`. -/
noncomputable def centeredIntervalTruncation
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(ℝ^n)) :
    W^{1,p}(ℝ^n) :=
  mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := p) (Ω := Set.univ)
    (centeredIntervalTruncationBase a b U)
    (centeredIntervalTruncationRows a b U)
    (centeredIntervalTruncationRows_base a b U)
    (centeredIntervalTruncationRows_memLp hab U)
    (centeredIntervalTruncationRows_weak hp_top hab U)

/-- The base coordinate of centered Sobolev interval truncation is the
centered pointwise clamp almost everywhere. -/
theorem centeredIntervalTruncation_base_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(ℝ^n)) :
    (((centeredIntervalTruncation hp_top hab U :
        WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          PDE.Analysis.Calculus.centeredIntervalTruncation a b
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) := by
  exact
    (mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (centeredIntervalTruncationBase a b U)
      (centeredIntervalTruncationRows a b U)
      (centeredIntervalTruncationRows_base a b U)
      (centeredIntervalTruncationRows_memLp hab U)
      (centeredIntervalTruncationRows_weak hp_top hab U)
      (baseIndex n 1)).trans <| by
        filter_upwards [] with x
        simp [centeredIntervalTruncationRows,
          centeredIntervalTruncationBase]

/-- The derivative coordinate of centered Sobolev interval truncation is the
sign-difference multiplier times the corresponding derivative. -/
theorem centeredIntervalTruncation_derivative_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((centeredIntervalTruncation hp_top hab U :
        WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          (((SignType.sign
            ((((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) - a) : ℝ) -
            (SignType.sign
              ((((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x) - b) : ℝ)) / 2) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x := by
  simpa [centeredIntervalTruncation,
    centeredIntervalTruncationRows] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (centeredIntervalTruncationBase a b U)
      (centeredIntervalTruncationRows a b U)
      (centeredIntervalTruncationRows_base a b U)
      (centeredIntervalTruncationRows_memLp hab U)
      (centeredIntervalTruncationRows_weak hp_top hab U)
      (singleDerivIndex n i)

/-- The derivative of centered interval truncation is the original derivative
on the open interval and zero outside it, almost everywhere. -/
theorem centeredIntervalTruncation_derivative_indicator_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((centeredIntervalTruncation hp_top hab U :
        WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          if a <
              ((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x ∧
              ((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x < b then
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x
          else 0 := by
  let u : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)
  let du : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : ℝ^n → ℝ)
  filter_upwards [centeredIntervalTruncation_derivative_ae hp_top hab U i,
    derivative_eq_zero_ae_of_base_eq U i a, derivative_eq_zero_ae_of_base_eq U i b]
    with x hderiv hlevela hlevelb
  change _ = if a < u x ∧ u x < b then du x else 0
  have hformula : _ = ((SignType.sign (u x - a) : ℝ) - SignType.sign (u x - b)) / 2 * du x :=
    hderiv
  rw [hformula]
  rcases lt_trichotomy (u x) a with hua | hua | hua
  · rw [ite_eq_right fun h ↦ lt_asymm hua h.1, sign_neg (sub_neg.2 hua),
      sign_neg (sub_neg.2 (hua.trans_le hab))]
    norm_num
  · rw [show du x = 0 from hlevela hua, mul_zero, ite_self]
  rcases lt_trichotomy (u x) b with hub | hub | hub
  · rw [ite_eq_left ⟨hua, hub⟩, sign_pos (sub_pos.2 hua), sign_neg (sub_neg.2 hub)]
    norm_num
  · rw [show du x = 0 from hlevelb hub, mul_zero, ite_self]
  · rw [ite_eq_right fun h ↦ lt_asymm hub h.2, sign_pos (sub_pos.2 hua),
      sign_pos (sub_pos.2 hub)]
    norm_num

/-- Interval truncation as an operation on global finite-exponent
`W^{1,p}`, when the truncation interval contains zero. -/
noncomputable def intervalTruncation
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (U : W^{1,p}(ℝ^n)) :
    W^{1,p}(ℝ^n) :=
  centeredIntervalTruncation hp_top (ha.trans hb) U

/-- The base coordinate of Sobolev interval truncation is the pointwise
clamp almost everywhere. -/
theorem intervalTruncation_base_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (U : W^{1,p}(ℝ^n)) :
    (((intervalTruncation hp_top ha hb U :
        WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          PDE.Analysis.Calculus.intervalTruncation a b
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) := by
  simpa [intervalTruncation,
    PDE.Analysis.Calculus.centeredIntervalTruncation_eq_intervalTruncation
      ha hb] using
    centeredIntervalTruncation_base_ae hp_top (ha.trans hb) U

/-- The derivative coordinate of Sobolev interval truncation is the
sign-difference multiplier times the corresponding derivative. -/
theorem intervalTruncation_derivative_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((intervalTruncation hp_top ha hb U :
        WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          (((SignType.sign
            ((((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) - a) : ℝ) -
            (SignType.sign
              ((((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x) - b) : ℝ)) / 2) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x := by
  exact centeredIntervalTruncation_derivative_ae
    hp_top (ha.trans hb) U i

/-- The derivative of interval truncation is the original derivative on the
open interval and zero outside it, almost everywhere. -/
theorem intervalTruncation_derivative_indicator_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((intervalTruncation hp_top ha hb U :
        WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          if a <
              ((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x ∧
              ((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x < b then
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x
          else 0 := by
  exact centeredIntervalTruncation_derivative_indicator_ae
    hp_top (ha.trans hb) U i

/-- Clamping to a shrinking interval about zero converges strongly to zero in every
finite-exponent Sobolev space. The derivative vanishes on the zero level set. -/
theorem tendsto_intervalTruncation_zero
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (U : W^{1,p}(ℝ^n)) {ε : ℕ → ℝ} (hε : ∀ j, 0 ≤ ε j)
    (hεzero : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j ↦ intervalTruncation hp_top (neg_nonpos.mpr (hε j)) (hε j) U)
      atTop (𝓝 0) := by
  let V (j : ℕ) : W^{1,p}(ℝ^n) := intervalTruncation hp_top (neg_nonpos.mpr (hε j)) (hε j) U
  let u : ℝ^n → ℝ := wkpCoordinateCLM (baseIndex n 1) U
  apply tendsto_wkp_of_coordinate_eLpNorm (U := V)
  intro a
  have heq (j : ℕ) :
      eLpNorm ((wkpCoordinateCLM a (V j) : ℝ^n → ℝ) -
        (wkpCoordinateCLM a (0 : W^{1,p}(ℝ^n)) : ℝ^n → ℝ)) p
          (domainMeasure n univ) =
        eLpNorm (wkpCoordinateCLM a (V j) : ℝ^n → ℝ) p (domainMeasure n univ) := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_zero ℝ p (domainMeasure n univ)] with x hx
    simp only [map_zero, Pi.sub_apply, hx, Pi.zero_apply, sub_zero]
  simp_rw [heq]
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · have hbase (j : ℕ) :
        (wkpCoordinateCLM (baseIndex n 1) (V j) : ℝ^n → ℝ) =ᵐ[domainMeasure n univ]
          fun x ↦ PDE.Analysis.Calculus.intervalTruncation (-ε j) (ε j) (u x) :=
      intervalTruncation_base_ae hp_top (neg_nonpos.mpr (hε j)) (hε j) U
    have hdom (j : ℕ) : ∀ᵐ x ∂domainMeasure n univ,
        ‖(wkpCoordinateCLM (baseIndex n 1) (V j) : ℝ^n → ℝ) x‖ ≤ ‖u x‖ := by
      filter_upwards [hbase j] with x hx
      rw [hx, ← PDE.Analysis.Calculus.centeredIntervalTruncation_eq_intervalTruncation
        (neg_nonpos.mpr (hε j)) (hε j)]
      simpa using (PDE.Analysis.Calculus.lipschitzWith_centeredIntervalTruncation
        (by linarith [hε j] : -ε j ≤ ε j)).norm_sub_le (u x) 0
    have hpoint : ∀ᵐ x ∂domainMeasure n univ,
        Tendsto (fun j ↦ (wkpCoordinateCLM (baseIndex n 1) (V j) : ℝ^n → ℝ) x)
          atTop (𝓝 0) := by
      filter_upwards [ae_all_iff.mpr hbase] with x hx
      refine squeeze_zero_norm (fun j ↦ ?_) hεzero
      rw [hx j, PDE.Analysis.Calculus.intervalTruncation_eq_min_max (neg_le_self (hε j)),
        Real.norm_eq_abs, abs_le]
      exact ⟨le_min (neg_le_self (hε j)) (le_max_left _ _), min_le_left _ _⟩
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using
      tendsto_Lp_of_tendsto_ae_of_ae_norm_le (Fact.out : 1 ≤ p) hp_top
        (fun j ↦ (Lp.memLp (wkpCoordinateCLM (baseIndex n 1) (V j))).aestronglyMeasurable)
        MemLp.zero (Lp.memLp (wkpCoordinateCLM (baseIndex n 1) U)) hdom hpoint
  · let du : ℝ^n → ℝ := wkpCoordinateCLM (singleDerivIndex n i) U
    have hderiv (j : ℕ) :
        (wkpCoordinateCLM (singleDerivIndex n i) (V j) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n univ] fun x ↦
            if -ε j < u x ∧ u x < ε j then du x else 0 :=
      intervalTruncation_derivative_indicator_ae hp_top
        (neg_nonpos.mpr (hε j)) (hε j) U i
    have hdom (j : ℕ) : ∀ᵐ x ∂domainMeasure n univ,
        ‖(wkpCoordinateCLM (singleDerivIndex n i) (V j) : ℝ^n → ℝ) x‖ ≤ ‖du x‖ := by
      filter_upwards [hderiv j] with x hx
      rw [hx]
      split_ifs <;> simp
    have hpoint : ∀ᵐ x ∂domainMeasure n univ,
        Tendsto (fun j ↦ (wkpCoordinateCLM (singleDerivIndex n i) (V j) : ℝ^n → ℝ) x)
          atTop (𝓝 0) := by
      filter_upwards [ae_all_iff.mpr hderiv,
        derivative_eq_zero_ae_of_base_eq_zero U i] with x hx hlevel
      refine tendsto_const_nhds.congr' ?_
      by_cases hu : u x = 0
      · have hd : du x = 0 := hlevel hu
        exact .of_forall fun j ↦ ((hx j).trans (by rw [hd, ite_self])).symm
      · filter_upwards [hεzero.eventually (gt_mem_nhds (abs_pos.mpr hu))] with j hj
        rw [hx j, ite_eq_right fun h ↦ lt_asymm hj (abs_lt.2 h)]
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using
      tendsto_Lp_of_tendsto_ae_of_ae_norm_le (Fact.out : 1 ≤ p) hp_top
        (fun j ↦ (Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) (V j))).aestronglyMeasurable)
        MemLp.zero (Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) U)) hdom hpoint


end SobolevSpace.GraphSpace
