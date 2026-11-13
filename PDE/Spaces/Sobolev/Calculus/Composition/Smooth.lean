/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.Lipschitz

/-!
# Smooth scalar composition in finite-exponent Sobolev spaces

We prove a global first-order Nemytskii theorem for zero-preserving
real scalar maps. If `F` is continuously differentiable, fixes zero, and has
derivative bounded by one, then

`∂ᵢ (F ∘ u) = (F' ∘ u) ∂ᵢ u`

for every real-valued `u ∈ W^{1,p}(ℝ^n)`, `1 ≤ p ≤ ∞`.

The weak chain rule is the Lipschitz chain rule `hasWeakDerivativeOn_comp_lipschitz`
with `deriv F = F'`. The zero-preserving hypothesis is necessary on the
infinite-measure domain `ℝ^n`: a nonzero constant need not belong to `Lᵖ`.

The derivative witness `F'` is explicit so that computed derivative formulas can be
used directly. Its continuity and the Lipschitz bound follow from the other hypotheses.

This is the chain rule for `C¹` maps with bounded derivative acting on `W^{1,p}` (Gilbarg and
Trudinger, *Elliptic Partial Differential Equations of Second Order*, Chapter 7; Evans, PDE, §5.10,
Problem 17, p. 308, poses it as an exercise on bounded domains, where `F(0) = 0` is not needed). The
one-Lipschitz normalization `|F'| ≤ 1` is a convenience, not a restriction: any `C¹` map with
bounded derivative is a constant multiple of such a map. On open domains the Lipschitz chain rule
`hasWeakDerivativeOn_comp_lipschitz_on` needs neither `F 0 = 0` nor `|F'| ≤ 1`.

## Main results

* `hasWeakDerivativeOn_comp_of_hasDerivAt`: the weak chain rule
  `∂ᵢ(F ∘ u) = (F' ∘ u) ∂ᵢu` on `ℝ^n` for `u ∈ W^{1,p}(ℝ^n)`.
* `smoothComposition`: `F ∘ U` as an element of `W^{1,p}(ℝ^n)`, with
  `smoothComposition_base_ae` and `smoothComposition_derivative_ae` describing its
  coordinates almost everywhere.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7, Sobolev Spaces, pp. 144-176, for the chain
  rule for `C¹` functions with bounded derivative on `W^{1,p}`.
  <https://doi.org/10.1007/978-3-642-61798-0>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.10, Problem 17, p. 308, the exercise that
  `F(u) ∈ W^{1,p}(U)` with `(F(u))_{x_i} = F'(u) u_{x_i}` for `F ∈ C¹` with `F'` bounded, `U`
  bounded, `u ∈ W^{1,p}(U)` and `1 ≤ p ≤ ∞`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set Function ENNReal
open scoped Topology Sobolev

private theorem continuous_scalar_derivative {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hFderiv : ∀ x, HasDerivAt F (F' x) x) :
    Continuous F' := by
  have heq : deriv F = F' := funext fun x ↦ (hFderiv x).deriv
  rw [← heq]
  exact hF.continuous_deriv_one

private theorem scalar_lipschitzWith_one {F F' : ℝ → ℝ}
    (hFderiv : ∀ x, HasDerivAt F (F' x) x)
    (hbound : ∀ x, |F' x| ≤ 1) : LipschitzWith 1 F := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hFderiv x).differentiableAt)
  intro x
  rw [(hFderiv x).deriv]
  exact_mod_cast (show ‖F' x‖ ≤ (1 : ℝ) by
    simpa only [Real.norm_eq_abs] using hbound x)

/-- A zero-preserving scalar map with derivative bounded by one obeys the weak chain rule
`∂ᵢ(F ∘ u) = (F' ∘ u) ∂ᵢu` on global real-valued `W^{1,p}` for every `1 ≤ p ≤ ∞`. This is
`hasWeakDerivativeOn_comp_lipschitz` with the derivative written as the explicit `F'`. -/
theorem hasWeakDerivativeOn_comp_of_hasDerivAt
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F F' : ℝ → ℝ}
    (hFderiv : ∀ x, HasDerivAt F (F' x) x)
    (hFzero : F 0 = 0)
    (hF'bound : ∀ x, |F' x| ≤ 1)
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
      (fun x ↦ F (u x))
      (fun x ↦ F' (u x) * du x) := by
  have hderiv : deriv F = F' := funext fun x ↦ (hFderiv x).deriv
  simpa only [Function.comp_def, hderiv] using
    hasWeakDerivativeOn_comp_lipschitz (scalar_lipschitzWith_one hFderiv hF'bound) hFzero U i

/-- The coordinate rows of the smooth composition: the base row is `F ∘ u` and
the `i`th derivative row is `(F' ∘ u) ∂ᵢu`. -/
def smoothCompositionRows
    {n : ℕ} {p : ℝ≥0∞}
    (F F' : ℝ → ℝ) (U : W^{1,p}(ℝ^n))
    (a : DerivIndex n 1) :
    ℝ^n → ℝ :=
  firstOrderRows (compositionBase F U)
    (fun i x ↦
        F' (((U : WkpAmbientOn n 1 p Set.univ)
          (baseIndex n 1) : ℝ^n → ℝ) x) *
          ((U : WkpAmbientOn n 1 p Set.univ)
            (singleDerivIndex n i) : ℝ^n → ℝ) x)
    a

/-- The base row of `smoothCompositionRows` is `compositionBase`. -/
theorem smoothCompositionRows_base
    {n : ℕ} {p : ℝ≥0∞}
    (F F' : ℝ → ℝ) (U : W^{1,p}(ℝ^n)) :
    smoothCompositionRows F F' U (baseIndex n 1) =
      compositionBase F U := by
  simp [smoothCompositionRows]

/-- Every row of `smoothCompositionRows` lies in `Lp` when `F` is
zero-preserving and one-Lipschitz with derivative bounded by one. -/
theorem smoothCompositionRows_memLp
    {n : ℕ} {p : ℝ≥0∞}
    {F F' : ℝ → ℝ}
    (hF' : Continuous F')
    (hFzero : F 0 = 0)
    (hFlip : LipschitzWith 1 F)
    (hF'bound : ∀ x, |F' x| ≤ 1)
    (U : W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    MemLp (smoothCompositionRows F F' U a)
      p (domainMeasure n Set.univ) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hbase :
        MemLp
          (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
          p (domainMeasure n Set.univ) :=
      Lp.memLp _
    simpa [smoothCompositionRows] using hFlip.comp_memLp hFzero hbase
  · subst a
    have hbaseMeas :
        AEStronglyMeasurable
          (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
          (domainMeasure n Set.univ) :=
      (Lp.memLp _).aestronglyMeasurable
    have hcoord :
        MemLp
          (((U : WkpAmbientOn n 1 p Set.univ) (singleDerivIndex n i) :
            DerivLp n p Set.univ) : ℝ^n → ℝ)
          p (domainMeasure n Set.univ) :=
      Lp.memLp _
    apply MemLp.of_le_mul hcoord
    · rw [smoothCompositionRows, firstOrderRows_singleDerivIndex]
      exact
        (hF'.comp_aestronglyMeasurable hbaseMeas).mul
          hcoord.aestronglyMeasurable
    · filter_upwards [] with x
      rw [smoothCompositionRows, firstOrderRows_singleDerivIndex, Real.norm_eq_abs,
        abs_mul, one_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hF'bound _)

/-- Each row of `smoothCompositionRows` is the corresponding weak derivative of
`compositionBase` on the whole space. -/
theorem smoothCompositionRows_weak
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hFderiv : ∀ x, HasDerivAt F (F' x) x)
    (hFzero : F 0 = 0)
    (hF'bound : ∀ x, |F' x| ≤ 1)
    (U : W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    HasWeakDerivativeOn (n := n) Set.univ a.toList
      (compositionBase F U)
      (smoothCompositionRows F F' U a) := by
  have hF' := continuous_scalar_derivative hF hFderiv
  have hFlip := scalar_lipschitzWith_one hFderiv hF'bound
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hloc :=
      memLp_locallyIntegrableOn_domain
        (smoothCompositionRows_memLp
          hF' hFzero hFlip hF'bound U (baseIndex n 1))
        (Fact.out : (1 : ℝ≥0∞) ≤ p)
    have hloc' :
        LocallyIntegrableOn (compositionBase F U) Set.univ
          (volume : Measure (ℝ^n)) := by
      simpa [smoothCompositionRows] using hloc
    simpa [smoothCompositionRows, iteratedPartialDeriv] using
      (show HasWeakDerivativeOn (n := n) Set.univ []
        (compositionBase F U)
        (compositionBase F U) from
        hasWeakDerivativeOn_nil hloc')
  · subst a
    rw [singleDerivIndex_toList]
    apply
      (hasWeakDerivativeOn_congr_ae
        (n := n) (Ω := Set.univ) (α := [i])
        (f := compositionBase F U)
        (g := fun x ↦
          F (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) x))
        (f' := smoothCompositionRows F F' U (singleDerivIndex n i))
        (g' := fun x ↦
          F' (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x)
        (by
          filter_upwards [] with x
          rfl)
        (by
          filter_upwards [] with x
          simp [smoothCompositionRows])).2
    exact hasWeakDerivativeOn_comp_of_hasDerivAt hFderiv hFzero hF'bound U i

/-- Composition by a zero-preserving one-Lipschitz `C¹` scalar map as an
operation on global real-valued `W^{1,p}`. -/
noncomputable def smoothComposition
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hFderiv : ∀ x, HasDerivAt F (F' x) x)
    (hFzero : F 0 = 0)
    (hF'bound : ∀ x, |F' x| ≤ 1)
    (U : W^{1,p}(ℝ^n)) :
    W^{1,p}(ℝ^n) :=
  let hF' : Continuous F' := by exact continuous_scalar_derivative hF hFderiv
  let hFlip : LipschitzWith 1 F := by exact scalar_lipschitzWith_one hFderiv hF'bound
  mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := p) (Ω := Set.univ)
    (compositionBase F U)
    (smoothCompositionRows F F' U)
    (smoothCompositionRows_base F F' U)
    (smoothCompositionRows_memLp hF' hFzero hFlip hF'bound U)
    (smoothCompositionRows_weak hF hFderiv hFzero hF'bound U)

/-- The base coordinate of `smoothComposition` is `F ∘ u` almost
everywhere. -/
theorem smoothComposition_base_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hFderiv : ∀ x, HasDerivAt F (F' x) x)
    (hFzero : F 0 = 0)
    (hF'bound : ∀ x, |F' x| ≤ 1)
    (U : W^{1,p}(ℝ^n)) :
    (((smoothComposition hF hFderiv hFzero
        hF'bound U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          F (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) x) := by
  have hF' := continuous_scalar_derivative hF hFderiv
  have hFlip := scalar_lipschitzWith_one hFderiv hF'bound
  exact
    (mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (compositionBase F U)
      (smoothCompositionRows F F' U)
      (smoothCompositionRows_base F F' U)
      (smoothCompositionRows_memLp hF' hFzero hFlip hF'bound U)
      (smoothCompositionRows_weak hF hFderiv hFzero hF'bound U)
      (baseIndex n 1)).trans <| by
        filter_upwards [] with x
        simp [smoothCompositionRows, compositionBase]

/-- The `i`th weak derivative of `smoothComposition` is
`(F' ∘ u) ∂ᵢu` almost everywhere. -/
theorem smoothComposition_derivative_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hFderiv : ∀ x, HasDerivAt F (F' x) x)
    (hFzero : F 0 = 0)
    (hF'bound : ∀ x, |F' x| ≤ 1)
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((smoothComposition hF hFderiv hFzero
        hF'bound U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          F' (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x := by
  have hF' := continuous_scalar_derivative hF hFderiv
  have hFlip := scalar_lipschitzWith_one hFderiv hF'bound
  simpa [smoothComposition, smoothCompositionRows] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (compositionBase F U)
      (smoothCompositionRows F F' U)
      (smoothCompositionRows_base F F' U)
      (smoothCompositionRows_memLp hF' hFzero hFlip hF'bound U)
      (smoothCompositionRows_weak hF hFderiv hFzero hF'bound U)
      (singleDerivIndex n i)

end SobolevSpace.GraphSpace
