/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Topology.Order.OrderClosed

/-!
# Gluing `C²` functions along a level set, and reflections that match to second order

A function `v` is given on one side of a hypersurface, and we want to continue it to the other
side so that the result is `C²`, using only values of `v`. Two tools do this, in any real normed
spaces. The gluing lemma `contDiff_two_ite`: if `A` and `B` are `C²` and agree with their first
and second derivatives where a continuous `π` equals `c`, then the function that is `A` on
`π < c` and `B` on `π ≥ c` is `C²`. And the reflection sum `∑ⱼ cⱼ v(y + tⱼ q(y))` for a map `q`
that vanishes on the hypersurface (for a sphere, `q(y) = y/|y| - y`): under the moment
conditions `∑ cⱼ = 1`, `∑ cⱼ tⱼ = 0` and `∑ cⱼ tⱼ² = 0` it agrees with `v` to second order there.
The extension of a function across the two spheres of an annulus
(`PDE.Analysis.annulusExtension`) uses both, with `c = (6, -8, 3)` and `t = (2, 3, 4)`. Only
order two is written; `k + 1` nodes with `k + 1` moment conditions would give a `C^k`
continuation in the same way.

## Main results

* `hasFDerivAt_ite_of_eq`: the glued function of two differentiable functions that agree with
  their derivatives on the level set has the glued derivative at every point.
* `contDiff_two_ite`: the glued function of two `C²` functions that agree to second order on the
  level set is `C²`.
* `reflectionSum_eq`, `fderiv_reflectionSum_eq`, `fderiv_fderiv_reflectionSum_eq`: at a zero of
  `q`, a reflection sum with one, two or three moment conditions has the value, the first
  derivative and the second derivative of `v`, for `C²` functions `v` and `q`.

## How it works

Off the level set the glued function is `A` or `B` near the point. On the level set it is `B` on
the closed side `c ≤ π` and `A` on the closed side `π ≤ c`, because `B = A` where `π = c`; the
two derivatives agree there, and Mathlib's `HasFDerivWithinAt.union` joins the two sides. The
same lemma applied to the derivatives gives `C²`. For the reflection sum, the chain rule gives
the derivative `(∑ cⱼ) Dv + (∑ cⱼ tⱼ) Dv ∘ Dq` at a zero of `q`. The derivative is again a
reflection sum of `Dv`, plus a reflection sum with the weights `cⱼ tⱼ` composed with `Dq`; the
second term vanishes to first order at a zero of `q` because `∑ cⱼ tⱼ = ∑ cⱼ tⱼ² = 0`. So no
derivative of `q` has to be computed.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ## Gluing along a level set -/

/-- **Gluing two differentiable functions along the level set `π = c`.** If `B = A` and
`B' = A'` where `π = c`, then `q ↦ if c ≤ π q then B q else A q` has the derivative
`if c ≤ π p then B' p else A' p` at every `p`. On the level set the function is `B` on the
closed side `c ≤ π` and `A` on the closed side `π ≤ c`, with the same derivative on both. -/
theorem hasFDerivAt_ite_of_eq {A B : E → F} {A' B' : E → E →L[ℝ] F} {π : E → ℝ}
    (hπ : Continuous π) (c : ℝ) (hA : ∀ p, HasFDerivAt A (A' p) p)
    (hB : ∀ p, HasFDerivAt B (B' p) p) (h0 : ∀ p, π p = c → B p = A p)
    (h1 : ∀ p, π p = c → B' p = A' p) (p : E) :
    HasFDerivAt (fun q ↦ if c ≤ π q then B q else A q) (if c ≤ π p then B' p else A' p) p := by
  rcases lt_trichotomy (π p) c with h | h | h
  · -- below the level set the glued function is `A` near `p`
    rw [ite_eq_right h.not_ge]
    refine (hA p).congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.eventually_lt continuousAt_const h] with q hq
    exact ite_eq_right hq.not_ge
  · have hS : HasFDerivWithinAt (fun q ↦ if c ≤ π q then B q else A q) (B' p)
        {q | c ≤ π q} p :=
      (hB p).hasFDerivWithinAt.congr' (fun q (hq : c ≤ π q) ↦ ite_eq_left hq) h.ge
    have hT : HasFDerivWithinAt (fun q ↦ if c ≤ π q then B q else A q) (B' p)
        {q | π q ≤ c} p := by
      rw [h1 p h]
      refine (hA p).hasFDerivWithinAt.congr' (fun q (hq : π q ≤ c) ↦ ?_) h.le
      show (if c ≤ π q then B q else A q) = A q
      by_cases hc : c ≤ π q
      · exact (ite_eq_left hc).trans (h0 q (le_antisymm hq hc))
      · exact ite_eq_right hc
    have hU : {q | c ≤ π q} ∪ {q | π q ≤ c} = Set.univ :=
      Set.eq_univ_of_forall fun q ↦ le_total c (π q)
    rw [ite_eq_left h.ge, ← hasFDerivWithinAt_univ, ← hU]
    exact hS.union hT
  · -- above the level set the glued function is `B` near `p`
    rw [ite_eq_left h.le]
    refine (hB p).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hπ.continuousAt h] with q hq
    exact ite_eq_left hq.le

/-- **Gluing two `C²` functions along a level set.** If `A` and `B` are `C²` and agree with their
first and second derivatives where `π = c`, then `q ↦ if c ≤ π q then B q else A q` is `C²`. This
is `hasFDerivAt_ite_of_eq` applied to `A`, `B` and to their derivatives; the glued second
derivative is continuous because the two second derivatives agree on the level set. -/
theorem contDiff_two_ite {A B : E → F} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) {π : E → ℝ}
    (hπ : Continuous π) (c : ℝ) (h0 : ∀ p, π p = c → B p = A p)
    (h1 : ∀ p, π p = c → fderiv ℝ B p = fderiv ℝ A p)
    (h2 : ∀ p, π p = c → fderiv ℝ (fderiv ℝ B) p = fderiv ℝ (fderiv ℝ A) p) :
    ContDiff ℝ 2 (fun q ↦ if c ≤ π q then B q else A q) := by
  have hA1 : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (by norm_num)
  have hB1 : ContDiff ℝ 1 (fderiv ℝ B) := hB.fderiv_right (by norm_num)
  have hd0 := hasFDerivAt_ite_of_eq hπ c
    (fun p ↦ (hA.differentiable (by norm_num) p).hasFDerivAt)
    (fun p ↦ (hB.differentiable (by norm_num) p).hasFDerivAt) h0 h1
  have hd1 := hasFDerivAt_ite_of_eq hπ c
    (fun p ↦ (hA1.differentiable one_ne_zero p).hasFDerivAt)
    (fun p ↦ (hB1.differentiable one_ne_zero p).hasFDerivAt) h1 h2
  have hc2 : Continuous fun q ↦
      if c ≤ π q then fderiv ℝ (fderiv ℝ B) q else fderiv ℝ (fderiv ℝ A) q :=
    Continuous.if_le (hB1.continuous_fderiv one_ne_zero) (hA1.continuous_fderiv one_ne_zero)
      continuous_const hπ fun p hp ↦ h2 p hp.symm
  have e0 : fderiv ℝ (fun q ↦ if c ≤ π q then B q else A q) =
      fun q ↦ if c ≤ π q then fderiv ℝ B q else fderiv ℝ A q := funext fun p ↦ (hd0 p).fderiv
  have e1 : fderiv ℝ (fun q ↦ if c ≤ π q then fderiv ℝ B q else fderiv ℝ A q) =
      fun q ↦ if c ≤ π q then fderiv ℝ (fderiv ℝ B) q else fderiv ℝ (fderiv ℝ A) q :=
    funext fun p ↦ (hd1 p).fderiv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun p ↦ (hd0 p).differentiableAt, by simp, ?_⟩
  rw [e0, contDiff_one_iff_fderiv, e1]
  exact ⟨fun p ↦ (hd1 p).differentiableAt, hc2⟩

/-! ## Reflection sums -/

section ReflectionSum

variable {ι : Type*} (s : Finset ι) (c t : ι → ℝ) (q : E → E)

/-- The sum `∑ⱼ cⱼ v(y + tⱼ q(y))`. When `q` vanishes on a hypersurface and the coefficients
satisfy the moment conditions, it continues `v` across the hypersurface. -/
def reflectionSum (v : E → F) (y : E) : F :=
  ∑ j ∈ s, c j • v (y + t j • q y)

variable {s c t q} {v : E → F} {p : E}

/-- The derivative of a reflection sum, by the chain rule:
`∑ⱼ cⱼ Dv(y + tⱼ q(y)) ∘ (1 + tⱼ Dq(y))`. -/
theorem hasFDerivAt_reflectionSum (hv : Differentiable ℝ v) {y : E}
    (hq : DifferentiableAt ℝ q y) :
    HasFDerivAt (reflectionSum s c t q v)
      (∑ j ∈ s, c j • (fderiv ℝ v (y + t j • q y)).comp
        (ContinuousLinearMap.id ℝ E + t j • fderiv ℝ q y)) y := by
  have h (j : ι) : HasFDerivAt (fun y ↦ c j • v (y + t j • q y))
      (c j • (fderiv ℝ v (y + t j • q y)).comp
        (ContinuousLinearMap.id ℝ E + t j • fderiv ℝ q y)) y :=
    ((hv _).hasFDerivAt.comp y
      ((hasFDerivAt_id y).add (hq.hasFDerivAt.const_smul (t j)))).const_smul (c j)
  have hsum := HasFDerivAt.sum fun j (_ : j ∈ s) ↦ h j
  refine hsum.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
  simp [reflectionSum, Finset.sum_apply]

/-- A reflection sum with `∑ cⱼ = 1` agrees with `v` at the zeros of `q`. -/
theorem reflectionSum_eq (hq0 : q p = 0) (h0 : ∑ j ∈ s, c j = 1) :
    reflectionSum s c t q v p = v p := by
  simp [reflectionSum, hq0, ← Finset.sum_smul, h0]

/-- A reflection sum with `∑ cⱼ = a` and `∑ cⱼ tⱼ = b` has the derivative
`a Dv + b Dv ∘ Dq` at the zeros of `q`. -/
theorem fderiv_reflectionSum_of_moments (hv : Differentiable ℝ v) (hq : DifferentiableAt ℝ q p)
    (hq0 : q p = 0) {a b : ℝ} (h0 : ∑ j ∈ s, c j = a) (h1 : ∑ j ∈ s, c j * t j = b) :
    fderiv ℝ (reflectionSum s c t q v) p =
      a • fderiv ℝ v p + b • (fderiv ℝ v p).comp (fderiv ℝ q p) := by
  rw [(hasFDerivAt_reflectionSum hv hq).fderiv]
  ext h
  simp only [hq0, smul_zero, add_zero, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, add_apply, ContinuousLinearMap.coe_id', id_eq,
    map_add, map_smul, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul, h0, h1]

/-- A reflection sum with `∑ cⱼ = 1` and `∑ cⱼ tⱼ = 0` has the derivative of `v` at the zeros
of `q`. -/
theorem fderiv_reflectionSum_eq (hv : Differentiable ℝ v) (hq : DifferentiableAt ℝ q p)
    (hq0 : q p = 0) (h0 : ∑ j ∈ s, c j = 1) (h1 : ∑ j ∈ s, c j * t j = 0) :
    fderiv ℝ (reflectionSum s c t q v) p = fderiv ℝ v p := by
  rw [fderiv_reflectionSum_of_moments hv hq hq0 h0 h1, one_smul, zero_smul, add_zero]

/-- **A reflection sum with three moment conditions matches to second order.** If
`∑ cⱼ = 1`, `∑ cⱼ tⱼ = 0` and `∑ cⱼ tⱼ² = 0`, then at the zeros of `q` the second derivative of
`∑ⱼ cⱼ v(y + tⱼ q(y))` is the second derivative of `v`. -/
theorem fderiv_fderiv_reflectionSum_eq (hv : ContDiff ℝ 2 v) (hq : ContDiff ℝ 2 q)
    (hq0 : q p = 0) (h0 : ∑ j ∈ s, c j = 1) (h1 : ∑ j ∈ s, c j * t j = 0)
    (h2 : ∑ j ∈ s, c j * t j ^ 2 = 0) :
    fderiv ℝ (fderiv ℝ (reflectionSum s c t q v)) p = fderiv ℝ (fderiv ℝ v) p := by
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hqd : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hv1 : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hq1 : Differentiable ℝ (fderiv ℝ q) :=
    (hq.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  -- the first derivative, as a reflection sum of `Dv` plus a term with the weights `cⱼ tⱼ`
  have hfun : fderiv ℝ (reflectionSum s c t q v) = fun y ↦
      reflectionSum s c t q (fderiv ℝ v) y +
        (reflectionSum s (fun j ↦ c j * t j) t q (fderiv ℝ v) y).comp (fderiv ℝ q y) := by
    funext y
    rw [(hasFDerivAt_reflectionSum hvd (hqd y)).fderiv]
    ext h
    simp only [reflectionSum, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, add_apply, ContinuousLinearMap.coe_id', id_eq,
      map_add, map_smul, smul_add, smul_smul, Finset.sum_add_distrib]
  -- the derivative of the first term is `D²v`, the second term vanishes to first order
  have hd1 : HasFDerivAt (reflectionSum s c t q (fderiv ℝ v)) (fderiv ℝ (fderiv ℝ v) p) p := by
    have h := (hasFDerivAt_reflectionSum (s := s) (c := c) (t := t) hv1 (hqd p)).differentiableAt
    have e := fderiv_reflectionSum_eq (s := s) (c := c) (t := t) hv1 (hqd p) hq0 h0 h1
    rw [← e]
    exact h.hasFDerivAt
  have hS0 : reflectionSum s (fun j ↦ c j * t j) t q (fderiv ℝ v) p = 0 := by
    simp [reflectionSum, hq0, ← Finset.sum_smul, h1]
  have hS1 : HasFDerivAt (reflectionSum s (fun j ↦ c j * t j) t q (fderiv ℝ v))
      (0 : E →L[ℝ] E →L[ℝ] F) p := by
    have h := (hasFDerivAt_reflectionSum (s := s) (c := fun j ↦ c j * t j) (t := t) hv1
      (hqd p)).differentiableAt
    have e := fderiv_reflectionSum_of_moments (s := s) (c := fun j ↦ c j * t j) (t := t) hv1
      (hqd p) hq0 h1 (b := 0) (by simpa only [mul_assoc, ← sq] using h2)
    rw [zero_smul, zero_smul, add_zero] at e
    rw [← e]
    exact h.hasFDerivAt
  have hd2 := hS1.clm_comp (hq1 p).hasFDerivAt
  rw [hS0] at hd2
  have hsum : HasFDerivAt (fun y ↦ reflectionSum s c t q (fderiv ℝ v) y +
      (reflectionSum s (fun j ↦ c j * t j) t q (fderiv ℝ v) y).comp (fderiv ℝ q y)) _ p :=
    hd1.add hd2
  rw [hfun, hsum.fderiv]
  simp

end ReflectionSum

end PDE.Analysis
