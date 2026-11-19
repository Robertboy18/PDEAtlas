/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import PDE.Common.Euclidean
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Scalar noncharacteristic first-order equations

We prove the scalar implicit-function step behind a noncharacteristic condition: local
solvability for the distinguished derivative variable in a flat first-order model. For a flat
boundary this is the condition `F_{p_n} ≠ 0` of Lemma 1 in Evans, §3.2.3, equation (35); when
`F` is affine in `p` it is, at one point, the condition (6) of §4.6.1 with `k = 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.3, Lemma 1, equation (35); §4.6.1, equations (5)-(6)
  and (8).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace NonlinearFirstOrder

/-- For a scalar equation `F(t,x,z,p)=0`, noncharacteristic in the distinguished derivative
variable `p` means that the `p`-slice is differentiable and has nonzero derivative.

For `F` affine in `p` this is, at one point, the noncharacteristic condition (6) of Evans,
§4.6.1, with `k = 1`. -/
def IsNoncharacteristicInP {n : ℕ} (F : ℝ → ℝ^n → ℝ → ℝ → ℝ)
    (t0 : ℝ) (x0 : ℝ^n) (z0 p0 : ℝ) : Prop :=
  DifferentiableAt ℝ (fun p ↦ F t0 x0 z0 p) p0 ∧
    deriv (fun p ↦ F t0 x0 z0 p) p0 ≠ 0

/-- The model equation `p = 0` is noncharacteristic in the derivative variable `p`. -/
theorem isNoncharacteristicInP_identity {n : ℕ} (t0 : ℝ) (x0 : ℝ^n) (z0 p0 : ℝ) :
    IsNoncharacteristicInP (fun _ _ _ p ↦ p) t0 x0 z0 p0 := by
  constructor
  · fun_prop
  · simp

/-- Any affine equation with nonzero `p` coefficient is noncharacteristic in `p`. -/
theorem isNoncharacteristicInP_affine {n : ℕ} (a b : ℝ) (hb : b ≠ 0) (t0 : ℝ) (x0 : ℝ^n)
    (z0 p0 : ℝ) :
    IsNoncharacteristicInP (fun _ _ _ p ↦ b * p + a) t0 x0 z0 p0 := by
  constructor
  · fun_prop
  · simp [hb]

/-- The scalar noncharacteristic condition makes the derivative in the distinguished
variable invertible. -/
theorem IsNoncharacteristicInP.isInvertible {n : ℕ} {F : ℝ → ℝ^n → ℝ → ℝ → ℝ} {g : ℝ^n → ℝ}
    {x0 : ℝ^n} {p0 : ℝ} (hn : IsNoncharacteristicInP F 0 x0 (g x0) p0)
    (h : DifferentiableAt ℝ (fun xp : ℝ^n × ℝ ↦ F 0 xp.1 (g xp.1) xp.2) (x0, p0)) :
    (fderiv ℝ (fun xp : ℝ^n × ℝ ↦ F 0 xp.1 (g xp.1) xp.2) (x0, p0) ∘L
      ContinuousLinearMap.inr ℝ (ℝ^n) ℝ).IsInvertible := by
  let c := deriv (fun p ↦ F 0 x0 (g x0) p) p0
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hn.2), ?_⟩
  apply ContinuousLinearMap.ext_ring
  have hslice := h.hasFDerivAt.comp_hasDerivAt p0
    ((hasDerivAt_const p0 x0).prodMk (hasDerivAt_id p0))
  simpa [c, Function.comp_def] using hslice.deriv

/-- On a flat initial surface, a nonzero distinguished derivative gives a local graph
of the equation through the prescribed base point. The graph has the same positive
regularity order as the restricted equation, including finite, smooth, and analytic orders. -/
theorem IsNoncharacteristicInP.exists_local_implicitFunction {n : ℕ} {F : ℝ → ℝ^n → ℝ → ℝ → ℝ}
    {g : ℝ^n → ℝ} {x0 : ℝ^n} {p0 : ℝ} (hn : IsNoncharacteristicInP F 0 x0 (g x0) p0)
    {k : WithTop ℕ∞} (hk : k ≠ 0)
    (h : ContDiffAt ℝ k (fun xp : ℝ^n × ℝ ↦ F 0 xp.1 (g xp.1) xp.2) (x0, p0))
    (hbase : F 0 x0 (g x0) p0 = 0) :
    ∃ U : Set (ℝ^n), IsOpen U ∧ x0 ∈ U ∧ ∃ p : ℝ^n → ℝ,
      p x0 = p0 ∧ ContDiffAt ℝ k p x0 ∧ ∀ x ∈ U, F 0 x (g x) (p x) = 0 := by
  have hi := hn.isInvertible (h.differentiableAt hk)
  have heq := h.eventually_apply_implicitFunction hk hi
  obtain ⟨U, hU, hopen, hx0⟩ := mem_nhds_iff.mp heq
  refine ⟨U, hopen, hx0, h.implicitFunction hk hi,
    h.implicitFunction_apply_self hk hi, h.contDiffAt_implicitFunction hk hi, ?_⟩
  exact fun x hx ↦ (hU hx).trans hbase

end NonlinearFirstOrder
