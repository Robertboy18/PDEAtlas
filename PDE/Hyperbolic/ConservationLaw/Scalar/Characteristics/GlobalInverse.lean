/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics.LocalInverse
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# Global characteristic inversion before shock formation

At every nonnegative time strictly below `conservationShockTime`, the
characteristic map has a uniform positive lower bound on its spatial
derivative. The mean value theorem and intermediate value theorem therefore
give a global spatial inverse. Local C¹ inverses agree with this inverse by
injectivity, producing the classical solution on the entire pre-shock
strip with its full initial condition.

The initial profile need not be monotone. Monotonicity of the characteristic position is proved only
before shock formation.

The solution obtained is the implicit formula (61) of Evans, §3.2.5, Example 5, on the whole
strip below the shock time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.5, Example 5, equations (60)-(61).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set PDE.Common
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- Spatial position of the characteristic with initial label `ξ`. -/
def conservationCharPosition (a u₀ : ℝ → ℝ) (t ξ : ℝ) : ℝ :=
  ξ + t * a (u₀ ξ)

/-- The spatial Jacobian is the derivative of the characteristic position. -/
theorem hasDerivAt_conservationCharPosition {a u₀ : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) (t ξ : ℝ) :
    HasDerivAt (conservationCharPosition a u₀ t) (1 + t * deriv a (u₀ ξ) * deriv u₀ ξ) ξ := by
  convert (hasDerivAt_id ξ).add
    (((ha (u₀ ξ)).hasDerivAt.comp ξ (hu₀ ξ).hasDerivAt).const_mul t) using 1
  · rfl
  · simp [mul_assoc]

/-- Before the first degeneracy, the characteristic Jacobian is positive,
since it starts at one and cannot cross zero at an earlier time. -/
theorem conservationCharDenom_pos_of_lt_shockTime (a u₀ : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) (ξ : ℝ) :
    0 < 1 + t * deriv a (u₀ ξ) * deriv u₀ ξ := by
  by_contra hn
  have hc : ContinuousOn (fun r : ℝ ↦ 1 + r * deriv a (u₀ ξ) * deriv u₀ ξ) (Icc 0 t) :=
    (by fun_prop : Continuous _).continuousOn
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc' ht0 hc
    (show 0 ∈ Icc (1 + t * deriv a (u₀ ξ) * deriv u₀ ξ)
      (1 + 0 * deriv a (u₀ ξ) * deriv u₀ ξ) from ⟨le_of_not_gt hn, by simp⟩)
  exact conservationDenom_ne_zero_of_lt_shockTime a u₀ hr.1
    ((WithTop.coe_le_coe.mpr hr.2).trans_lt ht) ξ hz

/-- Strictly before shock formation the spatial Jacobian has a uniform
positive lower bound, even if the initial derivative is unbounded above. -/
theorem exists_pos_le_conservationCharDenom (a u₀ : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ, δ ≤ 1 + t * deriv a (u₀ ξ) * deriv u₀ ξ := by
  obtain ⟨τ, htτ, hτ⟩ := WithTop.lt_iff_exists_coe_btwn.mp ht
  have htτ' : t < τ := WithTop.coe_lt_coe.mp htτ
  have hτ0 : 0 < τ := ht0.trans_lt htτ'
  refine ⟨(τ - t) / τ, div_pos (sub_pos.mpr htτ') hτ0, fun ξ ↦ ?_⟩
  have hd := conservationCharDenom_pos_of_lt_shockTime a u₀ hτ0.le hτ ξ
  apply (div_le_iff₀ hτ0).mpr
  nlinarith [mul_nonneg ht0 hd.le]

/-- The characteristic position is strictly increasing at each pre-shock time. -/
theorem strictMono_conservationCharPosition {a u₀ : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) :
    StrictMono (conservationCharPosition a u₀ t) := by
  refine strictMono_of_deriv_pos fun ξ ↦ ?_
  rw [(hasDerivAt_conservationCharPosition ha hu₀ t ξ).deriv]
  exact conservationCharDenom_pos_of_lt_shockTime a u₀ ht0 ht ξ

/-- At each pre-shock time every spatial point has a characteristic footpoint.
Surjectivity follows from the uniform lower Jacobian bound and the intermediate value theorem. -/
theorem surjective_conservationCharPosition {a u₀ : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) :
    Function.Surjective (conservationCharPosition a u₀ t) := by
  let f := conservationCharPosition a u₀ t
  have hf : Differentiable ℝ f := fun ξ ↦
    (hasDerivAt_conservationCharPosition ha hu₀ t ξ).differentiableAt
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_le_conservationCharDenom a u₀ ht0 ht
  have hder : ∀ ξ, δ ≤ deriv f ξ := by
    intro ξ
    rw [(hasDerivAt_conservationCharPosition ha hu₀ t ξ).deriv]
    exact hbound ξ
  intro x
  let R := (|x - f 0| + 1) / δ
  have hR : 0 ≤ R := div_nonneg (by positivity) hδ.le
  have hmul : δ * R = |x - f 0| + 1 := by
    dsimp [R]
    cas using hδ.ne'
  have hright := mul_sub_le_image_sub_of_le_deriv hf hder hR
  have hleft := mul_sub_le_image_sub_of_le_deriv hf hder (neg_nonpos.mpr hR)
  have hxl : f (-R) ≤ x := by
    simp only [sub_zero, zero_sub, neg_neg] at hright hleft
    linarith [neg_abs_le (x - f 0)]
  have hxr : x ≤ f R := by
    simp only [sub_zero] at hright
    linarith [le_abs_self (x - f 0)]
  exact intermediate_value_univ (-R) R hf.continuous ⟨hxl, hxr⟩

/-- The global characteristic footpoint, used on the pre-shock strip.
Outside that strip `invFun` supplies an arbitrary total extension. -/
def conservationFootpoint (a u₀ : ℝ → ℝ) (p : ℝ^2) : ℝ :=
  Function.invFun (conservationCharPosition a u₀ (p 0)) (p 1)

/-- The global characteristic construction of the solution. -/
def conservationClassicalSolution (a u₀ : ℝ → ℝ) (p : ℝ^2) : ℝ :=
  u₀ (conservationFootpoint a u₀ p)

/-- The global inverse satisfies the characteristic equation. -/
theorem conservationFootpoint_relation {a u₀ : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) {p : ℝ^2}
    (hp0 : 0 ≤ p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    p 1 = conservationFootpoint a u₀ p + p 0 * a (u₀ (conservationFootpoint a u₀ p)) :=
  (Function.rightInverse_invFun (surjective_conservationCharPosition ha hu₀ hp0 hp) (p 1)).symm

/-- Inverting a characteristic recovers its initial label. -/
theorem conservationFootpoint_characteristic {a u₀ : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) (ξ : ℝ) :
    conservationFootpoint a u₀ !₂[t, conservationCharPosition a u₀ t ξ] = ξ :=
  Function.leftInverse_invFun (strictMono_conservationCharPosition ha hu₀ ht0 ht).injective ξ

/-- The constructed solution carries each initial value along its characteristic. -/
theorem conservationClassicalSolution_characteristic {a u₀ : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) (ξ : ℝ) :
    conservationClassicalSolution a u₀ !₂[t, conservationCharPosition a u₀ t ξ] = u₀ ξ := by
  simp only [conservationClassicalSolution, conservationFootpoint_characteristic ha hu₀ ht0 ht]

/-- The complete initial line is attained, independently of the lifespan. -/
theorem conservationClassicalSolution_initial (a u₀ : ℝ → ℝ) (x : ℝ) :
    conservationClassicalSolution a u₀ !₂[0, x] = u₀ x := by
  have hf : conservationCharPosition a u₀ 0 = id := by
    funext ξ
    simp [conservationCharPosition]
  change u₀ (Function.invFun (conservationCharPosition a u₀ 0) x) = u₀ x
  rw [hf]
  exact congrArg u₀ (Function.leftInverse_invFun Function.injective_id x)

/-- Near each nonnegative pre-shock point the global footpoint agrees, on
nonnegative times, with a C¹ local inverse. This includes the initial
line without imposing invertibility of the characteristic map at negative times. -/
theorem exists_local_extension_conservationFootpoint {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {p : ℝ^2}
    (hp0 : 0 ≤ p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    ∃ (U : Set ℝ^2) (ξ : ℝ^2 → ℝ), IsOpen U ∧ p ∈ U ∧ (∀ q ∈ U, ContDiffAt ℝ 1 ξ q) ∧
      (∀ q ∈ U, 0 ≤ q 0 → conservationFootpoint a u₀ q = ξ q) := by
  have had := ha.differentiable_one
  have hud := hu₀.differentiable_one
  let p₀ := !₂[p 0, conservationFootpoint a u₀ p]
  have hmap : conservationCharMap a u₀ p₀ = p := by
    ext i
    fin_cases i
    · simp [conservationCharMap, p₀]
    · simpa [conservationCharMap, p₀] using (conservationFootpoint_relation had hud hp0 hp).symm
  have hd : conservationCharDenom a u₀ p₀ ≠ 0 :=
    (conservationCharDenom_pos_of_lt_shockTime a u₀ hp0 hp (conservationFootpoint a u₀ p)).ne'
  obtain ⟨V, hV, hpV, ξ, _, hrel, hC⟩ :=
    exists_local_contDiff_footpointMap_of_denom_ne_zero a u₀ p₀ ha hu₀ hd
  rw [hmap] at hpV
  obtain ⟨τ, hpτ, hτ⟩ := WithTop.lt_iff_exists_coe_btwn.mp hp
  have hO : IsOpen {q : ℝ^2 | q 0 < τ} :=
    isOpen_lt (by fun_prop) continuous_const
  refine ⟨V ∩ {q : ℝ^2 | q 0 < τ}, ξ, hV.inter hO,
    ⟨hpV, WithTop.coe_lt_coe.mp hpτ⟩, fun q hq ↦ hC q hq.1, ?_⟩
  intro q hq hq0
  have hqt : (q 0 : WithTop ℝ) < conservationShockTime a u₀ :=
    (WithTop.coe_lt_coe.mpr hq.2).trans hτ
  apply (strictMono_conservationCharPosition had hud hq0 hqt).injective
  exact (conservationFootpoint_relation had hud hq0 hqt).symm.trans (hrel q hq.1)

/-- C¹ regularity up to the initial line, from the nonnegative-time side. -/
theorem contDiffWithinAt_conservationFootpoint {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {p : ℝ^2}
    (hp0 : 0 ≤ p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    ContDiffWithinAt ℝ 1 (conservationFootpoint a u₀) {q : ℝ^2 | 0 ≤ q 0} p := by
  obtain ⟨U, ξ, hU, hpU, hC, heq⟩ := exists_local_extension_conservationFootpoint ha hu₀ hp0 hp
  apply (hC p hpU).contDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hpU), self_mem_nhdsWithin]
      with q hq hq0 using heq q hq hq0
  · exact heq p hpU hp0

/-- The global inverse is C¹ in the open pre-shock strip. -/
theorem contDiffAt_conservationFootpoint {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {p : ℝ^2}
    (hp0 : 0 < p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    ContDiffAt ℝ 1 (conservationFootpoint a u₀) p := by
  apply (contDiffWithinAt_conservationFootpoint ha hu₀ hp0.le hp).contDiffAt
  have hO : IsOpen {q : ℝ^2 | 0 < q 0} :=
    isOpen_lt continuous_const (by fun_prop)
  exact mem_of_superset (hO.mem_nhds hp0) fun q (hq : 0 < q 0) ↦ hq.le

/-- The classical solution is C¹ up to the initial line from the right. -/
theorem contDiffWithinAt_conservationClassicalSolution {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {p : ℝ^2}
    (hp0 : 0 ≤ p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    ContDiffWithinAt ℝ 1 (conservationClassicalSolution a u₀) {q : ℝ^2 | 0 ≤ q 0} p :=
  hu₀.contDiffAt.comp_contDiffWithinAt p (contDiffWithinAt_conservationFootpoint ha hu₀ hp0 hp)

/-- C¹ regularity of the constructed solution at every positive pre-shock time. -/
theorem contDiffAt_conservationClassicalSolution {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {p : ℝ^2}
    (hp0 : 0 < p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    ContDiffAt ℝ 1 (conservationClassicalSolution a u₀) p :=
  hu₀.contDiffAt.comp p (contDiffAt_conservationFootpoint ha hu₀ hp0 hp)

private theorem exists_open_footRelation {a u₀ : ℝ → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) {p : ℝ^2}
    (hp0 : 0 < p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    ∃ U : Set ℝ^2, IsOpen U ∧ p ∈ U ∧
      ConservationFootRelationOn a u₀ (conservationFootpoint a u₀) U := by
  obtain ⟨τ, hpτ, hτ⟩ := WithTop.lt_iff_exists_coe_btwn.mp hp
  refine ⟨{q : ℝ^2 | q 0 ∈ Ioo 0 τ}, isOpen_Ioo.preimage (by fun_prop),
    ⟨hp0, WithTop.coe_lt_coe.mp hpτ⟩, ?_⟩
  exact fun q hq ↦ conservationFootpoint_relation ha hu₀ hq.1.le
    ((WithTop.coe_lt_coe.mpr hq.2).trans hτ)

/-- The global construction solves `u_t + a(u) u_x = 0` throughout
the open pre-shock strip. -/
theorem conservationClassicalSolution_satisfies_pde {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {p : ℝ^2}
    (hp0 : 0 < p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    (∂[(0 : Fin 2)] (conservationClassicalSolution a u₀)) p +
      a (conservationClassicalSolution a u₀ p) *
        (∂[(1 : Fin 2)] (conservationClassicalSolution a u₀)) p = 0 := by
  obtain ⟨U, hU, hpU, hrel⟩ :=
    exists_open_footRelation ha.differentiable_one hu₀.differentiable_one hp0 hp
  exact hrel.satisfies_pde_at hU ha.differentiable_one hu₀.differentiable_one hpU
    (contDiffAt_conservationFootpoint ha hu₀ hp0 hp).differentiableAt_one

/-- Spatial derivative of the solution, with the characteristic
Jacobian in the denominator. -/
theorem partialDeriv_space_conservationClassicalSolution {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {p : ℝ^2}
    (hp0 : 0 < p 0) (hp : (p 0 : WithTop ℝ) < conservationShockTime a u₀) :
    (∂[(1 : Fin 2)] (conservationClassicalSolution a u₀)) p =
      deriv u₀ (conservationFootpoint a u₀ p) / (1 + p 0 * deriv a
      (u₀ (conservationFootpoint a u₀ p)) * deriv u₀ (conservationFootpoint a u₀ p)) := by
  obtain ⟨U, hU, hpU, hrel⟩ :=
    exists_open_footRelation ha.differentiable_one hu₀.differentiable_one hp0 hp
  have hξ := (contDiffAt_conservationFootpoint ha hu₀ hp0 hp).differentiableAt_one
  unfold conservationClassicalSolution
  rw [partialDeriv_comp_real 1 hu₀.differentiable_one.differentiableAt hξ,
    hrel.partialDeriv_space hU ha.differentiable_one hu₀.differentiable_one hpU hξ]
  simp [conservationDenom, div_eq_mul_inv, mul_comm]

/-- The slope formula along a characteristic is an identity for the derivative
of the constructed classical solution. -/
theorem partialDeriv_space_conservationClassicalSolution_characteristic
    {a u₀ : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {t : ℝ}
    (ht0 : 0 < t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) (ξ : ℝ) :
    (∂[(1 : Fin 2)] (conservationClassicalSolution a u₀)) !₂[t, conservationCharPosition a u₀ t ξ] =
      deriv u₀ ξ / (1 + t * deriv a (u₀ ξ) * deriv u₀ ξ) := by
  rw [partialDeriv_space_conservationClassicalSolution ha hu₀ ht0 ht,
    conservationFootpoint_characteristic ha.differentiable_one hu₀.differentiable_one ht0.le ht]
  rfl

end PDE.Hyperbolic.ConservationLaw.Scalar
