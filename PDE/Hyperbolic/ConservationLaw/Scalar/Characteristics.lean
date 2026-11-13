/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import PDE.FDeriv.Calculus
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Characteristics for one-dimensional scalar conservation laws

We formalize the 1D scalar conservation law in quasilinear form

`u_t + a(u) u_x = 0`,

including:
- the characteristic *footpoint relation* `x = ξ + t * a(u₀(ξ))`;
- the corresponding implicit characteristic candidate `u(t,x)=u₀(ξ(t,x))`;
- a formal *shock time* as the infimum of nonnegative times at which the characteristic
  Jacobian vanishes, with value `⊤` when there are none;
- its value: `-1 / m` when the product `a'(u₀) u₀'` has infimum `m < 0`
  (`conservationShockTime_eq_of_isGLB`), since `1 + t k` vanishes at `t = -1 / k` for each
  negative value `k` of the product, and `⊤` when the product is nonnegative
  (`conservationShockTime_eq_top_of_nonneg`).

Differentiating the footpoint relation on an open set gives the equation for
`u(t,x)=u₀(ξ(t,x))`. The spatial derivative also forces the Jacobian denominator
to be nonzero wherever the footpoint is differentiable. The construction in
`Characteristics.LocalInverse` supplies these local footpoints before the
shock time and proves the initial condition for the resulting solution.

With `a = F'`, the footpoint relation is the projected characteristic (60) of Evans, §3.2.5,
Example 5, and the candidate is his implicit formula (61), `u = u₀(x - t a(u))`. Evans notes
that (61) gives a solution while `1 + t u₀'(ξ) a'(u₀(ξ)) ≠ 0`, the nonvanishing of our
characteristic Jacobian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.5, Example 5, equations (56)-(61).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

noncomputable section

open PDE.Common
open scoped Topology

/-- The footpoint relation on a set `U` (useful for local solutions). -/
def ConservationFootRelationOn
    (a u₀ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) (U : Set ℝ^2) : Prop :=
  ∀ x ∈ U, x 1 = ξ x + x 0 * a (u₀ (ξ x))

/-- Characteristic candidate built from a supplied footpoint map `ξ`. -/
def conservationSolutionFromFoot (u₀ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  fun x ↦ u₀ (ξ x)

/-- The Jacobian denominator `1 + t * a'(u₀(ξ)) * u₀'(ξ)` appearing in implicit differentiation. -/
def conservationDenom (a u₀ : ℝ → ℝ) (ξ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  1 + x 0 * deriv a (u₀ (ξ x)) * deriv u₀ (ξ x)

private theorem partialDeriv_mul_conservationDenom {a u₀ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) (i : Fin 2) (x : ℝ^2)
    (hξ : DifferentiableAt ℝ ξ x)
    (hrel : (fun y : ℝ^2 ↦ y 1) =ᶠ[𝓝 x] fun y ↦ ξ y + y 0 * a (u₀ (ξ y))) :
    (∂[i] ξ) x * conservationDenom a u₀ ξ x =
      (∂[i] (fun y : ℝ^2 ↦ y 1)) x - (∂[i] (fun y : ℝ^2 ↦ y 0)) x * a (u₀ (ξ x)) := by
  have ht : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x := by
    fun_prop
  have hu : DifferentiableAt ℝ (fun y ↦ u₀ (ξ y)) x := hu₀.differentiableAt.comp x hξ
  have hv : DifferentiableAt ℝ (fun y ↦ a (u₀ (ξ y))) x := ha.differentiableAt.comp x hu
  have hidentity := partialDeriv_congr_nhds i hrel
  rw [partialDeriv_add (i := i) (f := ξ) (g := fun y ↦ y 0 * a (u₀ (ξ y))) hξ (ht.mul hv),
    partialDeriv_mul (i := i) (f := fun y : ℝ^2 ↦ y 0) (g := fun y ↦ a (u₀ (ξ y))) ht hv,
    partialDeriv_comp_real i ha.differentiableAt hu,
    partialDeriv_comp_real i hu₀.differentiableAt hξ] at hidentity
  rw [hidentity]
  unfold conservationDenom
  cas

/-- A differentiable local footpoint map has nonzero characteristic Jacobian. -/
theorem ConservationFootRelationOn.denom_ne_zero {a u₀ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {U : Set ℝ^2}
    (hrel : ConservationFootRelationOn a u₀ ξ U) (hU : IsOpen U) (ha : Differentiable ℝ a)
    (hu₀ : Differentiable ℝ u₀) {x : ℝ^2} (hx : x ∈ U) (hξ : DifferentiableAt ℝ ξ x) :
    conservationDenom a u₀ ξ x ≠ 0 := by
  have hnear := (show Set.EqOn (fun y : ℝ^2 ↦ y 1)
    (fun y ↦ ξ y + y 0 * a (u₀ (ξ y))) U from hrel).eventuallyEq_of_mem (hU.mem_nhds hx)
  have hs : (∂[(1 : Fin 2)] ξ) x * conservationDenom a u₀ ξ x = 1 := by
    simpa [partialDeriv_coord] using partialDeriv_mul_conservationDenom ha hu₀ 1 x hξ hnear
  exact right_ne_zero_of_mul_eq_one hs

/-- Implicit differentiation gives the time derivative of a local footpoint map. -/
theorem ConservationFootRelationOn.partialDeriv_time {a u₀ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {U : Set ℝ^2}
    (hrel : ConservationFootRelationOn a u₀ ξ U) (hU : IsOpen U) (ha : Differentiable ℝ a)
    (hu₀ : Differentiable ℝ u₀) {x : ℝ^2} (hx : x ∈ U) (hξ : DifferentiableAt ℝ ξ x) :
    (∂[(0 : Fin 2)] ξ) x = -(a (u₀ (ξ x))) / conservationDenom a u₀ ξ x := by
  apply (eq_div_iff (hrel.denom_ne_zero hU ha hu₀ hx hξ)).2
  have hnear := (show Set.EqOn (fun y : ℝ^2 ↦ y 1)
    (fun y ↦ ξ y + y 0 * a (u₀ (ξ y))) U from hrel).eventuallyEq_of_mem (hU.mem_nhds hx)
  simpa [partialDeriv_coord] using partialDeriv_mul_conservationDenom ha hu₀ 0 x hξ hnear

/-- Implicit differentiation gives the space derivative of a local footpoint map. -/
theorem ConservationFootRelationOn.partialDeriv_space {a u₀ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {U : Set ℝ^2}
    (hrel : ConservationFootRelationOn a u₀ ξ U) (hU : IsOpen U) (ha : Differentiable ℝ a)
    (hu₀ : Differentiable ℝ u₀) {x : ℝ^2} (hx : x ∈ U) (hξ : DifferentiableAt ℝ ξ x) :
    (∂[(1 : Fin 2)] ξ) x = 1 / conservationDenom a u₀ ξ x := by
  apply (eq_div_iff (hrel.denom_ne_zero hU ha hu₀ hx hξ)).2
  have hnear := (show Set.EqOn (fun y : ℝ^2 ↦ y 1)
    (fun y ↦ ξ y + y 0 * a (u₀ (ξ y))) U from hrel).eventuallyEq_of_mem (hU.mem_nhds hx)
  simpa [partialDeriv_coord] using partialDeriv_mul_conservationDenom ha hu₀ 1 x hξ hnear

/-- A differentiable footpoint map on an open set gives a local conservation-law solution.

The denominator is automatically nonzero: differentiating the spatial footpoint relation gives
`ξ_x * conservationDenom = 1`. -/
theorem ConservationFootRelationOn.satisfies_pde_at {a u₀ : ℝ → ℝ} {ξ : ℝ^2 → ℝ} {U : Set ℝ^2}
    (hrel : ConservationFootRelationOn a u₀ ξ U) (hU : IsOpen U) (ha : Differentiable ℝ a)
    (hu₀ : Differentiable ℝ u₀) {x : ℝ^2} (hx : x ∈ U) (hξ : DifferentiableAt ℝ ξ x) :
    (∂[(0 : Fin 2)] (conservationSolutionFromFoot u₀ ξ)) x +
        a (conservationSolutionFromFoot u₀ ξ x) *
          (∂[(1 : Fin 2)] (conservationSolutionFromFoot u₀ ξ)) x = 0 := by
  have hnear := (show Set.EqOn (fun y : ℝ^2 ↦ y 1)
    (fun y ↦ ξ y + y 0 * a (u₀ (ξ y))) U from fun y hy ↦ hrel y hy).eventuallyEq_of_mem
      (hU.mem_nhds hx)
  have ht := partialDeriv_mul_conservationDenom ha hu₀ 0 x hξ hnear
  have hs := partialDeriv_mul_conservationDenom ha hu₀ 1 x hξ hnear
  simp only [partialDeriv_coord, Fin.isValue, zero_ne_one, one_ne_zero, ite_false,
    ite_true, zero_sub, zero_mul, sub_zero, one_mul] at ht hs
  have hden := right_ne_zero_of_mul_eq_one hs
  have htransport : (∂[(0 : Fin 2)] ξ) x +
      a (u₀ (ξ x)) * (∂[(1 : Fin 2)] ξ) x = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hden
    calc
      ((∂[(0 : Fin 2)] ξ) x + a (u₀ (ξ x)) * (∂[(1 : Fin 2)] ξ) x) * conservationDenom a u₀ ξ x =
        (∂[(0 : Fin 2)] ξ) x * conservationDenom a u₀ ξ x +
          a (u₀ (ξ x)) * ((∂[(1 : Fin 2)] ξ) x * conservationDenom a u₀ ξ x) := by
            cas
      _ = 0 := by rw [ht, hs]; simp
  unfold conservationSolutionFromFoot
  rw [partialDeriv_comp_real 0 hu₀.differentiableAt hξ,
    partialDeriv_comp_real 1 hu₀.differentiableAt hξ, ← mul_assoc, ← add_mul, htransport, zero_mul]

/-- The footpoint relation implies the initial condition at `t=0`. -/
theorem conservationSolutionFromFoot_initial {a u₀ : ℝ → ℝ} {ξ : ℝ^2 → ℝ}
    (x : ℝ^2) (hx : x 0 = 0) (hrelx : x 1 = ξ x + x 0 * a (u₀ (ξ x))) :
    conservationSolutionFromFoot u₀ ξ x = u₀ (x 1) := by
  have hξeq : ξ x = x 1 := by
    simpa [hx] using hrelx.symm
  simp [conservationSolutionFromFoot, hξeq]

/-!
## Shock time

The characteristic map at fixed time `t` is `ξ ↦ ξ + t * a(u₀(ξ))`. Its derivative is
`1 + t * a'(u₀(ξ)) * u₀'(ξ)`. In the classical characteristic picture, shock formation is tied to
this derivative hitting `0`, and we formalize the associated vanishing-time set. Since `deriv`
is totalized in Mathlib, this set has its intended analytic meaning only when `a` and `u₀` are
differentiable. The construction in `Characteristics.LocalInverse` assumes those
hypotheses.
-/

/-- The *shock set*: times `t ≥ 0` for which the characteristic map has vanishing derivative
somewhere. -/
def conservationShockSet (a u₀ : ℝ → ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ ∃ ξ : ℝ, 1 + t * deriv a (u₀ ξ) * deriv u₀ ξ = 0}

/-- Infimum of the nonnegative Jacobian-vanishing times, or `⊤` if the set is empty.

The infimum need not be attained on the unbounded footpoint line. The definition alone
gives no singularity or loss of global invertibility at the threshold. -/
noncomputable def conservationShockTime (a u₀ : ℝ → ℝ) : WithTop ℝ :=
  by
    classical
    exact
      if (conservationShockSet a u₀).Nonempty then
        ↑(sInf (conservationShockSet a u₀))
      else
        ⊤

/-- If the characteristic Jacobian never vanishes at nonnegative time, there is no finite
formal shock time. -/
theorem conservationShockTime_eq_top_of_empty (a u₀ : ℝ → ℝ) (h : conservationShockSet a u₀ = ∅) :
    conservationShockTime a u₀ = ⊤ := by
  simp [conservationShockTime, h]

private theorem bddBelow_conservationShockSet (a u₀ : ℝ → ℝ) :
    BddBelow (conservationShockSet a u₀) :=
  ⟨0, fun _t ht ↦ ht.1⟩

/-- Any nonnegative time strictly below the formal shock time is not in the shock set, so the
characteristic Jacobian `1 + t * a'(u₀(ξ)) * u₀'(ξ)` cannot vanish. -/
theorem conservationDenom_ne_zero_of_lt_shockTime (a u₀ : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : (t : WithTop ℝ) < conservationShockTime a u₀) :
    ∀ ξ : ℝ, 1 + t * deriv a (u₀ ξ) * deriv u₀ ξ ≠ 0 := by
  intro ξ hzero
  have ht_mem : t ∈ conservationShockSet a u₀ := ⟨ht0, ⟨ξ, hzero⟩⟩
  have hnonempty : (conservationShockSet a u₀).Nonempty := ⟨t, ht_mem⟩
  have hle : sInf (conservationShockSet a u₀) ≤ t :=
    csInf_le (bddBelow_conservationShockSet a u₀) ht_mem
  have hlt : t < sInf (conservationShockSet a u₀) := by
    simpa [conservationShockTime, hnonempty] using ht
  exact (not_lt_of_ge hle) hlt

/-- At a nonnegative time, being outside the shock set is exactly the pointwise
nonvanishing of the characteristic Jacobian. This is the condition under which the implicit
formula (61) of Evans, §3.2.5, Example 5, gives a solution, required at every footpoint `ξ`. -/
theorem not_mem_conservationShockSet_iff (a u₀ : ℝ → ℝ) {t : ℝ} (ht0 : 0 ≤ t) :
    t ∉ conservationShockSet a u₀ ↔ ∀ ξ : ℝ, 1 + t * deriv a (u₀ ξ) * deriv u₀ ξ ≠ 0 := by
  constructor
  · exact fun ht ξ hzero ↦ ht ⟨ht0, ⟨ξ, hzero⟩⟩
  · intro h ht
    rcases ht with ⟨_ht0, ξ, hzero⟩
    exact h ξ hzero

/-- When the product `a' (u₀ ξ) u₀' (ξ)` has infimum `m < 0`, the shock time is `-1 / m`. The
infimum need not be attained. -/
theorem conservationShockTime_eq_of_isGLB {a u₀ : ℝ → ℝ} {m : ℝ}
    (hm : IsGLB (Set.range fun ξ ↦ deriv a (u₀ ξ) * deriv u₀ ξ) m) (hneg : m < 0) :
    conservationShockTime a u₀ = ((-1 / m : ℝ) : WithTop ℝ) := by
  classical
  have hmem : ∀ {k : ℝ} (ξ : ℝ), deriv a (u₀ ξ) * deriv u₀ ξ = k → k < 0 →
      -1 / k ∈ conservationShockSet a u₀ := by
    intro k ξ hξ hk
    refine ⟨div_nonneg_of_nonpos (by norm_num) hk.le, ξ, ?_⟩
    rw [mul_assoc, hξ]
    have := hk.ne
    cas using [this]
  have hS : IsGLB (conservationShockSet a u₀) (-1 / m) := by
    constructor
    · rintro t ⟨ht, ξ, hξ⟩
      have hk : m ≤ deriv a (u₀ ξ) * deriv u₀ ξ := hm.1 ⟨ξ, rfl⟩
      rw [div_le_iff_of_neg hneg]
      nlinarith
    · intro L hL
      by_contra hlt
      rw [not_le] at hlt
      have hL0 : 0 < L := lt_trans (div_pos_of_neg_of_neg (by norm_num) hneg) hlt
      have hmL : m < -1 / L := by
        rw [div_lt_iff_of_neg hneg] at hlt
        rw [lt_div_iff₀ hL0]
        linarith
      obtain ⟨_, ⟨ξ, rfl⟩, -, hk⟩ := hm.exists_between hmL
      have hk0 : deriv a (u₀ ξ) * deriv u₀ ξ < 0 :=
        hk.trans (div_neg_of_neg_of_pos (by norm_num) hL0)
      have hle := hL (hmem ξ rfl hk0)
      rw [le_div_iff_of_neg hk0] at hle
      rw [lt_div_iff₀ hL0] at hk
      linarith
  obtain ⟨_, ⟨ξ, rfl⟩, -, hk⟩ := hm.exists_between hneg
  have hne : (conservationShockSet a u₀).Nonempty := ⟨_, hmem ξ rfl hk⟩
  simp only [conservationShockTime, hne, ↓reduceIte, hS.csInf_eq hne]

/-- When `a' (u₀) u₀' ≥ 0` the characteristic Jacobian never vanishes and there is no shock
time. -/
theorem conservationShockTime_eq_top_of_nonneg {a u₀ : ℝ → ℝ}
    (h : ∀ ξ, 0 ≤ deriv a (u₀ ξ) * deriv u₀ ξ) :
    conservationShockTime a u₀ = ⊤ := by
  refine conservationShockTime_eq_top_of_empty a u₀ (Set.eq_empty_of_forall_notMem ?_)
  rintro t ⟨ht, ξ, hξ⟩
  rw [mul_assoc] at hξ
  nlinarith [mul_nonneg ht (h ξ)]

end

end PDE.Hyperbolic.ConservationLaw.Scalar
