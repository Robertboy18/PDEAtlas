/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Field

/-!
# Mixed derivatives of sums

`mixedDeriv k l F x y = ∂ₓᵏ (∂ᵧˡ F)` is built from one-variable iterated derivatives, which are
additive only where the summands are differentiable often enough. `MixedSmooth k l F x y` asks
that `F x'` be `Cˡ` at `y` for `x'` near `x` and that `x' ↦ ∂ᵧˡ F x' y` be `Cᵏ` at `x`; then
`mixedDeriv` of a sum is the sum (`mixedDeriv_add`). A function that is `Cⁿ` near `(x, y)` as a
function of two variables is `MixedSmooth k l` there for `k + l ≤ n`
(`mixedSmooth_of_contDiffAt`): the partial derivatives `∂ᵧʲ F` are `C^{n-j}` jointly, by the
parametric derivative `ContDiffAt.fderiv`. Mixed derivatives depend only on the germ of `F` at
`(x, y)` (`mixedDeriv_congr_of_eventuallyEq`).

## Main definitions

* `MixedSmooth`: the regularity of `F` at `(x, y)` under which `mixedDeriv k l` is additive.
* `partialY`: the partial derivatives `∂ᵧʲ F` as functions of two variables.

## Main results

* `mixedDeriv_add`: for `MixedSmooth k l` functions `F`, `G`,
  `mixedDeriv k l (F + G) x y = mixedDeriv k l F x y + mixedDeriv k l G x y`.
* `mixedSmooth_of_contDiffAt`: a function that is `Cⁿ` at `(x, y)` as a function of two variables
  is `MixedSmooth k l` there for `k + l ≤ n`.
* `contDiffAt_partialY`: if `F` is `Cⁿ` at `p`, then `∂ᵧʲ F` is `C^(n - j)` at `p` for `j ≤ n`.
* `mixedDeriv_congr_of_eventuallyEq`: mixed derivatives at a point depend only on the germ of the
  function there.
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open Filter
open scoped Topology

/-- The regularity of `F` at `(x, y)` under which `mixedDeriv k l` is additive. -/
structure MixedSmooth (k l : ℕ) (F : ℝ → ℝ → ℝ) (x y : ℝ) : Prop where
  /-- `F x'` is `Cˡ` at `y` for `x'` near `x`. -/
  inner : ∀ᶠ x' in 𝓝 x, ContDiffAt ℝ l (F x') y
  /-- `x' ↦ ∂ᵧˡ F x' y` is `Cᵏ` at `x`. -/
  outer : ContDiffAt ℝ k (fun x' ↦ iteratedDeriv l (F x') y) x

/-- **Mixed derivatives of sums.** -/
theorem mixedDeriv_add {k l : ℕ} {F G : ℝ → ℝ → ℝ} {x y : ℝ} (hF : MixedSmooth k l F x y)
    (hG : MixedSmooth k l G x y) :
    mixedDeriv k l (fun x y ↦ F x y + G x y) x y = mixedDeriv k l F x y + mixedDeriv k l G x y := by
  unfold mixedDeriv
  have heq : (fun x' ↦ iteratedDeriv l (fun y ↦ F x' y + G x' y) y) =ᶠ[𝓝 x]
      fun x' ↦ iteratedDeriv l (F x') y + iteratedDeriv l (G x') y := by
    filter_upwards [hF.inner, hG.inner] with x' h1 h2
    exact iteratedDeriv_add h1 h2
  rw [heq.iteratedDeriv_eq]
  exact iteratedDeriv_add hF.outer hG.outer

/-- Mixed derivatives at a point depend only on the germ of the function of two variables
there. -/
theorem mixedDeriv_congr_of_eventuallyEq {F G : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : (fun q : ℝ × ℝ ↦ F q.1 q.2) =ᶠ[𝓝 (x, y)] fun q ↦ G q.1 q.2) (k l : ℕ) :
    mixedDeriv k l F x y = mixedDeriv k l G x y := by
  rw [nhds_prod_eq] at h
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp h
  unfold mixedDeriv
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hU] with x' hx'
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hV] with y' hy'
  exact hUV (Set.mk_mem_prod hx' hy')

/-- The partial derivatives `∂ᵧʲ F` as functions of two variables. -/
noncomputable def partialY (F : ℝ → ℝ → ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ := iteratedDeriv j (F p.1) p.2

/-- If `F` is `Cⁿ` at `p` as a function of two variables, then `∂ᵧʲ F` is `C^(n - j)` at `p` for
every `j ≤ n`. -/
theorem contDiffAt_partialY {F : ℝ → ℝ → ℝ} {n : ℕ} {p : ℝ × ℝ}
    (hF : ContDiffAt ℝ n (fun q : ℝ × ℝ ↦ F q.1 q.2) p) :
    ∀ j ≤ n, ContDiffAt ℝ ((n - j : ℕ) : WithTop ℕ∞) (partialY F j) p := by
  intro j hj
  induction j generalizing p with
  | zero =>
    have h0 : partialY F 0 = fun q : ℝ × ℝ ↦ F q.1 q.2 := by funext q; simp [partialY]
    rw [h0]; simpa using hF
  | succ j ih =>
    have hj' := ih hF (by omega)
    have hcomp : ContDiffAt ℝ ((n - j : ℕ) : WithTop ℕ∞) (Function.uncurry fun (q : ℝ × ℝ) (t : ℝ) ↦
        partialY F j (q.1, t)) (p, p.2) := by
      have hlin : ContDiff ℝ ⊤ (fun z : (ℝ × ℝ) × ℝ ↦ (z.1.1, z.2)) := by fun_prop
      exact hj'.comp (p, p.2) (hlin.contDiffAt.of_le le_top)
    have hfd := ContDiffAt.fderiv (f := fun (q : ℝ × ℝ) (t : ℝ) ↦ partialY F j (q.1, t))
      (g := fun q : ℝ × ℝ ↦ q.2) (m := (n - (j + 1) : ℕ)) hcomp
      contDiffAt_snd (by
        have : ((n - (j + 1) : ℕ) : WithTop ℕ∞) + 1 = ((n - j : ℕ) : WithTop ℕ∞) := by
          norm_cast; omega
        rw [this])
    have hval : partialY F (j + 1) = fun q ↦
        (fderiv ℝ (fun t ↦ partialY F j (q.1, t)) q.2) 1 := by
      funext q
      simp only [partialY, iteratedDeriv_succ]
      rfl
    rw [hval]
    exact hfd.clm_apply contDiffAt_const

/-- **Regularity for mixed derivatives.** A function that is `Cⁿ` at `(x, y)` as a function of two
variables is `MixedSmooth k l` there for `k + l ≤ n`. -/
theorem mixedSmooth_of_contDiffAt {F : ℝ → ℝ → ℝ} {n k l : ℕ} (hkl : k + l ≤ n) {x y : ℝ}
    (hF : ContDiffAt ℝ n (fun q : ℝ × ℝ ↦ F q.1 q.2) (x, y)) : MixedSmooth k l F x y := by
  refine ⟨?_, ?_⟩
  · have hev := hF.eventually (by simp)
    have hcont : Continuous fun x' : ℝ ↦ (x', y) := by fun_prop
    have hev' := hcont.continuousAt.eventually hev
    filter_upwards [hev'] with x' hx'
    have hlin : ContDiff ℝ ⊤ (fun t : ℝ ↦ (x', t)) := by fun_prop
    have h := ContDiffAt.comp (g := fun q : ℝ × ℝ ↦ F q.1 q.2) (f := fun t : ℝ ↦ (x', t)) y hx'
      (hlin.contDiffAt.of_le le_top)
    exact h.of_le (by exact_mod_cast (show l ≤ n by omega))
  · have hP := contDiffAt_partialY hF l (by omega)
    have hlin : ContDiff ℝ ⊤ (fun x' : ℝ ↦ (x', y)) := by fun_prop
    have h := ContDiffAt.comp (g := partialY F l) (f := fun x' : ℝ ↦ (x', y)) x hP
      (hlin.contDiffAt.of_le le_top)
    exact h.of_le (by exact_mod_cast (show k ≤ n - l by omega))

end CAS.Numerics.TensorSpline
