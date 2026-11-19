/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ClassicalCurve

/-!
# The Hamiltonian of a classical Lagrangian

Suppose every momentum equation `∇_q L(q, x) = p` has the unique solution `q = Q(p, x)`, with
`Q` of class `C¹`, and set `H(p, x) = ⟪p, Q(p, x)⟫ - L(Q(p, x), x)`. Then every Euler–Lagrange
critical curve satisfies Hamilton's equations, with one-sided derivatives at the endpoints, and
conserves `H`. This is Evans, §3.3.1, Theorem 2, for a Lagrangian on a real Hilbert space. No
minimizing property, Hamilton–Jacobi solution or convexity of the Lagrangian is assumed.

## Main results

* `legendreHamiltonian_gradients`: `∇_p H = Q` and `∇_x H = -∇_x L(Q, x)`; the derivatives of
  `Q` cancel because `Q` solves the momentum equation.
* `hamilton_equations_and_conservation_of_eulerLagrange`: Hamilton's equations and conservation
  of `H` along a critical curve.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.1, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped RealInnerProductSpace Gradient

namespace PDE.CalculusOfVariations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {L : E × E → ℝ} {Q : E × E → E}

/-- The Hamiltonian obtained from an inverse momentum map `Q`. -/
def legendreHamiltonian (L : E × E → ℝ) (Q : E × E → E) (z : E × E) : ℝ :=
  ⟪z.1, Q z⟫ - L (Q z, z.2)

/-- The derivative of the inverse momentum map cancels from the differential
of the Hamiltonian. -/
theorem hasFDerivAt_legendreHamiltonian {p x : E}
    (hL : DifferentiableAt ℝ L (Q (p, x), x))
    (hQ : DifferentiableAt ℝ Q (p, x))
    (hsolve : ∇ (fun q ↦ L (q, x)) (Q (p, x)) = p) :
    HasFDerivAt (legendreHamiltonian L Q)
      (((InnerProductSpace.toDual ℝ E) (Q (p, x))).comp (ContinuousLinearMap.fst ℝ E E) -
        ((InnerProductSpace.toDual ℝ E)
          (∇ (fun y ↦ L (Q (p, x), y)) x)).comp (ContinuousLinearMap.snd ℝ E E))
      (p, x) := by
  have hd := ((hasFDerivAt_fst (𝕜 := ℝ)).inner ℝ hQ.hasFDerivAt).sub
    (hL.hasFDerivAt.comp (p, x)
      (hQ.hasFDerivAt.prodMk (hasFDerivAt_snd (𝕜 := ℝ))))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro z
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', fderivInnerCLM_apply, InnerProductSpace.toDual_apply_apply]
  rw [fderiv_lagrangian_apply hL, hsolve, real_inner_comm (Q (p, x)) z.1]
  ring

/-- The partial gradients of the Hamiltonian are the inverse momentum and the
negative position gradient of the Lagrangian. -/
theorem legendreHamiltonian_gradients (hL : ContDiff ℝ 1 L) (hQ : ContDiff ℝ 1 Q)
    (hsolve : ∀ p x, ∇ (fun q ↦ L (q, x)) (Q (p, x)) = p) (p x : E) :
    ∇ (fun r ↦ legendreHamiltonian L Q (r, x)) p = Q (p, x) ∧
      ∇ (fun y ↦ legendreHamiltonian L Q (p, y)) x =
        -∇ (fun y ↦ L (Q (p, x), y)) x := by
  have hd := hasFDerivAt_legendreHamiltonian
    (hL.differentiable one_ne_zero _) (hQ.differentiable one_ne_zero _) (hsolve p x)
  constructor
  · apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    apply (hd.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p x)).congr_fderiv
    ext v
    simp
  · apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    apply (hd.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) p x)).congr_fderiv
    ext v
    simp

/-- Every classical Euler–Lagrange critical curve satisfies Hamilton's equations
and conserves the autonomous Hamiltonian. The inverse hypothesis says exactly
that each momentum equation has the unique solution given by `Q`.

The ODE includes one-sided derivatives at both endpoints. No minimizing
property or Hamilton–Jacobi solution is assumed. -/
theorem hamilton_equations_and_conservation_of_eulerLagrange
    {a b : ℝ} {X : ℝ → E} (hab : a < b) (hL : ContDiff ℝ 2 L) (hQ : ContDiff ℝ 1 Q)
    (hinverse : ∀ q p x, ∇ (fun r ↦ L (r, x)) q = p ↔ q = Q (p, x))
    (hX : ContDiffOn ℝ 2 X (Icc a b))
    (hEL : ∀ s ∈ Icc a b,
      derivWithin
          (fun t ↦ ∇ (fun q ↦ L (q, X t)) (derivWithin X (Icc a b) t))
          (Icc a b) s =
        ∇ (fun x ↦ L (derivWithin X (Icc a b) s, x)) (X s)) :
    let p := fun s ↦ ∇ (fun q ↦ L (q, X s)) (derivWithin X (Icc a b) s)
    let H := legendreHamiltonian L Q
    (∀ s ∈ Icc a b,
      HasDerivWithinAt X (∇ (fun r ↦ H (r, X s)) (p s)) (Icc a b) s ∧
        HasDerivWithinAt p (-∇ (fun x ↦ H (p s, x)) (X s)) (Icc a b) s) ∧
      ∀ s ∈ Icc a b, H (p s, X s) = H (p a, X a) := by
  let p := fun s ↦ ∇ (fun q ↦ L (q, X s)) (derivWithin X (Icc a b) s)
  let H := legendreHamiltonian L Q
  change (∀ s ∈ Icc a b,
    HasDerivWithinAt X (∇ (fun r ↦ H (r, X s)) (p s)) (Icc a b) s ∧
      HasDerivWithinAt p (-∇ (fun x ↦ H (p s, x)) (X s)) (Icc a b) s) ∧
        ∀ s ∈ Icc a b, H (p s, X s) = H (p a, X a)
  have hU := uniqueDiffOn_Icc hab
  have hp : ContDiffOn ℝ 1 p (Icc a b) :=
    (contDiff_lagrangian_gradients hL).1.comp_contDiffOn
      ((hX.derivWithin hU (by norm_num)).prodMk (hX.of_le (by norm_num)))
  have hsolve (p x : E) : ∇ (fun q ↦ L (q, x)) (Q (p, x)) = p :=
    (hinverse (Q (p, x)) p x).mpr rfl
  have hvelocity (s : ℝ) : Q (p s, X s) = derivWithin X (Icc a b) s :=
    ((hinverse (derivWithin X (Icc a b) s) (p s) (X s)).mp rfl).symm
  have hgrad (s : ℝ) := legendreHamiltonian_gradients
    (hL.of_le (by norm_num)) hQ hsolve (p s) (X s)
  have henergy (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun t ↦ H (p t, X t)) 0 (Icc a b) s := by
    have hd := (hasFDerivAt_legendreHamiltonian
      (hL.differentiable (by norm_num) _) (hQ.differentiable one_ne_zero _)
      (hsolve (p s) (X s))).comp_hasDerivWithinAt s
          ((hp.differentiableOn one_ne_zero s hs).hasDerivWithinAt.prodMk
            (hX.differentiableOn (by norm_num) s hs).hasDerivWithinAt)
    apply hd.congr_deriv
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      InnerProductSpace.toDual_apply_apply, hvelocity]
    rw [show derivWithin p (Icc a b) s =
      ∇ (fun x ↦ L (derivWithin X (Icc a b) s, x)) (X s) from hEL s hs]
    exact sub_eq_zero.mpr (real_inner_comm _ _)
  constructor
  · intro s hs
    constructor
    · simpa only [H, (hgrad s).1, hvelocity] using
        (hX.differentiableOn (by norm_num) s hs).hasDerivWithinAt
    · simpa only [H, (hgrad s).2, hvelocity, neg_neg, ← hEL s hs] using
        (hp.differentiableOn one_ne_zero s hs).hasDerivWithinAt
  · apply constant_of_derivWithin_zero
      (fun s hs ↦ (henergy s hs).differentiableWithinAt)
    intro s hs
    exact (henergy s (Ico_subset_Icc_self hs)).derivWithin (hU s (Ico_subset_Icc_self hs))

end PDE.CalculusOfVariations
