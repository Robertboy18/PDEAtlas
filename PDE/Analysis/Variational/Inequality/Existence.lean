/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Bilinear
import PDE.Analysis.Variational.QuadraticEnergy
import PDE.Analysis.WeakCompactness
import PDE.CalculusOfVariations.DirectMethod
import PDE.CalculusOfVariations.WeakLowerSemicontinuity
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Variational inequalities on bounded convex constraints

A nonnegative symmetric quadratic form attains its minimum on a nonempty
bounded closed convex subset of a real Hilbert space. Differentiating the
energy on this convex constraint gives the variational inequality. No
coercivity of the form is needed when the constraint itself is bounded. For the obstacle
problem of Evans, §8.4.2, these are Theorem 3, the existence of a minimizer of (24) over the
admissible set (25), and Theorem 4, its variational inequality. His admissible set is
unbounded; his proof of Theorem 3 takes a minimizing sequence that converges weakly in
`H¹₀(U)`.

## Main results

* `exists_variationalInequality_of_isBounded`: for a continuous symmetric bilinear form `B`
  with `B u u ≥ 0`, a continuous linear `ell` and a nonempty, bounded, closed, convex `K`,
  some `u ∈ K` satisfies `ell (v - u) ≤ B u (v - u)` for every `v ∈ K`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.2, (24), (25) and Theorem 3 (Existence of
  minimizer), p. 492, and Theorem 4 (Variational characterization of minimizer), p. 493.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.Variational

/-- A bounded closed convex constraint suffices for existence of a variational
inequality for a nonnegative symmetric form on a real Hilbert space. -/
theorem exists_variationalInequality_of_isBounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hsymm : ∀ u v, B u v = B v u) (hpos : ∀ u, 0 ≤ B u u)
    (ell : StrongDual ℝ H) {K : Set H}
    (hconvex : Convex ℝ K) (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) (hne : K.Nonempty) :
    ∃ u ∈ K, ∀ v ∈ K, ell (v - u) ≤ B u (v - u) := by
  let F := energy B ell
  have hF : ConvexOn ℝ univ F := by
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a b ha hb hab
    have hgap :
        a * F u + b * F v - F (a • u + b • v) =
          a * b / 2 * B (u - v) (u - v) := by
      simp only [F, energy, map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
        map_sub, sub_apply, hsymm v u]
      rw [show b = 1 - a by linarith]
      ring
    change F (a • u + b • v) ≤ a * F u + b * F v
    have hnonneg := mul_nonneg
      (div_nonneg (mul_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 2)) (hpos (u - v))
    linarith
  have hcont : Continuous F := by
    change Continuous (fun u : H ↦ (1 / 2 : ℝ) * B u u - ell u)
    fun_prop
  have hweak := PDE.CalculusOfVariations.lowerSemicontinuous_weakSpace_of_convex
    F hF hcont.lowerSemicontinuous
  obtain ⟨w, hw⟩ := hne
  obtain ⟨u, hu, hmin⟩ :=
    PDE.CalculusOfVariations.exists_isMinOn_of_weak_lowerSemicontinuousOn_of_bounded_sublevel
      PDE.Analysis.inclusionInDoubleDual_surjective F
      (PDE.CalculusOfVariations.isClosed_toWeakSpace_image_of_convex hconvex hclosed)
      (hweak.lowerSemicontinuousOn _) hw (hbounded.subset (fun _ hx ↦ hx.1))
  have hquadratic :
      HasFDerivAt (fun w : H ↦ (1 / 2 : ℝ) * B w w) (B u) u := by
    have hd := B.hasFDerivAt_of_bilinear
      (hasFDerivAt_id (𝕜 := ℝ) (x := u)) (hasFDerivAt_id (𝕜 := ℝ) (x := u))
    apply (hd.const_mul (1 / 2 : ℝ)).congr_fderiv
    ext v
    simp [hsymm v u]
    ring
  have hd : HasFDerivAt F (B u - ell) u := hquadratic.sub ell.hasFDerivAt
  have hvi := (PDE.CalculusOfVariations.isMinOn_iff_forall_fderiv_sub_nonneg
    (hF.subset (subset_univ K) hconvex) hu hd).mp hmin
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  simpa only [sub_apply, sub_nonneg] using hvi v hv

end PDE.Analysis.Variational
