/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.WeakSolution
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Lax–Milgram variational problems

The Lax–Milgram theorem: if `B` is a bounded bilinear form on a real Hilbert
space `V` that is coercive, `B v v ≥ c ‖v‖²` for some `c > 0`, then for every
`ell ∈ V*` there is a unique `u ∈ V` with `B u v = ell v` for all `v`, and
`‖u‖ ≤ ‖ell‖ / c`. Mathlib has the hard part as the equivalence
`IsCoercive.continuousLinearEquivOfBilin`. Here `solve B coercive ell` is the
inverse of that equivalence applied to the Riesz representative of `ell`, and
`solveCLM` is the same map as a continuous linear map `StrongDual ℝ V →L[ℝ] V`.
In the elliptic application `V = H¹₀(Ω)` and `B` is the Dirichlet form.

## Main results

* `solve B coercive ell`: the Lax–Milgram solution, and `solveCLM` the same
  as a continuous linear map `StrongDual ℝ V →L[ℝ] V`.
* `solve.isWeakSolution`, `IsWeakSolution.existsUnique`,
  `IsWeakSolution.eq_solve`: existence and uniqueness of weak solutions.
* `solve.norm_le_div`, `solveCLM.norm_le`: the quantitative estimate
  `‖u‖ ≤ ‖ell‖ / c` for a specified coercivity modulus `c`.
* `solve.norm_le`, `solve.norm_sub_le`: a uniform bound and Lipschitz
  dependence on the load with a constant depending only on `B`.
* `norm_le_dual_norm_div_of_pairing`: the elementary inequality
  `c ‖v‖² ≤ A v ⟹ ‖v‖ ≤ ‖A‖ / c` behind the estimates.

## How it works

The theorem is classical (Evans, §6.2.1, Theorem 1), and Mathlib's equivalence does the work; what
we add is the solution operator and its estimates. Uniqueness needs only coercivity on a normed
space (`IsWeakSolution.unique`). Existence uses completeness and the inner product through the
Riesz representative `(InnerProductSpace.toDual ℝ V).symm ell`. Mathlib's `IsCoercive` hides the
modulus inside an existential, so `solve.norm_le` can only produce some constant `C`. When the
modulus `c` is known, `solve.norm_le_div` gives `‖ell‖ / c` and `solveCLM.norm_le` gives
`‖solveCLM‖ ≤ c⁻¹`; both rest on `norm_le_dual_norm_div_of_pairing`, which is the computation
`β ‖u‖² ≤ B[u, u] ≤ ‖A u‖ ‖u‖` of step 3 of Evans's proof with `β = c`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1, pp. 315-316, and its proof,
  pp. 316-317. <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Chapter 5. <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

open scoped InnerProductSpace

/-- If `c ‖v‖² ≤ A v` with `c > 0`, then `‖v‖ ≤ ‖A‖ / c`. -/
theorem norm_le_dual_norm_div_of_pairing
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : StrongDual ℝ V) (c : ℝ) (hc : 0 < c) (v : V)
    (hpairing : c * ‖v‖ * ‖v‖ ≤ A v) :
    ‖v‖ ≤ ‖A‖ / c := by
  have hdual : A v ≤ ‖A‖ * ‖v‖ := by
    calc
      A v ≤ |A v| := le_abs_self _
      _ = ‖A v‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  have htotal : c * ‖v‖ * ‖v‖ ≤ ‖A‖ * ‖v‖ :=
    hpairing.trans hdual
  by_cases hv : ‖v‖ = 0
  · rw [hv]
    exact div_nonneg (norm_nonneg _) hc.le
  · have hvpos : 0 < ‖v‖ :=
      lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have hcancel : c * ‖v‖ ≤ ‖A‖ := by
      nlinarith
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hcancel)

section Coercive

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A coercive form on a real normed space has at most one weak solution for each
load. -/
theorem IsWeakSolution.unique
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (ell : StrongDual ℝ V) {u u' : V}
    (hu : IsWeakSolution B ell u) (hu' : IsWeakSolution B ell u') :
    u = u' := by
  have hhomogeneous : IsWeakSolution B 0 (u - u') :=
    hu.sub_same_load hu'
  have hzero : B (u - u') (u - u') = 0 := by
    simpa using hhomogeneous (u - u')
  rcases coercive with ⟨c, hc, hcoercive⟩
  have hbound := hcoercive (u - u')
  rw [hzero] at hbound
  have hnorm : ‖u - u'‖ = 0 := by
    by_contra hne
    have hnorm_pos : 0 < ‖u - u'‖ :=
      lt_of_le_of_ne (norm_nonneg (u - u')) (Ne.symm hne)
    have hproduct_pos : 0 < c * ‖u - u'‖ * ‖u - u'‖ :=
      mul_pos (mul_pos hc hnorm_pos) hnorm_pos
    exact (not_lt_of_ge hbound) hproduct_pos
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end Coercive

section Hilbert

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The weak solution supplied by Lax-Milgram, expressed through the Riesz
representative of the load. -/
def solve
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (ell : StrongDual ℝ V) : V :=
  let y : V := (InnerProductSpace.toDual ℝ V).symm ell
  (coercive.continuousLinearEquivOfBilin).symm y

/-- The Lax-Milgram solution operator as a continuous linear map from the
strong dual to the Hilbert space. -/
def solveCLM
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B) :
    StrongDual ℝ V →L[ℝ] V :=
  (coercive.continuousLinearEquivOfBilin).symm.toContinuousLinearMap.comp
    ((InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Evaluating the bundled solution operator gives `solve`. -/
@[simp]
theorem solveCLM_apply
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (ell : StrongDual ℝ V) :
    solveCLM B coercive ell = solve B coercive ell := by
  simp [solveCLM, solve]

/-- The Lax-Milgram solution satisfies the variational equation. -/
theorem solve.isWeakSolution
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (ell : StrongDual ℝ V) :
    IsWeakSolution B ell (solve B coercive ell) := by
  intro v
  let y : V := (InnerProductSpace.toDual ℝ V).symm ell
  have hu :
      coercive.continuousLinearEquivOfBilin (solve B coercive ell) = y := by
    simp [solve, y]
  have hB : ⟪y, v⟫_ℝ = B (solve B coercive ell) v := by
    have h :=
      coercive.continuousLinearEquivOfBilin_apply
        (v := solve B coercive ell) (w := v)
    simpa [hu] using h
  have hell : ⟪y, v⟫_ℝ = ell v := by
    change ⟪(InnerProductSpace.toDual ℝ V).symm ell, v⟫_ℝ = ell v
    exact
      InnerProductSpace.toDual_symm_apply
        (𝕜 := ℝ) (E := V) (x := v) (y := ell)
  exact hB.symm.trans hell

/-- Quantitative Lax-Milgram estimate for a specified coercivity modulus. -/
theorem solve.norm_le_div
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ * ‖v‖ ≤ B v v)
    (ell : StrongDual ℝ V) :
    ‖solve B coercive ell‖ ≤ ‖ell‖ / c := by
  apply norm_le_dual_norm_div_of_pairing ell c hc
  calc
    c * ‖solve B coercive ell‖ * ‖solve B coercive ell‖ ≤
        B (solve B coercive ell) (solve B coercive ell) :=
      hcoercive _
    _ = ell (solve B coercive ell) :=
      solve.isWeakSolution B coercive ell _

/-- The solution operator has norm at most the reciprocal of any supplied
coercivity modulus. -/
theorem solveCLM.norm_le
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖solveCLM B coercive‖ ≤ c⁻¹ := by
  apply (solveCLM B coercive).opNorm_le_bound (inv_nonneg.mpr hc.le)
  intro ell
  rw [solveCLM_apply]
  simpa [div_eq_mul_inv, mul_comm] using
    solve.norm_le_div B coercive c hc hcoercive ell

/-- The Lax-Milgram solution obeys a uniform estimate whose constant depends
only on the coercive form. -/
theorem solve.norm_le
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ell : StrongDual ℝ V, ‖solve B coercive ell‖ ≤ C * ‖ell‖ := by
  classical
  rcases coercive.bounded_below (B := B) with ⟨C0, hC0, hbelow⟩
  refine ⟨C0⁻¹, inv_pos.2 hC0, ?_⟩
  intro ell
  let y : V := (InnerProductSpace.toDual ℝ V).symm ell
  have hy_norm : ‖y‖ = ‖ell‖ := by
    simp [y, (InnerProductSpace.toDual ℝ V).symm.norm_map ell]
  have hEq :
      coercive.continuousLinearEquivOfBilin (solve B coercive ell) = y := by
    simp [solve, y]
  have hBu :
      (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B)
          (solve B coercive ell) = y := by
    simpa [IsCoercive.continuousLinearEquivOfBilin] using hEq
  have h0 : C0 * ‖solve B coercive ell‖ ≤ ‖y‖ := by
    simpa [hBu] using hbelow (solve B coercive ell)
  have hsolution : ‖solve B coercive ell‖ ≤ C0⁻¹ * ‖y‖ := by
    have hmul :=
      mul_le_mul_of_nonneg_left h0 (le_of_lt (inv_pos.2 hC0))
    have hmul' :
        (C0⁻¹ * C0) * ‖solve B coercive ell‖ ≤ C0⁻¹ * ‖y‖ := by
      simpa [mul_assoc] using hmul
    simpa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hC0)] using hmul'
  simpa [hy_norm, mul_assoc] using hsolution

/-- The Lax-Milgram solution depends Lipschitz-continuously on the load. -/
theorem solve.norm_sub_le
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell₁ ell₂ : StrongDual ℝ V,
      ‖solve B coercive ell₁ - solve B coercive ell₂‖ ≤
        C * ‖ell₁ - ell₂‖ := by
  rcases solve.norm_le B coercive with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro ell₁ ell₂
  have hlin :
      solve B coercive (ell₁ - ell₂) =
        solve B coercive ell₁ - solve B coercive ell₂ := by
    rw [← solveCLM_apply B coercive (ell₁ - ell₂)]
    rw [map_sub]
    simp
  simpa [hlin] using hC (ell₁ - ell₂)

/-- The continuous-linear-map solver also returns a weak solution. -/
theorem solveCLM.isWeakSolution
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (ell : StrongDual ℝ V) :
    IsWeakSolution B ell (solveCLM B coercive ell) := by
  simpa using solve.isWeakSolution B coercive ell

/-- Lax-Milgram with zero load returns the zero vector. -/
@[simp]
theorem solve.zero
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B) :
    solve B coercive 0 = 0 :=
  IsWeakSolution.unique B coercive 0
    (solve.isWeakSolution B coercive 0) (IsWeakSolution.zero B)

/-- Lax-Milgram gives a unique weak solution for every continuous load. -/
theorem IsWeakSolution.existsUnique
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (ell : StrongDual ℝ V) :
    ∃! u, IsWeakSolution B ell u := by
  refine ⟨solve B coercive ell, solve.isWeakSolution B coercive ell, ?_⟩
  intro u hu
  exact IsWeakSolution.unique B coercive ell hu
    (solve.isWeakSolution B coercive ell)

/-- Every weak solution agrees with the Lax-Milgram solution. -/
theorem IsWeakSolution.eq_solve
    (B : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive B)
    (ell : StrongDual ℝ V) {u : V}
    (hu : IsWeakSolution B ell u) :
    u = solve B coercive ell :=
  IsWeakSolution.unique B coercive ell hu
    (solve.isWeakSolution B coercive ell)

end Hilbert

end PDE.Analysis.Variational
