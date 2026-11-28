/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Variational.WeightedEnergyBall
import PDE.Analysis.Evolution.Galerkin.Restriction

/-!
# Linear problems with a scalar feedback

An eigenvalue problem `B u = λ C u + f` whose eigenvalue correction `λ = ℓ(u)` is a bounded
linear functional of the unknown is quadratic in `u`. This module gives a solution strictly
inside a weighted energy ball `η ‖u‖² + ‖∇u‖² < r²`, for every real Hilbert space and all forms
and constants that satisfy a capacity condition, with no smallness of a Lipschitz constant. The
solution comes from a compactness argument, so its uniqueness is not claimed.
`exists_solution_of_weighted_energy_transport` is the companion for a transport nonlinearity,
where the coefficient of the frozen problem is a field and the form stays coercive by
cancellation.

## Main results

* `exists_solution_of_scalar_feedback`: a solution of `B u - ℓ(u) C u = f` strictly inside the
  ball, with the weighted energy bound of the a priori estimate.
* `exists_solution_of_scalar_feedback_on_submodule`: the same in a closed subspace.

## How it works

Freeze the scalar. For an input `w` in the ball let `T w` solve the linear problem
`B u - ℓ(w) C u = f`. If `B` has the lower bound `a ‖u‖² + b ‖∇u‖² - c ‖u‖ ‖∇u‖`, `C` is at most
`Θ ‖u‖²` on the diagonal and `|ℓ(w)| ≤ Λ` on the ball, the frozen form keeps the lower bound with
`ã = a - Θ Λ` in place of `a`, uniformly in the input. So the Lax–Milgram theorem
(`PDE.Analysis.Variational.solve`) defines `T`, and testing with the output gives
`ã ‖u‖² + b ‖∇u‖² - c ‖u‖ ‖∇u‖ ≤ ε ‖u‖`. Under the capacity condition

`b > c / (2 √η)`,  `(ã - η b) (b - c / (2 √η)) > ε² / (4 r²)`

this puts the output strictly inside the ball (`weighted_energy_lt_of_capacity`). The
difference of two outputs solves a frozen problem whose right side is `ℓ(w - w') C (T w')`, so
`T` is Lipschitz for a weaker norm in which `ℓ` is continuous. If the energy space embeds
compactly in the weaker space, Schauder's theorem
(`PDE.FixedPoint.exists_isFixedPt_of_compact_embedding_on`) gives a fixed point, and a fixed
point solves `B u - ℓ(u) C u = f`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.4, the proof of
  Proposition 2. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Variational

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **A linear problem with a scalar feedback.** Let `B` have the lower bound
`a ‖u‖² + b ‖∇u‖² - c ‖u‖ ‖∇u‖`, let `|C u u| ≤ Θ ‖u‖²`, let the functional `ℓ` be at most `Λ`
on the ball `η ‖u‖² + ‖∇u‖² ≤ r²` and continuous for the weaker norm of a compact injective
embedding `e`, and let the load `ell` have size `ε` in the value norm. With `ã = a - Θ Λ`, if

`b > c / (2 √η)`  and  `(ã - η b) (b - c / (2 √η)) > ε² / (4 r²)`,

there is `u` with `η ‖u‖² + ‖∇u‖² < r²` and `B u - ℓ(u) C u = ell`. Its weighted energy is at
most `ε² / (4 (ã - η b) (b - c / (2 √η)))`, the value that the a priori estimate gives. -/
theorem exists_solution_of_scalar_feedback
    {H Z : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (mass : V →L[ℝ] H) (gradient : V →L[ℝ] Z)
    (hnorm : ∀ u, ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2)
    (B C : V →L[ℝ] StrongDual ℝ V) (ℓ ell : StrongDual ℝ V)
    (e : V →L[ℝ] W) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    {a b c η r ε Θ Λ γ : ℝ} (hη : 0 < η) (hr : 0 < r) (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    (hcoercive : ∀ u,
      a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 - c * ‖mass u‖ * ‖gradient u‖ ≤ B u u)
    (hC : ∀ u, |C u u| ≤ Θ * ‖mass u‖ ^ 2)
    (hℓ : ∀ w, η * ‖mass w‖ ^ 2 + ‖gradient w‖ ^ 2 ≤ r ^ 2 → |ℓ w| ≤ Λ)
    (hℓweak : ∀ w, |ℓ w| ≤ γ * ‖e w‖)
    (hell : ∀ v, |ell v| ≤ ε * ‖mass v‖)
    (hb : c / (2 * √η) < b)
    (hcap : ε ^ 2 / (4 * r ^ 2) < (a - Θ * Λ - η * b) * (b - c / (2 * √η))) :
    ∃ u, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 < r ^ 2 ∧
      η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤
        ε ^ 2 / (4 * (a - Θ * Λ - η * b) * (b - c / (2 * √η))) ∧
      ∀ v, B u v - ℓ u * C u v = ell v := by
  classical
  have hsη : 0 < √η := Real.sqrt_pos.mpr hη
  set β := b - c / (2 * √η) with hβdef
  have hβ : 0 < β := sub_pos.mpr hb
  have hα : 0 < a - Θ * Λ - η * b :=
    pos_of_mul_pos_left ((by positivity : (0 : ℝ) ≤ ε ^ 2 / (4 * r ^ 2)).trans_lt hcap) hβ.le
  set κ := β * min η 1 with hκdef
  have hκ : 0 < κ := mul_pos hβ (lt_min hη one_pos)
  let s : Set V := weightedEnergyBall mass gradient η r
  let D : V → V →L[ℝ] StrongDual ℝ V := fun w ↦ B - ℓ w • C
  have hDapp (w u v : V) : D w u v = B u v - ℓ w * C u v := rfl
  -- The frozen form keeps the lower bound with `a - Θ Λ`.
  have hlower (w : V) (hw : w ∈ s) (u : V) :
      (a - Θ * Λ) * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 - c * ‖mass u‖ * ‖gradient u‖ ≤
        D w u u := by
    have h1 : |ℓ w * C u u| ≤ Λ * (Θ * ‖mass u‖ ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul (hℓ w hw) (hC u) (abs_nonneg _) ((abs_nonneg _).trans (hℓ w hw))
    rw [hDapp]
    linarith [hcoercive u, le_abs_self (ℓ w * C u u)]
  -- The lower bound dominates a multiple of the squared norm.
  have hquad (x y : ℝ) :
      κ * (x ^ 2 + y ^ 2) ≤ (a - Θ * Λ) * x ^ 2 + b * y ^ 2 - c * x * y := by
    have hmixed : c * x * y ≤ c / (2 * √η) * (η * x ^ 2 + y ^ 2) := by
      have hsq : 2 * √η * (x * y) ≤ η * x ^ 2 + y ^ 2 := by
        nlinarith [sq_nonneg (√η * x - y), Real.sq_sqrt hη.le]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hmin : min η 1 * (x ^ 2 + y ^ 2) ≤ η * x ^ 2 + y ^ 2 := by
      nlinarith [min_le_left η 1, min_le_right η 1, sq_nonneg x, sq_nonneg y]
    have h1 : κ * (x ^ 2 + y ^ 2) ≤ β * (η * x ^ 2 + y ^ 2) := by
      rw [hκdef, mul_assoc]
      exact mul_le_mul_of_nonneg_left hmin hβ.le
    have h2 : (a - Θ * Λ) * x ^ 2 + b * y ^ 2 - c / (2 * √η) * (η * x ^ 2 + y ^ 2) =
        (a - Θ * Λ - η * b) * x ^ 2 + β * (η * x ^ 2 + y ^ 2) := by
      rw [hβdef]
      ring
    nlinarith [mul_nonneg hα.le (sq_nonneg x)]
  have hD (w : V) (hw : w ∈ s) : IsCoercive (D w) :=
    ⟨κ, hκ, fun u ↦ by
      rw [mul_assoc, ← sq, hnorm]
      exact (hquad _ _).trans (hlower w hw u)⟩
  let T : V → V := fun w ↦ if h : w ∈ s then solve (D w) (hD w h) ell else 0
  have hT (w : V) (hw : w ∈ s) (v : V) : D w (T w) v = ell v := by
    simp only [T, hw, ↓reduceDIte]
    exact solve.isWeakSolution (D w) (hD w hw) ell v
  -- The output satisfies the a priori estimate, so it lies strictly inside the ball.
  have hapriori (w : V) (hw : w ∈ s) :
      (a - Θ * Λ) * ‖mass (T w)‖ ^ 2 + b * ‖gradient (T w)‖ ^ 2 -
        c * ‖mass (T w)‖ * ‖gradient (T w)‖ ≤ ε * ‖mass (T w)‖ := by
    calc
      _ ≤ D w (T w) (T w) := hlower w hw (T w)
      _ = ell (T w) := hT w hw (T w)
      _ ≤ ε * ‖mass (T w)‖ := (le_abs_self _).trans (hell (T w))
  have hstrict (w : V) (hw : w ∈ s) :
      η * ‖mass (T w)‖ ^ 2 + ‖gradient (T w)‖ ^ 2 < r ^ 2 :=
    weighted_energy_lt_of_capacity hη hr hc hb hcap (hapriori w hw)
  have hmap : Set.MapsTo T s s := fun w hw ↦ (hstrict w hw).le
  have hbound (u : V) (hu : u ∈ s) : ‖u‖ ≤ r / √η + r :=
    norm_le_of_mem_weightedEnergyBall hη hr.le (hnorm u) hu
  -- The difference of two outputs solves a frozen problem with the right side `ℓ(w - w') C (T w')`.
  let q : NNReal := ⟨‖e‖ * (γ * ‖C‖ * (r / √η + r)) / κ, by positivity⟩
  have hcontinuous (w : V) (hw : w ∈ s) (w' : V) (hw' : w' ∈ s) :
      ‖e (T w - T w')‖ ≤ q * ‖e (w - w')‖ := by
    have hδ (v : V) : D w (T w - T w') v = ℓ (w - w') * C (T w') v := by
      have h1 := hT w hw v
      have h2 := hT w' hw' v
      rw [hDapp] at h1 h2
      rw [hDapp, map_sub, map_sub, map_sub, sub_apply, sub_apply]
      linarith
    have hnormδ : ‖T w - T w'‖ ≤ γ * ‖e (w - w')‖ * ‖C‖ * (r / √η + r) / κ := by
      set δ := T w - T w'
      have hpair : κ * ‖δ‖ * ‖δ‖ ≤ (γ * ‖e (w - w')‖ * ‖C‖ * (r / √η + r)) * ‖δ‖ := by
        calc
          κ * ‖δ‖ * ‖δ‖ ≤ D w δ δ := by
            rw [mul_assoc, ← sq, hnorm]
            exact (hquad _ _).trans (hlower w hw δ)
          _ = ℓ (w - w') * C (T w') δ := hδ δ
          _ ≤ |ℓ (w - w')| * |C (T w') δ| := by
            rw [← abs_mul]
            exact le_abs_self _
          _ ≤ (γ * ‖e (w - w')‖) * (‖C‖ * (r / √η + r) * ‖δ‖) := by
            refine mul_le_mul (hℓweak _) ?_ (abs_nonneg _) (by positivity)
            calc
              |C (T w') δ| ≤ ‖C (T w')‖ * ‖δ‖ := (C (T w')).le_opNorm δ
              _ ≤ (‖C‖ * ‖T w'‖) * ‖δ‖ := by
                gcongr
                exact C.le_opNorm _
              _ ≤ (‖C‖ * (r / √η + r)) * ‖δ‖ := by
                gcongr
                exact hbound _ (hmap hw')
          _ = _ := by ring
      rw [le_div_iff₀ hκ]
      rcases (norm_nonneg δ).eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul]
        positivity
      · have := le_of_mul_le_mul_right hpair hpos
        linarith
    calc
      ‖e (T w - T w')‖ ≤ ‖e‖ * ‖T w - T w'‖ := e.le_opNorm _
      _ ≤ ‖e‖ * (γ * ‖e (w - w')‖ * ‖C‖ * (r / √η + r) / κ) :=
        mul_le_mul_of_nonneg_left hnormδ (norm_nonneg e)
      _ = q * ‖e (w - w')‖ := by
        change _ = ‖e‖ * (γ * ‖C‖ * (r / √η + r)) / κ * ‖e (w - w')‖
        ring
  obtain ⟨u, hu, hfix⟩ := PDE.FixedPoint.exists_isFixedPt_of_compact_embedding_on e he hcompact
    ⟨0, zero_mem_weightedEnergyBall mass gradient η r⟩
    (isClosed_weightedEnergyBall mass gradient η r)
    (convex_weightedEnergyBall mass gradient hη.le r)
    ((Metric.isBounded_closedBall (x := (0 : V)) (r := r / √η + r)).subset fun u hu ↦ by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound u hu) T hmap hcontinuous
  have hfix' : T u = u := hfix
  refine ⟨u, ?_, ?_, fun v ↦ ?_⟩
  · have h := hstrict u hu
    rwa [hfix'] at h
  · have h := weighted_energy_le_of_quadratic_constraint hη hc hb (sub_pos.mp hα)
      (hapriori u hu)
    rwa [hfix'] at h
  · have h := hT u hu v
    rwa [hfix'] at h

/-- A linear problem with a scalar feedback in a closed subspace `S`. Every hypothesis is
required only on `S`, the solution lies in `S`, and the equation is tested by the vectors of
`S`. The argument runs in the Hilbert space `S` itself. -/
theorem exists_solution_of_scalar_feedback_on_submodule
    {H Z : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : Submodule ℝ V) (hS : IsClosed (S : Set V))
    (mass : V →L[ℝ] H) (gradient : V →L[ℝ] Z)
    (hnorm : ∀ u ∈ S, ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2)
    (B C : V →L[ℝ] StrongDual ℝ V) (ℓ ell : StrongDual ℝ V)
    (e : V →L[ℝ] W) (he : Set.InjOn e S) (hcompact : IsCompactOperator e)
    {a b c η r ε Θ Λ γ : ℝ} (hη : 0 < η) (hr : 0 < r) (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    (hcoercive : ∀ u ∈ S,
      a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 - c * ‖mass u‖ * ‖gradient u‖ ≤ B u u)
    (hC : ∀ u ∈ S, |C u u| ≤ Θ * ‖mass u‖ ^ 2)
    (hℓ : ∀ w ∈ S, η * ‖mass w‖ ^ 2 + ‖gradient w‖ ^ 2 ≤ r ^ 2 → |ℓ w| ≤ Λ)
    (hℓweak : ∀ w ∈ S, |ℓ w| ≤ γ * ‖e w‖)
    (hell : ∀ v ∈ S, |ell v| ≤ ε * ‖mass v‖)
    (hb : c / (2 * √η) < b)
    (hcap : ε ^ 2 / (4 * r ^ 2) < (a - Θ * Λ - η * b) * (b - c / (2 * √η))) :
    ∃ u ∈ S, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 < r ^ 2 ∧
      η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤
        ε ^ 2 / (4 * (a - Θ * Λ - η * b) * (b - c / (2 * √η))) ∧
      ∀ v ∈ S, B u v - ℓ u * C u v = ell v := by
  have : CompleteSpace S := hS.completeSpace_coe
  obtain ⟨u, hu, hu', heq⟩ := exists_solution_of_scalar_feedback
    (mass.comp S.subtypeL) (gradient.comp S.subtypeL) (fun u ↦ hnorm u u.2)
    (PDE.Analysis.Evolution.restrictForm S B) (PDE.Analysis.Evolution.restrictForm S C)
    (PDE.Analysis.Evolution.restrictFunctional S ℓ)
    (PDE.Analysis.Evolution.restrictFunctional S ell) (e.comp S.subtypeL)
    (fun u v huv ↦ Subtype.ext (he u.2 v.2 huv)) (hcompact.comp_clm S.subtypeL)
    hη hr hc hγ
    (fun u ↦ by
      rw [PDE.Analysis.Evolution.restrictForm_apply]
      exact hcoercive u u.2)
    (fun u ↦ by
      rw [PDE.Analysis.Evolution.restrictForm_apply]
      exact hC u u.2)
    (fun w hw ↦ hℓ w w.2 hw) (fun w ↦ hℓweak w w.2) (fun v ↦ hell v v.2) hb hcap
  exact ⟨u, u.2, hu, hu', fun v hv ↦ heq ⟨v, hv⟩⟩

end PDE.Analysis.Variational
