/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import PDE.Analysis.Operator.StrongMonotonicity
import PDE.Analysis.Variational.LaxMilgram

/-!
# Monotone semilinear variational equations

We give the abstract stability and uniqueness argument for a
coercive variational form perturbed by a monotone nonlinear load. If `u` and
`w` solve equations with loads `ell₁` and `ell₂`, coercivity and monotonicity
give

`‖u - w‖ ≤ ‖ell₁ - ell₂‖ / c`.

The result is stated directly for continuous bilinear forms and strong duals;
no problem structure is introduced.

## Main results

* `coercive_le_semilinear_pairing_sub`,
  `coercivity_sub_mul_norm_sq_le_semilinear_pairing_sub_of_semimonotone`:
  strong monotonicity of `u ↦ B u + N u` with modulus `c`, or `c - L` for a
  semimonotone load with loss `L`.
* `norm_sub_le_load_sub_norm_div`,
  `norm_sub_le_load_sub_norm_div_of_semimonotone`,
  `norm_sub_le_load_sub_norm_div_of_lipschitz_lt_coercivity`: stability of
  solutions with respect to the load.
* `eq_of_coercive_of_monotone`, `eq_of_coercive_of_semimonotone`,
  `eq_zero_of_coercive_of_nonneg`: uniqueness and zero-load rigidity.
* `bijective_semilinear_operator_of_semimonotone_of_lipschitzWith`,
  `existsUnique_semilinear_solution_of_monotone_of_lipschitzWith`: for a
  globally Lipschitz load, existence for every right-hand side by a
  Hilbert-space forward-step (contraction) argument, with no smallness
  condition on the Lipschitz constant when the load is monotone.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.1 (monotonicity methods).
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Chapter 5 (Hilbert Spaces), pp. 131-156.
  <https://doi.org/10.1007/978-0-387-70914-7_5>
-/

@[expose] public section

namespace SobolevSpace.Weak

open PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Coercivity of the bilinear part and monotonicity of the nonlinear part
make their sum strongly monotone. -/
theorem coercive_le_semilinear_pairing_sub
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    {u w : V}
    (hmonotone : 0 ≤ (N u - N w) (u - w)) :
    c * ‖u - w‖ * ‖u - w‖ ≤
      ((B u + N u) - (B w + N w)) (u - w) := by
  let d : V := u - w
  change c * ‖d‖ * ‖d‖ ≤
    ((B u + N u) - (B w + N w)) d
  have hmonotone' : 0 ≤ N u d - N w d := by
    simpa only [d, sub_apply] using hmonotone
  calc
    c * ‖d‖ * ‖d‖ ≤ B d d := hcoercive d
    _ = (B u - B w) d := by
      change B (u - w) d = (B u - B w) d
      rw [B.map_sub]
    _ ≤ ((B u + N u) - (B w + N w)) d := by
      simp only [sub_apply, add_apply]
      linarith [hmonotone']

/-- The inverse of a coercive monotone semilinear operator is Lipschitz on
its range, with constant `1 / c`. -/
theorem norm_sub_le_semilinear_operator_sub_norm_div
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    {u w : V}
    (hmonotone : 0 ≤ (N u - N w) (u - w)) :
    ‖u - w‖ ≤
      ‖(B u + N u) - (B w + N w)‖ / c := by
  let d : V := u - w
  let A : StrongDual ℝ V := (B u + N u) - (B w + N w)
  change ‖d‖ ≤ ‖A‖ / c
  have hpairing : c * ‖d‖ * ‖d‖ ≤ A d := by
    simpa only [d, A] using
      coercive_le_semilinear_pairing_sub B c hcoercive N hmonotone
  exact norm_le_dual_norm_div_of_pairing A c hc d hpairing

/-- If the nonlinear load is semimonotone with constant `L`, coercivity
leaves the strong-monotonicity modulus `c - L`. -/
theorem coercivity_sub_mul_norm_sq_le_semilinear_pairing_sub_of_semimonotone
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    (L : ℝ)
    {u w : V}
    (hsemimonotone :
      -L * ‖u - w‖ * ‖u - w‖ ≤
        (N u - N w) (u - w)) :
    (c - L) * ‖u - w‖ * ‖u - w‖ ≤
      ((B u + N u) - (B w + N w)) (u - w) := by
  let d : V := u - w
  change (c - L) * ‖d‖ * ‖d‖ ≤
    ((B u + N u) - (B w + N w)) d
  have hsemimonotone' :
      -L * ‖d‖ * ‖d‖ ≤ N u d - N w d := by
    simpa only [d, sub_apply] using hsemimonotone
  have hcoercive' : c * ‖d‖ * ‖d‖ ≤ B d d :=
    hcoercive d
  have hBsub : B d d = B u d - B w d := by
    change B (u - w) d = B u d - B w d
    rw [B.map_sub, sub_apply]
  simp only [sub_apply, add_apply]
  linarith [hBsub]

/-- A semimonotone perturbation preserves inverse stability whenever its
one-sided loss `L` is smaller than the coercivity modulus `c`. -/
theorem norm_sub_le_semilinear_operator_sub_norm_div_of_semimonotone
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    (L : ℝ) (hLc : L < c)
    {u w : V}
    (hsemimonotone :
      -L * ‖u - w‖ * ‖u - w‖ ≤
        (N u - N w) (u - w)) :
    ‖u - w‖ ≤
      ‖(B u + N u) - (B w + N w)‖ / (c - L) := by
  let d : V := u - w
  let A : StrongDual ℝ V := (B u + N u) - (B w + N w)
  change ‖d‖ ≤ ‖A‖ / (c - L)
  apply norm_le_dual_norm_div_of_pairing A (c - L) (sub_pos.mpr hLc)
  simpa only [d, A] using
    coercivity_sub_mul_norm_sq_le_semilinear_pairing_sub_of_semimonotone
      B c hcoercive N L hsemimonotone

/-- A coercive monotone semilinear operator is injective. -/
theorem injective_semilinear_operator_of_monotone
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    (hmonotone : ∀ u w, 0 ≤ (N u - N w) (u - w)) :
    Function.Injective fun u ↦ B u + N u := by
  intro u w huw
  have hnorm :
      ‖u - w‖ ≤
        ‖(B u + N u) - (B w + N w)‖ / c :=
    norm_sub_le_semilinear_operator_sub_norm_div
      B c hc hcoercive N (hmonotone u w)
  change B u + N u = B w + N w at huw
  rw [huw, sub_self, norm_zero, zero_div] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

/-- A coercive semilinear operator remains injective under a semimonotone
perturbation whose one-sided loss is smaller than the coercivity modulus. -/
theorem injective_semilinear_operator_of_semimonotone
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    (L : ℝ) (hLc : L < c)
    (hsemimonotone : ∀ u w,
      -L * ‖u - w‖ * ‖u - w‖ ≤
        (N u - N w) (u - w)) :
    Function.Injective fun u ↦ B u + N u := by
  intro u w huw
  have hnorm :
      ‖u - w‖ ≤
        ‖(B u + N u) - (B w + N w)‖ / (c - L) :=
    norm_sub_le_semilinear_operator_sub_norm_div_of_semimonotone
      B c hcoercive N L hLc (hsemimonotone u w)
  change B u + N u = B w + N w at huw
  rw [huw, sub_self, norm_zero, zero_div] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

section Hilbert

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [CompleteSpace W]

/-- A globally Lipschitz semilinear operator is bijective when coercivity
dominates the one-sided monotonicity loss of the nonlinear term. This is a
Hilbert-space forward-step argument, not an application of Browder–Minty. -/
theorem bijective_semilinear_operator_of_semimonotone_of_lipschitzWith
    (B : W →L[ℝ] W →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : W → StrongDual ℝ W)
    (L : ℝ) (hLc : L < c)
    {K : NNReal} (hN : LipschitzWith K N)
    (hsemimonotone : ∀ u w,
      -L * ‖u - w‖ * ‖u - w‖ ≤
        (N u - N w) (u - w)) :
    Function.Bijective fun u ↦ B u + N u := by
  exact
    PDE.Analysis.Operator.bijective_dual_of_pairing_lower_bound_of_lipschitzWith
      (fun u ↦ B u + N u) (c - L) (sub_pos.mpr hLc)
      (fun u w ↦
        coercivity_sub_mul_norm_sq_le_semilinear_pairing_sub_of_semimonotone
          B c hcoercive N L (hsemimonotone u w))
      (B.lipschitzWith.add hN)

/-- A coercive monotone semilinear operator with a globally Lipschitz
nonlinear term is bijective. No smallness condition is imposed on the
Lipschitz constant. -/
theorem bijective_semilinear_operator_of_monotone_of_lipschitzWith
    (B : W →L[ℝ] W →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : W → StrongDual ℝ W)
    {K : NNReal} (hN : LipschitzWith K N)
    (hmonotone : ∀ u w, 0 ≤ (N u - N w) (u - w)) :
    Function.Bijective fun u ↦ B u + N u := by
  apply bijective_semilinear_operator_of_semimonotone_of_lipschitzWith
    B c hcoercive N 0 hc hN
  intro u w
  simpa only [neg_zero, zero_mul] using hmonotone u w

/-- Under the semimonotonicity and Lipschitz assumptions above, every load
has a unique semilinear weak solution. -/
theorem existsUnique_semilinear_solution_of_semimonotone_of_lipschitzWith
    (B : W →L[ℝ] W →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : W → StrongDual ℝ W)
    (L : ℝ) (hLc : L < c)
    {K : NNReal} (hN : LipschitzWith K N)
    (hsemimonotone : ∀ u w,
      -L * ‖u - w‖ * ‖u - w‖ ≤
        (N u - N w) (u - w))
    (ell : StrongDual ℝ W) :
    ∃! u, ∀ v, B u v + N u v = ell v := by
  have hbijective :=
    bijective_semilinear_operator_of_semimonotone_of_lipschitzWith
      B c hcoercive N L hLc hN hsemimonotone
  obtain ⟨u, hu, hunique⟩ := hbijective.existsUnique ell
  refine ⟨u, ?_, ?_⟩
  · intro v
    exact DFunLike.congr_fun hu v
  · intro w hw
    apply hunique w
    ext v
    exact hw v

/-- Every load has a unique weak solution for a coercive monotone
semilinear operator whose nonlinear term is globally Lipschitz. -/
theorem existsUnique_semilinear_solution_of_monotone_of_lipschitzWith
    (B : W →L[ℝ] W →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : W → StrongDual ℝ W)
    {K : NNReal} (hN : LipschitzWith K N)
    (hmonotone : ∀ u w, 0 ≤ (N u - N w) (u - w))
    (ell : StrongDual ℝ W) :
    ∃! u, ∀ v, B u v + N u v = ell v := by
  have hbijective :=
    bijective_semilinear_operator_of_monotone_of_lipschitzWith
      B c hc hcoercive N hN hmonotone
  obtain ⟨u, hu, hunique⟩ := hbijective.existsUnique ell
  refine ⟨u, ?_, ?_⟩
  · intro v
    exact DFunLike.congr_fun hu v
  · intro w hw
    apply hunique w
    ext v
    exact hw v

end Hilbert

/-- Coercivity and monotonicity bound the distance between two semilinear
weak solutions by the distance between their loads. -/
theorem norm_sub_le_load_sub_norm_div
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    {ell₁ ell₂ : StrongDual ℝ V} {u w : V}
    (hu : ∀ v, B u v + N u v = ell₁ v)
    (hw : ∀ v, B w v + N w v = ell₂ v)
    (hmonotone : 0 ≤ (N u - N w) (u - w)) :
    ‖u - w‖ ≤ ‖ell₁ - ell₂‖ / c := by
  have hu' : B u + N u = ell₁ := by
    ext v
    exact hu v
  have hw' : B w + N w = ell₂ := by
    ext v
    exact hw v
  simpa only [hu', hw'] using
    norm_sub_le_semilinear_operator_sub_norm_div
      B c hc hcoercive N hmonotone

/-- Coercivity dominates a semimonotone nonlinear perturbation when `L < c`;
the resulting load-to-solution stability constant is `1 / (c - L)`. -/
theorem norm_sub_le_load_sub_norm_div_of_semimonotone
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    (L : ℝ) (hLc : L < c)
    {ell₁ ell₂ : StrongDual ℝ V} {u w : V}
    (hu : ∀ v, B u v + N u v = ell₁ v)
    (hw : ∀ v, B w v + N w v = ell₂ v)
    (hsemimonotone :
      -L * ‖u - w‖ * ‖u - w‖ ≤
        (N u - N w) (u - w)) :
    ‖u - w‖ ≤ ‖ell₁ - ell₂‖ / (c - L) := by
  have hu' : B u + N u = ell₁ := by
    ext v
    exact hu v
  have hw' : B w + N w = ell₂ := by
    ext v
    exact hw v
  simpa only [hu', hw'] using
    norm_sub_le_semilinear_operator_sub_norm_div_of_semimonotone
      B c hcoercive N L hLc hsemimonotone

/-- A globally `K`-Lipschitz dual-valued map is semimonotone with loss `K`.
No sign condition is required: the dual norm controls the absolute value of
the pairing with `u - w`. -/
theorem neg_mul_norm_sq_le_apply_sub_of_lipschitzWith
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N) (u w : V) :
    -(K : ℝ) * ‖u - w‖ * ‖u - w‖ ≤
      (N u - N w) (u - w) := by
  have hpairing :
      |(N u - N w) (u - w)| ≤
        (K : ℝ) * ‖u - w‖ * ‖u - w‖ := by
    calc
      |(N u - N w) (u - w)| = ‖(N u - N w) (u - w)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖N u - N w‖ * ‖u - w‖ :=
        (N u - N w).le_opNorm (u - w)
      _ ≤ ((K : ℝ) * ‖u - w‖) * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (hN.norm_sub_le u w) (norm_nonneg _)
  calc
    -(K : ℝ) * ‖u - w‖ * ‖u - w‖ ≤
        -|(N u - N w) (u - w)| := by
      simpa only [neg_mul] using neg_le_neg hpairing
    _ ≤ (N u - N w) (u - w) := neg_abs_le _

/-- Solutions of a coercive semilinear equation with a globally Lipschitz
nonlinear load depend Lipschitz-continuously on the external load. The
remaining coercivity modulus is exactly `c - K`. -/
theorem norm_sub_le_load_sub_norm_div_of_lipschitz_lt_coercivity
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N) (hKc : (K : ℝ) < c)
    {ell₁ ell₂ : StrongDual ℝ V} {u w : V}
    (hu : ∀ v, B u v + N u v = ell₁ v)
    (hw : ∀ v, B w v + N w v = ell₂ v) :
    ‖u - w‖ ≤ ‖ell₁ - ell₂‖ / (c - K) := by
  exact norm_sub_le_load_sub_norm_div_of_semimonotone
    B c hcoercive N K hKc hu hw
      (neg_mul_norm_sq_le_apply_sub_of_lipschitzWith N hN u w)

/-- A semilinear weak solution is bounded by its load when the nonlinear
term has nonnegative pairing with the solution. -/
theorem norm_le_load_norm_div_of_nonneg
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    {ell : StrongDual ℝ V} {u : V}
    (hu : ∀ v, B u v + N u v = ell v)
    (hnonlinear : 0 ≤ N u u) :
    ‖u‖ ≤ ‖ell‖ / c := by
  apply norm_le_dual_norm_div_of_pairing ell c hc u
  calc
    c * ‖u‖ * ‖u‖ ≤ B u u := hcoercive u
    _ ≤ B u u + N u u := le_add_of_nonneg_right hnonlinear
    _ = ell u := hu u

/-- A homogeneous coercive semilinear equation has only the zero solution
when the nonlinear term pairs nonnegatively with that solution. -/
theorem eq_zero_of_coercive_of_nonneg
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V)
    {u : V}
    (hu : ∀ v, B u v + N u v = 0)
    (hnonlinear : 0 ≤ N u u) :
    u = 0 := by
  rcases hB with ⟨c, hc, hcoercive⟩
  have hnorm : ‖u‖ ≤ ‖(0 : StrongDual ℝ V)‖ / c :=
    norm_le_load_norm_div_of_nonneg
      B c hc hcoercive N (ell := 0) (by simpa using hu) hnonlinear
  exact norm_eq_zero.mp (le_antisymm (by simpa using hnorm) (norm_nonneg u))

/-- A coercive semilinear variational equation has at most one solution when
the nonlinear load is monotone between the two candidate solutions. -/
theorem eq_of_coercive_of_monotone
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V)
    {ell : StrongDual ℝ V} {u w : V}
    (hu : ∀ v, B u v + N u v = ell v)
    (hw : ∀ v, B w v + N w v = ell v)
    (hmonotone : 0 ≤ (N u - N w) (u - w)) :
    u = w := by
  rcases hB with ⟨c, hc, hcoercive⟩
  have hnorm :
      ‖u - w‖ ≤ ‖ell - ell‖ / c :=
    norm_sub_le_load_sub_norm_div
      B c hc hcoercive N hu hw hmonotone
  have hzero : ‖u - w‖ = 0 :=
    le_antisymm (by simpa using hnorm) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- A coercive semilinear variational equation has at most one solution when
the nonlinear term is semimonotone with constant below the coercivity
modulus. -/
theorem eq_of_coercive_of_semimonotone
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ)
    (hcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (N : V → StrongDual ℝ V)
    (L : ℝ) (hLc : L < c)
    {ell : StrongDual ℝ V} {u w : V}
    (hu : ∀ v, B u v + N u v = ell v)
    (hw : ∀ v, B w v + N w v = ell v)
    (hsemimonotone :
      -L * ‖u - w‖ * ‖u - w‖ ≤
        (N u - N w) (u - w)) :
    u = w := by
  have hnorm :
      ‖u - w‖ ≤ ‖ell - ell‖ / (c - L) :=
    norm_sub_le_load_sub_norm_div_of_semimonotone
      B c hcoercive N L hLc hu hw hsemimonotone
  have hzero : ‖u - w‖ = 0 :=
    le_antisymm (by simpa using hnorm) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end SobolevSpace.Weak
