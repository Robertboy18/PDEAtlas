/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Parity
public import PDE.Hyperbolic.Classical.MovingBallTransport
public import PDE.Hyperbolic.Models.Wave.DAlembert.ClassicalSolution
public import PDE.Analysis.Calculus.Radial.WeightedDerivative
import PDE.FDeriv.SpaceTime

/-!
# Analytic tools for the odd-dimensional wave representation

The odd-dimensional reduction of Evans, §2.4.1(d), produces a classical one-dimensional wave
with assigned Cauchy data. Two analytic tools identify that wave with the
d'Alembert solution:

* commutation of the radial transform (28) of Evans with time differentiation, under
  explicit joint regularity of its intermediate transforms;
* global uniqueness for the one-dimensional assigned-Cauchy-data problem.

The initial-value problem records the wave residual only for positive time.
For a `C²` field, continuity of the second derivatives first extends the
residual to the initial slice. The moving-ball energy theorem then gives
global uniqueness for nonnegative time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(d), equations (28)-(29) and Lemma 3; §2.4.3,
  Theorem 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SatisfiesPDEProblem)

noncomputable section

namespace WaveEquation

open Filter PDE.Analysis PDE.Common Set
open scoped Topology

variable {n : ℕ}

private theorem equivOfUnique_symm_eq_single (r : ℝ) :
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm r = EuclideanSpace.single (0 : Fin 1) r := by
  ext i
  fin_cases i
  simp

private theorem toLp_uniqueElim_eq_single (r : ℝ) :
    WithLp.toLp 2 (uniqueElim (ι := Fin 1) r) = EuclideanSpace.single (0 : Fin 1) r := by
  ext i
  fin_cases i
  simp

/-- The spatial coordinate of `(t, r)` in one-dimensional spacetime is `r`. -/
@[local simp]
theorem timeSpaceCons_single_one (t r : ℝ) :
    timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r) (1 : Fin 2) = r := by
  simpa using timeSpaceCons_succ t (EuclideanSpace.single (0 : Fin 1) r) (0 : Fin 1)

/-- Mixed ordinary derivatives of a jointly `C²` field commute when the first
variable is time and the second is a one-dimensional radius. -/
private theorem deriv_deriv_time_radius_comm (F : ℝ^2 → ℝ) (hF : ContDiff ℝ 2 F) (t r : ℝ) :
    deriv (fun q ↦
        deriv (fun s ↦ F (timeSpaceCons q (EuclideanSpace.single (0 : Fin 1) s))) r) t =
      deriv (fun s ↦
        deriv (fun q ↦ F (timeSpaceCons q (EuclideanSpace.single (0 : Fin 1) s))) t) r := by
  let G : ℝ^1 × ℝ → ℝ := fun p ↦ F (joinSpaceTime p)
  have hG : ContDiff ℝ 2 G := (contDiff_comp_joinSpaceTime_iff (m := 2) F).2 hF
  have hspace (q : ℝ) :
      deriv (fun s ↦ F (timeSpaceCons q (EuclideanSpace.single (0 : Fin 1) s))) r =
        (∂[(0 : Fin 1)] (fun y ↦ G (y, q))) (EuclideanSpace.single (0 : Fin 1) r) := by
    simpa [G, Function.comp_def, joinSpaceTime, equivOfUnique_symm_eq_single,
      toLp_uniqueElim_eq_single] using PDE.deriv_comp_equivOfUnique_symm
        (fun y : ℝ^1 ↦ G (y, q)) r (((hG.of_le (by norm_num)).comp
          (contDiff_id.prodMk contDiff_const)).differentiable_one.differentiableAt)
  have hright :
      deriv (fun s ↦
          deriv (fun q ↦ F (timeSpaceCons q (EuclideanSpace.single (0 : Fin 1) s))) t) r =
        (∂[(0 : Fin 1)] (fun y : ℝ^1 ↦ deriv (fun q ↦ G (y, q)) t))
          (EuclideanSpace.single (0 : Fin 1) r) := by
    simpa [G, Function.comp_def, joinSpaceTime, equivOfUnique_symm_eq_single,
      toLp_uniqueElim_eq_single] using PDE.deriv_comp_equivOfUnique_symm
        (fun y : ℝ^1 ↦ deriv (fun q ↦ G (y, q)) t) r
        (PDE.contDiff_deriv_prod_timeSlice G t hG).differentiable_one.differentiableAt
  rw [funext hspace, PDE.deriv_partialDeriv_timeSlice_comm (0 : Fin 1) G
    (EuclideanSpace.single (0 : Fin 1) r) t hG]
  exact hright.symm

/-- Away from the center, a finite Evans radial transform commutes with one
time derivative.

The regularity assumption concerns the intermediate transforms. It encodes the removable-singularity
statement at `r = 0`. -/
theorem deriv_oddRadialTransform_time_of_ne (m : ℕ) (φ : ℝ → ℝ → ℝ)
    (hregular : ∀ k ≤ m, ContDiff ℝ 2 (fun p : ℝ^2 ↦ oddRadialTransform k (φ (p 0)) (p 1))) (t : ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    deriv (fun q ↦ oddRadialTransform m (φ q) r) t =
      oddRadialTransform m (fun s ↦ deriv (fun q ↦ φ q s) t) r := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
    have htime : (fun s ↦ deriv (fun q ↦ oddRadialTransform m (φ q) s) t) =ᶠ[𝓝 r]
        fun s ↦ oddRadialTransform m (fun a ↦ deriv (fun q ↦ φ q a) t) s := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hr)] with s hs
      exact ih (r := s) (fun k hk ↦ hregular k (hk.trans (Nat.le_succ m))) (by simpa using hs)
    rw [show (fun q ↦ oddRadialTransform (m + 1) (φ q) r) =
        fun q ↦ evansRadialDerivative (oddRadialTransform m (φ q)) r from
          funext fun q ↦ by rw [oddRadialTransform_succ'], oddRadialTransform_succ']
    simp only [evansRadialDerivative]
    rw [deriv_div_const, ← htime.deriv_eq]
    simpa using congrArg (· / r) (deriv_deriv_time_radius_comm
      (fun p : ℝ^2 ↦ oddRadialTransform m (φ (p 0)) (p 1)) (hregular m (Nat.le_succ m)) t r)

/-- Commutation with one time derivative also holds at the center, where every
transform of positive order takes the value `0`. -/
theorem deriv_oddRadialTransform_time (m : ℕ) (φ : ℝ → ℝ → ℝ)
    (hregular : ∀ k ≤ m, ContDiff ℝ 2 (fun p : ℝ^2 ↦ oddRadialTransform k (φ (p 0)) (p 1)))
    (t r : ℝ) :
    deriv (fun q ↦ oddRadialTransform m (φ q) r) t =
      oddRadialTransform m (fun s ↦ deriv (fun q ↦ φ q s) t) r := by
  by_cases hr : r = 0
  · subst r
    cases m with
    | zero => rfl
    | succ k =>
      have h0 (g : ℝ → ℝ) : oddRadialTransform (k + 1) g 0 = 0 := by
        rw [oddRadialTransform_succ']
        simp [evansRadialDerivative]
      rw [show (fun q ↦ oddRadialTransform (k + 1) (φ q) 0) = fun _ ↦ 0 from
        funext fun q ↦ h0 _, deriv_const, h0]
  · exact deriv_oddRadialTransform_time_of_ne m φ hregular t hr

/-- For radial profiles whose intermediate Evans transforms are jointly `C³`, the transform
commutes with two time derivatives. -/
theorem deriv_deriv_oddRadialTransform_time (m : ℕ) (φ : ℝ → ℝ → ℝ)
    (hregular : ∀ k ≤ m, ContDiff ℝ 3 (fun p : ℝ^2 ↦ oddRadialTransform k (φ (p 0)) (p 1)))
    (t r : ℝ) :
    deriv (deriv (fun q ↦ oddRadialTransform m (φ q) r)) t =
      oddRadialTransform m (fun s ↦ deriv (deriv (fun q ↦ φ q s)) t) r := by
  let φt : ℝ → ℝ → ℝ := fun q s ↦ deriv (fun a ↦ φ a s) q
  have hregular_two : ∀ k ≤ m, ContDiff ℝ 2 (fun p : ℝ^2 ↦ oddRadialTransform k (φ (p 0)) (p 1)) :=
    fun k hk ↦ (hregular k hk).of_le (by norm_num)
  have hregular_t : ∀ k ≤ m,
      ContDiff ℝ 2 (fun p : ℝ^2 ↦ oddRadialTransform k (φt (p 0)) (p 1)) := by
    intro k hk
    let Wk : ℝ^2 → ℝ := fun p ↦ oddRadialTransform k (φ (p 0)) (p 1)
    have hWk : ContDiff ℝ 3 Wk := hregular k hk
    have hfield : (fun p : ℝ^2 ↦ oddRadialTransform k (φt (p 0)) (p 1)) =
        fun p ↦ (∂[(0 : Fin 2)] Wk) p := by
      funext p
      let y : ℝ^1 := EuclideanSpace.single (0 : Fin 1) (p 1)
      have hp : timeSpaceCons (p 0) y = p := by
        ext i
        cases i using Fin.cases with
        | zero => simp
        | succ i =>
          fin_cases i
          simp [y]
      have htime := PDE.partialDeriv_timeSpaceCons_eq_deriv Wk y (p 0)
        ((hWk.differentiable (by norm_num)).differentiableAt)
      rw [hp] at htime
      exact (deriv_oddRadialTransform_time k φ (fun j hj ↦ hregular_two j (hj.trans hk))
        (p 0) (p 1)).symm.trans htime.symm
    rw [hfield]
    exact PDE.contDiff_partialDeriv_of_succ (m := 2) (i := (0 : Fin 2)) hWk
  rw [funext fun q ↦ deriv_oddRadialTransform_time m φ hregular_two q r]
  simpa only [φt] using deriv_oddRadialTransform_time m φt hregular_t t r

private theorem partialDeriv_one_timeSpaceCons_single_eq_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ^2 → E) (hF : ContDiff ℝ 1 F) (t r : ℝ) :
    (∂[(1 : Fin 2)] F) (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) =
      deriv (fun s ↦ F (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) s))) r := by
  let slice : ℝ^1 → E := fun y ↦ F (timeSpaceCons t y)
  have hslice : ContDiff ℝ 1 slice := hF.comp (contDiff_timeSpaceCons_spatial 1 t)
  refine (PDE.partialDeriv_timeSpaceCons_spatial (0 : Fin 1) F t
    (EuclideanSpace.single (0 : Fin 1) r)
    ((hF.differentiable one_ne_zero).differentiableAt)).symm.trans ?_
  simpa [slice, Function.comp_def, equivOfUnique_symm_eq_single, toLp_uniqueElim_eq_single] using
    (PDE.deriv_comp_equivOfUnique_symm slice r hslice.differentiable_one.differentiableAt).symm

/-- In one space dimension, the spacetime wave operator is the ordinary
second time derivative minus the ordinary second radius derivative. -/
theorem waveOperator_one_timeSpaceCons_single (F : ℝ^2 → ℝ) (hF : ContDiff ℝ 2 F) (t r : ℝ) :
    waveOperator (n := 1) F (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) =
      deriv (deriv (fun q ↦ F (timeSpaceCons q (EuclideanSpace.single (0 : Fin 1) r)))) t -
        deriv (deriv (fun s ↦ F (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) s)))) r := by
  let y : ℝ^1 := EuclideanSpace.single (0 : Fin 1) r
  have hFone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have htime : (∂[(0 : Fin 2)] (fun p ↦ (∂[(0 : Fin 2)] F) p)) (timeSpaceCons t y) =
      deriv (deriv (fun q ↦ F (timeSpaceCons q y))) t := by
    rw [PDE.partialDeriv_timeSpaceCons_eq_deriv (fun p ↦ (∂[(0 : Fin 2)] F) p) y t
      (((PDE.contDiff_partialDeriv_of_succ (m := 1) (i := (0 : Fin 2)) hF).differentiable
        one_ne_zero).differentiableAt)]
    exact congrArg (deriv · t) (funext fun q ↦ PDE.partialDeriv_timeSpaceCons_eq_deriv F y q
      ((hFone.differentiable one_ne_zero).differentiableAt))
  have hspace : (∂[(1 : Fin 2)] (fun p ↦ (∂[(1 : Fin 2)] F) p)) (timeSpaceCons t y) =
      deriv (deriv (fun s ↦ F (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) s)))) r := by
    rw [partialDeriv_one_timeSpaceCons_single_eq_deriv (fun p ↦ (∂[(1 : Fin 2)] F) p)
      (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := (1 : Fin 2)) hF) t r]
    exact congrArg (deriv · r) (funext fun s ↦
      partialDeriv_one_timeSpaceCons_single_eq_deriv F hFone t s)
  simp only [waveOperator, Fin.sum_univ_one]
  change (∂[(0 : Fin 2)] (fun p ↦ (∂[(0 : Fin 2)] F) p)) (timeSpaceCons t y) -
      (∂[(1 : Fin 2)] (fun p ↦ (∂[(1 : Fin 2)] F) p)) (timeSpaceCons t y) = _
  rw [htime, hspace]

section OneDimension

/-- Every classical one-dimensional solution of the assigned Cauchy problem
is the d'Alembert solution at nonnegative times. -/
theorem eq_dAlembertSolution1D_of_satisfiesResidualAssignedCauchyData {g h : ℝ^1 → ℝ} {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 2 (fun r : ℝ ↦ g (EuclideanSpace.single (0 : Fin 1) r)))
    (hh : ContDiff ℝ 1 (fun r : ℝ ↦ h (EuclideanSpace.single (0 : Fin 1) r)))
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 1) g h) u) {t : ℝ}
    (ht : 0 ≤ t) (x : ℝ^1) :
    u (timeSpaceCons t x) = dAlembertSolution1D g h (timeSpaceCons t x) :=
  eq_on_nonnegative_time_of_satisfiesResidualAssignedCauchyData hu
    (contDiff_two_dAlembertSolution1D g h hg hh) hsol
    (dAlembertSolution1D_satisfiesResidualAssignedCauchyData g h hg hh) ht x

end OneDimension

end WaveEquation
