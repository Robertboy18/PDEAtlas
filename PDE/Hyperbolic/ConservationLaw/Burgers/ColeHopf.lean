/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import CAS.ExactTactic
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.OpenSet

/-!
# The Cole–Hopf transform for viscous Burgers

Let `v` be a `C³`, nonvanishing solution of the one-dimensional heat equation `vₜ = νvₓₓ` on an
open spacetime domain. Then the field `u = -2νvₓ/v` is a `C²` solution of viscous Burgers
`uₜ + uuₓ = νuₓₓ` on the same domain. This is the Cole–Hopf transformation of Evans, §4.4.1(b),
with `a = ν`: Evans writes `u = wₓ`, where `w` solves (8), and the transformation (2) with
`b = 1/2` gives `w = -2ν log v`. We do not need the primitive `w`, and `v` need only be
nonvanishing.

## How it works

The proof expands the quotient-rule jets of `u`, differentiates the heat equation in space with
Clairaut's theorem at each point, and closes the resulting rational identity with the `cas`
tactic of SymLean, our computer algebra system for Lean.

Division is total in Lean, so the transform is defined for every `v`; the theorems assume `v`
nonvanishing on the domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equations (5)-(10); §4.4.1(a), equation (2).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

namespace BurgersEquation.ColeHopf

open scoped BigOperators

/-- One-dimensional viscous Burgers residual `u_t + u u_x - ν u_xx`, using coordinates
`x 0 = t`, `x 1 = x`. -/
noncomputable def viscousBurgersResidual (ν : ℝ) (u : ℝ^2 → ℝ) (xt : ℝ^2) : ℝ :=
  (∂[0] u) xt + u xt * (∂[(Fin.succ 0)] u) xt -
    ν * (∂[(Fin.succ 0)] (fun y : ℝ^2 ↦ (∂[(Fin.succ 0)] u) y)) xt

/-- A classical solution of one-dimensional viscous Burgers on a set.

Pointwise `C²` regularity is included explicitly because `partialDeriv` is totalized outside its
differentiability domain. -/
def SolvesViscousBurgersOn (ν : ℝ) (U : Set (ℝ^2)) (u : ℝ^2 → ℝ) : Prop :=
  (∀ xt ∈ U, ContDiffAt ℝ 2 u xt) ∧ ∀ xt ∈ U, viscousBurgersResidual ν u xt = 0

/-- A classical solution of `vₜ = νvₓₓ` on a set, using coordinate `0` for time and
coordinate `1` for space. Pointwise `C²` regularity rules out artifacts of totalized derivatives. -/
def SolvesHeat1DOn (ν : ℝ) (U : Set (ℝ^2)) (v : ℝ^2 → ℝ) : Prop :=
  (∀ xt ∈ U, ContDiffAt ℝ 2 v xt) ∧
    ∀ xt ∈ U, (∂[0] v) xt = ν * (∂[(Fin.succ 0)] (fun y ↦ (∂[(Fin.succ 0)] v) y)) xt

/-- The total Lean expression corresponding to the Cole–Hopf transform
`u = -2 ν (v_x / v)`. Mathematical uses should assume `v` is nonzero on the relevant domain. -/
noncomputable def coleHopfTransform (ν : ℝ) (v : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  fun xt ↦ (-2 * ν) * (∂[(Fin.succ 0)] v) xt / v xt

/-- Algebraic core of the Cole–Hopf calculation.

Here `a,b,c,d,e,f` stand respectively for `v,vₓ,vₓₓ,vₓₓₓ,vₜ,vₓₜ` at one
spacetime point.  The two hypotheses are the heat equation `vₜ = νvₓₓ` and
its spatial derivative `vₓₜ = νvₓₓₓ`.  The displayed expressions are exactly
the quotient-rule jets of `u = -2νvₓ/v`; their Burgers residual cancels, a
rational identity in `a ≠ 0` checked by `cas`.

This is the purely algebraic step. The six jet values are derived from a smooth
nonvanishing profile in `coleHopfTransform_solvesViscousBurgersOn`. -/
theorem coleHopf_jet_residual_eq_zero (ν a b c d e f : ℝ) (ha : a ≠ 0) (hheat : e = ν * c)
    (hheatx : f = ν * d) :
    let k := -2 * ν; let u := k * b / a; let ut := k * (f * a - b * e) / a ^ 2;
      let ux := k * (c * a - b ^ 2) / a ^ 2;
      let uxx := k * (((d * a - b * c) * a ^ 2) - (c * a - b ^ 2) * (2 * a * b)) / a ^ 4; ut + u *
      ux - ν * uxx = 0 := by
  dsimp
  rw [hheat, hheatx]
  cas

/-- Coordinate derivative of the Cole–Hopf transform at a nonvanishing `C²`
profile point.  This is the analytic quotient rule behind the jet identity
above and works for either the time or spatial coordinate. -/
theorem partialDeriv_coleHopfTransform (ν : ℝ) (v : ℝ^2 → ℝ) (xt : ℝ^2) (i : Fin 2)
    (hv : ContDiffAt ℝ 2 v xt) (hv0 : v xt ≠ 0) :
    (∂[i] (coleHopfTransform ν v)) xt = (-2 * ν) * ((∂[i] (fun y ↦ (∂[(Fin.succ 0)] v) y)) xt *
      v xt - (∂[(Fin.succ 0)] v) xt * (∂[i] v) xt) / (v xt) ^ 2 := by
  have hvx := (PDE.contDiffAt_partialDeriv 1 hv (Fin.succ 0)).differentiableAt one_ne_zero
  unfold coleHopfTransform
  rw [PDE.partialDeriv_div i _ v xt ((differentiableAt_const _).fun_mul hvx)
    (hv.differentiableAt two_ne_zero) hv0, PDE.partialDeriv_const_mul_fun]
  ring

/-- Second spatial derivative of the Cole–Hopf transform on an open domain.

The formula is local: `v` only needs to be `C³` and nonvanishing on a neighborhood of the point.
It is stated in quotient-rule form; the Burgers cancellation is
`coleHopf_jet_residual_eq_zero`. -/
theorem secondSpatialPartial_coleHopfTransformOn (ν : ℝ) (U : Set (ℝ^2)) (hU : IsOpen U)
    (v : ℝ^2 → ℝ) (hv : ContDiffOn ℝ 3 v U) (hv0 : ∀ y ∈ U, v y ≠ 0) (xt : ℝ^2) (hxt : xt ∈ U) :
    (∂[(Fin.succ 0)] (fun y ↦ (∂[(Fin.succ 0)] (coleHopfTransform ν v)) y)) xt =
      (-2 * ν) *
        ((((∂[(Fin.succ 0)] (fun y ↦ (∂[(Fin.succ 0)] (fun z ↦ (∂[(Fin.succ 0)] v) z)) y)) xt *
              v xt -
            (∂[(Fin.succ 0)] v) xt * (∂[(Fin.succ 0)] (fun y ↦ (∂[(Fin.succ 0)] v) y)) xt) *
            (v xt) ^ 2) -
          ((∂[(Fin.succ 0)] (fun y ↦ (∂[(Fin.succ 0)] v) y)) xt * v xt -
            ((∂[(Fin.succ 0)] v) xt) ^ 2) * (2 * v xt * (∂[(Fin.succ 0)] v) xt)) /
        (v xt) ^ 4 := by
  set i : Fin 2 := Fin.succ 0
  set vx : ℝ^2 → ℝ := fun y ↦ (∂[i] v) y
  set vxx : ℝ^2 → ℝ := fun y ↦ (∂[i] vx) y
  have hv3 : ContDiffAt ℝ 3 v xt := hv.contDiffAt (hU.mem_nhds hxt)
  have hv1 : DifferentiableAt ℝ v xt := hv3.differentiableAt (by norm_num)
  have hvx2 : ContDiffAt ℝ 2 vx xt := PDE.contDiffAt_partialDeriv 2 hv3 i
  have hvx1 : DifferentiableAt ℝ vx xt := hvx2.differentiableAt (by norm_num)
  have hvxx1 : DifferentiableAt ℝ vxx xt :=
    (PDE.contDiffAt_partialDeriv 1 hvx2 i).differentiableAt one_ne_zero
  -- Near `xt` the first spatial derivative is the quotient `-2ν (vₓₓ v - vₓ²) / v²`.
  have hux : (fun y ↦ (∂[i] (coleHopfTransform ν v)) y) =ᶠ[nhds xt]
      fun y ↦ (-2 * ν) * (vxx y * v y - vx y * vx y) / (v y * v y) := by
    filter_upwards [hU.mem_nhds hxt] with y hy
    rw [partialDeriv_coleHopfTransform ν v y i
      ((hv.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) (hv0 y hy)]
    ring
  rw [PDE.partialDeriv_congr_nhds i hux, PDE.partialDeriv_div i _ _ xt
    ((differentiableAt_const _).fun_mul ((hvxx1.fun_mul hv1).fun_sub (hvx1.fun_mul hvx1)))
    (hv1.fun_mul hv1) (mul_ne_zero (hv0 xt hxt) (hv0 xt hxt))]
  simp only [PDE.partialDeriv_const_mul_fun]
  rw [PDE.partialDeriv_sub (hvxx1.fun_mul hv1) (hvx1.fun_mul hvx1), PDE.partialDeriv_mul hvxx1 hv1,
    PDE.partialDeriv_mul hvx1 hvx1, PDE.partialDeriv_mul hv1 hv1]
  simp only [vx, vxx]
  ring

/-- Differentiating a smooth heat equation in space gives the third-order jet identity used by
Cole–Hopf. This local form only uses the equation on an open neighborhood. Clairaut's theorem
changes `∂ₓ∂ₜv` into `∂ₜ∂ₓv`. -/
theorem spatialDerivative_heatEquationOn (ν : ℝ) (U : Set (ℝ^2)) (hU : IsOpen U) (v : ℝ^2 → ℝ)
    (hv : ContDiffOn ℝ 3 v U) (hheat : SolvesHeat1DOn ν U v) (xt : ℝ^2) (hxt : xt ∈ U) :
    (∂[0] (fun y ↦ (∂[(Fin.succ 0)] v) y)) xt =
      ν * (∂[(Fin.succ 0)] (fun y ↦ (∂[(Fin.succ 0)] (fun z ↦ (∂[(Fin.succ 0)] v) z)) y)) xt := by
  rw [PDE.partialDeriv_partialDeriv_comm_at 0 (Fin.succ 0)
      ((hv.contDiffAt (hU.mem_nhds hxt)).of_le (by norm_num)),
    PDE.partialDeriv_congr_nhds _ (Filter.eventually_of_mem (hU.mem_nhds hxt) hheat.2),
    PDE.partialDeriv_const_mul_fun]

/-- The Cole–Hopf transformation of Evans, §4.4.1(b), on an arbitrary open spacetime domain.

If a `C³`, nonvanishing profile solves `vₜ = νvₓₓ` on `U`, then `u = -2νvₓ/v` solves
`uₜ + uuₓ = νuₓₓ` on `U`. The theorem uses the ordinary analytic PDE predicates; its proof factors
into local quotient rules, pointwise Clairaut commutation, and the exact jet cancellation above. -/
theorem coleHopfTransform_solvesViscousBurgersOn (ν : ℝ) (U : Set (ℝ^2)) (hU : IsOpen U)
    (v : ℝ^2 → ℝ) (hv : ContDiffOn ℝ 3 v U) (hv0 : ∀ y ∈ U, v y ≠ 0)
    (hheat : SolvesHeat1DOn ν U v) :
    SolvesViscousBurgersOn ν U (coleHopfTransform ν v) := by
  refine ⟨fun xt hxt ↦ ?_, fun xt hxt ↦ ?_⟩
  · have hv3 : ContDiffAt ℝ 3 v xt := hv.contDiffAt (hU.mem_nhds hxt)
    exact (contDiffAt_const.mul (PDE.contDiffAt_partialDeriv 2 hv3 _)).div
      (hv3.of_le (by norm_num)) (hv0 xt hxt)
  have hv2 : ContDiffAt ℝ 2 v xt := (hv.contDiffAt (hU.mem_nhds hxt)).of_le (by norm_num)
  unfold viscousBurgersResidual
  rw [partialDeriv_coleHopfTransform ν v xt 0 hv2 (hv0 xt hxt),
    partialDeriv_coleHopfTransform ν v xt _ hv2 (hv0 xt hxt),
    secondSpatialPartial_coleHopfTransformOn ν U hU v hv hv0 xt hxt]
  simpa [coleHopfTransform, pow_two] using coleHopf_jet_residual_eq_zero ν (v xt)
    ((∂[Fin.succ 0] v) xt) _ _ _ _ (hv0 xt hxt) (hheat.2 xt hxt)
    (spatialDerivative_heatEquationOn ν U hU v hv hheat xt hxt)

end BurgersEquation.ColeHopf
