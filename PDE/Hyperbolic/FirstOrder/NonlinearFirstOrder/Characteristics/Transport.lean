/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.FDeriv.Operators

/-!
# Characteristics for nonlinear first-order equations

For a fully nonlinear first-order equation `F(Du, u, x) = 0` on an open set
`U ⊆ ℝ^n`, the method of characteristics follows the triple
`(p(s), z(s), x(s)) = (Du(x(s)), u(x(s)), x(s))` along curves `x(s)` with
`ẋ = D_pF`. We set up the phase-space derivatives of `F` and prove
the two facts about that triple on which the local existence theory rests.

The operator is a function `F : ℝ^n → ℝ → ℝ^n → ℝ` of `(p, z, x)`, and
`phaseFunction F` is its uncurried form on `ℝ^n × ℝ × ℝ^n`. Differentiability of
`F` is always assumed in this joint form; the partial gradients
`momentumGradient` (`D_pF`), `positionGradient` (`D_xF`), and
`valueDerivative` (`F_z`) are then the components of its Fréchet derivative.

## Main results

* `characteristic_equations_at`: if `u ∈ C²(U)` solves `F(Du, u, x) = 0` and
  `x(s)` is differentiable with `ẋ(s) = D_pF`, then at `s` one has
  `ż = ⟪D_pF, p⟫` and `ṗ = -D_xF - F_z p`, together with `F(p, z, x) = 0`.
  This is the derivation of the characteristic ODE from a smooth solution.
* `deriv_residual_along_characteristic_eq_zero`: conversely, along any
  differentiable triple satisfying the three characteristic equations, the
  residual `F(p(s), z(s), x(s))` has zero derivative. Compatible initial data
  therefore stay on the constraint `F = 0`, which is what lets the
  characteristic flow produce a solution.
* `differentiableAt_gradient`: the gradient of a `C²` function is
  differentiable; this supplies the second derivative behind the first result.
* `contDiffOn_solution_phase`: the phase map `(Du, u, x)` of a C²
  function is C¹ on its open regularity domain. This supplies the regularity
  needed to construct spatial characteristics from a classical solution.

`characteristic_equations_at` assumes `hF : ContDiff ℝ 1` of the phase function and
`hu : ContDiffOn ℝ 2 u U`, and it is pointwise at one parameter `s`, with `hx_char` assumed
only there. The mixed partials commute by `PDE.partialDeriv_partialDeriv_comm_at`, which rests
on Mathlib's `ContDiffAt.isSymmSndFDerivAt`.

The first result is Theorem 1 of Evans, §3.2.1, with the differentiated equation (7). The
second is step 2, equations (39)-(40), of the proof of Theorem 2 in §3.2.4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.1, Theorem 1, equations (7)-(12); §3.2.4, proof of
  Theorem 2, equations (39)-(40).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (SpaceTime partialDeriv)

namespace NonlinearFirstOrder

open scoped RealInnerProductSpace Topology
open Finset

variable {n : ℕ}

/-!
## §3.2 Characteristics

Evans, §3.2.1 derives the *characteristic ODE* for a smooth solution of
`F(Du,u,x)=0`. The computation is formalized at a point, using the library's
`gradient` and `partialDeriv`.
-/

section Characteristics

variable (F : ℝ^n → ℝ → ℝ^n → ℝ)

/-- Gradient of a first-order PDE operator with respect to its momentum
variable $`p`. This is Evans's $`D_pF(p,z,x)`. -/
noncomputable def momentumGradient (p : ℝ^n) (z : ℝ) (x : ℝ^n) : ℝ^n :=
  ∇ (fun q : ℝ^n ↦ F q z x) p

/-- Gradient of a first-order PDE operator with respect to its spatial
variable $`x`. This is Evans's $`D_xF(p,z,x)`. -/
noncomputable def positionGradient (p : ℝ^n) (z : ℝ) (x : ℝ^n) : ℝ^n :=
  ∇ (fun y : ℝ^n ↦ F p z y) x

/-- Derivative of a first-order PDE operator with respect to its scalar value
variable $`z`. This is Evans's $`F_z(p,z,x)`. -/
noncomputable def valueDerivative (p : ℝ^n) (z : ℝ) (x : ℝ^n) : ℝ :=
  deriv (fun r : ℝ ↦ F p r x) z

/-- Uncurried phase-space form of a first-order PDE operator, with arguments
ordered as momentum, scalar value, and position. -/
noncomputable def phaseFunction : (ℝ^n × ℝ × ℝ^n) → ℝ :=
  fun pzx ↦ F pzx.1 pzx.2.1 pzx.2.2

/-- Hamiltonians with the same phase-space germ have the same momentum gradient.
Restriction to the momentum slice preserves the germ, so this needs no
differentiability assumption. -/
theorem momentumGradient_eq_of_phaseFunction_eventuallyEq {n : ℕ} (F G : ℝ^n → ℝ → ℝ^n → ℝ)
    (p : ℝ^n) (z : ℝ) (x : ℝ^n) (hFG : phaseFunction F =ᶠ[𝓝 (p, (z, x))] phaseFunction G) :
    momentumGradient F p z x = momentumGradient G p z x := by
  have hslice : ContinuousAt (fun q : ℝ^n ↦ (q, (z, x))) p :=
    continuousAt_id.prodMk continuousAt_const
  have heq : (fun q ↦ F q z x) =ᶠ[𝓝 p] fun q ↦ G q z x := by
    simpa only [Function.comp_def, phaseFunction] using hFG.comp_tendsto hslice
  exact heq.gradient_eq

private theorem differentiable_partialDeriv (u : ℝ^n → ℝ) (x : ℝ^n) (hu : ContDiffAt ℝ 2 u x)
    (j : Fin n) :
    DifferentiableAt ℝ (fun y ↦ (∂[j] u) y) x :=
  ((hu.fderiv_right_succ (n := 1)).differentiableAt (by simp)).clm_apply (differentiableAt_const _)

/-- A twice continuously differentiable scalar function has a differentiable Euclidean
gradient. -/
theorem differentiableAt_gradient (u : ℝ^n → ℝ) (x : ℝ^n) (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (∇ u) x :=
  (((InnerProductSpace.toDual ℝ (ℝ^n)).symm.contDiff (n := 1)).contDiffAt.differentiableAt
    one_ne_zero).comp x ((hu.fderiv_right_succ (n := 1)).differentiableAt (by simp))

private theorem fderiv_gradient_apply (u : ℝ^n → ℝ) (x : ℝ^n) (hu : ContDiffAt ℝ 2 u x)
    (i j : Fin n) :
    (fderiv ℝ (∇ u) x (EuclideanSpace.single i (1 : ℝ))) j = (∂[i] (fun y ↦ (∂[j] u) y)) x := by
  have h := congrArg (· (EuclideanSpace.single i (1 : ℝ))) ((EuclideanSpace.proj (𝕜 := ℝ) j
    ).hasFDerivAt.comp x (differentiableAt_gradient u x hu).hasFDerivAt).fderiv
  rw [show ⇑(EuclideanSpace.proj (𝕜 := ℝ) j) ∘ ∇ u = fun y ↦ (∂[j] u) y from
    funext fun y ↦ PDE.gradient_apply_eq_partialDeriv u y j] at h
  exact h.symm

private theorem fderiv_phaseFunction_apply_p (p : ℝ^n) (z : ℝ) (x : ℝ^n) (dp : ℝ^n)
    (hF : DifferentiableAt ℝ (phaseFunction (n := n) F) (p, (z, x))) :
    (fderiv ℝ (phaseFunction (n := n) F) (p, (z, x))) (dp, (0, 0)) =
      fderiv ℝ (fun q : ℝ^n ↦ F q z x) p dp :=
  (congrArg (· dp) (hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p (z, x))).fderiv).symm

private theorem fderiv_phaseFunction_apply_z (p : ℝ^n) (z : ℝ) (x : ℝ^n) (dz : ℝ)
    (hF : DifferentiableAt ℝ (phaseFunction (n := n) F) (p, (z, x))) :
    (fderiv ℝ (phaseFunction (n := n) F) (p, (z, x))) (0, (dz, 0)) =
      fderiv ℝ (fun r : ℝ ↦ F p r x) z dz :=
  (congrArg (· dz) (hF.hasFDerivAt.comp z ((hasFDerivAt_prodMk_right (𝕜 := ℝ) p (z, x)).comp z
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) z x))).fderiv).symm

private theorem fderiv_phaseFunction_apply_x (p : ℝ^n) (z : ℝ) (x : ℝ^n) (dx : ℝ^n)
    (hF : DifferentiableAt ℝ (phaseFunction (n := n) F) (p, (z, x))) :
    (fderiv ℝ (phaseFunction (n := n) F) (p, (z, x))) (0, (0, dx)) =
      fderiv ℝ (fun y : ℝ^n ↦ F p z y) x dx :=
  (congrArg (· dx) (hF.hasFDerivAt.comp x ((hasFDerivAt_prodMk_right (𝕜 := ℝ) p (z, x)).comp x
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) z x))).fderiv).symm

private theorem fderiv_phaseFunction_apply (p : ℝ^n) (z : ℝ) (x : ℝ^n) (dp : ℝ^n) (dz : ℝ)
    (dx : ℝ^n) (hF : DifferentiableAt ℝ (phaseFunction (n := n) F) (p, (z, x))) :
    (fderiv ℝ (phaseFunction (n := n) F) (p, (z, x))) (dp, (dz, dx)) =
      fderiv ℝ (fun q : ℝ^n ↦ F q z x) p dp + fderiv ℝ (fun r : ℝ ↦ F p r x) z dz +
      fderiv ℝ (fun y : ℝ^n ↦ F p z y) x dx := by
  rw [show (dp, (dz, dx)) = (dp, ((0 : ℝ), (0 : ℝ^n))) + (0, (dz, (0 : ℝ^n))) + (0, ((0 : ℝ), dx))
      by ext <;> simp, map_add, map_add, fderiv_phaseFunction_apply_p F p z x dp hF,
    fderiv_phaseFunction_apply_z F p z x dz hF, fderiv_phaseFunction_apply_x F p z x dx hF]

/-- Along a curve `x(t)` differentiable at `s`, with `u` of class `C²` near `x(s)`, the momentum
`p = Du ∘ x` satisfies `p_i'(s) = ∑_j x_j'(s) ∂_i∂_j u(x(s))`. -/
private theorem deriv_gradient_comp_apply (u : ℝ^n → ℝ) (xcurve : ℝ → ℝ^n) (s : ℝ)
    (hu : ContDiffAt ℝ 2 u (xcurve s)) (hx : DifferentiableAt ℝ xcurve s) (i : Fin n) :
    deriv (fun t ↦ ∇ u (xcurve t)) s i =
      ∑ j : Fin n, deriv xcurve s j * (∂[i] (fun y ↦ (∂[j] u) y)) (xcurve s) := by
  have hp : HasDerivAt (fun t ↦ ∇ u (xcurve t)) (deriv (fun t ↦ ∇ u (xcurve t)) s) s :=
    ((differentiableAt_gradient u (xcurve s) hu).comp s hx).hasDerivAt
  have hcoord :
      deriv (fun t ↦ ∇ u (xcurve t)) s i = deriv (fun t ↦ (∂[i] u) (xcurve t)) s := by
    simpa [Function.comp_def] using
      ((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s hp).deriv.symm
  have hchain : deriv (fun t ↦ (∂[i] u) (xcurve t)) s =
        fderiv ℝ (fun y ↦ (∂[i] u) y) (xcurve s) (deriv xcurve s) := by
    simpa only [Function.comp_def] using fderiv_comp_deriv (l := fun y ↦ (∂[i] u) y) (f := xcurve) s
        (differentiable_partialDeriv u (xcurve s) hu i) hx
  rw [hcoord, hchain, PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [mul_comm, PDE.partialDeriv_partialDeriv_comm_at j i hu]

/-- Chain rule for the residual `y ↦ F(Du(y), u(y), y)`: its derivative at `x` in the direction
`e_i` is `⟪D_pF, D(Du)(x) e_i⟫ + F_z ∂_i u(x) + (D_xF)_i`, with the partial derivatives of `F`
taken at `(Du(x), u(x), x)`. -/
private theorem fderiv_residual_apply_single (u : ℝ^n → ℝ) (x : ℝ^n)
    (hgrad : DifferentiableAt ℝ (∇ u) x) (hu : DifferentiableAt ℝ u x)
    (hF : DifferentiableAt ℝ (phaseFunction (n := n) F) (∇ u x, (u x, x))) (i : Fin n) :
    fderiv ℝ (fun y : ℝ^n ↦ F (∇ u y) (u y) y) x (EuclideanSpace.single i (1 : ℝ)) =
      ⟪momentumGradient (n := n) F (∇ u x) (u x) x,
          fderiv ℝ (∇ u) x (EuclideanSpace.single i (1 : ℝ))⟫ +
        valueDerivative (n := n) F (∇ u x) (u x) x * ∇ u x i +
          positionGradient (n := n) F (∇ u x) (u x) x i := by
  have hH : HasFDerivAt (fun y : ℝ^n ↦ (∇ u y, (u y, y)))
      ((fderiv ℝ (∇ u) x).prod ((fderiv ℝ u x).prod (ContinuousLinearMap.id ℝ (ℝ^n)))) x :=
    hgrad.hasFDerivAt.prodMk (hu.hasFDerivAt.prodMk (hasFDerivAt_id x))
  have hz : fderiv ℝ (fun r : ℝ ↦ F (∇ u x) r x) (u x)
          (fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) =
        valueDerivative (n := n) F (∇ u x) (u x) x * ∇ u x i := by
    rw [fderiv_eq_deriv_mul, PDE.fderiv_apply_single_one_eq_gradient_apply]
    rfl
  change fderiv ℝ (phaseFunction (n := n) F ∘ fun y ↦ (∇ u y, (u y, y))) x _ = _
  rw [(hF.hasFDerivAt.comp x hH).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [fderiv_phaseFunction_apply (n := n) F _ _ _ _ _ _ hF, hz, ← inner_gradient_left,
    PDE.fderiv_apply_single_one_eq_gradient_apply]
  rfl

/-- Evans, §3.2.1, equation (7): if `F(Du, u, x) = 0` near `x` and `u` is `C²` near `x`, then
`∑_j (D_pF)_j ∂_i∂_j u + F_z ∂_i u + (D_xF)_i = 0` at `(Du(x), u(x), x)`. -/
private theorem sum_momentumGradient_mul_partialDeriv_add_eq_zero (u : ℝ^n → ℝ) (x : ℝ^n)
    (hu : ContDiffAt ℝ 2 u x) (hF : DifferentiableAt ℝ (phaseFunction (n := n) F) (∇ u x, (u x, x)))
    (hpde : ∀ᶠ y in 𝓝 x, F (∇ u y) (u y) y = 0) (i : Fin n) :
    ∑ j : Fin n, momentumGradient (n := n) F (∇ u x) (u x) x j * (∂[i] (fun y ↦ (∂[j] u) y)) x +
      valueDerivative (n := n) F (∇ u x) (u x) x * ∇ u x i +
      positionGradient (n := n) F (∇ u x) (u x) x i = 0 := by
  have hzero : (fun y : ℝ^n ↦ F (∇ u y) (u y) y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := hpde
  have hinner : ⟪momentumGradient (n := n) F (∇ u x) (u x) x,
          fderiv ℝ (∇ u) x (EuclideanSpace.single i (1 : ℝ))⟫ =
        ∑ j : Fin n, momentumGradient (n := n) F (∇ u x) (u x) x j *
          (∂[i] (fun y ↦ (∂[j] u) y)) x := by
    rw [EuclideanSpace.real_inner_eq_sum]
    exact sum_congr rfl fun j _ ↦ by rw [fderiv_gradient_apply u x hu i j]
  rw [← hinner, ← fderiv_residual_apply_single F u x (differentiableAt_gradient u x hu)
    (hu.differentiableAt (by decide)) hF i, hzero.fderiv_eq]
  simp

/-- Evans, §3.2.1, Theorem 1 and equations (11): if `u ∈ C²(U)` solves
`F(Du,u,x)=0` on the open set `U` and `x(s) ∈ U`, then a characteristic
through `x(s)` satisfies the characteristic identities at `s`. -/
theorem characteristic_equations_at {U : Set (ℝ^n)} (u : ℝ^n → ℝ) (xcurve : ℝ → ℝ^n) (s : ℝ)
    (hU : IsOpen U) (hxs : xcurve s ∈ U) (hF : ContDiff ℝ 1 (phaseFunction (n := n) F))
    (hu : ContDiffOn ℝ 2 u U) (hpde : ∀ x ∈ U, F (∇ u x) (u x) x = 0)
    (hx : DifferentiableAt ℝ xcurve s)
    (hx_char : deriv xcurve s =
      momentumGradient (n := n) F (∇ u (xcurve s)) (u (xcurve s)) (xcurve s)) :
    let p : ℝ → ℝ^n := fun t ↦ ∇ u (xcurve t)
    let z : ℝ → ℝ := fun t ↦ u (xcurve t)
    (deriv z s =
        ⟪momentumGradient (n := n) F (p s) (z s) (xcurve s), p s⟫) ∧
      (deriv p s =
        -positionGradient (n := n) F (p s) (z s) (xcurve s) -
          (valueDerivative (n := n) F (p s) (z s) (xcurve s)) • p s) ∧
      F (p s) (z s) (xcurve s) = 0 := by
  dsimp only
  have huAt : ContDiffAt ℝ 2 u (xcurve s) := hu.contDiffAt (hU.mem_nhds hxs)
  refine ⟨?_, ?_, hpde (xcurve s) hxs⟩
  · -- `z' = ⟪Du, x'⟫` by the chain rule, and `x' = D_pF`.
    have hz := fderiv_comp_deriv (l := u) (f := xcurve) s (huAt.differentiableAt (by decide)) hx
    rw [Function.comp_def] at hz
    rw [hz, ← inner_gradient_left, hx_char, real_inner_comm]
  · -- `p_i' = ∑_j (D_pF)_j ∂_i∂_j u`, which Evans (7) evaluates to `-(D_xF)_i - F_z p_i`.
    ext i
    have h7 := sum_momentumGradient_mul_partialDeriv_add_eq_zero F u (xcurve s) huAt
      (hF.contDiffAt.differentiableAt (by simp)) (Filter.eventually_of_mem (hU.mem_nhds hxs) hpde) i
    rw [deriv_gradient_comp_apply u xcurve s huAt hx i, hx_char]
    simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    linarith

/-- Evans, §3.2.1: preservation of the characteristic constraint.

Along any differentiable triple `(p,z,x)` satisfying the characteristic
system

`x' = DₚF`, `z' = ⟪DₚF,p⟫`,
`p' = -DₓF - F_z p`,

the residual `F(p,z,x)` has derivative zero.  Thus compatible initial data
remain on the constraint hypersurface wherever the characteristic ODE is
defined. -/
theorem deriv_residual_along_characteristic_eq_zero (p xcurve : ℝ → ℝ^n) (z : ℝ → ℝ) (s : ℝ)
    (hF : DifferentiableAt ℝ (phaseFunction (n := n) F) (p s, (z s, xcurve s)))
    (hp : DifferentiableAt ℝ p s) (hz : DifferentiableAt ℝ z s) (hx : DifferentiableAt ℝ xcurve s)
    (hp_char : deriv p s = -positionGradient (n := n) F (p s) (z s) (xcurve s) -
      valueDerivative (n := n) F (p s) (z s) (xcurve s) • p s)
    (hz_char : deriv z s = ⟪momentumGradient (n := n) F (p s) (z s) (xcurve s), p s⟫)
    (hx_char : deriv xcurve s = momentumGradient (n := n) F (p s) (z s) (xcurve s)) :
    deriv (fun t ↦ F (p t) (z t) (xcurve t)) s = 0 := by
  have h : deriv (fun t ↦ F (p t) (z t) (xcurve t)) s = fderiv ℝ (phaseFunction (n := n) F)
      (p s, (z s, xcurve s)) (deriv p s, (deriv z s, deriv xcurve s)) :=
    ((hF.hasFDerivAt.comp_hasDerivAt s
      (hp.hasDerivAt.prodMk (hz.hasDerivAt.prodMk hx.hasDerivAt))).deriv :)
  rw [h, fderiv_phaseFunction_apply F _ _ _ _ _ _ hF, hp_char, hz_char, hx_char,
    ← inner_gradient_left (𝕜 := ℝ), fderiv_eq_deriv_mul, ← inner_gradient_left (𝕜 := ℝ)]
  change ⟪momentumGradient (n := n) F (p s) (z s) (xcurve s),
        -positionGradient (n := n) F (p s) (z s) (xcurve s) -
          valueDerivative (n := n) F (p s) (z s) (xcurve s) • p s⟫ +
      valueDerivative (n := n) F (p s) (z s) (xcurve s) *
        ⟪momentumGradient (n := n) F (p s) (z s) (xcurve s), p s⟫ +
      ⟪positionGradient (n := n) F (p s) (z s) (xcurve s),
        momentumGradient (n := n) F (p s) (z s) (xcurve s)⟫ = 0
  rw [inner_sub_right, inner_neg_right, real_inner_smul_right, real_inner_comm
    (positionGradient (n := n) F (p s) (z s) (xcurve s))]
  ring

end Characteristics

section SolutionPhase

variable {k : ℕ}

/-- The graph of a C² solution together with its gradient is a C¹ phase map. -/
theorem contDiffOn_solution_phase (u : SpaceTime k → ℝ) (Ω : Set (SpaceTime k)) (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) :
    ContDiffOn ℝ 1 (fun x ↦ (∇ u x, (u x, x))) Ω := by
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) Ω :=
    hu.fderiv_of_isOpen hΩ (by norm_num)
  have hgrad : ContDiffOn ℝ 1 (∇ u) Ω :=
    (InnerProductSpace.toDual ℝ (SpaceTime k)).symm.contDiff.comp_contDiffOn hDu
  exact hgrad.prodMk ((hu.of_le (by norm_num)).prodMk contDiffOn_id)

end SolutionPhase

end NonlinearFirstOrder
