/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Transport
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Implicit function theorem for nonlinear first-order PDE (Evans, §3.2.3, Lemma 1)

Evans’ noncharacteristic boundary lemma (§3.2.3) reduces to a standard implicit-function step:
solve a scalar equation `Φ(y,q)=0` for `q=q(y)` near a basepoint when `∂Φ/∂q ≠ 0`.

This is Mathlib's `C¹` implicit function theorem `ContDiffAt.implicitFunction`; the partial
derivative `∂Φ/∂q` is an invertible map `ℝ → ℝ` because it is nonzero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.3, Lemma 1, equations (29)-(30) and (33)-(36); §3.2.4,
  Lemma 2.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (SpaceTime)

namespace NonlinearFirstOrder

noncomputable section

open scoped Topology

section

variable {k : ℕ}

/-- Differentiating a map on `ℝ^k × ℝ` in a boundary-parameter direction at fixed
characteristic time `s` evaluates its Fréchet derivative on `(dy, 0)`. -/
theorem fderiv_boundary_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : (ℝ^k × ℝ) → G) (y : ℝ^k) (s : ℝ) (hg : DifferentiableAt ℝ g (y, s)) (dy : ℝ^k) :
    fderiv ℝ (fun η : ℝ^k ↦ g (η, s)) y dy = fderiv ℝ g (y, s) (dy, 0) :=
  congrArg (· dy) (hg.hasFDerivAt.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)).fderiv

/-- Differentiating a map on `ℝ^k × ℝ` in the characteristic-time direction at a fixed
boundary parameter `y` evaluates its Fréchet derivative on `(0, 1)`. -/
theorem deriv_time_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : (ℝ^k × ℝ) → G)
    (y : ℝ^k) (s : ℝ) (hg : DifferentiableAt ℝ g (y, s)) :
    deriv (fun τ : ℝ ↦ g (y, τ)) s = fderiv ℝ g (y, s) (0, 1) := by
  have hinsert : HasDerivAt (fun τ : ℝ ↦ (y, τ)) ((0 : ℝ^k), (1 : ℝ)) s :=
    (hasDerivAt_const (x := s) (c := y)).prodMk (hasDerivAt_id s)
  exact (hg.hasFDerivAt.comp_hasDerivAt s hinsert).deriv

end

section

variable {k : ℕ} [Fact (0 < k)]

omit [Fact (0 < k)] in
/-- Implicit-function component used in Evans, §3.2.3: solve
`Φ(y,q)=0` for one local branch `q=q(y)` near `(y0,q0)` when
`∂Φ/∂q(y0,q0) ≠ 0`. -/
theorem exists_local_implicitFunction_of_ne_partial_snd {Φ : (ℝ^k × ℝ) → ℝ} {y0 : ℝ^k} {q0 : ℝ}
    (hΦ : ContDiffAt ℝ 1 Φ (y0, q0)) (hΦ0 : Φ (y0, q0) = 0)
    (hc : (fderiv ℝ Φ (y0, q0)) ((0 : ℝ^k), (1 : ℝ)) ≠ 0) :
    ∃ W : Set ℝ^k, IsOpen W ∧ y0 ∈ W ∧ ∃ q : ℝ^k → ℝ, ContDiffAt ℝ 1 q y0 ∧
      (∀ y ∈ W, Φ (y, q y) = 0) := by
  have hinv : (fderiv ℝ Φ (y0, q0) ∘L .inr ℝ (ℝ^k) ℝ).IsInvertible :=
    ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hc), ContinuousLinearMap.ext_ring (by simp)⟩
  obtain ⟨W, hsub, hW, hy0⟩ :=
    _root_.mem_nhds_iff.mp (hΦ.eventually_apply_implicitFunction one_ne_zero hinv)
  exact ⟨W, hW, hy0, _, hΦ.contDiffAt_implicitFunction one_ne_zero hinv,
    fun y hy ↦ (hsub hy).trans hΦ0⟩

end

/-!
## Local invertibility component used in Evans, §3.2.4

Evans derives invertibility of the characteristic parametrization from the
noncharacteristic condition and then obtains unique local coordinates. The
result below is the inverse-function-theorem step: from an invertible
derivative it produces a local right inverse.
-/

section

variable {k : ℕ} [Fact (0 < k)]

/-- The derivative of Evans's characteristic parametrization at the initial
surface.

The `ℝ^k` component differentiates the boundary parametrization, while the
scalar component advances in the characteristic direction `DₚF`.  In
coordinates, this is the matrix whose first `k` columns are tangent to the
initial surface and whose final column is `DₚF`; its invertibility is Evans's
noncharacteristic condition (36). -/
noncomputable def characteristicInitialDerivative
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (y0 : ℝ^k)
    (p0 : SpaceTime k) (z0 : ℝ) : (ℝ^k × ℝ) →L[ℝ] SpaceTime k :=
  (fderiv ℝ boundary y0).comp
      (ContinuousLinearMap.fst ℝ ℝ^k ℝ) +
    ContinuousLinearMap.smulRight
      (ContinuousLinearMap.snd ℝ ℝ^k ℝ)
      (momentumGradient (n := k + 1) F p0 z0 (boundary y0))

omit [Fact (0 < k)] in
/-- The initial derivative acts on `(dy, s)` by pushing `dy` through the
boundary parametrization and adding `s` times the characteristic direction
`D_pF`. -/
@[simp]
theorem characteristicInitialDerivative_apply (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (y0 : ℝ^k) (p0 : SpaceTime k) (z0 s : ℝ) (dy : ℝ^k) :
    characteristicInitialDerivative F boundary y0 p0 z0 (dy, s) =
      fderiv ℝ boundary y0 dy + s • momentumGradient (n := k + 1) F p0 z0 (boundary y0) := by
  rfl

/-- Evans, §3.2.3: noncharacteristic condition (36).

At the initial point, the tangent directions of the parametrized boundary
together with the characteristic direction `DₚF` form an invertible linear
map onto the ambient space.  This coordinate-free formulation is equivalent
to the nonvanishing determinant in Evans after bases are chosen. -/
def IsNoncharacteristicAt
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (y0 : ℝ^k)
    (p0 : SpaceTime k) (z0 : ℝ) : Prop :=
  ∃ e : (ℝ^k × ℝ) ≃L[ℝ] SpaceTime k,
    (e : (ℝ^k × ℝ) →L[ℝ] SpaceTime k) =
      characteristicInitialDerivative F boundary y0 p0 z0

/-- Evans, §3.2.3: compatibility equations (29)-(30).

The proposed initial gradient `p0` satisfies the PDE residual at the
boundary point and its tangential components differentiate the prescribed
boundary value. -/
def IsCompatibleInitialGradientAt
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (y0 : ℝ^k) (p0 : SpaceTime k) : Prop :=
  F p0 (data y0) (boundary y0) = 0 ∧
    ∀ dy : ℝ^k,
      fderiv ℝ data y0 dy =
        (innerSL ℝ p0) (fderiv ℝ boundary y0 dy)

omit [Fact (0 < k)] in
/-- A differentiable classical solution induces Evans-compatible initial
gradient data on every differentiably parametrized boundary.

This is the necessity direction of the compatibility equations: the PDE
gives the residual equation, while the chain rule for
`data = u ∘ boundary` gives all tangential equations. -/
theorem isCompatibleInitialGradientAt_of_classical_trace (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (u : SpaceTime k → ℝ) (y0 : ℝ^k)
    (hboundary : DifferentiableAt ℝ boundary y0) (hu : DifferentiableAt ℝ u (boundary y0))
    (hdata : data =ᶠ[nhds y0] fun y ↦ u (boundary y))
    (hpde : F (∇ u (boundary y0)) (u (boundary y0)) (boundary y0) = 0) :
    IsCompatibleInitialGradientAt F boundary data y0 (∇ u (boundary y0)) := by
  refine ⟨by simpa [hdata.self_of_nhds] using hpde, fun dy ↦ ?_⟩
  rw [hdata.fderiv_eq, fderiv_fun_comp y0 hu hboundary, ContinuousLinearMap.comp_apply]
  exact (inner_gradient_left (𝕜 := ℝ) (f := u)).symm

omit [Fact (0 < k)] in
/-- Generic IFT component of Evans, §3.2.4: if `xmap : (y,s) ↦ x` is
`C^1` and its derivative at `(y0,s0)` is supplied as a continuous linear
equivalence, then there is an open neighborhood `V` of
`x0 = xmap(y0,s0)` and inverse-coordinate maps `y(x), s(x)` satisfying
`xmap (y(x), s(x)) = x`.

This statement gives `C^1` germs at the basepoint; the invertibility of the
derivative is a hypothesis. -/
theorem exists_local_inverse_coords_of_hasFDerivAt_equiv {xmap : (ℝ^k × ℝ) → SpaceTime k} {y0 : ℝ^k}
    {s0 : ℝ} (hx : ContDiffAt ℝ 1 xmap (y0, s0)) {f0' : (ℝ^k × ℝ) ≃L[ℝ] SpaceTime k}
    (hx' : HasFDerivAt xmap (f0' : (ℝ^k × ℝ) →L[ℝ] SpaceTime k) (y0, s0)) :
    ∃ V : Set (SpaceTime k), IsOpen V ∧ xmap (y0, s0) ∈ V ∧
      ∃ y : SpaceTime k → ℝ^k, ∃ s : SpaceTime k → ℝ,
        ContDiffAt ℝ 1 y (xmap (y0, s0)) ∧
        ContDiffAt ℝ 1 s (xmap (y0, s0)) ∧
        (∀ x ∈ V, xmap (y x, s x) = x) ∧
        y (xmap (y0, s0)) = y0 ∧
        s (xmap (y0, s0)) = s0 := by
  have hinv := hx.to_localInverse hx' one_ne_zero
  obtain ⟨V, hsub, hV, hxV⟩ :=
    _root_.mem_nhds_iff.mp (hx.hasStrictFDerivAt' hx' one_ne_zero).eventually_right_inverse
  have h0 := hx.localInverse_apply_image hx' one_ne_zero
  exact ⟨V, hV, hxV, fun x ↦ (hx.localInverse hx' one_ne_zero x).1,
    fun x ↦ (hx.localInverse hx' one_ne_zero x).2, contDiffAt_fst.comp _ hinv,
    contDiffAt_snd.comp _ hinv, fun x hx ↦ hsub hx, congrArg Prod.fst h0, congrArg Prod.snd h0⟩

omit [Fact (0 < k)] in
/-- Evans, §3.2.4 local-coordinate conclusion from the
noncharacteristic condition.

If a characteristic parametrization has derivative
`D boundary ⊕ DₚF` at the initial point, the noncharacteristic hypothesis
supplies the continuous linear equivalence required by the inverse function
theorem.  Hence nearby spatial points have local boundary/time coordinates.

This is the geometric inverse-coordinate step in Evans's local-existence
proof. The parametrization `xmap` and its derivative are hypotheses;
the conclusion provides local inverse coordinates. -/
theorem exists_local_inverse_coords_of_noncharacteristic (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (y0 : ℝ^k) (p0 : SpaceTime k) (z0 s0 : ℝ)
    (xmap : (ℝ^k × ℝ) → SpaceTime k) (hx : ContDiffAt ℝ 1 xmap (y0, s0))
    (hx' : HasFDerivAt xmap (characteristicInitialDerivative F boundary y0 p0 z0) (y0, s0))
    (hnonchar : IsNoncharacteristicAt F boundary y0 p0 z0) :
    ∃ V : Set (SpaceTime k), IsOpen V ∧ xmap (y0, s0) ∈ V ∧
      ∃ y : SpaceTime k → ℝ^k, ∃ s : SpaceTime k → ℝ,
        ContDiffAt ℝ 1 y (xmap (y0, s0)) ∧
        ContDiffAt ℝ 1 s (xmap (y0, s0)) ∧
        (∀ x ∈ V, xmap (y x, s x) = x) ∧
        y (xmap (y0, s0)) = y0 ∧
        s (xmap (y0, s0)) = s0 := by
  obtain ⟨e, he⟩ := hnonchar
  exact exists_local_inverse_coords_of_hasFDerivAt_equiv hx (f0' := e) (he ▸ hx')

end

end

end NonlinearFirstOrder
