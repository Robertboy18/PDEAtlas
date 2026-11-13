/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# One-dimensional systems of conservation laws

Pointwise definitions and identities for the system

`u_t + (f(u))_x = 0`,

where `u` and the flux `f` take values in a finite-dimensional real
Euclidean space:

* flux and quasilinear residuals, together with their chain-rule equivalence;
* classical solutions on a set;
* hyperbolicity, strict hyperbolicity, and the symmetric-Jacobian criterion;
* the vector Rankine–Hugoniot condition and uniqueness of shock speed;
* entropy pairs for systems and the classical entropy identity.

The Jacobian is Mathlib's `fderiv`, with no intermediate matrix encoding.

The Rankine–Hugoniot condition is (20) of Evans, §11.1.1, written with right-minus-left
jumps; Evans writes `[[u]] = u_l - u_r`, which gives the same condition. Strict hyperbolicity
is the definition of §11.1.2. The compatibility condition of an entropy pair is (26) of
§11.4.2, and the classical entropy identity is the computation (27); Evans also requires the
convexity (25), which we record separately in `ConvexEntropyPair`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equation (20); §11.1.2, definition of strict
  hyperbolicity; §11.4.2, definition of entropy/entropy-flux pair, equations (25)-(27).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace PDE.Hyperbolic.ConservationLaw.System


variable {m : ℕ}

/-! ## Flux and quasilinear forms -/

/-- The flux-form residual `u_t + (f(u))_x`. -/
def fluxResidual
    (flux : ℝ^m → ℝ^m) (u : ℝ^2 → ℝ^m)
    (p : ℝ^2) : ℝ^m :=
  (∂[0] u) p + (∂[1] (flux ∘ u)) p

/-- The quasilinear residual `u_t + Df(u)u_x`. -/
def quasilinearResidual
    (flux : ℝ^m → ℝ^m) (u : ℝ^2 → ℝ^m)
    (p : ℝ^2) : ℝ^m :=
  (∂[0] u) p + fderiv ℝ flux (u p) ((∂[1] u) p)

/-- For differentiable data, the flux and quasilinear residuals agree. -/
theorem fluxResidual_eq_quasilinearResidual {flux : ℝ^m → ℝ^m} {u : ℝ^2 → ℝ^m} {p : ℝ^2}
    (hflux : DifferentiableAt ℝ flux (u p)) (hu : DifferentiableAt ℝ u p) :
  fluxResidual flux u p = quasilinearResidual flux u p := by
  rw [fluxResidual, quasilinearResidual]
  unfold partialDeriv
  rw [fderiv_comp p hflux hu]
  rfl

/-- A classical solution of a system conservation law on a set. -/
structure IsClassicalSolutionOn
    (flux : ℝ^m → ℝ^m) (U : Set ℝ^2)
    (u : ℝ^2 → ℝ^m) : Prop where
  /-- Pointwise differentiability of the state. -/
  differentiableAt : ∀ p ∈ U, DifferentiableAt ℝ u p
  /-- Pointwise differentiability of the flux at states attained by the solution. -/
  flux_differentiableAt : ∀ p ∈ U, DifferentiableAt ℝ flux (u p)
  /-- Vanishing of the conservative residual. -/
  residual_eq_zero : ∀ p ∈ U, fluxResidual flux u p = 0

/-- A classical conservative solution also satisfies the quasilinear equation. -/
theorem IsClassicalSolutionOn.quasilinearResidual_eq_zero {flux : ℝ^m → ℝ^m} {U : Set ℝ^2}
    {u : ℝ^2 → ℝ^m} (hu : IsClassicalSolutionOn flux U u) {p : ℝ^2} (hp : p ∈ U) :
    quasilinearResidual flux u p = 0 := by
  rw [← fluxResidual_eq_quasilinearResidual
    (hu.flux_differentiableAt p hp) (hu.differentiableAt p hp)]
  exact hu.residual_eq_zero p hp

/-! ## Hyperbolicity -/

/-- The flux is hyperbolic at a state when it is differentiable there and
its Jacobian has a real eigenbasis. -/
def IsHyperbolicAt (flux : ℝ^m → ℝ^m) (state : ℝ^m) : Prop :=
  DifferentiableAt ℝ flux state ∧ ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∃ speed : Fin m → ℝ,
      ∀ k, Module.End.HasEigenvector (fderiv ℝ flux state).toLinearMap (speed k) (b k)

/-- The flux is strictly hyperbolic at a state when its characteristic
speeds are pairwise distinct. By differentiability, `fderiv ℝ flux state` is the
Jacobian of the flux at the state. -/
def IsStrictlyHyperbolicAt
    (flux : ℝ^m → ℝ^m) (state : ℝ^m) : Prop :=
  DifferentiableAt ℝ flux state ∧ ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∃ speed : Fin m → ℝ,
      Function.Injective speed ∧ ∀ k, Module.End.HasEigenvector
          (fderiv ℝ flux state).toLinearMap (speed k) (b k)

/-- Hyperbolicity at every state in a set. -/
def IsHyperbolicOn (flux : ℝ^m → ℝ^m) (states : Set (ℝ^m)) : Prop :=
  ∀ state ∈ states, IsHyperbolicAt flux state

/-- Strict hyperbolicity at every state in a set. -/
def IsStrictlyHyperbolicOn
    (flux : ℝ^m → ℝ^m) (states : Set (ℝ^m)) : Prop :=
  ∀ state ∈ states, IsStrictlyHyperbolicAt flux state

/-- Strict hyperbolicity implies hyperbolicity at the same state. -/
theorem IsStrictlyHyperbolicAt.isHyperbolicAt {flux : ℝ^m → ℝ^m} {state : ℝ^m}
    (h : IsStrictlyHyperbolicAt flux state) :
    IsHyperbolicAt flux state := by
  rcases h with ⟨hflux, b, speed, _, heigen⟩
  exact ⟨hflux, b, speed, heigen⟩

/-- Strict hyperbolicity on a set implies hyperbolicity there. -/
theorem IsStrictlyHyperbolicOn.isHyperbolicOn {flux : ℝ^m → ℝ^m} {states : Set (ℝ^m)}
    (h : IsStrictlyHyperbolicOn flux states) :
    IsHyperbolicOn flux states :=
  fun state hstate ↦ (h state hstate).isHyperbolicAt

/-- The flux is differentiable at a state and its Jacobian is symmetric. -/
def IsSymmetricAt (flux : ℝ^m → ℝ^m) (state : ℝ^m) : Prop :=
  DifferentiableAt ℝ flux state ∧ (fderiv ℝ flux state : ℝ^m →ₗ[ℝ] ℝ^m).IsSymmetric

/-- The flux Jacobian is symmetric at every state in a set. -/
def IsSymmetricOn (flux : ℝ^m → ℝ^m) (states : Set (ℝ^m)) : Prop :=
  ∀ state ∈ states, IsSymmetricAt flux state

/-- A symmetric flux Jacobian is hyperbolic by the finite-dimensional
real spectral theorem. -/
theorem IsSymmetricAt.isHyperbolicAt {flux : ℝ^m → ℝ^m} {state : ℝ^m}
    (h : IsSymmetricAt flux state) :
    IsHyperbolicAt flux state := by
  have hrank : Module.finrank ℝ (ℝ^m) = m := by
    simp
  exact ⟨h.1, (h.2.eigenvectorBasis hrank).toBasis,
      h.2.eigenvalues hrank, h.2.hasEigenvector_eigenvectorBasis hrank⟩

/-- A symmetric flux is hyperbolic on the same set of states. -/
theorem IsSymmetricOn.isHyperbolicOn {flux : ℝ^m → ℝ^m} {states : Set (ℝ^m)}
    (h : IsSymmetricOn flux states) :
    IsHyperbolicOn flux states :=
  fun state hstate ↦ (h state hstate).isHyperbolicAt

/-! ## Discontinuities -/

/-- Vector Rankine–Hugoniot condition
`f(uR) - f(uL) = s (uR - uL)`, with right-minus-left jumps. -/
def RankineHugoniot
    (flux : ℝ^m → ℝ^m) (uL uR : ℝ^m) (speed : ℝ) : Prop :=
  flux uR - flux uL = speed • (uR - uL)

/-- A nonzero jump has at most one Rankine–Hugoniot speed. -/
theorem RankineHugoniot.unique_speed {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {s₁ s₂ : ℝ} (hjump : uR ≠ uL)
    (h₁ : RankineHugoniot flux uL uR s₁) (h₂ : RankineHugoniot flux uL uR s₂) :
    s₁ = s₂ :=
  smul_left_injective ℝ (sub_ne_zero.mpr hjump) (h₁.symm.trans h₂)

/-! ## Entropy pairs -/

/-- A `C¹` compatible entropy and entropy-flux pair for a system flux.

The compatibility relation is `Dq = Dη ∘ Df`; convexity is recorded
separately by `ConvexEntropyPair`. -/
structure EntropyPair (flux : ℝ^m → ℝ^m) where
  /-- The flux is differentiable, so `fderiv ℝ flux` is its Jacobian at every state. -/
  flux_differentiable : Differentiable ℝ flux
  /-- Scalar entropy. -/
  entropy : ℝ^m → ℝ
  /-- Scalar entropy flux. -/
  entropyFlux : ℝ^m → ℝ
  /-- Regularity of the entropy. -/
  entropy_contDiff : ContDiff ℝ 1 entropy
  /-- Regularity of the entropy flux. -/
  entropyFlux_contDiff : ContDiff ℝ 1 entropyFlux
  /-- Compatibility of the two differentials with the system Jacobian. -/
  compatibility : ∀ state,
    fderiv ℝ entropyFlux state =
      (fderiv ℝ entropy state).comp (fderiv ℝ flux state)

/-- An entropy pair whose entropy is convex on the whole state space. -/
structure ConvexEntropyPair (flux : ℝ^m → ℝ^m)
    extends EntropyPair flux where
  /-- Convexity of the entropy, used to select dissipative weak solutions. -/
  entropy_convex : ConvexOn ℝ Set.univ entropy

/-- A discontinuity is admissible for an entropy pair when it satisfies
Rankine–Hugoniot and its distributional entropy production
`[q] - s[η]` is nonpositive. -/
def EntropyPair.IsAdmissibleShock
    {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (uL uR : ℝ^m) (speed : ℝ) : Prop :=
  RankineHugoniot flux uL uR speed ∧ E.entropyFlux uR - E.entropyFlux uL ≤
      speed * (E.entropy uR - E.entropy uL)

/-- Pointwise form of entropy-pair compatibility. -/
theorem EntropyPair.fderiv_entropyFlux_apply {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (state direction : ℝ^m) :
    fderiv ℝ E.entropyFlux state direction =
      fderiv ℝ E.entropy state (fderiv ℝ flux state direction) := by
  rw [E.compatibility state]
  rfl

/-- The entropy residual `∂t η(u) + ∂x q(u)`. -/
def entropyResidual
    {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (u : ℝ^2 → ℝ^m) (p : ℝ^2) : ℝ :=
  (∂[0] (E.entropy ∘ u)) p + (∂[1] (E.entropyFlux ∘ u)) p

/-- The entropy differential applied to the quasilinear residual is the
entropy residual, even when the equation has a nonzero right-hand side. -/
theorem EntropyPair.entropyResidual_eq_fderiv_quasilinearResidual {flux : ℝ^m → ℝ^m}
    (E : EntropyPair flux) {u : ℝ^2 → ℝ^m} {p : ℝ^2} (hu : DifferentiableAt ℝ u p) :
    entropyResidual E u p = fderiv ℝ E.entropy (u p) (quasilinearResidual flux u p) := by
  have hEntropy := E.entropy_contDiff.differentiable_one (u p)
  have hEntropyFlux := E.entropyFlux_contDiff.differentiable_one (u p)
  unfold entropyResidual partialDeriv quasilinearResidual
  rw [fderiv_comp p hEntropy hu, ContinuousLinearMap.comp_apply,
    fderiv_comp p hEntropyFlux hu, ContinuousLinearMap.comp_apply,
    E.fderiv_entropyFlux_apply, map_add]
  rfl

/-- A differentiable quasilinear solution satisfies the entropy identity
for every compatible entropy pair. -/
theorem EntropyPair.entropyResidual_eq_zero_of_quasilinear {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    {u : ℝ^2 → ℝ^m} {p : ℝ^2} (hu : DifferentiableAt ℝ u p)
    (hpde : quasilinearResidual flux u p = 0) :
    entropyResidual E u p = 0 := by
  rw [E.entropyResidual_eq_fderiv_quasilinearResidual hu, hpde, map_zero]

/-- A differentiable flux-form solution satisfies the entropy identity. -/
theorem EntropyPair.entropyResidual_eq_zero_of_flux {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    {u : ℝ^2 → ℝ^m} {p : ℝ^2} (hu : DifferentiableAt ℝ u p) (hpde : fluxResidual flux u p = 0) :
    entropyResidual E u p = 0 := by
  apply E.entropyResidual_eq_zero_of_quasilinear hu
  rwa [← fluxResidual_eq_quasilinearResidual (E.flux_differentiable (u p)) hu]

end PDE.Hyperbolic.ConservationLaw.System
