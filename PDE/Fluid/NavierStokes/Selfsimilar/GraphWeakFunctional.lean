/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphWeakForm

/-!
# Testing the linearization with fields of the graph domain

Let `v` be a field of `H¹(ℝⁿ)ⁿ` in the graph domain of a dilation test space, so that the drift
`φ ↦ ∫ (x·∇v)·φ` extends to a continuous functional on the closed span of the test fields. This
module moves the drift from one field of the graph domain to another. For `h`, `k` in the graph
domain, `⟨x·∇h, k⟩ + ⟨x·∇k, h⟩ = -n ⟨h, k⟩`, with no weight on either field. So the linearization
of `h` tested with `k` is its bounded part, plus half the drift of `k` tested with `h`, plus
`(n/2) ⟨h, k⟩`, and this is continuous in `h` for the `H¹` norm. All statements hold for every
dilation test space and every coefficient `b` with bounded components. Whether the test fields
are dense in the graph domain for the graph norm is not stated. None of the results needs it.

In three dimensions, a field whose weak eigenvalue density integrates to `ℓ(φ)` against every
test field `φ`, for a continuous functional `ℓ`, lies in the graph domain and satisfies
`L v + μ J v = ℓ` (`DilationTestSpace.mem_graphDomain_of_weakEigen_eq`,
`DilationTestSpace.linearization_eq_of_weakEigen_eq`). With the results here such an equation
can be paired with a field that is not compactly supported, for example an approximate
eigenfunction, as in the proof of Proposition 2 of Hou, Wang and Yang.

## Main results

* `DilationTestSpace.dilationDrift_apply_add_swap`: `⟨x·∇h, k⟩ + ⟨x·∇k, h⟩ = -n ⟨h, k⟩` for `h`,
  `k` in the graph domain.
* `DilationTestSpace.linearization_apply_eq_adjoint`:
  `⟨L h, k⟩ = B(h, k) + ½ ⟨x·∇k, h⟩ + (n/2) ⟨h, k⟩`, with `B` the bounded part.
* `DilationTestSpace.linearization_apply_eq_of_adjoint_tests`: if a continuous functional `g`
  is the adjoint linearization of `k` on the test fields, without the mass terms, then
  `⟨L h, k⟩ = g(h) + ((n - 1)/2) ⟨h, k⟩`.
* `DilationTestSpace.exists_linearization_apply_eq_of_weakEigen_eq`: in three dimensions, a
  field of the closed span whose weak eigenvalue density integrates to `ℓ(φ)` against every
  test field satisfies `⟨L v, w⟩ + μ ⟨v, w⟩ = ℓ(w)` for every `w` of the closed span.

## How it works

On the graph domain the drift satisfies `⟨x·∇h, h⟩ = -(n/2) ‖h‖₂²`
(`DilationTestSpace.dilationDrift_self`). Applied to `h + k`, `h` and `k`, this gives the
identity for two fields by polarization. The other statements rewrite the drift term of the
linearization with it.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.4, the proof of
  Proposition 2. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary
open PDE.Analysis.Evolution (restrictForm restrictForm_apply)

set_option linter.missingDocs true

namespace DilationTestSpace

section Drift

variable {n : ℕ} (T : DilationTestSpace n)

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- **The dilation identity for two fields.** For `h`, `k` in the graph domain,
`⟨x·∇h, k⟩ + ⟨x·∇k, h⟩ = -n ⟨h, k⟩`, where `⟨x·∇h, ·⟩` is the dilation drift of `h` and
`⟨h, k⟩` the `L²` pairing. This is integration by parts for the drift, with no weight on
either field. It is `dilationDrift_self` applied to `h + k`, `h` and `k`. -/
theorem dilationDrift_apply_add_swap (h k : T.graphDomain) :
    T.dilationDrift h (k : T.space) + T.dilationDrift k (h : T.space) =
      -(n : ℝ) * massPairing ((h : T.space) : H) ((k : T.space) : H) := by
  have hs := T.dilationDrift_self (h + k)
  have hh := T.dilationDrift_self h
  have hk := T.dilationDrift_self k
  have hc := massPairing_comm ((k : T.space) : H) ((h : T.space) : H)
  rw [← massForm_apply] at hs hh hk
  rw [← massForm_apply, ← massForm_apply] at hc
  rw [← massForm_apply]
  simp only [map_add, Submodule.coe_add, add_apply] at hs
  linear_combination hs - hh - hk - (n : ℝ) / 2 * hc

/-- **The linearization tested with a field of the graph domain.** For a coefficient `b` with
bounded components and `h`, `k` in the graph domain,

`⟨L h, k⟩ = B(h, k) + ½ ⟨x·∇k, h⟩ + (n/2) ⟨h, k⟩`,

with `B` the bounded part of the linearization. The drift of `h` has moved to `k`
(`dilationDrift_apply_add_swap`), so the right side is continuous in `h` for the `H¹` norm. -/
theorem linearization_apply_eq_adjoint (b : Fin n → DerivLp n ∞ univ) (h k : T.graphDomain) :
    T.linearization b h (k : T.space) =
      boundedPart b ((h : T.space) : H) ((k : T.space) : H) +
        1 / 2 * T.dilationDrift k (h : T.space) +
        (n : ℝ) / 2 * massPairing ((h : T.space) : H) ((k : T.space) : H) := by
  have hswap := T.dilationDrift_apply_add_swap h k
  rw [linearization_apply, sub_apply, smul_apply, restrictForm_apply, smul_eq_mul]
  linear_combination (-1 / 2 : ℝ) * hswap

/-- **The linearization tested with `k`, from the adjoint of `k` on the test fields.** Let `k`
be in the graph domain and let `g` be a continuous linear functional on the closed span with

`∫ ∇φ : ∇k + ∫ ((b·∇)φ + (φ·∇)b)·k + ½ ∫ (x·∇k)·φ = g(φ)`

for every test field `φ`: in the sense of distributions, `g` is
`-Δk - (b·∇)k + (∇b)ᵀ k + ½ x·∇k`. Then for every `h` in the graph domain

`⟨L h, k⟩ = g(h) + ((n - 1)/2) ⟨h, k⟩`.

Both sides of the hypothesis are continuous in the test field for the `H¹` norm, so it
extends to the closed span; `linearization_apply_eq_adjoint` moves the drift. -/
theorem linearization_apply_eq_of_adjoint_tests (b : Fin n → DerivLp n ∞ univ)
    (k : T.graphDomain) {g : StrongDual ℝ T.space}
    (hk : ∀ φ : T.carrier, gradientForm (T.toH1 φ) ((k : T.space) : H) +
      convectionForm b (T.toH1 φ) ((k : T.space) : H) +
        1 / 2 * T.driftAt φ ((k : T.space) : H) = g (T.point φ))
    (h : T.graphDomain) :
    T.linearization b h (k : T.space) = g (h : T.space) +
      ((n : ℝ) - 1) / 2 * massPairing ((h : T.space) : H) ((k : T.space) : H) := by
  have hfun : (restrictForm T.space gradientForm).flip (k : T.space) +
      (restrictForm T.space (convectionForm b)).flip (k : T.space) +
        (1 / 2 : ℝ) • T.dilationDrift k = g :=
    T.ext_point fun φ ↦ by
      simp only [add_apply, ContinuousLinearMap.flip_apply, restrictForm_apply, smul_apply,
        smul_eq_mul, dilationDrift_point]
      exact hk φ
  have hval := DFunLike.congr_fun hfun (h : T.space)
  simp only [add_apply, ContinuousLinearMap.flip_apply, restrictForm_apply, smul_apply,
    smul_eq_mul] at hval
  have hadj := T.linearization_apply_eq_adjoint b h k
  simp only [boundedPart_apply] at hadj
  linear_combination hadj + hval

end Drift

section WeakEigen

variable (U : ℝ^3 → ℝ^3) (b : Fin 3 → DerivLp 3 ∞ univ) (T : DilationTestSpace 3)

/-- **A weak eigenvalue equation with a continuous right side, tested with a field of the
closed span.** Let `v` be a field of `H¹(ℝ³)³` in the closed span of the test fields whose
weak eigenvalue density integrates to `ℓ(φ)` against every test field `φ`. Then `v` is a field
`h` of the graph domain, and for every `w` in the closed span

`⟨L h, w⟩ + μ ⟨v, w⟩ = ℓ(w)`.

This is `linearization_eq_of_weakEigen_eq` evaluated at `w`. -/
theorem exists_linearization_apply_eq_of_weakEigen_eq
    (hb : ∀ i, (b i : ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ U x i) {μ : ℝ}
    {v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hvT : v ∈ T.space) {ℓ : StrongDual ℝ T.space}
    (hv : ∀ φ : T.carrier, ∫ x, Nonuniqueness.weakEigenDensity U μ v φ x = ℓ (T.point φ)) :
    ∃ h : T.graphDomain, ((h : T.space) : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) = v ∧
      ∀ w : T.space, T.linearization b h w +
        μ * massPairing v (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) = ℓ w := by
  have hv' : ∀ φ : T.carrier, ∫ x, Nonuniqueness.weakEigenDensity U μ
      ((⟨v, hvT⟩ : T.space) : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) φ x = ℓ (T.point φ) := hv
  refine ⟨⟨⟨v, hvT⟩, T.mem_graphDomain_of_weakEigen_eq U b hb hv'⟩, rfl, fun w ↦ ?_⟩
  have h := DFunLike.congr_fun (T.linearization_eq_of_weakEigen_eq U b hb hv') w
  simp only [add_apply, smul_apply, smul_eq_mul, l2Form_apply] at h
  exact h

end WeakEigen

end DilationTestSpace

end NavierStokes.Selfsimilar
