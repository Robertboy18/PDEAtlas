/-
Authors: Levent Alpöge, Tristan Buckmaster

The definitions of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where each was written in several modules. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.style.header false

/-!
# General definitions and their first lemmas: the space `ℂ³`, an angular wave and a geometric sum

Each definition is a formula in objects of Mathlib: an abbreviation of a Euclidean space, a complex
exponential, a finite sum. Two first lemmas on the angular wave follow, both proved by unfolding it:
it is continuous, and its conjugate is the wave of the opposite frequency.

## Main results

* `PDE.Analysis.Coef`: the space `EuclideanSpace ℂ (Fin 3)` of the values of Fourier coefficients of
  a vector field.
* `PDE.Analysis.angularWave`: `exp (i κ θ)` for an integer `κ` and a real `θ`.
* `PDE.Analysis.geomSumOneSub`: the sum `∑ i < e, (1 - t) ^ i`, as a complex number.
* `PDE.Analysis.continuous_angularWave`, `PDE.Analysis.conj_angularWave`: the wave is continuous in
  `θ`, and its complex conjugate is `angularWave (-κ) θ`.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the definitions and lemmas of this module and their proofs, adapted to this
  library. See `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- The angular wave of frequency `κ`: `angularWave κ θ = exp (i κ θ)`. -/
def angularWave (κ : ℤ) (θ : ℝ) : ℂ := Complex.exp ((((κ : ℝ) * θ : ℝ) : ℂ) * Complex.I)

/-- The space `ℂ³` in which the Fourier coefficients of a vector field take their values:
`EuclideanSpace ℂ (Fin 3)`. -/
abbrev Coef := EuclideanSpace ℂ (Fin 3)

/-- The geometric sum `∑ i < e, (1 - t) ^ i` of a real `t`, as a complex number. -/
def geomSumOneSub (e : ℕ) (t : ℝ) : ℂ := ((∑ i ∈ Finset.range e, (1 - t) ^ i : ℝ) : ℂ)

/-- The angular wave `θ ↦ angularWave κ θ = exp (i κ θ)` is continuous. -/
theorem continuous_angularWave (κ : ℤ) : Continuous (angularWave κ) := by
  unfold angularWave
  fun_prop

/-- The complex conjugate of `angularWave κ θ` is `angularWave (-κ) θ`. -/
theorem conj_angularWave (κ : ℤ) (θ : ℝ) :
    (starRingEnd ℂ) (angularWave κ θ) = angularWave (-κ) θ := by
  unfold angularWave
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

end PDE.Analysis
