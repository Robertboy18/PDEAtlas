/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep
public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates

/-!
# Smooth cutoffs into `H¹₀`

Two cutoff operations recur throughout the regularity theory. A smooth
compactly supported `ρ` on `ℝ^n` multiplies `H¹₀(Ω)` into itself, since `ρ φ`
is a test function whenever `φ` is and multiplication by `ρ` is bounded in
`H¹`. A smooth `ρ` whose support lies inside `Ω` sends every `u ∈ H¹(Ω)` into
`H¹₀(Ω)`; this is how a local weak solution without any boundary condition is
turned into a zero-trace one. Both maps are defined in
`PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary`, and the coordinates of
`cutoffH10` are computed in `PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates`.
We record the base and derivative coordinates of the interior cutoff. The
base coordinate is `ρ u` and the derivatives satisfy the product rule
`∂ᵢ(ρ u) = (∂ᵢ ρ) u + ρ ∂ᵢ u` in `L²`.

## Main results

* `baseCoordCLM_cutoffH1ToH10`, `derivCoordCLM_cutoffH1ToH10`: coordinates of
  the interior cutoff `cutoffH1ToH10 : H¹(Ω) → H¹₀(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1 and remark (i) after it (the solution
  need not vanish on the boundary).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open SobolevSpace.CompactSupportLocalization
open scoped BigOperators Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The base coordinate of an interior cutoff is `ρu` in `L²`. -/
theorem baseCoordCLM_cutoffH1ToH10
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) (u : H¹(Ω)) :
    baseCoordCLM (n := n) (Ω := Ω)
        (cutoffH1ToH10 hΩopen ρ hρΩ u) =
      testFunctionLpTop (n := n) (Ω := Ω) ρ •
        wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := 2) (Ω := Ω) u := by
  apply MeasureTheory.Lp.ext
  have hleft := cutoffCLM_base_apply_ae
    (n := n) (p := 2) (Ω := Ω) ρ u
  have hρ := testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ρ
  have hright := MeasureTheory.Lp.coeFn_lpSMul
    (r := (2 : ENNReal))
    (testFunctionLpTop (n := n) (Ω := Ω) ρ)
    (wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 2) (Ω := Ω) u)
  filter_upwards [hleft, hρ, hright] with x hl hρx hr
  change
    ((((cutoffCLM (n := n) (p := 2) (Ω := Ω) ρ u :
        W^{1,2}(Ω)) : WkpAmbientOn n 1 2 Ω)
      (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ) x = _
  rw [hl, hr]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [hρx]
  rfl

/-- The first weak derivatives of an interior cutoff satisfy the product rule
in `L²`. -/
theorem derivCoordCLM_cutoffH1ToH10
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) (u : H¹(Ω)) (i : Fin n) :
    derivCoordCLM (n := n) (Ω := Ω) i
        (cutoffH1ToH10 hΩopen ρ hρΩ u) =
      testFunctionLpTop (n := n) (Ω := Ω) ρ •
          wkpCoordinateCLM
            (n := n) (m := 1) (p := 2) (Ω := Ω)
            (singleDerivIndex (n := n) i) u +
        partialTestFunctionLpTop (n := n) (Ω := Ω) ρ i •
          wkpBaseCoordinateCLM
            (n := n) (m := 1) (p := 2) (Ω := Ω) u := by
  apply MeasureTheory.Lp.ext
  have hleft := cutoffCLM_singleDeriv_apply_ae
    (n := n) (p := 2) (Ω := Ω) ρ u i
  have hρ := testFunctionLpTop_apply_ae (n := n) (Ω := Ω) ρ
  have hdρ := partialTestFunctionLpTop_apply_ae
    (n := n) (Ω := Ω) ρ i
  have hmulρ := MeasureTheory.Lp.coeFn_lpSMul
    (r := (2 : ENNReal))
    (testFunctionLpTop (n := n) (Ω := Ω) ρ)
    (wkpCoordinateCLM
      (n := n) (m := 1) (p := 2) (Ω := Ω)
      (singleDerivIndex (n := n) i) u)
  have hmuldρ := MeasureTheory.Lp.coeFn_lpSMul
    (r := (2 : ENNReal))
    (partialTestFunctionLpTop (n := n) (Ω := Ω) ρ i)
    (wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 2) (Ω := Ω) u)
  have hadd := MeasureTheory.Lp.coeFn_add
    (testFunctionLpTop (n := n) (Ω := Ω) ρ •
      wkpCoordinateCLM
        (n := n) (m := 1) (p := 2) (Ω := Ω)
        (singleDerivIndex (n := n) i) u)
    (partialTestFunctionLpTop (n := n) (Ω := Ω) ρ i •
      wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := 2) (Ω := Ω) u)
  filter_upwards [hleft, hρ, hdρ, hmulρ, hmuldρ, hadd]
    with x hl hρx hdρx hmρ hmdρ ha
  change
    ((((cutoffCLM (n := n) (p := 2) (Ω := Ω) ρ u :
        W^{1,2}(Ω)) : WkpAmbientOn n 1 2 Ω)
      (singleDerivIndex n i) : DerivLp n 2 Ω) : ℝ^n → ℝ) x = _
  rw [hl, ha]
  simp only [Pi.add_apply]
  rw [hmρ, hmdρ]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [hρx, hdρx]
  rfl

end SobolevSpace.GraphSpace
