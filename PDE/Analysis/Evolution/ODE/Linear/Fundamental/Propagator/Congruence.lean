/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Propagator.Uniqueness

/-!
# Propagator congruence

If two paths `q` and `γ` agree on `[0, H]`, their linearized coefficients
`Df(q(t))` and `Df(γ(t))` agree there. Restricting a fundamental solution for `q`
on `[0, H]` to `[0, e]`, with `e ≤ H`, therefore gives the same propagator as any
fundamental solution for `γ` on `[0, e]`, even when the normalization times differ.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.Evolution.FundamentalSolution

/-- Agreement of two paths on the larger interval identifies their propagators
on the smaller interval. The normalization times may differ. -/
theorem propagator_eq_of_orbit_eqOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {q γ : ℝ → E} {e H tAnchor sOut : ℝ}
    (he : 0 ≤ e) (heH : e ≤ H) (hqγ : EqOn q γ (Icc (0 : ℝ) H))
    (S : FundamentalSolution
      (fun t ↦ fderiv ℝ f (γ t)) tAnchor (Icc (0 : ℝ) e))
    (Sout : FundamentalSolution
      (fun t ↦ fderiv ℝ f (q t)) sOut (Icc (0 : ℝ) H))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) e) :
    Sout.propagator e t = S.propagator e t := by
  have hsub : Icc (0 : ℝ) e ⊆ Icc (0 : ℝ) H := Icc_subset_Icc le_rfl heH
  have hcoeff : EqOn (fun s ↦ fderiv ℝ f (q s))
      (fun s ↦ fderiv ℝ f (γ s)) (Icc (0 : ℝ) e) := by
    intro s hs
    change fderiv ℝ f (q s) = fderiv ℝ f (γ s)
    rw [hqγ (hsub hs)]
  let Sout' : FundamentalSolution
      (fun s ↦ fderiv ℝ f (γ s)) sOut (Icc (0 : ℝ) e) :=
    (Sout.restrict hsub).congr hcoeff
  change Sout'.propagator e t = S.propagator e t
  exact Sout'.propagator_eq_on_Icc S ht ⟨he, le_rfl⟩

end PDE.Analysis.Evolution.FundamentalSolution
