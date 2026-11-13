/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.CoordinateChange.Uniqueness

/-!
# Analytic germ uniqueness from normal data

The level chart and its conormal parametrizations are built from the analytic
defining function. Equal ordinary lower normal data give equal full lower jets
by tangential differentiation, so the flat uniqueness theorem applies in the
chart. For smooth solutions, Evans, §4.6.1, Theorem 1, says that the Cauchy data on a
noncharacteristic surface determine all derivatives there. Since an analytic germ is fixed by
its derivatives at one point, the analytic analogue is
`eventuallyEq_of_analytic_solution_of_normal_data`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis.MultiIndex
open scoped Topology

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

/-- Two analytic solution germs with the same lower normal data on a regular
analytic level agree near its base point. Coefficient analyticity and the
noncharacteristic condition are assumed only at the lower jet of `u` at `p`.
Equality with the lower jet of `v` is derived from the ordinary normal data. -/
theorem eventuallyEq_of_analytic_solution_of_normal_data
    {p : ℝ^(d + 1)}
    {u v : ℝ^(d + 1) → ℝ}
    (a : Sym (Fin (d + 1)) (k + 1) →
      ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (ha : ∀ α, AnalyticAt ℝ (a α) (p, coordinateJetLT (k + 1) u p))
    (hb : AnalyticAt ℝ b (p, coordinateJetLT (k + 1) u p))
    {φ : ℝ^(d + 1) → ℝ} (hφ : AnalyticAt ℝ φ p)
    (hp : φ p = 0) (hreg : fderiv ℝ φ p ≠ 0)
    (hsymbol : ∑ α, a α (p, coordinateJetLT (k + 1) u p) *
      monomial α (PDE.Analysis.Hypersurface.levelNormal φ p) ≠ 0)
    (hu : AnalyticAt ℝ u p) (hv : AnalyticAt ℝ v p)
    (hdata : ∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin (k + 1),
      normalData (j : ℕ) u (PDE.Analysis.Hypersurface.levelNormal φ x) x =
        normalData (j : ℕ) v (PDE.Analysis.Hypersurface.levelNormal φ x) x)
    (hPu : ∀ᶠ x in 𝓝 p,
      ∑ α, a α (x, coordinateJetLT (k + 1) u x) * coordinateDeriv α u x =
        b (x, coordinateJetLT (k + 1) u x))
    (hPv : ∀ᶠ x in 𝓝 p,
      ∑ α, a α (x, coordinateJetLT (k + 1) v x) * coordinateDeriv α v x =
        b (x, coordinateJetLT (k + 1) v x)) :
    u =ᶠ[𝓝 p] v := by
  obtain ⟨c, hps, hcp, hc, hψ, hlevel⟩ :=
    PDE.Analysis.Hypersurface.exists_analytic_level_chart_zero hφ hp hreg
  exact eventuallyEq_of_analytic_solution_of_level_chart
    a b ha hb hreg c hps hcp hc hψ hlevel hsymbol hu hv hdata hPu hPv

end PDE.Cauchy.Quasilinear.Analytic
