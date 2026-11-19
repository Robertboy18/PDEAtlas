/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Jet.CoordinateChange
public import PDE.Analysis.Geometry.Hypersurface.Analytic

/-!
# Coordinate arguments for a quasilinear equation

The original coefficients depend on position and every lower coordinate
derivative. Under a change of variables, the position is pulled back by the
inverse chart and the entire lower jet is transported by the chart.
The resulting map is analytic on all finite jet arrays. This is the substitution
`u(x) = v(Φ(x))` of Evans, §4.6.1, proof of Theorem 1, (9), carried out on jets.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1(b), Theorem 1 (Cauchy data and
  noncharacteristic surfaces) and its proof, (9)-(12), pp. 235-236.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear.Analytic

variable {n k : ℕ}


/-- Position and lower jet in the original coordinates, expressed in chart
coordinates and arbitrary lower jet variables. -/
def coordinateArguments (k : ℕ) (c ψ : ℝ^n → ℝ^n)
    (z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)) :
    ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) :=
  (ψ z.1, transport n k z.2 (jetLT ℝ k c (ψ z.1)))

/-- The complete argument map is analytic wherever the chart and its
inverse are analytic. The jet array `q` need not be the jet of a function. -/
theorem analyticAt_coordinateArguments {c ψ : ℝ^n → ℝ^n} {y : ℝ^n}
    (hc : AnalyticAt ℝ c (ψ y)) (hψ : AnalyticAt ℝ ψ y)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) :
    AnalyticAt ℝ (coordinateArguments k c ψ) (y, q) := by
  have hcn : AnalyticOnNhd ℝ c {ψ y} := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hc
  have hj : AnalyticAt ℝ (jetLT ℝ k c) (ψ y) :=
    AnalyticAt.pi fun i ↦ hcn.iteratedFDeriv i (ψ y) (Set.mem_singleton _)
  have hp : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ ψ z.1) (y, q) :=
    hψ.comp_of_eq analyticAt_fst rfl
  have hinner : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦
        (z.2, jetLT ℝ k c (ψ z.1))) (y, q) :=
    analyticAt_snd.prod (hj.comp_of_eq hp rfl)
  have houter := (analyticAt_transport n k (q, jetLT ℝ k c (ψ y))).comp_of_eq
    hinner rfl
  exact hp.prod houter

/-- Substituting the lower jet of `u` at `y` gives the lower jet of `u ∘ c`
at `ψ y`. -/
theorem coordinateArguments_coordinateJetLT {c ψ : ℝ^n → ℝ^n} {y : ℝ^n}
    {u : ℝ^n → ℝ} (hc : AnalyticAt ℝ c (ψ y)) (hu : AnalyticAt ℝ u y)
    (hcy : c (ψ y) = y) :
    coordinateArguments k c ψ (y, coordinateJetLT k u y) =
      (ψ y, coordinateJetLT k (u ∘ c) (ψ y)) := by
  unfold coordinateArguments
  refine Prod.ext ?_ ?_
  · rfl
  have h := transport_coordinateJetLT hc (hcy.symm ▸ hu) k
  simpa only [hcy] using h

end PDE.Cauchy.Quasilinear.Analytic
