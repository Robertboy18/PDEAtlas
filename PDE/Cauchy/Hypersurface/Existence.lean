/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Cauchy.NormalData.Jet
public import PDE.Cauchy.CoordinateChange.Equation
public import PDE.Cauchy.InitialData.Existence

/-!
# Analytic Cauchy existence on a regular level

An analytic level chart and one scalar extension carrying the normal data are
constructed from the defining function and the individual analytic data.
The transformed equation is solved on a positive ball, then pulled back to
the original coordinates. The radius is allowed to shrink.

`exists_analytic_solution_of_normal_data` is the Cauchy–Kovalevskaya theorem for a scalar
quasilinear equation of order `k + 1` with analytic Cauchy data on an analytic
level set, the problem that Evans, §4.6.3, reduces to Theorem 2 by flattening the boundary,
subtracting the data and passing to a first-order system. The noncharacteristic condition is
(8) of §4.6.1 for the unit normal of the level set, assumed only at the base point and at the
lower jet given by the data. The data are ordinary normal derivatives, and the solution exists
on some ball of positive radius.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1, (8), and §4.6.3(a), Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis.MultiIndex
open scoped Topology

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

/-- A scalar analytic quasilinear equation of any positive order has an analytic
solution near a noncharacteristic point of a regular analytic level, with
prescribed normal data `g`. Analyticity of the coefficients and the
noncharacteristic condition are assumed only at the lower jet determined by `g`.
The data `g i` are arbitrary analytic functions; the proof builds one extension
carrying all of them, using the unit normal to the level. -/
theorem exists_analytic_solution_of_normal_data
    {Ω : Set (ℝ^(d + 1))} (hΩ : IsOpen Ω) {p : ℝ^(d + 1)} (hpΩ : p ∈ Ω)
    (a : Sym (Fin (d + 1)) (k + 1) →
      ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    {φ : ℝ^(d + 1) → ℝ} (hφ : AnalyticAt ℝ φ p)
    (hp : φ p = 0) (hreg : fderiv ℝ φ p ≠ 0)
    (g : Fin (k + 1) → ℝ^(d + 1) → ℝ)
    (hg : ∀ i, AnalyticAt ℝ (g i) p)
    (ha : ∀ α, AnalyticAt ℝ (a α) (p, PDE.Analysis.Cauchy.normalDataJet φ g p))
    (hb : AnalyticAt ℝ b (p, PDE.Analysis.Cauchy.normalDataJet φ g p))
    (hsymbol : ∑ α, a α (p, PDE.Analysis.Cauchy.normalDataJet φ g p) *
      monomial α (PDE.Analysis.Hypersurface.levelNormal φ p) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ Ω ∧ ∃ u : ℝ^(d + 1) → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball p r) ∧
      (∀ x ∈ Metric.ball p r,
        ∑ α, a α (x, coordinateJetLT (k + 1) u x) * coordinateDeriv α u x =
          b (x, coordinateJetLT (k + 1) u x)) ∧
      ∀ x ∈ Metric.ball p r, φ x = 0 →
        ∀ i : Fin (k + 1),
          normalData (i : ℕ) u (PDE.Analysis.Hypersurface.levelNormal φ x) x = g i x := by
  obtain ⟨c, hps, hcp, hc, hψ, hlevel⟩ :=
    PDE.Analysis.Hypersurface.exists_analytic_level_chart_zero hφ hp hreg
  obtain ⟨G, hG, hdata, hGjet⟩ :=
    PDE.Analysis.Cauchy.exists_analytic_normalData_with_jet hφ hreg g hg
  have hip : c.symm 0 = p := by
    rw [← hcp]
    exact c.left_inv hps
  let F : ℝ^(d + 1) → ℝ := G ∘ c.symm
  have hF : AnalyticAt ℝ F 0 := hG.comp_of_eq hψ hip
  obtain ⟨hA, hB, hprincipal⟩ := analyticAt_transformed_of_level_chart
    a b c hps hcp hc hψ hreg 0 (Filter.Eventually.of_forall hlevel) hG
    (by simpa only [hGjet] using ha) (by simpa only [hGjet] using hb)
    (by simpa only [hGjet] using hsymbol)
  obtain ⟨s, hs, v, hv, htrace, hP⟩ :=
    exists_analytic_solution_of_data_extension
      (transformedCoefficients a c c.symm) (transformedForcing a b c c.symm)
      F hA hB hF hprincipal
  have hcball : ∀ᶠ x in 𝓝 p, c x ∈ Metric.ball 0 s :=
    (hcp ▸ hc.continuousAt.tendsto).eventually (Metric.ball_mem_nhds 0 hs)
  have hFnear : ∀ᶠ x in 𝓝 p, AnalyticAt ℝ F (c x) :=
    (hcp ▸ hc.continuousAt.tendsto).eventually hF.eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.Eventually.and (hΩ.mem_nhds hpΩ) (Filter.Eventually.and
      (c.open_source.mem_nhds hps)
      (hc.eventually_analyticAt.and (hcball.and (hFnear.and hdata)))))
  refine ⟨r, hr, fun x hx ↦ (hball hx).1, v ∘ c, ?_, ?_, ?_⟩
  · intro x hx
    exact (hv (c x) (hball hx).2.2.2.1).comp (hball hx).2.2.1
  · intro x hx
    have hxs := (hball hx).2.1
    have hcx := (hball hx).2.2.1
    have hvx := hv (c x) (hball hx).2.2.2.1
    have heq := (equation_comp_iff a b (c := c) (ψ := c.symm) (u := v) (y := c x)
      (Nat.succ_pos k) (by simpa only [c.left_inv hxs] using hcx)
      hvx (c.right_inv (c.map_source hxs))).mpr
      (hP (c x) (hball hx).2.2.2.1)
    simpa only [c.left_inv hxs] using heq
  · intro x hx hφx i
    have hxs := (hball hx).2.1
    have hcx := (hball hx).2.2.1
    have hflat := htrace (c x) (hball hx).2.2.2.1 (by rw [hlevel, hφx])
    have hFx : AnalyticAt ℝ F (c x) := (hball hx).2.2.2.2.1
    have hlocal : F ∘ c =ᶠ[𝓝 x] G := by
      filter_upwards [c.open_source.mem_nhds hxs] with y hy
      change G (c.symm (c y)) = G y
      rw [c.left_inv hy]
    have hujet : coordinateJetLT (k + 1) (v ∘ c) x =
        coordinateJetLT (k + 1) G x := by
      rw [← transport_coordinateJetLT hcx (hv (c x) (hball hx).2.2.2.1) (k + 1),
        hflat, transport_coordinateJetLT hcx hFx]
      funext j α
      exact congrArg (fun D ↦ D (directions α))
        ((hlocal.iteratedFDeriv ℝ j).self_of_nhds)
    have hn := (hball hx).2.2.2.2.2 hφx i
    have hux : AnalyticAt ℝ (v ∘ c) x :=
      (hv (c x) (hball hx).2.2.2.1).comp hcx
    have hGx : AnalyticAt ℝ G x := (hFx.comp hcx).congr hlocal
    have hD : iteratedFDeriv ℝ i (v ∘ c) x = iteratedFDeriv ℝ i G x := by
      rw [← multilinearFromCoordinates_coordinateDeriv hux i,
        ← multilinearFromCoordinates_coordinateDeriv hGx i]
      exact congrArg (multilinearFromCoordinates (d + 1) i) (congrFun hujet i)
    exact (congrArg (fun A ↦ A (fun _ : Fin (i : ℕ) ↦
      PDE.Analysis.Hypersurface.levelNormal φ x)) hD).trans hn

end PDE.Cauchy.Quasilinear.Analytic
