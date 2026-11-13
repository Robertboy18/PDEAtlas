/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Cauchy.NormalData.Jet
public import PDE.Cauchy.CoordinateChange.Equation
public import PDE.Cauchy.InitialData.Uniqueness

/-!
# Uniqueness in an analytic level chart

Equal ordinary normal data first determine the whole lower original jet by
tangential differentiation. Finite jet transport then gives the lower
hyperplane traces required by the scalar analytic uniqueness theorem.
The first coordinate of the chart is the analytic defining function of the
hypersurface. Compare Evans, §4.6.1, proof of Theorem 1, step 3, where the Cauchy data (12) of
the transformed function on `{yₙ = 0}` are computed from the chart and the original data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1(b), Theorem 1 (Cauchy data and
  noncharacteristic surfaces) and its proof, (9)-(12), pp. 235-236.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis PDE.Analysis.MultiIndex
open scoped Topology

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

/-- Analytic solution germs with equal ordinary normal data agree in an
analytic level chart. The lower chart-coordinate traces are derived from the
normal data by `PDE.Analysis.Cauchy.eventually_coordinateJetLT_eq_of_normal_data`. -/
theorem eventuallyEq_of_analytic_solution_of_level_chart
    {p : ℝ^(d + 1)}
    {u v : ℝ^(d + 1) → ℝ}
    (a : Sym (Fin (d + 1)) (k + 1) →
      ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (ha : ∀ α, AnalyticAt ℝ (a α) (p, coordinateJetLT (k + 1) u p))
    (hb : AnalyticAt ℝ b (p, coordinateJetLT (k + 1) u p))
    {φ : ℝ^(d + 1) → ℝ} (hreg : fderiv ℝ φ p ≠ 0)
    (c : OpenPartialHomeomorph (ℝ^(d + 1)) (ℝ^(d + 1)))
    (hps : p ∈ c.source) (hcp : c p = 0)
    (hc : AnalyticAt ℝ c p) (hψ : AnalyticAt ℝ c.symm 0)
    (hlevel : ∀ x, c x 0 = φ x)
    (hsymbol : ∑ α, a α (p, coordinateJetLT (k + 1) u p) *
      monomial α (Hypersurface.levelNormal φ p) ≠ 0)
    (hu : AnalyticAt ℝ u p) (hv : AnalyticAt ℝ v p)
    (hdata : ∀ᶠ x in 𝓝 p, φ x = 0 → ∀ j : Fin (k + 1),
      normalData (j : ℕ) u (Hypersurface.levelNormal φ x) x =
        normalData (j : ℕ) v (Hypersurface.levelNormal φ x) x)
    (hPu : ∀ᶠ x in 𝓝 p,
      ∑ α, a α (x, coordinateJetLT (k + 1) u x) * coordinateDeriv α u x =
        b (x, coordinateJetLT (k + 1) u x))
    (hPv : ∀ᶠ x in 𝓝 p,
      ∑ α, a α (x, coordinateJetLT (k + 1) v x) * coordinateDeriv α v x =
        b (x, coordinateJetLT (k + 1) v x)) :
    u =ᶠ[𝓝 p] v := by
  have hip : c.symm 0 = p := by
    rw [← hcp]
    exact c.left_inv hps
  let U : ℝ^(d + 1) → ℝ := u ∘ c.symm
  let V : ℝ^(d + 1) → ℝ := v ∘ c.symm
  have hU : AnalyticAt ℝ U 0 := hu.comp_of_eq hψ hip
  have hV : AnalyticAt ℝ V 0 := hv.comp_of_eq hψ hip
  have hφ : AnalyticAt ℝ φ p := by
    have ht : AnalyticAt ℝ (fun x : ℝ^(d + 1) ↦ c x 0) p :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).analyticAt (c p)).comp hc
    simpa only [hlevel] using ht
  have hj := PDE.Analysis.Cauchy.eventually_coordinateJetLT_eq_of_normal_data
    hφ hreg hu hv hdata
  have hψt : Tendsto c.symm (𝓝 0) (𝓝 p) := hip ▸ hψ.continuousAt.tendsto
  have htarget : c.target ∈ 𝓝 (0 : ℝ^(d + 1)) :=
    c.open_target.mem_nhds (hcp ▸ c.map_source hps)
  have htrace : ∀ᶠ y in 𝓝 (0 : ℝ^(d + 1)), y 0 = 0 →
      coordinateJetLT (k + 1) U y = coordinateJetLT (k + 1) V y := by
    filter_upwards [hψt.eventually (hu.eventually_analyticAt.and hv.eventually_analyticAt),
      hψ.eventually_analyticAt, htarget, hψt.eventually hj] with y hy hψy hyt hjy
    intro hy0
    have hφy : φ (c.symm y) = 0 := by
      rw [← hlevel, c.right_inv hyt, hy0]
    have hjet := hjy hφy
    change coordinateJetLT (k + 1) (u ∘ c.symm) y =
      coordinateJetLT (k + 1) (v ∘ c.symm) y
    rw [← transport_coordinateJetLT hψy hy.1 (k + 1),
      hjet, transport_coordinateJetLT hψy hy.2]
  have hucomp : U ∘ c =ᶠ[𝓝 p] u := by
    filter_upwards [c.open_source.mem_nhds hps] with x hx
    change u (c.symm (c x)) = u x
    rw [c.left_inv hx]
  have hvcomp : V ∘ c =ᶠ[𝓝 p] v := by
    filter_upwards [c.open_source.mem_nhds hps] with x hx
    change v (c.symm (c x)) = v x
    rw [c.left_inv hx]
  obtain ⟨hA, hB, hprincipal⟩ := analyticAt_transformed_of_level_chart
    a b c hps hcp hc hψ hreg 0 (Filter.Eventually.of_forall hlevel) hu ha hb hsymbol
  have hEq {f F : ℝ^(d + 1) → ℝ} (hF : AnalyticAt ℝ F 0)
      (hcomp : F ∘ c =ᶠ[𝓝 p] f)
      (hPf : ∀ᶠ x in 𝓝 p,
        ∑ α, a α (x, coordinateJetLT (k + 1) f x) * coordinateDeriv α f x =
          b (x, coordinateJetLT (k + 1) f x)) :
      ∀ᶠ y in 𝓝 (0 : ℝ^(d + 1)),
        ∑ α, transformedCoefficients a c c.symm α (y, coordinateJetLT (k + 1) F y) *
          coordinateDeriv α F y =
            transformedForcing a b c c.symm (y, coordinateJetLT (k + 1) F y) := by
    have hlow : ∀ᶠ x in 𝓝 p,
        coordinateJetLT (k + 1) (F ∘ c) x = coordinateJetLT (k + 1) f x := by
      filter_upwards [Filter.eventually_all.mpr
        (fun j : Fin (k + 1) ↦ hcomp.iteratedFDeriv ℝ j)] with x hx
      funext j α
      exact congrArg (fun D ↦ D (directions α)) (hx j)
    filter_upwards [hψt.eventually hPf, hψt.eventually hlow,
      hψt.eventually (hcomp.iteratedFDeriv ℝ (k + 1)),
      hψt.eventually hc.eventually_analyticAt,
      hF.eventually_analyticAt, htarget] with y hpy hly hdy hcy hFy hyt
    apply (equation_comp_iff a b (Nat.succ_pos k) hcy hFy (c.right_inv hyt)).mp
    simpa only [hly, coordinateDeriv, hdy] using hpy
  have heq := eventuallyEq_of_analytic_solution_of_lower_jet hU hV hA hB
    hprincipal htrace (hEq hU hucomp hPu) (hEq hV hvcomp hPv)
  have hct : Tendsto c (𝓝 p) (𝓝 0) := hcp ▸ hc.continuousAt.tendsto
  filter_upwards [hct.eventually heq, hucomp, hvcomp] with x hx hux hvx
  exact hux.symm.trans (hx.trans hvx)

end PDE.Cauchy.Quasilinear.Analytic
