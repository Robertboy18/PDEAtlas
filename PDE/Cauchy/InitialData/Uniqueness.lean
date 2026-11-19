/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.InitialData.Normalization
public import PDE.Cauchy.NormalForm.Uniqueness

/-!
# Analytic germ uniqueness after shifting the data

Subtracting one solution reduces equality of the lower hyperplane jets to
zero pure-time Cauchy traces. The shifted coefficients and forcing come from
the original equation. `CoordinateChange/Uniqueness` applies this step after
recovering the lower jets from the normal data on a curved hypersurface.

Evans, §4.6.3(a), also subtracts an analytic function to reach the zero Cauchy data of (14);
here the subtracted function is one of the two solutions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(a), (14), p. 239.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Topology
open Filter PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}


/-- Analytic solutions with the same entire lower hyperplane jet agree as
germs, provided the pure-time principal coefficient is nonzero at their
common initial jet. -/
theorem eventuallyEq_of_analytic_solution_of_lower_jet
    {a : Sym (Fin (d + 1)) (k + 1) →
      ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ}
    {b : ℝ^(d + 1) × (∀ j : Fin (k + 1), Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ}
    {u v : ℝ^(d + 1) → ℝ} (hu : AnalyticAt ℝ u 0) (hv : AnalyticAt ℝ v 0)
    (ha : ∀ α, AnalyticAt ℝ (a α) (0, coordinateJetLT (k + 1) u 0))
    (hb : AnalyticAt ℝ b (0, coordinateJetLT (k + 1) u 0))
    (hprincipal : a (Sym.replicate (k + 1) 0) (0, coordinateJetLT (k + 1) u 0) ≠ 0)
    (htrace : ∀ᶠ x in 𝓝 (0 : ℝ^(d + 1)), x 0 = 0 →
      coordinateJetLT (k + 1) u x = coordinateJetLT (k + 1) v x)
    (hPu : ∀ᶠ x in 𝓝 (0 : ℝ^(d + 1)),
      ∑ α, a α (x, coordinateJetLT (k + 1) u x) * coordinateDeriv α u x =
        b (x, coordinateJetLT (k + 1) u x))
    (hPv : ∀ᶠ x in 𝓝 (0 : ℝ^(d + 1)),
      ∑ α, a α (x, coordinateJetLT (k + 1) v x) * coordinateDeriv α v x =
        b (x, coordinateJetLT (k + 1) v x)) :
    u =ᶠ[𝓝 0] v := by
  let w := v - u
  have hw : AnalyticAt ℝ w 0 := hv.sub hu
  have hsum : u + w = v := by
    funext x
    change u x + (v x - u x) = v x
    ring
  have hj0 : coordinateJetLT (k + 1) u 0 = coordinateJetLT (k + 1) v 0 :=
    htrace.self_of_nhds rfl
  have hargs {f : ℝ^(d + 1) → ℝ} (hf : AnalyticAt ℝ f 0) :
      AnalyticAt ℝ (fun x ↦ (x, coordinateJetLT (k + 1) f x)) 0 :=
    analyticAt_id.prod (AnalyticAt.pi fun j ↦
      AnalyticAt.pi fun α ↦ analyticAt_coordinateDeriv hf α)
  have hdu : ∀ᶠ x in 𝓝 (0 : ℝ^(d + 1)),
      a (Sym.replicate (k + 1) 0) (x, coordinateJetLT (k + 1) u x) ≠ 0 :=
    ((ha _).comp_of_eq (hargs hu) rfl).continuousAt.eventually_ne hprincipal
  have hdv : ∀ᶠ x in 𝓝 (0 : ℝ^(d + 1)),
      a (Sym.replicate (k + 1) 0) (x, coordinateJetLT (k + 1) v x) ≠ 0 :=
    ((hj0 ▸ ha _).comp_of_eq (hargs hv) rfl).continuousAt.eventually_ne
      (by simpa only [Function.comp_apply, ← hj0] using hprincipal)
  let γ (x : Fin d → ℝ) : ℝ^(d + 1) := WithLp.toLp 2 (Fin.cons 0 x)
  have hγa : AnalyticAt ℝ γ 0 := by
    have hc : AnalyticAt ℝ
        (fun x : Fin d → ℝ ↦ (Fin.cons 0 x : Fin (d + 1) → ℝ)) 0 := by
      apply AnalyticAt.pi
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change AnalyticAt ℝ (fun _ : Fin d → ℝ ↦ (0 : ℝ)) 0
        exact analyticAt_const
      · change AnalyticAt ℝ (fun x : Fin d → ℝ ↦ x j) 0
        exact (ContinuousLinearMap.proj j : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt 0
    exact ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (d + 1) ↦ ℝ)).symm.analyticAt _).comp hc
  have hγ0 : γ 0 = 0 := by
    simp only [γ, ← Matrix.vecCons.eq_1, Matrix.cons_zero_zero, WithLp.toLp_zero]
  have hγ : Tendsto γ (𝓝 0) (𝓝 0) := hγ0 ▸ hγa.continuousAt.tendsto
  have hwtrace (j : ℕ) (hj : j < k + 1) :
      (fun x : Fin d → ℝ ↦
        coordinateDeriv (Sym.replicate j 0) w (WithLp.toLp 2 (Fin.cons 0 x))) =ᶠ[𝓝 0] 0 := by
    filter_upwards [hγ.eventually htrace, hγ.eventually hu.eventually_analyticAt,
      hγ.eventually hv.eventually_analyticAt] with x htx hux hvx
    change coordinateDeriv (Sym.replicate j 0) (v - u) (γ x) = 0
    rw [coordinateDeriv_sub _ hvx.contDiffAt hux.contDiffAt, sub_eq_zero]
    exact (congrFun (congrFun (htx rfl) ⟨j, hj⟩) (Sym.replicate j 0)).symm
  have hzeroTrace (j : ℕ) (_ : j < k + 1) :
      (fun x : Fin d → ℝ ↦ coordinateDeriv (Sym.replicate j 0)
        (0 : ℝ^(d + 1) → ℝ) (WithLp.toLp 2 (Fin.cons 0 x))) =ᶠ[𝓝 0] 0 := by
    simp only [coordinateDeriv, iteratedFDeriv_zero]
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hwP : coordinateDeriv (Sym.replicate (k + 1) 0) w =ᶠ[𝓝 0]
      rightHandSide (normalizedCoefficients a u) (normalizedForcing a b u) w := by
    filter_upwards [hPv, hu.eventually_analyticAt, hw.eventually_analyticAt, hdv]
      with x hpx hux hwx hdx
    exact (equation_add_iff a b hux hwx (by rwa [hsum])).mp (by rwa [hsum])
  have hzeroP : coordinateDeriv (Sym.replicate (k + 1) 0) (0 : ℝ^(d + 1) → ℝ) =ᶠ[𝓝 0]
      rightHandSide (normalizedCoefficients a u) (normalizedForcing a b u) 0 := by
    filter_upwards [hPu, hu.eventually_analyticAt, hdu] with x hpx hux hdx
    exact (equation_add_iff a b hux (show AnalyticAt ℝ (0 : ℝ^(d + 1) → ℝ) x from
      analyticAt_const) (by simpa only [add_zero] using hdx)).mp
        (by simpa only [add_zero] using hpx)
  have heq := eventuallyEq_of_analytic_solution_zero
    (analyticAt_normalizedCoefficients ha hu hprincipal)
    (analyticAt_normalizedForcing ha hb hu hprincipal)
    hw (show AnalyticAt ℝ (0 : ℝ^(d + 1) → ℝ) 0 from analyticAt_const)
    hwtrace hzeroTrace hwP hzeroP
  filter_upwards [heq] with x hx
  exact (sub_eq_zero.mp hx).symm

end PDE.Cauchy.Quasilinear.Analytic
