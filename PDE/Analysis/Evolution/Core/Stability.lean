/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Core.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Difference energy from Hilbert-valued evolution equations

Two absolutely continuous curves `u, v` in a real inner product space `H` solve
`u' = B(t) U + f` and `v' = B(t) V + g` almost everywhere. The drift
`B(t) : S → H` acts on states `U, V` in another space `S`, which represent `u, v`
through a map `J : S → H`. A one-sided bound
`2 ⟪B(t) x - B(t) y, J x - J y⟫ ≤ C ‖J x - J y‖²` gives the `L²` stability estimate
`‖u(t) - v(t)‖² ≤ (‖u(a) - v(a)‖² + ∫ₐᵇ ‖f - g‖²) e^{(C+1)(t-a)}`. Since `B` is
only evaluated on `S`, a spatial differential operator need not extend boundedly
to `H`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace PDE.Analysis.Evolution

/-- `L²` stability for two curves with a common one-sided bounded drift. If
`u = J ∘ U` and `v = J ∘ V` almost everywhere, `u' = B(t) U + f` and
`v' = B(t) V + g` almost everywhere, `f - g ∈ L²` and
`2 ⟪B(t) x - B(t) y, J x - J y⟫ ≤ C ‖J x - J y‖²` with `C ≥ 0`, then
`‖u(t) - v(t)‖² ≤ (‖u(a) - v(a)‖² + ∫ₐᵇ ‖f - g‖²) e^{(C+1)(t-a)}`. -/
theorem norm_sub_sq_le_exp_of_ae_drift_equations
    {H S : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} (hab : a ≤ b) (J : S → H) (B : ℝ → S → H)
    {u v : ℝ → H} {U V : ℝ → S} {f g : ℝ → H}
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : AbsolutelyContinuousOnInterval v a b)
    (hU : u =ᵐ[volume.restrict (Ioc a b)] fun t ↦ J (U t))
    (hV : v =ᵐ[volume.restrict (Ioc a b)] fun t ↦ J (V t))
    (heu : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (B t (U t) + f t) t)
    (hev : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt v (B t (V t) + g t) t)
    (hfg : MemLp (fun t ↦ f t - g t) 2 (volume.restrict (Ioc a b)))
    {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ x y : S,
      2 * ⟪B t x - B t y, J x - J y⟫_ℝ ≤ C * ‖J x - J y‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t - v t‖ ^ 2 ≤
        (‖u a - v a‖ ^ 2 + ∫ s in a..b, ‖f s - g s‖ ^ 2) *
          Real.exp ((C + 1) * (t - a)) := by
  let q : ℝ → ℝ := fun t ↦ ‖u t - v t‖ ^ 2
  let d : ℝ → H := fun t ↦ f t - g t
  have hqAC : AbsolutelyContinuousOnInterval q a b :=
    absolutelyContinuousOnInterval_norm_sq (hu.sub hv)
  have hdsq : IntegrableOn (fun t ↦ ‖d t‖ ^ 2) (Ioc a b) volume :=
    (memLp_two_iff_integrable_sq_norm hfg.aestronglyMeasurable).mp hfg
  have hdsqInt : IntervalIntegrable (fun t ↦ ‖d t‖ ^ 2) volume a b := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hdsq
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv q t ≤ (C + 1) * q t + ‖d t‖ ^ 2 := by
    filter_upwards [hU, hV, heu, hev, hB] with t htU htV htu htv htB
    have hqt : deriv q t =
        2 * ⟪u t - v t, (B t (U t) + f t) - (B t (V t) + g t)⟫_ℝ :=
      (htu.sub htv).norm_sq.deriv
    have hsplit : (B t (U t) + f t) - (B t (V t) + g t) =
        (B t (U t) - B t (V t)) + (f t - g t) := by abel
    rw [hqt, hsplit, inner_add_right]
    have hprincipal := htB (U t) (V t)
    rw [← htU, ← htV,
      ← real_inner_comm (B t (U t) - B t (V t)) (u t - v t)] at hprincipal
    have hforcing := real_inner_le_norm (u t - v t) (f t - g t)
    dsimp only [q, d]
    nlinarith only [hprincipal, hforcing, sq_nonneg (‖u t - v t‖ - ‖f t - g t‖)]
  exact le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le hab hqAC hdsqInt
    (Eventually.of_forall fun t ↦ sq_nonneg ‖d t‖) (by positivity) hderiv

end PDE.Analysis.Evolution
