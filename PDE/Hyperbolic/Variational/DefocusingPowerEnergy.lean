/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.PowerEnergy

/-!
# Global defocusing power waves

For `r ≥ 1`, the source `-|Jq|^(r-1) Jq` conserves the sum of quadratic wave
energy and the nonnegative power potential. Coercivity of the spatial form then bounds
both displacement and velocity. A finite maximal lifetime would force the
product norm to become arbitrarily large, so this constructed trajectory is global.

The source must have a Lipschitz bound on each norm ball. The scalar potential
is integrable because both `Jq` and its odd power lie in `L²`; the measure may
be infinite. Domain and exponent restrictions enter through construction of
that source, not through the continuation argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution PDE.Analysis.Calculus

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The positive total energy for the negative odd-power wave source. For `r ≥ 1`,
its potential is a finite integral whenever the odd power belongs to `L²`. -/
def defocusingPowerEnergy (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] Lp ℝ 2 μ) (r : ℝ) (z : V × Lp ℝ 2 μ) : ℝ :=
  (1 / 2 : ℝ) * autonomousWaveEnergy B z +
    (∫ y, |J z.1 y| ^ (r + 1) ∂μ) / (r + 1)

/-- The positive power energy controls both components and the full product
norm. The bound follows directly from nonnegativity of the potential and
coercivity of the spatial form. -/
theorem defocusingPowerEnergy_bounds (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] Lp ℝ 2 μ) {c : ℝ}
    (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) {r : ℝ} (hr : 1 ≤ r) (z : V × Lp ℝ 2 μ) :
    c * ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 2 * defocusingPowerEnergy B J r z ∧
      ‖z‖ ≤ Real.sqrt (2 * defocusingPowerEnergy B J r z / min c 1) := by
  have hpotential : 0 ≤ (∫ y, |J z.1 y| ^ (r + 1) ∂μ) / (r + 1) := by
    simpa only [Real.signedPowerPotential, integral_div] using (integral_nonneg (μ := μ)
        (f := fun y : α ↦ Real.signedPowerPotential r (J z.1 y))
        fun y ↦ Real.signedPowerPotential_nonneg hr (J z.1 y))
  have hquadratic : autonomousWaveEnergy B z ≤ 2 * defocusingPowerEnergy B J r z := by
    unfold defocusingPowerEnergy
    linarith
  constructor
  · exact (add_le_add (hcoercive z.1) (le_refl (‖z.2‖ ^ 2))).trans hquadratic
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (lt_min hc zero_lt_one)).mpr
    simpa only [mul_comm] using
      (min_mul_norm_sq_le_autonomousWaveEnergy B hc hcoercive z).trans hquadratic

omit [NormedSpace ℝ V] in
/-- Ballwise Lipschitz bounds for the power source also control the first-order wave
source `(0, -N)`, hence make that source locally Lipschitz. -/
theorem locallyLipschitz_defocusingWaveSource (N : C(V × Lp ℝ 2 μ, Lp ℝ 2 μ))
    (hballs : ∀ R : ℝ, 0 < R → ∃ L : NNReal,
      LipschitzOnWith L N (Metric.closedBall (0 : V × Lp ℝ 2 μ) R)) :
    LocallyLipschitz ((ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk (-N)) := by
  refine StronglyContinuousSemigroup.locallyLipschitz_of_lipschitzOn_closedBall_zero fun R hR ↦ ?_
  obtain ⟨L, hL⟩ := hballs R hR
  refine ⟨L, ?_⟩
  change LipschitzOnWith L (fun z : V × Lp ℝ 2 μ ↦ ((0 : V), -N z))
    (Metric.closedBall (0 : V × Lp ℝ 2 μ) R)
  simpa only [Pi.neg_apply, max_eq_right (show (0 : NNReal) ≤ L from bot_le)] using
    (LipschitzWith.const (0 : V)).lipschitzOnWith.prodMk hL.neg

variable [CompleteSpace V]

/-- The maximal trajectory for the negative odd-power source has infinite
forward lifetime and conserves its positive total energy. The displayed bounds
control displacement and velocity for every nonnegative time. Only linear
semigroup energy and kinematics are assumed; the nonlinear conservation law
and the global lifetime are conclusions. -/
theorem defocusing_power_global (S : StronglyContinuousSemigroup (V × Lp ℝ 2 μ))
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (henergy : ∀ t x, autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x)
    (J : V →L[ℝ] Lp ℝ 2 μ)
    (hkin : ∀ (f : ℝ → Lp ℝ 2 μ), Continuous f → ∀ (x : V × Lp ℝ 2 μ) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun s ↦ ((0 : V), f s)) s;
      (∫ s in (0 : ℝ)..t, (z s).2) = J (z t).1 - J x.1)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v) {r : ℝ} (hr : 1 ≤ r)
    (N : C(V × Lp ℝ 2 μ, Lp ℝ 2 μ)) (hNae : ∀ z, N z =ᵐ[μ] fun y ↦ Real.signedPower r (J z.1 y))
    (hballs : ∀ R : ℝ, 0 < R → ∃ L : NNReal,
      LipschitzOnWith L N (Metric.closedBall (0 : V × Lp ℝ 2 μ) R))
    (x₀ : V × Lp ℝ 2 μ) :
    let F := (ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk (-N)
    let z := S.maximalMildSolution (locallyLipschitz_defocusingWaveSource N hballs) x₀
    S.mildLifespan F x₀ = ∞ ∧
      ∀ t : ℝ, 0 ≤ t →
        defocusingPowerEnergy B J r (z t) = defocusingPowerEnergy B J r x₀ ∧
        c * ‖(z t).1‖ ^ 2 + ‖(z t).2‖ ^ 2 ≤ 2 * defocusingPowerEnergy B J r x₀ ∧
        ‖z t‖ ≤ Real.sqrt (2 * defocusingPowerEnergy B J r x₀ / min c 1) := by
  let F := (ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk (-N)
  have hF : LocallyLipschitz F := locallyLipschitz_defocusingWaveSource N hballs
  let z := S.maximalMildSolution hF x₀
  have hnegative : LocallyLipschitz ((-1 : ℝ) • N) := by
    rw [neg_one_smul]
    change LocallyLipschitz (fun z ↦ -N z)
    exact LipschitzWith.prod_snd.locallyLipschitz.comp hF
  have hconserve (t : ℝ) (ht : 0 ≤ t) (hlt : ENNReal.ofReal t < S.mildLifespan F x₀) :
      defocusingPowerEnergy B J r (z t) = defocusingPowerEnergy B J r x₀ := by
    have hlt' : ENNReal.ofReal t < S.mildLifespan
        ((ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk ((-1 : ℝ) • N)) x₀ := by
      simpa only [neg_one_smul] using hlt
    simpa only [defocusingPowerEnergy, neg_one_smul, neg_one_mul, sub_neg_eq_add] using
      scaled_power_energy_maximalMildSolution S B hsymm henergy J hkin hr (-1) N
        hnegative hNae x₀ ht hlt'
  have hFballs : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : V × Lp ℝ 2 μ) R) := by
    intro R hR
    obtain ⟨L, hL⟩ := hballs R hR
    refine ⟨L, ?_⟩
    change LipschitzOnWith L (fun z : V × Lp ℝ 2 μ ↦ ((0 : V), -N z))
      (Metric.closedBall (0 : V × Lp ℝ 2 μ) R)
    simpa only [Pi.neg_apply, max_eq_right (show (0 : NNReal) ≤ L from bot_le)] using
      (LipschitzWith.const (0 : V)).lipschitzOnWith.prodMk hL.neg
  have hbounded (t : ℝ) (ht : 0 ≤ t) (hlt : ENNReal.ofReal t < S.mildLifespan F x₀) :
      ‖z t‖ ≤ Real.sqrt (2 * defocusingPowerEnergy B J r x₀ / min c 1) := by
    simpa only [hconserve t ht hlt] using (defocusingPowerEnergy_bounds B J hc hcoercive hr (z t)).2
  have hglobal : S.mildLifespan F x₀ = ∞ := S.mildLifespan_eq_top_of_bounded hF hFballs x₀ hbounded
  refine ⟨hglobal, fun t ht ↦ ?_⟩
  have hlt : ENNReal.ofReal t < S.mildLifespan F x₀ := by
    rw [hglobal]
    exact ENNReal.ofReal_lt_top
  have heq := hconserve t ht hlt
  refine ⟨heq, ?_⟩
  simpa only [heq] using defocusingPowerEnergy_bounds B J hc hcoercive hr (z t)

end Hyperbolic.Variational
