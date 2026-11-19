/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.WaveEnergy
public import PDE.Analysis.Calculus.PowerPotential

/-!
# Conservation of signed power energy

The maximal Picard trajectory of the source `σ |Jq|^(r-1) Jq` conserves
`(B(q,q) + ‖p‖²)/2 - σ ∫ |Jq|^(r+1)/(r+1)` before its lifespan.
The focusing theorem is the specialization `σ = 1`.
The source is identified almost everywhere with `|Jq|^(r-1) Jq`, and its potential identity is
proved from that formula.

The linear semigroup hypotheses are exactly energy preservation and the
integrated displacement equation. The spectral Dirichlet constructor supplies
both. The theorem itself is independent of the spatial dimension and domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution PDE.Analysis.Calculus

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Multiplying the odd-power source by any real coefficient multiplies its
potential by that coefficient. This gives one conservation law for both signs
along the maximal constructed trajectory. -/
theorem scaled_power_energy_maximalMildSolution (S : StronglyContinuousSemigroup (V × Lp ℝ 2 μ))
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (henergy : ∀ t x, autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x)
    (J : V →L[ℝ] Lp ℝ 2 μ)
    (hkin : ∀ (f : ℝ → Lp ℝ 2 μ), Continuous f → ∀ (x : V × Lp ℝ 2 μ) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun s ↦ ((0 : V), f s)) s;
      (∫ s in (0 : ℝ)..t, (z s).2) = J (z t).1 - J x.1)
    {r : ℝ} (hr : 1 ≤ r) (σ : ℝ) (N : C(V × Lp ℝ 2 μ, Lp ℝ 2 μ)) (hN : LocallyLipschitz (σ • N))
    (hNae : ∀ z, N z =ᵐ[μ] fun y ↦ Real.signedPower r (J z.1 y)) (x₀ : V × Lp ℝ 2 μ) {t : ℝ}
    (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t <
      S.mildLifespan ((ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk (σ • N)) x₀) :
    let F := (ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk (σ • N)
    let hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : V)).prodMk hN
    let z := S.maximalMildSolution hF x₀
    (1 / 2 : ℝ) * autonomousWaveEnergy B (z t) -
        σ * ((∫ y, |J (z t).1 y| ^ (r + 1) ∂μ) / (r + 1)) =
      (1 / 2 : ℝ) * autonomousWaveEnergy B x₀ -
        σ * ((∫ y, |J x₀.1 y| ^ (r + 1) ∂μ) / (r + 1)) := by
  let Φ := fun q : V ↦ ∫ y, Real.signedPowerPotential r (J q y) ∂μ
  have hgradient (q : V) (p : Lp ℝ 2 μ) :
      HasFDerivAt (fun v ↦ σ * Φ v) ((innerSL ℝ ((σ • N) (q, p))).comp J) q := by
    have hd := (hasFDerivAt_integral_signedPowerPotential J hr (fun v ↦ N (v, p))
      (fun v ↦ hNae (v, p)) q
      (N.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt).const_smul σ
    have hlin : σ • ((innerSL ℝ (N (q, p))).comp J) =
        ((innerSL ℝ ((σ • N) (q, p))).comp J) := by
      ext v
      change σ * ⟪N (q, p), J v⟫_ℝ = ⟪σ • N (q, p), J v⟫_ℝ
      exact (real_inner_smul_left _ _ _).symm
    rwa [hlin] at hd
  have hΦ (q : V) : Φ q = (∫ y, |J q y| ^ (r + 1) ∂μ) / (r + 1) :=
    integral_div (r + 1) (fun y ↦ |J q y| ^ (r + 1))
  simpa only [hΦ] using potential_energy_maximalMildSolution S B hsymm henergy J hkin
    (σ • N) (fun q ↦ σ * Φ q) hgradient ((LocallyLipschitz.const (0 : V)).prodMk hN) x₀ ht hlt

/-- The focusing power energy of the maximal constructed trajectory is constant
at every nonnegative time strictly below its lifespan. The hypotheses identify
the scalar source and its local Lipschitz continuity, not a solution or an energy law. -/
theorem power_energy_maximalMildSolution (S : StronglyContinuousSemigroup (V × Lp ℝ 2 μ))
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (henergy : ∀ t x, autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x)
    (J : V →L[ℝ] Lp ℝ 2 μ)
    (hkin : ∀ (f : ℝ → Lp ℝ 2 μ), Continuous f → ∀ (x : V × Lp ℝ 2 μ) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun s ↦ ((0 : V), f s)) s;
      (∫ s in (0 : ℝ)..t, (z s).2) = J (z t).1 - J x.1)
    {r : ℝ} (hr : 1 ≤ r) (N : C(V × Lp ℝ 2 μ, Lp ℝ 2 μ)) (hN : LocallyLipschitz N)
    (hNae : ∀ z, N z =ᵐ[μ] fun y ↦ Real.signedPower r (J z.1 y)) (x₀ : V × Lp ℝ 2 μ) {t : ℝ}
    (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t <
      S.mildLifespan ((ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk N) x₀) :
    let F := (ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk N
    let hF : LocallyLipschitz F := (LocallyLipschitz.const (0 : V)).prodMk hN
    let z := S.maximalMildSolution hF x₀
    (1 / 2 : ℝ) * autonomousWaveEnergy B (z t) -
        (∫ y, |J (z t).1 y| ^ (r + 1) ∂μ) / (r + 1) =
      (1 / 2 : ℝ) * autonomousWaveEnergy B x₀ -
        (∫ y, |J x₀.1 y| ^ (r + 1) ∂μ) / (r + 1) := by
  have hN' : LocallyLipschitz ((1 : ℝ) • N) := by
    simpa only [one_smul] using hN
  have hlt' : ENNReal.ofReal t < S.mildLifespan
      ((ContinuousMap.const (V × Lp ℝ 2 μ) (0 : V)).prodMk ((1 : ℝ) • N)) x₀ := by
    simpa only [one_smul] using hlt
  simpa only [one_smul, one_mul] using
    scaled_power_energy_maximalMildSolution S B hsymm henergy J hkin hr 1 N hN' hNae x₀ ht hlt'

end Hyperbolic.Variational
