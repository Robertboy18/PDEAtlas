/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.CompactData.ForwardEnergy
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardUniqueness
public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.GlobalObstruction

/-!
# Compact-data negative-energy obstruction

Compact displacement and velocity, negative initial energy, and the potential
inequality `z V'(z) ≤ Λ V(z)` with `Λ > 2` exclude a global forward classical
solution. The field is C² only at positive times and C¹ on the closed forward
half-space. Its initial velocity is the right derivative.

Finite propagation constructs support, compact cylinders construct all integral
majorants, and the initial energy limit supplies a negative positive-time slice.
Smooth localization above that slice then applies the concavity
obstruction. This applies that theorem to compactly supported data.

This is Evans, §12.5.1, Theorem 1, for classical rather than smooth solutions. As in Evans, the
compact support of the solution comes from the domain of dependence, §12.1.2, Theorem 3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 3; §12.5.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, Theorem I(A),
  pp. 4-5.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology BigOperators

namespace WaveEquation.NegativeEnergy

variable {n : ℕ}

/-- The superquadratic potential inequality forces zero to be an equilibrium.
Indeed, `Λ V(z) - z V'(z)` attains its minimum at zero. -/
theorem deriv_potential_zero_of_growth {V : ℝ → ℝ} {Λ : ℝ}
    (hV : ContDiff ℝ 2 V) (hVzero : V 0 = 0) (hΛ : 2 < Λ)
    (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z) : deriv V 0 = 0 := by
  have hmin : IsLocalMin (fun z ↦ Λ * V z - z * deriv V z) 0 := by
    refine Eventually.of_forall fun z ↦ ?_
    simpa [hVzero] using sub_nonneg.mpr (hgrowth z)
  have hd := ((hV.differentiable (by norm_num) 0).hasDerivAt.const_mul Λ).sub
    ((hasDerivAt_id 0).mul ((hV.differentiable_deriv_two 0).hasDerivAt))
  have he := hmin.hasDerivAt_eq_zero hd
  simp only [id_eq, one_mul, zero_mul, add_zero] at he
  have hm : (Λ - 1) * deriv V 0 = 0 := by nlinarith [he]
  exact (mul_eq_zero.mp hm).resolve_left (by linarith)

/-- Compact Cauchy data with negative energy admit no global forward classical
solution of `u_tt - Δu + V'(u) = 0` under the superquadratic potential inequality.
Support, domination, energy conservation and positive-time regularity are derived
in the proof. -/
theorem not_global_forward_semilinearWave_of_compact_negative_energy [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ} {Λ : ℝ} (hV : ContDiff ℝ 2 V) (hVzero : V 0 = 0)
    (hΛ : 2 < Λ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z) (hgcompact : HasCompactSupport g)
    (hhcompact : HasCompactSupport h)
    (henergy : (∫ x : ℝ^n, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x)) < 0)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n,
      waveOperator u (timeSpaceCons t x) + deriv V (u (timeSpaceCons t x)) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    False := by
  obtain ⟨Rg, _, hg⟩ := hgcompact.exists_pos_le_norm
  obtain ⟨Rh, _, hh⟩ := hhcompact.exists_pos_le_norm
  let R := max Rg Rh
  have hgR (x : ℝ^n) (hx : R < ‖x‖) : g x = 0 := hg x ((le_max_left Rg Rh).trans hx.le)
  have hhR (x : ℝ^n) (hx : R < ‖x‖) : h x = 0 := hh x ((le_max_right Rg Rh).trans hx.le)
  have hV₁ : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hf : LocallyLipschitz (deriv V) := hV.deriv'.locallyLipschitz
  have hs := hasForwardSupport_of_cauchyData hf
    (deriv_potential_zero_of_growth hV hVzero hΛ hgrowth) hu hu₀ hwave hpos hvel hgR hhR
  have hlimit := tendsto_semilinearWaveSpatialEnergy_initial hV.continuous hVzero
    hu₀ hs hpos hvel hhR
  have hnegative : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ semilinearWaveSpatialEnergy V u t < 0 := by
    filter_upwards [self_mem_nhdsWithin, hlimit.eventually (Iio_mem_nhds henergy)]
      with t ht he using And.intro ht he
  obtain ⟨t, ht, hEt⟩ := hnegative.exists
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_eqOn_forward hu (half_pos ht)
  have hUs (r : ℝ) (hr : t / 2 < r) (x : ℝ^n) (hx : R + r < ‖x‖) :
      U (timeSpaceCons r x) = 0 := by
    rw [hUeq (show t / 2 ≤ (timeSpaceCons r x) 0 by simpa using hr.le)]
    exact hs r (by linarith) x hx
  have hUE : semilinearWaveSpatialEnergy V U t = semilinearWaveSpatialEnergy V u t := by
    apply integral_congr_ae
    refine Eventually.of_forall fun x ↦ ?_
    have hp : t / 2 < (timeSpaceCons t x) 0 := by simpa using half_lt_self ht
    unfold semilinearWaveSpatialEnergyDensity semilinearWaveEnergyDensity
    rw [classicalWaveEnergyDensity_congr_nhds (eventuallyEq_of_eqOn_forward hUeq hp), hUeq hp.le]
  apply WaveEquation.not_global_forward_semilinearWave_of_negative_energy hVzero hV₁ hU
    hΛ hgrowth (t₀ := t) ?_ ((dominatedVirialDataOfConeSupport hU hUs).mono
      (show Ici t ⊆ Ioi (t / 2) from fun _ hr ↦ (half_lt_self ht).trans_le hr))
    ((dominatedEnergyDataOfConeSupport hV₁ hVzero hU hUs).mono
      (show Ici t ⊆ Ioi (t / 2) from fun _ hr ↦ (half_lt_self ht).trans_le hr)) (hUE.symm ▸ hEt)
  intro r hr x
  have hp : t / 2 < (timeSpaceCons r x) 0 := by simp only [timeSpaceCons_zero]; linarith
  unfold semilinearWaveOperator
  rw [waveOperator_congr_nhds (eventuallyEq_of_eqOn_forward hUeq hp), hUeq hp.le]
  exact hwave r (ht.trans_le hr) x

end WaveEquation.NegativeEnergy
