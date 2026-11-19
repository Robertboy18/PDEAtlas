/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactEnergy.Cutoff
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
public import PDE.Hyperbolic.NonlinearWave.Momentum.Balance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.Support

/-! # Exact compact-cutoff energy and momentum identities -/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common PDE.Analysis
open scoped ContDiff Topology

namespace WaveEquation

variable {n : ℕ}

/-- Physical energy paired with a fixed compact spatial cutoff. -/
def cutoffEnergy (χ : ℝ^n → ℝ) (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (r : ℝ) : ℝ :=
  ∫ x, χ x * semilinearWaveEnergyDensity V u (timeSpaceCons r x)

/-- Momentum paired with the spatial gradient of the cutoff. -/
def cutoffMomentum (χ : ℝ^n → ℝ) (u : ℝ^(n + 1) → ℝ) (r : ℝ) : ℝ :=
  ∑ i : Fin n, ∫ x, (∂[i] χ) x * classicalWaveEnergyFlux u i (timeSpaceCons r x)

/-- Spatial stress paired with the Hessian of the cutoff. -/
def cutoffStress (χ : ℝ^n → ℝ) (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (r : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ∫ x, (∂[j] (∂[i] χ)) x * waveSpatialStress V u i j (timeSpaceCons r x)

/-- The derivative of cutoff energy is minus cutoff momentum on a wave. -/
theorem hasDerivAt_cutoffEnergy {χ : ℝ^n → ℝ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ I, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons r x)) {r : ℝ} (hr : r ∈ I)
    (hw : ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0) :
    HasDerivAt (cutoffEnergy χ V u) (-cutoffMomentum χ u r) r := by
  have hd := hasDerivAt_cutoffPairing hI hχ.continuous hc
    (fun s hs x ↦ contDiffAt_semilinearWaveEnergyDensity hV.contDiffAt (hu s hs x)) hr
  have he (x : ℝ^n) : (∂[0] (semilinearWaveEnergyDensity V u)) (timeSpaceCons r x) =
        ∑ j : Fin n, (∂[j.succ] (classicalWaveEnergyFlux u j)) (timeSpaceCons r x) := by
    have hz := semilinearWaveEnergyBalanceResidual_eq_zero hV (hu r hr x) (hw x)
    rw [semilinearWaveEnergyBalanceResidual_eq_partialDeriv_sub_sum hV (hu r hr x),
      sub_eq_zero] at hz
    exact hz
  simp_rw [he] at hd
  rw [integral_cutoff_spatialDivergence r hχ hc
    (fun j x ↦ contDiffAt_classicalWaveEnergyFlux (hu r hr x) j)] at hd
  exact hd

/-- The derivative of cutoff momentum is minus the cutoff stress integral. -/
theorem hasDerivAt_cutoffMomentum {χ : ℝ^n → ℝ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ I, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons r x)) {r : ℝ} (hr : r ∈ I)
    (hw : ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0) :
    HasDerivAt (cutoffMomentum χ u) (-cutoffStress χ V u r) r := by
  have hd (i : Fin n) :
      HasDerivAt (fun s ↦ ∫ x, (∂[i] χ) x * classicalWaveEnergyFlux u i (timeSpaceCons s x))
        (-∑ j : Fin n,
          ∫ x, (∂[j] (∂[i] χ)) x * waveSpatialStress V u i j (timeSpaceCons r x)) r := by
    have hi := hasDerivAt_cutoffPairing hI (hχ.partialDeriv i (k := 1)).continuous
      (hc.partialDeriv i) (fun s hs x ↦ contDiffAt_classicalWaveEnergyFlux (hu s hs x) i) hr
    have he (x : ℝ^n) : (∂[0] (classicalWaveEnergyFlux u i)) (timeSpaceCons r x) =
          ∑ j : Fin n, (∂[j.succ] (waveSpatialStress V u i j)) (timeSpaceCons r x) := by
      have hz := waveSpatialStress_balance hV.contDiffAt (hu r hr x) i
      rw [hw x, mul_zero, sub_eq_zero] at hz
      exact hz
    simp_rw [he] at hi
    rw [integral_cutoff_spatialDivergence r (hχ.partialDeriv i (k := 1)) (hc.partialDeriv i)
      (fun j x ↦ contDiffAt_waveSpatialStress hV.contDiffAt (hu r hr x) i j)] at hi
    exact hi
  unfold cutoffMomentum cutoffStress
  rw [← Finset.sum_neg_distrib]
  exact HasDerivAt.fun_sum fun i _ ↦ hd i

/-- Each Hessian-stress integral is continuous on the regularity band. -/
theorem continuousOn_cutoffStress {χ : ℝ^n → ℝ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {I : Set ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ I, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons r x)) :
    ContinuousOn (cutoffStress χ V u) I := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact continuousOn_cutoffPairing
    (((hχ.partialDeriv i (k := 1)).partialDeriv j (k := 0)).continuous)
    ((hc.partialDeriv i).partialDeriv j)
    (fun r hr x ↦ (contDiffAt_waveSpatialStress hV.contDiffAt (hu r hr x) i j).continuousAt)

/-- Integrating the two balances gives a finite-time weighted stress identity.
The PDE is only required in the interior; the regularity band includes both endpoints. -/
theorem cutoffEnergy_sub_eq_timeWeightedStress {χ : ℝ^n → ℝ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {I : Set ℝ} {s t : ℝ} (hI : IsOpen I) (hst : s ≤ t) (hband : Icc s t ⊆ I) (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ I, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons r x))
    (hw : ∀ r ∈ Ioo s t, ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0) :
    cutoffEnergy χ V u t - cutoffEnergy χ V u s = (∫ r in s..t, (t - r) * cutoffStress χ V u r) -
      (t - s) * cutoffMomentum χ u s := by
  have hG : ContinuousOn (cutoffEnergy χ V u) I := continuousOn_cutoffPairing hχ.continuous hc
      (fun r hr x ↦ (contDiffAt_semilinearWaveEnergyDensity hV.contDiffAt (hu r hr x)).continuousAt)
  have hQ : ContinuousOn (cutoffMomentum χ u) I := by
    unfold cutoffMomentum
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_cutoffPairing (hχ.partialDeriv i (k := 1)).continuous (hc.partialDeriv i)
      (fun r hr x ↦ (contDiffAt_classicalWaveEnergyFlux (hu r hr x) i).continuousAt)
  have hH := continuousOn_cutoffStress hχ hc hV hu
  have hF : ContinuousOn
      (fun r ↦ cutoffEnergy χ V u r - (t - r) * cutoffMomentum χ u r) (Icc s t) :=
    (hG.sub ((continuous_const.sub continuous_id).continuousOn.mul hQ)).mono hband
  have hder (r : ℝ) (hr : r ∈ Ioo s t) :
      HasDerivAt (fun r ↦ cutoffEnergy χ V u r - (t - r) * cutoffMomentum χ u r)
        ((t - r) * cutoffStress χ V u r) r := by
    have hi := hband ⟨hr.1.le, hr.2.le⟩
    have hgd := hasDerivAt_cutoffEnergy hI (hχ.of_le (by norm_num)) hc hV hu hi (hw r hr)
    have hqd := hasDerivAt_cutoffMomentum hI hχ hc hV hu hi (hw r hr)
    have hlin : HasDerivAt (fun z : ℝ ↦ t - z) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub t
    convert hgd.fun_sub (hlin.fun_mul hqd) using 1
    ring
  have hint : IntervalIntegrable (fun r ↦ (t - r) * cutoffStress χ V u r) volume s t :=
    ContinuousOn.intervalIntegrable_of_Icc hst
      (((continuous_const.sub continuous_id).continuousOn.mul hH).mono hband)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hF hder hint
  simp only [sub_self, zero_mul, sub_zero] at he
  linarith

/-- Capturing the endpoint energy supports and being constant near initial momentum
removes all endpoint cutoff terms. -/
theorem energy_sub_eq_timeWeightedStress_of_endpoint_supports {χ : ℝ^n → ℝ} {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {I : Set ℝ} {s t : ℝ} (hI : IsOpen I) (hst : s ≤ t) (hband : Icc s t ⊆ I)
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ I, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons r x))
    (hw : ∀ r ∈ Ioo s t, ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0)
    (hstart : ∀ x ∈ tsupport (semilinearWaveSpatialEnergyDensity V u s), χ x = 1)
    (hend : ∀ x ∈ tsupport (semilinearWaveSpatialEnergyDensity V u t), χ x = 1)
    (hmom : ∀ i : Fin n, ∀ x ∈ tsupport (fun y ↦ classicalWaveEnergyFlux u i (timeSpaceCons s y)),
      χ =ᶠ[nhds x] fun _ ↦ (1 : ℝ)) :
    semilinearWaveSpatialEnergy V u t - semilinearWaveSpatialEnergy V u s = ∫ r in s..t,
      (t - r) * cutoffStress χ V u r := by
  have hcap (r : ℝ) (hcov : ∀ x ∈ tsupport (semilinearWaveSpatialEnergyDensity V u r), χ x = 1) :
      cutoffEnergy χ V u r = semilinearWaveSpatialEnergy V u r := by
    unfold cutoffEnergy semilinearWaveSpatialEnergy
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport (semilinearWaveSpatialEnergyDensity V u r)
    · rw [hcov x hx, one_mul]
      rfl
    · have hz := image_eq_zero_of_notMem_tsupport hx
      change χ x * semilinearWaveSpatialEnergyDensity V u r x =
        semilinearWaveSpatialEnergyDensity V u r x
      rw [hz, mul_zero]
  have hq : cutoffMomentum χ u s = 0 := by
    unfold cutoffMomentum
    apply Finset.sum_eq_zero
    intro i _
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    change (∂[i] χ) x * classicalWaveEnergyFlux u i (timeSpaceCons s x) = 0
    by_cases hx : x ∈ tsupport (fun y ↦ classicalWaveEnergyFlux u i (timeSpaceCons s y))
    · rw [PDE.partialDeriv_congr_nhds i (hmom i x hx), PDE.partialDeriv_const, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have he := cutoffEnergy_sub_eq_timeWeightedStress hI hst hband hχ hc hV hu hw
  rwa [hcap s hstart, hcap t hend, hq, mul_zero, sub_zero] at he

end WaveEquation
