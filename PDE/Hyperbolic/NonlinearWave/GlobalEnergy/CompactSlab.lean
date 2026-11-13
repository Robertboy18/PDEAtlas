/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSupport
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Energy on a closed forward slab

Common compact support justifies continuity at the initial time without
assuming any support at negative times. Integration of the interior energy
identity then gives conservation up to both endpoints.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Uniform support on a closed forward slab justifies energy continuity at both endpoints. -/
theorem continuousOn_semilinearWaveSpatialEnergy_of_compact_support {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {K : Set (ℝ^n)} {T : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K) (hT : 0 < T) (hs : ∀ t ∈ Icc 0 T, ∀ x ∉ K, u (timeSpaceCons t x) = 0) :
    ContinuousOn (semilinearWaveSpatialEnergy V u) (Icc 0 T) := by
  have hc : Continuous (Function.uncurry (semilinearWaveSpatialEnergyDensity V u)) :=
    (contDiff_semilinearWaveEnergyDensity hV hu).continuous.comp
      (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous
  have heq (x : ℝ^n) (hx : x ∉ K) :
      EqOn (fun t ↦ semilinearWaveSpatialEnergyDensity V u t x) (fun _ ↦ 0) (Icc 0 T) := by
    have hz : EqOn (fun t ↦ semilinearWaveSpatialEnergyDensity V u t x) (fun _ ↦ 0) (Ioo 0 T) :=
      fun t ht ↦ semilinearWaveSpatialEnergyDensity_eq_zero_off_support hVzero isOpen_Ioo
        hK.isClosed (fun _ _ _ ↦ (hu.of_le (by norm_num)).contDiffAt)
        (fun s hsI y hy ↦ hs s (Ioo_subset_Icc_self hsI) y hy) ht hx
    have hcl := hz.closure (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
    simpa only [closure_Ioo hT.ne] using hcl
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hc hK
  exact hi.continuousOn.congr fun t ht ↦ (setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (fun x hx ↦ heq x hx ht)).symm

/-- Energy is conserved on a closed slab with common compact support. In
particular the initial endpoint uses continuity, not support at negative times. -/
theorem semilinearWaveSpatialEnergy_eq_of_compact_support_on_Icc {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {K : Set (ℝ^n)} {T : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 2 u)
    (hK : IsCompact K) (hT : 0 < T) (hs : ∀ t ∈ Icc 0 T, ∀ x ∉ K, u (timeSpaceCons t x) = 0)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    semilinearWaveSpatialEnergy V u t = semilinearWaveSpatialEnergy V u 0 := by
  have hc := continuousOn_semilinearWaveSpatialEnergy_of_compact_support hV hVzero hu hK hT hs
  have hd (s : ℝ) (hsI : s ∈ interior (Icc 0 T)) :
      HasDerivAt (semilinearWaveSpatialEnergy V u) 0 s := by
    rw [interior_Icc] at hsI
    exact hasDerivAt_semilinearWaveSpatialEnergy_of_compact_support hV hVzero
      isOpen_Ioo hK (fun _ _ _ ↦ hu.contDiffAt)
      (fun r hr x hx ↦ hs r (Ioo_subset_Icc_self hr) x hx) hsI (hwave s hsI)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T) hc
    (fun s hsI ↦ (hd s hsI).hasDerivWithinAt) (fun _ _ ↦ le_rfl)
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) T) hc
    (fun s hsI ↦ (hd s hsI).hasDerivWithinAt) (fun _ _ ↦ le_rfl)
  exact le_antisymm (ha ⟨le_rfl, hT.le⟩ ht ht.1) (hm ⟨le_rfl, hT.le⟩ ht ht.1)

end WaveEquation
