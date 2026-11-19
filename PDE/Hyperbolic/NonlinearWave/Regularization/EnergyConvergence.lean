/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Topology.UniformConvergence
public import PDE.FDeriv.PartialDeriv.Regularity
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ConeFlux

/-!
# Convergence of wave energy and flux

A field and its first derivatives determine both the energy density and the outgoing null flux.
Locally uniform convergence of this first-order data therefore passes to both quantities. We use
continuity of the potential and of the chosen normal.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace WaveEquation

/-- Continuous first coordinate derivatives assemble into a continuous spatial gradient. -/
theorem continuousOn_classicalWaveSpatialGradient {n : ℕ} {u : ℝ^(n + 1) → ℝ}
    {S : Set (ℝ^(n + 1))} (hu : ContDiffOn ℝ 1 u S) (hS : IsOpen S) :
    ContinuousOn (classicalWaveSpatialGradient u) S :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_continuousOn
    (continuousOn_pi.mpr fun j ↦ hu.continuousOn_partialDeriv j.succ hS)

/-- Convergence of the spatial coordinate derivatives gives convergence of the gradient. -/
theorem tendstoLocallyUniformlyOn_classicalWaveSpatialGradient {n : ℕ} {ι : Type*}
    {U : ι → ℝ^(n + 1) → ℝ} {u : ℝ^(n + 1) → ℝ} {l : Filter ι} {S : Set (ℝ^(n + 1))}
    (hD : ∀ j : Fin n, TendstoLocallyUniformlyOn (fun i ↦ ∂[j.succ] (U i)) (∂[j.succ] u) l S) :
    TendstoLocallyUniformlyOn (fun i ↦ classicalWaveSpatialGradient (U i))
      (classicalWaveSpatialGradient u) l S :=
  (PiLp.uniformContinuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_tendstoLocallyUniformlyOn
    (PDE.tendstoLocallyUniformlyOn_pi.mpr hD)

/-- Locally uniform convergence of a field and its first derivatives preserves
its semilinear energy density for every continuous potential. -/
theorem tendstoLocallyUniformlyOn_semilinearWaveEnergyDensity {n : ℕ} {ι : Type*}
    {U : ι → ℝ^(n + 1) → ℝ} {u : ℝ^(n + 1) → ℝ} {V : ℝ → ℝ} {l : Filter ι} {S : Set (ℝ^(n + 1))}
    (hV : Continuous V) (hu : ContDiffOn ℝ 1 u S) (hS : IsOpen S)
    (hU : TendstoLocallyUniformlyOn U u l S)
    (hD : ∀ j : Fin (n + 1), TendstoLocallyUniformlyOn (fun i ↦ ∂[j] (U i)) (∂[j] u) l S) :
    TendstoLocallyUniformlyOn (fun i ↦ semilinearWaveEnergyDensity V (U i))
      (semilinearWaveEnergyDensity V u) l S := by
  have hgrad := tendstoLocallyUniformlyOn_classicalWaveSpatialGradient (fun j ↦ hD j.succ)
  have hc : Continuous (fun q : (ℝ × ℝ^n) × ℝ ↦
      (1 / 2 : ℝ) * (q.1.1 ^ 2 + ‖q.1.2‖ ^ 2) + V q.2) := by fun_prop
  exact hc.comp_tendstoLocallyUniformlyOn (((hD 0).prodMk hgrad).prodMk hU)
    (((hu.continuousOn_partialDeriv 0 hS).prodMk
      (continuousOn_classicalWaveSpatialGradient hu hS)).prodMk hu.continuousOn)

/-- The null flux has the same locally uniform limit whenever the chosen normal
is continuous. This applies to a cone truncated strictly before its vertex. -/
theorem tendstoLocallyUniformlyOn_semilinearWaveNullFlux {n : ℕ} {ι : Type*} {U : ι → ℝ^(n + 1) → ℝ}
    {u : ℝ^(n + 1) → ℝ} {V : ℝ → ℝ} {ν : ℝ^(n + 1) → ℝ^n} {l : Filter ι} {S : Set (ℝ^(n + 1))}
    (hV : Continuous V) (hu : ContDiffOn ℝ 1 u S) (hS : IsOpen S) (hν : ContinuousOn ν S)
    (hU : TendstoLocallyUniformlyOn U u l S)
    (hD : ∀ j : Fin (n + 1), TendstoLocallyUniformlyOn (fun i ↦ ∂[j] (U i)) (∂[j] u) l S) :
    TendstoLocallyUniformlyOn (fun i p ↦ semilinearWaveNullFlux V (U i) p (ν p))
      (fun p ↦ semilinearWaveNullFlux V u p (ν p)) l S := by
  have hgrad : TendstoLocallyUniformlyOn
      (fun i ↦ classicalWaveSpatialGradient (U i)) (classicalWaveSpatialGradient u) l S :=
    tendstoLocallyUniformlyOn_classicalWaveSpatialGradient (fun j ↦ hD j.succ)
  have hnormal : TendstoLocallyUniformlyOn (fun _ : ι ↦ ν) ν l S := by
    intro W hW p _
    refine ⟨S, self_mem_nhdsWithin, Eventually.of_forall fun i y _ ↦ ?_⟩
    exact refl_mem_uniformity hW
  let J := fun i p ↦ (((∂[0] (U i)) p, classicalWaveSpatialGradient (U i) p), U i p)
  let j := fun p ↦ (((∂[0] u) p, classicalWaveSpatialGradient u p), u p)
  have hJ : TendstoLocallyUniformlyOn J j l S := ((hD 0).prodMk hgrad).prodMk hU
  have hj : ContinuousOn j S := ((hu.continuousOn_partialDeriv 0 hS).prodMk
      (continuousOn_classicalWaveSpatialGradient hu hS)).prodMk hu.continuousOn
  let G := fun q : ((ℝ × ℝ^n) × ℝ) × ℝ^n ↦ (1 / 2 : ℝ) * ‖q.1.1.1 • q.2 - q.1.1.2‖ ^ 2 + V q.1.2
  have hc : Continuous G := by
    have hd : Continuous (fun q : ((ℝ × ℝ^n) × ℝ) × ℝ^n ↦ q.1.1.1 • q.2 - q.1.1.2) :=
      (continuous_fst.fst.fst.smul continuous_snd).sub continuous_fst.fst.snd
    exact (continuous_const.mul (hd.norm.pow 2)).add (hV.comp continuous_fst.snd)
  have hfull : TendstoLocallyUniformlyOn (fun i p ↦ (J i p, ν p))
      (fun p ↦ (j p, ν p)) l S := hJ.prodMk hnormal
  have hfullc : ContinuousOn (fun p ↦ (j p, ν p)) S := hj.prodMk hν
  change TendstoLocallyUniformlyOn (fun i p ↦ G (J i p, ν p)) (fun p ↦ G (j p, ν p)) l S
  exact hc.comp_tendstoLocallyUniformlyOn hfull hfullc

end WaveEquation
