/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongEvolution

/-!
# Spatial regularity transfer for the nonlinear wave

A continuous higher Sobolev lift of the source upgrades the original
energy solution, with its original initial data. The proof constructs the
higher trajectory by Duhamel's formula and identifies its projection through
the weak equation. Only nonnegative times enter this identification.

The successor step separates nonlinear composition from wave propagation:
a continuous composition operator on Hᵏ upgrades a continuous Hᵏ displacement
to an Hᵏ⁺¹ × Hᵏ trajectory. Its composition hypotheses concern an operator on
the entire Sobolev space. Establishing those hypotheses from a scalar reaction
is a separate analytic obligation; this transfer theorem alone is not a
classical existence theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n k : ℕ} {f : ℝ → ℝ} {L : NNReal}
  {hf : LipschitzWith L f} {hf0 : f 0 = 0}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- A higher Sobolev lift of the source determines a higher trajectory
of the same weak energy solution, including both initial values. -/
theorem IsEnergySolution.exists_continuous_higherOrder_of_source
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) u)
    (g : C(ℝ, W^{k,2}(ℝ^n)))
    (hg : ∀ t : ℝ, 0 ≤ t →
      wkpBaseCoordinateCLM (g t) = source hf hf0 (u t).1) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = u t := by
  let F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) := fun s ↦ (0, g s)
  obtain ⟨U, hU₀, hU⟩ := exists_continuous_higherOrder_forced n k x
    (show Continuous F from continuous_const.prodMk g.continuous)
  refine ⟨U, hU₀, fun t ht ↦ ?_⟩
  have hforcing : (linearSemigroup n).duhamel (fun s ↦ higherEnergyInclusionCLM n k (F s)) t =
        (linearSemigroup n).duhamel
          (fun s ↦ (C).symm (0, source hf hf0 (u s).1)) t := by
    refine (linearSemigroup n).duhamel_congr ht fun s hs ↦ ?_
    apply (C).injective
    rw [coordinates_higherEnergyInclusionCLM, ContinuousLinearEquiv.apply_symm_apply]
    change (lowerOrderCLM _ 0, wkpBaseCoordinateCLM (g s)) = _
    rw [map_zero, hg s hs.1]
  have heq : higherEnergyInclusionCLM n k (U t) = (C).symm (u t) := by
    rw [hU t, hforcing, h.mild_eq ht]
    rfl
  have hc := congrArg C heq
  simpa only [coordinates_higherEnergyInclusionCLM, ContinuousLinearEquiv.apply_symm_apply] using hc

/-- Continuous composition on Hᵏ supplies the forcing for the next wave
energy level. The resulting displacement and velocity belong to the original
energy solution, rather than to an unrelated higher-order construction. -/
theorem IsEnergySolution.exists_continuous_succOrder
    (hk : 1 ≤ k)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) u)
    (N : C(W^{k,2}(ℝ^n), W^{k,2}(ℝ^n)))
    (hN : ∀ q : W^{k,2}(ℝ^n),
      wkpBaseCoordinateCLM (N q) = hf.compLp hf0 (wkpBaseCoordinateCLM q))
    (q : C(ℝ, W^{k,2}(ℝ^n)))
    (hq : ∀ t : ℝ, 0 ≤ t → lowerOrderCLM hk (q t) = (u t).1) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = u t := by
  let g : C(ℝ, W^{k,2}(ℝ^n)) := ⟨fun t ↦ q t - N (q t),
    q.continuous.sub (N.continuous.comp q.continuous)⟩
  refine h.exists_continuous_higherOrder_of_source x g fun t ht ↦ ?_
  change wkpBaseCoordinateCLM (q t - N (q t)) = _
  rw [map_sub, hN]
  have hbase : wkpBaseCoordinateCLM (q t) = (energyTriple n).inclusion (u t).1 :=
    congrArg (energyTriple n).inclusion (hq t ht)
  rw [hbase]
  rfl

/-- Continuous scalar composition lifts through order `k` propagate the
Sobolev energy level Hᵏ⁺¹ × Hᵏ from the data. The induction constructs the trajectory at each level.
The lifts must be established separately for the scalar reaction. -/
theorem IsEnergySolution.exists_continuous_higherOrder
    (k : ℕ)
    (N : ∀ j : Fin k, C(W^{j.val + 1,2}(ℝ^n), W^{j.val + 1,2}(ℝ^n)))
    (hN : ∀ (j : Fin k) (q : W^{j.val + 1,2}(ℝ^n)),
      wkpBaseCoordinateCLM (N j q) = hf.compLp hf0 (wkpBaseCoordinateCLM q))
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) u) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = u t := by
  induction k with
  | zero =>
    let U : C(ℝ, H¹(ℝ^n) × W^{0,2}(ℝ^n)) := ⟨fun t ↦ (zeroOrderEnergyEquiv n).symm ((C).symm (u t)),
        (zeroOrderEnergyEquiv n).symm.continuous.comp ((C).symm.continuous.comp u.continuous)⟩
    have hproj (t : ℝ) :
        (lowerOrderCLM (by decide : 1 ≤ 0 + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = u t := by
      have hz := (zeroOrderEnergyEquiv n).apply_symm_apply ((C).symm (u t))
      have hc := congrArg C hz
      change C (zeroOrderEnergyEquiv n (U t)) = C ((C).symm (u t)) at hc
      rw [ContinuousLinearEquiv.apply_symm_apply] at hc
      change ((U t).1, wkpBaseCoordinateCLM (U t).2) = u t at hc
      simpa only [lowerOrderCLM_refl_apply] using hc
    refine ⟨U, ?_, fun t _ ↦ hproj t⟩
    apply higherEnergyInclusionCLM_injective n 0
    apply (C).injective
    rw [coordinates_higherEnergyInclusionCLM, coordinates_higherEnergyInclusionCLM,
      hproj, h.initial]
  | succ j ih =>
    let y : W^{j + 1,2}(ℝ^n) × W^{j,2}(ℝ^n) :=
      (lowerOrderCLM (Nat.le_succ (j + 1)) x.1, lowerOrderCLM (Nat.le_succ j) x.2)
    have hy : IsEnergySolution hf hf0
        (lowerOrderCLM (by omega : 1 ≤ j + 1) y.1, wkpBaseCoordinateCLM y.2) u := by
      change IsEnergySolution hf hf0
        (lowerOrderCLM _ (lowerOrderCLM _ x.1), wkpBaseCoordinateCLM x.2) u
      simpa only [lowerOrderCLM_trans_apply] using h
    obtain ⟨V, _, hV⟩ := ih (fun i ↦ N i.castSucc) (fun i ↦ hN i.castSucc) y hy
    exact h.exists_continuous_succOrder (Nat.succ_pos j) x (N (Fin.last j)) (hN (Fin.last j))
      ⟨fun t ↦ (V t).1, V.continuous.fst⟩ (fun t ht ↦ congrArg Prod.fst (hV t ht))

end PDE.Hyperbolic.NonlinearWave.Cauchy
