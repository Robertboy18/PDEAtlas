/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletPowers
public import PDE.Parabolic.Heat.Spectral.DirichletRegularity

/-!
# Spectral heat smoothing in every Sobolev order

Iterating the bounded Dirichlet inverse maps the eigenvalue-weighted `L²` series
to higher Sobolev spaces. The base coordinate identifies each lifted series with
the original heat vector. Convergence and time derivatives therefore hold
in every even Sobolev order, for arbitrary initial `L²` data.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)

/-- Iterating the geometrically constructed inverse gains two derivatives per step. -/
def iteratedDirichletSolveCLM : (k : ℕ) → DerivLp n 2 Ω →L[ℝ] W^{k * 2,2}(Ω)
  | 0 => orderZeroSobolevCLM
  | k + 1 =>
      (lowerOrderCLM (by omega : (k + 1) * 2 ≤ k * 2 + 2)).comp
        ((dirichletHigherSolveCLM (k * 2) hopen hbounded (by
          exact_mod_cast hgraph (k * 2 + 2))).comp (iteratedDirichletSolveCLM k))

/-- At order zero the iterated inverse is the canonical `L²` Sobolev conversion. -/
theorem iteratedDirichletSolveCLM_zero_base (f : DerivLp n 2 Ω) :
    wkpBaseCoordinateCLM (iteratedDirichletSolveCLM hopen hbounded hgraph 0 f) = f :=
  orderZeroSobolevCLM_base f

/-- Each iteration applies one more weak Dirichlet inverse to the base coordinate. -/
theorem iteratedDirichletSolveCLM_succ_base (k : ℕ) (f : DerivLp n 2 Ω) :
    wkpBaseCoordinateCLM (iteratedDirichletSolveCLM hopen hbounded hgraph (k + 1) f) =
      baseCoordCLM (dirichletSolveCLM (Fact.out : 0 < n) hbounded
        (wkpBaseCoordinateCLM (iteratedDirichletSolveCLM hopen hbounded hgraph k f))) := by
  apply MeasureTheory.Lp.ext
  have hbase := baseRepresentative_lowerOrderCLM (by omega : (k + 1) * 2 ≤ k * 2 + 2)
    (dirichletHigherSolveCLM (k * 2) hopen hbounded (by
      exact_mod_cast hgraph (k * 2 + 2)) (iteratedDirichletSolveCLM hopen hbounded hgraph k f))
  apply Filter.EventuallyEq.trans (Filter.Eventually.of_forall (congrFun hbase))
  exact Filter.Eventually.of_forall fun x ↦ congrArg (fun F : DerivLp n 2 Ω ↦ F x)
    (dirichletHigherSolveCLM_base (k * 2) hopen hbounded (by
      exact_mod_cast hgraph (k * 2 + 2)) (iteratedDirichletSolveCLM hopen hbounded hgraph k f))

namespace DirichletHeatSpectrum

variable (S : DirichletHeatSpectrum n Ω)

/-- The `H^{2k}` representative of an eigenvalue-weighted heat vector. -/
def sobolevPower (k m : ℕ) (f : DerivLp n 2 Ω) (t : ℝ) : W^{k * 2,2}(Ω) :=
  iteratedDirichletSolveCLM hopen hbounded hgraph k
    (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + k) f t)

/-- Every lifted trajectory represents the original weighted Hilbert vector. -/
theorem sobolevPower_base (k m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    wkpBaseCoordinateCLM (S.sobolevPower hopen hbounded hgraph k m f t) =
      spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg m f t := by
  induction k generalizing m with
  | zero => exact iteratedDirichletSolveCLM_zero_base hopen hbounded hgraph _
  | succ k ih =>
    unfold sobolevPower
    rw [iteratedDirichletSolveCLM_succ_base]
    rw [show m + (k + 1) = (m + 1) + k by omega]
    rw [show wkpBaseCoordinateCLM
        (iteratedDirichletSolveCLM hopen hbounded hgraph k
          (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg ((m + 1) + k) f t)) =
        spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + 1) f t from ih (m + 1)]
    exact S.energyPower_base (Fact.out : 0 < n) hbounded m f ht

/-- The weighted spectral series converges after applying the iterated inverse,
in the full `H^{2k}` norm. -/
theorem hasSum_sobolevPower (k m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasSum (fun i ↦ (S.eigenvalue i ^ (m + k) * Real.exp (-S.eigenvalue i * t) *
      S.basis.repr f i) • iteratedDirichletSolveCLM hopen hbounded hgraph k (S.basis i))
      (S.sobolevPower hopen hbounded hgraph k m f t) := by
  unfold sobolevPower
  simpa only [map_smul] using
    (iteratedDirichletSolveCLM hopen hbounded hgraph k).hasSum
      (hasSum_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + k) f ht)

/-- Positive-time differentiation holds in each higher Sobolev norm. -/
theorem hasDerivAt_sobolevPower (k m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (S.sobolevPower hopen hbounded hgraph k m f)
      (-S.sobolevPower hopen hbounded hgraph k (m + 1) f t) t := by
  have h := (iteratedDirichletSolveCLM hopen hbounded hgraph k).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + k) f ht)
  rw [map_neg, show m + k + 1 = (m + 1) + k by omega] at h
  exact h

end DirichletHeatSpectrum

end HeatEquation
