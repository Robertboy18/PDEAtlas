/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletSobolev
public import PDE.Parabolic.Heat.Spectral.DomainEmbedding

/-!
# Classical derivative convergence of Dirichlet heat series

The iterated elliptic inverse followed by Sobolev embedding is a bounded map from
`L²` to `C^{j,γ}` on the closure. Applying it to sufficiently weighted spectral
series gives classical representatives with convergence of every derivative through
order `j` in the uniform norm. Time differentiation holds in the same Hölder graph
space. Representatives constructed at different orders agree on the closure.
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace HolderSpace MeasureTheory
open scoped Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)

/-- An iterated elliptic inverse with values in a classical Hölder derivative graph. -/
def dirichletHolderLiftCLM (j : ℕ) : DerivLp n 2 Ω →L[ℝ] CKGammaOn n j Ω γ :=
  (domainHolderCLM j hopen hbounded (hgraph 1) hγ).comp
    ((lowerOrderCLM (by omega : j + 1 + n ≤ (j + n + 1) * 2)).comp
      (iteratedDirichletSolveCLM hopen hbounded hgraph (j + n + 1)))

/-- The classical lift represents the base of the iterated weak inverse. -/
theorem dirichletHolderLiftCLM_ae (j : ℕ) (f : DerivLp n 2 Ω) :
    (dirichletHolderLiftCLM hopen hbounded hgraph hγ j f).interiorDerivative 0
      =ᵐ[domainMeasure n Ω]
        baseRepresentative (iteratedDirichletSolveCLM hopen hbounded hgraph (j + n + 1) f) := by
  have h := domainHolderCLM_ae j hopen hbounded (hgraph 1) hγ
      (lowerOrderCLM (by omega : j + 1 + n ≤ (j + n + 1) * 2)
        (iteratedDirichletSolveCLM hopen hbounded hgraph (j + n + 1) f))
  apply h.trans
  exact Filter.Eventually.of_forall (congrFun (baseRepresentative_lowerOrderCLM
    (by omega : j + 1 + n ≤ (j + n + 1) * 2)
    (iteratedDirichletSolveCLM hopen hbounded hgraph (j + n + 1) f)))

namespace DirichletHeatSpectrum

variable (S : DirichletHeatSpectrum n Ω)

/-- The `C^{j,γ}` representative of the `m`th weighted heat vector. -/
def holderPower (j m : ℕ) (f : DerivLp n 2 Ω) (t : ℝ) : CKGammaOn n j Ω γ :=
  dirichletHolderLiftCLM hopen hbounded hgraph hγ j
    (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + (j + n + 1)) f t)

/-- Classical smoothing preserves the weighted Hilbert heat vector almost everywhere. -/
theorem holderPower_ae (j m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    (S.holderPower hopen hbounded hgraph hγ j m f t).interiorDerivative 0
      =ᵐ[domainMeasure n Ω]
        ⇑(spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg m f t) := by
  have h := dirichletHolderLiftCLM_ae hopen hbounded hgraph hγ j
    (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + (j + n + 1)) f t)
  change _ =ᵐ[domainMeasure n Ω]
    (wkpBaseCoordinateCLM (S.sobolevPower hopen hbounded hgraph (j + n + 1) m f t) :
      ℝ^n → ℝ) at h
  rw [S.sobolevPower_base hopen hbounded hgraph _ _ f ht] at h
  exact h

/-- Time differentiation is valid in the full classical Hölder derivative graph. -/
theorem hasDerivAt_holderPower (j m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (S.holderPower hopen hbounded hgraph hγ j m f)
      (-S.holderPower hopen hbounded hgraph hγ j (m + 1) f t) t := by
  have h := (dirichletHolderLiftCLM hopen hbounded hgraph hγ j).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg
      (m + (j + n + 1)) f ht)
  rw [map_neg, show m + (j + n + 1) + 1 = (m + 1) + (j + n + 1) by omega] at h
  exact h

/-- Sufficiently weighted spectral sums converge in the classical Hölder norm. -/
theorem hasSum_holderPower (j m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasSum (fun i ↦
      (S.eigenvalue i ^ (m + (j + n + 1)) * Real.exp (-S.eigenvalue i * t) *
        S.basis.repr f i) • dirichletHolderLiftCLM hopen hbounded hgraph hγ j (S.basis i))
      (S.holderPower hopen hbounded hgraph hγ j m f t) := by
  unfold holderPower
  simpa only [map_smul] using
    (dirichletHolderLiftCLM hopen hbounded hgraph hγ j).hasSum
      (hasSum_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg
        (m + (j + n + 1)) f ht)

/-- Each derivative series converges uniformly on the domain closure. -/
theorem hasSum_holderPower_derivative (j m : ℕ) (a : MultiIndex n j)
    (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasSum (fun i ↦
      (S.eigenvalue i ^ (m + (j + n + 1)) * Real.exp (-S.eigenvalue i * t) *
        S.basis.repr f i) •
          (dirichletHolderLiftCLM hopen hbounded hgraph hγ j (S.basis i)).derivative a)
      ((S.holderPower hopen hbounded hgraph hγ j m f t).derivative a) := by
  simpa only [map_smul, CKGammaOn.derivativeCLM_apply] using
    (CKGammaOn.derivativeCLM a).hasSum
      (S.hasSum_holderPower hopen hbounded hgraph hγ j m f ht)

/-- Changing the classical order or Hölder exponent retains exactly one function
on the closure. -/
theorem holderPower_coherent {δ : Exponent} (hδ : (δ : ℝ) < 1)
    (j l m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    (S.holderPower hopen hbounded hgraph hγ j m f t).toBoundedContinuousFunction =
      (S.holderPower hopen hbounded hgraph hδ l m f t).toBoundedContinuousFunction :=
  CKGammaOn.toBoundedContinuousFunction_eq_of_ae_eq hopen
    ((S.holderPower_ae hopen hbounded hgraph hγ j m f ht).trans
      (S.holderPower_ae hopen hbounded hgraph hδ l m f ht).symm)

end DirichletHeatSpectrum

end HeatEquation
