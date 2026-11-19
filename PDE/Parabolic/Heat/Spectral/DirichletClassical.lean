/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletHolder
public import PDE.Elliptic.Regularity.Interior.ClassicalPoisson
import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary

/-!
# The classical heat equation for the Dirichlet spectral sum

The order-two Hölder representative defines one function. Coherence with every higher
representative proves spatial smoothness. Its time derivative is minus the next
weighted representative, while the weak Poisson equation identifies that representative
with minus its Laplacian. The energy-space trace gives zero values on the geometric
boundary.

Initial data are arbitrary `L²` classes, and the statements concern positive time.
-/

@[expose] public section

noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace HolderSpace MeasureTheory Set
open scoped Sobolev ENNReal ContDiff

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- A single classical representative of each weighted Dirichlet heat series.
The ambient expression is extended by zero outside the closure. -/
def classicalPower (m : ℕ) (f : DerivLp n 2 Ω) (t : ℝ) : ℝ^n → ℝ :=
  (S.holderPower hopen hbounded hgraph hγ 2 m f t).interiorDerivative 0

/-- The classical function represents the weighted Hilbert sum. -/
theorem classicalPower_ae (m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    S.classicalPower hopen hbounded hgraph hγ m f t =ᵐ[domainMeasure n Ω]
      ⇑(spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg m f t) :=
  S.holderPower_ae hopen hbounded hgraph hγ 2 m f ht

/-- Any higher Hölder representative gives the same ambient expression. -/
theorem classicalPower_eq_holderPower (j m : ℕ) (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) :
    S.classicalPower hopen hbounded hgraph hγ m f t =
      (S.holderPower hopen hbounded hgraph hγ j m f t).interiorDerivative 0 := by
  change Function.extend Subtype.val
      (S.holderPower hopen hbounded hgraph hγ 2 m f t).toBoundedContinuousFunction 0 =
    Function.extend Subtype.val
      (S.holderPower hopen hbounded hgraph hγ j m f t).toBoundedContinuousFunction 0
  rw [S.holderPower_coherent hopen hbounded hgraph hγ hγ 2 j m f ht]

/-- Every weighted classical heat sum is spatially smooth in the domain. -/
theorem contDiffOn_classicalPower (m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    ContDiffOn ℝ ∞ (S.classicalPower hopen hbounded hgraph hγ m f t) Ω := by
  apply contDiffOn_infty.mpr
  intro j
  rw [S.classicalPower_eq_holderPower hopen hbounded hgraph hγ j m f ht]
  exact (S.holderPower hopen hbounded hgraph hγ j m f t).contDiffOn_derivative
    hopen j 0 (by simp)

/-- Every weighted classical sum extends continuously to the closure. -/
theorem continuousOn_classicalPower (m : ℕ) (f : DerivLp n 2 Ω) (t : ℝ) :
    ContinuousOn (S.classicalPower hopen hbounded hgraph hγ m f t) (closure Ω) :=
  (S.holderPower hopen hbounded hgraph hγ 2 m f t).derivative 0
    |>.continuousOn_extend_zero

/-- The scalar time derivative exists at every point of the closure. -/
theorem hasDerivAt_classicalPower (m : ℕ) (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) {x : ℝ^n} (hx : x ∈ closure Ω) :
    HasDerivAt (fun s ↦ S.classicalPower hopen hbounded hgraph hγ m f s x)
      (-S.classicalPower hopen hbounded hgraph hγ (m + 1) f t x) t := by
  let E : CKGammaOn n 2 Ω γ →L[ℝ] ℝ := (BoundedContinuousFunction.evalCLM ℝ ⟨x, hx⟩).comp
    (CKGammaOn.derivativeCLM (0 : MultiIndex n 2))
  have h := E.hasFDerivAt.comp_hasDerivAt t
    (S.hasDerivAt_holderPower hopen hbounded hgraph hγ 2 m f ht)
  rw [map_neg] at h
  change HasDerivAt
    (fun s ↦ (S.holderPower hopen hbounded hgraph hγ 2 m f s).derivative 0 ⟨x, hx⟩)
    (-(S.holderPower hopen hbounded hgraph hγ 2 (m + 1) f t).derivative 0 ⟨x, hx⟩) t at h
  simpa only [classicalPower, CKGammaOn.interiorDerivative_apply _ _ hx] using h

/-- The weak Poisson identity becomes the pointwise Laplace equation. -/
theorem neg_laplacian_classicalPower (m : ℕ) (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, -PDE.laplacian (S.classicalPower hopen hbounded hgraph hγ m f t) x =
      S.classicalPower hopen hbounded hgraph hγ (m + 1) f t x := by
  apply (S.energyPower_isWeakPoissonSolution (Fact.out : 0 < n) hbounded
    m f t).neg_laplacian_eq_of_representatives
  · rw [S.energyPower_base (Fact.out : 0 < n) hbounded m f ht]
    exact (S.classicalPower_ae hopen hbounded hgraph hγ m f ht).symm
  · intro x hx
    exact ((S.contDiffOn_classicalPower hopen hbounded hgraph hγ m f ht).of_le
      (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt (hopen.mem_nhds hx)
  · exact (S.classicalPower_ae hopen hbounded hgraph hγ (m + 1) f ht).symm
  · exact (S.continuousOn_classicalPower hopen hbounded hgraph hγ (m + 1) f t).mono
      subset_closure

/-- The time derivative of the constructed series is its Laplacian. -/
theorem hasDerivAt_classicalPower_laplacian (m : ℕ) (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) {x : ℝ^n} (hx : x ∈ Ω) :
    HasDerivAt (fun s ↦ S.classicalPower hopen hbounded hgraph hγ m f s x)
      (PDE.laplacian (S.classicalPower hopen hbounded hgraph hγ m f t) x) t := by
  have h := S.hasDerivAt_classicalPower hopen hbounded hgraph hγ m f ht (subset_closure hx)
  rw [← S.neg_laplacian_classicalPower hopen hbounded hgraph hγ m f ht x hx, neg_neg] at h
  exact h

/-- Positive-time weighted sums vanish pointwise on the entire geometric boundary. -/
theorem classicalPower_zero_on_frontier (m : ℕ) (f : DerivLp n 2 Ω)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ frontier Ω, S.classicalPower hopen hbounded hgraph hγ m f t x = 0 := by
  let u := S.energyPower (Fact.out : 0 < n) hbounded m f t
  have hu : (baseCoordCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      S.classicalPower hopen hbounded hgraph hγ m f t := by
    rw [S.energyPower_base (Fact.out : 0 < n) hbounded m f ht]
    exact (S.classicalPower_ae hopen hbounded hgraph hγ m f ht).symm
  have hc := S.continuousOn_classicalPower hopen hbounded hgraph hγ m f t
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
  have htrace (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : ENNReal.ofReal 2 = p)
      (U : W^{1,p}(Ω))
      (hU : U ∈ (wkp0SubmoduleOn (n := d + 1) (k := 1) (p := p) (Ω := Ω)).toSubmodule)
      (hUz : baseRepresentative U =ᵐ[domainMeasure (d + 1) Ω]
        S.classicalPower hopen hbounded hgraph hγ m f t) :
      ∀ x ∈ frontier Ω, S.classicalPower hopen hbounded hgraph hγ m f t x = 0 := by
    subst p
    exact (Trace.C1.mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
      hopen hbounded ((hgraph 1).hasC1GraphBoundary le_rfl) 2 U hc hUz).mp hU
  exact htrace 2 (ENNReal.ofReal_ofNat 2) u.val u.property hu

end HeatEquation.DirichletHeatSpectrum
