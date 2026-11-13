/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletInitial
public import PDE.Analysis.Evolution.Semigroup.Duhamel.Classical

/-!
# Uniqueness of the Dirichlet spectral heat trajectory

Testing the weak Poisson equation against the energy eigenfunctions identifies its
forcing coefficients. This derives membership in the spectral generator graph.
Variation of constants then identifies any continuous pivot trajectory satisfying
the weak heat equation, with a pivot derivative at positive time, with the heat
series. No eigenfunction expansion or energy inequality is imposed on the competitor.
-/

@[expose] public section

noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Set
open scoped Sobolev InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} (S : DirichletHeatSpectrum n Ω)

/-- The weak Poisson equation determines every eigenvalue-weighted coefficient. -/
theorem repr_of_isWeakPoissonSolution {f : DerivLp n 2 Ω} {u : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution f u) (i : ℕ) :
    S.basis.repr f i = S.eigenvalue i * S.basis.repr (baseCoordCLM u) i := by
  have h := (isWeakSolution_iff_isWeakPoissonSolution hu.1 f u).2 hu
    (S.eigenfunction i)
  have he := (isWeakSolution_iff_isWeakPoissonSolution hu.1 _ _).2
    (S.poisson_eigenfunction i) u
  rw [dirichletForm_symm] at h
  rw [he, loadFunctional_apply, loadFunctional_apply, S.base_eigenfunction,
    real_inner_smul_left] at h
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  exact (real_inner_comm _ _).trans h.symm

/-- A weak Dirichlet Laplacian in the pivot space belongs to the spectral generator graph. -/
theorem hasGeneratorAt_of_isWeakPoissonSolution {f : DerivLp n 2 Ω} {u : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution f u) :
    (spectralHeatSemigroup S.basis S.eigenvalue S.eigenvalue_nonneg).HasGeneratorAt
      (baseCoordCLM u) (-f) := by
  apply spectralHeatSemigroup_hasGeneratorAt_of_repr
  intro i
  simp only [map_neg, lp.coeFn_neg, Pi.neg_apply, S.repr_of_isWeakPoissonSolution hu,
    neg_mul]

/-- Any continuous `L²` trajectory whose positive-time slices lie in `H¹₀` and whose
pivot derivative satisfies the distributional heat equation is the spectral
heat evolution. No derivative at the initial or terminal time is required. -/
theorem eq_spectralHeatEvolution_of_weak_heat
    {z v : ℝ → DerivLp n 2 Ω} {a b : ℝ} (hab : a ≤ b)
    (hz : ContinuousOn z (Icc a b))
    (hweak : ∀ t ∈ Ioo a b, ∃ u : H¹₀(Ω), baseCoordCLM u = z t ∧
      IsWeakPoissonSolution (-v t) u)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt z (v t) t) :
    z b = spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg
      (z a) (b - a).toNNReal := by
  have h := (spectralHeatSemigroup S.basis S.eigenvalue S.eigenvalue_nonneg)
    |>.eq_orbit_add_integral_of_hasDerivWithinAt (u := z) (Au := v) (f := 0)
      hab hz continuousOn_const ?_ ?_
  · simpa only [Pi.zero_apply, map_zero, intervalIntegral.integral_zero, add_zero,
      spectralHeatSemigroup_apply] using h
  · intro t ht
    obtain ⟨u, hu, hp⟩ := hweak t ht
    simpa only [hu, neg_neg] using S.hasGeneratorAt_of_isWeakPoissonSolution hp
  · intro t ht
    simpa only [Pi.zero_apply, add_zero] using (hd t ht).hasDerivWithinAt

variable [Fact (0 < n)] {γ : HolderSpace.Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)

/-- The constructed classical heat series is unique against an independently supplied
weak Dirichlet heat trajectory continuous in `L²`, with a positive-time `L²`
derivative. The competitor need not have spatial classical regularity. -/
theorem eq_dirichletHeatL2_of_weak_heat
    (f : DerivLp n 2 Ω) {z v : ℝ → DerivLp n 2 Ω} {T : ℝ} (hT : 0 ≤ T)
    (hz : ContinuousOn z (Icc 0 T)) (hzero : z 0 = f)
    (hweak : ∀ t ∈ Ioo 0 T, ∃ u : H¹₀(Ω), baseCoordCLM u = z t ∧
      IsWeakPoissonSolution (-v t) u)
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt z (v t) t) :
    z T = S.dirichletHeatL2 hopen hbounded hgraph hγ f T := by
  rw [S.dirichletHeatL2_eq_spectralHeatEvolution hopen hbounded hgraph hγ]
  simpa only [hzero, sub_zero] using
    S.eq_spectralHeatEvolution_of_weak_heat hT hz hweak hd

/-- The constructed pivot trajectory itself satisfies the independent weak heat class
used in uniqueness, with its explicit eigenvalue-weighted velocity. -/
theorem dirichletHeatL2_weak_heat (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    (∃ u : H¹₀(Ω), baseCoordCLM u = S.dirichletHeatL2 hopen hbounded hgraph hγ f t ∧
      IsWeakPoissonSolution
        (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg 1 f t) u) ∧
    HasDerivAt (S.dirichletHeatL2 hopen hbounded hgraph hγ f)
      (-spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg 1 f t) t := by
  have heq (s : ℝ) (hs : 0 < s) :
      S.dirichletHeatL2 hopen hbounded hgraph hγ f s =
        spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg 0 f s := by
    rw [S.dirichletHeatL2_eq_spectralHeatEvolution hopen hbounded hgraph hγ,
      spectralHeatPower_zero_order S.basis S.eigenvalue S.eigenvalue_nonneg f hs]
    congr 1
    exact NNReal.eq (Real.coe_toNNReal s hs.le)
  constructor
  · refine ⟨S.energyPower (Fact.out : 0 < n) hbounded 0 f t, ?_,
      S.energyPower_isWeakPoissonSolution (Fact.out : 0 < n) hbounded 0 f t⟩
    rw [heq t ht]
    exact S.energyPower_base (Fact.out : 0 < n) hbounded 0 f ht
  · apply (hasDerivAt_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg
      0 f ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact heq s hs

end HeatEquation.DirichletHeatSpectrum
