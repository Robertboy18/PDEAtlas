/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.Spacetime

/-!
# Global classical defocusing cubic waves from smooth compact data

Arbitrary smooth compact displacement and velocity on ℝ³ yield a forward
global classical solution. Its displacement and observed velocity represent
the conserved energy evolution, which attains the data strongly in H¹ × L².
Every competing forward classical solution agrees with it.

The regularity assertion is joint C² at positive time and joint C¹ up to
time zero, with both right Cauchy traces.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Common
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

/-- Every smooth compact datum on ℝ³ gives a unique forward classical cubic
wave and its conserved energy trajectory. All bounds used to extend the
higher solution are derived from the defocusing energy and Sobolev estimates. -/
theorem exists_global_classical_cubic_of_smoothCompact (g h : ℝ^3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    let x : H¹(ℝ^3) × DerivLp 3 2 univ :=
      (mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ) g hg hgc, wkpBaseCoordinateCLM
          (mkWkpSpaceOnOfContDiff (k := 0) (p := 2) (Ω := univ) h hh hhc))
    ∃ (u v : C(ℝ^4, ℝ)) (e : C(ℝ, H¹(ℝ^3) × DerivLp 3 2 univ)),
      IsClassicalSolution g h u ∧ cubicNonlinearity.IsEnergySolution x e ∧
      Tendsto e (𝓝[≥] (0 : ℝ)) (𝓝 x) ∧
      (∀ t : ℝ, 0 ≤ t → cubicNonlinearity.energy (e t) = cubicNonlinearity.energy x ∧
        (fun y ↦ u (timeSpaceCons t y)) =ᵐ[volume] baseRepresentative (e t).1 ∧
        (fun y ↦ v (timeSpaceCons t y)) =ᵐ[volume] (e t).2 ∧
        ∀ y, HasDerivWithinAt (fun s ↦ u (timeSpaceCons s y)) (v (timeSpaceCons t y)) (Ici 0) t) ∧
      ∀ w : ℝ^4 → ℝ, IsClassicalSolution g h w → EqOn u w {p | 0 ≤ p 0} := by
  intro x
  let G := mkWkpSpaceOnOfContDiff (k := 5) (p := 2) (Ω := univ) g hg hgc
  let H := mkWkpSpaceOnOfContDiff (k := 4) (p := 2) (Ω := univ) h hh hhc
  have hprojection : energyProjectionCLM 4 (G, H) = x := by
    apply Prod.ext
    · exact lowerOrderCLM_mkWkpSpaceOnOfContDiff (by norm_num : 1 ≤ 5) g hg hgc
    · change wkpBaseCoordinateCLM H = wkpBaseCoordinateCLM
        (mkWkpSpaceOnOfContDiff (k := 0) (p := 2) (Ω := univ) h hh hhc)
      apply Lp.ext
      exact (wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (k := 4) (Ω := univ) hh hhc).trans
        (wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (k := 0) (Ω := univ) hh hhc).symm
  obtain ⟨u, v, hu, hfield⟩ := exists_global_classical_cubic (G, H)
  have hclassical : IsClassicalSolution g h u := by
    simpa only [G, H, classicalRepresentative_mkWkpSpaceOnOfContDiff] using hu
  rw [hprojection] at hfield
  have he := cubicNonlinearity.globalSolution_isEnergySolution x
  refine ⟨u, v, cubicNonlinearity.globalSolution x, hclassical, he, he.tendsto_initial, ?_,
    fun w hw ↦ hclassical.eqOn hw⟩
  exact fun t ht ↦ ⟨cubicNonlinearity.energy_globalSolution x ht, hfield t ht⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
