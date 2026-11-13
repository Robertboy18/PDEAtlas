/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianL2
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# The bounded Newtonian Hessian of a locally C² potential

For an L² source vanishing almost everywhere outside a compact set, the bounded
Newtonian Hessian represents the weak Hessian of the convolution.
On any open set where that potential is C², uniqueness of weak derivatives identifies
the operator with its classical Hessian and gives L² membership for the restricted measure.
No source derivative is required. Global C² agreement and membership follow by taking
the open set to be the whole space.

All statements use five-dimensional Cartesian volume. Regularity of the
potential is an input; the source approximation and distributional action come
from `NewtonianHessianL2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PotentialTheory

local notation "H" => Lp ℝ 2 (volume : Measure (ℝ^5))

/-- On an open set where the Newtonian potential is C², the bounded Hessian
agrees almost everywhere with its classical Hessian. The source is L² and vanishes
almost everywhere outside a compact set; no source derivative is required.
Only the operator's action on smooth compact sources is assumed. -/
theorem newtonianHessianL2_apply_ae_eq_of_contDiffOn_two_potential
    (i j : Fin 5) (S : H →L[ℝ] H)
    (hS : ∀ (g : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      S ((hg.continuous.memLp_of_hasCompactSupport hgc).toLp g) =ᵐ[volume]
        fun X ↦ (∂[i] (∂[j]
          (convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
    {f : ℝ^5 → ℝ} {K Ω : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0) (hΩ : IsOpen Ω)
    (hP : ContDiffOn ℝ 2
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) Ω) :
    S (hf.toLp f) =ᵐ[volume.restrict Ω]
      fun X ↦ (∂[i] (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X := by
  let potential : ℝ^5 → ℝ :=
    convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume
  have hreg (X : ℝ^5) (hX : X ∈ Ω) : ContDiffAt ℝ 2 potential X :=
    hP.contDiffAt (hΩ.mem_nhds hX)
  have hfirst := SobolevSpace.hasWeakDerivativeOn_of_contDiffAt_one hΩ
    (f := potential) (fun X hX ↦ (hreg X hX).of_le (by norm_num)) j
  have hsecond := SobolevSpace.hasWeakDerivativeOn_of_contDiffAt_one hΩ
    (fun X hX ↦ PDE.contDiffAt_partialDeriv 1 (hreg X hX) j) i
  have hclassical : SobolevSpace.HasWeakDerivativeOn Ω [i, j] potential
      (∂[i] (∂[j] potential)) :=
    (hfirst.append_single i hsecond).perm (List.Perm.swap _ _ [])
  have hweak := hasWeakDerivativeOn_newtonianHessianL2_of_ae_compact_support
    i j S hS hf hK hf0
  have hweakOn := SobolevSpace.HasWeakDerivativeOn.mono
    hΩ.measurableSet (Set.subset_univ Ω) hweak
  exact SobolevSpace.HasWeakDerivativeOn.unique_ae hΩ hweakOn hclassical

/-- A Newtonian potential that is C² on an open set has its classical Hessian in L²
for Cartesian volume restricted to that set, when its source is L² and vanishes
almost everywhere outside a compact set. -/
theorem fundamentalSolution_five_convolution_hessian_memLp_of_contDiffOn_two_potential
    {f : ℝ^5 → ℝ} {K Ω : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0) (hΩ : IsOpen Ω)
    (hP : ContDiffOn ℝ 2
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) Ω)
    (i j : Fin 5) :
    MemLp (fun X ↦ (∂[i] (∂[j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
      2 (volume.restrict Ω) := by
  obtain ⟨T, hT, _⟩ := exists_newtonianHessianL2
  have haction := newtonianHessianL2_apply_ae_eq_of_contDiffOn_two_potential i j (T i j)
    (fun g hg hgc ↦ hT.1 g hg hgc i j) hf hK hf0 hΩ hP
  exact (memLp_congr_ae haction).mp ((Lp.memLp (T i j (hf.toLp f))).restrict Ω)

/-- The bounded Newtonian Hessian agrees with the classical Hessian of the
C² potential of an L² source vanishing almost everywhere outside a compact set.
Only the operator's action on smooth compact sources is assumed. -/
theorem newtonianHessianL2_apply_ae_eq_of_contDiff_two_potential
    (i j : Fin 5) (S : H →L[ℝ] H)
    (hS : ∀ (g : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      S ((hg.continuous.memLp_of_hasCompactSupport hgc).toLp g) =ᵐ[volume]
        fun X ↦ (∂[i] (∂[j]
          (convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
    {f : ℝ^5 → ℝ} {K : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0)
    (hP : ContDiff ℝ 2
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)) :
    S (hf.toLp f) =ᵐ[volume]
      fun X ↦ (∂[i] (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X := by
  simpa only [Measure.restrict_univ] using
    newtonianHessianL2_apply_ae_eq_of_contDiffOn_two_potential
      (Ω := Set.univ) i j S hS hf hK hf0 isOpen_univ hP.contDiffOn

/-- A C² Newtonian potential has its classical Hessian in L² when its
source is L² and vanishes almost everywhere outside a compact set. -/
theorem fundamentalSolution_five_convolution_hessian_memLp_of_contDiff_two_potential
    {f : ℝ^5 → ℝ} {K : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0)
    (hP : ContDiff ℝ 2
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))
    (i j : Fin 5) :
    MemLp (fun X ↦ (∂[i] (∂[j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
      2 volume := by
  simpa only [Measure.restrict_univ] using
    fundamentalSolution_five_convolution_hessian_memLp_of_contDiffOn_two_potential
      (Ω := Set.univ) hf hK hf0 isOpen_univ hP.contDiffOn i j

end PotentialTheory
