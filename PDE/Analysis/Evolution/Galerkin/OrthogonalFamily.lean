/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.ProjectionConsistency
public import PDE.Analysis.Evolution.Galerkin.Spectral
public import PDE.Analysis.InnerProductSpace.CompatibleFamily

/-!
# Galerkin projections from an orthogonal energy basis

A densely spanning family orthogonal in the energy and pivot inner products gives
stable projections onto every finite subfamily, with energy bound one. When the
family is orthonormal in the pivot space, the initial projection is the usual
finite sum of pivot coefficients.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace PDE.Analysis.Evolution

variable {V H ι : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : GelfandTriple (V := V) (H := H)) {w : ι → V}

/-- Orthogonality in both spaces and density in the energy space give a stable
projection onto any finite subfamily, with energy bound one. -/
def stableTrialProjectionOfOrthogonalFamily
    [CompleteSpace H]
    (hw : Pairwise (fun i j ↦ ⟪w i, w j⟫_ℝ = 0))
    (hJw : Pairwise (fun i j ↦ ⟪T.inclusion (w i), T.inclusion (w j)⟫_ℝ = 0))
    (hdense : Dense (Submodule.span ℝ (range w) : Set V)) (s : Finset ι) :
    StableTrialProjection T (Submodule.span ℝ (w '' (s : Set ι))) 1 := by
  letI := FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image w)
  exact stableTrialProjectionOfCompatibility T _ fun v z ↦
    T.inclusion.inner_map_sub_starProjection_eq_zero hw hJw hdense s v z z.property

/-- Form the trial vector with the given coefficients on a finite subfamily. -/
def finiteTrialCombination (w : ι → V) (s : Finset ι) :
    (s → ℝ) →L[ℝ] Submodule.span ℝ (w '' (s : Set ι)) :=
  ∑ i : s, (ContinuousLinearMap.proj i).smulRight
    ⟨w i, Submodule.subset_span ⟨i, i.property, rfl⟩⟩

/-- The combination map is the ordinary finite vector sum. -/
theorem finiteTrialCombination_apply (s : Finset ι) (d : s → ℝ) :
    (finiteTrialCombination w s d : V) = ∑ i : s, d i • w i := by
  simp [finiteTrialCombination]

/-- Taking a pivot coefficient of a finite combination returns that coefficient. -/
theorem inner_inclusion_finiteTrialCombination
    (hJw : Orthonormal ℝ (fun i ↦ T.inclusion (w i))) (s : Finset ι)
    (d : s → ℝ) (i : s) :
    ⟪T.inclusion (w i), T.inclusion (finiteTrialCombination w s d : V)⟫_ℝ = d i := by
  rw [finiteTrialCombination_apply]
  simp only [map_sum, map_smul]
  exact (hJw.comp (fun j : s ↦ (j : ι)) Subtype.val_injective).inner_right_fintype d i

namespace StableTrialProjection

/-- A projection onto the span of a pivot-orthonormal finite family is its finite
coefficient sum, including for initial data outside the energy space. -/
theorem projection_eq_sum
    (hJw : Orthonormal ℝ (fun i ↦ T.inclusion (w i))) (s : Finset ι)
    {K : NNReal}
    (P : StableTrialProjection T (Submodule.span ℝ (w '' (s : Set ι))) K)
    (h : H) :
    (P.projection h : V) = ∑ i ∈ s, ⟪T.inclusion (w i), h⟫_ℝ • w i := by
  let S := Submodule.span ℝ (w '' (s : Set ι))
  let d : S := ⟨∑ i ∈ s, ⟪T.inclusion (w i), h⟫_ℝ • w i,
    Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)⟩
  have heq : ∀ z : S, ⟪T.inclusion (d : V), T.inclusion (z : V)⟫_ℝ =
      ⟪h, T.inclusion (z : V)⟫_ℝ := by
    let L := (innerSL ℝ (T.inclusion (d : V))).comp T.inclusion
    let R := (innerSL ℝ h).comp T.inclusion
    have hgen : EqOn L R (w '' (s : Set ι)) := by
      rintro _ ⟨i, hi, rfl⟩
      change ⟪T.inclusion (d : V), T.inclusion (w i)⟫_ℝ =
        ⟪h, T.inclusion (w i)⟫_ℝ
      simp only [d, map_sum, map_smul]
      rw [hJw.inner_left_sum _ hi]
      simp [real_inner_comm]
    exact fun z ↦ LinearMap.eqOn_span' (f := L.toLinearMap) (g := R.toLinearMap)
      hgen z.property
  exact (T.injective (P.inclusion_eq_pivotProjection_of_inner_eq d h heq)).symm

/-- Every trial vector is reconstructed by its pivot coefficients. -/
theorem sum_inner_eq_self
    (hJw : Orthonormal ℝ (fun i ↦ T.inclusion (w i))) (s : Finset ι)
    {K : NNReal}
    (P : StableTrialProjection T (Submodule.span ℝ (w '' (s : Set ι))) K)
    (u : Submodule.span ℝ (w '' (s : Set ι))) :
    ∑ i ∈ s, ⟪T.inclusion (w i), T.inclusion (u : V)⟫_ℝ • w i = (u : V) := by
  rw [← P.projection_eq_sum T hJw s, P.fixes]

/-- The finite combination of the pivot coefficients reconstructs a trial vector. -/
theorem finiteTrialCombination_inner_eq_self
    (hJw : Orthonormal ℝ (fun i ↦ T.inclusion (w i))) (s : Finset ι)
    {K : NNReal}
    (P : StableTrialProjection T (Submodule.span ℝ (w '' (s : Set ι))) K)
    (u : Submodule.span ℝ (w '' (s : Set ι))) :
    finiteTrialCombination w s (fun i ↦ ⟪T.inclusion (w i), T.inclusion (u : V)⟫_ℝ) =
      u := by
  apply Subtype.ext
  rw [finiteTrialCombination_apply,
    Finset.sum_coe_sort s (fun i ↦ ⟪T.inclusion (w i), T.inclusion (u : V)⟫_ℝ • w i)]
  exact P.sum_inner_eq_self T hJw s u

end StableTrialProjection

end PDE.Analysis.Evolution
