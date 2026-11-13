/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.Representative
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Vector.LinearMap

/-!
# Linear maps preserve canonical Sobolev representatives

The pointwise representative commutes with maps of the values. In particular,
assembling scalar Sobolev data and then taking the canonical vector
representative gives precisely the original scalar representatives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BesselPotentialSpace SchwartzMap

namespace BesselPotentialSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  {s : ℝ}

/-- A bounded linear map commutes pointwise with the canonical representative. -/
theorem c1Representative_postcomp
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1))
    (L : F →L[ℂ] G) (f : H^{s}(E, F)) (x : E) :
    c1Representative hs (postcomp L f) x = L (c1Representative hs f x) := by
  have heq := eq_c1Representative_of_integral_smul hs (postcomp L f)
    (L.continuous.comp (c1Representative hs f).continuous)
  apply congrFun (heq ?_).symm x
  intro φ
  have hi : Integrable (fun y ↦ φ y • c1Representative hs f y) :=
    φ.integrable.smul_bdd ‖c1Representative hs f‖
      (c1Representative hs f).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (c1Representative hs f).norm_coe_le_norm)
  change (∫ y, φ y • L (c1Representative hs f y)) = L (f.toDistr φ)
  rw [← integral_smul_c1Representative hs f φ, ← L.integral_comp_comm hi]
  simp only [map_smul]

/-- The canonical representative of an assembled vector has the prescribed
canonical scalar coordinates. -/
theorem c1Representative_euclideanTuple_apply
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1))
    {m : ℕ} (f : Fin m → H^{s}(E)) (x : E) (i : Fin m) :
    c1Representative hs (euclideanTuple f) x i = c1Representative hs (f i) x := by
  have hproj : postcomp (EuclideanSpace.proj i) (euclideanTuple f) = f i := by
    apply BesselPotentialSpace.ext
    ext φ
    exact toDistr_euclideanTuple_apply f φ i
  have h := c1Representative_postcomp hs (EuclideanSpace.proj i) (euclideanTuple f) x
  rw [hproj] at h
  exact h.symm

end BesselPotentialSpace
