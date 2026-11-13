/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.ClassicalSolution
public import PDE.Analysis.Integration.SphereProjection.Average

/-!
# Hadamard descent in every even dimension

Lift the data constantly in one extra spatial coordinate and restrict the
odd-dimensional wave to its zero slice. The entire lifted wave is independent
of that coordinate, at every center and signed time. This identity is needed
before discarding the extra spatial second derivative.

This is the method of descent of Evans, §2.4.1(e): the lifted data are `ḡ` and `h̄` of (34), and
the odd-dimensional wave is formula (31) with `n + 1` in place of `n`. With `n = 2k + 2` and
`m = (n + 2)/2 = k + 2`, `contDiff_two_evenWaveSolution` assumes `g ∈ C^(m+1)` and `h ∈ C^m`, as
in Evans, §2.4.1(e), Theorem 3, and gives the regularity of Theorem 3(i) for all signed times.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(e), equations (33)-(35) and Theorem 3(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE (time)
open PDE.Analysis PDE.Common

/-- The signed extension of the even-dimensional wave, obtained by constant-coordinate
lifting of the data and restriction of the odd-dimensional construction. -/
def evenWaveSolution (k : ℕ) (g h : ℝ^(2 * k + 2) → ℝ) : ℝ^(2 * k + 2 + 1) → ℝ :=
  spaceTimeUncurry (fun x t ↦ oddWaveSolution k
    (g ∘ coordinateProjection) (h ∘ coordinateProjection) (timeSpaceCons t (coordinateInclusion x)))

/-- Evaluating the descended field on canonical spacetime gives the odd wave on the
zero slice of the extra coordinate. -/
@[simp]
theorem evenWaveSolution_timeSpaceCons (k : ℕ) (g h : ℝ^(2 * k + 2) → ℝ)
    (x : ℝ^(2 * k + 2)) (t : ℝ) :
    evenWaveSolution k g h (timeSpaceCons t x) = oddWaveSolution k (g ∘ coordinateProjection)
      (h ∘ coordinateProjection) (timeSpaceCons t (coordinateInclusion x)) := by
  simp [evenWaveSolution, spaceTimeUncurry, time]

/-- The entire radial profile of lifted data depends only on the projected center. -/
theorem oddSphericalProfile_coordinateProjection_center (k : ℕ)
    (f : ℝ^(2 * k + 2) → ℝ) (z : ℝ^(2 * k + 3)) :
    oddSphericalProfile k (f ∘ coordinateProjection) z = oddSphericalProfile k
      (f ∘ coordinateProjection) (coordinateInclusion (coordinateProjection z)) := by
  unfold oddSphericalProfile
  congr 1
  funext r
  rw [unitSphereAverage_coordinateProjection_center]

/-- The full lifted wave, at arbitrary centers and signed times, is the pullback of
its descended field. This proves independence before the Laplacian is restricted. -/
theorem oddWaveSolution_coordinateProjection_center (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 1) g) (z : ℝ^(2 * k + 3)) (t : ℝ) :
    oddWaveSolution k (g ∘ coordinateProjection) (h ∘ coordinateProjection) (timeSpaceCons t z) =
      evenWaveSolution k g h (timeSpaceCons t (coordinateProjection z)) := by
  rw [evenWaveSolution_timeSpaceCons]
  simp only [oddWaveSolution,
    partialDeriv_oddWavePotential_time k (hg.comp coordinateProjection.contDiff),
    oddWavePotential_timeSpaceCons]
  rw [oddSphericalProfile_coordinateProjection_center k g z,
    oddSphericalProfile_coordinateProjection_center k h z]

/-- The descended wave is jointly `C²` on all signed times at the finite
orders `C^(k+3)` and `C^(k+2)`. -/
theorem contDiff_two_evenWaveSolution (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) :
    ContDiff ℝ 2 (evenWaveSolution k g h) := by
  apply (contDiff_spaceTimeUncurry_iff _).mpr
  exact (contDiff_two_oddWaveSolution k (hg.comp coordinateProjection.contDiff)
    (hh.comp coordinateProjection.contDiff)).comp ((contDiff_timeSpaceCons_uncurry (2 * k + 3)).comp
        (contDiff_snd.prodMk (coordinateInclusion.contDiff.comp contDiff_fst)))

/-- Closed-halfspace regularity follows from the signed extension. -/
theorem contDiffOn_two_evenWaveSolution (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) :
    ContDiffOn ℝ 2 (evenWaveSolution k g h) {p | 0 ≤ p 0} :=
  (contDiff_two_evenWaveSolution k hg hh).contDiffOn

/-- Fixed-time spatial slices retain joint second-order regularity. -/
theorem contDiff_two_evenWaveSolution_slice (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) (t : ℝ) :
    ContDiff ℝ 2 (fun x ↦ evenWaveSolution k g h (timeSpaceCons t x)) :=
  (contDiff_two_evenWaveSolution k hg hh).comp (contDiff_timeSpaceCons_spatial (2 * k + 2) t)

end WaveEquation
