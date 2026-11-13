/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Naturality

/-!
# Independence of the Banach-valued surface trace from the C¹ atlas

A bounded trace is determined by its physical boundary values on compact ambient
smooth representatives. Density in the Sobolev graph therefore identifies the
trace operators constructed from any two finite C¹ extension atlases on the same domain.

Both operators take values in the same intrinsic surface-measure `Lp` space.
The result includes exponent one and arbitrary real Banach targets.

Evans defines `T` in step 4 of the proof of §5.5, Theorem 1, as the limit of `T u_m` for smooth
`u_m → u`, and notes that the limit does not depend on the approximating sequence. The same
density argument gives the independence of the atlas.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, proof of Theorem 1, step 4, (3), p. 273.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- For real `p ≥ 1` and a real Banach space `F`, a continuous linear operator
`T : W^{1,p}(Ω; F) → Lᵖ(∂Ω; F)` such that `T U` is a.e. the boundary restriction of `f`
whenever `U` has a smooth compactly supported ambient representative `f` equals the physical
surface trace `traceLp p hp`. -/
theorem eq_traceLp_of_classical
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (T : W^{1,ENNReal.ofReal p}(Ω; F) →L[ℝ]
      Lp F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1))))
    (hT : ∀ (U : W^{1,ENNReal.ofReal p}(Ω; F)) (f : ℝ^(m + 1) → F),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
        =ᵐ[domainMeasure (m + 1) Ω] f →
      (T U : ℝ^(m + 1) → F) =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))] f) :
    T = traceLp p hp := by
  ext U : 1
  refine (dense_compact_smooth ENNReal.ofReal_ne_top).induction ?_
    (isClosed_eq T.continuous (traceLp p hp).continuous) U
  rintro V ⟨f, hf, hfc, hbase⟩
  apply Lp.ext
  exact (hT V f hf hfc hbase).trans
    (traceLp_coeFn_ae hp V (hf.of_le (by simp)) hbase).symm

/-- Any two finite C¹ extension atlases give the same Banach-valued surface trace
at every finite real exponent at least one. -/
theorem traceLp_eq_of_atlases
    (A B : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1)))
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p) :
    traceLp (hΩ := A) (F := F) p hp = traceLp (hΩ := B) p hp := by
  apply eq_traceLp_of_classical (hΩ := B) hp (traceLp (hΩ := A) p hp)
  intro U f hf _ hbase
  exact traceLp_coeFn_ae (hΩ := A) hp U (hf.of_le (by simp)) hbase

end SobolevSpace.VectorValued.Trace.C1
