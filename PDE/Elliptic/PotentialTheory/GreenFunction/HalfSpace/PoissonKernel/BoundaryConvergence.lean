/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Normalization
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenKernel -- shake: keep
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Integrability

/-!
# Boundary convergence of the half-space Poisson extension

Let `g` be measurable and bounded on the boundary hyperplane, with continuous boundary restriction
at `(a, 0)`. Its Poisson extension recovers that value from every approach within the upper
half-space:

`poissonHalfSpaceExtension g x → g(a, 0)` as `x → (a, 0)`, `xₙ > 0`.

This is part (iii) of Evans's §2.2.4(b), Theorem 14, where `g` is continuous and bounded on the
whole hyperplane.

## Main results

* `tendsto_poissonHalfSpaceExtension_parametric`: simultaneous horizontal and vertical limits.
* `tendsto_poissonHalfSpaceExtension_boundary`: arbitrary approach within the half-space.
* `tendsto_poissonHalfSpaceExtension_vertical`: the vertical specialization for continuous data.

## How it works

Evans fixes `ε`, splits the boundary integral at `B(x⁰, δ)`, and controls the near part by (34) and
the far part by the decay of `K`, his (35)-(36). We change variables instead. Translation by `x'`
and scaling by `xₙ` turn the kernel into the fixed unit-height profile `K(z) = ‖eₙ - (z, 0)‖⁻ⁿ`,
whose integral is `n α(n) / 2`, and the data become `g(x' + xₙz, 0)`, which converge pointwise to
`g(a, 0)`. Boundedness supplies a common integrable majorant, so dominated convergence along
countably generated filters (Mathlib's
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`) gives the joint horizontal and
vertical limit of `tendsto_poissonHalfSpaceExtension_parametric`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), Theorem 14 (Poisson's formula for half-space),
  p. 37, and step 3 of its proof, (35)-(36), pp. 38-39.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open LaplacianEquation
open PDE.Analysis
open PotentialTheory
open MeasureTheory
open Set

section PoissonHalfSpaceBoundaryConvergence

open MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

private theorem poissonHalfSpaceExtension_vertical_eq_integral
    {g : ℝ^n → ℝ}
    (hg : Measurable g) (a : ℝ^(n - 1))
    {t : ℝ} (ht : 0 < t) :
    poissonHalfSpaceExtension (n := n) g
        (halfSpaceEmb (n := n) a +
          t • eLast (n := n)) =
      2 / ((n : ℝ) * unitBallVolume n) *
        ∫ z : ℝ^(n - 1),
          (dist (eLast (n := n)) (halfSpaceEmb (n := n) z) ^ n)⁻¹ *
            g (halfSpaceEmb (n := n) (a + t • z)) := by
  let x : ℝ^n := halfSpaceEmb (n := n) a + t • eLast (n := n)
  let f : ℝ^(n - 1) → ℝ := fun y ↦
    g (halfSpaceEmb (n := n) y) / dist x (halfSpaceEmb (n := n) y) ^ n
  have heLast : eLast (n := n) ∈ SobolevSpace.HalfSpace.upper n := by
    simp [SobolevSpace.HalfSpace.upper, eLast, PDE.Common.lastIndex]
  have hpoint (z : ℝ^(n - 1)) : f (a + t • z) = (t ^ n)⁻¹ *
      ((dist (eLast (n := n)) (halfSpaceEmb (n := n) z) ^ n)⁻¹ *
        g (halfSpaceEmb (n := n) (a + t • z))) := by
    have := dist_ne_zero.mpr (halfSpace_ne_halfSpaceEmb (n := n) heLast z)
    have hdist : dist x (halfSpaceEmb (n := n) (a + t • z)) =
        t * dist (eLast (n := n)) (halfSpaceEmb (n := n) z) := by
      rw [halfSpaceEmb_add]
      simpa [x, abs_of_pos ht] using distance_smul_single_last (n := n) t z
    simp only [f, hdist, mul_pow]
    field_simp
  have hs := Measure.integral_comp_smul_of_nonneg (hR := ht.le) (volume : Measure ℝ^(n - 1))
    (fun y ↦ f (a + y)) t
  simp only [hpoint, integral_const_mul, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    integral_add_left_eq_self] at hs
  rw [show t ^ n = t ^ (n - 1) * t by rw [← pow_succ, Nat.sub_add_cancel (Fact.out : 0 < n)],
    mul_inv, mul_assoc] at hs
  have hI := mul_left_cancel₀ (by positivity) hs
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
  have := (unitBallVolume_pos n).ne'
  rw [poissonHalfSpaceExtension_eq_integral (n := n) g hg x]
  change (2 * x PDE.Common.lastIndex) / ((n : ℝ) * unitBallVolume n) *
    (∫ y : ℝ^(n - 1), f y) = _
  rw [show x PDE.Common.lastIndex = t by simp [x, eLast, PDE.Common.lastIndex, halfSpaceEmb],
    ← hI]
  field_simp


/-- The horizontal coordinate and positive height may tend to a boundary point simultaneously.
Only continuity of the boundary restriction at the limiting point is needed; the ambient datum
need only be measurable. The countable filter basis is the hypothesis of dominated convergence. -/
theorem tendsto_poissonHalfSpaceExtension_parametric
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded : ∃ M : ℝ, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {a : ℝ^(n - 1)}
    (hga : ContinuousAt (fun y ↦ g (halfSpaceEmb (n := n) y)) a)
    {A : ι → ℝ^(n - 1)} {h : ι → ℝ}
    (hA : Tendsto A l (𝓝 a)) (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < h i) :
    Tendsto
      (fun i ↦
        poissonHalfSpaceExtension (n := n) g
          (halfSpaceEmb (n := n) (A i) + h i • eLast (n := n)))
      l
      (𝓝 (g (halfSpaceEmb (n := n) a))) := by
  let K : ℝ^(n - 1) → ℝ := fun z ↦ (dist (eLast (n := n)) (halfSpaceEmb (n := n) z) ^ n)⁻¹
  rcases hg_bounded with ⟨M, hM⟩
  have hK : Integrable K := integrable_inv_distance_pow (n := n) eLast
    (by simp [SobolevSpace.HalfSpace.upper, eLast, PDE.Common.lastIndex])
  have hIntegral := tendsto_integral_filter_of_dominated_convergence (l := l)
    (F := fun i z ↦ K z * g (halfSpaceEmb (n := n) (A i + h i • z)))
    (f := fun z ↦ K z * g (halfSpaceEmb (n := n) a)) (fun z ↦ M * K z)
    (.of_forall fun i ↦ hK.aestronglyMeasurable.mul (hg.comp ((continuous_halfSpaceEmb
      (n := n)).comp (continuous_const.add (continuous_const_smul (h i)))).measurable
        |>.aestronglyMeasurable))
    (.of_forall fun i ↦ ae_of_all _ fun z ↦ by
      simp only [K, norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, abs_dist]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _ (halfSpaceEmb_mem_boundary _)) (by positivity))
    (hK.const_mul M)
    (ae_of_all _ fun z ↦ tendsto_const_nhds.mul (hga.tendsto.comp
      (by simpa using hA.add (hh.smul (tendsto_const_nhds (x := z))))))
  rw [integral_mul_const, show (∫ z, K z) = (n : ℝ) * unitBallVolume n / 2 from
    integral_distance_pow_inv_eLast] at hIntegral
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
  have := (unitBallVolume_pos n).ne'
  rw [← show 2 / ((n : ℝ) * unitBallVolume n) * ((n : ℝ) * unitBallVolume n / 2 *
      g (halfSpaceEmb (n := n) a)) = g (halfSpaceEmb (n := n) a) by field_simp]
  refine (tendsto_const_nhds.mul hIntegral).congr' ?_
  filter_upwards [hpos] with i hi
  exact (poissonHalfSpaceExtension_vertical_eq_integral hg (A i) hi).symm


/-- The half-space Poisson extension tends to the boundary datum along every approach from
above. Continuity is needed only for the restriction of the datum to the boundary, at the
point in question; no restriction on the ratio of horizontal displacement to height is imposed. -/
theorem tendsto_poissonHalfSpaceExtension_boundary
    {g : ℝ^n → ℝ} (hg : Measurable g)
    (hg_bounded : ∃ M : ℝ, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (a : ℝ^(n - 1))
    (hga : ContinuousAt (fun y ↦ g (halfSpaceEmb (n := n) y)) a) :
    Tendsto (poissonHalfSpaceExtension (n := n) g)
      (𝓝[SobolevSpace.HalfSpace.upper n] halfSpaceEmb (n := n) a)
      (𝓝 (g (halfSpaceEmb (n := n) a))) := by
  have hproj :
      Tendsto (halfSpaceProj (n := n))
        (𝓝[SobolevSpace.HalfSpace.upper n] halfSpaceEmb (n := n) a) (𝓝 a) := by
    simpa only [halfSpaceProj_halfSpaceEmb] using
      (continuous_halfSpaceProj (n := n)).continuousAt
        (x := halfSpaceEmb (n := n) a) |>.tendsto.mono_left
          (nhdsWithin_le_nhds (s := SobolevSpace.HalfSpace.upper n))
  have hheight :
      Tendsto (fun x : ℝ^n ↦ x PDE.Common.lastIndex)
        (𝓝[SobolevSpace.HalfSpace.upper n] halfSpaceEmb (n := n) a) (𝓝 0) := by
    simpa [halfSpaceEmb, PDE.Common.lastIndex] using
      (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).continuous.continuousAt
        (x := halfSpaceEmb (n := n) a) |>.tendsto.mono_left
          (nhdsWithin_le_nhds (s := SobolevSpace.HalfSpace.upper n))
  have h := tendsto_poissonHalfSpaceExtension_parametric hg hg_bounded hga hproj hheight
    (show ∀ᶠ x in 𝓝[SobolevSpace.HalfSpace.upper n] halfSpaceEmb (n := n) a,
      0 < x PDE.Common.lastIndex from self_mem_nhdsWithin)
  convert h using 1
  funext x
  congr 1
  exact (sub_eq_iff_eq_add.mp (sub_halfSpaceEmb_halfSpaceProj_eq x)).trans (add_comm _ _)

/-- The vertical specialization of boundary convergence for continuous ambient data. -/
theorem tendsto_poissonHalfSpaceExtension_vertical
    {g : ℝ^n → ℝ}
    (hg : Continuous g)
    (hg_bounded : ∃ M : ℝ, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (a : ℝ^(n - 1)) :
    Tendsto
      (fun t : ℝ ↦ poissonHalfSpaceExtension (n := n) g
        (halfSpaceEmb (n := n) a + t • eLast (n := n)))
      (𝓝[Set.Ioi 0] 0) (𝓝 (g (halfSpaceEmb (n := n) a))) :=
  tendsto_poissonHalfSpaceExtension_parametric hg.measurable hg_bounded
    (hg.comp continuous_halfSpaceEmb).continuousAt tendsto_const_nhds
    nhdsWithin_le_nhds self_mem_nhdsWithin

end PoissonHalfSpaceBoundaryConvergence

end GreenFunction
