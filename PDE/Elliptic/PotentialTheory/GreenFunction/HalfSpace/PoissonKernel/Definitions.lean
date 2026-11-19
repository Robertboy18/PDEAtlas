/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenKernel -- shake: keep

/-!
# Half-space Poisson kernel

The Poisson kernel of the upper half-space `ℝ^n₊ = {x : xₙ > 0}` is

`K(x, y) = 2 xₙ / (n α(n) ‖x - y‖ⁿ)`, for `x ∈ ℝ^n₊` and `y` on the boundary `{yₙ = 0}`,

where `α(n)` is the volume of the unit ball. On the boundary, `K = ∂G/∂yₙ = -∂G/∂ν` for the
method-of-images Green function `G` and the outer normal `ν = -eₙ`. The Poisson extension of
boundary data `g` is `u(x) = ∫_{∂ℝ^n₊} K(x, y) g(y) dS(y)`, which is Poisson's formula (33) in
Evans's §2.2.4(b).

The boundary hyperplane is parametrised by `halfSpaceEmb : ℝ^(n-1) → ℝ^n`, which appends a zero last
coordinate, and the surface measure on the boundary is the pushforward of Lebesgue measure on
`ℝ^(n-1)` under this map. The Poisson extension is defined by integrating against that pushforward
measure, and the main lemma rewrites it as an explicit integral over `ℝ^(n-1)`, the form used by the
analytic modules.

## Main definitions

* `halfSpacePoissonKernel`, `poissonHalfSpaceExtension`: the kernel and the extension operator.
* `halfSpaceEmb`, `halfSpaceProj`, `halfSpaceBoundaryMeasure`: boundary parametrisation, the
  tangential projection, and the boundary surface measure.

## Main results

* `norm_halfSpaceEmb`, `norm_sub_halfSpaceProj_le_distance`, `lastCoord_le_distance_halfSpaceEmb`:
  the embedding is an isometry onto the hyperplane, and both the tangential displacement and the
  height `xₙ` are bounded by the distance from `x` to a boundary point.
* `poissonHalfSpaceExtension_eq_integral`: for measurable data, rewrite the extension as an integral
  over `ℝ^(n-1)`.

## Implementation notes

All definitions are total Lean functions. The analytic statements in the sibling modules
(`Integrability`, `Normalization`, `Differentiation`, `BoundaryConvergence`) carry the geometric
hypotheses `x ∈ HalfSpace.upper n` and `y ∈ HalfSpace.boundary n` explicitly. Boundary data are
functions on all of `ℝ^n`; only their restriction to the hyperplane enters the integral.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), the definition of Green's function for the
  half-space, its normal derivative `∂G/∂ν`, Poisson's kernel `K` and Poisson's formula (33), p. 37.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open LaplacianEquation
open PDE.Analysis
open PotentialTheory
open MeasureTheory
open Set

/-- Poisson kernel for the upper half-space. -/
noncomputable def halfSpacePoissonKernel {n : ℕ} [Fact (0 < n)]
    (x y : ℝ^n) : ℝ :=
  (2 * x PDE.Common.lastIndex) / (n * unitBallVolume n * dist x y ^ n)

/-- Coordinate embedding of `ℝ^(n - 1)` into the boundary hyperplane
`x_n = 0` of `ℝ^n`. -/
noncomputable def halfSpaceEmb {n : ℕ} :
    ℝ^(n - 1) → ℝ^n :=
  fun y ↦
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm fun i ↦
      if hi : (i : ℕ) < n - 1 then y ⟨i, hi⟩ else 0

/-- Projection onto the first `n - 1` coordinates of `ℝ^n`. -/
noncomputable def halfSpaceProj {n : ℕ} (x : ℝ^n) : ℝ^(n - 1) :=
  WithLp.toLp 2 fun i : Fin (n - 1) ↦ x (i.castLT (by omega))

/-- Boundary measure on `SobolevSpace.HalfSpace.boundary n`, modeled as a pushforward of
`(n-1)`-dimensional volume. -/
noncomputable def halfSpaceBoundaryMeasure {n : ℕ} :
    MeasureTheory.Measure (ℝ^n) :=
  MeasureTheory.Measure.map (halfSpaceEmb (n := n))
    (MeasureTheory.volume :
      MeasureTheory.Measure (ℝ^(n - 1)))

/-- The Poisson extension associated to `halfSpacePoissonKernel`, integrating
against `halfSpaceBoundaryMeasure`. -/
noncomputable def poissonHalfSpaceExtension {n : ℕ} [Fact (0 < n)]
    (g : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  (2 * x PDE.Common.lastIndex) / (n * unitBallVolume n) *
    ∫ y, g y / dist x y ^ n ∂(halfSpaceBoundaryMeasure (n := n))

/-!
## Poisson formula for the half-space

The boundary is parametrized by appending a zero last coordinate. The lemmas below record the
geometry and pushforward-integral formula used by the analytic modules.
-/

section PoissonHalfSpace

open MeasureTheory Filter Topology
open scoped BigOperators
open scoped InnerProductSpace

variable {n : ℕ}

/-- The standard parametrization of the boundary hyperplane is continuous. -/
theorem continuous_halfSpaceEmb : Continuous (halfSpaceEmb (n := n)) := by
  classical
  let f : ℝ^(n - 1) → Fin n → ℝ := fun y i ↦
    if hi : (i : ℕ) < n - 1 then y ⟨i, hi⟩ else 0
  have hf : Continuous f := by
    refine continuous_pi ?_
    intro i
    by_cases hi : (i : ℕ) < n - 1
    · -- coordinate projection on `ℝ^(n - 1)`
      simpa [f, hi, EuclideanSpace.proj] using
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n - 1)) (⟨(i : ℕ), hi⟩ : Fin (n - 1))).continuous
    · simpa [f, hi] using (continuous_const : Continuous fun _ : ℝ^(n - 1) ↦ (0 : ℝ))
  rw [show halfSpaceEmb (n := n) =
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm ∘ f by
    funext y
    simp only [halfSpaceEmb, f, Function.comp_apply]]
  exact (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.continuous.comp hf

/-- The standard parametrization of the boundary hyperplane is measurable. -/
theorem measurable_halfSpaceEmb : Measurable (halfSpaceEmb (n := n)) :=
  (continuous_halfSpaceEmb (n := n)).measurable

/-- Projection onto the boundary coordinates is continuous. -/
theorem continuous_halfSpaceProj : Continuous (halfSpaceProj (n := n)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i ↦ (EuclideanSpace.proj (i.castLT (by omega))).continuous

/-- Projecting an embedded boundary point recovers its coordinates. -/
@[simp] lemma halfSpaceProj_halfSpaceEmb (a : ℝ^(n - 1)) :
    halfSpaceProj (halfSpaceEmb (n := n) a) = a := by
  ext i
  simp [halfSpaceProj, halfSpaceEmb]

private theorem integral_halfSpaceBoundaryMeasure (f : ℝ^n → ℝ)
    (hf : AEStronglyMeasurable f (halfSpaceBoundaryMeasure (n := n))) :
    (∫ y, f y ∂(halfSpaceBoundaryMeasure (n := n))) =
      ∫ y : ℝ^(n - 1), f (halfSpaceEmb (n := n) y) ∂(volume : Measure ℝ^(n - 1)) := by
  classical
  simpa [halfSpaceBoundaryMeasure] using
    (MeasureTheory.integral_map (μ := (volume : Measure ℝ^(n - 1)))
      (φ := halfSpaceEmb (n := n)) (f := f) (measurable_halfSpaceEmb (n := n)).aemeasurable hf)

variable [Fact (0 < n)]

/-- The last coordinate of a point in the boundary parametrization is zero. -/
theorem lastCoord_halfSpaceEmb (y : ℝ^(n - 1)) :
    (halfSpaceEmb (n := n) y) PDE.Common.lastIndex = 0 := by
  classical
  simp [PDE.Common.lastIndex, halfSpaceEmb]

/-- Every point in the image of `halfSpaceEmb` lies on the half-space boundary. -/
theorem halfSpaceEmb_mem_boundary (y : ℝ^(n - 1)) :
    halfSpaceEmb (n := n) y ∈ SobolevSpace.HalfSpace.boundary n := by
  classical
  have : (halfSpaceEmb (n := n) y) PDE.Common.lastIndex = 0 :=
    lastCoord_halfSpaceEmb (n := n) y
  simpa [SobolevSpace.HalfSpace.boundary] using this

/-!
### Basic rewriting lemmas for the boundary measure
-/

/-- Appending a zero coordinate preserves the Euclidean norm. -/
theorem norm_halfSpaceEmb (y : ℝ^(n - 1)) : ‖halfSpaceEmb (n := n) y‖ = ‖y‖ := by
  classical
  -- Compare squared norms, then take square roots.
  cases n with
  | zero =>
      -- Impossible by `Fact (0 < n)`.
      exfalso
      exact (lt_irrefl (0 : ℕ) (Fact.out : 0 < 0))
  | succ m =>
      -- Here `ℝ^(n - 1) = ℝ^m`, and the embedding appends a zero coordinate.
      have hsq :
          ‖halfSpaceEmb (n := m.succ) y‖ ^ 2 = ‖y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
        simp [halfSpaceEmb, Fin.sum_univ_castSucc]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- Tangential displacement is bounded by the full distance to the boundary point. -/
theorem norm_sub_halfSpaceProj_le_distance (x : ℝ^n) (y : ℝ^(n - 1)) :
    ‖y - halfSpaceProj (n := n) x‖ ≤ dist x (halfSpaceEmb (n := n) y) := by
  classical
  cases n with
  | zero =>
      exfalso
      exact (lt_irrefl (0 : ℕ) (Fact.out : 0 < 0))
  | succ m =>
      rw [← sq_le_sq₀ (norm_nonneg _) dist_nonneg, dist_eq_norm,
        EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      change
        (∑ i : Fin m, (y i - halfSpaceProj (n := m + 1) x i) ^ 2) ≤
          ∑ i : Fin (m + 1), (x i - halfSpaceEmb (n := m + 1) y i) ^ 2
      have hproj (i : Fin m) :
          halfSpaceProj (n := m + 1) x i = x i.castSucc := by
        change x (i.castLT (by omega)) = x i.castSucc
        exact congrArg (fun j ↦ x j) (Fin.ext (by rfl))
      have hemb_castSucc (i : Fin m) :
          halfSpaceEmb (n := m + 1) y i.castSucc = y i := by
        simp [halfSpaceEmb]
      have hemb_last :
          halfSpaceEmb (n := m + 1) y (Fin.last m) = 0 := by
        simp [halfSpaceEmb]
      have hleft :
          (∑ i : Fin m, (y i - halfSpaceProj (n := m + 1) x i) ^ 2) =
            ∑ i : Fin m, (x i.castSucc - y i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hproj]
        ring
      have hright :
          (∑ i : Fin (m + 1), (x i - halfSpaceEmb (n := m + 1) y i) ^ 2) =
            (∑ i : Fin m, (x i.castSucc - y i) ^ 2) + x (Fin.last m) ^ 2 := by
        simp only [Fin.sum_univ_castSucc, hemb_castSucc, hemb_last, sub_zero]
      rw [hleft, hright]
      exact le_add_of_nonneg_right (sq_nonneg _)

/-- An interior point's height bounds its distance to every boundary point. -/
theorem lastCoord_le_distance_halfSpaceEmb
    (x : ℝ^n) (hx : x ∈ SobolevSpace.HalfSpace.upper n)
    (y : ℝ^(n - 1)) : x PDE.Common.lastIndex ≤ dist x (halfSpaceEmb (n := n) y) := by
  classical
  -- Use Cauchy-Schwarz on the last coordinate.
  have hxpos : 0 < x PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx
  have hy0 : (halfSpaceEmb (n := n) y) (PDE.Common.lastIndex (n := n)) = 0 := by
    simp [halfSpaceEmb, PDE.Common.lastIndex]
  have hcoord :
      (x - halfSpaceEmb (n := n) y) (PDE.Common.lastIndex (n := n)) = x PDE.Common.lastIndex := by
    simp [hy0]
  have habs :
      |(x - halfSpaceEmb (n := n) y) (PDE.Common.lastIndex (n := n))| ≤
        ‖x - halfSpaceEmb (n := n) y‖ := by
    -- `|(x-y)_i| = |⟪e_i, x-y⟫| ≤ ‖e_i‖ * ‖x-y‖ = ‖x-y‖`.
    have habs' :=
      abs_real_inner_le_norm (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ))
        (x - halfSpaceEmb (n := n) y)
    have habs'' :
        |inner ℝ (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ))
            (x - halfSpaceEmb (n := n) y)| ≤
          ‖x - halfSpaceEmb (n := n) y‖ := by
      simpa [EuclideanSpace.single] using habs'
    have hinner :
        inner ℝ (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ))
            (x - halfSpaceEmb (n := n) y) =
          (x - halfSpaceEmb (n := n) y).ofLp (PDE.Common.lastIndex (n := n)) := by
      simp [EuclideanSpace.single, PiLp.inner_apply, PiLp.single_apply]
    -- Rewrite the inner product into the coordinate difference.
    simpa [hinner, PiLp.sub_apply]
      using habs''
  -- Turn the coordinate estimate into the desired bound on `dist`.
  have : x PDE.Common.lastIndex ≤ ‖x - halfSpaceEmb (n := n) y‖ := by
    -- remove abs using positivity
    have : |x PDE.Common.lastIndex| ≤ ‖x - halfSpaceEmb (n := n) y‖ := by
      simpa [hcoord] using habs
    rw [abs_of_pos hxpos] at this
    exact this
  -- `dist x (emb y) = ‖emb y - x‖ = ‖x - emb y‖`.
  simpa [dist_eq_norm] using this

/-- Rewrite the Poisson extension using Lebesgue measure on the boundary coordinates. -/
theorem poissonHalfSpaceExtension_eq_integral (g : ℝ^n → ℝ) (hg : Measurable g)
    (x : ℝ^n) :
    poissonHalfSpaceExtension (n := n) g x =
      (2 * x PDE.Common.lastIndex) / (n * unitBallVolume n) *
        ∫ y : ℝ^(n - 1), g (halfSpaceEmb (n := n) y) / dist x (halfSpaceEmb (n := n) y) ^ n
          ∂(volume : Measure ℝ^(n - 1)) := by
  classical
  -- Rewrite the integral against the pushforward measure.
  have hmeas :
      AEStronglyMeasurable
        (fun y : ℝ^n ↦ g y / dist x y ^ n) (halfSpaceBoundaryMeasure (n := n)) := by
    -- Measurable functions into `ℝ` are automatically a.e. strongly measurable.
    refine (Measurable.aestronglyMeasurable ?_)
    -- `dist x y` is continuous in `y`, hence measurable.
    have hdist_cont : Continuous fun y : ℝ^n ↦ dist x y := by
      exact continuous_const.dist continuous_id
    have hdist : Measurable fun y : ℝ^n ↦ dist x y := hdist_cont.measurable
    have hpow : Measurable fun y : ℝ^n ↦ dist x y ^ n := hdist.pow_const n
    have hinv : Measurable fun y : ℝ^n ↦ (dist x y ^ n)⁻¹ := hpow.inv
    have hmul : Measurable fun y : ℝ^n ↦ g y * (dist x y ^ n)⁻¹ := hg.mul hinv
    simpa [div_eq_mul_inv] using hmul
  -- Apply `integral_halfSpaceBoundaryMeasure`.
  simp [poissonHalfSpaceExtension,
    integral_halfSpaceBoundaryMeasure (n := n) (f := fun y ↦ g y / dist x y ^ n) hmeas]

end PoissonHalfSpace

end GreenFunction
