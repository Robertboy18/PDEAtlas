/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Laplacian.Cylindrical

/-!
# The Laplacian of an axisymmetric field on the meridian plane

A function `F` on `ℝ^3` invariant under the rotations about the third axis is determined by its
meridian slice `F̂(r, z) = F(r, 0, z)`. Off the axis its Laplacian at `(r, 0, z)` is the
axisymmetric Laplacian of the slice,

```text
Δ F (r, 0, z) = ∂_rr F̂ + r⁻¹ ∂_r F̂ + ∂_zz F̂,
```

because the angular derivatives in the cylindrical Laplacian vanish
(`laplacian_comp_meridianEmbedding`). Only `C²` regularity of `F` at the point is used.

## Main definitions

* `meridianEmbedding`: the linear map `(r, z) ↦ (r, 0, z)`.

## Main results

* `partialDeriv_comp_clm`, `partialDeriv_comp_clm_of_eq`, `secondPartialDeriv_comp_clm_of_eq`:
  coordinate derivatives of compositions with linear maps sending a basis vector to a multiple
  of a basis vector.
* `laplacian_comp_meridianEmbedding`: the Laplacian of an axisymmetric field at an off-axis
  meridian point.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems

open EuclideanSpace PDE
open scoped Topology

set_option linter.missingDocs true

variable {m n : ℕ}

/-- The coordinate derivative of `f ∘ A` for a linear map `A`. -/
theorem partialDeriv_comp_clm (A : ℝ^m →L[ℝ] ℝ^n) {f : ℝ^n → ℝ} {q : ℝ^m} (i : Fin m)
    (hf : DifferentiableAt ℝ f (A q)) :
    (∂[i] (f ∘ A)) q = fderiv ℝ f (A q) (A (single i 1)) := by
  rw [partialDeriv, fderiv_comp q hf A.differentiableAt, A.fderiv]
  rfl

/-- If a linear map sends the `i`th basis vector to `s` times the `j`th, the `i`th derivative of
`f ∘ A` is `s` times the `j`th derivative of `f` at the image point. -/
theorem partialDeriv_comp_clm_of_eq (A : ℝ^m →L[ℝ] ℝ^n) {f : ℝ^n → ℝ} {q : ℝ^m} {i : Fin m}
    {j : Fin n} {s : ℝ} (hA : A (single i 1) = s • single j 1)
    (hf : DifferentiableAt ℝ f (A q)) :
    (∂[i] (f ∘ A)) q = s * (∂[j] f) (A q) := by
  rw [partialDeriv_comp_clm A i hf, hA, map_smul, smul_eq_mul]
  rfl

/-- If a linear map sends the `i`th basis vector to `0`, the `i`th derivative of `f ∘ A`
vanishes. -/
theorem partialDeriv_comp_clm_of_eq_zero (A : ℝ^m →L[ℝ] ℝ^n) {f : ℝ^n → ℝ} {q : ℝ^m}
    {i : Fin m} (hA : A (single i 1) = 0) (hf : DifferentiableAt ℝ f (A q)) :
    (∂[i] (f ∘ A)) q = 0 := by
  rw [partialDeriv_comp_clm A i hf, hA, map_zero]

/-- The second `i`th derivative of `f ∘ A` is `s²` times the second `j`th derivative of `f`
when `A` sends the `i`th basis vector to `s` times the `j`th and `f` is `C²` at the image
point. -/
theorem secondPartialDeriv_comp_clm_of_eq (A : ℝ^m →L[ℝ] ℝ^n) {f : ℝ^n → ℝ} {q : ℝ^m}
    {i : Fin m} {j : Fin n} {s : ℝ} (hA : A (single i 1) = s • single j 1)
    (hf : ContDiffAt ℝ 2 f (A q)) :
    (∂[i] (∂[i] (f ∘ A))) q = s ^ 2 * (∂[j] (∂[j] f)) (A q) := by
  have hev : ∀ᶠ y in 𝓝 q, DifferentiableAt ℝ f (A y) := by
    filter_upwards [(A.continuous.tendsto q).eventually (hf.eventually (by simp))] with y hy
    exact hy.differentiableAt (by simp)
  have heq : (∂[i] (f ∘ A)) =ᶠ[𝓝 q] fun y ↦ s * ((∂[j] f) ∘ A) y := by
    filter_upwards [hev] with y hy
    exact partialDeriv_comp_clm_of_eq A hA hy
  have hd : DifferentiableAt ℝ (∂[j] f) (A q) :=
    (hf.partialDeriv j (k := 1) (by norm_num)).differentiableAt (by simp)
  have hconst : (∂[i] (fun y ↦ s * ((∂[j] f) ∘ A) y)) q = s * (∂[i] ((∂[j] f) ∘ A)) q := by
    simpa [smul_eq_mul] using partialDeriv_const_smul (i := i) (f := (∂[j] f) ∘ A) (x := q) s
  rw [partialDeriv, heq.fderiv_eq]
  change (∂[i] (fun y ↦ s * ((∂[j] f) ∘ A) y)) q = _
  rw [hconst, partialDeriv_comp_clm_of_eq A hA hd]
  ring

/-- The second `i`th derivative of `f ∘ A` vanishes when `A` sends the `i`th basis vector to
`0` and `f` is differentiable near the image point. -/
theorem secondPartialDeriv_comp_clm_of_eq_zero (A : ℝ^m →L[ℝ] ℝ^n) {f : ℝ^n → ℝ} {q : ℝ^m}
    {i : Fin m} (hA : A (single i 1) = 0) (hf : ContDiffAt ℝ 2 f (A q)) :
    (∂[i] (∂[i] (f ∘ A))) q = 0 := by
  have hev : ∀ᶠ y in 𝓝 q, DifferentiableAt ℝ f (A y) := by
    filter_upwards [(A.continuous.tendsto q).eventually (hf.eventually (by simp))] with y hy
    exact hy.differentiableAt (by simp)
  have heq : (∂[i] (f ∘ A)) =ᶠ[𝓝 q] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hev] with y hy
    exact partialDeriv_comp_clm_of_eq_zero A hA hy
  rw [partialDeriv, heq.fderiv_eq]
  simp

/-- The meridian embedding `(r, z) ↦ (r, 0, z)` of the meridian plane into `ℝ^3`. -/
def meridianEmbedding : ℝ^2 →L[ℝ] ℝ^3 :=
  (proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).smulRight (single (0 : Fin 3) (1 : ℝ)) +
    (proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).smulRight (single (2 : Fin 3) (1 : ℝ))

/-- The meridian embedding is `meridianPoint`. -/
theorem meridianEmbedding_apply (p : ℝ^2) : meridianEmbedding p = meridianPoint (p 0) (p 1) := by
  ext i
  fin_cases i <;> simp [meridianEmbedding, meridianPoint]

/-- The projection `(q₀, q₁, q₂) ↦ (q₀, q₂)`, forgetting the angle of cylindrical coordinates. -/
def radialAxialProjection : ℝ^3 →L[ℝ] ℝ^2 :=
  (proj (0 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight (single (0 : Fin 2) (1 : ℝ)) +
    (proj (2 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight (single (1 : Fin 2) (1 : ℝ))

/-- The cylindrical chart is the rotation by the angle of the meridian embedding of the radius
and the height. -/
theorem cylindricalMap_eq_axisRotation (q : ℝ^3) :
    cylindricalMap q = axisRotation (q 1) (meridianEmbedding (radialAxialProjection q)) := by
  rw [cylindricalMap_apply]
  ext i
  fin_cases i <;> simp [meridianEmbedding, radialAxialProjection, axisRotation] <;> ring

/-- **The Laplacian of an axisymmetric field on the meridian plane.** For `F` invariant under the
rotations about the third axis and `C²` at the off-axis point `(r, 0, z)`, with meridian slice
`F̂ = F ∘ meridianEmbedding`, `Δ F (r, 0, z) = Δ F̂ (r, z) + ∂_r F̂ (r, z) / r`. -/
theorem laplacian_comp_meridianEmbedding {F : ℝ^3 → ℝ} (hF : IsInvariantUnderAxisRotation F)
    {p : ℝ^2} (hp : p 0 ≠ 0) (hreg : ContDiffAt ℝ 2 F (meridianEmbedding p)) :
    laplacian F (meridianEmbedding p) =
      laplacian (F ∘ meridianEmbedding) p + (∂[0] (F ∘ meridianEmbedding)) p / p 0 := by
  set f : ℝ^2 → ℝ := F ∘ meridianEmbedding
  set q : ℝ^3 := WithLp.toLp 2 ![p 0, 0, p 1]
  have hq : cylindricalMap q = meridianEmbedding p := by
    rw [cylindricalMap_apply, meridianEmbedding_apply]
    ext i
    fin_cases i <;> simp [q, meridianPoint]
  have hAq : radialAxialProjection q = p := by
    ext i
    fin_cases i <;> simp [q, radialAxialProjection]
  have hcomp : F ∘ cylindricalMap = f ∘ radialAxialProjection := by
    funext x
    simp only [Function.comp_apply, f]
    rw [cylindricalMap_eq_axisRotation, hF]
  have hfreg : ContDiffAt ℝ 2 f (radialAxialProjection q) := by
    rw [hAq]
    exact hreg.comp p meridianEmbedding.contDiff.contDiffAt
  have hA0 : radialAxialProjection (single (0 : Fin 3) 1) = (1 : ℝ) • single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [radialAxialProjection]
  have hA1 : radialAxialProjection (single (1 : Fin 3) 1) = 0 := by
    ext i
    fin_cases i <;> simp [radialAxialProjection]
  have hA2 : radialAxialProjection (single (2 : Fin 3) 1) = (1 : ℝ) • single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [radialAxialProjection]
  have hq0 : q 0 = p 0 := by simp [q]
  have hcyl := cylindricalLaplacian_comp_cylindricalMap (f := F) (q := q) (by rwa [hq])
    (by rwa [hq0])
  rw [hq] at hcyl
  rw [← hcyl, hcomp, cylindricalLaplacian,
    secondPartialDeriv_comp_clm_of_eq _ hA0 hfreg,
    partialDeriv_comp_clm_of_eq _ hA0 (hfreg.differentiableAt (by simp)),
    secondPartialDeriv_comp_clm_of_eq_zero _ hA1 hfreg,
    secondPartialDeriv_comp_clm_of_eq _ hA2 hfreg, hAq, hq0]
  simp only [laplacian, Fin.sum_univ_two, smul_eq_mul, mul_zero, add_zero]
  field_simp
  ring

end PDE.CoordinateSystems
