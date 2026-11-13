/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Euclidean.Norm
public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Cartesian differentiation of spherical axisymmetric fields

The polar cosine `x₃ / ‖x‖` is smooth away from the origin, including the
symmetry axis. Writing meridional fields using this cosine avoids divisions
by the cylindrical radius in Cartesian reconstruction. The radial component of a
meridional field `F(r) S(cos θ) e_r + G(r) T(cos θ) sin θ e_θ` is `F(r) S(cos θ)`, and
azimuthal fields are orthogonal to the position.
-/

@[expose] public noncomputable section

namespace PDE.FDeriv.Spherical

open scoped RealInnerProductSpace

/-- The polar cosine, with the third coordinate as the symmetry axis. -/
def polarCosine (x : ℝ^3) : ℝ := x 2 / ‖x‖

/-- The polar cosine is differentiable away from the origin, including on the axis. -/
theorem hasFDerivAt_polarCosine {x : ℝ^3} (hx : x ≠ 0) :
    HasFDerivAt polarCosine
      (‖x‖⁻¹ • EuclideanSpace.proj (2 : Fin 3) - (x 2 / ‖x‖ ^ 2) •
        innerSL ℝ (‖x‖⁻¹ • x)) x := by
  have hn := EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn
  have hd := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.mul hi
  unfold polarCosine
  convert hd using 1
  · ext y
    exact div_eq_mul_inv _ _
  · ext v
    simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply,
      EuclideanSpace.coe_proj, smul_eq_mul, div_eq_mul_inv, Function.comp_def]
    ring

/-- A scalar coefficient times the position vector plus an axial field has
divergence given by one radial directional derivative and one axial derivative. -/
theorem divergence_scalar_position_add_axial {a b : ℝ^3 → ℝ} {x : ℝ^3}
    {da db : ℝ^3 →L[ℝ] ℝ} (ha : HasFDerivAt a da x) (hb : HasFDerivAt b db x) :
    PDE.divergence (fun y ↦ a y • y + b y • EuclideanSpace.single (2 : Fin 3) 1) x =
      da x + 3 * a x + db (EuclideanSpace.single (2 : Fin 3) 1) := by
  have hcoord (i : Fin 3) :
      PDE.partialDeriv i (fun y : ℝ^3 ↦ ((a y • y + b y •
        EuclideanSpace.single (2 : Fin 3) 1) : ℝ^3) i) x =
      da (EuclideanSpace.single i 1) * x i + a x +
        db (EuclideanSpace.single i 1) * (EuclideanSpace.single (2 : Fin 3) 1) i := by
    have hd := (ha.mul (EuclideanSpace.proj i).hasFDerivAt).add
      (hb.mul_const ((EuclideanSpace.single (2 : Fin 3) 1) i))
    change HasFDerivAt (fun y : ℝ^3 ↦ a y * y i + b y *
      (EuclideanSpace.single (2 : Fin 3) 1) i) _ x at hd
    have heq : (fun y : ℝ^3 ↦ ((a y • y + b y •
        EuclideanSpace.single (2 : Fin 3) 1) : ℝ^3) i) =
      fun y ↦ a y * y i + b y * (EuclideanSpace.single (2 : Fin 3) 1) i := by
      ext y
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [heq, PDE.partialDeriv, hd.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply,
      EuclideanSpace.coe_proj, PiLp.single_apply, ite_true, mul_one, smul_eq_mul]
    ring
  have hsplit : da x = da (EuclideanSpace.single (0 : Fin 3) 1) * x 0 +
      da (EuclideanSpace.single (1 : Fin 3) 1) * x 1 +
      da (EuclideanSpace.single (2 : Fin 3) 1) * x 2 := by
    have hx' : x = x 0 • EuclideanSpace.single (0 : Fin 3) 1 +
        x 1 • EuclideanSpace.single (1 : Fin 3) 1 +
        x 2 • EuclideanSpace.single (2 : Fin 3) 1 := by
      ext i
      fin_cases i <;> simp
    calc
      da x = da (x 0 • EuclideanSpace.single (0 : Fin 3) 1 +
        x 1 • EuclideanSpace.single (1 : Fin 3) 1 +
        x 2 • EuclideanSpace.single (2 : Fin 3) 1) := congrArg da hx'
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]; ring
  unfold PDE.divergence
  simp only [hcoord, Fin.sum_univ_three, PiLp.single_apply]
  norm_num
  linarith only [hsplit]

/-- The derivative of the Euclidean radius in the position direction is the radius itself. -/
theorem radiusDerivative_apply_self {x : ℝ^3} (hx : x ≠ 0) :
    innerSL ℝ (‖x‖⁻¹ • x) x = ‖x‖ := by
  simp only [innerSL_apply_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

/-- The axial derivative of the radius is the polar cosine. -/
theorem radiusDerivative_apply_axis (x : ℝ^3) :
    innerSL ℝ (‖x‖⁻¹ • x) (EuclideanSpace.single (2 : Fin 3) 1) = polarCosine x := by
  have h : inner ℝ x (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) = x 2 := by
    simpa using EuclideanSpace.inner_single_right (i := (2 : Fin 3)) (a := (1 : ℝ)) (v := x)
  rw [innerSL_apply_apply, real_inner_smul_left, h]
  simp only [polarCosine, div_eq_mul_inv]
  ring

/-- The polar cosine does not change in the position direction. -/
theorem polarCosineDerivative_apply_self {x : ℝ^3} (hx : x ≠ 0) :
    ((‖x‖⁻¹ • EuclideanSpace.proj (2 : Fin 3) - (x 2 / ‖x‖ ^ 2) •
      innerSL ℝ (‖x‖⁻¹ • x)) : ℝ^3 →L[ℝ] ℝ) x = 0 := by
  simp only [_root_.sub_apply, _root_.smul_apply, EuclideanSpace.coe_proj,
    smul_eq_mul, radiusDerivative_apply_self hx]
  field_simp
  ring

/-- The axial derivative of the polar cosine is nonsingular away from the origin. -/
theorem polarCosineDerivative_apply_axis {x : ℝ^3} (hx : x ≠ 0) :
    ((‖x‖⁻¹ • EuclideanSpace.proj (2 : Fin 3) - (x 2 / ‖x‖ ^ 2) •
      innerSL ℝ (‖x‖⁻¹ • x)) : ℝ^3 →L[ℝ] ℝ) (EuclideanSpace.single (2 : Fin 3) 1) =
        (1 - polarCosine x ^ 2) / ‖x‖ := by
  simp only [_root_.sub_apply, _root_.smul_apply, EuclideanSpace.coe_proj,
    smul_eq_mul, PiLp.single_apply, ite_true, radiusDerivative_apply_axis, polarCosine]
  field_simp

/-- A meridional spherical mode reconstructed directly in Cartesian coordinates.
`T` is the angular polynomial derivative, and the polar angular basis is `sin θ * T`.
No cylindrical-radius denominator occurs. -/
def meridionalField (F G S T : ℝ → ℝ) (x : ℝ^3) : ℝ^3 :=
  ((F ‖x‖ * S (polarCosine x) + G ‖x‖ * T (polarCosine x) * polarCosine x) * ‖x‖⁻¹) • x +
    (-(G ‖x‖ * T (polarCosine x))) • EuclideanSpace.single (2 : Fin 3) 1

/-- Cartesian divergence of a spherical meridional mode, including on the symmetry axis. -/
theorem divergence_meridionalField {F G S T : ℝ → ℝ} {x : ℝ^3} (hx : x ≠ 0)
    {F' G' T' : ℝ}
    (hF : HasDerivAt F F' ‖x‖) (hG : HasDerivAt G G' ‖x‖)
    (hS : HasDerivAt S (T (polarCosine x)) (polarCosine x))
    (hT : HasDerivAt T T' (polarCosine x)) :
    PDE.divergence (meridionalField F G S T) x =
      (F' + 2 * F ‖x‖ / ‖x‖) * S (polarCosine x) +
        G ‖x‖ / ‖x‖ * (2 * polarCosine x * T (polarCosine x) -
          (1 - polarCosine x ^ 2) * T') := by
  have hn := EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx
  have hc := hasFDerivAt_polarCosine hx
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn
  have hf := hF.comp_hasFDerivAt x hn
  have hg := hG.comp_hasFDerivAt x hn
  have hs := hS.comp_hasFDerivAt x hc
  have ht := hT.comp_hasFDerivAt x hc
  have ha := ((hf.mul hs).add ((hg.mul ht).mul hc)).mul hi
  have hb := (hg.mul ht).neg
  have hdiv := divergence_scalar_position_add_axial ha hb
  change PDE.divergence (meridionalField F G S T) x = _ at hdiv
  rw [hdiv]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply,
    Function.comp_def, Pi.mul_apply, Pi.add_apply, smul_eq_mul,
    radiusDerivative_apply_self hx, radiusDerivative_apply_axis,
    polarCosineDerivative_apply_self hx, polarCosineDerivative_apply_axis hx]
  unfold polarCosine
  field_simp
  ring

/-- Smooth radial and polar-cosine coefficients give a differentiable meridional field
away from the origin, even on the symmetry axis. -/
theorem differentiableAt_meridionalField {F G S T : ℝ → ℝ} {x : ℝ^3} (hx : x ≠ 0)
    (hF : DifferentiableAt ℝ F ‖x‖) (hG : DifferentiableAt ℝ G ‖x‖)
    (hS : DifferentiableAt ℝ S (polarCosine x))
    (hT : DifferentiableAt ℝ T (polarCosine x)) :
    DifferentiableAt ℝ (meridionalField F G S T) x := by
  have hn := (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx).differentiableAt
  have hc := (hasFDerivAt_polarCosine hx).differentiableAt
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).differentiableAt.comp x hn
  have hf := hF.comp x hn
  have hg := hG.comp x hn
  have hs := hS.comp x hc
  have ht := hT.comp x hc
  have ha := ((hf.mul hs).add ((hg.mul ht).mul hc)).mul hi
  have hb := (hg.mul ht).neg
  exact (ha.smul differentiableAt_id).add
    (hb.smul (differentiableAt_const (c := EuclideanSpace.single (2 : Fin 3) (1 : ℝ))))

/-- The radius derivative in a coordinate direction. -/
theorem radiusDerivative_apply_coord (x : ℝ^3) (i : Fin 3) :
    innerSL ℝ (‖x‖⁻¹ • x) (EuclideanSpace.single i 1) = x i / ‖x‖ := by
  have h : inner ℝ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
    simpa using EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (v := x)
  rw [innerSL_apply_apply, real_inner_smul_left, h]
  simp only [div_eq_mul_inv]
  ring

/-- The azimuthal spherical field in Cartesian coordinates, with an angular polynomial
coefficient after the factor `sin θ` cancels the spherical frame denominator. -/
def azimuthalField (H A : ℝ → ℝ) (x : ℝ^3) : ℝ^3 :=
  let q := H ‖x‖ * A (polarCosine x) * ‖x‖⁻¹
  WithLp.toLp 2 ![-(q * x 1), q * x 0, 0]

/-- Any differentiable radial and polar-cosine azimuthal coefficient has zero divergence. -/
theorem divergence_azimuthalField_eq_zero {H A : ℝ → ℝ} {x : ℝ^3} (hx : x ≠ 0)
    {H' A' : ℝ} (hH : HasDerivAt H H' ‖x‖)
    (hA : HasDerivAt A A' (polarCosine x)) :
    PDE.divergence (azimuthalField H A) x = 0 := by
  have hn := EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx
  have hc := hasFDerivAt_polarCosine hx
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn
  have hh := hH.comp_hasFDerivAt x hn
  have ha := hA.comp_hasFDerivAt x hc
  let q : ℝ^3 → ℝ := fun y ↦ H ‖y‖ * A (polarCosine y) * ‖y‖⁻¹
  have hq := (hh.mul ha).mul hi
  change HasFDerivAt q _ x at hq
  have hgrad : PDE.partialDeriv 0 q x * x 1 = PDE.partialDeriv 1 q x * x 0 := by
    rw [PDE.partialDeriv, PDE.partialDeriv, hq.fderiv]
    simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, smul_eq_mul,
      Function.comp_def, Pi.mul_apply, radiusDerivative_apply_coord, EuclideanSpace.coe_proj,
      PiLp.single_apply]
    norm_num
    ring
  unfold PDE.divergence
  rw [Fin.sum_univ_three]
  change PDE.partialDeriv 0 (fun y ↦ -(q y * y 1)) x +
    PDE.partialDeriv 1 (fun y ↦ q y * y 0) x + PDE.partialDeriv 2 (fun _ ↦ (0 : ℝ)) x = 0
  have hz (i : Fin 3) : DifferentiableAt ℝ (fun y : ℝ^3 ↦ y i) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt (x := x)
  rw [show (fun y : ℝ^3 ↦ -(q y * y 1)) = -(fun y : ℝ^3 ↦ q y * y 1) from rfl,
    partialDeriv_neg,
    partialDeriv_mul hq.differentiableAt (hz 1),
    partialDeriv_mul hq.differentiableAt (hz 0),
    partialDeriv_const, partialDeriv_coord, partialDeriv_coord]
  norm_num
  linarith only [hgrad]

/-- The azimuthal reconstruction is differentiable away from the origin. -/
theorem differentiableAt_azimuthalField {H A : ℝ → ℝ} {x : ℝ^3} (hx : x ≠ 0)
    (hH : DifferentiableAt ℝ H ‖x‖) (hA : DifferentiableAt ℝ A (polarCosine x)) :
    DifferentiableAt ℝ (azimuthalField H A) x := by
  have hn := (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx).differentiableAt
  have hc := (hasFDerivAt_polarCosine hx).differentiableAt
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).differentiableAt.comp x hn
  have hq := ((hH.comp x hn).mul (hA.comp x hc)).mul hi
  have hz (i : Fin 3) : DifferentiableAt ℝ (fun y : ℝ^3 ↦ y i) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt (x := x)
  apply (differentiableAt_piLp (2 : ENNReal)).mpr
  intro i
  fin_cases i
  · exact (hq.mul (hz 1)).neg
  · exact hq.mul (hz 0)
  · change DifferentiableAt ℝ (fun _ : ℝ^3 ↦ (0 : ℝ)) x
    exact differentiableAt_const 0

/-- Cartesian divergence distributes over a finite sum of fields differentiable at the point. -/
theorem divergence_sum {ι : Type*} [Fintype ι] (u : ι → ℝ^3 → ℝ^3) (x : ℝ^3)
    (hu : ∀ j, DifferentiableAt ℝ (u j) x) :
    PDE.divergence (fun y ↦ ∑ j, u j y) x = ∑ j, PDE.divergence (u j) x := by
  have hcoord (i : Fin 3) : (fun y ↦ (∑ j, u j y) i) =
      fun y ↦ ∑ j, u j y i := by
    ext y
    exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) i) _ _
  unfold PDE.divergence
  simp only [hcoord]
  have hd (i : Fin 3) := partialDeriv_sum (n := 3) Finset.univ
    (f := fun j y ↦ (u j y) i) (fun j _ ↦
      (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x (hu j)) i
  simp only [hd]
  exact Finset.sum_comm

/-- The radial component of a meridional field: `⟪x, M(x)⟫ = ‖x‖ F(‖x‖) S(cos θ)`. -/
theorem inner_meridionalField (F G S T : ℝ → ℝ) {x : ℝ^3} (hx : x ≠ 0) :
    ⟪x, meridionalField F G S T x⟫ = ‖x‖ * F ‖x‖ * S (polarCosine x) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [meridionalField, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_single_right, polarCosine]
  simp only [conj_trivial]
  field_simp
  ring

/-- Azimuthal fields are orthogonal to the position. -/
theorem inner_azimuthalField (H A : ℝ → ℝ) (x : ℝ^3) : ⟪x, azimuthalField H A x⟫ = 0 := by
  simp only [azimuthalField, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial]
  simp
  ring

end PDE.FDeriv.Spherical
