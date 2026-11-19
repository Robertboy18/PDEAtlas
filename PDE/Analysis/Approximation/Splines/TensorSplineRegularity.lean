/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.CheckedBranchRegularity
public import PDE.Analysis.Approximation.Splines.TensorBranchEnclosure
public import PDE.Analysis.Approximation.Splines.TensorHornerDerivatives

/-!
# Finite regularity and jets of rational tensor splines

Exact one-dimensional branch and jet checks give joint finite regularity of the
assembled coefficient tensor, including grid knots and their intersections.
The mixed derivative formula retains the separate regularity budgets in the two
coordinates. Coefficients, degrees, counts, and both knot sequences are arbitrary.

On an open cell, the symbolic branch represents the source on a
neighborhood. At grid knots we use matched jets instead: finite regularity does
not imply equality to a single polynomial on a full neighborhood.
-/

@[expose] public section

namespace CAS.Splines

open CAS.Verified Set
open scoped Topology

section CheckedTensor

variable {qx qy : ℕ → ℚ} {lx rx ly ry px py rows cols sx sy : ℕ}
    (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (cx : CoxDeBoorJetCertificate qx lx rx px rows sx)
    (cy : CoxDeBoorJetCertificate qy ly ry py cols sy)

include hxknots hyknots cx cy in
/-- Matching basis jets gives joint finite regularity of the tensor at
every point of the neighboring rectangle, including its interior grid lines. -/
theorem contDiffAt_rationalTensorSpline (coefficient : ℕ → ℕ → ℚ)
    (n : ℕ) (hnx : n ≤ sx) (hny : n ≤ sy) {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (kx lx) (kx (rx + 1)))
    (hy : p.2 ∈ Ioo (ky ly) (ky (ry + 1))) :
    ContDiffAt ℝ n
      (fun q : ℝ × ℝ ↦ rationalTensorSpline kx ky px py rows cols coefficient q.1 q.2) p := by
  unfold rationalTensorSpline
  apply ContDiffAt.sum
  intro i hi
  apply ((cx.contDiffAt_basis kx hxknots ⟨i, Finset.mem_range.mp hi⟩ n hnx hx).comp
    p contDiffAt_fst).mul
  apply ContDiffAt.sum
  intro j hj
  exact ((cy.contDiffAt_basis ky hyknots ⟨j, Finset.mem_range.mp hj⟩ n hny hy).comp
    p contDiffAt_snd).mul contDiffAt_const

include hyknots cy in
/-- Every fixed radial slice has the independently checked axial regularity. -/
theorem contDiffAt_rationalTensorSpline_axial (coefficient : ℕ → ℕ → ℚ)
    (b : ℕ) (hb : b ≤ sy) (x : ℝ) {y : ℝ}
    (hy : y ∈ Ioo (ky ly) (ky (ry + 1))) :
    ContDiffAt ℝ b (rationalTensorSpline kx ky px py rows cols coefficient x) y := by
  unfold rationalTensorSpline
  apply ContDiffAt.sum
  intro i _
  apply contDiffAt_const.mul
  exact ContDiffAt.sum fun j hj ↦
    (cy.contDiffAt_basis ky hyknots ⟨j, Finset.mem_range.mp hj⟩ b hb hy).mul contDiffAt_const

include hyknots cy in
/-- Axial differentiation passes through the finite tensor sum using the checked
axial regularity. The radial coordinate is unrestricted. -/
theorem iteratedDeriv_rationalTensorSpline_axial (coefficient : ℕ → ℕ → ℚ)
    (b : ℕ) (hb : b ≤ sy) (x : ℝ) {y : ℝ}
    (hy : y ∈ Ioo (ky ly) (ky (ry + 1))) :
    iteratedDeriv b (rationalTensorSpline kx ky px py rows cols coefficient x) y =
      ∑ i ∈ Finset.range rows, coxDeBoorBasis kx px i x *
        ∑ j ∈ Finset.range cols, iteratedDeriv b (coxDeBoorBasis ky py j) y *
          (coefficient i j : ℝ) := by
  have hterm (i j : ℕ) (hj : j ∈ Finset.range cols) :
      ContDiffAt ℝ b (fun z ↦ coxDeBoorBasis ky py j z * (coefficient i j : ℝ)) y :=
    (cy.contDiffAt_basis ky hyknots ⟨j, Finset.mem_range.mp hj⟩ b hb hy).mul contDiffAt_const
  unfold rationalTensorSpline
  rw [iteratedDeriv_fun_sum (fun i _ ↦
    contDiffAt_const.mul (ContDiffAt.sum (fun j hj ↦ hterm i j hj)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sum (fun j hj ↦ hterm i j hj)]
  simp only [iteratedDeriv_mul_const_field]

include hxknots hyknots cx cy in
/-- Checked tensor jets are mixed iterated derivatives even at grid knots.
The separate bounds `a ≤ sx` and `b ≤ sy` suffice for a finite tensor product. -/
theorem mixed_iteratedDeriv_rationalTensorSpline (coefficient : ℕ → ℕ → ℚ)
    (a b : ℕ) (ha : a ≤ sx) (hb : b ≤ sy) {x y : ℝ}
    (hx : x ∈ Ioo (kx lx) (kx (rx + 1)))
    (hy : y ∈ Ioo (ky ly) (ky (ry + 1))) :
    iteratedDeriv a
      (fun r ↦ iteratedDeriv b (rationalTensorSpline kx ky px py rows cols coefficient r) y) x =
      ∑ i ∈ Finset.range rows, iteratedDeriv a (coxDeBoorBasis kx px i) x *
        ∑ j ∈ Finset.range cols, iteratedDeriv b (coxDeBoorBasis ky py j) y *
          (coefficient i j : ℝ) := by
  rw [funext (fun r ↦
    iteratedDeriv_rationalTensorSpline_axial kx ky hyknots cy coefficient b hb r hy)]
  rw [iteratedDeriv_fun_sum (fun i hi ↦
    (cx.contDiffAt_basis kx hxknots ⟨i, Finset.mem_range.mp hi⟩ a ha hx).mul contDiffAt_const)]
  simp only [iteratedDeriv_mul_const_field]

include hxknots hyknots cx cy in
/-- Axial jets retain the independently checked radial regularity.
This supplies the slice regularity used to replay derivatives on closed cells. -/
theorem contDiffAt_rationalTensorSpline_axialJet (coefficient : ℕ → ℕ → ℚ)
    (a b : ℕ) (ha : a ≤ sx) (hb : b ≤ sy) {x y : ℝ}
    (hx : x ∈ Ioo (kx lx) (kx (rx + 1)))
    (hy : y ∈ Ioo (ky ly) (ky (ry + 1))) :
    ContDiffAt ℝ a
      (fun r ↦
        iteratedDeriv b (rationalTensorSpline kx ky px py rows cols coefficient r) y) x := by
  rw [funext (fun r ↦
    iteratedDeriv_rationalTensorSpline_axial kx ky hyknots cy coefficient b hb r hy)]
  exact ContDiffAt.sum fun i hi ↦
    (cx.contDiffAt_basis kx hxknots ⟨i, Finset.mem_range.mp hi⟩ a ha hx).mul contDiffAt_const

include hxknots hyknots cx cy in
/-- Exact branch normalization gives the mixed source jet on a half-closed
cell, including its lower grid edges and corner. Matching basis jets supply the
ordinary derivative regularity at those interfaces. No analytic branch equality
or derivative enclosure is a premise. -/
theorem mixed_iteratedDeriv_rationalTensorSpline_of_polynomial_check
    (coefficient : ℕ → ℕ → ℚ) (cellX cellY nx ny : ℕ) (polynomial : ℕ → ℕ → ℚ)
    (hcheck : polynomialIdentityCheck
      (tensorBranchExpr qx qy (0 : Fin 2) 1 cellX cellY px py rows cols coefficient)
      (tensorHornerExpr (tensorCoefficients nx ny polynomial)) = true)
    (a b : ℕ) (ha : a ≤ sx) (hb : b ≤ sy) {x y : ℝ}
    (hx : x ∈ Ioo (kx lx) (kx (rx + 1)))
    (hy : y ∈ Ioo (ky ly) (ky (ry + 1)))
    (hxcell : x ∈ Ico (kx cellX) (kx (cellX + 1)))
    (hycell : y ∈ Ico (ky cellY) (ky (cellY + 1))) :
    iteratedDeriv a
      (fun r ↦ iteratedDeriv b (rationalTensorSpline kx ky px py rows cols coefficient r) y) x =
        tensorHornerValue (tensorDerivativeCoefficients nx ny polynomial a b) x y := by
  apply mixed_iteratedDeriv_eq_tensorHorner_of_eqOn nx ny polynomial
    (rationalTensorSpline kx ky px py rows cols coefficient) a b
    (uniqueDiffOn_Ico _ _) (uniqueDiffOn_Ico _ _) hxcell hycell
  · intro r hr z hz
    let ρ : Fin 2 → ℝ := ![r, z]
    have hvalue := polynomialIdentityCheck_sound _ _ hcheck (WithLp.toLp 2 ρ)
    change (tensorBranchExpr qx qy (0 : Fin 2) 1 cellX cellY px py rows cols
      coefficient).eval ρ =
        (tensorHornerExpr (tensorCoefficients nx ny polynomial)).eval ρ at hvalue
    rw [tensorBranchExpr_eval qx qy (0 : Fin 2) 1 ρ kx ky hxknots hyknots
      cellX cellY px py rows cols coefficient hr hz, tensorHornerExpr_eval] at hvalue
    exact hvalue
  · intro r _
    exact contDiffAt_rationalTensorSpline_axial kx ky hyknots cy coefficient b hb r hy
  · exact contDiffAt_rationalTensorSpline_axialJet kx ky hxknots hyknots cx cy
      coefficient a b ha hb hx hy

end CheckedTensor

/-- In the interior of an active cell, the branch expression represents the
assembled source on a full neighborhood, as required by symbolic derivative replay. -/
theorem rationalTensorSpline_eventuallyEq_tensorBranchExpr (qx qy : ℕ → ℚ)
    (kx ky : KnotSequence)
    (hxknots : ∀ i, kx i = (qx i : ℝ))
    (hyknots : ∀ i, ky i = (qy i : ℝ))
    (cellX cellY degreeX degreeY rows cols : ℕ) (coefficient : ℕ → ℕ → ℚ)
    {p : ℝ^2}
    (hx : p 0 ∈ Ioo (kx cellX) (kx (cellX + 1)))
    (hy : p 1 ∈ Ioo (ky cellY) (ky (cellY + 1))) :
    (fun q : ℝ^2 ↦ rationalTensorSpline kx ky degreeX degreeY rows cols coefficient (q 0) (q 1))
      =ᶠ[𝓝 p] fun q ↦
        (tensorBranchExpr qx qy (0 : Fin 2) 1 cellX cellY degreeX degreeY rows cols
          coefficient).eval q := by
  have hproj (i : Fin 2) : Continuous (fun q : ℝ^2 ↦ q i) := by fun_prop
  filter_upwards [(isOpen_Ioo.preimage (hproj 0)).mem_nhds hx,
    (isOpen_Ioo.preimage (hproj 1)).mem_nhds hy] with q hqx hqy
  exact (tensorBranchExpr_eval qx qy (0 : Fin 2) 1 q kx ky hxknots hyknots
    cellX cellY degreeX degreeY rows cols coefficient
    ⟨hqx.1.le, hqx.2⟩ ⟨hqy.1.le, hqy.2⟩).symm

end CAS.Splines
