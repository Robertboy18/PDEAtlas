/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.CrossProduct
public import PDE.Common.Euclidean

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import PDE.Analysis.Matrix.Determinant.Derivative

/-!
# Smooth families of GN-neutral bilinear corrections

The covectors are normalized determinants. The two coefficients are obtained by
inverting the continuous linear map whose columns are the two projected frame
vectors. This is a fixed-coordinate two-dimensional inverse, so no family of
chosen bases is differentiated.

The formula and its pointwise specification also give an explicit witness for
the existential pointwise construction. The family theorem only requires the
tangent coordinate in the omitted frame direction to be nonzero.
-/

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise

namespace PDE.Analysis.GNNeutralHessian

/-- The covector with value `det(v,u,x) / det(v,u,W)` at `x`, in that row order.
It is defined everywhere; its normalization and smoothness require the displayed
denominator to be nonzero only at the points under consideration. -/
def normalizedDetCovector (v u W : ℝ^3) : (ℝ^3) →L[ℝ] ℝ :=
  let e : (ℝ^3) ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  (Matrix.det ![⇑v, ⇑u, ⇑W])⁻¹ •
    ((dotProductBilin ℝ ℝ (e v ⨯₃ e u)).comp e.toLinearMap).toContinuousLinearMap

theorem normalizedDetCovector_apply (v u W x : ℝ^3) :
    normalizedDetCovector v u W x = Matrix.det ![⇑v, ⇑u, ⇑x] / Matrix.det ![⇑v, ⇑u, ⇑W] := by
  change (Matrix.det ![⇑v, ⇑u, ⇑W])⁻¹ * ((⇑v ⨯₃ ⇑u) ⬝ᵥ ⇑x) = _
  rw [dotProduct_comm (⇑v ⨯₃ ⇑u) (⇑x),
    triple_product_permutation (⇑x) (⇑v) (⇑u), triple_product_eq_det, div_eq_inv_mul]

/-- Normalization and both vanishing conditions for the same determinant covector. -/
theorem normalizedDetCovector_normalization (v u W : ℝ^3) (hne : Matrix.det ![⇑v, ⇑u, ⇑W] ≠ 0) :
    normalizedDetCovector v u W v = 0 ∧
    normalizedDetCovector v u W u = 0 ∧ normalizedDetCovector v u W W = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [normalizedDetCovector_apply, Matrix.det_zero_of_row_eq (M := ![⇑v, ⇑u, ⇑v])
        (show (0 : Fin 3) ≠ 2 by decide) rfl, zero_div]
  · rw [normalizedDetCovector_apply, Matrix.det_zero_of_row_eq (M := ![⇑v, ⇑u, ⇑u])
        (show (1 : Fin 3) ≠ 2 by decide) rfl, zero_div]
  · rw [normalizedDetCovector_apply, div_self hne]

/-- The two-column map in the fixed Euclidean coordinates of `ℝ^2`.
Its matrix is `!![p 0, q 0; p 1, q 1]`. -/
def projectedPair (p q : ℝ^2) : (ℝ^2) →L[ℝ] (ℝ^2) :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight p + (EuclideanSpace.proj (1 : Fin 2)).smulRight q

@[simp] theorem projectedPair_apply (p q c : ℝ^2) :
    projectedPair p q c = c 0 • p + c 1 • q := rfl

/-- Only the omitted coordinate of the tangent is needed to invert the projected
pair. The finite-dimensional equivalence here witnesses invertibility; the
construction below uses Mathlib's single inverse function, not this witness. -/
theorem isInvertible_projectedPair (r : Module.Basis (Fin 3) ℝ (ℝ^3)) (v : ℝ^3)
    (π : (ℝ^3) →L[ℝ] (ℝ^2))
    (hker : LinearMap.ker π.toLinearMap = Submodule.span ℝ ({v} : Set (ℝ^3))) (i j k : Fin 3)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hcoeff : r.repr v k ≠ 0) :
    (projectedPair (π (r i)) (π (r j))).IsInvertible := by
  let M := projectedPair (π (r i)) (π (r j))
  have hzero : LinearMap.ker M.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    change M c = 0 at hc
    have hm : c 0 • r i + c 1 • r j ∈ LinearMap.ker π.toLinearMap := by
      change π (c 0 • r i + c 1 • r j) = 0
      simpa only [M, projectedPair_apply, map_add, map_smul] using hc
    rw [hker] at hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    have hak : a * r.repr v k = 0 := by
      have heq := congrArg (fun x : ℝ^3 ↦ r.repr x k) ha
      simpa [map_add, map_smul, r.repr_self_apply, hki.symm, hkj.symm] using heq
    have ha0 : a = 0 := (mul_eq_zero.mp hak).resolve_right hcoeff
    have hc0 : c 0 = 0 := by
      have heq := congrArg (fun x : ℝ^3 ↦ r.repr x i) ha
      simpa [ha0, map_add, map_smul, r.repr_self_apply, hij.symm] using heq.symm
    have hc1 : c 1 = 0 := by
      have heq := congrArg (fun x : ℝ^3 ↦ r.repr x j) ha
      simpa [ha0, map_add, map_smul, r.repr_self_apply, hij] using heq.symm
    apply PiLp.ext
    intro m
    fin_cases m
    · exact hc0
    · exact hc1
  have hinj : Function.Injective M := LinearMap.ker_eq_bot.mp hzero
  refine ⟨(LinearEquiv.ofInjectiveEndo M.toLinearMap hinj).toContinuousLinearEquiv, ?_⟩
  ext c
  rfl

/-- The explicit sum of two symmetric terms. The coefficient vector is the
unique solution of the displayed two-column system wherever that system is
invertible. The definition itself is total. -/
def bilinearCorrection (v u₁ u₂ W : ℝ^3)
    (π : (ℝ^3) →L[ℝ] (ℝ^2)) (η : ℝ^2) :
    (ℝ^3) →L[ℝ] (ℝ^3) →L[ℝ] (ℝ^3) :=
  let a₁ := normalizedDetCovector v u₁ W
  let a₂ := normalizedDetCovector v u₂ W
  let c := (projectedPair (π u₁) (π u₂)).inverse η
  c 0 • a₁.smulRight (a₁.smulRight u₁) + c 1 • a₂.smulRight (a₂.smulRight u₂)

theorem bilinearCorrection_apply (v u₁ u₂ W : ℝ^3) (π : (ℝ^3) →L[ℝ] (ℝ^2)) (η : ℝ^2) (x y : ℝ^3) :
    bilinearCorrection v u₁ u₂ W π η x y =
      let c := (projectedPair (π u₁) (π u₂)).inverse η
      (c 0 * (normalizedDetCovector v u₁ W x * normalizedDetCovector v u₁ W y)) • u₁ +
      (c 1 * (normalizedDetCovector v u₂ W x * normalizedDetCovector v u₂ W y)) • u₂ := by
  simp only [bilinearCorrection, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_smul, mul_assoc]

/-- Pointwise specification of the same formula used for the smooth family.
The diagonal is measured by the dual basis `r.repr`, not by inner products. -/
theorem bilinearCorrection_spec (r : Module.Basis (Fin 3) ℝ (ℝ^3)) (v W : ℝ^3)
    (π : (ℝ^3) →L[ℝ] (ℝ^2)) (η : ℝ^2) (i j : Fin 3) (hij : i ≠ j)
    (hi : Matrix.det ![⇑v, ⇑(r i), ⇑W] ≠ 0) (hj : Matrix.det ![⇑v, ⇑(r j), ⇑W] ≠ 0)
    (hM : (projectedPair (π (r i)) (π (r j))).IsInvertible) :
    let B := bilinearCorrection v (r i) (r j) W π η; (∀ x y, B x y = B y x) ∧ (∀ y, B v y = 0) ∧
      (∀ m, r.repr (B (r m) (r m)) m = 0) ∧ π (B W W) = η := by
  let a₁ := normalizedDetCovector v (r i) W
  let a₂ := normalizedDetCovector v (r j) W
  let c := (projectedPair (π (r i)) (π (r j))).inverse η
  obtain ⟨ha₁v, ha₁i, ha₁W⟩ := normalizedDetCovector_normalization v (r i) W hi
  obtain ⟨ha₂v, ha₂j, ha₂W⟩ := normalizedDetCovector_normalization v (r j) W hj
  change a₁ v = 0 at ha₁v
  change a₁ (r i) = 0 at ha₁i
  change a₁ W = 1 at ha₁W
  change a₂ v = 0 at ha₂v
  change a₂ (r j) = 0 at ha₂j
  change a₂ W = 1 at ha₂W
  have hsolve : c 0 • π (r i) + c 1 • π (r j) = η := hM.self_apply_inverse η
  have hB (x y : ℝ^3) : bilinearCorrection v (r i) (r j) W π η x y =
      (c 0 * (a₁ x * a₁ y)) • r i + (c 1 * (a₂ x * a₂ y)) • r j :=
    bilinearCorrection_apply v (r i) (r j) W π η x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    rw [hB, hB, mul_comm (a₁ x) (a₁ y), mul_comm (a₂ x) (a₂ y)]
  · intro y
    simp [hB, ha₁v, ha₂v]
  · intro m
    by_cases hmi : m = i
    · subst m
      simp [hB, map_smul, ha₁i, hij.symm]
    · by_cases hmj : m = j
      · subst m
        simp [hB, map_smul, ha₂j, hij]
      · simp [hB, map_add, map_smul, Ne.symm hmi, Ne.symm hmj]
  · simpa only [hB, ha₁W, ha₂W, mul_one, map_add, map_smul] using hsolve

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {s : Set P} {n : WithTop ℕ∞}

/-- Local smoothness of the explicit determinant covector, including its
continuous-linear-map norm topology. No denominator condition outside `s`. -/
theorem contDiffOn_normalizedDetCovector {v u W : P → ℝ^3} (hv : ContDiffOn ℝ n v s)
    (hu : ContDiffOn ℝ n u s) (hW : ContDiffOn ℝ n W s)
    (hne : ∀ t ∈ s, Matrix.det ![⇑(v t), ⇑(u t), ⇑(W t)] ≠ 0) :
    ContDiffOn ℝ n (fun t ↦ normalizedDetCovector (v t) (u t) (W t)) s := by
  have hdet (w : P → ℝ^3) (hw : ContDiffOn ℝ n w s) :
      ContDiffOn ℝ n (fun t ↦ Matrix.det ![⇑(v t), ⇑(u t), ⇑(w t)]) s := by
    have hrows : ContDiffOn ℝ n
        (fun t ↦ (![⇑(v t), ⇑(u t), ⇑(w t)] : Matrix (Fin 3) (Fin 3) ℝ)) s := by
      apply contDiffOn_pi.mpr
      intro row
      apply contDiffOn_pi.mpr
      intro col
      fin_cases row
      · exact (EuclideanSpace.proj col : ℝ^3 →L[ℝ] ℝ).contDiff.comp_contDiffOn hv
      · exact (EuclideanSpace.proj col : ℝ^3 →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
      · exact (EuclideanSpace.proj col : ℝ^3 →L[ℝ] ℝ).contDiff.comp_contDiffOn hw
    exact PDE.Analysis.Matrix.contDiff_det.comp_contDiffOn hrows
  apply contDiffOn_clm_apply.mpr
  intro x
  simp only [normalizedDetCovector_apply]
  convert! (hdet (fun _ ↦ x) contDiffOn_const).div (hdet W hW) hne using 1

/-- Smoothness of the explicit formula. Inversion is applied to one
explicit map into endomorphisms of `ℝ^2`, at its invertible values. -/
theorem contDiffOn_bilinearCorrection {v u₁ u₂ W : P → ℝ^3} {π : P → (ℝ^3) →L[ℝ] (ℝ^2)}
    {η : P → ℝ^2} (hv : ContDiffOn ℝ n v s) (h₁ : ContDiffOn ℝ n u₁ s) (h₂ : ContDiffOn ℝ n u₂ s)
    (hW : ContDiffOn ℝ n W s) (hπ : ContDiffOn ℝ n π s) (hη : ContDiffOn ℝ n η s)
    (hi : ∀ t ∈ s, Matrix.det ![⇑(v t), ⇑(u₁ t), ⇑(W t)] ≠ 0)
    (hj : ∀ t ∈ s, Matrix.det ![⇑(v t), ⇑(u₂ t), ⇑(W t)] ≠ 0)
    (hInv : ∀ t ∈ s, (projectedPair (π t (u₁ t)) (π t (u₂ t))).IsInvertible) :
    ContDiffOn ℝ n (fun t ↦ bilinearCorrection (v t) (u₁ t) (u₂ t) (W t) (π t) (η t)) s := by
  have ha₁ := contDiffOn_normalizedDetCovector hv h₁ hW hi
  have ha₂ := contDiffOn_normalizedDetCovector hv h₂ hW hj
  have hM : ContDiffOn ℝ n (fun t ↦ projectedPair (π t (u₁ t)) (π t (u₂ t))) s := by
    unfold projectedPair
    exact (contDiffOn_const.smulRight (hπ.clm_apply h₁)).add
      (contDiffOn_const.smulRight (hπ.clm_apply h₂))
  have hinverse : ContDiffOn ℝ n (fun t ↦ (projectedPair (π t (u₁ t)) (π t (u₂ t))).inverse) s := by
    intro t ht
    exact (hInv t ht).contDiffAt_map_inverse.comp_contDiffWithinAt t (hM t ht)
  have hc := hinverse.clm_apply hη
  have hc₀ := (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.comp_contDiffOn hc
  have hc₁ := (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.comp_contDiffOn hc
  unfold bilinearCorrection
  exact (hc₀.smul (ha₁.smulRight (ha₁.smulRight h₁))).add
    (hc₁.smul (ha₂.smulRight (ha₂.smulRight h₂)))

/-- A smooth family for the same supplied frame, tangent, transverse vector and
projection. On an open parameter arc take `P = ℝ` and `n = (⊤ : ℕ∞)`.

The invertibility needed for the projected solve is derived from the kernel and
one omitted tangent coefficient. Neither smoothness of a selected correction
nor any target projected identity is a hypothesis. Only the two used frame
vectors require smoothness; the dual-basis identities hold for every frame
vector at every point of `s`. -/
theorem contDiffOn_bilinearCorrection_of_ker (r : P → Module.Basis (Fin 3) ℝ (ℝ^3)) (v W : P → ℝ^3)
    (π : P → (ℝ^3) →L[ℝ] (ℝ^2)) (η : P → ℝ^2) (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (hiSmooth : ContDiffOn ℝ n (fun t ↦ r t i) s)
    (hjSmooth : ContDiffOn ℝ n (fun t ↦ r t j) s) (hv : ContDiffOn ℝ n v s)
    (hW : ContDiffOn ℝ n W s) (hπ : ContDiffOn ℝ n π s) (hη : ContDiffOn ℝ n η s)
    (hker : ∀ t ∈ s, LinearMap.ker (π t).toLinearMap = Submodule.span ℝ ({v t} : Set (ℝ^3)))
    (hcoeff : ∀ t ∈ s, (r t).repr (v t) k ≠ 0)
    (hi : ∀ t ∈ s, Matrix.det ![⇑(v t), ⇑(r t i), ⇑(W t)] ≠ 0)
    (hj : ∀ t ∈ s, Matrix.det ![⇑(v t), ⇑(r t j), ⇑(W t)] ≠ 0) :
    let B := fun t ↦ bilinearCorrection (v t) (r t i) (r t j) (W t) (π t) (η t)
    ContDiffOn ℝ n B s ∧
    ∀ t ∈ s,
      (∀ x y, B t x y = B t y x) ∧
      (∀ y, B t (v t) y = 0) ∧
      (∀ m, (r t).repr (B t (r t m) (r t m)) m = 0) ∧
      π t (B t (W t) (W t)) = η t := by
  have hInv (t : P) (ht : t ∈ s) : (projectedPair (π t (r t i)) (π t (r t j))).IsInvertible :=
    isInvertible_projectedPair (r t) (v t) (π t) (hker t ht) i j k hij hki hkj (hcoeff t ht)
  refine ⟨contDiffOn_bilinearCorrection hv hiSmooth hjSmooth hW hπ hη hi hj hInv, ?_⟩
  intro t ht
  exact bilinearCorrection_spec (r t) (v t) (W t) (π t) (η t) i j hij
    (hi t ht) (hj t ht) (hInv t ht)

end PDE.Analysis.GNNeutralHessian
