/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram

/-!
# Residual-corrected finite-rank solves

Let `L₀ + K` be a weak-form operator on an energy space. An interpolation has the
factorization `Ψ ∘ S`, where `S` extracts finitely many coordinates and `Ψ` reconstructs
a trial function. Approximate solves for these trial functions give another reconstruction
`Φ`. Their residual is `(L₀ + K) ∘ Φ + K ∘ Ψ`.

Instead of discarding that residual, we add it to the unresolved part of the operator.
The resulting operator is exactly `(L₀ + K) ∘ (id + Φ ∘ S)`. Small interpolation and
solve residuals preserve the coercivity of `L₀`; Lax–Milgram then supplies a solution
of the original equation after reconstruction by `id + Φ ∘ S`. With `A = L₀ + K`,

```text
corrected L₀ K S Ψ Φ = L₀ + K ∘ (id - Ψ ∘ S) + (A ∘ Φ + K ∘ Ψ) ∘ S = A ∘ (id + Φ ∘ S)
```

(`corrected_eq_comp`), and if `L₀` is coercive with constant `c`, a bound `δ` of the tail
`K ∘ (id - Ψ ∘ S)` and a bound `ε` of the residual leave the constant `c - δ - ε`
(`corrected_pairing_ge`).

All constants and reconstruction maps are parameters. In applications `F` is a finite
coordinate space, but the identities and estimates need no dimension assumption. The
operators take values in the strong dual of the energy space, so an elliptic differential
operator need not be bounded on `L²`.

A nearly exact right inverse of a bounded coordinate map can also be corrected
by a Neumann inverse on the coordinate space: if `‖id - Q ∘ Φ‖ < 1`, then
`exactRightInverse Q Φ = Φ ∘ (Q ∘ Φ)⁻¹` is an exact right inverse of `Q`
(`comp_exactRightInverse`). Only the coordinate space must be complete; the
reconstruction and its image under a bounded spatial operator retain explicit norm bounds.
This correction does not require a dimension assumption.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Sections 3.1.2 and 3.2.1,
  (3.4)-(3.6) and (3.11)-(3.13). <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

namespace ContinuousLinearMap

section ExactRightInverse

variable {𝕜 E F H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Correct a proposed right inverse on its coefficient space. Under the residual bound
in `comp_exactRightInverse`, this has exactly the prescribed coordinates. The total ring
inverse is zero when the coefficient operator is not invertible. -/
def exactRightInverse (Q : E →L[𝕜] F) (Φ : F →L[𝕜] E) : F →L[𝕜] E :=
  Φ.comp (Ring.inverse (Q.comp Φ))

private theorem inverse_bounds_of_norm_sub_le (A : F →L[𝕜] F) {δ : ℝ}
    (hres : ‖ContinuousLinearMap.id 𝕜 F - A‖ ≤ δ) (hδ : δ < 1) :
    IsUnit A ∧ ‖Ring.inverse A‖ ≤ 1 / (1 - δ) := by
  have hlt : ‖(1 : F →L[𝕜] F) - A‖ < 1 := hres.trans_lt hδ
  have hunit : IsUnit A := by
    simpa using isUnit_one_sub_of_norm_lt_one hlt
  refine ⟨hunit, ?_⟩
  have hseries := tsum_geometric_le_of_norm_lt_one ((1 : F →L[𝕜] F) - A) hlt
  rw [geom_series_eq_inverse _ hlt, sub_sub_cancel] at hseries
  calc
    ‖Ring.inverse A‖ ≤ ‖(1 : F →L[𝕜] F)‖ - 1 + (1 - ‖(1 : F →L[𝕜] F) - A‖)⁻¹ :=
      hseries
    _ ≤ (1 - ‖(1 : F →L[𝕜] F) - A‖)⁻¹ := by
      have hnorm : ‖(1 : F →L[𝕜] F)‖ ≤ 1 := norm_id_le
      linarith
    _ ≤ 1 / (1 - δ) := by
      rw [one_div]
      exact (inv_le_inv₀ (sub_pos.mpr hlt) (sub_pos.mpr hδ)).2 (sub_le_sub_left hres 1)

/-- A coordinate residual below one gives an exact right inverse. This uses completeness
only of the coordinate space, and also covers the zero-dimensional case. -/
theorem comp_exactRightInverse (Q : E →L[𝕜] F) (Φ : F →L[𝕜] E) {δ : ℝ}
    (hres : ‖ContinuousLinearMap.id 𝕜 F - Q.comp Φ‖ ≤ δ) (hδ : δ < 1) :
    Q.comp (exactRightInverse Q Φ) = ContinuousLinearMap.id 𝕜 F := by
  have hunit := (inverse_bounds_of_norm_sub_le (Q.comp Φ) hres hδ).1
  simpa only [exactRightInverse, ← comp_assoc, ← mul_def, one_def] using
    Ring.mul_inverse_cancel (Q.comp Φ) hunit

/-- The exact reconstruction costs at most the proposal norm divided by the residual margin. -/
theorem norm_exactRightInverse_le (Q : E →L[𝕜] F) (Φ : F →L[𝕜] E) {δ : ℝ}
    (hres : ‖ContinuousLinearMap.id 𝕜 F - Q.comp Φ‖ ≤ δ) (hδ : δ < 1) :
    ‖exactRightInverse Q Φ‖ ≤ ‖Φ‖ / (1 - δ) := by
  calc
    ‖exactRightInverse Q Φ‖ ≤ ‖Φ‖ * ‖Ring.inverse (Q.comp Φ)‖ := opNorm_comp_le _ _
    _ ≤ ‖Φ‖ * (1 / (1 - δ)) :=
      mul_le_mul_of_nonneg_left (inverse_bounds_of_norm_sub_le _ hres hδ).2 (norm_nonneg Φ)
    _ = ‖Φ‖ / (1 - δ) := by rw [mul_one_div]

/-- The correction of the proposed reconstruction is proportional to its coordinate residual. -/
theorem norm_exactRightInverse_sub_le (Q : E →L[𝕜] F) (Φ : F →L[𝕜] E) {δ : ℝ}
    (hres : ‖ContinuousLinearMap.id 𝕜 F - Q.comp Φ‖ ≤ δ) (hδ : δ < 1) :
    ‖exactRightInverse Q Φ - Φ‖ ≤ ‖Φ‖ * δ / (1 - δ) := by
  obtain ⟨hunit, hnorm⟩ := inverse_bounds_of_norm_sub_le (Q.comp Φ) hres hδ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hres
  have hinv : Ring.inverse (Q.comp Φ) - 1 =
      Ring.inverse (Q.comp Φ) * (1 - Q.comp Φ) := by
    rw [mul_sub, mul_one, Ring.inverse_mul_cancel _ hunit]
  have hdiff : exactRightInverse Q Φ - Φ =
      Φ.comp (Ring.inverse (Q.comp Φ) - ContinuousLinearMap.id 𝕜 F) := by
    simp [exactRightInverse]
  rw [hdiff]
  calc
    ‖Φ.comp (Ring.inverse (Q.comp Φ) - ContinuousLinearMap.id 𝕜 F)‖ ≤
        ‖Φ‖ * ‖Ring.inverse (Q.comp Φ) - ContinuousLinearMap.id 𝕜 F‖ := opNorm_comp_le _ _
    _ ≤ ‖Φ‖ * (‖Ring.inverse (Q.comp Φ)‖ * ‖ContinuousLinearMap.id 𝕜 F - Q.comp Φ‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg Φ)
      change ‖Ring.inverse (Q.comp Φ) - 1‖ ≤ _
      rw [hinv]
      exact norm_mul_le _ _
    _ ≤ ‖Φ‖ * ((1 / (1 - δ)) * δ) := by
      gcongr
    _ = ‖Φ‖ * δ / (1 - δ) := by ring

/-- A bound on the spatial image of the proposal survives exact coordinate correction.
Bounding `L ∘ Φ` directly can be sharper than multiplying the separate operator norms. -/
theorem norm_comp_exactRightInverse_le (L : E →L[𝕜] H) (Q : E →L[𝕜] F)
    (Φ : F →L[𝕜] E) {δ : ℝ}
    (hres : ‖ContinuousLinearMap.id 𝕜 F - Q.comp Φ‖ ≤ δ) (hδ : δ < 1) :
    ‖L.comp (exactRightInverse Q Φ)‖ ≤ ‖L.comp Φ‖ / (1 - δ) := by
  rw [exactRightInverse, ← comp_assoc]
  calc
    ‖(L.comp Φ).comp (Ring.inverse (Q.comp Φ))‖ ≤
        ‖L.comp Φ‖ * ‖Ring.inverse (Q.comp Φ)‖ := opNorm_comp_le _ _
    _ ≤ ‖L.comp Φ‖ * (1 / (1 - δ)) :=
      mul_le_mul_of_nonneg_left (inverse_bounds_of_norm_sub_le _ hres hδ).2 (norm_nonneg _)
    _ = ‖L.comp Φ‖ / (1 - δ) := by rw [mul_one_div]

end ExactRightInverse

end ContinuousLinearMap

namespace PDE.Analysis.Operator.FiniteRankCorrection

section Normed

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The residual of the approximate basis solves, evaluated at the extracted coordinates. -/
def residual (L K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) : V →L[ℝ] StrongDual ℝ V :=
  (L.comp Φ + K.comp Ψ).comp S

/-- The principal form plus the interpolation tail and the complete basis-solve residual. -/
def corrected (L₀ K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) : V →L[ℝ] StrongDual ℝ V :=
  L₀ + K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S) + residual (L₀ + K) K S Ψ Φ

/-- Keeping the basis-solve residual makes reconstruction an exact operator identity. -/
theorem corrected_eq_comp (L₀ K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) :
    corrected L₀ K S Ψ Φ = (L₀ + K).comp (ContinuousLinearMap.id ℝ V + Φ.comp S) := by
  ext u v
  simp [corrected, residual]
  ring

/-- The energy amplification of the reconstruction is bounded by its finite-rank part. -/
theorem reconstruction_norm_le (S : V →L[ℝ] F) (Φ : F →L[ℝ] V) :
    ‖ContinuousLinearMap.id ℝ V + Φ.comp S‖ ≤ 1 + ‖Φ.comp S‖ := by
  exact (norm_add_le (ContinuousLinearMap.id ℝ V) (Φ.comp S)).trans
    (add_le_add (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := V)) (le_refl _))

/-- Coordinate extraction controlled in the weaker norm also controls reconstruction
there. This avoids requiring a small reconstruction or an energy-norm contraction. -/
theorem reconstruction_weak_norm_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V →L[ℝ] W) (S : V →L[ℝ] F) (Φ : F →L[ℝ] V) {s : NNReal}
    (hS : ∀ u, ‖S u‖ ≤ s * ‖e u‖) (u : V) :
    ‖e (u + Φ (S u))‖ ≤ (1 + ‖e.comp Φ‖ * s) * ‖e u‖ := by
  calc
    ‖e (u + Φ (S u))‖ ≤ ‖e u‖ + ‖e (Φ (S u))‖ := by
      rw [map_add]
      exact norm_add_le _ _
    _ ≤ ‖e u‖ + ‖e.comp Φ‖ * ‖S u‖ :=
      add_le_add (le_refl _) ((e.comp Φ).le_opNorm (S u))
    _ ≤ ‖e u‖ + ‖e.comp Φ‖ * (s * ‖e u‖) := by
      gcongr
      exact hS u
    _ = (1 + ‖e.comp Φ‖ * s) * ‖e u‖ := by ring

/-- A bound on the basis residual lifts to the entire energy space through `S`. -/
theorem residual_norm_le (L K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) {ε : ℝ} (hres : ‖L.comp Φ + K.comp Ψ‖ ≤ ε) :
    ‖residual L K S Ψ Φ‖ ≤ ε * ‖S‖ := by
  calc
    ‖residual L K S Ψ Φ‖ ≤ ‖L.comp Φ + K.comp Ψ‖ * ‖S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ε * ‖S‖ := mul_le_mul_of_nonneg_right hres (norm_nonneg S)

/-- The interpolation tail and basis residual pay separately for the perturbation of `L₀`. -/
theorem corrected_sub_norm_le (L₀ K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) {δ ε : ℝ}
    (htail : ‖K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S)‖ ≤ δ)
    (hres : ‖residual (L₀ + K) K S Ψ Φ‖ ≤ ε) :
    ‖corrected L₀ K S Ψ Φ - L₀‖ ≤ δ + ε := by
  have hsub : corrected L₀ K S Ψ Φ - L₀ =
      K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S) + residual (L₀ + K) K S Ψ Φ := by
    ext u v
    simp [corrected]
    ring
  rw [hsub]
  calc
    ‖K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S) + residual (L₀ + K) K S Ψ Φ‖ ≤
        ‖K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S)‖ +
          ‖residual (L₀ + K) K S Ψ Φ‖ :=
      norm_add_le (K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S))
        (residual (L₀ + K) K S Ψ Φ)
    _ ≤ δ + ε := add_le_add htail hres

/-- Certified operator errors lower the coercivity modulus by their sum. -/
theorem corrected_pairing_ge (L₀ K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) {c δ ε : ℝ}
    (hbase : ∀ u, c * ‖u‖ * ‖u‖ ≤ L₀ u u)
    (htail : ‖K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S)‖ ≤ δ)
    (hres : ‖residual (L₀ + K) K S Ψ Φ‖ ≤ ε) (u : V) :
    (c - (δ + ε)) * ‖u‖ * ‖u‖ ≤ corrected L₀ K S Ψ Φ u u := by
  let D := corrected L₀ K S Ψ Φ - L₀
  have hnorm : ‖D‖ ≤ δ + ε := corrected_sub_norm_le L₀ K S Ψ Φ htail hres
  have herr : ‖D u u‖ ≤ (δ + ε) * ‖u‖ * ‖u‖ := by
    calc
      ‖D u u‖ ≤ ‖D u‖ * ‖u‖ := (D u).le_opNorm u
      _ ≤ (‖D‖ * ‖u‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (D.le_opNorm u) (norm_nonneg u)
      _ ≤ ((δ + ε) * ‖u‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg u)) (norm_nonneg u)
  have hlower := neg_abs_le (D u u)
  rw [← Real.norm_eq_abs] at hlower
  have hbaseu := hbase u
  change ‖corrected L₀ K S Ψ Φ u u - L₀ u u‖ ≤ _ at herr
  change -‖corrected L₀ K S Ψ Φ u u - L₀ u u‖ ≤
    corrected L₀ K S Ψ Φ u u - L₀ u u at hlower
  nlinarith

/-- A strict error margin certifies the corrected form for Lax–Milgram. -/
theorem corrected_isCoercive (L₀ K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) {c δ ε : ℝ}
    (hbase : ∀ u, c * ‖u‖ * ‖u‖ ≤ L₀ u u)
    (htail : ‖K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S)‖ ≤ δ)
    (hres : ‖residual (L₀ + K) K S Ψ Φ‖ ≤ ε) (hmargin : δ + ε < c) :
    IsCoercive (corrected L₀ K S Ψ Φ) :=
  ⟨c - (δ + ε), sub_pos.mpr hmargin,
    corrected_pairing_ge L₀ K S Ψ Φ hbase htail hres⟩

end Normed

section Hilbert

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Solving the corrected coercive form gives an exact solution of the original weak equation.
The error bound includes the size of the finite-rank reconstruction. -/
theorem exists_weak_solution_norm_le (L₀ K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F)
    (Ψ Φ : F →L[ℝ] V) {c δ ε : ℝ}
    (hbase : ∀ u, c * ‖u‖ * ‖u‖ ≤ L₀ u u)
    (htail : ‖K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S)‖ ≤ δ)
    (hres : ‖residual (L₀ + K) K S Ψ Φ‖ ≤ ε) (hmargin : δ + ε < c)
    (ell : StrongDual ℝ V) :
    ∃ u, PDE.Analysis.Variational.IsWeakSolution (L₀ + K) ell u ∧
      ‖u‖ ≤ (1 + ‖Φ.comp S‖) * (‖ell‖ / (c - (δ + ε))) := by
  let B := corrected L₀ K S Ψ Φ
  have hB : IsCoercive B := corrected_isCoercive L₀ K S Ψ Φ hbase htail hres hmargin
  let x := PDE.Analysis.Variational.solve B hB ell
  have hx : ‖x‖ ≤ ‖ell‖ / (c - (δ + ε)) :=
    PDE.Analysis.Variational.solve.norm_le_div B hB _ (sub_pos.mpr hmargin)
      (corrected_pairing_ge L₀ K S Ψ Φ hbase htail hres) ell
  refine ⟨x + Φ (S x), ?_, ?_⟩
  · intro v
    have h := PDE.Analysis.Variational.solve.isWeakSolution B hB ell v
    change corrected L₀ K S Ψ Φ x v = ell v at h
    rw [corrected_eq_comp] at h
    exact h
  · calc
      ‖x + Φ (S x)‖ ≤ ‖x‖ + ‖Φ (S x)‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ‖Φ.comp S‖ * ‖x‖ := add_le_add (le_refl ‖x‖) ((Φ.comp S).le_opNorm x)
      _ = (1 + ‖Φ.comp S‖) * ‖x‖ := by ring
      _ ≤ (1 + ‖Φ.comp S‖) * (‖ell‖ / (c - (δ + ε))) :=
        mul_le_mul_of_nonneg_left hx (by positivity)

end Hilbert

end PDE.Analysis.Operator.FiniteRankCorrection
