/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite-rank capture of a positive semidefinite form

Let `E` be an energy form, `M` a mass form and `Q` a positive semidefinite symmetric
form on a real vector space. A finite family `ψ` spans a trial space `V_N`, and the
captured modes `ψ̄ⱼ = ∑ₖ Cₖⱼ ψₖ` with approximate eigenvalues `μⱼ` span a subspace
`V_lg ⊆ V_N`. The finite-rank functional `∑ⱼ Q(f, ψ̄ⱼ)² / μⱼ` captures most of `Q(f, f)`:

```text
Q(f, f) - ∑ⱼ Q(f, ψ̄ⱼ)² / μⱼ ≤ (K₅ + K₆ / (1 - ε₄)²) E(f, f) + ε₃ Λ M(f, f).
```

The constants are certified separately.

* `Q(f, f) ≤ Λ M(f, f)`, and `Λ M(f, f) ≤ K₅ E(f, f)` when `f` is `E`-orthogonal to `V_N`.
* `Q(u, u) ≤ K₆ E(u, u)` for `u ∈ V_N` with `Q(u, ψ̄ⱼ) = 0` for every `j`.
* `Q(g, g) - ∑ⱼ Q(g, ψ̄ⱼ)² / μⱼ ≤ ε₃ Q(g, g)` on `V_lg`, the Gram mismatch.
* `E(g, u)² ≤ ε₄² E(g, g) E(u, u)` for `g ∈ V_lg` and `u ∈ V_N` with `Q(u, ψ̄ⱼ) = 0`.

The proof splits `f` into its `E`-projection onto `V_N` and the remainder, splits the
projection along `V_lg` and its `Q`-orthogonal complement in `V_N`, and compares with the
`Q`-orthogonal projection of `f` onto `V_lg`. The angle bound `ε₄` gives the factor
`1 / (1 - ε₄²)`, which is at most `1 / (1 - ε₄)²`. Projections exist for every
finite family and every positive semidefinite symmetric form, so neither independence of
the modes nor definiteness of the forms is needed.

The quasi-orthogonality bound follows from residuals of the generalized eigenproblem
`Q(ψ̄ⱼ, v) = μⱼ E(ψ̄ⱼ, v) + E(rⱼ, v)`, and the Gram mismatch from the `Q`-Gram matrix of
the modes. A stored form that is only nearly positive is used through a positive
semidefinite shift `Q_δ = Q + δ B`. The capture constants are those of `Q_δ`, while the
functional keeps `Q(f, ψ̄ⱼ)`. Either a cross term pays for the change of functional, or a
lower bound `G_Q ≥ (1 - ε₃) Λ` on the `Q`-Gram matrix of the modes removes `δ` entirely.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.2.2, Lemmas 1-3,
  (4.13)-(4.18), and Appendix B. <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Operator

open scoped Matrix

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

section Forms

variable [TopologicalSpace H] {ι κ : Type*}

/-- The matrix `(B(vᵢ, wⱼ))ᵢⱼ` of a form on two finite families. It is Mathlib's
`LinearMap.toMatrix₂Aux` of the underlying bilinear map (`formMatrix_eq_toMatrix₂Aux`). -/
def formMatrix (B : H →L[ℝ] H →L[ℝ] ℝ) (v : ι → H) (w : κ → H) : Matrix ι κ ℝ :=
  Matrix.of fun i j ↦ B (v i) (w j)

@[simp]
theorem formMatrix_apply (B : H →L[ℝ] H →L[ℝ] ℝ) (v : ι → H) (w : κ → H) (i : ι) (j : κ) :
    formMatrix B v w i j = B (v i) (w j) :=
  rfl

theorem formMatrix_eq_toMatrix₂Aux (B : H →L[ℝ] H →L[ℝ] ℝ) (v : ι → H) (w : κ → H) :
    formMatrix B v w = LinearMap.toMatrix₂Aux ℝ v w B.toLinearMap₁₂ :=
  rfl

/-- Expansion of a form on the diagonal at a sum. -/
theorem form_add_add (B : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
  simp only [map_add, add_apply]
  ring

/-- Expansion of a form on the diagonal at a difference. -/
theorem form_sub_sub (B : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) :
    B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
  simp only [map_sub, sub_apply]
  ring

variable [Fintype ι] [Fintype κ]

/-- A form is linear in its first argument across a finite linear combination. -/
theorem form_sum_smul_left (B : H →L[ℝ] H →L[ℝ] ℝ) (v : ι → H) (c : ι → ℝ) (w : H) :
    B (∑ i, c i • v i) w = ∑ i, c i * B (v i) w := by
  simp [map_sum, map_smul]

/-- A form is linear in its second argument across a finite linear combination. -/
theorem form_sum_smul_right (B : H →L[ℝ] H →L[ℝ] ℝ) (w : H) (v : ι → H) (c : ι → ℝ) :
    B w (∑ i, c i • v i) = ∑ i, c i * B w (v i) := by
  simp [map_sum, map_smul]

/-- A form evaluated on two linear combinations is the quadratic expression of its matrix. -/
theorem form_sum_smul_sum_smul (B : H →L[ℝ] H →L[ℝ] ℝ) (v : ι → H) (w : κ → H)
    (c : ι → ℝ) (d : κ → ℝ) :
    B (∑ i, c i • v i) (∑ j, d j • w j) = c ⬝ᵥ formMatrix B v w *ᵥ d := by
  simp only [form_sum_smul_left, form_sum_smul_right, dotProduct, Matrix.mulVec,
    formMatrix_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The Cauchy–Schwarz inequality for a positive semidefinite symmetric form. -/
theorem form_sq_le (B : H →L[ℝ] H →L[ℝ] ℝ) (hsymm : ∀ f g, B f g = B g f)
    (hnonneg : ∀ f, 0 ≤ B f f) (f g : H) : B f g ^ 2 ≤ B f f * B g g :=
  LinearMap.BilinForm.apply_sq_le_of_symm (B := B.toLinearMap₁₂) hnonneg
    ⟨fun x y ↦ by simpa using hsymm x y⟩ f g

/-- A vector orthogonal to a finite family is orthogonal to its span. -/
theorem form_eq_zero_of_mem_span {ι' : Type*} [Finite ι'] (B : H →L[ℝ] H →L[ℝ] ℝ)
    (v : ι' → H) {x : H} (hx : ∀ j, B x (v j) = 0) {y : H}
    (hy : y ∈ Submodule.span ℝ (Set.range v)) : B x y = 0 := by
  have := Fintype.ofFinite ι'
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  simp [hx]

/-- Pythagoras for a projection `p` onto the span of a finite family, orthogonal for a
symmetric form. -/
private theorem form_eq_add_of_orthogonal {ι' : Type*} [Finite ι'] (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hsymm : ∀ f g, B f g = B g f) (v : ι' → H) {f p : H}
    (hp : p ∈ Submodule.span ℝ (Set.range v)) (hfp : ∀ j, B (f - p) (v j) = 0) :
    B f f = B (f - p) (f - p) + B p p := by
  have h0 := form_eq_zero_of_mem_span B v hfp hp
  conv_lhs => rw [← sub_add_cancel f p]
  rw [form_add_add, h0, hsymm p (f - p), h0]
  ring

/-- Vectors with orthogonal difference have the same pairings. -/
private theorem form_apply_eq_of_sub_eq_zero (B : H →L[ℝ] H →L[ℝ] ℝ) {f p w : H}
    (h : B (f - p) w = 0) : B f w = B p w := by
  rwa [map_sub, sub_apply, sub_eq_zero] at h

/-- Every vector has a projection onto the span of a finite family, orthogonal for a
positive semidefinite symmetric form. The family may be dependent and the form degenerate:
the load `B f` vanishes on null vectors by Cauchy–Schwarz, so it lies in the range of the
Gram map by finite-dimensional duality. -/
theorem exists_sub_sum_smul_orthogonal (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hsymm : ∀ f g, B f g = B g f) (hnonneg : ∀ f, 0 ≤ B f f) (v : ι → H) (f : H) :
    ∃ c : ι → ℝ, ∀ j, B (f - ∑ i, c i • v i) (v j) = 0 := by
  classical
  let S : (ι → ℝ) →ₗ[ℝ] H := Fintype.linearCombination ℝ v
  let b : (ι → ℝ) →ₗ[ℝ] Module.Dual ℝ (ι → ℝ) := (B.toLinearMap₁₂).compl₁₂ S S
  let ℓ : Module.Dual ℝ (ι → ℝ) := (B f : H →ₗ[ℝ] ℝ).comp S
  have hℓ : ℓ ∈ LinearMap.range b.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro c hc
    have hcc : B (S c) (S c) = 0 := by
      simpa [b] using LinearMap.congr_fun (LinearMap.mem_ker.mp hc) c
    have hcs := form_sq_le B hsymm hnonneg f (S c)
    rw [hcc, mul_zero] at hcs
    have hzero : B f (S c) = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hcs (sq_nonneg _))
    simpa [ℓ] using hzero
  obtain ⟨φ, hφ⟩ := hℓ
  obtain ⟨c, rfl⟩ := (Module.evalEquiv ℝ (ι → ℝ)).surjective φ
  refine ⟨c, fun j ↦ ?_⟩
  have h : B (v j) (S c) = B f (v j) := by
    simpa [b, ℓ, S, Fintype.linearCombination_apply_single] using
      LinearMap.congr_fun hφ (Pi.single j 1)
  rw [map_sub, sub_apply, ← h, hsymm, Fintype.linearCombination_apply, sub_self]

/-- Cauchy–Schwarz turns energy bounds `E(rⱼ, rⱼ) ≤ ρⱼ²` into a bound on every combination. -/
theorem form_sum_smul_self_le_sq (B : H →L[ℝ] H →L[ℝ] ℝ) (hsymm : ∀ f g, B f g = B g f)
    (hnonneg : ∀ f, 0 ≤ B f f) (r : ι → H) (ρ : ι → ℝ) (hρ0 : ∀ j, 0 ≤ ρ j)
    (hρ : ∀ j, B (r j) (r j) ≤ ρ j ^ 2) (a : ι → ℝ) :
    B (∑ i, a i • r i) (∑ i, a i • r i) ≤ (∑ i, |a i| * ρ i) ^ 2 := by
  have hpair (i j : ι) : a i * a j * B (r i) (r j) ≤ |a i| * ρ i * (|a j| * ρ j) := by
    have habs : |B (r i) (r j)| ≤ ρ i * ρ j :=
      abs_le_of_sq_le_sq ((form_sq_le B hsymm hnonneg _ _).trans ((mul_le_mul (hρ i) (hρ j)
        (hnonneg _) (sq_nonneg _)).trans_eq (mul_pow _ _ _).symm)) (mul_nonneg (hρ0 i) (hρ0 j))
    calc a i * a j * B (r i) (r j) ≤ |a i| * |a j| * |B (r i) (r j)| := by
          rw [← abs_mul, ← abs_mul]; exact le_abs_self _
      _ ≤ |a i| * |a j| * (ρ i * ρ j) := by gcongr
      _ = |a i| * ρ i * (|a j| * ρ j) := by ring
  rw [form_sum_smul_sum_smul, sq, Finset.sum_mul_sum]
  simp only [dotProduct, Matrix.mulVec, formMatrix_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  calc
    a i * (B (r i) (r j) * a j) = a i * a j * B (r i) (r j) := by ring
    _ ≤ _ := hpair i j

end Forms

/-- The captured modes `ψ̄ⱼ = ∑ₖ Cₖⱼ ψₖ`, with coefficient columns `C` in the trial
family `ψ`. -/
def capturedMode {N m : ℕ} (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (j : Fin m) : H :=
  ∑ k, C k j • ψ k

/-- Every captured mode lies in the trial span `V_N`. -/
theorem capturedMode_mem_span {N m : ℕ} (ψ : Fin N → H) (C : Fin N → Fin m → ℝ)
    (j : Fin m) : capturedMode ψ C j ∈ Submodule.span ℝ (Set.range ψ) :=
  Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The captured subspace `V_lg` lies in the trial span `V_N`. -/
theorem span_capturedMode_le {N m : ℕ} (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) :
    Submodule.span ℝ (Set.range (capturedMode ψ C)) ≤ Submodule.span ℝ (Set.range ψ) :=
  Submodule.span_le.mpr <| by
    rintro _ ⟨j, rfl⟩
    exact capturedMode_mem_span ψ C j

section Capture

variable [TopologicalSpace H] {N m : ℕ}

/-- The pairing of a trial combination with a captured mode, as a row of `cᵀ A C` for the
matrix `A` of the form on the trial family. -/
theorem form_sum_smul_capturedMode (B : H →L[ℝ] H →L[ℝ] ℝ) (ψ : Fin N → H)
    (C : Fin N → Fin m → ℝ) (c : Fin N → ℝ) (j : Fin m) :
    B (∑ k, c k • ψ k) (capturedMode ψ C j) = (c ᵥ* (formMatrix B ψ ψ * Matrix.of C)) j := by
  rw [capturedMode, form_sum_smul_sum_smul, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  rfl

/-- **The projection residual.** If `h ∈ V_lg` is a `Q`-orthogonal projection of `f` onto
the captured subspace, then `Q(f - h, f - h) ≤ (K₅ + K₆ / (1 - ε₄²)) E(f, f)`. The factor
`1 / (1 - ε₄²)` comes from `E(g + u, g + u) ≥ (1 - ε₄²) E(u, u)` for `g ∈ V_lg` and `u` in its
`Q`-orthogonal complement in `V_N`. -/
theorem capture_projection_residual_le (Eform Mform Qform : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) {Λ K₅ K₆ ε₄ : ℝ}
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hQnonneg : ∀ f, 0 ≤ Qform f f)
    (hQ : ∀ f, Qform f f ≤ Λ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λ * Mform f f ≤ K₅ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
      Qform u u ≤ K₆ * Eform u u)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄ ^ 2 * Eform g g * Eform u u)
    (hK₅ : 0 ≤ K₅) (hK₆0 : 0 ≤ K₆) (hε₄1 : ε₄ ^ 2 < 1) {f h : H}
    (hh : h ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)))
    (hfh : ∀ j, Qform (f - h) (capturedMode ψ C j) = 0) :
    Qform (f - h) (f - h) ≤ (K₅ + K₆ / (1 - ε₄ ^ 2)) * Eform f f := by
  set ψbar := capturedMode ψ C
  -- The `E`-projection `fN` of `f` onto `V_N` and the remainder `fo`.
  obtain ⟨c, hc⟩ := exists_sub_sum_smul_orthogonal Eform hEsymm hEnonneg ψ f
  set fN := ∑ k, c k • ψ k
  set fo := f - fN with hfo_def
  have hfN : fN ∈ Submodule.span ℝ (Set.range ψ) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, rfl⟩
  have hEf : Eform f f = Eform fo fo + Eform fN fN :=
    form_eq_add_of_orthogonal Eform hEsymm ψ hfN hc
  have hQfo : Qform fo fo ≤ K₅ * Eform fo fo := (hQ fo).trans (htail fo hc)
  -- The `Q`-orthogonal splitting `fN = g + u` along `V_lg`.
  obtain ⟨d, hd⟩ := exists_sub_sum_smul_orthogonal Qform hQsymm hQnonneg ψbar fN
  set g := ∑ j, d j • ψbar j
  set u := fN - g with hu_def
  have hg : g ∈ Submodule.span ℝ (Set.range ψbar) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨d, rfl⟩
  have hu : u ∈ Submodule.span ℝ (Set.range ψ) :=
    Submodule.sub_mem _ hfN (span_capturedMode_le ψ C hg)
  have hpos : 0 < 1 - ε₄ ^ 2 := sub_pos.mpr hε₄1
  have hEu : (1 - ε₄ ^ 2) * Eform u u ≤ Eform fN fN := by
    have hamgm := two_mul_le_add_of_sq_le_mul (r := -Eform g u) (hEnonneg g)
      (mul_nonneg (sq_nonneg ε₄) (hEnonneg u)) (by rw [neg_sq]; linarith [hε₄ g hg u hu hd])
    rw [show fN = g + u by rw [hu_def, add_sub_cancel], form_add_add, hEsymm u g]
    linarith
  have hQu : Qform u u ≤ K₆ / (1 - ε₄ ^ 2) * Eform fN fN := by
    refine (hK₆ u hu hd).trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith [mul_le_mul_of_nonneg_left hEu hK₆0]
  -- `f - h` is the best `Q`-approximation, so it is no larger than `f - g = fo + u`.
  have hfh' : ∀ y ∈ Submodule.span ℝ (Set.range ψbar), Qform (f - h) y = 0 :=
    fun y hy ↦ form_eq_zero_of_mem_span Qform ψbar hfh hy
  have hI₁ : Qform (f - h) (f - h) ≤ Qform (fo + u) (fo + u) := by
    have hdiff : g - h ∈ Submodule.span ℝ (Set.range ψbar) := Submodule.sub_mem _ hg hh
    have hrw : fo + u = (f - h) - (g - h) := by
      rw [hfo_def, hu_def]
      abel
    rw [hrw, form_sub_sub _ (f - h) (g - h), hfh' _ hdiff, hQsymm (g - h) (f - h),
      hfh' _ hdiff]
    linarith [hQnonneg (g - h)]
  have hI₁' : Qform (fo + u) (fo + u) ≤
      (K₅ + K₆ / (1 - ε₄ ^ 2)) * (Eform fo fo + Eform fN fN) := by
    set K' := K₆ / (1 - ε₄ ^ 2)
    have hK'0 : 0 ≤ K' := div_nonneg hK₆0 hpos.le
    have hsplit : Qform (fo + u) (fo + u) = Qform fo fo + 2 * Qform fo u + Qform u u := by
      rw [form_add_add, hQsymm u fo]
      ring
    have hcross : 2 * Qform fo u ≤ K' * Eform fo fo + K₅ * Eform fN fN :=
      two_mul_le_add_of_sq_le_mul (mul_nonneg hK'0 (hEnonneg _)) (mul_nonneg hK₅ (hEnonneg _))
        (((form_sq_le Qform hQsymm hQnonneg fo u).trans
          (mul_le_mul hQfo hQu (hQnonneg u) (mul_nonneg hK₅ (hEnonneg _)))).trans_eq (by ring))
    rw [hsplit]
    linarith [hQfo, hQu, hcross]
  rw [hEf]
  exact hI₁.trans hI₁'

/-- **Finite-rank capture**, with the sharp angle factor `K₆ / (1 - ε₄²)`. -/
theorem finiteRank_capture_le_energy (Eform Mform Qform : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ) {Λ K₅ K₆ ε₃ ε₄ : ℝ}
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hQnonneg : ∀ f, 0 ≤ Qform f f)
    (hQ : ∀ f, Qform f f ≤ Λ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λ * Mform f f ≤ K₅ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
      Qform u u ≤ K₆ * Eform u u)
    (hε₃ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      Qform g g - ∑ j, Qform g (capturedMode ψ C j) ^ 2 / μ j ≤ ε₃ * Qform g g)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄ ^ 2 * Eform g g * Eform u u)
    (hK₅ : 0 ≤ K₅) (hK₆0 : 0 ≤ K₆) (hε₃0 : 0 ≤ ε₃) (hε₄1 : ε₄ ^ 2 < 1) (f : H) :
    Qform f f - ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j ≤
      (K₅ + K₆ / (1 - ε₄ ^ 2)) * Eform f f + ε₃ * Λ * Mform f f := by
  set ψbar := capturedMode ψ C
  -- The `Q`-orthogonal projection `h` of `f` onto `V_lg`.
  obtain ⟨e, he⟩ := exists_sub_sum_smul_orthogonal Qform hQsymm hQnonneg ψbar f
  set h := ∑ j, e j • ψbar j
  have hh : h ∈ Submodule.span ℝ (Set.range ψbar) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨e, rfl⟩
  have hI₁ := capture_projection_residual_le Eform Mform Qform ψ C hEsymm hEnonneg hQsymm
    hQnonneg hQ htail hK₆ hε₄ hK₅ hK₆0 hε₄1 hh he
  have hQf := form_eq_add_of_orthogonal Qform hQsymm ψbar hh he
  -- The Gram mismatch on `V_lg`.
  have hI₂ := hε₃ h hh
  have hQh : ε₃ * Qform h h ≤ ε₃ * (Λ * Mform f f) :=
    mul_le_mul_of_nonneg_left (by linarith [hQnonneg (f - h), hQ f]) hε₃0
  rw [Finset.sum_congr rfl fun j _ ↦ by rw [form_apply_eq_of_sub_eq_zero Qform (he j)]]
  linarith

/-- **Finite-rank capture** (Hou–Wang–Yang, Lemma 3 and Appendix B). For a positive
semidefinite symmetric form `Q` with `Q ≤ Λ M`, the captured functional
`∑ⱼ Q(f, ψ̄ⱼ)² / μⱼ` leaves at most `M₁ ‖∇f‖² + (η₂ M₁ + ε₃ Λ) ‖f‖²` with
`M₁ = K₅ + K₆ / (1 - ε₄)²`, where `E = ‖∇·‖² + η₂ ‖·‖²` on the diagonal. Only the upper
bound is needed for the coercivity estimate, and it needs `Q ≥ 0`, through the
Cauchy–Schwarz inequality in the `Q`-seminorm. -/
theorem finiteRank_capture_le (Eform Mform Qform gradientForm : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ) {η₂ Λ K₅ K₆ ε₃ ε₄ : ℝ}
    (hE : ∀ f, Eform f f = gradientForm f f + η₂ * Mform f f)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hQnonneg : ∀ f, 0 ≤ Qform f f)
    (hQ : ∀ f, Qform f f ≤ Λ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λ * Mform f f ≤ K₅ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
      Qform u u ≤ K₆ * Eform u u)
    (hε₃ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      Qform g g - ∑ j, Qform g (capturedMode ψ C j) ^ 2 / μ j ≤ ε₃ * Qform g g)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄ ^ 2 * Eform g g * Eform u u)
    (hK₅ : 0 ≤ K₅) (hK₆0 : 0 ≤ K₆) (hε₃0 : 0 ≤ ε₃) (hε₄0 : 0 ≤ ε₄) (hε₄1 : ε₄ < 1) :
    ∀ f, Qform f f - ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j ≤
      (K₅ + K₆ / (1 - ε₄) ^ 2) * gradientForm f f +
        (η₂ * (K₅ + K₆ / (1 - ε₄) ^ 2) + ε₃ * Λ) * Mform f f := by
  intro f
  have hsharp := finiteRank_capture_le_energy Eform Mform Qform ψ C μ hEsymm hEnonneg
    hQsymm hQnonneg hQ htail hK₆ hε₃ hε₄ hK₅ hK₆0 hε₃0 (pow_lt_one₀ hε₄0 hε₄1 two_ne_zero) f
  -- `(1 - ε₄)² ≤ 1 - ε₄²` since `0 ≤ ε₄ (1 - ε₄)`.
  have hfac : K₆ / (1 - ε₄ ^ 2) ≤ K₆ / (1 - ε₄) ^ 2 :=
    div_le_div_of_nonneg_left hK₆0 (pow_pos (sub_pos.2 hε₄1) 2)
      (by linarith [mul_nonneg hε₄0 (sub_nonneg.2 hε₄1.le)])
  have hmono := mul_le_mul_of_nonneg_right hfac (hEnonneg f)
  rw [hE f] at hsharp hmono
  linarith

/-- **Capture with a modified functional.** If the capture holds for a form `Q_δ` and the
functional built from another form `Q` differs by at most `δ c_δ M(f, f)`, the residual of
`Q_δ` against the functional of `Q` gains `δ c_δ` in the mass coefficient. -/
theorem finiteRank_capture_le_of_cross
    (Eform Mform Qform Qδform gradientForm : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ)
    {η₂ Λδ K₅δ K₆δ ε₃δ ε₄δ δ cδ : ℝ}
    (hE : ∀ f, Eform f f = gradientForm f f + η₂ * Mform f f)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQδsymm : ∀ f g, Qδform f g = Qδform g f) (hQδ : ∀ f, 0 ≤ Qδform f f)
    (hQδΛ : ∀ f, Qδform f f ≤ Λδ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λδ * Mform f f ≤ K₅δ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
      Qδform u u ≤ K₆δ * Eform u u)
    (hε₃ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      Qδform g g - ∑ j, Qδform g (capturedMode ψ C j) ^ 2 / μ j ≤ ε₃δ * Qδform g g)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄δ ^ 2 * Eform g g * Eform u u)
    (hK₅ : 0 ≤ K₅δ) (hK₆0 : 0 ≤ K₆δ) (hε₃0 : 0 ≤ ε₃δ) (hε₄0 : 0 ≤ ε₄δ) (hε₄1 : ε₄δ < 1)
    (hcross : ∀ f, ∑ j, (Qδform f (capturedMode ψ C j) ^ 2 -
      Qform f (capturedMode ψ C j) ^ 2) / μ j ≤ δ * cδ * Mform f f) :
    ∀ f, Qδform f f - ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j ≤
      (K₅δ + K₆δ / (1 - ε₄δ) ^ 2) * gradientForm f f +
        (η₂ * (K₅δ + K₆δ / (1 - ε₄δ) ^ 2) + ε₃δ * Λδ + δ * cδ) * Mform f f := by
  intro f
  have hcap := finiteRank_capture_le Eform Mform Qδform gradientForm ψ C μ hE hEsymm
    hEnonneg hQδsymm hQδ hQδΛ htail hK₆ hε₃ hε₄ hK₅ hK₆0 hε₃0 hε₄0 hε₄1 f
  have hc := hcross f
  simp only [sub_div, Finset.sum_sub_distrib] at hc
  linarith

/-- **Capture for a shifted form** `Q = Q_δ - δ B`. The capture is certified for the
positive semidefinite form `Q_δ`, while the functional keeps the published pairings
`Q(f, ψ̄ⱼ)`. Since `Q_δ(f, ψ̄ⱼ)² - Q(f, ψ̄ⱼ)² = δ B(f, ψ̄ⱼ) (2 Q(f, ψ̄ⱼ) + δ B(f, ψ̄ⱼ))`,
the cross hypothesis is a bound for that finite-rank quadratic form. -/
theorem finiteRank_capture_le_of_shift
    (Eform Mform Qform Qδform Bform gradientForm : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ)
    {η₂ Λδ K₅δ K₆δ ε₃δ ε₄δ δ cδ : ℝ} (hδ : 0 ≤ δ)
    (hshift : ∀ f g, Qform f g = Qδform f g - δ * Bform f g)
    (hE : ∀ f, Eform f f = gradientForm f f + η₂ * Mform f f)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQδsymm : ∀ f g, Qδform f g = Qδform g f) (hQδ : ∀ f, 0 ≤ Qδform f f)
    (hQδΛ : ∀ f, Qδform f f ≤ Λδ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λδ * Mform f f ≤ K₅δ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
      Qδform u u ≤ K₆δ * Eform u u)
    (hε₃ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      Qδform g g - ∑ j, Qδform g (capturedMode ψ C j) ^ 2 / μ j ≤ ε₃δ * Qδform g g)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄δ ^ 2 * Eform g g * Eform u u)
    (hK₅ : 0 ≤ K₅δ) (hK₆0 : 0 ≤ K₆δ) (hε₃0 : 0 ≤ ε₃δ) (hε₄0 : 0 ≤ ε₄δ) (hε₄1 : ε₄δ < 1)
    (hcross : ∀ f, ∑ j, Bform f (capturedMode ψ C j) *
      (2 * Qform f (capturedMode ψ C j) + δ * Bform f (capturedMode ψ C j)) / μ j ≤
        cδ * Mform f f) :
    ∀ f, Qδform f f - ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j ≤
      (K₅δ + K₆δ / (1 - ε₄δ) ^ 2) * gradientForm f f +
        (η₂ * (K₅δ + K₆δ / (1 - ε₄δ) ^ 2) + ε₃δ * Λδ + δ * cδ) * Mform f f := by
  refine finiteRank_capture_le_of_cross Eform Mform Qform Qδform gradientForm ψ C μ hE
    hEsymm hEnonneg hQδsymm hQδ hQδΛ htail hK₆ hε₃ hε₄ hK₅ hK₆0 hε₃0 hε₄0 hε₄1 ?_
  intro f
  have hterm (j : Fin m) : (Qδform f (capturedMode ψ C j) ^ 2 -
      Qform f (capturedMode ψ C j) ^ 2) / μ j =
        δ * (Bform f (capturedMode ψ C j) *
          (2 * Qform f (capturedMode ψ C j) + δ * Bform f (capturedMode ψ C j)) / μ j) := by
    rw [hshift]
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hcross f) hδ

/-- **Sharp capture with a modified functional.** The energy form of
`finiteRank_capture_le_of_cross`, with the factor `K₆ / (1 - ε₄²)`. -/
theorem finiteRank_capture_le_energy_of_cross
    (Eform Mform Qform Qδform : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ)
    {Λδ K₅δ K₆δ ε₃δ ε₄δ δ cδ : ℝ}
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQδsymm : ∀ f g, Qδform f g = Qδform g f) (hQδ : ∀ f, 0 ≤ Qδform f f)
    (hQδΛ : ∀ f, Qδform f f ≤ Λδ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λδ * Mform f f ≤ K₅δ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
      Qδform u u ≤ K₆δ * Eform u u)
    (hε₃ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      Qδform g g - ∑ j, Qδform g (capturedMode ψ C j) ^ 2 / μ j ≤ ε₃δ * Qδform g g)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄δ ^ 2 * Eform g g * Eform u u)
    (hK₅ : 0 ≤ K₅δ) (hK₆0 : 0 ≤ K₆δ) (hε₃0 : 0 ≤ ε₃δ) (hε₄1 : ε₄δ ^ 2 < 1)
    (hcross : ∀ f, ∑ j, (Qδform f (capturedMode ψ C j) ^ 2 -
      Qform f (capturedMode ψ C j) ^ 2) / μ j ≤ δ * cδ * Mform f f) (f : H) :
    Qδform f f - ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j ≤
      (K₅δ + K₆δ / (1 - ε₄δ ^ 2)) * Eform f f + (ε₃δ * Λδ + δ * cδ) * Mform f f := by
  have hcap := finiteRank_capture_le_energy Eform Mform Qδform ψ C μ hEsymm hEnonneg
    hQδsymm hQδ hQδΛ htail hK₆ hε₃ hε₄ hK₅ hK₆0 hε₃0 hε₄1 f
  have hc := hcross f
  simp only [sub_div, Finset.sum_sub_distrib] at hc
  linarith

/-- The Sedrakyan step behind the shifted capture: if `a² ≤ P c` and `b² ≤ R e` with
nonnegative `P, R, c, e, δ`, then `(a + δ b)² ≤ (P + δ R) (c + δ e)`. -/
theorem sq_add_mul_le_mul_add_mul {a b c e P R δ : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R)
    (hc : 0 ≤ c) (he : 0 ≤ e) (hδ : 0 ≤ δ) (ha : a ^ 2 ≤ P * c) (hb : b ^ 2 ≤ R * e) :
    (a + δ * b) ^ 2 ≤ (P + δ * R) * (c + δ * e) := by
  have hab : 2 * (a * b) ≤ P * e + R * c :=
    two_mul_le_add_of_sq_le_mul (mul_nonneg hP he) (mul_nonneg hR hc) ((mul_pow a b 2).trans_le
      ((mul_le_mul ha hb (sq_nonneg b) (mul_nonneg hP hc)).trans_eq (by ring)))
  linarith [mul_le_mul_of_nonneg_left hab hδ, mul_le_mul_of_nonneg_left hb (sq_nonneg δ)]

/-- **Capture for a nearly positive form without a cross term.** Let `Q = Q_δ - δ B` with
`Q_δ` and `B` positive semidefinite, and let `K₅, K₆, ε₄` be capture constants of `Q_δ`. If
the `Q`-Gram matrix of the modes satisfies `G_Q ≥ (1 - ε₃) Λ` and the functional has the
Bessel bound `∑ⱼ Q(f, ψ̄ⱼ)² / μⱼ ≤ p₀ M(f, f)`, then the published form `Q` is captured with
`M₁ = K₅ + K₆ / (1 - ε₄²)` and `M₂ = η₂ M₁ + ε₃ p₀ / (1 - ε₃)`.

For the `Q_δ`-projection `g` of `f` onto `V_lg`, Sedrakyan's inequality gives
`Q_δ(g, g) ≤ Q(f, g)² / Q(g, g) + δ B(f, g)² / B(g, g)`. The first term is at most
`∑ⱼ Q(f, ψ̄ⱼ)² / ((1 - ε₃) μⱼ)` by the Gram bound, and the second at most `δ B(f, f)`, which
cancels against `Q(f, f) = Q_δ(f, f) - δ B(f, f)`. -/
theorem finiteRank_capture_le_of_shift_gram
    (Eform Mform Qform Qδform Bform gradientForm : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ)
    {η₂ Λδ K₅ K₆ ε₃ ε₄ δ p₀ : ℝ} (hδ : 0 ≤ δ)
    (hshift : ∀ f g, Qform f g = Qδform f g - δ * Bform f g)
    (hBsymm : ∀ f g, Bform f g = Bform g f) (hBnonneg : ∀ f, 0 ≤ Bform f f)
    (hE : ∀ f, Eform f f = gradientForm f f + η₂ * Mform f f)
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQδsymm : ∀ f g, Qδform f g = Qδform g f) (hQδ : ∀ f, 0 ≤ Qδform f f)
    (hQδΛ : ∀ f, Qδform f f ≤ Λδ * Mform f f)
    (htail : ∀ f, (∀ k, Eform f (ψ k) = 0) → Λδ * Mform f f ≤ K₅ * Eform f f)
    (hK₆ : ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
      Qδform u u ≤ K₆ * Eform u u)
    (hε₄ : ∀ g ∈ Submodule.span ℝ (Set.range (capturedMode ψ C)),
      ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qδform u (capturedMode ψ C j) = 0) →
        Eform g u ^ 2 ≤ ε₄ ^ 2 * Eform g g * Eform u u)
    (hμ : ∀ j, 0 < μ j)
    (hgram : ∀ d : Fin m → ℝ, (1 - ε₃) * ∑ j, μ j * d j ^ 2 ≤
      Qform (∑ j, d j • capturedMode ψ C j) (∑ j, d j • capturedMode ψ C j))
    (hp₀ : ∀ f, ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j ≤ p₀ * Mform f f)
    (hK₅ : 0 ≤ K₅) (hK₆0 : 0 ≤ K₆) (hε₃0 : 0 ≤ ε₃) (hε₃1 : ε₃ < 1) (hε₄1 : ε₄ ^ 2 < 1) :
    ∀ f, Qform f f - ∑ j, Qform f (capturedMode ψ C j) ^ 2 / μ j ≤
      (K₅ + K₆ / (1 - ε₄ ^ 2)) * gradientForm f f +
        (η₂ * (K₅ + K₆ / (1 - ε₄ ^ 2)) + ε₃ * p₀ / (1 - ε₃)) * Mform f f := by
  intro f
  set ψbar := capturedMode ψ C
  set M₁ := K₅ + K₆ / (1 - ε₄ ^ 2)
  -- The `Q_δ`-orthogonal projection `g` of `f` onto `V_lg`.
  obtain ⟨d, hd⟩ := exists_sub_sum_smul_orthogonal Qδform hQδsymm hQδ ψbar f
  set g := ∑ j, d j • ψbar j
  have hg : g ∈ Submodule.span ℝ (Set.range ψbar) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨d, rfl⟩
  have hres : Qδform (f - g) (f - g) ≤ M₁ * Eform f f :=
    capture_projection_residual_le Eform Mform Qδform ψ C hEsymm hEnonneg hQδsymm hQδ hQδΛ
      htail hK₆ hε₄ hK₅ hK₆0 hε₄1 hg hd
  have hsplit := form_eq_add_of_orthogonal Qδform hQδsymm ψbar hg hd
  have hfg' : Qδform f g = Qδform g g :=
    form_apply_eq_of_sub_eq_zero Qδform (form_eq_zero_of_mem_span Qδform ψbar hd hg)
  set S := ∑ j, Qform f (ψbar j) ^ 2 / μ j
  set W := ∑ j, μ j * d j ^ 2
  have hε₃pos : 0 < 1 - ε₃ := sub_pos.mpr hε₃1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ div_nonneg (sq_nonneg _) (hμ j).le
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun j _ ↦ mul_nonneg (hμ j).le (sq_nonneg _)
  -- Cauchy–Schwarz in the weights `μⱼ` and the Gram bound.
  have hcs : Qform f g ^ 2 ≤ W * S := by
    rw [form_sum_smul_right]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun j _ ↦ mul_nonneg (hμ j).le (sq_nonneg _))
      (fun j _ ↦ div_nonneg (sq_nonneg _) (hμ j).le) fun j _ ↦ le_of_eq ?_
    field_simp [(hμ j).ne']
  have hc : (1 - ε₃) * W ≤ Qform g g := hgram d
  have hc0 : 0 ≤ Qform g g := (mul_nonneg hε₃pos.le hW0).trans hc
  have hP : Qform f g ^ 2 ≤ S / (1 - ε₃) * Qform g g := by
    refine hcs.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hε₃pos]
    linarith [mul_le_mul_of_nonneg_left hc hS0]
  -- The projection norm exceeds the quadratic of `Q` by at most `δ B(f, f)`.
  have hkey : Qδform g g ≤ S / (1 - ε₃) + δ * Bform f f := by
    have hsq := sq_add_mul_le_mul_add_mul (div_nonneg hS0 hε₃pos.le) (hBnonneg f) hc0
      (hBnonneg g) hδ hP (form_sq_le Bform hBsymm hBnonneg f g)
    rw [show Qform f g + δ * Bform f g = Qδform g g by rw [← hfg', hshift]; ring,
      show Qform g g + δ * Bform g g = Qδform g g by rw [hshift]; ring, sq] at hsq
    rcases (hQδ g).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact add_nonneg (div_nonneg hS0 hε₃pos.le) (mul_nonneg hδ (hBnonneg f))
    · exact le_of_mul_le_mul_right hsq hpos
  have hdiv : S / (1 - ε₃) - S = ε₃ * S / (1 - ε₃) := by
    field_simp
    ring
  have hε₃S : ε₃ * S / (1 - ε₃) ≤ ε₃ * p₀ / (1 - ε₃) * Mform f f := by
    rw [div_mul_eq_mul_div, mul_assoc]
    gcongr; exact hp₀ f
  rw [hE f] at hres
  rw [hshift f f, hsplit]
  linarith

end Capture

section Certificates

variable [TopologicalSpace H] {ι : Type*} [Fintype ι]

/-- **Quasi-orthogonality from eigen-residuals** (Hou–Wang–Yang, Lemma 2). Let the modes
satisfy `Q(ψ̄ⱼ, v) = μⱼ E(ψ̄ⱼ, v) + E(rⱼ, v)` on a subspace `V`. If the residual combination
`∑ⱼ (bⱼ / μⱼ) rⱼ` has energy at most `ε₄²` times that of `∑ⱼ bⱼ ψ̄ⱼ`, then every
combination of the modes makes an `E`-angle at most `ε₄` with every `u ∈ V` that is
`Q`-orthogonal to the modes. -/
theorem form_sq_le_of_residual (Eform Qform : H →L[ℝ] H →L[ℝ] ℝ) (V : Submodule ℝ H)
    (ψbar r : ι → H) (μ : ι → ℝ) {ε₄ : ℝ}
    (hEsymm : ∀ f g, Eform f g = Eform g f) (hEnonneg : ∀ f, 0 ≤ Eform f f)
    (hQsymm : ∀ f g, Qform f g = Qform g f) (hμ : ∀ j, μ j ≠ 0)
    (hres : ∀ j, ∀ v ∈ V, Qform (ψbar j) v = μ j * Eform (ψbar j) v + Eform (r j) v)
    (hε₄ : ∀ b : ι → ℝ, Eform (∑ j, (b j / μ j) • r j) (∑ j, (b j / μ j) • r j) ≤
      ε₄ ^ 2 * Eform (∑ j, b j • ψbar j) (∑ j, b j • ψbar j)) :
    ∀ g ∈ Submodule.span ℝ (Set.range ψbar), ∀ u ∈ V, (∀ j, Qform u (ψbar j) = 0) →
      Eform g u ^ 2 ≤ ε₄ ^ 2 * Eform g g * Eform u u := by
  intro g hg u hu horth
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  have hmode (j : ι) : Eform (ψbar j) u = -(Eform (r j) u / μ j) := by
    have h := hres j u hu
    rw [hQsymm, horth j] at h
    field_simp [hμ j]
    linarith
  have hpair : Eform (∑ j, b j • ψbar j) u = -Eform (∑ j, (b j / μ j) • r j) u := by
    rw [form_sum_smul_left, form_sum_smul_left, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hmode j]
    ring
  rw [hpair, neg_sq]
  calc
    _ ≤ Eform (∑ j, (b j / μ j) • r j) (∑ j, (b j / μ j) • r j) * Eform u u :=
      form_sq_le Eform hEsymm hEnonneg _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hε₄ b) (hEnonneg u)

/-- **Gram mismatch from the mode matrix** (Hou–Wang–Yang, Lemma 1). With `G` the matrix of
`Q` on the modes, `Q(g, g) = dᵀ G d` and `Q(g, ψ̄ⱼ) = (dᵀ G)ⱼ` for `g = ∑ᵢ dᵢ ψ̄ᵢ`, so the
mismatch on the span is a quadratic inequality for `G`. With `y = G^{1/2} d` it reads
`yᵀ (1 - G^{1/2} Λ⁻¹ G^{1/2}) y ≤ ε₃ |y|²`, a bound on the largest eigenvalue only. This
one-sided form is the one certified: for the shifted Gram matrix of the stored modes at
`δ = 1/5000` that eigenvalue is about `-8.9e-5` (even) and `-7.8e-5` (odd). -/
theorem sub_sum_sq_div_le_of_matrix (Qform : H →L[ℝ] H →L[ℝ] ℝ) (ψbar : ι → H) (μ : ι → ℝ)
    {ε₃ : ℝ}
    (hmat : ∀ d : ι → ℝ,
      d ⬝ᵥ formMatrix Qform ψbar ψbar *ᵥ d - ∑ j, (d ᵥ* formMatrix Qform ψbar ψbar) j ^ 2 / μ j ≤
        ε₃ * (d ⬝ᵥ formMatrix Qform ψbar ψbar *ᵥ d)) :
    ∀ g ∈ Submodule.span ℝ (Set.range ψbar),
      Qform g g - ∑ j, Qform g (ψbar j) ^ 2 / μ j ≤ ε₃ * Qform g g := by
  intro g hg
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hg
  have hrow (j : ι) :
      Qform (∑ i, d i • ψbar i) (ψbar j) = (d ᵥ* formMatrix Qform ψbar ψbar) j := by
    simp [Matrix.vecMul, dotProduct]
  simp only [hrow, form_sum_smul_sum_smul]
  exact hmat d

/-- The trial-space bound `K₆` from matrices (Hou–Wang–Yang, (4.17)). With `A` and `B` the
matrices of `Q` and `E` on the trial family and `C` the mode coefficients, the matrix
inequality `cᵀ A c - ∑ⱼ ((cᵀ A C)ⱼ)² / μⱼ ≤ K₆ cᵀ B c` on all of `V_N` gives the bound (4.16)
on the `Q`-orthogonal complement of the modes, where the sum vanishes. -/
theorem capture_bound_of_matrix {N m : ℕ} (Eform Qform : H →L[ℝ] H →L[ℝ] ℝ)
    (ψ : Fin N → H) (C : Fin N → Fin m → ℝ) (μ : Fin m → ℝ) {K₆ : ℝ}
    (hmat : ∀ c : Fin N → ℝ,
      c ⬝ᵥ formMatrix Qform ψ ψ *ᵥ c -
          ∑ j, (c ᵥ* (formMatrix Qform ψ ψ * Matrix.of C)) j ^ 2 / μ j ≤
        K₆ * (c ⬝ᵥ formMatrix Eform ψ ψ *ᵥ c)) :
    ∀ u ∈ Submodule.span ℝ (Set.range ψ), (∀ j, Qform u (capturedMode ψ C j) = 0) →
      Qform u u ≤ K₆ * Eform u u := by
  intro u hu horth
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
  have h := hmat c
  simp only [← form_sum_smul_capturedMode, horth, ← form_sum_smul_sum_smul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Finset.sum_const_zero,
    sub_zero] at h
  exact h

/-- The cross term of a shift from two finite-rank Bessel bounds. If `μⱼ > 0`,
`∑ⱼ bⱼ² / μⱼ ≤ g_B M` and `∑ⱼ qⱼ² / μⱼ ≤ g_Q M`, then
`∑ⱼ bⱼ (2 qⱼ + δ bⱼ) / μⱼ ≤ (2 s + δ g_B) M` whenever `g_B g_Q ≤ s²` and `s ≥ 0`. For a shift
`Q = Q_δ - δ B` take `bⱼ = B(f, ψ̄ⱼ)`, `qⱼ = Q(f, ψ̄ⱼ)` and `M = M(f, f)`.

The bound is loose. For the stored even and odd modes at `δ = 1/5000` it gives
`c_δ ≈ 28.1` and `21.6`, against `5.58` and `6.08` for the exact finite-rank quadratic form,
which `le_mul_form_of_forall_mem_span` reduces to the span of the pairing vectors.
`finiteRank_capture_le_of_shift_gram` needs no cross term. -/
theorem sum_shift_cross_le (b q μ : ι → ℝ) {M gB gQ s δ : ℝ} (hμ : ∀ j, 0 < μ j)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hs : 0 ≤ s) (hgs : gB * gQ ≤ s ^ 2) (hgB : 0 ≤ gB)
    (hb : ∑ j, b j ^ 2 / μ j ≤ gB * M) (hq : ∑ j, q j ^ 2 / μ j ≤ gQ * M) :
    ∑ j, b j * (2 * q j + δ * b j) / μ j ≤ (2 * s + δ * gB) * M := by
  have hsplit : ∑ j, b j * (2 * q j + δ * b j) / μ j =
      2 * ∑ j, b j * q j / μ j + δ * ∑ j, b j ^ 2 / μ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hq0 : 0 ≤ ∑ j, q j ^ 2 / μ j :=
    Finset.sum_nonneg fun j _ ↦ div_nonneg (sq_nonneg _) (hμ j).le
  have hcs : (∑ j, b j * q j / μ j) ^ 2 ≤ (∑ j, b j ^ 2 / μ j) * ∑ j, q j ^ 2 / μ j := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun j _ ↦ div_nonneg (sq_nonneg _) (hμ j).le)
      (fun j _ ↦ div_nonneg (sq_nonneg _) (hμ j).le) fun j _ ↦ le_of_eq ?_
    field_simp [(hμ j).ne']
  have hbq : ∑ j, b j * q j / μ j ≤ s * M := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ (mul_nonneg hs hM))
    calc
      _ ≤ (∑ j, b j ^ 2 / μ j) * ∑ j, q j ^ 2 / μ j := hcs
      _ ≤ (gB * M) * (gQ * M) := mul_le_mul hb hq hq0 (mul_nonneg hgB hM)
      _ = (gB * gQ) * M ^ 2 := by ring
      _ ≤ (s * M) ^ 2 := by rw [mul_pow]; gcongr
  rw [hsplit]
  linarith [mul_le_mul_of_nonneg_left hb hδ]

/-- A function of `f` that depends only on the pairings `M(f, wₖ)` with a finite family is
bounded by `c M(f, f)` once it is bounded on the span of the family: the `M`-projection onto
the span has the same pairings and no larger mass. With `B(f, ψ̄ⱼ) = M(f, βⱼ)` and
`Q(f, ψ̄ⱼ) = M(f, qⱼ)`, this gives the exact cross constant `c_δ` of a shift from a `2m × 2m`
eigenvalue problem on the span of the `βⱼ` and `qⱼ`. -/
theorem le_mul_form_of_forall_mem_span {ι' : Type*} [Finite ι'] (M : H →L[ℝ] H →L[ℝ] ℝ)
    (hMsymm : ∀ f g, M f g = M g f) (hMnonneg : ∀ f, 0 ≤ M f f) (w : ι' → H) (F : H → ℝ)
    (hF : ∀ f g, (∀ k, M f (w k) = M g (w k)) → F f = F g) {c : ℝ} (hc : 0 ≤ c)
    (hspan : ∀ g ∈ Submodule.span ℝ (Set.range w), F g ≤ c * M g g) (f : H) :
    F f ≤ c * M f f := by
  have := Fintype.ofFinite ι'
  obtain ⟨a, ha⟩ := exists_sub_sum_smul_orthogonal M hMsymm hMnonneg w f
  set p := ∑ k, a k • w k
  have hp : p ∈ Submodule.span ℝ (Set.range w) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨a, rfl⟩
  have hmass : M p p ≤ M f f := by
    rw [form_eq_add_of_orthogonal M hMsymm w hp ha]
    linarith [hMnonneg (f - p)]
  rw [hF f p fun k ↦ form_apply_eq_of_sub_eq_zero M (ha k)]
  exact (hspan p hp).trans (mul_le_mul_of_nonneg_left hmass hc)

end Certificates

end PDE.Analysis.Operator
