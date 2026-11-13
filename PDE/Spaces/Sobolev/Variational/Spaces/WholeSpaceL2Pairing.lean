/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# The whole-space `L²` pairing as an integral

For `u, v` in the spatial `L²` space `DerivLp n 2 univ` with almost everywhere representatives
`f` and `g`, the inner product `⟪u, v⟫` is `∫ f g`, and every function equal almost everywhere
to `f g` is integrable with that integral. Weak forms of differential operators are sums of
such pairings, with the representatives given by classical derivatives of test fields or by
multiplication with bounded coefficients.
-/

@[expose] public section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- The `L²` inner product computed from almost everywhere representatives. -/
theorem inner_eq_integral_mul_of_ae {u v : DerivLp n 2 univ} {f g : ℝ^n → ℝ}
    (hu : (u : ℝ^n → ℝ) =ᵐ[volume] f) (hv : (v : ℝ^n → ℝ) =ᵐ[volume] g) :
    inner ℝ u v = ∫ x, f x * g x := by
  rw [L2.inner_def]
  simp only [domainMeasure, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- A function equal almost everywhere to the product of the representatives of two `L²`
fields is integrable, and its integral is their inner product. -/
theorem integrable_and_integral_eq_inner {f F G : ℝ^n → ℝ} {u w : DerivLp n 2 univ}
    (hu : (u : ℝ^n → ℝ) =ᵐ[volume] F) (hw : (w : ℝ^n → ℝ) =ᵐ[volume] G)
    (hf : ∀ᵐ x, f x = F x * G x) : Integrable f ∧ ∫ x, f x = inner ℝ u w := by
  have hu2 : MemLp (u : ℝ^n → ℝ) 2 volume := by simpa [domainMeasure] using Lp.memLp u
  have hw2 : MemLp (w : ℝ^n → ℝ) 2 volume := by simpa [domainMeasure] using Lp.memLp w
  have hint : Integrable (fun x ↦ (u : ℝ^n → ℝ) x * (w : ℝ^n → ℝ) x) volume :=
    hu2.integrable_mul (q := 2) hw2
  refine ⟨hint.congr ?_, ?_⟩
  · filter_upwards [hu, hw, hf] with x h1 h2 h3
    rw [h3, h1, h2]
  · rw [inner_eq_integral_mul_of_ae hu hw]
    exact integral_congr_ae hf

end SobolevSpace.GraphSpace
