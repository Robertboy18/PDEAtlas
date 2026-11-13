/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Multilinear maps supported in a conormal direction

If a multilinear map vanishes whenever one argument lies in the kernel of a
linear functional, its values are determined by one transverse tuple. This is
the algebraic step in recovering a jet from its tangential derivatives.
-/

@[expose] public section

namespace MultilinearMap

variable {𝕜 E F ι : Type*} [CommRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [Fintype ι] [LinearOrder ι]

/-- Vanishing in each kernel direction determines a multilinear map from its
value on a normalized transverse vector. The assertion includes the empty tuple. -/
theorem apply_eq_prod_smul_of_vanishes_on_ker
    (A : MultilinearMap 𝕜 (fun _ : ι ↦ E) F) (ℓ : E →ₗ[𝕜] 𝕜)
    {e : E} (he : ℓ e = 1)
    (hA : ∀ (v : ι → E) (i : ι), ℓ (v i) = 0 → A v = 0) (v : ι → E) :
    A v = (∏ i, ℓ (v i)) • A (fun _ ↦ e) := by
  classical
  have h := A.map_sub_map_piecewise v (fun i ↦ ℓ (v i) • e) Finset.univ
  have hz :
      ∑ i : ι, A (fun j ↦
        if j ∈ (Finset.univ : Finset ι) → j < i then v j
        else if i = j then v j - ℓ (v j) • e else ℓ (v j) • e) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply hA _ i
    simp [he]
  simp only [Finset.piecewise_univ, Finset.mem_univ, forall_const] at h
  simp only [Finset.mem_univ, forall_const] at hz
  rw [hz] at h
  exact (sub_eq_zero.mp h).trans (A.map_smul_univ _ _)

end MultilinearMap
