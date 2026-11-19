/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Existence
public import PDE.Analysis.Convex.Proximal.Optimality
public import PDE.Analysis.InnerProductSpace.NormComparison

/-!
# The resolvent of a proper convex Hilbert subdifferential

For a proper, convex, lower semicontinuous energy `I` on a real Hilbert space and `λ > 0`,
every `w` has exactly one `u` with `u + λ v = w` for some `v ∈ ∂I(u)`, and the resolvent
`w ↦ u` is firmly nonexpansive. These are Evans, §9.6.1, Theorem 1(iv) and Theorem 2(i). The
equation contains a member of the multivalued subdifferential; no gradient or surjectivity
hypothesis is used.

## Main results

* `existsUnique_subdifferential_resolvent`: unique solvability of `u + λ ∂I(u) ∋ w`.
* `resolvent`, `resolvent_spec`: the resolvent and its defining equation.
* `existsUnique_minimizer_proximalEnergy`: the resolvent value is the unique minimizer of the
  proximal energy.
* `resolvent_norm_sq_le_inner`, `lipschitzWith_resolvent`: firm nonexpansiveness and the
  Lipschitz constant one.

## How it works

We follow steps 4 to 7 of Evans's proof of Theorem 1(iv). The solution minimizes
`proximalEnergy I λ w u = I u + ‖u - w‖² / (2λ)`, which differs from Evans's `J` in (3) by the
factor `λ` and a constant. Evans proves the lower bound (5) on `I` by contradiction; we take an
affine minorant from `exists_affine_minorant`, and `exists_minimizer_proximalEnergy` finds the
minimizer by weak compactness of a bounded sublevel. Where Evans computes the subdifferential
of `J`, `residual_mem_subdifferential_of_minimizes` derives the supporting inequality for
`(w - u) / λ` from minimality along segments. Uniqueness and firm nonexpansiveness come from
monotonicity, as in step 7 and in step 1 of the proof of Theorem 2
(`eq_of_subdifferential_resolvent_eq`, `subdifferential_resolvent_norm_sq_le_inner`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, Theorem 1(iv) and steps 4-7 of its proof,
  (3)-(6), pp. 561-563, the definition of the nonlinear resolvent, p. 563, and Theorem 2(i)
  and step 1 of its proof, pp. 563-564. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Two solutions of subdifferential resolvent equations satisfy firm nonexpansiveness. -/
theorem subdifferential_resolvent_norm_sq_le_inner {I : H → EReal} (hproper : IsProper I)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) {w₁ w₂ u₁ u₂ v₁ v₂ : H}
    (h₁ : v₁ ∈ subdifferential I u₁) (h₂ : v₂ ∈ subdifferential I u₂)
    (heq₁ : u₁ + lambda • v₁ = w₁) (heq₂ : u₂ + lambda • v₂ = w₂) :
    ‖u₁ - u₂‖ ^ 2 ≤ inner ℝ (w₁ - w₂) (u₁ - u₂) := by
  have hbalance : w₁ - w₂ = (u₁ - u₂) + lambda • (v₁ - v₂) := by
    rw [← heq₁, ← heq₂, smul_sub]
    abel
  rw [hbalance, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_right (mul_nonneg hlambda (subdifferential_monotone hproper h₁ h₂))

/-- Uniqueness in the resolvent equation follows from monotonicity alone. -/
theorem eq_of_subdifferential_resolvent_eq {I : H → EReal} (hproper : IsProper I)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) {w u₁ u₂ v₁ v₂ : H}
    (h₁ : v₁ ∈ subdifferential I u₁) (h₂ : v₂ ∈ subdifferential I u₂)
    (heq₁ : u₁ + lambda • v₁ = w) (heq₂ : u₂ + lambda • v₂ = w) : u₁ = u₂ := by
  have h := subdifferential_resolvent_norm_sq_le_inner hproper hlambda h₁ h₂ heq₁ heq₂
  simp only [sub_self, inner_zero_left] at h
  have hn : ‖u₁ - u₂‖ = 0 := by nlinarith [norm_nonneg (u₁ - u₂)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hn)

variable [CompleteSpace H]

/-- Every positive resolvent equation has exactly one base point in the subdifferential domain.

This is Evans, §9.6.1, Theorem 1(iv), with the supporting vector exhibited in the equation. -/
theorem existsUnique_subdifferential_resolvent {I : H → EReal} (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    {lambda : ℝ} (hlambda : 0 < lambda) (w : H) :
    ∃! u, ∃ v ∈ subdifferential I u, u + lambda • v = w := by
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_proximalEnergy hproper hconvex hlsc hlambda w
  have hsub := residual_mem_subdifferential_of_minimizes hproper hconvex hu hmin
  have heq : u + lambda • (lambda⁻¹ • (w - u)) = w := by
    rw [smul_inv_smul₀ hlambda.ne']
    abel
  refine ⟨u, ⟨_, hsub, heq⟩, ?_⟩
  rintro z ⟨v, hv, hz⟩
  exact eq_of_subdifferential_resolvent_eq hproper hlambda.le hv hsub hz heq

/-- The resolvent constructed from a proper convex lower-semicontinuous signed energy. -/
def resolvent (I : H → EReal) (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    (lambda : ℝ) (hlambda : 0 < lambda) (w : H) : H :=
  (existsUnique_subdifferential_resolvent hproper hconvex hlsc hlambda w).choose

variable {I : H → EReal} (hproper : IsProper I)
  (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
  {lambda : ℝ} (hlambda : 0 < lambda)

/-- The chosen resolvent satisfies the multivalued equation. -/
theorem resolvent_spec (w : H) :
    ∃ v ∈ subdifferential I (resolvent I hproper hconvex hlsc lambda hlambda w),
      resolvent I hproper hconvex hlsc lambda hlambda w + lambda • v = w :=
  (existsUnique_subdifferential_resolvent hproper hconvex hlsc hlambda w).choose_spec.1

/-- The residual of the constructed resolvent is a supporting vector at its value. -/
theorem resolvent_residual_mem_subdifferential (w : H) :
    lambda⁻¹ • (w - resolvent I hproper hconvex hlsc lambda hlambda w) ∈
      subdifferential I (resolvent I hproper hconvex hlsc lambda hlambda w) := by
  obtain ⟨v, hv, heq⟩ := resolvent_spec hproper hconvex hlsc hlambda w
  have hres : w - resolvent I hproper hconvex hlsc lambda hlambda w = lambda • v := by
    exact sub_eq_iff_eq_add.2 (by simpa only [add_comm] using heq.symm)
  rwa [hres, inv_smul_smul₀ hlambda.ne']

/-- The resolvent is characterized by any solution of the subdifferential equation. -/
theorem resolvent_eq_of_mem_subdifferential {w u v : H}
    (hv : v ∈ subdifferential I u) (heq : u + lambda • v = w) :
    resolvent I hproper hconvex hlsc lambda hlambda w = u := by
  obtain ⟨v₀, hv₀, h₀⟩ := resolvent_spec hproper hconvex hlsc hlambda w
  exact eq_of_subdifferential_resolvent_eq hproper hlambda.le hv₀ hv h₀ heq

/-- The constructed resolvent obeys the strong three-point energy estimate. -/
theorem resolvent_three_point_le (w z : H) :
    proximalEnergy I lambda w (resolvent I hproper hconvex hlsc lambda hlambda w) +
        (quadraticPenalty lambda (resolvent I hproper hconvex hlsc lambda hlambda w) z : EReal) ≤
      proximalEnergy I lambda w z :=
  proximalEnergy_three_point_le hproper
    (resolvent_residual_mem_subdifferential hproper hconvex hlsc hlambda w) z

include hproper hconvex hlsc hlambda in
/-- The constructed resolvent is the unique minimizer of the extended proximal energy. -/
theorem existsUnique_minimizer_proximalEnergy (w : H) :
    ∃! u, ∀ z, proximalEnergy I lambda w u ≤ proximalEnergy I lambda w z := by
  refine ⟨resolvent I hproper hconvex hlsc lambda hlambda w, ?_, ?_⟩
  · exact (minimizes_proximalEnergy_iff hproper hconvex hlambda).2
      (resolvent_residual_mem_subdifferential hproper hconvex hlsc hlambda w)
  · intro u hu
    have hs := (minimizes_proximalEnergy_iff hproper hconvex hlambda).1 hu
    apply (resolvent_eq_of_mem_subdifferential hproper hconvex hlsc hlambda hs ?_).symm
    rw [smul_inv_smul₀ hlambda.ne']
    abel

/-- Firm nonexpansiveness of the constructed resolvent. -/
theorem resolvent_norm_sq_le_inner (x y : H) :
    ‖resolvent I hproper hconvex hlsc lambda hlambda x -
        resolvent I hproper hconvex hlsc lambda hlambda y‖ ^ 2 ≤
      inner ℝ (x - y) (resolvent I hproper hconvex hlsc lambda hlambda x -
        resolvent I hproper hconvex hlsc lambda hlambda y) := by
  obtain ⟨v₁, h₁, heq₁⟩ := resolvent_spec hproper hconvex hlsc hlambda x
  obtain ⟨v₂, h₂, heq₂⟩ := resolvent_spec hproper hconvex hlsc hlambda y
  exact subdifferential_resolvent_norm_sq_le_inner hproper hlambda.le h₁ h₂ heq₁ heq₂

/-- The constructed resolvent does not increase distances. -/
theorem norm_resolvent_sub_le (x y : H) :
    ‖resolvent I hproper hconvex hlsc lambda hlambda x -
        resolvent I hproper hconvex hlsc lambda hlambda y‖ ≤ ‖x - y‖ := by
  simpa only [inv_one, one_mul] using
    norm_le_of_mul_norm_sq_le_inner zero_lt_one
      (by simpa only [one_mul] using
        resolvent_norm_sq_le_inner hproper hconvex hlsc hlambda x y)

/-- The resolvent is 1-Lipschitz, as in Evans, §9.6.1, Theorem 2(i). -/
theorem lipschitzWith_resolvent :
    LipschitzWith 1 (resolvent I hproper hconvex hlsc lambda hlambda) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
    norm_resolvent_sub_le hproper hconvex hlsc hlambda x y

end PDE.Analysis.Convex
