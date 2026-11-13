/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.WeakSpectrum

/-!
# Equality in a Rayleigh bound

For symmetric energy and mass forms, equality in a global Rayleigh bound characterizes
nonzero weak eigenfunctions at that bound. The proof uses Mathlib's kernel characterization
of a nonnegative symmetric bilinear form, applied to the shifted energy. A least quotient
therefore gives the weak eigen-equation without differentiating the quotient.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ENNReal InnerProductSpace

namespace SobolevSpace.Weak

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For symmetric energy and mass forms, equality in a global Rayleigh bound
characterizes the nonzero weak eigenfunctions at that bound. Coercivity and compactness
are needed to produce such a bound, not for its equality case. -/
theorem isWeakEigenfunction_iff_rayleigh_eq
    (B M : V →L[ℝ] StrongDual ℝ V) (lambda : ℝ)
    (hB : ∀ u v, B u v = B v u) (hM : ∀ u v, M u v = M v u)
    (hbound : ∀ v, lambda * M v v ≤ B v v) {u : V} (hu : u ≠ 0) :
    IsWeakEigenfunction B M lambda u ↔ B u u = lambda * M u u := by
  constructor
  · exact fun h ↦ h.2 u
  · intro heq
    let Q := (pencilForm B M lambda).toBilinForm
    have hnonneg (v : V) : 0 ≤ Q v v := by
      change 0 ≤ pencilForm B M lambda v v
      rw [pencilForm_apply]
      exact sub_nonneg.mpr (hbound v)
    have hsymm : LinearMap.IsSymm Q := ⟨fun v w ↦ by
      change pencilForm B M lambda v w = pencilForm B M lambda w v
      simp only [pencilForm_apply, hB v w, hM v w]⟩
    have hzero : Q u u = 0 := by
      change pencilForm B M lambda u u = 0
      simp only [pencilForm_apply, heq, sub_self]
    have hker := (Q.apply_apply_same_eq_zero_iff hnonneg hsymm).mp hzero
    have hmap : Q u = 0 := hker
    refine ⟨hu, fun v ↦ ?_⟩
    have hv := congrArg (fun f : V →ₗ[ℝ] ℝ ↦ f v) hmap
    change pencilForm B M lambda u v = 0 at hv
    rw [pencilForm_apply] at hv
    exact sub_eq_zero.mp hv

/-- Every vector attaining the least Rayleigh quotient is a weak eigenfunction.
Strict positivity of the mass form makes the quotient well-defined for every nonzero
vector. No differentiability of the quotient is required. -/
theorem isWeakEigenfunction_of_isLeast_rayleigh
    (B M : V →L[ℝ] StrongDual ℝ V) (lambda : ℝ)
    (hB : ∀ u v, B u v = B v u) (hM : ∀ u v, M u v = M v u)
    (hMpos : ∀ v : V, v ≠ 0 → 0 < M v v)
    (hleast : IsLeast ((fun v : V ↦ B v v / M v v) '' {v | v ≠ 0}) lambda)
    {u : V} (hu : u ≠ 0) (heq : B u u / M u u = lambda) :
    IsWeakEigenfunction B M lambda u := by
  have hbound (v : V) : lambda * M v v ≤ B v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (le_div_iff₀ (hMpos v hv)).mp (hleast.2 ⟨v, hv, rfl⟩)
  apply (isWeakEigenfunction_iff_rayleigh_eq B M lambda hB hM hbound hu).mpr
  exact (div_eq_iff (hMpos u hu).ne').mp heq

end SobolevSpace.Weak
