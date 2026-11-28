/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Spaces of finite energy

Regularity is often measured by a functional `E` on a large space `X` with values in `[0, ∞]`:
`E x` is the square of a norm, and `x` is regular when `E x` is finite. Estimates are then
inequalities `E₂ (T x) ≤ C E₁ x`, which compare well across a scale of functionals. Fixed-point
arguments and Bochner integrals want a normed space `H` of the regular elements and bounded
operators on it instead. This module passes from the first description to the second, so that
each estimate is proved once.

A linear map `J : H → X` from a normed space realizes `H` as the space of finite energy `E`
(`IsEnergySpace`) when `E (J u) = ‖u‖²` for every `u` and every `x` with `E x < ∞` is `J u` for
some `u`. The exponent two is fixed: the energy is the square of the norm. Completeness is a
property of `H` alone, and nothing here uses it. The Sobolev spaces of real order on the whole
space are energy spaces for the Bessel energies (`SobolevSpace.Fractional.isEnergySpace_toL2`),
so every estimate between Bessel energies is a bounded operator between them.

## Main results

* `IsEnergySpace.injective`: the realization is injective.
* `IsEnergySpace.exists_clm`: a linear map `G₀ : F → X` with `E (G₀ u) ≤ C ‖u‖²` lifts to a
  bounded operator `G : F → H` with `J ∘ G = G₀` and `‖G‖ ≤ √C`. `IsEnergySpace.exists_clm₂` is
  the same for bilinear maps with `E (B u v) ≤ C ‖u‖² ‖v‖²`.
* `IsEnergySpace.exists_clm_of_le`, `IsEnergySpace.lift`: a linear `T : X₁ → X₂` with
  `E₂ (T x) ≤ C E₁ x` gives a bounded operator between the two spaces of finite energy over `T`,
  of norm at most `√C` (`norm_lift_le`). It is unique (`clm_ext`), and `energy_le_of_clm` is the
  converse.
* `IsEnergySpace.comp_equiv`: a linear equivalence of the ambient spaces that carries one energy
  to another keeps the space of finite energy.
* `IsEnergySpace.energy_add_le`: `E (x + y) ≤ 2 (E x + E y)`.

## How it works

The lift is chosen pointwise. Each `G₀ u` has finite energy, so it is `J (g u)` for some `g u`.
The map `g` is linear because `J` is injective, and `‖g u‖² = E (G₀ u) ≤ C ‖u‖²` bounds its norm.
No closed graph theorem is used, and the constant is explicit. This is the quantitative form of
`ContinuousLinearMap.exists_lift_of_injective`, which lifts through an injective bounded map of
Banach spaces by the closed graph theorem, without a bound.
-/

@[expose] public noncomputable section

open scoped ENNReal NNReal

namespace PDE.Analysis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X X₁ X₂ : Type*} [AddCommGroup X] [Module 𝕜 X] [AddCommGroup X₁] [Module 𝕜 X₁]
  [AddCommGroup X₂] [Module 𝕜 X₂]
variable {H H₁ H₂ : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁] [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]
variable {F F' : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- **`J` realizes `H` as the space of finite energy `E`**: the energy of `J u` is `‖u‖²`, and
every element of finite energy is `J u` for some `u`. -/
structure IsEnergySpace (E : X → ℝ≥0∞) (J : H →ₗ[𝕜] X) : Prop where
  /-- The energy of `J u` is the square of the norm of `u`. -/
  energy_apply (u : H) : E (J u) = ENNReal.ofReal (‖u‖ ^ 2)
  /-- Every element of finite energy is in the range of `J`. -/
  exists_apply_eq (x : X) : E x < ⊤ → ∃ u, J u = x

namespace IsEnergySpace

variable {E : X → ℝ≥0∞} {J : H →ₗ[𝕜] X} {E₁ : X₁ → ℝ≥0∞} {J₁ : H₁ →ₗ[𝕜] X₁}
  {E₂ : X₂ → ℝ≥0∞} {J₂ : H₂ →ₗ[𝕜] X₂}

/-- The elements of the range of `J` have finite energy. -/
theorem energy_apply_lt_top (hJ : IsEnergySpace E J) (u : H) : E (J u) < ⊤ := by
  rw [hJ.energy_apply]
  exact ENNReal.ofReal_lt_top

/-- An element has finite energy exactly when it is in the range of `J`. -/
theorem energy_lt_top_iff (hJ : IsEnergySpace E J) (x : X) : E x < ⊤ ↔ ∃ u, J u = x :=
  ⟨hJ.exists_apply_eq x, fun ⟨u, hu⟩ ↦ hu ▸ hJ.energy_apply_lt_top u⟩

/-- **The realization is injective**: an element of norm zero is zero. -/
theorem injective (hJ : IsEnergySpace E J) : Function.Injective J := by
  refine (injective_iff_map_eq_zero J).2 fun u hu ↦ ?_
  have h0 : E 0 = 0 := by simpa using hJ.energy_apply 0
  have h := hJ.energy_apply u
  rw [hu, h0, eq_comm, ENNReal.ofReal_eq_zero] at h
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg _)))

/-- The norm from the energy: `‖u‖ ≤ K` when `E (J u) ≤ K²`. -/
theorem norm_le_of_energy_le (hJ : IsEnergySpace E J) {u : H} {K : ℝ} (hK : 0 ≤ K)
    (h : E (J u) ≤ ENNReal.ofReal (K ^ 2)) : ‖u‖ ≤ K := by
  rw [hJ.energy_apply, ENNReal.ofReal_le_ofReal_iff (sq_nonneg K)] at h
  exact le_of_sq_le_sq h hK

/-- **A linear map with values of bounded energy factors through the space of finite energy.**
If `G₀ : F → X` is linear and `E (G₀ u) ≤ C ‖u‖²` for all `u`, there is a bounded operator
`G : F → H` with `J (G u) = G₀ u` and `‖G‖ ≤ √C`. -/
theorem exists_clm (hJ : IsEnergySpace E J) (G₀ : F →ₗ[𝕜] X) {C : ℝ≥0}
    (h : ∀ u, E (G₀ u) ≤ C * ENNReal.ofReal (‖u‖ ^ 2)) :
    ∃ G : F →L[𝕜] H, (∀ u, J (G u) = G₀ u) ∧ ‖G‖ ≤ NNReal.sqrt C := by
  choose g hg using fun u ↦ hJ.exists_apply_eq (G₀ u)
    ((h u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top))
  let L : F →ₗ[𝕜] H :=
    { toFun := g
      map_add' := fun u v ↦ hJ.injective (by simp only [hg, map_add])
      map_smul' := fun c u ↦ hJ.injective (by simp only [hg, map_smul, RingHom.id_apply]) }
  have hbound (u : F) : ‖L u‖ ≤ NNReal.sqrt C * ‖u‖ := by
    refine hJ.norm_le_of_energy_le (by positivity) ?_
    change E (J (g u)) ≤ _
    rw [hg, mul_pow, ← NNReal.coe_pow, NNReal.sq_sqrt, ENNReal.ofReal_mul C.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    exact h u
  exact ⟨L.mkContinuous (NNReal.sqrt C) hbound, hg,
    L.mkContinuous_norm_le (NNReal.sqrt C).coe_nonneg hbound⟩

/-- **An energy estimate is a bounded operator between the spaces of finite energy.** If
`T : X₁ → X₂` is linear and `E₂ (T x) ≤ C E₁ x` on the elements of finite energy, there is a
bounded operator `G : H₁ → H₂` over `T`, that is `J₂ (G u) = T (J₁ u)`, with `‖G‖ ≤ √C`. -/
theorem exists_clm_of_le (h₁ : IsEnergySpace E₁ J₁) (h₂ : IsEnergySpace E₂ J₂)
    (T : X₁ →ₗ[𝕜] X₂) {C : ℝ≥0} (h : ∀ u, E₂ (T (J₁ u)) ≤ C * E₁ (J₁ u)) :
    ∃ G : H₁ →L[𝕜] H₂, (∀ u, J₂ (G u) = T (J₁ u)) ∧ ‖G‖ ≤ NNReal.sqrt C :=
  h₂.exists_clm (T ∘ₗ J₁) fun u ↦ by
    rw [← h₁.energy_apply]
    exact h u

/-- **The bounded operator over a linear map with an energy estimate**, chosen by
`exists_clm_of_le`. It is the only bounded operator `G` with `J₂ (G u) = T (J₁ u)`. -/
def lift (h₁ : IsEnergySpace E₁ J₁) (h₂ : IsEnergySpace E₂ J₂) (T : X₁ →ₗ[𝕜] X₂) (C : ℝ≥0)
    (h : ∀ u, E₂ (T (J₁ u)) ≤ C * E₁ (J₁ u)) : H₁ →L[𝕜] H₂ :=
  Classical.choose (h₁.exists_clm_of_le h₂ T h)

/-- The lift lies over `T`. -/
theorem apply_lift (h₁ : IsEnergySpace E₁ J₁) (h₂ : IsEnergySpace E₂ J₂) (T : X₁ →ₗ[𝕜] X₂)
    (C : ℝ≥0) (h : ∀ u, E₂ (T (J₁ u)) ≤ C * E₁ (J₁ u)) (u : H₁) :
    J₂ (h₁.lift h₂ T C h u) = T (J₁ u) :=
  (Classical.choose_spec (h₁.exists_clm_of_le h₂ T h)).1 u

/-- The norm of the lift is at most `√C`. -/
theorem norm_lift_le (h₁ : IsEnergySpace E₁ J₁) (h₂ : IsEnergySpace E₂ J₂) (T : X₁ →ₗ[𝕜] X₂)
    (C : ℝ≥0) (h : ∀ u, E₂ (T (J₁ u)) ≤ C * E₁ (J₁ u)) :
    ‖h₁.lift h₂ T C h‖ ≤ NNReal.sqrt C :=
  (Classical.choose_spec (h₁.exists_clm_of_le h₂ T h)).2

/-- **Two bounded operators into a space of finite energy that agree after `J` are equal.** -/
theorem clm_ext (hJ : IsEnergySpace E J) {G G' : F →L[𝕜] H} (h : ∀ u, J (G u) = J (G' u)) :
    G = G' :=
  ContinuousLinearMap.ext fun u ↦ hJ.injective (h u)

/-- **A bilinear map with values of bounded energy factors through the space of finite
energy.** If `B : F → F' → X` is bilinear and `E (B u v) ≤ C ‖u‖² ‖v‖²`, there is a bounded
bilinear operator `G` with `J (G u v) = B u v` and `‖G‖ ≤ √C`. -/
theorem exists_clm₂ (hJ : IsEnergySpace E J) (B : F →ₗ[𝕜] F' →ₗ[𝕜] X) {C : ℝ≥0}
    (h : ∀ u v, E (B u v) ≤ C * (ENNReal.ofReal (‖u‖ ^ 2) * ENNReal.ofReal (‖v‖ ^ 2))) :
    ∃ G : F →L[𝕜] F' →L[𝕜] H, (∀ u v, J (G u v) = B u v) ∧ ‖G‖ ≤ NNReal.sqrt C := by
  choose g hg using fun u v ↦ hJ.exists_apply_eq (B u v)
    ((h u v).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)))
  let L : F →ₗ[𝕜] F' →ₗ[𝕜] H := LinearMap.mk₂ 𝕜 g
    (fun u u' v ↦ hJ.injective (by simp only [hg, map_add, LinearMap.add_apply]))
    (fun c u v ↦ hJ.injective (by simp only [hg, map_smul, LinearMap.smul_apply]))
    (fun u v v' ↦ hJ.injective (by simp only [hg, map_add]))
    (fun c u v ↦ hJ.injective (by simp only [hg, map_smul]))
  have hbound (u : F) (v : F') : ‖L u v‖ ≤ NNReal.sqrt C * ‖u‖ * ‖v‖ := by
    refine hJ.norm_le_of_energy_le (by positivity) ?_
    change E (J (g u v)) ≤ _
    rw [hg, mul_pow, mul_pow, ← NNReal.coe_pow, NNReal.sq_sqrt, mul_assoc,
      ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_mul (sq_nonneg _)]
    exact h u v
  exact ⟨L.mkContinuous₂ (NNReal.sqrt C) hbound, hg,
    L.mkContinuous₂_norm_le (NNReal.sqrt C).coe_nonneg hbound⟩

/-- **A space of finite energy seen through a linear equivalence of the ambient spaces**: if
`e : X ≃ X₁` carries the energy `E` to `E'`, then `e ∘ J` realizes `H` as the space of finite
energy `E'`. -/
theorem comp_equiv (hJ : IsEnergySpace E J) (e : X ≃ₗ[𝕜] X₁) {E' : X₁ → ℝ≥0∞}
    (hE : ∀ x, E' (e x) = E x) : IsEnergySpace E' (e.toLinearMap ∘ₗ J) where
  energy_apply u := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hE, hJ.energy_apply]
  exists_apply_eq y hy := by
    obtain ⟨u, hu⟩ := hJ.exists_apply_eq (e.symm y) (by rwa [← hE, e.apply_symm_apply])
    exact ⟨u, by rw [LinearMap.comp_apply, hu, LinearEquiv.coe_coe, e.apply_symm_apply]⟩

/-- **The energy of a sum**: `E (x + y) ≤ 2 (E x + E y)`. On its domain the energy is the square
of a norm, and outside the right side is infinite. -/
theorem energy_add_le (hJ : IsEnergySpace E J) (x y : X) : E (x + y) ≤ 2 * (E x + E y) := by
  by_cases hfin : E x < ⊤ ∧ E y < ⊤
  · obtain ⟨u, rfl⟩ := hJ.exists_apply_eq x hfin.1
    obtain ⟨v, rfl⟩ := hJ.exists_apply_eq y hfin.2
    rw [← map_add, hJ.energy_apply, hJ.energy_apply, hJ.energy_apply,
      ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  · have htop : E x + E y = ⊤ := by
      rcases not_and_or.1 hfin with h | h
      · rw [not_lt, top_le_iff] at h
        rw [h, top_add]
      · rw [not_lt, top_le_iff] at h
        rw [h, add_top]
    rw [htop, ENNReal.mul_top two_ne_zero]
    exact le_top

/-- **A bounded operator over `T` gives the energy estimate** on the elements of finite energy:
`E₂ (T (J₁ u)) ≤ ‖G‖² E₁ (J₁ u)` when `J₂ (G u) = T (J₁ u)`. This is the converse of
`exists_clm_of_le`. -/
theorem energy_le_of_clm (h₁ : IsEnergySpace E₁ J₁) (h₂ : IsEnergySpace E₂ J₂) {T : X₁ → X₂}
    (G : H₁ →L[𝕜] H₂) (hG : ∀ u, J₂ (G u) = T (J₁ u)) (u : H₁) :
    E₂ (T (J₁ u)) ≤ ENNReal.ofReal (‖G‖ ^ 2) * E₁ (J₁ u) := by
  rw [← hG, h₁.energy_apply, h₂.energy_apply, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (G.le_opNorm u) 2)

end IsEnergySpace

end PDE.Analysis
