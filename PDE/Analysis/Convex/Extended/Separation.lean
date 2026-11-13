/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.Topology

/-!
# Affine lower bounds for proper convex energies

Separating the closed real-height epigraph from a point immediately below a finite energy
value gives a continuous affine minorant. Comparing the separator at two points on the same
vertical line forces its height coefficient to be strictly positive. No interior assumption
on the effective domain and no lower bound for the energy is required.
-/

@[expose] public section

namespace PDE.Analysis.Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every proper lower-semicontinuous convex energy has a continuous affine minorant. -/
theorem exists_affine_minorant {I : E → EReal} (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I) :
    ∃ (L : E →L[ℝ] ℝ) (b : ℝ), ∀ x, ((L x + b : ℝ) : EReal) ≤ I x := by
  obtain ⟨x₀, r₀, hx₀⟩ := hproper.exists_eq_coe
  have hbelow : (x₀, r₀ - 1) ∉ realEpigraph I := by
    change ¬I x₀ ≤ ((r₀ - 1 : ℝ) : EReal)
    rw [hx₀, EReal.coe_le_coe_iff]
    linarith
  obtain ⟨f, c, hbelow, habove⟩ :=
    geometric_hahn_banach_point_closed hconvex (isClosed_realEpigraph hlsc) hbelow
  let L : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let a : ℝ := f (0, 1)
  have hf (x : E) (r : ℝ) : f (x, r) = L x + a * r := by
    have hp : (x, r) = (x, 0) + r • (0, 1) := by simp
    rw [hp, map_add, map_smul]
    simp [L, a, mul_comm]
  have hheight : c < L x₀ + a * r₀ := by
    rw [← hf]
    exact habove (x₀, r₀) hx₀.le
  rw [hf] at hbelow
  have ha : 0 < a := by nlinarith
  refine ⟨(-a⁻¹) • L, c / a, fun x ↦ ?_⟩
  by_cases hx : I x = ⊤
  · rw [hx]
    exact le_top
  have hxcoe := EReal.coe_toReal hx (hproper.1 x)
  have hsep := habove (x, (I x).toReal) hxcoe.symm.le
  rw [hf] at hsep
  rw [← hxcoe]
  apply EReal.coe_le_coe_iff.2
  change -a⁻¹ * L x + c / a ≤ (I x).toReal
  have hdiv : c / a < L x / a + (I x).toReal := by
    apply (div_lt_iff₀ ha).2
    field_simp
    nlinarith
  simp only [div_eq_mul_inv] at hdiv ⊢
  nlinarith

end PDE.Analysis.Convex
