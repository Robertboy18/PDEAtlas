/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Contact
public import PDE.Hyperbolic.HamiltonJacobi.Control.Hamiltonian
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialValue

/-!
# The Hamilton–Jacobi equation for the control value

The constructed value, with time reversed, satisfies the touching inequalities
for `W_t - inf_v (⟪DₓW, f(x,v)⟫ + h(x,v)) = 0`.
Its test functions are locally C¹; the value need not be
differentiable. The state can be a separable real Hilbert space.

The two contact inequalities come from the trajectory construction and
dynamic programming. The terminal cost need only be bounded below.

This is the existence half of Theorem 2 of Evans, §10.3.3, in the initial-value form of his
Remark (iii); the contact inequalities are steps 2 and 3 of his proof, (26)-(40).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Theorem 2, Remark (iii), and steps 2-3 of the
  proof, equations (26)-(40).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

open Function Set TopologicalSpace
open scoped InnerProductSpace

namespace HamiltonJacobi

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]
  [Nonempty A]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Reversing the time coordinate subtracts the time derivative and leaves
the spatial derivative unchanged. The spatial gradient is its Riesz representative. -/
private theorem reversed_test_rate_eq {φ : E × ℝ → ℝ} {z : E × ℝ}
    (hφ : DifferentiableAt ℝ φ z) (v : E) (c : ℝ) :
    fderiv ℝ φ z (v, -1) + c = ⟪∇ (fun x ↦ φ (x, z.2)) z.1, v⟫_ℝ + c - fderiv ℝ φ z (0, 1) := by
  rw [inner_gradient_left, fderiv_spaceSlice hφ]
  change fderiv ℝ φ z (v, -1) + c = fderiv ℝ φ z (v, 0) + c - fderiv ℝ φ z (0, 1)
  have hp : (v, (-1 : ℝ)) = (v, (0 : ℝ)) - (0, (1 : ℝ)) := by ext <;> simp
  rw [hp, map_sub]
  ring

/-- The time-reversed control value satisfies both local C¹ touching
inequalities for positive time. The dynamics are bounded, continuous and Lipschitz in
the state; the running cost is bounded, jointly measurable and Lipschitz in the state,
uniformly in the control; the terminal cost is only bounded below. -/
theorem isSpatialViscositySolution_controlInitialValue (f : E → A → E)
    (hf : Continuous (fun p : E × A ↦ f p.1 p.2)) (K M : NNReal)
    (hK : ∀ v, LipschitzWith K (fun x ↦ f x v)) (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ)) (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (g : E → ℝ) (hg : BddBelow (range g)) :
    IsSpatialViscositySolution (controlHamiltonian f h) positiveTimeDomain
      (controlInitialValue f hf K M hK hM h g) := by
  constructor
  · refine ⟨isOpen_positiveTimeDomain, fun z hz φ hφ hmax ↦ ?_⟩
    have hr := control_initialValue_upper_contact f hf K M hK hM
      h hh C hC (fun v ↦ (hL v).continuous) g hg
      hz hφ (hmax.isLocalMax (isOpen_positiveTimeDomain.mem_nhds hz))
    have hinf : fderiv ℝ φ z (0, 1) ≤ sInf (range (fun v ↦ ⟪∇ (fun x ↦ φ (x, z.2)) z.1, f z.1 v⟫_ℝ +
          h z.1 v)) := by
      apply le_csInf (range_nonempty _)
      rintro _ ⟨v, rfl⟩
      have hv := hr v
      rw [reversed_test_rate_eq hφ.differentiableAt_one] at hv
      linarith only [hv]
    change fderiv ℝ φ z (0, 1) + -sInf _ ≤ 0
    linarith only [hinf]
  · refine ⟨isOpen_positiveTimeDomain, fun z hz φ hφ hmin ↦ ?_⟩
    let p := ∇ (fun x ↦ φ (x, z.2)) z.1
    let S := range (fun v ↦ ⟪p, f z.1 v⟫_ℝ + h z.1 v)
    have hbdd : BddBelow S := by
      refine ⟨-(‖p‖ * (M : ℝ) + (C : ℝ)), ?_⟩
      rintro _ ⟨v, rfl⟩
      apply (abs_le.mp (?_ : |⟪p, f z.1 v⟫_ℝ + h z.1 v| ≤ _)).1
      exact (abs_add_le _ _).trans (add_le_add ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hM z.1 v) (norm_nonneg p))) (hC z.1 v))
    have hr := control_initialValue_lower_contact f hf K M hK hM h hh C L hC hL
      g hg hz hφ (hmin.isLocalMin (isOpen_positiveTimeDomain.mem_nhds hz))
    have hlower : sInf S - fderiv ℝ φ z (0, 1) ≤
        sInf (range (fun v ↦ fderiv ℝ φ z (f z.1 v, -1) + h z.1 v)) := by
      apply le_csInf (range_nonempty _)
      rintro _ ⟨v, rfl⟩
      have hv := csInf_le hbdd (mem_range_self v)
      dsimp only
      rw [reversed_test_rate_eq hφ.differentiableAt_one]
      exact sub_le_sub_right hv _
    change 0 ≤ fderiv ℝ φ z (0, 1) + -sInf S
    linarith only [hlower, hr]

end HamiltonJacobi
