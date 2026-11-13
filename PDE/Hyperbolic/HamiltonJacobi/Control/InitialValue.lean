/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Viscosity
public import PDE.Hyperbolic.HamiltonJacobi.Control.ValueRegularity
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.SpatialInitialComparison

/-!
# The control value solves the initial-value problem

Bounded Lipschitz terminal data yield a value that is bounded and uniformly
continuous on every finite time slab. Dynamic programming and the integrated
local C¹ chain rule give its viscosity equation; the zero-length horizon gives
the initial datum exactly.

Existence holds in a separable real Hilbert space. In finite dimension, the
momentum and spatial estimates for the control Hamiltonian give uniqueness
among viscosity solutions that are bounded and uniformly continuous on each
finite time slab. No optimal control or compact control space is required.

This is Theorem 2 of Evans, §10.3.3, in the initial-value form of his Remark (iii). The
uniqueness is the comparison theorem of `SpatialInitialComparison`, Theorem 1 of §10.2, whose
condition (3) the control Hamiltonian satisfies as in Remark (i).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Theorem 2 and Remarks (i) and (iii); §10.2,
  condition (3) and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Function Set TopologicalSpace

namespace HamiltonJacobi

section Slab

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]
  [Nonempty A]

/-- Bounded Lipschitz terminal data give bounded uniform continuity of the value
on every finite forward-time slab. The bound is `C*T+D`; spatial and time
moduli follow from response sensitivity and dynamic programming. -/
theorem isBoundedUniformContinuousOnSlabs_controlInitialValue (f : E → A → E)
    (hf : Continuous (fun p : E × A ↦ f p.1 p.2)) (K M : NNReal)
    (hK : ∀ v, LipschitzWith K (fun x ↦ f x v)) (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ)) (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (g : E → ℝ) (D G : NNReal)
    (hg : ∀ x, |g x| ≤ (D : ℝ)) (hG : LipschitzWith G g) :
    IsBoundedUniformContinuousOnSlabs (controlInitialValue f hf K M hK hM h g) := by
  let W := controlInitialValue f hf K M hK hM h g
  change IsBoundedUniformContinuousOnSlabs W
  have hgb : BddBelow (range g) := by
    refine ⟨-(D : ℝ), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (hg x)).1
  intro T hT
  constructor
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(C : ℝ) * T + (D : ℝ), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change 0 ≤ z.2 ∧ z.2 ≤ T at hz
    have hb : |W z| ≤ (C : ℝ) * z.2 + (D : ℝ) := by
      simpa only [W, controlInitialValue, max_eq_left hz.1, zero_sub, neg_neg] using
        abs_control_value_le f hf K M hK hM h C hC g D hg
          (a := -max z.2 0) (b := 0) (neg_nonpos.mpr (le_max_right _ _)) z.1
    rw [Real.norm_eq_abs]
    exact hb.trans (add_le_add (mul_le_mul_of_nonneg_left hz.2 C.property) (le_refl _))
  · let k : NNReal := Real.toNNReal ((1 + (M : ℝ)) * ((L : ℝ) * (0 - -T) + (G : ℝ)) *
        Real.exp ((K : ℝ) * (0 - -T)) + (C : ℝ))
    have hlip := lipschitzWith_control_value_slab f hf K M hK hM
      h hh C L hC hL g hgb G hG (a := -T) (b := 0) (neg_nonpos.mpr hT.le)
    have hw : LipschitzOnWith k W (closedTimeSlab T) := by
      refine LipschitzOnWith.of_dist_le_mul fun z hz w hw ↦ ?_
      change 0 ≤ z.2 ∧ z.2 ≤ T at hz
      change 0 ≤ w.2 ∧ w.2 ≤ T at hw
      let z' : E × Icc (-T) 0 := (z.1, ⟨-z.2, neg_le_neg hz.2, neg_nonpos.mpr hz.1⟩)
      let w' : E × Icc (-T) 0 := (w.1, ⟨-w.2, neg_le_neg hw.2, neg_nonpos.mpr hw.1⟩)
      have hd : dist z' w' = dist z w := by
        change max (dist z.1 w.1) (dist (-z.2) (-w.2)) = max (dist z.1 w.1) (dist z.2 w.2)
        rw [dist_neg_neg]
      have hr := hlip.dist_le_mul z' w'
      rw [hd] at hr
      simpa only [W, controlInitialValue, z', w', max_eq_left hz.1, max_eq_left hw.1] using hr
    exact hw.uniformContinuousOn

end Slab

section Equation

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]
  [Nonempty A]

/-- The infimum over measurable-control costs solves the forward HJB
initial-value problem for bounded Lipschitz terminal data. Tests are locally
C¹; the value itself is required only to be bounded and uniformly continuous
on each finite time slab. -/
theorem isViscosityInitialSolution_controlInitialValue (f : E → A → E)
    (hf : Continuous (fun p : E × A ↦ f p.1 p.2)) (K M : NNReal)
    (hK : ∀ v, LipschitzWith K (fun x ↦ f x v)) (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ)) (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (g : E → ℝ) (D G : NNReal)
    (hg : ∀ x, |g x| ≤ (D : ℝ)) (hG : LipschitzWith G g) :
    IsViscosityInitialSolution (controlHamiltonian f h) g
      (controlInitialValue f hf K M hK hM h g) := by
  have hgb : BddBelow (range g) := by
    refine ⟨-(D : ℝ), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (abs_le.mp (hg x)).1
  exact ⟨isBoundedUniformContinuousOnSlabs_controlInitialValue
      f hf K M hK hM h hh C L hC hL g D G hg hG,
    isSpatialViscositySolution_controlInitialValue f hf K M hK hM h hh C L hC hL g hgb,
    control_initialValue_initial f hf K M hK hM h g⟩

/-- In finite dimension every bounded uniformly continuous viscosity solution
with the same datum agrees with the constructed control value for `t ≥ 0`.
The Hamiltonian estimates follow from the bounded dynamics and the common
state Lipschitz constants. -/
theorem eqOn_controlInitialValue [FiniteDimensional ℝ E] (f : E → A → E)
    (hf : Continuous (fun p : E × A ↦ f p.1 p.2)) (K M : NNReal)
    (hK : ∀ v, LipschitzWith K (fun x ↦ f x v)) (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ)) (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (g : E → ℝ) (D G : NNReal)
    (hg : ∀ x, |g x| ≤ (D : ℝ)) (hG : LipschitzWith G g) {u : E × ℝ → ℝ}
    (hu : IsViscosityInitialSolution (controlHamiltonian f h) g u) :
    EqOn u (controlInitialValue f hf K M hK hM h g) {z : E × ℝ | 0 ≤ z.2} :=
  hu.eqOn_of_initial_eq_of_lipschitz
    (isViscosityInitialSolution_controlInitialValue f hf K M hK hM h hh C L hC hL g D G hg hG)
    (lipschitzWith_controlHamiltonian f h M C hM hC)
    (abs_controlHamiltonian_sub_position_le f h M C hM hC K L hK hL)

end Equation

end HamiltonJacobi
