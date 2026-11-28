/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralMinimum
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Functional
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Jet

/-!
# Euler–Lagrange equations for finite systems

A finite family of scalar Sobolev fields represents a vector-valued map. Its first-order
jet records the value and weak gradient of each component. A density may couple all these
components; no separability or convexity of the density is required.

A finite minimum in the prescribed affine class gives an integrable weak first-variation
identity. The jet is a linear map into `Lᵖ`, so the identity is the general extended-integral
minimum theorem `MeasureTheory.integral_firstVariation_eq_zero_of_affine_lintegral_min` on the
product of the zero-boundary spaces. It does not assume differentiability of the induced
functional.

The density is written in two coordinates. In
`integral_firstVariation_eq_zero_of_vectorWkpLIntegral_minimizer` it acts on the family of
value-gradient pairs `Fin m → ℝ × ℝⁿ`. In
`integral_firstVariation_eq_zero_of_vectorWkpLIntegral_le` it acts on the Euclidean value in
`ℝᵐ` and the matrix gradient in `ℝ^(m * n)`, the state of `vectorWkpLIntegral` and of the
existence theorem `exists_minimizer_vectorWkpLIntegral_prescribed_boundary`. Both are the same
theorem for two linear jets. `integral_firstVariation_eq_zero_of_integral_vectorWkp_le` is the
Euclidean form for a minimizer of the ordinary integral, from
`MeasureTheory.integral_firstVariation_eq_zero_of_affine_min_of_integrable`.

This is the necessary-condition argument for systems in Evans, §8.2.4(a), Theorem 7.
The jet uses the maximum norm on the finite family of value-gradient pairs. The power
bound is stated for this norm and the associated operator norm of the full derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(a), Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal Topology

namespace PDE.CalculusOfVariations

variable {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p)
local notation "S" => wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)
local notation "J" =>
  (fun w : Fin m → W^{1,p}(Ω) ↦ fun x : ℝ^n ↦ fun k : Fin m ↦ (B (w k) x, ∇ (w k) x))

/-- A finite extended-energy minimizer of a coupled density satisfies its weak
Euler–Lagrange system against every vector-valued zero-boundary Sobolev variation.
The full derivative has conjugate power growth on one common a.e. set.

Boundary conditions are imposed componentwise in the supported smooth-core closure,
which gives the usual affine `W¹ᵖ₀` class on open sets. The result includes `p = 1, q = ∞`
and allows zero spatial dimension or an empty system. It needs no coercivity,
upper growth bound on the density, or continuity of the derivative. -/
theorem integral_firstVariation_eq_zero_of_vectorWkpLIntegral_minimizer
    (hp_top : p ≠ ∞)
    {F : ℝ^n → (Fin m → ℝ × ℝ^n) → ℝ}
    {dF : ℝ^n → (Fin m → ℝ × ℝ^n) → (Fin m → ℝ × ℝ^n) →L[ℝ] ℝ}
    {b h : ℝ^n → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hdF : Measurable (fun z :
      (ℝ^n) × (Fin m → ℝ × ℝ^n) × (Fin m → ℝ × ℝ^n) ↦
        dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hlower : ∀ᵐ x ∂μ, ∀ z, -b x ≤ F x z)
    (g u : Fin m → W^{1,p}(Ω)) (hu : ∀ k, u k - g k ∈ S)
    (hfinite : (∫⁻ x, ENNReal.ofReal (F x (J u x) + b x) ∂μ) ≠ ∞)
    (hmin : ∀ w : Fin m → W^{1,p}(Ω), (∀ k, w k - g k ∈ S) →
      (∫⁻ x, ENNReal.ofReal (F x (J u x) + b x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (F x (J w x) + b x) ∂μ)
    (v : Fin m → W^{1,p}(Ω)) (hv : ∀ k, v k ∈ S) :
    Integrable (fun x ↦ dF x (J u x) (J v x)) μ ∧
      (∫ x, dF x (J u x) (J v x) ∂μ) = 0 := by
  classical
  let J' := vectorWkpFirstJetCLM (ι := Fin m) (n := n) (p := p) (Ω := Ω)
  let T : Submodule ℝ (Fin m → W^{1,p}(Ω)) := Submodule.pi Set.univ fun _ ↦ (S).toSubmodule
  have hmem (w : Fin m → W^{1,p}(Ω)) : w ∈ T ↔ ∀ k, w k ∈ S := by
    simp only [T, Submodule.mem_pi, Set.mem_univ, forall_const]
    rfl
  have heq (w : Fin m → W^{1,p}(Ω)) :
      (∫⁻ x, ENNReal.ofReal (F x (J' w x) + b x) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (F x (J w x) + b x) ∂μ :=
    lintegral_congr_ae ((vectorWkpFirstJetCLM_apply_ae w).mono fun x hx ↦
      congrArg (fun z ↦ ENNReal.ofReal (F x z + b x)) hx)
  obtain ⟨hint, hzero⟩ := integral_firstVariation_eq_zero_of_affine_lintegral_min
    J'.toLinearMap T hp_top hF hb hdF hderiv hh hgrowth hlower g u ((hmem (u - g)).mpr hu)
    (by rw [ContinuousLinearMap.coe_coe, heq]; exact hfinite)
    (fun w hw ↦ by
      rw [ContinuousLinearMap.coe_coe, heq, heq]
      exact hmin w ((hmem (w - g)).mp hw))
    v ((hmem v).mpr hv)
  have hrep : (fun x ↦ dF x (J' u x) (J' v x)) =ᵐ[μ] fun x ↦ dF x (J u x) (J v x) := by
    filter_upwards [vectorWkpFirstJetCLM_apply_ae u,
      vectorWkpFirstJetCLM_apply_ae v] with x hu hv
    rw [hu, hv]
  exact ⟨hint.congr hrep, (integral_congr_ae hrep).symm.trans hzero⟩

/-- The same statement in Euclidean coordinates, for the energy `vectorWkpLIntegral`. The
density acts on the value in `ℝᵐ` and the matrix gradient in `ℝ^(m * n)`. A finite minimizer
of the extended energy in a prescribed boundary class satisfies the weak Euler–Lagrange system
against every zero-boundary variation `v`:
`∫ dF(x, u, ∇u)(v, ∇v) = 0`, where `dF` is the full derivative in the value and the gradient.
The derivative has conjugate power growth; no upper bound on the density, no convexity and no
coercivity is assumed. -/
theorem integral_firstVariation_eq_zero_of_vectorWkpLIntegral_le
    (hp_top : p ≠ ∞)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ}
    {dF : ℝ^n → ℝ^m × ℝ^(m * n) → (ℝ^m × ℝ^(m * n)) →L[ℝ] ℝ}
    {b h : ℝ^n → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hdF : Measurable (fun z :
      (ℝ^n) × (ℝ^m × ℝ^(m * n)) × (ℝ^m × ℝ^(m * n)) ↦ dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hlower : ∀ᵐ x ∂μ, ∀ z, -b x ≤ F x z)
    (g u : Fin m → W^{1,p}(Ω)) (hu : ∀ k, u k - g k ∈ S)
    (hfinite : vectorWkpLIntegral F b u ≠ ∞)
    (hmin : ∀ w : Fin m → W^{1,p}(Ω), (∀ k, w k - g k ∈ S) →
      vectorWkpLIntegral F b u ≤ vectorWkpLIntegral F b w)
    (v : Fin m → W^{1,p}(Ω)) (hv : ∀ k, v k ∈ S) :
    Integrable (fun x ↦ dF x (vectorWkpValueCLM u x, ∇ u x)
      (vectorWkpValueCLM v x, ∇ v x)) μ ∧
      (∫ x, dF x (vectorWkpValueCLM u x, ∇ u x) (vectorWkpValueCLM v x, ∇ v x) ∂μ) = 0 := by
  let J' := vectorWkpJetCLM (m := m) (n := n) (p := p) (Ω := Ω)
  let T : Submodule ℝ (Fin m → W^{1,p}(Ω)) := Submodule.pi Set.univ fun _ ↦ (S).toSubmodule
  have hmem (w : Fin m → W^{1,p}(Ω)) : w ∈ T ↔ ∀ k, w k ∈ S := by
    simp only [T, Submodule.mem_pi, Set.mem_univ, forall_const]
    rfl
  have heq (w : Fin m → W^{1,p}(Ω)) :
      (∫⁻ x, ENNReal.ofReal (F x (J' w x) + b x) ∂μ) = vectorWkpLIntegral F b w :=
    lintegral_congr_ae ((vectorWkpJetCLM_apply_ae w).mono fun x hx ↦
      congrArg (fun z ↦ ENNReal.ofReal (F x z + b x)) hx)
  obtain ⟨hint, hzero⟩ := integral_firstVariation_eq_zero_of_affine_lintegral_min
    J'.toLinearMap T hp_top hF hb hdF hderiv hh hgrowth hlower g u ((hmem (u - g)).mpr hu)
    (by rw [ContinuousLinearMap.coe_coe, heq]; exact hfinite)
    (fun w hw ↦ by
      rw [ContinuousLinearMap.coe_coe, heq, heq]
      exact hmin w ((hmem (w - g)).mp hw))
    v ((hmem v).mpr hv)
  have hrep : (fun x ↦ dF x (J' u x) (J' v x)) =ᵐ[μ]
      fun x ↦ dF x (vectorWkpValueCLM u x, ∇ u x) (vectorWkpValueCLM v x, ∇ v x) := by
    filter_upwards [vectorWkpJetCLM_apply_ae u, vectorWkpJetCLM_apply_ae v] with x hu hv
    rw [hu, hv]
  exact ⟨hint.congr hrep, (integral_congr_ae hrep).symm.trans hzero⟩

/-- The Euclidean form for the ordinary integral. Let the density be integrable at `u`, and
let `∫ F(x, u, ∇u)` be least among the fields of a prescribed boundary class at which the
density is integrable. Then `u` satisfies the weak Euler–Lagrange system
`∫ dF(x, u, ∇u)(v, ∇v) = 0` against every zero-boundary variation `v`. The derivative has
conjugate power growth. No lower bound, convexity or coercivity is assumed, and fields with a
non-integrable density are not compared. -/
theorem integral_firstVariation_eq_zero_of_integral_vectorWkp_le
    (hp_top : p ≠ ∞)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ}
    {dF : ℝ^n → ℝ^m × ℝ^(m * n) → (ℝ^m × ℝ^(m * n)) →L[ℝ] ℝ}
    {h : ℝ^n → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hdF : Measurable (fun z :
      (ℝ^n) × (ℝ^m × ℝ^(m * n)) × (ℝ^m × ℝ^(m * n)) ↦ dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (g u : Fin m → W^{1,p}(Ω)) (hu : ∀ k, u k - g k ∈ S)
    (hbase : Integrable (fun x ↦ F x (vectorWkpValueCLM u x, ∇ u x)) μ)
    (hmin : ∀ w : Fin m → W^{1,p}(Ω), (∀ k, w k - g k ∈ S) →
      Integrable (fun x ↦ F x (vectorWkpValueCLM w x, ∇ w x)) μ →
      (∫ x, F x (vectorWkpValueCLM u x, ∇ u x) ∂μ) ≤
        ∫ x, F x (vectorWkpValueCLM w x, ∇ w x) ∂μ)
    (v : Fin m → W^{1,p}(Ω)) (hv : ∀ k, v k ∈ S) :
    Integrable (fun x ↦ dF x (vectorWkpValueCLM u x, ∇ u x)
      (vectorWkpValueCLM v x, ∇ v x)) μ ∧
      (∫ x, dF x (vectorWkpValueCLM u x, ∇ u x) (vectorWkpValueCLM v x, ∇ v x) ∂μ) = 0 := by
  let J' := vectorWkpJetCLM (m := m) (n := n) (p := p) (Ω := Ω)
  let T : Submodule ℝ (Fin m → W^{1,p}(Ω)) := Submodule.pi Set.univ fun _ ↦ (S).toSubmodule
  have hmem (w : Fin m → W^{1,p}(Ω)) : w ∈ T ↔ ∀ k, w k ∈ S := by
    simp only [T, Submodule.mem_pi, Set.mem_univ, forall_const]
    rfl
  have hjet (w : Fin m → W^{1,p}(Ω)) : (fun x ↦ F x (J' w x)) =ᵐ[μ]
      fun x ↦ F x (vectorWkpValueCLM w x, ∇ w x) :=
    (vectorWkpJetCLM_apply_ae w).mono fun x hx ↦ congrArg (F x) hx
  obtain ⟨hint, hzero⟩ := integral_firstVariation_eq_zero_of_affine_min_of_integrable
    J'.toLinearMap T hp_top hF hdF hderiv hh hgrowth g u ((hmem (u - g)).mpr hu)
    (hbase.congr (hjet u).symm)
    (fun w hw hwint ↦ by
      rw [ContinuousLinearMap.coe_coe, integral_congr_ae (hjet u), integral_congr_ae (hjet w)]
      exact hmin w ((hmem (w - g)).mp hw) (hwint.congr (hjet w)))
    v ((hmem v).mpr hv)
  have hrep : (fun x ↦ dF x (J' u x) (J' v x)) =ᵐ[μ]
      fun x ↦ dF x (vectorWkpValueCLM u x, ∇ u x) (vectorWkpValueCLM v x, ∇ v x) := by
    filter_upwards [vectorWkpJetCLM_apply_ae u, vectorWkpJetCLM_apply_ae v] with x hu hv
    rw [hu, hv]
  exact ⟨hint.congr hrep, (integral_congr_ae hrep).symm.trans hzero⟩

end PDE.CalculusOfVariations
