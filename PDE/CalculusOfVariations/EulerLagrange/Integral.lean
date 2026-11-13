/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralMinimum
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.GraphSpace.Operators.FirstJet

/-!
# First variation under density upper growth

An integral density with `p`-growth is integrable on every first-order Sobolev field.
If its derivative has conjugate growth, a minimum in a prescribed boundary class
satisfies the weak Euler–Lagrange equation. Neither convexity nor a uniform spatial
lower bound on the density is needed for this necessary condition.

These are the first-variation arguments of Evans, §8.2.3, Theorem 4 (scalar case) and
§8.2.4(a), Theorem 7 (systems).
The density acts on the value-gradient pair, or on a finite family of such pairs.
The full derivative can therefore include all couplings between the components.
Integrability and differentiation of the functional are proved, not assumed.

## Main results

* `integral_firstVariation_eq_zero_of_mixedWkpIntegral_minimizer`: the scalar weak
  Euler–Lagrange equation.
* `integral_firstVariation_eq_zero_of_vectorWkpIntegral_minimizer`: the same for a finite
  family of components.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.3, Theorem 4, and §8.2.4(a),
  Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)
local notation "S" => wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)

/-- A minimum of a density with `p`-growth has zero weak first variation along
every zero-boundary Sobolev direction. The derivative is the full derivative
in the value and gradient variables. The exponent range includes `p = 1, q = ∞`,
and no boundary regularity or lower bound on the density is required. -/
theorem integral_firstVariation_eq_zero_of_mixedWkpIntegral_minimizer
    (hp_top : p ≠ ∞)
    {F : ℝ^n → ℝ × ℝ^n → ℝ}
    {dF : ℝ^n → ℝ × ℝ^n → (ℝ × ℝ^n) →L[ℝ] ℝ}
    {a h : ℝ^n → ℝ} {C D : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hdF : Measurable (fun z : (ℝ^n) × (ℝ × ℝ^n) × (ℝ × ℝ^n) ↦
      dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (ha : Integrable a μ)
    (hupper : ∀ᵐ x ∂μ, ∀ z, ‖F x z‖ ≤ a x + D * ‖z‖ ^ p.toReal)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (g u : W^{1,p}(Ω)) (hu : u - g ∈ S)
    (hmin : ∀ w : W^{1,p}(Ω), w - g ∈ S →
      (∫ x, F x (B u x, ∇ u x) ∂μ) ≤ ∫ x, F x (B w x, ∇ w x) ∂μ)
    (v : W^{1,p}(Ω)) (hv : v ∈ S) :
    Integrable (fun x ↦ dF x (B u x, ∇ u x) (B v x, ∇ v x)) μ ∧
      (∫ x, dF x (B u x, ∇ u x) (B v x, ∇ v x) ∂μ) = 0 := by
  let J := wkpFirstJetCLM (n := n) (p := p) (Ω := Ω)
  have hbase : Integrable (fun x ↦ F x (J u x)) μ :=
    (Lp.memLp (J u)).integrable_comp_of_norm_rpow_le
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp_top hF ha hupper
  have heq (w : W^{1,p}(Ω)) :
      (∫ x, F x (J w x) ∂μ) = ∫ x, F x (B w x, ∇ w x) ∂μ :=
    integral_congr_ae ((wkpFirstJetCLM_apply_ae w).mono fun x hx ↦ congrArg (F x) hx)
  have hminJ (w : W^{1,p}(Ω)) (hw : w - g ∈ S) :
      (∫ x, F x (J u x) ∂μ) ≤ ∫ x, F x (J w x) ∂μ := by
    rw [heq, heq]
    exact hmin w hw
  obtain ⟨hint, hzero⟩ := integral_firstVariation_eq_zero_of_affine_min
    J.toLinearMap (S).toSubmodule hp_top hF hdF hderiv hh hgrowth g u hu hbase hminJ v hv
  have hrep : (fun x ↦ dF x (J u x) (J v x)) =ᵐ[μ]
      fun x ↦ dF x (B u x, ∇ u x) (B v x, ∇ v x) := by
    filter_upwards [wkpFirstJetCLM_apply_ae u, wkpFirstJetCLM_apply_ae v] with x hu hv
    rw [hu, hv]
  exact ⟨hint.congr hrep, (integral_congr_ae hrep).symm.trans hzero⟩

variable {ι : Type*} [Fintype ι]

local notation "J₀" =>
  (fun w : ι → W^{1,p}(Ω) ↦ fun x : ℝ^n ↦ fun i : ι ↦ (B (w i) x, ∇ (w i) x))

/-- A minimum of a coupled density satisfies its weak Euler–Lagrange system
against every finite family of zero-boundary variations. Density upper growth
provides integrability; conjugate growth of the full derivative permits the
variation. The system need not separate into scalar energies. -/
theorem integral_firstVariation_eq_zero_of_vectorWkpIntegral_minimizer
    (hp_top : p ≠ ∞)
    {F : ℝ^n → (ι → ℝ × ℝ^n) → ℝ}
    {dF : ℝ^n → (ι → ℝ × ℝ^n) → (ι → ℝ × ℝ^n) →L[ℝ] ℝ}
    {a h : ℝ^n → ℝ} {C D : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hdF : Measurable (fun z : (ℝ^n) × (ι → ℝ × ℝ^n) × (ι → ℝ × ℝ^n) ↦
      dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (ha : Integrable a μ)
    (hupper : ∀ᵐ x ∂μ, ∀ z, ‖F x z‖ ≤ a x + D * ‖z‖ ^ p.toReal)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (g u : ι → W^{1,p}(Ω)) (hu : ∀ i, u i - g i ∈ S)
    (hmin : ∀ w : ι → W^{1,p}(Ω), (∀ i, w i - g i ∈ S) →
      (∫ x, F x (J₀ u x) ∂μ) ≤ ∫ x, F x (J₀ w x) ∂μ)
    (v : ι → W^{1,p}(Ω)) (hv : ∀ i, v i ∈ S) :
    Integrable (fun x ↦ dF x (J₀ u x) (J₀ v x)) μ ∧
      (∫ x, dF x (J₀ u x) (J₀ v x) ∂μ) = 0 := by
  classical
  let J := vectorWkpFirstJetCLM (ι := ι) (n := n) (p := p) (Ω := Ω)
  let T : Submodule ℝ (ι → W^{1,p}(Ω)) := Submodule.pi Set.univ fun _ ↦ (S).toSubmodule
  have hmem (w : ι → W^{1,p}(Ω)) : w ∈ T ↔ ∀ i, w i ∈ S := by
    simp only [T, Submodule.mem_pi, Set.mem_univ, forall_const]
    rfl
  have hbase : Integrable (fun x ↦ F x (J u x)) μ :=
    (Lp.memLp (J u)).integrable_comp_of_norm_rpow_le
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp_top hF ha hupper
  have heq (w : ι → W^{1,p}(Ω)) :
      (∫ x, F x (J w x) ∂μ) = ∫ x, F x (J₀ w x) ∂μ :=
    integral_congr_ae ((vectorWkpFirstJetCLM_apply_ae w).mono fun x hx ↦ congrArg (F x) hx)
  have hminJ (w : ι → W^{1,p}(Ω)) (hw : w - g ∈ T) :
      (∫ x, F x (J u x) ∂μ) ≤ ∫ x, F x (J w x) ∂μ := by
    rw [heq, heq]
    exact hmin w ((hmem (w - g)).mp hw)
  obtain ⟨hint, hzero⟩ := integral_firstVariation_eq_zero_of_affine_min
    J.toLinearMap T hp_top hF hdF hderiv hh hgrowth g u ((hmem (u - g)).mpr hu)
      hbase hminJ v ((hmem v).mpr hv)
  have hrep : (fun x ↦ dF x (J u x) (J v x)) =ᵐ[μ]
      fun x ↦ dF x (J₀ u x) (J₀ v x) := by
    filter_upwards [vectorWkpFirstJetCLM_apply_ae u,
      vectorWkpFirstJetCLM_apply_ae v] with x hu hv
    rw [hu, hv]
  exact ⟨hint.congr hrep, (integral_congr_ae hrep).symm.trans hzero⟩

end PDE.CalculusOfVariations
