/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Anisotropic

/-!
# Interpolation of density-weighted Sobolev energies

We prove the measure-theoretic interpolation step used in weighted Sobolev estimates.  If an
intermediate nonnegative density is dominated by the geometric mean of two endpoint densities,
Hölder's inequality gives the corresponding log-convex bound for every nonnegative energy
density.  Applying the result to powers of a Sobolev graph coordinate gives a
weighted-coordinate interpolation theorem.

This is the Hölder (log-convexity) step of weighted interpolation. The Caffarelli–Kohn–Nirenberg
inequalities interpolate between `u` and `Du` in `Lᵖ` norms weighted by powers of `|x|`; they
hold exactly under a list of relations among the weights and exponents, one of which is
dimensional balance.

## References

* L. Caffarelli, R. Kohn and L. Nirenberg, "First order interpolation inequalities with weights",
  *Compositio Math.* 53 (1984), no. 3, 259-275, for interpolation inequalities between a function
  and its gradient with power weights `|x|^a`.
  <https://www.numdam.org/item/CM_1984__53_3_259_0/>
* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter II, for Hölder's inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace
namespace Weighted

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Pointwise geometric interpolation of two nonnegative densities. -/
def geometricDensity (θ : ℝ) (w₀ w₁ : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  fun x ↦ w₀ x ^ (1 - θ) * w₁ x ^ θ

/-- Geometric interpolation preserves almost-everywhere measurability. -/
theorem aemeasurable_geometricDensity {θ : ℝ} {w₀ w₁ : α → ℝ≥0∞}
    (hw₀ : AEMeasurable w₀ μ) (hw₁ : AEMeasurable w₁ μ) :
    AEMeasurable (geometricDensity θ w₀ w₁) μ :=
  (hw₀.pow_const (1 - θ)).mul (hw₁.pow_const θ)

/-- Hölder interpolation for an a.e.-dominated intermediate energy density. -/
theorem lintegral_le_geometric_interpolation
    {F₀ F₁ Fθ : α → ℝ≥0∞} {θ : ℝ}
    (hF₀ : AEMeasurable F₀ μ) (hF₁ : AEMeasurable F₁ μ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hdom : Fθ ≤ᵐ[μ] fun x ↦ F₀ x ^ (1 - θ) * F₁ x ^ θ) :
    ∫⁻ x, Fθ x ∂μ ≤
      (∫⁻ x, F₀ x ∂μ) ^ (1 - θ) * (∫⁻ x, F₁ x ∂μ) ^ θ := by
  calc
    ∫⁻ x, Fθ x ∂μ ≤ ∫⁻ x, F₀ x ^ (1 - θ) * F₁ x ^ θ ∂μ :=
      lintegral_mono_ae hdom
    _ ≤ (∫⁻ x, F₀ x ∂μ) ^ (1 - θ) * (∫⁻ x, F₁ x ∂μ) ^ θ :=
      ENNReal.lintegral_mul_norm_pow_le hF₀ hF₁
        (sub_nonneg.mpr hθ₁) hθ₀ (by ring)

/-- Integrating the same energy density against geometrically interpolated measures is
log-convex in the density. -/
theorem lintegral_withDensity_geometricDensity_le
    {energy w₀ w₁ : α → ℝ≥0∞} {θ : ℝ}
    (henergy : AEMeasurable energy μ)
    (hw₀ : AEMeasurable w₀ μ) (hw₁ : AEMeasurable w₁ μ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (∫⁻ x, energy x ∂μ.withDensity (geometricDensity θ w₀ w₁)) ≤
      (∫⁻ x, energy x ∂μ.withDensity w₀) ^ (1 - θ) *
        (∫⁻ x, energy x ∂μ.withDensity w₁) ^ θ := by
  rw [lintegral_withDensity_eq_lintegral_mul₀
      (aemeasurable_geometricDensity hw₀ hw₁) henergy,
    lintegral_withDensity_eq_lintegral_mul₀ hw₀ henergy,
    lintegral_withDensity_eq_lintegral_mul₀ hw₁ henergy]
  apply lintegral_le_geometric_interpolation
    (hw₀.mul henergy) (hw₁.mul henergy) hθ₀ hθ₁
  filter_upwards [] with x
  change (w₀ x ^ (1 - θ) * w₁ x ^ θ) * energy x ≤
    (w₀ x * energy x) ^ (1 - θ) * (w₁ x * energy x) ^ θ
  rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ₁),
    ENNReal.mul_rpow_of_nonneg _ _ hθ₀]
  apply le_of_eq
  calc
    (w₀ x ^ (1 - θ) * w₁ x ^ θ) * energy x =
        (w₀ x ^ (1 - θ) * w₁ x ^ θ) *
          (energy x ^ (1 - θ) * energy x ^ θ) := by
      rw [← ENNReal.rpow_add_of_nonneg (x := energy x) (1 - θ) θ
        (sub_nonneg.mpr hθ₁) hθ₀]
      simp
    _ = (w₀ x ^ (1 - θ) * energy x ^ (1 - θ)) *
        (w₁ x ^ θ * energy x ^ θ) := by
      ac_rfl

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- Pointwise `q`-power of one Sobolev graph coordinate. -/
def coordinatePowerDensity (q : ℝ)
    (U : W^{k,p}(Ω))
    (a : GraphSpace.DerivIndex n k) (x : ℝ^n) : ℝ≥0∞ :=
  ‖(((U : GraphSpace.WkpAmbientOn n k p Ω) a :
    GraphSpace.DerivLp n p Ω) : ℝ^n → ℝ) x‖ₑ ^ q

/-- The `q`-power energy of one Sobolev graph coordinate against a density.

The exponent `q` is independent of the carrier exponent `p`: `p` records which unweighted graph
space contains the coordinate, while `q` specifies the weighted estimate being interpolated. -/
def coordinatePowerEnergyWithDensity (q : ℝ) (density : ℝ^n → ℝ≥0∞)
    (U : W^{k,p}(Ω))
    (a : GraphSpace.DerivIndex n k) : ℝ≥0∞ :=
  ∫⁻ x, coordinatePowerDensity q U a x
    ∂(domainMeasure n Ω).withDensity density

/-- Powers of the extended norm of a Sobolev graph coordinate are a.e. measurable. -/
theorem coordinatePower_aemeasurable (q : ℝ)
    (U : W^{k,p}(Ω))
    (a : GraphSpace.DerivIndex n k) :
    AEMeasurable (coordinatePowerDensity q U a)
      (domainMeasure n Ω) := by
  exact ((Lp.memLp
    ((U : GraphSpace.WkpAmbientOn n k p Ω) a :
      GraphSpace.DerivLp n p Ω)).aemeasurable.enorm).pow_const q

/-- Weighted power energies of every Sobolev coordinate are log-convex in the density. -/
theorem coordinatePowerEnergyWithDensity_geometricDensity_le
    {q θ : ℝ} {w₀ w₁ : ℝ^n → ℝ≥0∞}
    (U : W^{k,p}(Ω))
    (a : GraphSpace.DerivIndex n k)
    (hw₀ : AEMeasurable w₀ (domainMeasure n Ω))
    (hw₁ : AEMeasurable w₁ (domainMeasure n Ω))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    coordinatePowerEnergyWithDensity q (geometricDensity θ w₀ w₁) U a ≤
      (coordinatePowerEnergyWithDensity q w₀ U a) ^ (1 - θ) *
        (coordinatePowerEnergyWithDensity q w₁ U a) ^ θ :=
  lintegral_withDensity_geometricDensity_le
    (coordinatePower_aemeasurable q U a) hw₀ hw₁ hθ₀ hθ₁

/-- Pointwise sum of the `q`-power energies over a finite derivative family. -/
def derivativeFamilyPowerEnergyDensity (q : ℝ)
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω)) (x : ℝ^n) : ℝ≥0∞ :=
  ∑ a ∈ family, coordinatePowerDensity q U a x

/-- Density-weighted `q`-power energy over a finite derivative family. -/
def derivativeFamilyPowerEnergyWithDensity (q : ℝ)
    (density : ℝ^n → ℝ≥0∞)
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω)) : ℝ≥0∞ :=
  ∫⁻ x, derivativeFamilyPowerEnergyDensity q family U x
    ∂(domainMeasure n Ω).withDensity density

/-- Finite sums of Sobolev coordinate power densities are a.e. measurable. -/
theorem derivativeFamilyPowerEnergyDensity_aemeasurable (q : ℝ)
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω)) :
    AEMeasurable (derivativeFamilyPowerEnergyDensity q family U)
      (domainMeasure n Ω) := by
  classical
  exact Finset.aemeasurable_fun_sum family fun a _ ↦
    coordinatePower_aemeasurable q U a

/-- Every finite Sobolev derivative-family energy is log-convex in the density. -/
theorem derivativeFamilyPowerEnergyWithDensity_geometricDensity_le
    {q θ : ℝ} {w₀ w₁ : ℝ^n → ℝ≥0∞}
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω))
    (hw₀ : AEMeasurable w₀ (domainMeasure n Ω))
    (hw₁ : AEMeasurable w₁ (domainMeasure n Ω))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    derivativeFamilyPowerEnergyWithDensity q
        (geometricDensity θ w₀ w₁) family U ≤
      (derivativeFamilyPowerEnergyWithDensity q w₀ family U) ^ (1 - θ) *
        (derivativeFamilyPowerEnergyWithDensity q w₁ family U) ^ θ :=
  lintegral_withDensity_geometricDensity_le
    (derivativeFamilyPowerEnergyDensity_aemeasurable q family U)
    hw₀ hw₁ hθ₀ hθ₁

/-- The scalar `q`-power gauge associated with a finite derivative-family energy.

For `q > 0` this is the usual `q`th-root expression.  It is called a gauge rather than a
`Seminorm` because the exponent range needed for a triangle inequality is not assumed. -/
def derivativeFamilyPowerGaugeWithDensity (q : ℝ)
    (density : ℝ^n → ℝ≥0∞)
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω)) : ℝ≥0∞ :=
  (derivativeFamilyPowerEnergyWithDensity q density family U) ^ q⁻¹

private theorem rpow_rpow_comm (x : ℝ≥0∞) (a b : ℝ) :
    (x ^ a) ^ b = (x ^ b) ^ a := by
  calc
    (x ^ a) ^ b = x ^ (a * b) := (ENNReal.rpow_mul x a b).symm
    _ = x ^ (b * a) := by rw [mul_comm]
    _ = (x ^ b) ^ a := ENNReal.rpow_mul x b a

/-- For positive `q`, the finite derivative-family `q`-power gauge is log-convex in the
density. -/
theorem derivativeFamilyPowerGaugeWithDensity_geometricDensity_le
    {q θ : ℝ} {w₀ w₁ : ℝ^n → ℝ≥0∞}
    (hq : 0 < q)
    (family : Finset (GraphSpace.DerivIndex n k))
    (U : W^{k,p}(Ω))
    (hw₀ : AEMeasurable w₀ (domainMeasure n Ω))
    (hw₁ : AEMeasurable w₁ (domainMeasure n Ω))
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    derivativeFamilyPowerGaugeWithDensity q
        (geometricDensity θ w₀ w₁) family U ≤
      (derivativeFamilyPowerGaugeWithDensity q w₀ family U) ^ (1 - θ) *
        (derivativeFamilyPowerGaugeWithDensity q w₁ family U) ^ θ := by
  have henergy :=
    derivativeFamilyPowerEnergyWithDensity_geometricDensity_le
      (q := q) family U hw₀ hw₁ hθ₀ hθ₁
  unfold derivativeFamilyPowerGaugeWithDensity
  calc
    (derivativeFamilyPowerEnergyWithDensity q
        (geometricDensity θ w₀ w₁) family U) ^ q⁻¹ ≤
        ((derivativeFamilyPowerEnergyWithDensity q w₀ family U) ^ (1 - θ) *
          (derivativeFamilyPowerEnergyWithDensity q w₁ family U) ^ θ) ^ q⁻¹ :=
      ENNReal.rpow_le_rpow henergy (inv_nonneg.mpr hq.le)
    _ = ((derivativeFamilyPowerEnergyWithDensity q w₀ family U) ^ q⁻¹) ^ (1 - θ) *
        ((derivativeFamilyPowerEnergyWithDensity q w₁ family U) ^ q⁻¹) ^ θ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hq.le)]
      congr 1
      · exact rpow_rpow_comm _ _ _
      · exact rpow_rpow_comm _ _ _

end Weighted
end SobolevSpace
