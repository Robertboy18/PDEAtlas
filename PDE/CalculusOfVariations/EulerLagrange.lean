/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralMinimum
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The weak equation of a finite extended-energy minimum

A finite minimizer of a mixed density satisfies a weak first-variation identity when
the full derivative on `ℝ × ℝⁿ` has conjugate power growth. Its action records
the value and gradient terms together: in the form
`A(x,s,z) r + ⟨D(x,s,z), w⟩`, the identity reads `-div D + A = 0` weakly.

The proof derives the derivative of the integral. Nearby integrability is proved before
comparing real integrals with the extended minimum. A measurable spatial shift makes
the density nonnegative; the shift itself need not be integrable. No density upper-growth
assumption is used.

Since it starts from a finite minimum, this necessary condition needs no coercivity,
convexity, boundedness of the domain, or positive dimension. Boundary
variations lie in the supported smooth-core closure, which is `W¹ᵖ₀` on open sets.
The exponent ranges over `1 ≤ p < ∞`, including `p = 1` with `q = ∞`; the existence
theorems for these energies need `p > 1`.

Here `∇ u` is the weak gradient in `Lp`; `∇ u x` evaluates its chosen
representative. Identities between these representatives are used almost everywhere.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal Topology

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [ENNReal.HolderConjugate p q]

local notation "μ" => domainMeasure n Ω
local notation "B" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := p)
local notation "S" => wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)

/-- A finite extended-energy minimum in a prescribed affine Sobolev class satisfies
an integrable weak first-variation identity for every zero-boundary Sobolev variation.
The full density derivative has conjugate power growth on one common a.e. set.
This includes `p = 1, q = ∞` and assumes no derivative of the integral functional.

Only the shifted density `F + b` must be nonnegative. Finiteness at the minimizer gives
its integrability there, and derivative growth gives integrability along nearby variations.
The spatial shift `b` need only be measurable. -/
theorem integral_firstVariation_eq_zero_of_mixedWkpLIntegral_minimizer
    (hp_top : p ≠ ∞)
    {F : ℝ^n → ℝ × ℝ^n → ℝ}
    {dF : ℝ^n → ℝ × ℝ^n → (ℝ × ℝ^n) →L[ℝ] ℝ}
    {b h : ℝ^n → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hdF : Measurable (fun z : (ℝ^n) × (ℝ × ℝ^n) × (ℝ × ℝ^n) ↦
      dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hlower : ∀ᵐ x ∂μ, ∀ z, -b x ≤ F x z)
    (g u : W^{1,p}(Ω)) (hu : u - g ∈ S)
    (hfinite : (∫⁻ x, ENNReal.ofReal (F x (B u x, ∇ u x) + b x) ∂μ) ≠ ∞)
    (hmin : ∀ w : W^{1,p}(Ω), w - g ∈ S →
      (∫⁻ x, ENNReal.ofReal (F x (B u x, ∇ u x) + b x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (F x (B w x, ∇ w x) + b x) ∂μ)
    (v : W^{1,p}(Ω)) (hv : v ∈ S) :
    Integrable (fun x ↦ dF x (B u x, ∇ u x) (B v x, ∇ v x)) μ ∧
      (∫ x, dF x (B u x, ∇ u x) (B v x, ∇ v x) ∂μ) = 0 := by
  let U (x : ℝ^n) := (B u x, ∇ u x)
  let V (x : ℝ^n) := (B v x, ∇ v x)
  have hpair (w : W^{1,p}(Ω)) : MemLp (fun x ↦ (B w x, ∇ w x)) p μ :=
    memLp_prod_iff.mpr ⟨Lp.memLp (B w), Lp.memLp (∇ w)⟩
  apply (hpair u).integral_derivative_eq_zero_of_lintegral_min
    (q := q) (hpair v) hp_top hF hb hdF hderiv hh hgrowth hlower hfinite
  apply Eventually.of_forall
  intro t
  have htclass : u + t • v - g ∈ S := by
    have hm := (S).toSubmodule.add_mem hu ((S).toSubmodule.smul_mem t hv)
    change u - g + t • v ∈ S at hm
    simpa only [sub_add_eq_add_sub] using hm
  have hrepresentative :
      (fun x ↦ F x (B (u + t • v) x, ∇ (u + t • v) x) + b x) =ᵐ[μ]
        fun x ↦ F x (U x + t • V x) + b x := by
    filter_upwards [Lp.coeFn_add (B u) (t • B v), Lp.coeFn_smul t (B v),
      Lp.coeFn_add (∇ u) (t • ∇ v), Lp.coeFn_smul t (∇ v)]
      with x hBa hBs hGa hGs
    simp only [map_add, map_smul, hBa, hBs, hGa, hGs, Pi.add_apply, Pi.smul_apply,
      U, V, Prod.mk_add_mk, Prod.smul_mk]
  have hle := hmin (u + t • v) htclass
  have hcongr := lintegral_congr_ae (hrepresentative.fun_comp ENNReal.ofReal)
  simp only [Function.comp_def] at hcongr
  rw [hcongr] at hle
  exact hle

end PDE.CalculusOfVariations
