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
# Euler–Lagrange equations for finite systems

A finite family of scalar Sobolev fields represents a vector-valued map. Its first-order
jet records the value and weak gradient of each component. A density may couple all these
components; no separability or convexity of the density is required.

A finite minimum in the prescribed affine class gives an integrable weak first-variation
identity. The proof assembles the jet with Mathlib's finite-product `MemLp` theorems and
uses the general extended-integral minimum theorem. It does not assume differentiability
of the induced functional.

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
  have hjet (w : Fin m → W^{1,p}(Ω)) : MemLp (J w) p μ :=
    memLp_pi_iff.mpr fun k ↦
      memLp_prod_iff.mpr ⟨Lp.memLp (B (w k)), Lp.memLp (∇ (w k))⟩
  apply (hjet u).integral_derivative_eq_zero_of_lintegral_min
    (q := q) (hjet v) hp_top hF hb hdF hderiv hh hgrowth hlower hfinite
  apply Eventually.of_forall
  intro t
  have htclass : ∀ k, (u + t • v) k - g k ∈ S := by
    intro k
    have hm := (S).toSubmodule.add_mem (hu k) ((S).toSubmodule.smul_mem t (hv k))
    change u k - g k + t • v k ∈ S at hm
    simpa only [Pi.add_apply, Pi.smul_apply, sub_add_eq_add_sub] using hm
  have hcoordinate (k : Fin m) :
      ∀ᵐ x ∂μ, (B ((u + t • v) k) x, ∇ ((u + t • v) k) x) =
        (B (u k) x, ∇ (u k) x) + t • (B (v k) x, ∇ (v k) x) := by
    filter_upwards [Lp.coeFn_add (B (u k)) (t • B (v k)),
      Lp.coeFn_smul t (B (v k)), Lp.coeFn_add (∇ (u k)) (t • ∇ (v k)),
      Lp.coeFn_smul t (∇ (v k))] with x hBa hBs hGa hGs
    simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, hBa, hBs, hGa, hGs,
      Prod.mk_add_mk, Prod.smul_mk]
  have hrepresentative : ∀ᵐ x ∂μ, J (u + t • v) x = J u x + t • J v x := by
    filter_upwards [ae_all_iff.2 hcoordinate] with x hx
    funext k
    exact hx k
  have hle := hmin (u + t • v) htclass
  have hcongr := lintegral_congr_ae
    (hrepresentative.mono fun x hx ↦ congrArg (fun z ↦ ENNReal.ofReal (F x z + b x)) hx)
  rw [hcongr] at hle
  exact hle

end PDE.CalculusOfVariations
