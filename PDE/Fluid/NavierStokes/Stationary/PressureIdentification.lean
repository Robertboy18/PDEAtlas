/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.RieszPressure
public import PDE.Elliptic.Regularity.Interior.Weyl.SecondOrder
public import PDE.Fluid.NavierStokes.Stationary.ProfileRegularity
import PDE.Analysis.MeasureTheory.Function.LocalL2

/-!
# The pressure of weak self-similar profiles

Let `U = W + w` be a weak solution of the self-similar profile equation
`-½ U - ½ ξ·∇U + (U·∇)U - ΔU + ∇P = 0` (the pressure form of equation (1.6) of Hou, Wang and
Yang), tested only with divergence-free fields, where `W` is a smooth divergence-free field with
`‖DᵏW(x)‖ ≤ Cₖ (1 + ‖x‖)^{-1-k}` and `w ∈ H¹(ℝ³)³` is divergence free. The pressure is the
Riesz pressure `P = Σᵢⱼ RᵢRⱼ(UᵢUⱼ)`: the equation holds against every smooth compactly
supported vector field (`profile_pressure_eq_riesz`).

## How it works

We test the equation with `ψ eₖ`. The functional
`H(φ) = ∫ (profile density of U against φ) - ∫ P div φ` is then the second-order distribution
`profilePairing U P k` with coefficients `Uₖ`, `½ ξⱼ Uₖ - Uₖ Uⱼ - δⱼₖ P` and `-Uₖ`
(`weakProfileDensity_decomposition`). It vanishes on divergence-free fields by the weak equation and
on gradients by the Poisson equation of `P` and `div U = 0`
(`sum_profilePairing_partialDeriv_eq_zero`, `NavierStokes.integral_rieszPressure_mul_laplacian`);
since `Δψ eₖ = ∇∂ₖψ - curl curl (ψ eₖ)`, it annihilates Laplacians
(`profilePairing_laplacian_eq_zero`). Rewriting the background part through
`stationaryVelocityOperator W` (`profilePairing_background`), every coefficient is a
square-integrable function, an `L⁴` function, or `ξⱼ wₖ` with `wₖ ∈ L²`, so its integrals over balls
`B(x, r)`, `r ≥ 1`, grow at most like `(1 + ‖x‖ + r) r^{3/2}`. A harmonic second-order distribution
with this growth vanishes (`LaplacianEquation.secondOrderPairing_eq_zero`), hence so does `H`. No
weighted bound on `ξ·∇w` is needed.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 1.2, (1.6), p. 3.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

namespace NavierStokes.Stationary

open MeasureTheory LaplacianEquation SobolevSpace SobolevSpace.GraphSpace Set
open MeasureTheory.LocallyIntegrable (integrable_mul_right_of_hasCompactSupport)
open scoped Sobolev SobolevSpace.WholeSpaceHilbert RealInnerProductSpace
open Nonuniqueness

/-- The first-order coefficient `½ ξⱼ Uₖ - Uₖ Uⱼ - δⱼₖ P` of the tested profile equation in
the direction `k`. -/
noncomputable def profileFirstCoefficient (U : ℝ^3 → ℝ^3) (P : ℝ^3 → ℝ) (k j : Fin 3)
    (x : ℝ^3) : ℝ :=
  (1 / 2) * x j * U x k - U x k * U x j - if j = k then P x else 0

/-- The profile equation with pressure `P`, tested with `ψ eₖ`: the second-order pairing with
coefficients `Uₖ`, `½ ξⱼ Uₖ - Uₖ Uⱼ - δⱼₖ P` and `-Uₖ`. -/
noncomputable def profilePairing (U : ℝ^3 → ℝ^3) (P : ℝ^3 → ℝ) (k : Fin 3)
    (ψ : ℝ^3 → ℝ) : ℝ :=
  secondOrderPairing (fun x ↦ U x k) (profileFirstCoefficient U P k) (fun x ↦ -U x k) ψ

/-- The first-order coefficients are locally integrable when `U`, the products `UᵢUⱼ` and `P`
are. -/
theorem locallyIntegrable_profileFirstCoefficient {U : ℝ^3 → ℝ^3} {P : ℝ^3 → ℝ}
    (hU : ∀ k, LocallyIntegrable (fun x ↦ U x k) volume)
    (hUU : ∀ i j, LocallyIntegrable (fun x ↦ U x i * U x j) volume)
    (hP : LocallyIntegrable P volume) (k j : Fin 3) :
    LocallyIntegrable (profileFirstCoefficient U P k j) volume := by
  have h1 : LocallyIntegrable (fun x : ℝ^3 ↦ (1 / 2) * x j * U x k) volume := by
    have := locallyIntegrable_continuous_mul (g := fun x : ℝ^3 ↦ (1 / 2) * x j)
      (by fun_prop) (hU k)
    simpa only [mul_assoc] using this
  have h2 : LocallyIntegrable (fun x : ℝ^3 ↦ if j = k then P x else 0) volume := by
    by_cases h : j = k
    · simpa [h] using hP
    · simpa [h] using (locallyIntegrable_const (0 : ℝ) :
        LocallyIntegrable (fun _ : ℝ^3 ↦ (0 : ℝ)) volume)
  exact (h1.sub (hUU k j)).sub h2

/-- With integrable terms, the second-order pairing is a single integral. -/
private theorem secondOrderPairing_eq_integral {a c : ℝ^3 → ℝ} {b : Fin 3 → ℝ^3 → ℝ}
    {ψ : ℝ^3 → ℝ} (ha : Integrable (fun x ↦ a x * ψ x) volume)
    (hb : ∀ j, Integrable (fun x ↦ b j x * PDE.partialDeriv j ψ x) volume)
    (hc : Integrable (fun x ↦ c x * PDE.laplacian ψ x) volume) :
    secondOrderPairing a b c ψ =
      ∫ x, (a x * ψ x + ∑ j, b j x * PDE.partialDeriv j ψ x + c x * PDE.laplacian ψ x) := by
  rw [integral_add (f := fun x ↦ a x * ψ x + ∑ j, b j x * PDE.partialDeriv j ψ x)
      (ha.add (integrable_finsetSum _ fun j _ ↦ hb j)) hc,
    integral_add ha (integrable_finsetSum _ fun j _ ↦ hb j), integral_finsetSum _ fun j _ ↦ hb j]
  rfl

/-- Decomposition of the profile functional into the pairings `profilePairing U P k`. -/
theorem weakProfileDensity_decomposition {U : ℝ^3 → ℝ^3} {P : ℝ^3 → ℝ}
    (hU : ∀ k, LocallyIntegrable (fun x ↦ U x k) volume)
    (hUU : ∀ i j, LocallyIntegrable (fun x ↦ U x i * U x j) volume)
    (hP : LocallyIntegrable P volume) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    Integrable (weakProfileDensity U φ) volume ∧
      Integrable (fun x ↦ P x * PDE.divergence φ x) volume ∧
      (∫ x, weakProfileDensity U φ x) - (∫ x, P x * PDE.divergence φ x) =
        ∑ k, profilePairing U P k (fun x ↦ φ x k) := by
  have hφk (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ φ x k) := contDiff_component hφ k
  have hφkc (k : Fin 3) : HasCompactSupport (fun x ↦ φ x k) := hasCompactSupport_component hc k
  have hb := locallyIntegrable_profileFirstCoefficient hU hUU hP
  have iA (k : Fin 3) : Integrable (fun x ↦ U x k * φ x k) volume :=
    integrable_mul_right_of_hasCompactSupport (hU k) (hφk k).continuous (hφkc k)
  have iB (k j : Fin 3) : Integrable (fun x ↦ profileFirstCoefficient U P k j x *
      PDE.partialDeriv j (fun y ↦ φ y k) x) volume :=
    integrable_mul_right_of_hasCompactSupport (hb k j)
      (PDE.contDiff_top_partialDeriv (i := j) (hφk k)).continuous ((hφkc k).partialDeriv j)
  have iC (k : Fin 3) : Integrable (fun x ↦ -U x k * PDE.laplacian (fun y ↦ φ y k) x) volume :=
    integrable_mul_right_of_hasCompactSupport (hU k).neg
      (PDE.contDiff_laplacian_coord (hφk k)).continuous
      (HasCompactSupport.coordinate_laplacian (hφkc k))
  have hdivc : Continuous (fun x ↦ PDE.divergence φ x) := by
    simp only [PDE.divergence_eq_sum]
    exact continuous_finsetSum _ fun k _ ↦ (PDE.contDiff_top_partialDeriv (hφk k)).continuous
  have hdivs : HasCompactSupport (fun x ↦ PDE.divergence φ x) := by
    simp only [PDE.divergence_eq_sum]
    simpa only [Finset.sum_fn] using
      HasCompactSupport.finset_sum (s := Finset.univ) fun k _ ↦ (hφkc k).partialDeriv k
  have iP : Integrable (fun x ↦ P x * PDE.divergence φ x) volume :=
    integrable_mul_right_of_hasCompactSupport hP hdivc hdivs
  have iK (k : Fin 3) : Integrable (fun x ↦ U x k * φ x k +
      ∑ j, profileFirstCoefficient U P k j x * PDE.partialDeriv j (fun y ↦ φ y k) x +
      -U x k * PDE.laplacian (fun y ↦ φ y k) x) volume :=
    ((iA k).add (integrable_finsetSum _ fun j _ ↦ iB k j)).add (iC k)
  have hpt (x : ℝ^3) : weakProfileDensity U φ x - P x * PDE.divergence φ x =
      ∑ k, (U x k * φ x k +
        ∑ j, profileFirstCoefficient U P k j x * PDE.partialDeriv j (fun y ↦ φ y k) x +
        -U x k * PDE.laplacian (fun y ↦ φ y k) x) := by
    rw [weakProfileDensity_eq_sum U (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      x, PDE.divergence_eq_sum]
    simp only [profileFirstCoefficient, Fin.sum_univ_three, Fin.isValue]
    simp only [Fin.isValue, one_div, ↓reduceIte, one_ne_zero, sub_zero, Fin.reduceEq, neg_mul,
      zero_ne_one]
    ring
  have iD : Integrable (weakProfileDensity U φ) volume := by
    have h := (integrable_finsetSum Finset.univ fun k _ ↦ iK k).add iP
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, ← hpt]
    ring
  refine ⟨iD, iP, ?_⟩
  rw [← integral_sub iD iP, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ fun k _ ↦ iK k]
  exact Finset.sum_congr rfl fun k _ ↦ (secondOrderPairing_eq_integral (iA k) (iB k) (iC k)).symm

/-- Components of `W + w` are sums of components. -/
theorem add_representative_apply (W : ℝ^3 → ℝ^3) (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (x : ℝ^3) (k : Fin 3) : (W + representative w) x k = W x k + representative w x k := rfl

/-- Divergence-free fields: `W` smooth with zero divergence plus a weakly divergence-free
`H¹` field annihilate gradients of test functions. -/
theorem sum_integral_add_representative_mul_partialDeriv_eq_zero {W : ℝ^3 → ℝ^3}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWdiv : ∀ x, PDE.divergence W x = 0)
    {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hw : divergenceCLM w = 0) {θ : ℝ^3 → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) :
    ∑ k, ∫ x, (W + representative w) x k * PDE.partialDeriv k θ x = 0 := by
  have hd (k : Fin 3) := (PDE.contDiff_top_partialDeriv (i := k) hθ).continuous
  have iW (k : Fin 3) : Integrable (fun x ↦ W x k * PDE.partialDeriv k θ x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (contDiff_component hW k).continuous
      (hd k) (hθc.partialDeriv k)
  have iw (k : Fin 3) : Integrable (fun x ↦ representative w x k * PDE.partialDeriv k θ x)
      volume := integrable_base_mul (w k) (hd k) (hθc.partialDeriv k)
  have hsplit (k : Fin 3) : ∫ x, (W + representative w) x k * PDE.partialDeriv k θ x =
      (∫ x, W x k * PDE.partialDeriv k θ x) +
        ∫ x, representative w x k * PDE.partialDeriv k θ x := by
    rw [← integral_add (iW k) (iw k)]
    congr 1
    funext x
    rw [add_representative_apply]
    ring
  rw [Finset.sum_congr rfl fun k _ ↦ hsplit k, Finset.sum_add_distrib]
  have hW0 : ∑ k, ∫ x, W x k * PDE.partialDeriv k θ x = 0 := by
    have h := PDE.Analysis.sum_integral_mul_mul_partialDeriv_eq_neg (a := fun _ ↦ (1 : ℝ))
      contDiff_const hW hWdiv hθ hθc
    simp only [one_mul] at h
    rw [h]
    simp
  have hw0 := sum_integral_base_mul_partialDeriv_eq_zero w hw hθ hθc
  rw [hW0, zero_add]
  exact hw0

/-- Linearity of the integral for an integrand `A + B - ∑ⱼ Cⱼ - D - E`. -/
private theorem integral_add_sub_sum_sub_sub {A B D E : ℝ^3 → ℝ} {C : Fin 3 → ℝ^3 → ℝ}
    (hA : Integrable A volume) (hB : Integrable B volume) (hC : ∀ j, Integrable (C j) volume)
    (hD : Integrable D volume) (hE : Integrable E volume) :
    ∫ x, (A x + B x - ∑ j, C j x - D x - E x) =
      (∫ x, A x) + (∫ x, B x) - (∑ j, ∫ x, C j x) - (∫ x, D x) - ∫ x, E x := by
  have hC' := integrable_finsetSum Finset.univ fun j _ ↦ hC j
  rw [integral_sub (f := fun x ↦ A x + B x - ∑ j, C j x - D x) (((hA.add hB).sub hC').sub hD) hE,
    integral_sub (f := fun x ↦ A x + B x - ∑ j, C j x) ((hA.add hB).sub hC') hD,
    integral_sub (f := fun x ↦ A x + B x) (hA.add hB) hC', integral_add hA hB,
    integral_finsetSum _ fun j _ ↦ hC j]

/-- The profile functional vanishes on gradients: if `U` is weakly divergence free and `P`
solves the weak Poisson equation `∫ P Δχ = -Σᵢⱼ ∫ UᵢUⱼ ∂ᵢ∂ⱼχ`, then
`Σₖ profilePairing U P k (∂ₖχ) = 0`. -/
theorem sum_profilePairing_partialDeriv_eq_zero {U : ℝ^3 → ℝ^3} {P : ℝ^3 → ℝ}
    (hU : ∀ k, LocallyIntegrable (fun x ↦ U x k) volume)
    (hUU : ∀ i j, LocallyIntegrable (fun x ↦ U x i * U x j) volume)
    (hP : LocallyIntegrable P volume)
    (hdiv : ∀ θ : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      ∑ k, ∫ x, U x k * PDE.partialDeriv k θ x = 0)
    (hpoisson : ∀ χ : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      ∫ x, P x * PDE.laplacian χ x =
        -∑ i, ∑ j, ∫ x, U x i * U x j * iteratedPartialDeriv [i, j] χ x)
    {χ : ℝ^3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∑ k, profilePairing U P k (fun x ↦ PDE.partialDeriv k χ x) = 0 := by
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  set g : Fin 3 → ℝ^3 → ℝ := fun k x ↦ PDE.partialDeriv k χ x with hg
  have hgs (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g k) := PDE.contDiff_top_partialDeriv hχ
  have hgc (k : Fin 3) : HasCompactSupport (g k) := hχc.partialDeriv k
  set θ : ℝ^3 → ℝ := fun x ↦ ∑ j, x j * PDE.partialDeriv j χ x with hθdef
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := ContDiff.sum fun j _ ↦
    ((EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).contDiff).mul (PDE.contDiff_top_partialDeriv hχ)
  have hθc : HasCompactSupport θ := by
    simpa only [hθdef, Finset.sum_fn] using HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun j (y : ℝ^3) ↦ y j * PDE.partialDeriv j χ y) fun j _ ↦ (hχc.partialDeriv j).mul_left
  have hl := PDE.contDiff_laplacian_coord hχ
  have hlc := HasCompactSupport.coordinate_laplacian hχc
  -- pointwise identities
  have hcomm (j k : Fin 3) (x : ℝ^3) : PDE.partialDeriv j (g k) x =
      iteratedPartialDeriv [k, j] χ x := by
    simp only [hg, iteratedPartialDeriv]
    exact PDE.partialDeriv_partialDeriv_comm j k (hχ.of_le h2) x
  have hθd (k : Fin 3) (x : ℝ^3) : PDE.partialDeriv k θ x =
      g k x + ∑ j, x j * PDE.partialDeriv j (g k) x := by
    have hdj (j : Fin 3) : DifferentiableAt ℝ (fun y : ℝ^3 ↦ y j * PDE.partialDeriv j χ y) x :=
      (((EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).differentiableAt).mul
        ((PDE.contDiff_top_partialDeriv hχ).differentiable (by simp) x))
    rw [hθdef, PDE.partialDeriv_sum _ (fun j _ ↦ hdj j)]
    have hterm (j : Fin 3) : PDE.partialDeriv k (fun y : ℝ^3 ↦ y j * PDE.partialDeriv j χ y) x =
        (if k = j then 1 else 0) * PDE.partialDeriv j χ x +
          x j * PDE.partialDeriv j (g k) x := by
      have hcd : DifferentiableAt ℝ (fun y : ℝ^3 ↦ y j) x := by fun_prop
      rw [PDE.partialDeriv_mul (f := fun y : ℝ^3 ↦ y j) (g := fun y ↦ PDE.partialDeriv j χ y) hcd
        ((PDE.contDiff_top_partialDeriv hχ).differentiable (by simp) x)]
      rw [PDE.partialDeriv_coord k j x, hcomm j k x]
      simp only [iteratedPartialDeriv]
    simp only [hterm, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  have hΔg (k : Fin 3) (x : ℝ^3) : PDE.laplacian (g k) x =
      PDE.partialDeriv k (fun y ↦ PDE.laplacian χ y) x := PDE.laplacian_partialDeriv_eq hχ k x
  have hΔχ (x : ℝ^3) : PDE.laplacian χ x = ∑ k, PDE.partialDeriv k (g k) x := rfl
  -- integrability of all pieces
  have hb := locallyIntegrable_profileFirstCoefficient hU hUU hP
  have hgd (k j : Fin 3) := (PDE.contDiff_top_partialDeriv (i := j) (hgs k)).continuous
  have hgdc (k j : Fin 3) : HasCompactSupport (fun x ↦ PDE.partialDeriv j (g k) x) :=
    (hgc k).partialDeriv j
  have iA (k : Fin 3) : Integrable (fun x ↦ U x k * g k x) volume :=
    integrable_mul_right_of_hasCompactSupport (hU k) (hgs k).continuous (hgc k)
  have iB (k j : Fin 3) : Integrable (fun x ↦ profileFirstCoefficient U P k j x *
      PDE.partialDeriv j (g k) x) volume :=
    integrable_mul_right_of_hasCompactSupport (hb k j) (hgd k j) (hgdc k j)
  have iC (k : Fin 3) : Integrable (fun x ↦ -U x k * PDE.laplacian (g k) x) volume :=
    integrable_mul_right_of_hasCompactSupport (hU k).neg
      (PDE.contDiff_laplacian_coord (hgs k)).continuous
      (HasCompactSupport.coordinate_laplacian (hgc k))
  have iT (k : Fin 3) : Integrable (fun x ↦ U x k * PDE.partialDeriv k θ x) volume :=
    integrable_mul_right_of_hasCompactSupport (hU k) (PDE.contDiff_top_partialDeriv hθ).continuous
      (hθc.partialDeriv k)
  have iUU (k j : Fin 3) : Integrable (fun x ↦ U x k * U x j * PDE.partialDeriv j (g k) x)
      volume := integrable_mul_right_of_hasCompactSupport (hUU k j) (hgd k j) (hgdc k j)
  have iP (k : Fin 3) : Integrable (fun x ↦ P x * PDE.partialDeriv k (g k) x) volume :=
    integrable_mul_right_of_hasCompactSupport hP (hgd k k) (hgdc k k)
  have iL (k : Fin 3) : Integrable
      (fun x ↦ U x k * PDE.partialDeriv k (fun y ↦ PDE.laplacian χ y) x) volume :=
    integrable_mul_right_of_hasCompactSupport (hU k) (PDE.contDiff_top_partialDeriv hl).continuous
      (hlc.partialDeriv k)
  have hk (k : Fin 3) : profilePairing U P k (g k) =
      (1 / 2) * (∫ x, U x k * g k x) + (1 / 2) * (∫ x, U x k * PDE.partialDeriv k θ x) -
        (∑ j, ∫ x, U x k * U x j * PDE.partialDeriv j (g k) x) -
        (∫ x, P x * PDE.partialDeriv k (g k) x) -
        ∫ x, U x k * PDE.partialDeriv k (fun y ↦ PDE.laplacian χ y) x := by
    have eL : profilePairing U P k (g k) = ∫ x, (U x k * g k x +
        ∑ j, profileFirstCoefficient U P k j x * PDE.partialDeriv j (g k) x +
        -U x k * PDE.laplacian (g k) x) := secondOrderPairing_eq_integral (iA k) (iB k) (iC k)
    rw [eL, ← integral_const_mul, ← integral_const_mul, ← integral_add_sub_sum_sub_sub
      ((iA k).const_mul (1 / 2)) ((iT k).const_mul (1 / 2)) (iUU k) (iP k) (iL k)]
    congr 1
    funext x
    have hsum : ∑ j, profileFirstCoefficient U P k j x * PDE.partialDeriv j (g k) x =
        (1 / 2) * U x k * (∑ j, x j * PDE.partialDeriv j (g k) x) -
          ∑ j, U x k * U x j * PDE.partialDeriv j (g k) x -
          P x * PDE.partialDeriv k (g k) x := by
      simp only [profileFirstCoefficient, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [hsum, hΔg k x, show (∑ j, x j * PDE.partialDeriv j (g k) x) =
      PDE.partialDeriv k θ x - g k x by rw [hθd k x]; ring]
    ring
  rw [Finset.sum_congr rfl fun k _ ↦ hk k]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ k, ∫ x, U x k * g k x = 0 := hdiv χ hχ hχc
  have h2 : ∑ k, ∫ x, U x k * PDE.partialDeriv k θ x = 0 := hdiv θ hθ hθc
  have h3 : ∑ k, ∫ x, U x k * PDE.partialDeriv k (fun y ↦ PDE.laplacian χ y) x = 0 :=
    hdiv _ hl hlc
  have h4 : ∑ k, ∫ x, P x * PDE.partialDeriv k (g k) x = ∫ x, P x * PDE.laplacian χ x := by
    rw [← integral_finsetSum _ fun k _ ↦ iP k]
    congr 1
    funext x
    rw [hΔχ, Finset.mul_sum]
  have h5 : ∑ k, ∑ j, ∫ x, U x k * U x j * PDE.partialDeriv j (g k) x =
      ∑ i, ∑ j, ∫ x, U x i * U x j * iteratedPartialDeriv [i, j] χ x := by
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    funext x
    rw [hcomm j k x]
  rw [h1, h2, h3, h4, h5, hpoisson χ hχ hχc]
  ring

/-- The profile functional annihilates Laplacians in each direction, once it vanishes on
divergence-free fields and on gradients: `Δψ eₖ = ∇∂ₖψ - curl curl (ψ eₖ)`. -/
theorem profilePairing_laplacian_eq_zero {U : ℝ^3 → ℝ^3} {P : ℝ^3 → ℝ}
    (hU : ∀ k, LocallyIntegrable (fun x ↦ U x k) volume)
    (hUU : ∀ i j, LocallyIntegrable (fun x ↦ U x i * U x j) volume)
    (hP : LocallyIntegrable P volume)
    (hsol : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) → ∑ m, profilePairing U P m (fun x ↦ φ x m) = 0)
    (hgrad : ∀ χ : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      ∑ m, profilePairing U P m (fun x ↦ PDE.partialDeriv m χ x) = 0)
    (k : Fin 3) {ψ : ℝ^3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    profilePairing U P k (fun x ↦ PDE.laplacian ψ x) = 0 := by
  have hb := locallyIntegrable_profileFirstCoefficient hU hUU hP
  set χ : ℝ^3 → ℝ := fun x ↦ PDE.partialDeriv k ψ x
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := PDE.contDiff_top_partialDeriv hψ
  have hχc : HasCompactSupport χ := hψc.partialDeriv k
  have h1 := hgrad χ hχ hχc
  have hcc := contDiff_curlCurlField hψ k
  have h2 := hsol (curlCurlField ψ k) hcc (hasCompactSupport_curlCurlField hψc k)
    (divergence_curlCurlField hψ k)
  have hdiff (m : Fin 3) : profilePairing U P m (fun x ↦ PDE.partialDeriv m χ x) -
      profilePairing U P m (fun x ↦ curlCurlField ψ k x m) =
      profilePairing U P m (fun x ↦ if m = k then PDE.laplacian ψ x else 0) := by
    unfold profilePairing
    rw [← secondOrderPairing_sub (f := fun x ↦ PDE.partialDeriv m χ x)
      (g := fun x ↦ curlCurlField ψ k x m) (c := fun x ↦ -U x m) (hU m) (hb m) (hU m).neg
      (PDE.contDiff_top_partialDeriv hχ)
      (hχc.partialDeriv m) (contDiff_component hcc m)
      (hasCompactSupport_component (hasCompactSupport_curlCurlField hψc k) m)]
    congr 1
    funext x
    rw [curlCurlField_apply]
    ring
  have hsum := congrArg₂ (· - ·) h1 h2
  simp only [sub_zero, ← Finset.sum_sub_distrib, hdiff] at hsum
  rw [Fin.sum_univ_three] at hsum
  fin_cases k <;> simpa [secondOrderPairing_zero, profilePairing] using hsum

/-- For a smooth divergence-free background field, the pressure-free profile pairing is the
pairing with the stationary operator. -/
theorem profilePairing_background {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWdiv : ∀ x, PDE.divergence W x = 0) (k : Fin 3) {ψ : ℝ^3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    profilePairing W (fun _ ↦ 0) k ψ = ∫ x, stationaryVelocityOperator W x k * ψ x := by
  set φ : ℝ^3 → ℝ^3 := fun x ↦ ψ x • EuclideanSpace.single k (1 : ℝ) with hφdef
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.smul contDiff_const
  have hφc : HasCompactSupport φ := hψc.smul_right
  have hφk : (fun x ↦ φ x k) = ψ := funext fun x ↦ by simp [hφdef]
  have h := integral_background_profile_eq hW hWdiv hφ hφc k
  have hfd (x : ℝ^3) : fderiv ℝ φ x x k = ∑ j, x j * PDE.partialDeriv j ψ x := by
    rw [PDE.Analysis.fderiv_apply_component (hφ.differentiable (by simp) x) x k, hφk]
  rw [show (fun y ↦ φ y k) = ψ from hφk] at h
  simp only [hfd, show ∀ x, φ x k = ψ x from congrFun hφk] at h
  rw [← h]
  have hWk (i : Fin 3) := (contDiff_component hW i).continuous
  have hd (j : Fin 3) := (PDE.contDiff_top_partialDeriv (i := j) hψ).continuous
  have i1 (j : Fin 3) : Integrable (fun x ↦ x j * W x k * PDE.partialDeriv j ψ x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right
      (((EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous).mul (hWk k)) (hd j)
      (hψc.partialDeriv j)
  have i2 (j : Fin 3) : Integrable (fun x ↦ W x k * W x j * PDE.partialDeriv j ψ x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hWk k).mul (hWk j)) (hd j)
      (hψc.partialDeriv j)
  have hfirst (j : Fin 3) : ∫ x, profileFirstCoefficient W (fun _ ↦ 0) k j x *
      PDE.partialDeriv j ψ x = (1 / 2) * (∫ x, x j * W x k * PDE.partialDeriv j ψ x) -
        ∫ x, W x k * W x j * PDE.partialDeriv j ψ x := by
    rw [← integral_const_mul, ← integral_sub ((i1 j).const_mul _) (i2 j)]
    congr 1
    funext x
    simp only [profileFirstCoefficient, ite_self, sub_zero]
    ring
  have hhalf : ∫ x, W x k * ∑ j, x j * PDE.partialDeriv j ψ x =
      ∑ j, ∫ x, x j * W x k * PDE.partialDeriv j ψ x := by
    rw [← integral_finsetSum _ fun j _ ↦ i1 j]
    congr 1
    funext x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  unfold profilePairing secondOrderPairing
  simp only [hfirst, Finset.sum_sub_distrib, ← Finset.mul_sum, neg_mul, integral_neg, hhalf]
  ring

/-- For `1 ≤ p < ∞` with `p ≤ 4`, the Hölder exponent `3 (1 - 1/p) - 1` of `Lᵖ(ℝ³)` is at most
`3/2`. -/
private theorem three_exponent_le {p : ENNReal} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤)
    (hp : p.toReal ≤ 4) : ((3 : ℕ) : ℝ) * (1 - 1 / p.toReal) - 1 ≤ 3 / 2 := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos hp1)) hpt
  have : 1 / p.toReal ≥ 1 / 4 := one_div_le_one_div_of_le hp0 hp
  push_cast
  linarith

/-- **The pressure of a weak self-similar profile is the Riesz pressure.** Let `W` be a smooth,
bounded, divergence-free field with `W ∈ L⁴` and `stationaryVelocityOperator W ∈ Lᵖ` for some
`1 ≤ p ≤ 4`, and let `w ∈ H¹(ℝ³)³` be divergence free with `U = W + w` a weak solution of the
profile equation (tested with divergence-free fields). Then `stationaryVelocityOperator U + ∇P = 0`
with `P = rieszPressure U` holds against every smooth compactly supported vector field `φ`:
`∫ (profile density of U against φ) = ∫ P div φ`. -/
theorem profile_pressure_eq_riesz_of_memLp_exponent {W : ℝ^3 → ℝ^3}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWdiv : ∀ x, PDE.divergence W x = 0) {C₀ : ℝ}
    (hWbd : ∀ x, ‖W x‖ ≤ C₀) (hW4 : MemLp W 4 volume) {p : ENNReal} (hp1 : 1 ≤ p)
    (hpt : p ≠ ⊤) (hp4 : p.toReal ≤ 4) (hF : MemLp (stationaryVelocityOperator W) p volume)
    {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hw : divergenceCLM w = 0)
    (hweak : WeakProfileEquation (W + representative w))
    {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (weakProfileDensity (W + representative w) φ) volume ∧
      Integrable (fun x ↦ rieszPressure (W + representative w) x * PDE.divergence φ x)
        volume ∧
      ∫ x, weakProfileDensity (W + representative w) φ x =
        ∫ x, rieszPressure (W + representative w) x * PDE.divergence φ x := by
  have : Fact (0 < 3) := ⟨by norm_num⟩
  set U := W + representative w with hUdef
  set P := rieszPressure U with hPdef
  have hUapp (x : ℝ^3) (k : Fin 3) : U x k = W x k + representative w x k := rfl
  have hWk (k : Fin 3) : Continuous (fun x ↦ W x k) := (contDiff_component hW k).continuous
  have hwk (k : Fin 3) : MemLp (fun x ↦ representative w x k) 2 volume := by
    have hi := Lp.memLp (massCLM w k)
    simp only [domainMeasure, Measure.restrict_univ] at hi
    exact hi
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans (hWbd 0)
  have hWbdk (k : Fin 3) (x : ℝ^3) : ‖W x k‖ ≤ C₀ := (PiLp.norm_apply_le (W x) k).trans (hWbd x)
  have hWw (i j : Fin 3) : MemLp (fun x ↦ W x i * representative w x j) 2 volume := by
    refine ((hwk j).const_mul C₀).of_le
      ((hWk i).aestronglyMeasurable.mul (hwk j).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hC₀]
    gcongr
    exact hWbdk i x
  have hww (i j : Fin 3) : MemLp (fun x ↦ representative w x i * representative w x j) 2
      volume := memLp_mul_H1 (w i) (w j)
  have hWW (i j : Fin 3) : MemLp (fun x ↦ W x i * W x j) 2 volume :=
    memLp_two_mul_of_memLp_four hW4 i j
  have hUWW (k j : Fin 3) : MemLp (fun x ↦ U x k * U x j - W x k * W x j) 2 volume := by
    refine (((hWw k j).add (hWw j k)).add (hww k j)).ae_eq
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply, hUapp]
    ring
  have hUU2 (i j : Fin 3) : MemLp (fun x ↦ U x i * U x j) 2 volume := by
    refine ((hUWW i j).add (hWW i j)).ae_eq (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hU (k : Fin 3) : LocallyIntegrable (fun x ↦ U x k) volume :=
    (hWk k).locallyIntegrable.add ((hwk k).locallyIntegrable (by norm_num))
  have hUUl (i j : Fin 3) : LocallyIntegrable (fun x ↦ U x i * U x j) volume :=
    (hUU2 i j).locallyIntegrable (by norm_num)
  have hPl : LocallyIntegrable P volume :=
    (memLp_two_rieszPressure U).locallyIntegrable (by norm_num)
  have hb := locallyIntegrable_profileFirstCoefficient hU hUUl hPl
  have hD := fun (φ : ℝ^3 → ℝ^3) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) ↦
    weakProfileDensity_decomposition hU hUUl hPl hφ hc
  have hsol : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) → ∑ m, profilePairing U P m (fun x ↦ φ x m) = 0 := by
    intro φ hφ hc hdiv
    obtain ⟨-, -, h⟩ := hD φ hφ hc
    rw [← h, (hweak φ ⟨hφ, hc, hdiv⟩).2]
    simp [hdiv]
  have hgrad := fun (χ : ℝ^3 → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) ↦
    sum_profilePairing_partialDeriv_eq_zero hU hUUl hPl
      (fun θ hθ hθc ↦ sum_integral_add_representative_mul_partialDeriv_eq_zero hW hWdiv hw hθ hθc)
      (fun χ hχ hχc ↦ integral_rieszPressure_mul_laplacian hUU2 hχ hχc) hχ hχc
  have hzero (k : Fin 3) {ψ : ℝ^3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hψc : HasCompactSupport ψ) : profilePairing U P k ψ = 0 := by
    set F : ℝ^3 → ℝ := fun x ↦ stationaryVelocityOperator W x k with hFdef
    have hFk : MemLp F p volume := (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).comp_memLp' hF
    have hFl : LocallyIntegrable F volume := hFk.locallyIntegrable hp1
    have hWl : LocallyIntegrable (fun x ↦ W x k) volume := (hWk k).locallyIntegrable
    have hbW := locallyIntegrable_profileFirstCoefficient (U := W) (P := fun _ ↦ 0)
      (fun i ↦ (hWk i).locallyIntegrable) (fun i j ↦ ((hWk i).mul (hWk j)).locallyIntegrable)
      (locallyIntegrable_const 0)
    set A : ℝ^3 → ℝ := fun y ↦ F y + (U y k - W y k) with hAdef
    set B : Fin 3 → ℝ^3 → ℝ := fun j y ↦
      profileFirstCoefficient U P k j y - profileFirstCoefficient W (fun _ ↦ 0) k j y with hBdef
    set C : ℝ^3 → ℝ := fun y ↦ -U y k - -W y k with hCdef
    have hAl : LocallyIntegrable A volume := hFl.add ((hU k).sub hWl)
    have hBl (j : Fin 3) : LocallyIntegrable (B j) volume := (hb k j).sub (hbW k j)
    have hCl : LocallyIntegrable C volume := (hU k).neg.sub hWl.neg
    have hrep : ∀ ψ : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        profilePairing U P k ψ = secondOrderPairing A B C ψ := by
      intro ψ hψ hψc
      have e1 := secondOrderPairing_sub_coefficients (a := fun x ↦ U x k)
        (c := fun x ↦ -U x k) (a' := fun x ↦ W x k) (c' := fun x ↦ -W x k)
        (hU k) (hb k) (hU k).neg hWl (hbW k) hWl.neg hψ hψc
      have e2 := secondOrderPairing_add_zeroth (a := fun y ↦ U y k - W y k) (b := B) (c := C)
        ((hU k).sub hWl) hFl hψ.continuous hψc
      have e3 := profilePairing_background hW hWdiv k hψ hψc
      unfold profilePairing at e3 ⊢
      rw [e2, ← e1, e3]
      ring
    have hT' : ∀ ψ : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        secondOrderPairing A B C (fun y ↦ PDE.laplacian ψ y) = 0 := by
      intro ψ hψ hψc
      rw [← hrep _ (PDE.contDiff_laplacian_coord hψ)
        (HasCompactSupport.coordinate_laplacian hψc)]
      exact profilePairing_laplacian_eq_zero hU hUUl hPl hsol hgrad k hψ hψc
    -- growth of the coefficients
    have hwmeas := (hwk k).aestronglyMeasurable
    have h2 : ((3 : ℕ) : ℝ) * (1 - 1 / (2 : ENNReal).toReal) - 1 ≤ 3 / 2 :=
      three_exponent_le (by norm_num) (by simp) (by norm_num)
    obtain ⟨CF, hCF, gF⟩ := exists_ballGrowth_of_memLp hp1 hFk (three_exponent_le hp1 hpt hp4)
    obtain ⟨Cw, hCw, gw⟩ := exists_ballGrowth_of_memLp (by norm_num) (hwk k) h2
    obtain ⟨CP, hCP, gP⟩ := exists_ballGrowth_of_memLp (by norm_num)
      (memLp_two_rieszPressure U) h2
    have gUW (j : Fin 3) := exists_ballGrowth_of_memLp (by norm_num) (hUWW k j) h2
    choose CUW hCUW gUW' using gUW
    obtain ⟨Mw, hMw, hMwb⟩ := exists_lintegral_ball_le_of_memLp (n := 3) (by norm_num) (hwk k)
    have gX : BallGrowth (fun y : ℝ^3 ↦ ‖y‖ * representative w y k) Mw (3 / 2) := by
      refine ballGrowth_of_norm_le_norm_mul (G := fun y ↦ representative w y k) hMw
        (fun x r hr ↦ ?_) fun y ↦ ?_
      · have h := hMwb x r (by linarith)
        convert h using 3
        norm_num
      · rw [norm_mul, norm_norm]
    have gA : BallGrowth A (CF + Cw) (3 / 2) :=
      ballGrowth_of_norm_le_add gF gw hFk.aestronglyMeasurable hCF hCw fun y ↦ by
        simp only [hAdef, hUapp, add_sub_cancel_left]
        exact norm_add_le _ _
    have gB (j : Fin 3) : BallGrowth (B j) (Mw + (CUW j + CP)) (3 / 2) := by
      have gUP := ballGrowth_of_norm_le_add (gUW' j) gP (hUWW k j).aestronglyMeasurable
        (hCUW j) hCP (K := fun y ↦ (U y k * U y j - W y k * W y j) +
          (if j = k then P y else 0)) fun y ↦ by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        split_ifs <;> simp [hPdef]
      refine ballGrowth_of_norm_le_add gX gUP
        (continuous_norm.aestronglyMeasurable.mul hwmeas) hMw
        (add_nonneg (hCUW j) hCP) fun y ↦ ?_
      have hBy : B j y = (1 / 2) * y j * representative w y k -
          ((U y k * U y j - W y k * W y j) + (if j = k then P y else 0)) := by
        simp only [hBdef, profileFirstCoefficient, hUapp, ite_self]
        ring
      rw [hBy]
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      rw [norm_mul, norm_mul, norm_mul, norm_norm]
      have : ‖(1 / 2 : ℝ)‖ * ‖y j‖ ≤ ‖y‖ := by
        have := PiLp.norm_apply_le y j
        rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        linarith [norm_nonneg (y j)]
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have gC : BallGrowth C (Cw + 0) (3 / 2) := by
      refine ballGrowth_of_norm_le_add gw (BallGrowth.zero 0 (3 / 2)) hwmeas hCw le_rfl
        fun y ↦ ?_
      simp only [hCdef, hUapp]
      simp
    set Cmax := (CF + Cw) + Cw + ∑ j, (Mw + (CUW j + CP)) with hCmax
    have hBnn (j : Fin 3) : 0 ≤ Mw + (CUW j + CP) := add_nonneg hMw (add_nonneg (hCUW j) hCP)
    have hsum0 := Finset.sum_nonneg (s := Finset.univ) fun j _ ↦ hBnn j
    have hCmax0 : 0 ≤ Cmax := by linarith
    have hle1 : CF + Cw ≤ Cmax := by linarith
    have hle2 : Cw + 0 ≤ Cmax := by linarith
    have hle3 (j : Fin 3) : Mw + (CUW j + CP) ≤ Cmax := by
      linarith [Finset.single_le_sum (f := fun j ↦ Mw + (CUW j + CP)) (fun j _ ↦ hBnn j)
        (Finset.mem_univ j)]
    rw [hrep ψ hψ hψc]
    exact secondOrderPairing_eq_zero hAl hBl hCl hT' hCmax0 (by norm_num) (by norm_num)
      (gA.mono_const hle1) (fun j ↦ (gB j).mono_const (hle3 j)) (gC.mono_const hle2) hψ hψc
  obtain ⟨hi1, hi2, h⟩ := hD φ hφ hc
  refine ⟨hi1, hi2, ?_⟩
  have hsum : ∑ k, profilePairing U P k (fun x ↦ φ x k) = 0 :=
    Finset.sum_eq_zero fun k _ ↦ hzero k (contDiff_component hφ k)
      (hasCompactSupport_component hc k)
  linarith

/-- **The pressure of a weak self-similar profile is the Riesz pressure**, with the stationary
operator of the reference field in `L²`, as in `memH2_of_weak_profile`. -/
theorem profile_pressure_eq_riesz_of_memLp {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWdiv : ∀ x, PDE.divergence W x = 0) {C₀ : ℝ} (hWbd : ∀ x, ‖W x‖ ≤ C₀)
    (hW4 : MemLp W 4 volume) (hF : MemLp (stationaryVelocityOperator W) 2 volume)
    {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hw : divergenceCLM w = 0)
    (hweak : WeakProfileEquation (W + representative w))
    {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (weakProfileDensity (W + representative w) φ) volume ∧
      Integrable (fun x ↦ rieszPressure (W + representative w) x * PDE.divergence φ x)
        volume ∧
      ∫ x, weakProfileDensity (W + representative w) φ x =
        ∫ x, rieszPressure (W + representative w) x * PDE.divergence φ x :=
  profile_pressure_eq_riesz_of_memLp_exponent (p := 2) hW hWdiv hWbd hW4 (by norm_num)
    (by simp) (by norm_num) hF hw hweak hφ hc

/-- Hou-Wang-Yang profile form: with the decay `‖DᵏW(x)‖ ≤ Cₖ (1 + ‖x‖)^{-1-k}`, `k ≤ 2`, of
the reference field, the weak profile equation holds with the Riesz pressure against every smooth
compactly supported vector field. The decay puts `W` and its stationary operator in `L⁴`. -/
theorem profile_pressure_eq_riesz {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWdiv : ∀ x, PDE.divergence W x = 0)
    (hdecay : ∀ k ≤ 2, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C / (1 + ‖x‖) ^ (k + 1))
    {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hw : divergenceCLM w = 0)
    (hweak : WeakProfileEquation (W + representative w))
    {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (weakProfileDensity (W + representative w) φ) volume ∧
      Integrable (fun x ↦ rieszPressure (W + representative w) x * PDE.divergence φ x)
        volume ∧
      ∫ x, weakProfileDensity (W + representative w) φ x =
        ∫ x, rieszPressure (W + representative w) x * PDE.divergence φ x := by
  obtain ⟨C0, h0⟩ := hdecay 0 (by norm_num)
  obtain ⟨C1, h1⟩ := hdecay 1 (by norm_num)
  obtain ⟨C2, h2⟩ := hdecay 2 le_rfl
  have hpos (x : ℝ^3) : 0 < 1 + ‖x‖ := by positivity
  have hone (x : ℝ^3) : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hW0 (x : ℝ^3) : ‖W x‖ ≤ C0 / (1 + ‖x‖) := by
    simpa [norm_iteratedFDeriv_zero] using h0 x
  have hC0 : 0 ≤ C0 := by simpa using (norm_nonneg _).trans (hW0 0)
  have hC1 : 0 ≤ C1 := by simpa using (norm_nonneg _).trans (h1 0)
  have hC2 : 0 ≤ C2 := by simpa using (norm_nonneg _).trans (h2 0)
  have hW1 (x : ℝ^3) : ‖fderiv ℝ W x‖ ≤ C1 / (1 + ‖x‖) ^ 2 := by
    simpa [norm_iteratedFDeriv_one] using h1 x
  have hbd (x : ℝ^3) : ‖W x‖ ≤ C0 :=
    (hW0 x).trans (div_le_self hC0 (hone x))
  have h2W : ContDiff ℝ 2 W := hW.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlap (x : ℝ^3) : ‖PDE.laplacian W x‖ ≤ 3 * C2 / (1 + ‖x‖) := by
    have hterm (i : Fin 3) : ‖PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i W y) x‖ ≤
        C2 / (1 + ‖x‖) := by
      rw [PDE.secondPartialDeriv_eq_iteratedFDeriv_apply i i h2W.contDiffAt]
      refine ((iteratedFDeriv ℝ 2 W x).le_opNorm _).trans ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        PiLp.norm_single, norm_one, mul_one]
      exact (h2 x).trans
        (div_le_div_of_nonneg_left hC2 (hpos x) (le_self_pow₀ (hone x) (by norm_num)))
    unfold PDE.laplacian
    calc ‖∑ i : Fin 3, PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i W y) x‖
        ≤ ∑ i : Fin 3, ‖PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i W y) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, C2 / (1 + ‖x‖) := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = 3 * C2 / (1 + ‖x‖) := by simp; ring
  have hF (x : ℝ^3) : ‖stationaryVelocityOperator W x‖ ≤
      ((C0 + C1) / 2 + C1 * C0 + 3 * C2) / (1 + ‖x‖) := by
    have ha : ‖fderiv ℝ W x x‖ ≤ C1 / (1 + ‖x‖) := by
      refine ((fderiv ℝ W x).le_opNorm x).trans ?_
      calc ‖fderiv ℝ W x‖ * ‖x‖ ≤ C1 / (1 + ‖x‖) ^ 2 * (1 + ‖x‖) :=
            mul_le_mul (hW1 x) (by linarith) (norm_nonneg _) (by positivity)
        _ = C1 / (1 + ‖x‖) := by field_simp
    have hb : ‖fderiv ℝ W x (W x)‖ ≤ C1 * C0 / (1 + ‖x‖) := by
      refine ((fderiv ℝ W x).le_opNorm (W x)).trans ?_
      calc ‖fderiv ℝ W x‖ * ‖W x‖ ≤ C1 / (1 + ‖x‖) ^ 2 * C0 :=
            mul_le_mul (hW1 x) (hbd x) (norm_nonneg _) (by positivity)
        _ ≤ C1 / (1 + ‖x‖) * C0 := by
            gcongr
            exact le_self_pow₀ (hone x) (by norm_num)
        _ = C1 * C0 / (1 + ‖x‖) := by ring
    unfold stationaryVelocityOperator PDE.advectiveDerivative
    calc ‖(-(1 / 2) : ℝ) • (W x + fderiv ℝ W x x) + fderiv ℝ W x (W x) - PDE.laplacian W x‖
        ≤ ‖(-(1 / 2) : ℝ) • (W x + fderiv ℝ W x x)‖ + ‖fderiv ℝ W x (W x)‖ +
          ‖PDE.laplacian W x‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (1 / 2) * (C0 / (1 + ‖x‖) + C1 / (1 + ‖x‖)) + C1 * C0 / (1 + ‖x‖) +
          3 * C2 / (1 + ‖x‖) := by
        rw [norm_smul]
        gcongr
        · norm_num
        · exact (norm_add_le _ _).trans (add_le_add (hW0 x) ha)
        · exact hlap x
      _ = _ := by ring
  have hFm : AEStronglyMeasurable (stationaryVelocityOperator W) volume := by
    have hfd : Continuous (fun x ↦ fderiv ℝ W x) := hW.continuous_fderiv (by simp)
    have hc : Continuous fun x ↦ (-(1 / 2) : ℝ) • (W x + fderiv ℝ W x x) +
        fderiv ℝ W x (W x) - PDE.laplacian W x := by
      refine (((continuous_const (y := (-(1 / 2) : ℝ))).smul
        (hW.continuous.add (hfd.clm_apply continuous_id))).add
        (hfd.clm_apply hW.continuous)).sub ?_
      unfold PDE.laplacian
      exact continuous_finsetSum _ fun i _ ↦
        (PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv hW)).continuous
    exact hc.aestronglyMeasurable
  have hL4 {E : Type} [NormedAddCommGroup E] {f : ℝ^3 → E} (hfm : AEStronglyMeasurable f volume)
      {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C / (1 + ‖x‖)) : MemLp f 4 volume :=
    memLp_of_norm_le_mul_one_add_norm_rpow_neg hfm (by norm_num) (by simp) (a := 1)
      (by norm_num) fun x ↦ by rw [Real.rpow_neg_one, ← div_eq_mul_inv]; exact hf x
  exact profile_pressure_eq_riesz_of_memLp_exponent (p := 4) hW hWdiv hbd
    (hL4 hW.continuous.aestronglyMeasurable hW0) (by norm_num) (by simp) (by norm_num)
    (hL4 hFm hF) hw hweak hφ hc

end NavierStokes.Stationary
