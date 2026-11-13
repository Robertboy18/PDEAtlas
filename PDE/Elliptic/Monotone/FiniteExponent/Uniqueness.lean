/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Monotone.FiniteExponent.Existence

/-!
# Uniqueness for strictly monotone fluxes at finite Sobolev exponents

Two weak solutions with the same load agree if their difference belongs to
`Wkp0SpaceOn`, the closure of compactly supported smooth functions. The flux is
strictly monotone almost everywhere and has conjugate power growth. On open sets,
this gives uniqueness in each affine `W^{1,p}_0` boundary class. No boundary
regularity or pointwise trace is required.

The difference is an admissible test function. Hölder gives integrability of
both flux pairings, and subtraction gives a nonnegative integrable function
with zero integral. Strict monotonicity forces equality of the gradients almost
everywhere. Bounded-domain Poincaré then gives equality in the full Sobolev space.

Uniqueness holds for every finite `p ≥ 1` and needs no hemicontinuity or coercive
lower bound. For `1 < p < ∞`, the existence theorem in `FiniteExponent.Existence` supplies
a solution under its additional hypotheses. The resulting `ExistsUnique`
statements allow arbitrary continuous dual loads or conjugate-`Lq` forcing.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal Sobolev Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal}
  [Fact (1 ≤ (p : ℝ≥0∞))]

local notation "μ" => domainMeasure n Ω
local notation "q" => ENNReal.conjExponent (p : ℝ≥0∞)
local notation "V" => W₀^{1,p}(Ω)

/-- Strict flux monotonicity and a nonpositive tested flux difference force
identity in a common Sobolev boundary class. The growth bound supplies the
integrability needed to turn the integral inequality into equality almost
everywhere; bounded-domain Poincaré then identifies the functions. This comparison
also applies when another monotone term contributes to the weak equation. -/
theorem eq_of_strictMonotone_wkpGradientFlux_of_pairing_le
    (hp : 1 ≤ p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hstrict : ∀ᵐ x ∂μ, ∀ z w, z ≠ w →
      0 < inner ℝ (a x z - a x w) (z - w))
    (u v : W^{1,p}(Ω))
    (huv : u - v ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω))
    (hpair : (∫ x, inner ℝ (a x (∇ u x) - a x (∇ v x)) (∇ u x - ∇ v x) ∂μ) ≤ 0) :
    u = v := by
  let w : V := ⟨u - v, huv⟩
  have hgrad : ∇ (w : W^{1,p}(Ω)) =ᵐ[μ] fun x ↦ ∇ u x - ∇ v x := by
    change ∇ (u - v) =ᵐ[μ] fun x ↦ ∇ u x - ∇ v x
    rw [map_sub]
    exact Lp.coeFn_sub (∇ u) (∇ v)
  let F (x : ℝ^n) := inner ℝ (a x (∇ u x) - a x (∇ v x)) (∇ (w : W^{1,p}(Ω)) x)
  have hIu := integrable_inner_wkpGradientFlux ENNReal.coe_ne_top
    a hmeas hh hgrowth u (w : W^{1,p}(Ω))
  have hIv := integrable_inner_wkpGradientFlux ENNReal.coe_ne_top
    a hmeas hh hgrowth v (w : W^{1,p}(Ω))
  have hFi : Integrable F μ := by
    refine (hIu.sub hIv).congr (ae_of_all μ fun x ↦ ?_)
    exact (inner_sub_left (a x (∇ u x)) (a x (∇ v x)) (∇ (w : W^{1,p}(Ω)) x)).symm
  have hFnonneg : ∀ᵐ x ∂μ, 0 ≤ F x := by
    filter_upwards [hstrict, hgrad] with x hx hdx
    change 0 ≤ inner ℝ (a x (∇ u x) - a x (∇ v x)) (∇ (w : W^{1,p}(Ω)) x)
    rw [hdx]
    by_cases heq : ∇ u x = ∇ v x
    · simp only [heq, sub_self, inner_zero_left, le_refl]
    · exact (hx _ _ heq).le
  have hFle : (∫ x, F x ∂μ) ≤ 0 := by
    calc
      (∫ x, F x ∂μ) =
          ∫ x, inner ℝ (a x (∇ u x) - a x (∇ v x)) (∇ u x - ∇ v x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        exact congrArg (fun z ↦ inner ℝ (a x (∇ u x) - a x (∇ v x)) z) hx
      _ ≤ 0 := hpair
  have hFzero : (∫ x, F x ∂μ) = 0 :=
    le_antisymm hFle (integral_nonneg_of_ae hFnonneg)
  have hFae : F =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hFnonneg hFi).mp hFzero
  have hsame : ∇ u =ᵐ[μ] ∇ v := by
    filter_upwards [hstrict, hFae, hgrad] with x hx hzero hdx
    by_contra hne
    change inner ℝ (a x (∇ u x) - a x (∇ v x)) (∇ (w : W^{1,p}(Ω)) x) = 0 at hzero
    rw [hdx] at hzero
    exact (ne_of_gt (hx _ _ hne)) hzero
  have hDw : ∇ (w : W^{1,p}(Ω)) = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hgrad, hsame] with x hdx heq
    change ∇ (w : W^{1,p}(Ω)) x = 0
    rw [hdx, heq, sub_self]
  obtain ⟨_, hP⟩ := exists_norm_le_wkpGradientCLM hn hΩ hp
  have hnorm : ‖w‖ ≤ 0 := by
    simpa only [hDw, norm_zero, mul_zero] using hP w
  have hwzero : w = 0 := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg w))
  have hsub : u - v = 0 := congrArg (fun z : V ↦ (z : W^{1,p}(Ω))) hwzero
  exact sub_eq_zero.mp hsub

/-- Strict monotonicity gives uniqueness for finite-exponent weak solutions
whose difference has zero Sobolev boundary data. The common load need not be
linear or continuous for this comparison: only its equality in the two weak
equations is used.

Power growth derives integrability of the tested fluxes. No uniform strict
monotonicity modulus, hemicontinuity, or coercive pairing lower bound is assumed.
On an open bounded set, the boundary hypothesis says that the two solutions
belong to the same affine `W^{1,p}_0` class. -/
theorem eq_of_strictMonotone_wkpGradientFlux
    (hp : 1 ≤ p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hstrict : ∀ᵐ x ∂μ, ∀ z w, z ≠ w →
      0 < inner ℝ (a x z - a x w) (z - w))
    (ℓ : V → ℝ) (u v : W^{1,p}(Ω))
    (huv : u - v ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω))
    (hu : ∀ z : V, (∫ x, inner ℝ (a x (∇ u x)) (∇ (z : W^{1,p}(Ω)) x) ∂μ) = ℓ z)
    (hv : ∀ z : V, (∫ x, inner ℝ (a x (∇ v x)) (∇ (z : W^{1,p}(Ω)) x) ∂μ) = ℓ z) :
    u = v := by
  let w : V := ⟨u - v, huv⟩
  have hgrad : ∇ (w : W^{1,p}(Ω)) =ᵐ[μ] fun x ↦ ∇ u x - ∇ v x := by
    change ∇ (u - v) =ᵐ[μ] fun x ↦ ∇ u x - ∇ v x
    rw [map_sub]
    exact Lp.coeFn_sub (∇ u) (∇ v)
  apply eq_of_strictMonotone_wkpGradientFlux_of_pairing_le
    hp a hmeas hh hgrowth hn hΩ hstrict u v huv
  have hIu := integrable_inner_wkpGradientFlux ENNReal.coe_ne_top
    a hmeas hh hgrowth u (w : W^{1,p}(Ω))
  have hIv := integrable_inner_wkpGradientFlux ENNReal.coe_ne_top
    a hmeas hh hgrowth v (w : W^{1,p}(Ω))
  have heq : (∫ x, inner ℝ (a x (∇ u x) - a x (∇ v x)) (∇ u x - ∇ v x) ∂μ) = 0 := by
    calc
      _ = ∫ x, inner ℝ (a x (∇ u x) - a x (∇ v x)) (∇ (w : W^{1,p}(Ω)) x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        rw [hx]
      _ = 0 := by
        simp only [inner_sub_left]
        rw [integral_sub hIu hIv, hu w, hv w, sub_self]
  exact heq.le

/-- A strictly monotone flux with conjugate power growth, right hemicontinuity,
and a positive `p`-power pairing lower bound has exactly one zero-boundary weak
solution for each continuous dual load when `1 < p < ∞`.

Browder–Minty gives existence from the coefficient assumptions. Pointwise
strictness and bounded-domain Poincaré give uniqueness: equal loads force
the gradients to agree, and the zero boundary data determine the solution. -/
theorem existsUnique_weak_solution_of_strictMonotone_wkpGradientFlux
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hstrict : ∀ᵐ x ∂μ, ∀ z w, z ≠ w →
      0 < inner ℝ (a x z - a x w) (z - w))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v : V,
      (∫ x, inner ℝ (a x (∇ (u : W^{1,p}(Ω)) x)) (∇ (v : W^{1,p}(Ω)) x) ∂μ) = ℓ v := by
  have hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w) := by
    filter_upwards [hstrict] with x hx
    intro z w
    by_cases hzw : z = w
    · simp only [hzw, sub_self, inner_zero_left, le_refl]
    · exact (hx z w hzw).le
  obtain ⟨u, hu⟩ := exists_weak_solution_of_monotone_wkpGradientFlux
    hp a hmeas hh hgrowth hn hΩ hmono hhemi hc hb hlower ℓ
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  apply Subtype.ext
  exact eq_of_strictMonotone_wkpGradientFlux hp.le a hmeas hh hgrowth hn hΩ
    hstrict (fun z ↦ ℓ z) (v : W^{1,p}(Ω)) (u : W^{1,p}(Ω))
    ((wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
      (Ω := Ω)).toSubmodule.sub_mem v.property u.property) hv hu

/-- Forcing in the conjugate `Lq` space gives exactly one weak solution of
`-div a(x, Du) = f` with zero Sobolev boundary data, under strict flux
monotonicity and the finite-exponent existence hypotheses.

The right-hand side uses the given representative of `f`. Hölder derives
the continuous load in the existence theorem, and uniqueness uses the same
integral load for both solutions. -/
theorem existsUnique_weak_solution_of_strictMonotone_wkpGradientFlux_of_memLp
    (hp : 1 < p) (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖a x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1))
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (hstrict : ∀ᵐ x ∂μ, ∀ z w, z ≠ w →
      0 < inner ℝ (a x z - a x w) (z - w))
    (hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ (p : ℝ) - b x ≤ inner ℝ (a x z) z)
    {f : ℝ^n → ℝ} (hf : MemLp f q μ) :
    ∃! u : V, ∀ v : V,
      (∫ x, inner ℝ (a x (∇ (u : W^{1,p}(Ω)) x)) (∇ (v : W^{1,p}(Ω)) x) ∂μ) =
        ∫ x, f x * wkpBaseCoordinateCLM (v : W^{1,p}(Ω)) x ∂μ := by
  have hmono : ∀ᵐ x ∂μ, ∀ z w, 0 ≤ inner ℝ (a x z - a x w) (z - w) := by
    filter_upwards [hstrict] with x hx
    intro z w
    by_cases hzw : z = w
    · simp only [hzw, sub_self, inner_zero_left, le_refl]
    · exact (hx z w hzw).le
  obtain ⟨u, hu⟩ := exists_weak_solution_of_monotone_wkpGradientFlux_of_memLp
    hp a hmeas hh hgrowth hn hΩ hmono hhemi hc hb hlower hf
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  apply Subtype.ext
  exact eq_of_strictMonotone_wkpGradientFlux hp.le a hmeas hh hgrowth hn hΩ
    hstrict (fun z : V ↦ ∫ x, f x * wkpBaseCoordinateCLM (z : W^{1,p}(Ω)) x ∂μ)
    (v : W^{1,p}(Ω)) (u : W^{1,p}(Ω))
    ((wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
      (Ω := Ω)).toSubmodule.sub_mem v.property u.property) hv hu

end SobolevSpace.GraphSpace
