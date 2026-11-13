/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AveragedFDeriv
public import PDE.Analysis.Calculus.ImplicitRay
public import PDE.Analysis.Calculus.LocalSpectralFrame
public import PDE.Hyperbolic.ConservationLaw.System.Basic
public import PDE.LinearAlgebra.Eigenbasis
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Shock curves with a varying left state

The averaged Jacobian is jointly differentiable in its endpoints. A single
operator eigenbranch and a parameterized implicit function therefore construct
shock curves jointly in strength and left state. Along zero strength their full
derivative sends `(a,h)` to `h + a r(q)`.

Differentiating the same eigenvalue branch on the averaged and the ordinary
Jacobian gives the factor one-half in the shock-speed derivative.

This is the construction in the proof of Theorem 2 of Evans, §11.2.3, steps 1-5, with the left
state as a parameter, and the factor one-half is the expansion (iii) there. Section 11.2.4 uses
both facts to assemble the wave curves `Tₖ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, Theorem 2 and its proof, equations (15)-(31);
  §11.2.4, definition of the wave curves `Tₖ`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter
open scoped ContDiff Topology

/-- A `C²` flux strictly hyperbolic at one state has joint local shock families.
The ordered eigenfields, curves, speeds, derivative matching data and half-factor
are constructed from the flux. All nearby left states share one neighborhood. -/
theorem exists_joint_shock_family {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux) {q₀ : ℝ^m}
    (hhyper : IsStrictlyHyperbolicAt flux q₀) :
    ∃ r : Fin m → ℝ^m → ℝ^m, ∃ eig : Fin m → ℝ^m → ℝ,
    ∃ S : Fin m → ℝ × ℝ^m → ℝ^m, ∃ speed : Fin m → ℝ × ℝ^m → ℝ,
      (∀ k, ContDiffAt ℝ 1 (r k) q₀ ∧ ContDiffAt ℝ 1 (eig k) q₀ ∧
        ContDiffAt ℝ 1 (S k) (0, q₀) ∧ ContDiffAt ℝ 1 (speed k) (0, q₀)) ∧
      (∀ᶠ q in 𝓝 q₀, StrictMono (fun k ↦ eig k q) ∧
        (∀ k, fderiv ℝ flux q (r k q) = eig k q • r k q) ∧
        ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k, b k = r k q) ∧
      (∀ᶠ q in 𝓝 q₀, ∀ k,
        S k (0, q) = q ∧ speed k (0, q) = eig k q ∧
        HasFDerivAt (S k)
          (ContinuousLinearMap.snd ℝ ℝ (ℝ^m) +
            (ContinuousLinearMap.fst ℝ ℝ (ℝ^m)).smulRight (r k q)) (0, q) ∧
        HasDerivAt (fun s ↦ speed k (s, q))
          ((1 / 2 : ℝ) * fderiv ℝ (eig k) q (r k q)) 0) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k,
        RankineHugoniot flux p.2 (S k p) (speed k p) ∧
        (p.1 ≠ 0 → S k p ≠ p.2)) ∧
      (∀ k, 0 ≤ fderiv ℝ (eig k) q₀ (r k q₀)) := by
  classical
  obtain ⟨_hdiff, b₀, a₀, hinj, heigen₀⟩ := hhyper
  obtain ⟨b, a, horder, heigen⟩ :=
    b₀.exists_ordered_eigenbasis (fderiv ℝ flux q₀).toLinearMap a₀ hinj
      (fun k ↦ (heigen₀ k).apply_eq_smul)
  obtain ⟨ψ, _hψbase, W, hW, hAW, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux q₀) a heigen horder
  let B : ℝ^m × ℝ^m → ℝ^m →L[ℝ] ℝ^m := fun z ↦ PDE.Analysis.averagedFDeriv flux z.1 z.2
  have hB : ContDiff ℝ 1 B := PDE.Analysis.contDiff_averagedFDeriv_joint (n := 1) hflux
  have hB0 : B (q₀, q₀) = fderiv ℝ flux q₀ := PDE.Analysis.averagedFDeriv_self flux q₀
  have hD : ContDiff ℝ 1 (fderiv ℝ flux) := hflux.fderiv_right le_rfl
  let eig : Fin m → ℝ^m → ℝ := fun k q ↦ (ψ k (fderiv ℝ flux q)).2
  let r₀ : Fin m → ℝ^m → ℝ^m := fun k q ↦ (ψ k (fderiv ℝ flux q)).1
  let η : Fin m → ℝ := fun k ↦ if 0 ≤ fderiv ℝ (eig k) q₀ (r₀ k q₀) then 1 else -1
  have hη (k : Fin m) : η k ≠ 0 := by
    dsimp [η]
    split_ifs <;> norm_num
  let r : Fin m → ℝ^m → ℝ^m := fun k q ↦ η k • r₀ k q
  have hψ (k : Fin m) : ContDiffAt ℝ 1 (ψ k) (fderiv ℝ flux q₀) :=
    ((hframe _ hAW).2.1 k).1.of_le (by simp)
  have hψB (k : Fin m) : ContDiffAt ℝ 1 (fun z ↦ ψ k (B z)) (q₀, q₀) :=
    (show ContDiffAt ℝ 1 (ψ k) (B (q₀, q₀)) by simpa only [hB0] using hψ k).comp (q₀, q₀)
      hB.contDiffAt
  have hbranches (k : Fin m) :=
    PDE.Analysis.exists_implicit_ray_family ((hψB k).fst.const_smul (η k))
  choose S hS0 hS hzero hray _hunique using hbranches
  let speed : Fin m → ℝ × ℝ^m → ℝ := fun k p ↦ (ψ k (B (p.2, S k p))).2
  have hspeed (k : Fin m) : ContDiffAt ℝ 1 (speed k) (0, q₀) := by
    have hp : ContDiffAt ℝ 1 (fun z ↦ ψ k (B z)) (q₀, S k (0, q₀)) := by
      simpa only [hS0 k] using hψB k
    exact (hp.comp (0, q₀) (contDiffAt_snd.prodMk (hS k))).snd
  have hDW : ∀ᶠ q in 𝓝 q₀, fderiv ℝ flux q ∈ W := hD.continuous.continuousAt (hW.mem_nhds hAW)
  refine ⟨r, eig, S, speed, fun k ↦ ⟨((hψ k).comp q₀ hD.contDiffAt).fst.const_smul (η k),
    ((hψ k).comp q₀ hD.contDiffAt).snd, hS k, hspeed k⟩, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hDW] with q hq
    obtain ⟨hord, hvec, hb⟩ := hframe _ hq
    refine ⟨hord, fun k ↦ ?_, ?_⟩
    · change fderiv ℝ flux q (η k • (ψ k (fderiv ℝ flux q)).1) =
        (ψ k (fderiv ℝ flux q)).2 • (η k • (ψ k (fderiv ℝ flux q)).1)
      have heig : fderiv ℝ flux q (ψ k (fderiv ℝ flux q)).1 =
          (ψ k (fderiv ℝ flux q)).2 • (ψ k (fderiv ℝ flux q)).1 := (hvec k).2.1.apply_eq_smul
      rw [map_smul, heig, smul_comm]
    · obtain ⟨bq, hbq⟩ := hb
      exact ⟨bq.unitsSMul (fun k ↦ Units.mk0 (η k) (hη k)), fun k ↦ by
        simp only [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, hbq k, r, r₀]⟩
  · filter_upwards [hDW, Filter.eventually_all.mpr hzero] with q hq hzeroq k
    obtain ⟨hSq, hdS⟩ := hzeroq k
    have hrdiag : η k • (ψ k (B (q, q))).1 = r k q := by
      simp only [B, PDE.Analysis.averagedFDeriv_self, r, r₀]
    have hdS' : HasFDerivAt (S k) (ContinuousLinearMap.snd ℝ ℝ (ℝ^m) +
          (ContinuousLinearMap.fst ℝ ℝ (ℝ^m)).smulRight (r k q)) (0, q) := by
      simpa only [hrdiag] using hdS
    have htan : HasDerivAt (fun s : ℝ ↦ S k (s, q)) (r k q) 0 := by
      simpa [Function.comp_def] using hdS'.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) q))
    have ha : DifferentiableAt ℝ (fun A ↦ (ψ k A).2) (fderiv ℝ flux q) :=
      (((hframe _ hq).2.1 k).1.of_le (by simp : (1 : ℕ∞ω) ≤ ω)).snd.differentiableAt one_ne_zero
    have havg' : HasFDerivAt (fun z ↦ (ψ k (B (q, z))).2)
        ((1 / 2 : ℝ) • fderiv ℝ (eig k) q) (S k (0, q)) := by
      simpa only [hSq, eig, B] using PDE.Analysis.hasFDerivAt_comp_averagedFDeriv_self hflux ha
    refine ⟨hSq, ?_, hdS', ?_⟩
    · simp only [speed, hSq, B, PDE.Analysis.averagedFDeriv_self, eig]
    · simpa only [Function.comp_def, smul_apply, smul_eq_mul, speed] using
        havg'.comp_hasDerivAt (0 : ℝ) htan
  · have hnear (k : Fin m) : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), B (p.2, S k p) ∈ W := by
      have ht : Tendsto (fun p : ℝ × ℝ^m ↦ B (p.2, S k p))
          (𝓝 (0, q₀)) (𝓝 (fderiv ℝ flux q₀)) := by
        simpa only [ContinuousAt, Function.comp_def, hS0 k, hB0] using
          hB.continuous.continuousAt.comp (continuousAt_snd.prodMk (hS k).continuousAt)
      exact ht (hW.mem_nhds hAW)
    filter_upwards [Filter.eventually_all.mpr hnear, Filter.eventually_all.mpr hray]
      with p hp hrayp k
    have hvec := ((hframe _ (hp k)).2.1 k).2.1
    have hinc := PDE.Analysis.averagedFDeriv_apply_sub
      (hflux.of_le (by simp)) p.2 (S k p)
    have hrayk := hrayp k
    refine ⟨?_, ?_⟩
    · change flux (S k p) - flux p.2 = (ψ k (B (p.2, S k p))).2 • (S k p - p.2)
      rw [← hinc]
      change B (p.2, S k p) (S k p - p.2) = _
      have heigen' : B (p.2, S k p) (η k • (ψ k (B (p.2, S k p))).1) =
            (ψ k (B (p.2, S k p))).2 • (η k • (ψ k (B (p.2, S k p))).1) := by
        have hv : B (p.2, S k p) (ψ k (B (p.2, S k p))).1 =
            (ψ k (B (p.2, S k p))).2 • (ψ k (B (p.2, S k p))).1 := hvec.apply_eq_smul
        rw [map_smul, hv, smul_comm]
      rw [hrayk, map_smul, heigen', smul_comm]
    · exact fun hs heq ↦ (smul_ne_zero hs (smul_ne_zero (hη k) hvec.2))
        (by rw [← hrayk, heq, sub_self])
  · intro k
    change 0 ≤ fderiv ℝ (eig k) q₀ (η k • r₀ k q₀)
    rw [map_smul]
    dsimp [η]
    split_ifs with hk
    · simpa using hk
    · simpa using (neg_nonneg.mpr (le_of_not_ge hk))

end PDE.Hyperbolic.ConservationLaw.System
