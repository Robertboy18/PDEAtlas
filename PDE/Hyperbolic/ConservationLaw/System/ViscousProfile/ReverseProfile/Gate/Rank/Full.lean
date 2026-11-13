/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder

import Mathlib.Analysis.Calculus.FDeriv.WithLp
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Rank.Nonparallel
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Rank.TangentPatch
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Variation
import PDE.LinearAlgebra.Determinant.Basis
import CAS.ExactTactic

/-!
# Two nonzero gate determinants for the selected full trajectory

The selected terminal residual and retained reference clock give an open patch
with three nonzero tangent coefficients. The full-flow speed variation
cannot remain parallel to that tangent on the patch. At one such time, the
normalized spectral basis therefore gives two distinct nonzero
determinants, with rows tangent, eigenvector, and speed variation in that order.
The conclusion also retains the three nonzero coefficients of that same tangent
in those same normalized eigenvectors.

The gate, coefficient, full family, and speed variation stay fixed throughout.
This is a zero-delta conclusion.
-/

@[expose] public noncomputable section

open Set PDE.Analysis PDE.Analysis.Evolution
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Assemble the tangent patch, speed-variation equations and
normalized spectral basis for the same selected full family. The nonzero tangent
coefficients and their exact expansion are retained at the selected time.

The reference and residual inputs are those of the full tangent-patch theorem.
The additional inputs are the supplied smooth full flow and its ODE on
one open parameter neighborhood. -/
theorem exists_prescribed_clock_full_gate_det_ne_zero {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L : ℝ × ℝ → ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {cStar : Fin 3 → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} {U0 : Set (ℝ × ℝ)} {V0 : Set (Fin 3 → ℝ)}
    {X Z tPlus : ℝ → ℝ} {A B T τ0 H : ℝ} (hF : Continuous F) (hb : ContDiff ℝ ∞ b)
    (hΨ : ContDiff ℝ ∞ Ψ) (hN : IsOpen N) (hbase : ((0, cStar), (0, 0)) ∈ N)
    (hode : ∀ θ ∈ N, ∀ t ∈ Icc (0 : ℝ) H, HasDerivAt (fun s ↦ Ψ (s, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (t, θ)) - θ.2.1 •
      Ψ (t, θ)) t)
    (hbsupp : tsupport (fun y ↦ b (cStar, y)) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (h0U0 : (0, 0) ∈ U0) (hcV0 : cStar ∈ V0) (hLbase : L (0, 0) = τ0)
    (hzbase : 0 < (F (L (0, 0), (0, 0))).2)
    (href : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc (-1 : ℝ) (τ0 + 1)))
    (hTτ : T < τ0) (hτH : τ0 < H) (hup : ∀ t ∈ Icc 1 T, HasDerivAt X (MiddleClock.g (X t) + 1) t)
    (hgate : ∀ y ∈ Icc (205 : ℝ) (2051 / 10), tPlus y ∈ Ioo 1 T ∧ X (tPlus y) = y)
    (hearly : ∀ t ∈ Icc 0 (tPlus (41001 / 200)), X t < 20501 / 100)
    (hZ : ∀ t ∈ Icc 1 T, HasDerivAt Z (2 * Z t) t) (hZlower : ∀ t ∈ Icc 1 T, 1 + t ≤ Z t)
    (hZsq : ∀ t ∈ Ioo 1 T, Z t ^ 2 < A ^ 2) (hAB : A ^ 2 < B ^ 2) :
    let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
      !₂[(F (t, p)).2 * scalarLinearSolution (fun _ : ℝ ↦ 4)
          (fun s ↦ b (c, (F (s, p)).1)) 0 0 t,
        (F (t, p)).1, (F (t, p)).2]
    let x0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ q u.2 u.1 (L u.2) 0
    let z0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ q u.2 u.1 (L u.2) 2
    let ρ0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ x0 u / z0 u
    let Gold : (Fin 3 → ℝ) → Fin 3 → ℝ := fun c ↦
      ![ρ0 (c, (0, 0)) - 1,
        deriv (fun a : ℝ ↦ ρ0 (c, (0, a))) 0,
        z0 (c, (0, 0)) * deriv (fun μ : ℝ ↦ ρ0 (c, (μ, 0))) 0 +
          2 * deriv (fun μ : ℝ ↦ z0 (c, (μ, 0))) 0 +
          2000000 * deriv (fun a : ℝ ↦ z0 (c, (0, a))) 0]
    Gold cStar = 0 →
    (∀ p ∈ U0, ∀ c ∈ V0,
      EqOn (fun t ↦ Ψ (t, ((0, c), p))) (q p c) (Icc (0 : ℝ) H)) →
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, ((0, cStar), (0, 0)))
    let v : ℝ → ℝ^3 := deriv γ
    let W : ℝ → ℝ^3 := prescribedClockFullVariation Ψ (0, cStar) (1, 0)
    let r : ℝ → Fin 3 → ℝ^3 := fun t ↦
      GatedFlux.rightEigenvector (fastLogCosh 0) MiddleClock.g cutoff
        (clockFeedback A B) (fun y ↦ b (cStar, y)) (γ t)
    ∃ t ∈ Ioo (0 : ℝ) H,
      t ∈ Ioo (tPlus (41001 / 200)) (tPlus (2051 / 10)) ∧
      γ t 1 ∈ Ioo (205 : ℝ) (2051 / 10) ∧ 2 < γ t 2 ∧ (γ t 2) ^ 2 < A ^ 2 ∧
      ∃ i j : Fin 3, i ≠ j ∧
        Matrix.det ![⇑(v t), ⇑(r t i), ⇑(W t)] ≠ 0 ∧
        Matrix.det ![⇑(v t), ⇑(r t j), ⇑(W t)] ≠ 0 ∧
        ∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ v t = ∑ k, a k • r t k := by
  intro q x0 z0 ρ0 Gold hGoldzero hcommon γ v W r
  obtain ⟨_, hsupp, l, u, hlu, hIH, hbranch, hpatch⟩ := exists_prescribed_clock_full_tangent_patch
      (F := F) (L := L) (b := b) (cStar := cStar) (Ψ := Ψ)
      (U0 := U0) (V0 := V0) (X := X) (Z := Z) (tPlus := tPlus)
      (A := A) (B := B) (T := T) (τ0 := τ0) (H := H)
      hF hb hbsupp h0U0 hcV0 hLbase hzbase href hTτ hτH hup hgate hearly
      hZ hZlower hZsq hAB hGoldzero hcommon
  have hproj := prescribed_clock_upward_gate_variation
    (I := Ioo l u) (c := cStar) (b := b) (Ψ := Ψ) (N := N) hAB hb hΨ hN hbase hode hsupp
    (fun t ht ↦ ⟨(hIH ht).1.le, (hIH ht).2.le⟩) (fun t ht ↦ (hpatch t ht).1)
    (fun t ht ↦ (hpatch t ht).2.1) (fun t ht ↦ (hpatch t ht).2.2.1)
  have hγ (t : ℝ) (ht : t ∈ Ioo l u) : HasDerivAt γ (v t) t := by
    obtain ⟨_, _, _, _, _, hd, _⟩ := hpatch t ht
    exact hd.congr_deriv hd.deriv.symm
  have hvy (t : ℝ) (ht : t ∈ Ioo l u) : v t 1 = MiddleClock.g (γ t 1) + 1 :=
    ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ t) 1).comp_hasDerivAt t (hγ t ht)).unique (hproj t ht).1
  have hvz (t : ℝ) (ht : t ∈ Ioo l u) : v t 2 = 2 * γ t 2 :=
    ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ t) 2).comp_hasDerivAt t
      (hγ t ht)).unique (hproj t ht).2.1
  obtain ⟨t, ht, hnonparallel, _⟩ := exists_prescribed_clock_gate_variation_nonparallel
    (γ := γ) (v := v) (W := W) isOpen_Ioo (nonempty_Ioo.mpr hlu)
    hγ hvy hvz (fun s hs ↦ (hproj s hs).2.2.1)
    (fun s hs ↦ (hproj s hs).2.2.2) (fun s hs ↦ (hpatch s hs).1)
    (fun s hs ↦ two_pos.trans (hpatch s hs).2.1)
  obtain ⟨hy, hz, hzA, _, ha, hd, hdecomp⟩ := hpatch t ht
  -- The scalar gap theorems apply at delta zero without a positive-delta premise.
  have hk : Differentiable ℝ (fastLogCosh 0) := (contDiff_fastLogCosh 0).differentiable (by simp)
  have hg : Differentiable ℝ MiddleClock.g := MiddleClock.contDiff_g.differentiable (by simp)
  have hC : Differentiable ℝ cutoff := contDiff_cutoff.differentiable (by simp)
  have hφ : Differentiable ℝ (clockFeedback A B) :=
    (contDiff_clockFeedback A B).differentiable (by simp)
  have hb' : Differentiable ℝ (fun y ↦ b (cStar, y)) :=
    (hb.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hleft : ∀ s : ℝ, s ≤ 100 → cutoff s = 1 := fun _ ↦ cutoff_of_le
  have hright : ∀ s : ℝ, 205 ≤ s → cutoff s = 0 := fun _ ↦ cutoff_of_ge
  have hCslope (s : ℝ) : -(1 / 100 : ℝ) ≤ deriv cutoff s ∧ deriv cutoff s ≤ 0 :=
    ⟨by simpa only [neg_div] using neg_one_div_le_deriv_cutoff s, deriv_cutoff_nonpos s⟩
  have hδ : |(0 : ℝ)| < 1 / 4 := by norm_num
  have hkslope : ∀ s : ℝ, 7 / 4 < deriv (fastLogCosh 0) s := seven_fourths_lt_deriv_fastLogCosh hδ
  have hlow : -deriv (fastLogCosh 0) (γ t 0) <
      GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B) (γ t) :=
    sub_pos.mp ((by norm_num : (0 : ℝ) < 5 / 4).trans
      (GatedFlux.five_fourths_lt_left_gap (a := 100) (by norm_num)
        hleft MiddleClock.abs_deriv_g_le hCslope (clockFeedback_mem_Icc A B) hkslope (γ t)))
  have hhigh : GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B) (γ t) <
      deriv (fastLogCosh 0) (γ t 2) :=
    sub_pos.mp ((by norm_num : (0 : ℝ) < 5 / 4).trans
      (GatedFlux.five_fourths_lt_right_gap (a := 100) (by norm_num)
        hleft MiddleClock.abs_deriv_g_le hCslope (clockFeedback_mem_Icc A B) hkslope (γ t)))
  have h100 : (0 : ℝ) < 100 := by norm_num
  have h100205 : (100 : ℝ) < 205 := by norm_num
  let R : Module.Basis (Fin 3) ℝ (ℝ^3) :=
    GatedFlux.eigenbasis hk hg hC hφ hb' h100 h100205 hleft hright hsupp hlow hhigh
  have hR (i : Fin 3) : R i = GatedFlux.rightEigenvector (fastLogCosh 0) MiddleClock.g cutoff
        (clockFeedback A B) (fun y ↦ b (cStar, y)) (γ t) i :=
    GatedFlux.eigenbasis_apply hk hg hC hφ hb' h100 h100205 hleft hright hsupp hlow hhigh i
  obtain ⟨i, j, hij, hi, hj⟩ := exists_distinct_det_ne_zero_of_basis R _ ha
      (by simpa only [hR] using hd.deriv.trans hdecomp) hnonparallel
  exact ⟨t, hIH ht, hbranch ht, hy, hz, hzA, i, j, hij, by simpa only [hR, r] using hi,
    by simpa only [hR, r] using hj, _, ha, by simpa only [r] using hd.deriv.trans hdecomp⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
