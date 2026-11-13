/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Rank.TangentComponent
import CAS.ExactTactic

/-!
# A nonzero tangent-component patch of the selected full trajectory

The selected terminal residual and its positive fast coordinate imply terminal
scalar value one for the same signed gate. The retained clock reference then
supplies the hypotheses of the gate tangent-component theorem on the base slice
of the speed family. Common closed-slab agreement transfers its open patch to
the full trajectory, with the strict margins needed by the upward variation rule.

The residual and agreement are conclusions of the selected full-terminal
construction; the clock itinerary and fast margins are hypotheses.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis PDE.Analysis.Evolution
open scoped BigOperators ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Consume the selected residual zero and the common candidate agreement to
obtain a full-trajectory patch with three nonzero tangent coefficients.

The candidate, terminal residual, and full family use the same `F`, `L`, `b`,
and `cStar`. Reference agreement is required only on its original closed slab.
The patch lies strictly inside the full time slab and the upward passage, so
closed-slab equality suffices to transfer ordinary derivatives. -/
theorem exists_prescribed_clock_full_tangent_patch {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L : ℝ × ℝ → ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {cStar : Fin 3 → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {U0 : Set (ℝ × ℝ)} {V0 : Set (Fin 3 → ℝ)} {X Z tPlus : ℝ → ℝ} {A B T τ0 H : ℝ}
    (hF : Continuous F) (hb : ContDiff ℝ ∞ b)
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
    let X0 : ℝ → ℝ := fun t ↦ (F (t, (0, 0))).1
    let Z0 : ℝ → ℝ := fun t ↦ (F (t, (0, 0))).2
    let ρ := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (cStar, X0 s)) 0 0
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, ((0, cStar), (0, 0)))
    let a : ℝ → Fin 3 → ℝ := fun t ↦
      ![Z0 t * ((b (cStar, X0 t) - 4 * ρ t) / 2 -
          deriv (fun y ↦ b (cStar, y)) (X0 t) * (MiddleClock.g (X0 t) + 1) /
            (deriv MiddleClock.g (X0 t) + 2)),
        MiddleClock.g (X0 t) + 1, 2 * Z0 t]
    ρ τ0 = 1 ∧
      tsupport (fun y ↦ b (cStar, y)) ⊆ Ioo (205 : ℝ) (2051 / 10) ∧
      ∃ l u : ℝ, l < u ∧ Ioo l u ⊆ Ioo (0 : ℝ) H ∧
        Ioo l u ⊆ Ioo (tPlus (41001 / 200)) (tPlus (2051 / 10)) ∧
        ∀ t ∈ Ioo l u,
          γ t 1 ∈ Ioo (205 : ℝ) (2051 / 10) ∧ 2 < γ t 2 ∧ (γ t 2) ^ 2 < A ^ 2 ∧
          a t 0 / γ t 2 = deriv ρ t / 2 -
            deriv (fun s ↦ b (cStar, X0 s)) t / (deriv MiddleClock.g (γ t 1) + 2) ∧
          (∀ i : Fin 3, a t i ≠ 0) ∧
          HasDerivAt γ
            (concreteGatedFlux 0 (clockFeedback A B) (fun y ↦ b (cStar, y)) (γ t)) t ∧
          concreteGatedFlux 0 (clockFeedback A B) (fun y ↦ b (cStar, y)) (γ t) =
            ∑ i : Fin 3, a t i •
              GatedFlux.rightEigenvector (fastLogCosh 0) MiddleClock.g cutoff
                (clockFeedback A B) (fun y ↦ b (cStar, y)) (γ t) i := by
  intro q x0 z0 ρ0 Gold hGoldzero hcommon X0 Z0 ρ γ a
  have hpair : Continuous (fun t : ℝ ↦ F (t, (0, 0))) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hbc : ContDiff ℝ ∞ (fun y : ℝ ↦ b (cStar, y)) := hb.comp (contDiff_const.prodMk contDiff_id)
  -- This is the first coordinate of the selected residual, with its denominator.
  have hmatch : ρ τ0 = 1 := by
    have hfirst := congrArg (fun v : Fin 3 → ℝ ↦ v 0) hGoldzero
    change Z0 (L (0, 0)) * ρ (L (0, 0)) / Z0 (L (0, 0)) - 1 = 0 at hfirst
    have hz : Z0 (L (0, 0)) ≠ 0 := hzbase.ne'
    rw [← hLbase]
    simpa only [mul_div_cancel_left₀ _ hz] using sub_eq_zero.mp hfirst
  have hrefX : EqOn X0 X (Icc (-1 : ℝ) (τ0 + 1)) := fun t ht ↦ congrArg Prod.fst (href ht)
  have hrefZ : EqOn Z0 Z (Icc (-1 : ℝ) (τ0 + 1)) := fun t ht ↦ congrArg Prod.snd (href ht)
  have hwide (t : ℝ) (ht : t ∈ Icc 1 T) : t ∈ Ioo (-1 : ℝ) (τ0 + 1) :=
    ⟨(by norm_num : (-1 : ℝ) < 1).trans_le ht.1,
      ht.2.trans_lt (hTτ.trans (lt_add_of_pos_right τ0 zero_lt_one))⟩
  have hrefNear (t : ℝ) (ht : t ∈ Icc 1 T) :
      (fun s ↦ F (s, (0, 0))) =ᶠ[𝓝 t] (fun s ↦ (X s, Z s)) := by
    filter_upwards [Ioo_mem_nhds (hwide t ht).1 (hwide t ht).2] with s hs
    exact href ⟨hs.1.le, hs.2.le⟩
  have hup0 (t : ℝ) (ht : t ∈ Icc 1 T) :
      HasDerivAt X0 (MiddleClock.g (X0 t) + 1) t := by
    rw [hrefX ⟨(hwide t ht).1.le, (hwide t ht).2.le⟩]
    exact (hup t ht).congr_of_eventuallyEq ((hrefNear t ht).mono fun s hs ↦ congrArg Prod.fst hs)
  have hgate0 (y : ℝ) (hy : y ∈ Icc (205 : ℝ) (2051 / 10)) : tPlus y ∈ Ioo 1 T ∧ X0 (tPlus y) = y :=
    ⟨(hgate y hy).1, (hrefX ⟨(hwide _ ⟨(hgate y hy).1.1.le, (hgate y hy).1.2.le⟩).1.le,
      (hwide _ ⟨(hgate y hy).1.1.le, (hgate y hy).1.2.le⟩).2.le⟩).trans (hgate y hy).2⟩
  have hr : tPlus (41001 / 200) ∈ Ioo 1 T := (hgate _ (by constructor <;> norm_num)).1
  have he : tPlus (2051 / 10) ∈ Ioo 1 T := (hgate _ ⟨by norm_num, le_rfl⟩).1
  have hearly0 (t : ℝ) (ht : t ∈ Icc 0 (tPlus (41001 / 200))) : X0 t < 20501 / 100 := by
    rw [hrefX ⟨by linarith [ht.1], by linarith [ht.2, hr.2]⟩]
    exact hearly t ht
  have hZ0 (t : ℝ) (ht : t ∈ Icc 1 T) : HasDerivAt Z0 (2 * Z0 t) t := by
    rw [hrefZ ⟨(hwide t ht).1.le, (hwide t ht).2.le⟩]
    exact (hZ t ht).congr_of_eventuallyEq ((hrefNear t ht).mono fun s hs ↦ congrArg Prod.snd hs)
  have hZlower0 (t : ℝ) (ht : t ∈ Icc 1 T) : 1 + t ≤ Z0 t := by
    rw [hrefZ ⟨(hwide t ht).1.le, (hwide t ht).2.le⟩]
    exact hZlower t ht
  have hZsq0 (t : ℝ) (ht : t ∈ Ioo 1 T) : Z0 t ^ 2 < A ^ 2 := by
    have hw := hwide t ⟨ht.1.le, ht.2.le⟩
    rw [hrefZ ⟨hw.1.le, hw.2.le⟩]
    exact hZsq t ht
  obtain ⟨l, u, hlu, hbranch, hpatch⟩ := exists_prescribed_clock_gate_tangent_components_ne_zero
      hpair.fst hbc hbsupp hup0 hgate0 hearly0 hZ0 hZlower0 hZsq0 hAB hmatch
  have hinside (t : ℝ) (ht : t ∈ Ioo l u) : t ∈ Ioo 1 T :=
    ⟨hr.1.trans (hbranch ht).1, (hbranch ht).2.trans he.2⟩
  have hslab (t : ℝ) (ht : t ∈ Ioo l u) : t ∈ Ioo (0 : ℝ) H :=
    ⟨zero_lt_one.trans (hinside t ht).1, (hinside t ht).2.trans (hTτ.trans hτH)⟩
  have heq : EqOn γ (q (0, 0) cStar) (Icc (0 : ℝ) H) := hcommon (0, 0) h0U0 cStar hcV0
  have hfast : fastLogCosh 0 = fun s : ℝ ↦ 2 * s :=
    funext fun s ↦ by simp only [fastLogCosh, zero_mul, add_zero]
  refine ⟨hmatch, hbsupp.trans (Ioo_subset_Ioo (by norm_num) (by norm_num)), l, u, hlu,
    fun t ht ↦ hslab t ht, hbranch, fun t ht ↦ ?_⟩
  obtain ⟨hxgate, _, hnormalized, hnonzero, hderiv, hdecomp⟩ := hpatch t ht
  have htI := hinside t ht
  have htH := hslab t ht
  have hstate : γ t = (!₂[Z0 t * ρ t, X0 t, Z0 t] : ℝ^3) := heq ⟨htH.1.le, htH.2.le⟩
  have hx : γ t 1 = X0 t := by rw [hstate]; rfl
  have hz : γ t 2 = Z0 t := by rw [hstate]; rfl
  have hinner : 2 < Z0 t := by linarith [hZlower0 t ⟨htI.1.le, htI.2.le⟩, htI.1]
  -- Every patch point is interior to the closed agreement slab.
  have hnear : γ =ᶠ[𝓝 t] q (0, 0) cStar :=
    eventually_of_mem (Ioo_mem_nhds htH.1 htH.2) fun s hs ↦ heq ⟨hs.1.le, hs.2.le⟩
  have hcandidate : HasDerivAt (q (0, 0) cStar)
      (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff (clockFeedback A B)
        (fun y ↦ b (cStar, y)) (q (0, 0) cStar t)) t := hderiv
  refine ⟨by simpa only [hx] using hxgate,
    by simpa only [hz] using hinner,
    by simpa only [hz] using hZsq0 t htI,
    by simpa only [hx, hz] using hnormalized, hnonzero, ?_, ?_⟩
  · apply (hcandidate.congr_of_eventuallyEq hnear).congr_deriv
    rw [concreteGatedFlux, hfast, heq ⟨htH.1.le, htH.2.le⟩]
  · rw [concreteGatedFlux, hfast, hstate]
    exact hdecomp

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
