/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar
public import PDE.Common.Euclidean

import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ImplicitContDiff
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.ResidualRegularity
import CAS.ExactTactic

/-!
# Positive delta matching for the retained prescribed terminal event

The supplied flow and event retain the scalar-solution candidates on a
common zero-delta product. Their terminal coordinates are smooth, and the positive
fast terminal value of the candidates gives a smaller domain with positive denominator.
The coefficient derivative of the candidate residual then gives a positive-delta zero of the three
matching residuals. The selected delta and coefficients are fixed on a common
neighborhood of the forward and reflected physical-parameter paths.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis PDE.Analysis.Evolution
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The retained full terminal germ admits a small positive delta and fixed coefficients
satisfying the three matching conditions at zero physical parameters. The candidate
residual supplies the coefficient derivative and selected zero. Positivity of its fast
terminal value gives a common smaller event domain, while both physical paths remain
in the original event domain after the delta and coefficients have been fixed. -/
theorem exists_prescribed_clock_positive_delta_terminal {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {L : ℝ × ℝ → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))}
    {U : Set (ℝ × ℝ)} {V : Set (Fin 3 → ℝ)} {cStar : Fin 3 → ℝ} {J : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    {H ε : ℝ} (hN : IsOpen N) (hbaseN : ((0, cStar), (0, 0)) ∈ N) (hΨ : ContDiff ℝ ∞ Ψ)
    (hT : ContDiffOn ℝ ∞ T N) (hU : IsOpen U) (hbaseU : (0, 0) ∈ U) (hV : IsOpen V)
    (hbaseV : cStar ∈ V) (hZbase : 0 < (F (L (0, 0), (0, 0))).2) (hε : 0 < ε) :
    let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
      !₂[(F (t, p)).2 * scalarLinearSolution (fun _ : ℝ ↦ 4)
          (fun s ↦ b (c, (F (s, p)).1)) 0 0 t, (F (t, p)).1, (F (t, p)).2]
    let x : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ := fun θ ↦ Ψ (T θ, θ) 0
    let z : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ := fun θ ↦ Ψ (T θ, θ) 2
    let x0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ q u.2 u.1 (L u.2) 0
    let z0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ q u.2 u.1 (L u.2) 2
    let ρ : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ := fun θ ↦ x θ / z θ
    let ρ0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ x0 u / z0 u
    let Gold : (Fin 3 → ℝ) → Fin 3 → ℝ := fun c ↦
      ![ρ0 (c, (0, 0)) - 1,
        deriv (fun a : ℝ ↦ ρ0 (c, (0, a))) 0,
        z0 (c, (0, 0)) * deriv (fun μ : ℝ ↦ ρ0 (c, (μ, 0))) 0 +
          2 * deriv (fun μ : ℝ ↦ z0 (c, (μ, 0))) 0 +
          2000000 * deriv (fun a : ℝ ↦ z0 (c, (0, a))) 0]
    (∀ p ∈ U, ∀ c ∈ V,
      ((0, c), p) ∈ N ∧ T ((0, c), p) = L p ∧
      EqOn (fun t ↦ Ψ (t, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) ∧
      Ψ (T ((0, c), p), ((0, c), p)) = q p c (L p)) →
    HasFDerivAt Gold J cStar → IsUnit J → Gold cStar = 0 →
    ∃ (N1 : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)))
      (U1 : Set (ℝ × ℝ)) (V1 : Set (Fin 3 → ℝ)),
      IsOpen N1 ∧ ((0, cStar), (0, 0)) ∈ N1 ∧ N1 ⊆ N ∧
      ContDiffOn ℝ ∞ x N1 ∧ ContDiffOn ℝ ∞ z N1 ∧
      (∀ θ ∈ N1, 0 < z θ) ∧
      IsOpen U1 ∧ (0, 0) ∈ U1 ∧ U1 ⊆ U ∧
      IsOpen V1 ∧ cStar ∈ V1 ∧ V1 ⊆ V ∧
      (∀ p ∈ U1, ∀ c ∈ V1,
        ((0, c), p) ∈ N1 ∧ T ((0, c), p) = L p ∧
        EqOn (fun t ↦ Ψ (t, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) ∧
        Ψ (T ((0, c), p), ((0, c), p)) = q p c (L p)) ∧
      ∃ (δPos : ℝ) (cPos : Fin 3 → ℝ) (W : Set ℝ),
        0 < δPos ∧ δPos < min ε (1 / 4) ∧ cPos ∈ V1 ∧
        ((δPos, cPos), (0, 0)) ∈ N1 ∧
        ρ ((δPos, cPos), (0, 0)) = 1 ∧
        deriv (fun a : ℝ ↦ ρ ((δPos, cPos), (0, a))) 0 = 0 ∧
        z ((δPos, cPos), (0, 0)) *
            deriv (fun μ : ℝ ↦ ρ ((δPos, cPos), (μ, 0))) 0 +
          2 * deriv (fun μ : ℝ ↦ z ((δPos, cPos), (μ, 0))) 0 +
          2000000 * deriv (fun a : ℝ ↦ z ((δPos, cPos), (0, a))) 0 = 0 ∧
        IsOpen W ∧ (0 : ℝ) ∈ W ∧
        ∀ μ ∈ W,
          ((δPos, cPos), (μ, 0)) ∈ N ∧
          ((δPos, cPos), (-μ, -2000000 * μ)) ∈ N ∧
          0 < z ((δPos, cPos), (μ, 0)) ∧
          0 < z ((δPos, cPos), (-μ, -2000000 * μ)) := by
  intro q x z x0 z0 ρ ρ0 Gold hcommon hGold hJUnit hGoldzero
  have hterminalSmooth : ContDiffOn ℝ ∞ (fun θ ↦ Ψ (T θ, θ)) N :=
    hΨ.comp_contDiffOn (hT.prodMk contDiffOn_id)
  have hx : ContDiffOn ℝ ∞ x N :=
    (contDiff_piLp_apply (i := (0 : Fin 3)) (2 : ENNReal)).comp_contDiffOn hterminalSmooth
  have hz : ContDiffOn ℝ ∞ z N :=
    (contDiff_piLp_apply (i := (2 : Fin 3)) (2 : ENNReal)).comp_contDiffOn hterminalSmooth
  let N1 := N ∩ z ⁻¹' Ioi (0 : ℝ)
  have hN1 : IsOpen N1 := hz.continuousOn.isOpen_inter_preimage hN isOpen_Ioi
  have hbaseN1 : ((0, cStar), (0, 0)) ∈ N1 :=
    ⟨hbaseN, hZbase.trans_eq (congrArg (· 2) (hcommon (0, 0) hbaseU cStar hbaseV).2.2.2).symm⟩
  have hN1sub : N1 ⊆ N := fun _ hθ ↦ hθ.1
  have hzpos : ∀ θ ∈ N1, 0 < z θ := fun _ hθ ↦ hθ.2
  have hx1 : ContDiffOn ℝ ∞ x N1 := hx.mono hN1sub
  have hz1 : ContDiffOn ℝ ∞ z N1 := hz.mono hN1sub
  -- Restrict one product, retaining the complete supplied candidate agreement.
  let ι : (Fin 3 → ℝ) × (ℝ × ℝ) → ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) := fun u ↦ ((0, u.1), u.2)
  have hι : Continuous ι := (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  obtain ⟨V1, U1, hV1, hbaseV1, hU1, hbaseU1, hprod1⟩ := mem_nhds_prod_iff'.mp
    (((hV.prod hU).inter (hN1.preimage hι)).mem_nhds ⟨⟨hbaseV, hbaseU⟩, hbaseN1⟩)
  have hV1sub : V1 ⊆ V := fun c hc ↦ (hprod1 (show (c, (0, 0)) ∈ V1 ×ˢ U1 from ⟨hc, hbaseU1⟩)).1.1
  have hU1sub : U1 ⊆ U := fun p hp ↦ (hprod1 (show (cStar, p) ∈ V1 ×ˢ U1 from ⟨hbaseV1, hp⟩)).1.2
  have hcommon1 : ∀ p ∈ U1, ∀ c ∈ V1, ((0, c), p) ∈ N1 ∧ T ((0, c), p) = L p ∧
      EqOn (fun t ↦ Ψ (t, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) ∧
      Ψ (T ((0, c), p), ((0, c), p)) = q p c (L p) := fun p hp c hc ↦
    ⟨(hprod1 (show (c, p) ∈ V1 ×ˢ U1 from ⟨hc, hp⟩)).2, (hcommon p (hU1sub hp) c (hV1sub hc)).2⟩
  let G : (ℝ × (Fin 3 → ℝ)) → Fin 3 → ℝ := fun σ ↦ ![ρ (σ, (0, 0)) - 1,
      deriv (fun a : ℝ ↦ ρ (σ, (0, a))) 0, z (σ, (0, 0)) * deriv (fun μ : ℝ ↦ ρ (σ, (μ, 0))) 0 +
        2 * deriv (fun μ : ℝ ↦ z (σ, (μ, 0))) 0 + 2000000 * deriv (fun a : ℝ ↦ z (σ, (0, a))) 0]
  have hGreg : IsOpen ((fun σ ↦ (σ, ((0 : ℝ), (0 : ℝ)))) ⁻¹' N1) ∧
      ContDiffOn ℝ ∞ G ((fun σ ↦ (σ, ((0 : ℝ), (0 : ℝ)))) ⁻¹' N1) :=
    contDiffOn_matching_residual hN1 hx1 hz1 (fun θ hθ ↦ (hzpos θ hθ).ne') 2000000
  have hGat : ContDiffAt ℝ ∞ G (0, cStar) := hGreg.2.contDiffAt (hGreg.1.mem_nhds hbaseN1)
  have hμ : Tendsto (fun μ : ℝ ↦ (μ, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  have ha : Tendsto (fun a : ℝ ↦ ((0 : ℝ), a)) (𝓝 0) (𝓝 (0, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto 0
  -- Equality on the common physical neighborhood transfers ordinary derivatives.
  have hG (c : Fin 3 → ℝ) (hc : c ∈ V1) : G (0, c) = Gold c := by
    have hxg : (fun p ↦ x ((0, c), p)) =ᶠ[𝓝 (0, 0)] (fun p ↦ x0 (c, p)) := eventually_of_mem
      (hU1.mem_nhds hbaseU1) fun p hp ↦ congrArg (· 0) (hcommon1 p hp c hc).2.2.2
    have hzg : (fun p ↦ z ((0, c), p)) =ᶠ[𝓝 (0, 0)] (fun p ↦ z0 (c, p)) := eventually_of_mem
      (hU1.mem_nhds hbaseU1) fun p hp ↦ congrArg (· 2) (hcommon1 p hp c hc).2.2.2
    have hρg : (fun p ↦ ρ ((0, c), p)) =ᶠ[𝓝 (0, 0)] (fun p ↦ ρ0 (c, p)) := hxg.div hzg
    have hρa : deriv (fun a : ℝ ↦ ρ ((0, c), (0, a))) 0 =
        deriv (fun a : ℝ ↦ ρ0 (c, (0, a))) 0 := (hρg.comp_tendsto ha).deriv_eq
    have hρμ : deriv (fun μ : ℝ ↦ ρ ((0, c), (μ, 0))) 0 =
        deriv (fun μ : ℝ ↦ ρ0 (c, (μ, 0))) 0 := (hρg.comp_tendsto hμ).deriv_eq
    have hzμ : deriv (fun μ : ℝ ↦ z ((0, c), (μ, 0))) 0 =
        deriv (fun μ : ℝ ↦ z0 (c, (μ, 0))) 0 := (hzg.comp_tendsto hμ).deriv_eq
    have hza : deriv (fun a : ℝ ↦ z ((0, c), (0, a))) 0 =
        deriv (fun a : ℝ ↦ z0 (c, (0, a))) 0 := (hzg.comp_tendsto ha).deriv_eq
    have hρbase : ρ ((0, c), (0, 0)) = ρ0 (c, (0, 0)) := hρg.self_of_nhds
    have hzbase : z ((0, c), (0, 0)) = z0 (c, (0, 0)) := hzg.self_of_nhds
    dsimp only [G, Gold]
    rw [hρbase, hzbase, hρa, hρμ, hzμ, hza]
  have hslice : HasFDerivAt (fun c ↦ G (0, c)) J cStar :=
    hGold.congr_of_eventuallyEq (eventually_of_mem (hV1.mem_nhds hbaseV1) hG)
  have hpartial : fderiv ℝ G (0, cStar) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ) = J :=
    ((hGat.differentiableAt (by simp)).hasFDerivAt.comp cStar
      (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)).hasFDerivAt).unique hslice
  have hinv : (fderiv ℝ G (0, cStar) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)).IsInvertible :=
    let ⟨junit, hjunit⟩ := hJUnit
    hpartial ▸ ⟨ContinuousLinearEquiv.unitsEquiv ℝ (Fin 3 → ℝ) junit, hjunit⟩
  have horder : (∞ : ℕ∞ω) ≠ 0 := by simp
  let c : ℝ → (Fin 3 → ℝ) := hGat.implicitFunction horder hinv
  have hcto : Tendsto c (𝓝 (0 : ℝ)) (𝓝 cStar) := by
    simpa only [ContinuousAt, hGat.implicitFunction_apply_self horder hinv] using
      (hGat.contDiffAt_implicitFunction horder hinv).continuousAt
  have hgood : ∀ᶠ δ in 𝓝 (0 : ℝ),
      G (δ, c δ) = 0 ∧ ((δ, c δ), (0, 0)) ∈ N1 ∧ c δ ∈ V1 := by
    filter_upwards [hGat.eventually_apply_implicitFunction horder hinv,
      ((tendsto_id.prodMk_nhds hcto).prodMk_nhds tendsto_const_nhds) (hN1.mem_nhds hbaseN1),
      hcto (hV1.mem_nhds hbaseV1)] with δ hδ hδN hδV
    exact ⟨hδ.trans ((hG cStar hbaseV1).trans hGoldzero), hδN, hδV⟩
  obtain ⟨δPos, hδgood, hδbounds⟩ := ((Filter.Eventually.filter_mono nhdsWithin_le_nhds hgood).and
    (Ioo_mem_nhdsGT (lt_min hε (by norm_num : (0 : ℝ) < 1 / 4)))).exists
  let cPos := c δPos
  -- These paths vary only the physical parameters, with delta and coefficients fixed.
  let W := (fun μ : ℝ ↦ ((δPos, cPos), (μ, (0 : ℝ)))) ⁻¹' N1 ∩
    (fun μ : ℝ ↦ ((δPos, cPos), (-μ, -2000000 * μ))) ⁻¹' N1
  refine ⟨N1, U1, V1, hN1, hbaseN1, hN1sub, hx1, hz1, hzpos,
    hU1, hbaseU1, hU1sub, hV1, hbaseV1, hV1sub, hcommon1,
    δPos, cPos, W, hδbounds.1, hδbounds.2, hδgood.2.2, hδgood.2.1,
    sub_eq_zero.mp (congrFun hδgood.1 0), congrFun hδgood.1 1, congrFun hδgood.1 2,
    (hN1.preimage (by fun_prop)).inter (hN1.preimage (by fun_prop)),
    ⟨hδgood.2.1, by simpa only [mem_preimage, neg_zero, mul_zero] using hδgood.2.1⟩,
    fun μ hμ ↦ ⟨hN1sub hμ.1, hN1sub hμ.2, hzpos _ hμ.1, hzpos _ hμ.2⟩⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
