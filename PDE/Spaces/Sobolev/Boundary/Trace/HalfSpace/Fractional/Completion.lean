/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentCompletion

/-!
# Fractional trace bounds by smooth approximation

A uniform nonnegative Gagliardo estimate on globally compactly supported smooth functions
passes to the finite-exponent half-space trace. Boundary `Lᵖ` convergence gives an
almost-everywhere convergent subsequence, and Fatou preserves the coordinate derivative
energy and its constant. No fractional space or lifting is used.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Filter Set
open scoped ENNReal NNReal Sobolev Topology

private theorem coordinate_enorm_rpow_eq_lintegral
    (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (φ : GlobalTestFunction n) (i : Fin (n + 1)) :
    ‖GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex (n + 1) i)
      (globalTestFunctionToUpperW1pLinear n p φ)‖ₑ ^ p =
      ∫⁻ x in HalfSpace.upper (n + 1), ‖(∂[i] φ.1.toFun) x‖ₑ ^ p := by
  let v := GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex (n + 1) i)
    (globalTestFunctionToUpperW1pLinear n p φ)
  have hv : (v : ℝ^(n + 1) → ℝ) =ᵐ[
      domainMeasure (n + 1) (HalfSpace.upper (n + 1))] ∂[i] φ.1.toFun := by
    dsimp only [v]
    rw [GraphSpace.wkpCoordinateCLM_apply, globalTestFunctionToUpperW1pLinear_eq_mk]
    simpa only [GraphSpace.singleDerivIndex_toList, iteratedPartialDeriv] using
      GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (p := ENNReal.ofReal p) (Ω := HalfSpace.upper (n + 1))
        φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport
        (GraphSpace.singleDerivIndex (n + 1) i)
  have hnorm : ‖v‖ₑ ^ p =
      ∫⁻ x, ‖v x‖ₑ ^ p ∂domainMeasure (n + 1) (HalfSpace.upper (n + 1)) := by
    rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top
      (Lp.aestronglyMeasurable v), ENNReal.toReal_ofReal hp.le]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hp).symm
  exact hnorm.trans (lintegral_congr_ae (hv.mono fun x hx ↦
    congrArg (fun t : ℝ ↦ ‖t‖ₑ ^ p) hx))

private theorem lintegral_sub_rpow_div_le_liminf
    (n : ℕ) {p a : ℝ} (hp : 0 < p)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j, AEStronglyMeasurable (f j) (volume : Measure (ℝ^n)))
    (hfg : ∀ᵐ x ∂(volume : Measure (ℝ^n)), Tendsto (fun j ↦ f j x) atTop (𝓝 (g x))) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖g z.1 - g z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ a
      ∂((volume : Measure (ℝ^n)).prod volume)) ≤
    atTop.liminf (fun j ↦
      ∫⁻ z : ℝ^n × ℝ^n,
        ‖f j z.1 - f j z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ a
        ∂((volume : Measure (ℝ^n)).prod volume)) := by
  let F (v : ℝ^n → ℝ) (z : ℝ^n × ℝ^n) :=
    ‖v z.1 - v z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ a
  have hmeas (j : ℕ) :
      AEMeasurable (F (f j)) ((volume : Measure (ℝ^n)).prod volume) := by
    exact (((hf j).aemeasurable.comp_fst.sub (hf j).aemeasurable.comp_snd).enorm.pow_const p).div
      (((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).pow_const a).aemeasurable
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae hfg
  have hsnd := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae hfg
  have hlim : ∀ᵐ z ∂((volume : Measure (ℝ^n)).prod volume),
      Tendsto (fun j ↦ F (f j) z) atTop (𝓝 (F g z)) := by
    filter_upwards [hfst, hsnd] with z hz₁ hz₂
    by_cases hz : z.1 = z.2
    · simp [F, hz, ENNReal.zero_rpow_of_pos hp]
    · apply ENNReal.Tendsto.div_const
        ((ENNReal.continuous_rpow_const.tendsto _).comp (hz₁.sub hz₂).enorm)
      exact Or.inr (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hz)))
        ENNReal.ofReal_ne_top).ne'
  calc
    _ = ∫⁻ z, atTop.liminf (fun j ↦ F (f j) z)
        ∂((volume : Measure (ℝ^n)).prod volume) :=
      lintegral_congr_ae (hlim.mono fun z hz ↦ hz.liminf_eq.symm)
    _ ≤ _ := lintegral_liminf_le' hmeas

/-- A uniform smooth fractional trace estimate passes to the completed `W¹ᵖ` trace.

The right side is the sum of the p-energies of the weak derivative coordinates.
The constant is finite, the boundary measure need not be finite, and boundary dimension
zero is allowed. The smooth estimate is a premise to be supplied by an analytic theorem. -/
theorem lintegral_traceLp_sub_rpow_div_le_of_smooth
    (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (C : ℝ≥0)
    (hsmooth : ∀ φ : GlobalTestFunction n,
      (∫⁻ z : ℝ^n × ℝ^n,
        ‖smoothBoundaryValue φ.1.toFun z.1 - smoothBoundaryValue φ.1.toFun z.2‖ₑ ^ p /
          (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
        ∂((volume : Measure (ℝ^n)).prod volume)) ≤
      (C : ℝ≥0∞) * ∑ i : Fin (n + 1),
        ∫⁻ x in HalfSpace.upper (n + 1), ‖(∂[i] φ.1.toFun) x‖ₑ ^ p)
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^n)).prod volume)) ≤
    (C : ℝ≥0∞) * ∑ i : Fin (n + 1),
      ‖GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex (n + 1) i) u‖ₑ ^ p := by
  classical
  let T := traceLp n p hp.le
  let core := globalTestFunctionToUpperW1pLinear n p
  let energy (v : ℝ^n → ℝ) :=
    ∫⁻ z : ℝ^n × ℝ^n,
      ‖v z.1 - v z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^n)).prod volume)
  let bound (v : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :=
    (C : ℝ≥0∞) * ∑ i : Fin (n + 1),
      ‖GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex (n + 1) i) v‖ₑ ^ p
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_globalTestFunctionToUpperW1pLinear n p u)
  choose φ hφ using hv
  have hcorelim : Tendsto (fun j ↦ core (φ j)) atTop (𝓝 u) := by
    simpa only [core, hφ] using hvlim
  have hTlim := (T.continuous.tendsto u).comp hcorelim
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hTlim).exists_seq_tendsto_ae
  have hbound (ψ : GlobalTestFunction n) : energy (T (core ψ)) ≤ bound (core ψ) := by
    have htrace : (T (core ψ) : ℝ^n → ℝ) =ᵐ[volume] smoothBoundaryValue ψ.1.toFun := by
      dsimp only [T, core]
      rw [traceLp_smooth]
      exact (smoothBoundaryValue_memLp_ofReal n p ψ).coeFn_toLp
    have hfst := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae htrace
    have hsnd := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae htrace
    calc
      energy (T (core ψ)) = energy (smoothBoundaryValue ψ.1.toFun) := by
        apply lintegral_congr_ae
        filter_upwards [hfst, hsnd] with z hz₁ hz₂
        rw [hz₁, hz₂]
      _ ≤ (C : ℝ≥0∞) * ∑ i : Fin (n + 1),
          ∫⁻ x in HalfSpace.upper (n + 1), ‖(∂[i] ψ.1.toFun) x‖ₑ ^ p := hsmooth ψ
      _ = bound (core ψ) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦
          (coordinate_enorm_rpow_eq_lintegral n p (zero_lt_one.trans hp) ψ i).symm
  have hboundlim : Tendsto (fun j ↦ bound (core (φ (ns j)))) atTop (𝓝 (bound u)) := by
    apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.coe_ne_top)
    apply tendsto_finsetSum
    intro i _
    let L := GraphSpace.wkpCoordinateCLM (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper (n + 1)) (GraphSpace.singleDerivIndex (n + 1) i)
    exact ((L.continuous.tendsto u).comp
      (hcorelim.comp hns.tendsto_atTop)).enorm.ennrpow_const p
  calc
    energy (T u) ≤ atTop.liminf (fun j ↦ energy (T (core (φ (ns j))))) :=
      lintegral_sub_rpow_div_le_liminf n (zero_lt_one.trans hp)
        (fun j ↦ Lp.aestronglyMeasurable _) hlim
    _ ≤ atTop.liminf (fun j ↦ bound (core (φ (ns j)))) :=
      Filter.liminf_le_liminf (Eventually.of_forall fun j ↦ hbound (φ (ns j)))
    _ = bound u := hboundlim.liminf_eq

end SobolevSpace.Trace.HalfSpace
