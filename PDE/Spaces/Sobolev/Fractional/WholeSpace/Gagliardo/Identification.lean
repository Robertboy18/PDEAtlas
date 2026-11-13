/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.BesselComparison

/-!
# `W^{s,2}(ℝ^n) = H^s(ℝ^n)` for functions

For `0 < s < 1`, a real function `v` on `ℝ^n` satisfies `MemGagliardo n s Set.univ v`
exactly when its complexification agrees almost everywhere with the `L²` representative of
some `u ∈ H^s(ℝ^n)`, and `u` can then be taken in `H^s(ℝ^n; ℝ)`. The proof goes through the
Gagliardo-Fourier identity and `memSobolev_iff_memLp_homogeneousWeightedFourier`. The same
identification for `L²` classes and complete spaces is `memGagliardo_univ_iff_memSobolev` and
`GagliardoSpace.equivHsSpaceReal`.

We also show that smooth compactly supported real functions and real functions agreeing almost
everywhere with a Schwartz function satisfy the Gagliardo condition on `ℝ^n`, that some non-constant
member has positive and finite seminorm, and that the condition is monotone in the order.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, "Hitchhiker's guide to the fractional Sobolev spaces",
  *Bull. Sci. Math.* 136 (2012), 521-573, numbering of arXiv:1104.4345v3, Proposition 3.4, which
  identifies `W^{s,2}(ℝ^n)` (their `H^s(ℝ^n)` of Section 2) with the Fourier space `Ĥ^s(ℝ^n)` of
  (3.7) for `s ∈ (0, 1)`.
  <https://arxiv.org/abs/1104.4345v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace ENNReal FourierTransform SchwartzMap ContDiff Sobolev

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

/-- For `0 ≤ s ≤ 2`, an `L²` function whose Fourier transform has finite homogeneous Fourier
integral `fourierSq n s` is the `L²` representative of an element of `H^s(ℝ^n)`. -/
theorem exists_toL2Fun_eq (hs : 0 ≤ s) (hs2 : s ≤ 2) (F : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (h : fourierSq n s (𝓕 F : Lp ℂ 2 volume) < ⊤) :
    ∃ u : H^{s}(ℝ^n), toL2Fun hs u = F := by
  have hmem : MemSobolev s 2 (F : 𝓢'(ℝ^n, ℂ)) :=
    (memSobolev_iff_memLp_homogeneousWeightedFourier hs hs2 F).2
      ((memLp_homogeneousWeightedFourier_iff s F).2 h)
  refine ⟨hmem.toBesselPotentialSpace, ?_⟩
  apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
  simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply]
  simpa only [MemSobolev.toBesselPotentialSpace_toDistr] using
    (toDistr_eq_toL2Fun hs hmem.toBesselPotentialSpace).symm

/-- For `0 < s < 1`, a real function on `ℝ^n` whose complexification agrees almost everywhere
with the `L²` representative of some `u ∈ H^s(ℝ^n)` satisfies the Gagliardo condition on
`ℝ^n`. -/
theorem memGagliardo_univ_of_hsSpace (hs0 : 0 < s) (hs1 : s < 1) {v : ℝ^n → ℝ}
    {u : H^{s}(ℝ^n)} (hv : (fun x ↦ (v x : ℂ)) =ᵐ[volume] (toL2Fun hs0.le u : ℝ^n → ℂ)) :
    MemGagliardo n s Set.univ v := by
  have hcx : MemLp (fun x ↦ (v x : ℂ)) 2 (volume : Measure (ℝ^n)) :=
    (Lp.memLp (toL2Fun hs0.le u)).ae_eq hv.symm
  refine (memGagliardo_univ_iff v).2 ⟨by simpa using hcx.re, ?_⟩
  rw [gagliardoSq_univ_eq_gagDouble, gagDouble_congr (s := s) hv]
  exact gagDouble_toL2Fun_lt_top hs0 hs1 u

/-- For `0 < s < 1`, the complexification of a real function satisfying the Gagliardo
condition on `ℝ^n` agrees almost everywhere with the `L²` representative of some element
of `H^s(ℝ^n)`. -/
theorem exists_hsSpace_of_memGagliardo_univ (hs0 : 0 < s) (hs1 : s < 1) {v : ℝ^n → ℝ}
    (hv : MemGagliardo n s Set.univ v) :
    ∃ u : H^{s}(ℝ^n), (fun x ↦ (v x : ℂ)) =ᵐ[volume] (toL2Fun hs0.le u : ℝ^n → ℂ) := by
  have hcx : MemLp (fun x ↦ (v x : ℂ)) 2 (volume : Measure (ℝ^n)) :=
    ((memGagliardo_univ_iff v).1 hv).1.ofReal
  obtain ⟨u, hu⟩ := exists_toL2Fun_eq hs0.le (by linarith) (hcx.toLp _)
    ((memGagliardo_univ_iff_fourierSq_lt_top hs0 hs1 v hcx).1 hv)
  refine ⟨u, ?_⟩
  rw [hu]
  exact hcx.coeFn_toLp.symm

/-- `W^{s,2}(ℝ^n) = H^s(ℝ^n)` for functions: for `0 < s < 1`, a real function on `ℝ^n`
satisfies the Gagliardo condition on `ℝ^n` if and only if its complexification agrees
almost everywhere with the `L²` representative of some element of `H^s(ℝ^n)`. -/
theorem memGagliardo_univ_iff_exists_hsSpace (hs0 : 0 < s) (hs1 : s < 1) (v : ℝ^n → ℝ) :
    MemGagliardo n s Set.univ v ↔
      ∃ u : H^{s}(ℝ^n), (fun x ↦ (v x : ℂ)) =ᵐ[volume] (toL2Fun hs0.le u : ℝ^n → ℂ) :=
  ⟨exists_hsSpace_of_memGagliardo_univ hs0 hs1,
    fun ⟨_, hu⟩ ↦ memGagliardo_univ_of_hsSpace hs0 hs1 hu⟩

/-- An `L²` function that agrees almost everywhere with the complexification of a real
function is real. -/
theorem isRealL2_of_ae_eq_ofReal {v : ℝ^n → ℝ} {f : Lp ℂ 2 (volume : Measure (ℝ^n))}
    (hv : (fun x ↦ (v x : ℂ)) =ᵐ[volume] (f : ℝ^n → ℂ)) : IsRealL2 f := by
  filter_upwards [hv] with x hx
  rw [← hx]
  simp

/-- The real form of `memGagliardo_univ_iff_exists_hsSpace`: for `0 < s < 1`, a real
function on `ℝ^n` satisfies the Gagliardo condition on `ℝ^n` if and only if its
complexification agrees almost everywhere with the `L²` representative of some element of
`H^s(ℝ^n; ℝ)`. -/
theorem memGagliardo_univ_iff_exists_hsSpaceReal (hs0 : 0 < s) (hs1 : s < 1) (v : ℝ^n → ℝ) :
    MemGagliardo n s Set.univ v ↔
      ∃ u : H^{s}(ℝ^n; ℝ), (fun x ↦ (v x : ℂ)) =ᵐ[volume] (toL2Fun hs0.le u.1 : ℝ^n → ℂ) := by
  rw [memGagliardo_univ_iff_exists_hsSpace hs0 hs1 v]
  exact ⟨fun ⟨u, hu⟩ ↦
      ⟨HsSpaceReal.ofPhysical hs0.le u (isRealL2_of_ae_eq_ofReal hu), hu⟩,
    fun ⟨u, hu⟩ ↦ ⟨u.1, hu⟩⟩

/-- For `0 < s < 1`, every smooth compactly supported real function on `ℝ^n` satisfies the
Gagliardo condition on `ℝ^n`. -/
theorem memGagliardo_univ_of_hasCompactSupport (hs0 : 0 < s) (hs1 : s < 1) {v : ℝ^n → ℝ}
    (hcs : HasCompactSupport v) (hsm : ContDiff ℝ ∞ v) :
    MemGagliardo n s Set.univ v :=
  (memGagliardo_univ_iff v).2
    ⟨hsm.continuous.memLp_of_hasCompactSupport hcs,
      gagliardoSq_univ_lt_top_of_hasCompactSupport hs0 hs1 hcs hsm⟩

/-- For `1 ≤ n` and `0 < s < 1`, some non-constant real function on `ℝ^n` satisfies the
Gagliardo condition on `ℝ^n` with positive and finite seminorm. Positivity is part of the
statement because a non-constant function can have seminorm zero, for example the indicator
of a point. -/
theorem exists_nonconstant_memGagliardo_univ (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ v : ℝ^n → ℝ, (∃ x y : ℝ^n, v x ≠ v y) ∧ MemGagliardo n s Set.univ v ∧
      0 < gagliardoSq n s Set.univ v ∧ gagliardoSq n s Set.univ v < ⊤ := by
  obtain ⟨v, hne, hcs, hsm⟩ := exists_nonconstant_contDiff_hasCompactSupport (n := n) hn
  exact ⟨v, hne, memGagliardo_univ_of_hasCompactSupport hs0 hs1 hcs hsm,
    gagliardoSq_univ_pos hsm.continuous hne,
    gagliardoSq_univ_lt_top_of_hasCompactSupport hs0 hs1 hcs hsm⟩

/-- For `0 < s < 1`, a real function on `ℝ^n` whose complexification agrees almost
everywhere with a Schwartz function satisfies the Gagliardo condition on `ℝ^n`. -/
theorem memGagliardo_univ_of_schwartz_ae (hs0 : 0 < s) (hs1 : s < 1) (v : ℝ^n → ℝ)
    (φ : 𝓢(ℝ^n, ℂ)) (hv : (fun x ↦ (v x : ℂ)) =ᵐ[volume] (φ : ℝ^n → ℂ)) :
    MemGagliardo n s Set.univ v := by
  have hcx : MemLp (fun x ↦ (v x : ℂ)) 2 (volume : Measure (ℝ^n)) :=
    (φ.memLp 2 volume).ae_eq hv.symm
  refine (memGagliardo_univ_iff v).2 ⟨by simpa using hcx.re, ?_⟩
  rw [gagliardoSq_univ_eq_gagDouble, gagDouble_congr (s := s) hv]
  exact gagDouble_schwartz_lt_top hs0 hs1 φ

/-- For `0 < s < 1`, a real function on `ℝ^n` whose complexification is a Schwartz function
satisfies the Gagliardo condition on `ℝ^n`. -/
theorem memGagliardo_univ_of_schwartz (hs0 : 0 < s) (hs1 : s < 1) (v : ℝ^n → ℝ)
    (φ : 𝓢(ℝ^n, ℂ)) (hv : ∀ x, ((v x : ℝ) : ℂ) = φ x) :
    MemGagliardo n s Set.univ v :=
  memGagliardo_univ_of_schwartz_ae hs0 hs1 v φ (Filter.Eventually.of_forall hv)

/-- The Gagliardo condition on `ℝ^n` is monotone in the order: for `0 < s ≤ t < 1`, a real
function satisfying it at order `t` satisfies it at order `s`. -/
theorem memGagliardo_univ_mono {t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (ht1 : t < 1)
    {v : ℝ^n → ℝ} (hv : MemGagliardo n t Set.univ v) : MemGagliardo n s Set.univ v := by
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  obtain ⟨u, hu⟩ := (memGagliardo_univ_iff_exists_hsSpace ht0 ht1 v).1 hv
  refine (memGagliardo_univ_iff_exists_hsSpace hs0 hs1 v).2 ⟨inclLinear n hst u, ?_⟩
  rwa [toL2Fun_inclLinear hst hs0.le ht0.le u]

end SobolevSpace.Fractional
