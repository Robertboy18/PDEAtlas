/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileSemigroupSobolev
public import PDE.Spaces.Sobolev.Fractional.Integer.RealOrders

/-!
# Smoothing of real order for the linearized self-similar semigroup

The semigroup `S(t)` of the self-similar Navier–Stokes operator linearized at a profile maps
`Hʲ` into `Hʲ⁺ᵐ` for integers `j` and `m`, with the bound `C t^{-m/2} e^{ωt}`
(`profileSemigroup_exists_smoothing`). This module extends the bound to all real orders
`0 ≤ σ₁ ≤ σ₂`, with the gain `t^{-(σ₂-σ₁)/2}` from `H^{σ₁}` to `H^{σ₂}`, stated with the
energies `E_σ = ‖·‖²_{H^σ}`. It holds for all transport and stretching coefficients that are
bounded with all their derivatives. A fixed point argument that loses one derivative needs such
a gain strictly between one and two. Hou, Wang and Yang use the estimate in Section 2.2 for the
stable part of the linearized operator. The semigroup as a strongly continuous semigroup on
`H^σ` for non-integer `σ` is not constructed here. A Duhamel argument uses only the estimate.

## Main results

* `vectorLowerOrderCLM_profileSemigroup_zero`: for every order `j`, the semigroup on `Hʲ` is the
  restriction of the semigroup on `L²`.
* `profileSemigroup_exists_besselEnergy_le_nat`: for all integers `j` and `m`,
  `E_{j+m}(S(t)x) ≤ C t^{-m} e^{ωt} E_j(x)` for all `t > 0` and all `x ∈ L²`.
* `profileSemigroup_exists_besselEnergy_le`: for all real `0 ≤ σ₁ ≤ σ₂`,
  `E_{σ₂}(S(t)x) ≤ C t^{-(σ₂-σ₁)} e^{ωt} E_{σ₁}(x)` for all `t > 0` and all `x ∈ L²`.

## How it works

The integer estimates become bounds between the energies `E_j` and `E_{j+m}` of the field at
time zero and at time `t` (`besselEnergy_le_of_lift`), with the constant `C t^{-m} e^{ωt}`, the
square of the operator bound. Take the four corners `(j, j + m)`, `(j + 1, j + 1 + m)`,
`(j, j + m + 1)`, `(j + 1, j + m + 2)` with `j = ⌊σ₁⌋` and `m = ⌊σ₂ - σ₁⌋`, and the same `C`
and `ω` at all four. Interpolation moves the source order to `σ₁` without changing the
constant, and the logarithmic convexity of the energy gives the gain `m + η`:
`(t^{-m})^{1-η} (t^{-m-1})^η = t^{-(m+η)}` (`besselEnergy_le_of_four_bounds`).

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.2, the smoothing
  estimates of the stable part. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.Selfsimilar

variable {b : Fin 3 → DerivLp 3 ∞ Set.univ} {c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ}

/-- **The semigroup on `Hʲ` is the restriction of the semigroup on `L²`.** This is
`vectorLowerOrderCLM_profileSemigroup` from order `0`, stated on `Hʲ` rather than on `H⁰⁺ʲ`. -/
theorem vectorLowerOrderCLM_profileSemigroup_zero (hk : ∀ k, ProfileCoefficientBounds k b c)
    (j : ℕ) (t : ℝ≥0) (u : VectorH 3 j) :
    vectorLowerOrderCLM (Nat.zero_le j) (profileSemigroup j b c (hk j) t u) =
      profileSemigroup 0 b c (hk 0) t (vectorLowerOrderCLM (Nat.zero_le j) u) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = 0 + m := ⟨j, (Nat.zero_add j).symm⟩
  exact vectorLowerOrderCLM_profileSemigroup 0 m (hk (0 + m)) (hk 0) t u

/-- **Smoothing between integer orders, for the energies.** With coefficients bounded at every
order, for all integers `j` and `m` there are `C > 0` and `ω ≥ 0` with
`E_{j+m}(S(t)x) ≤ C t^{-m} e^{ωt} E_j(x)` for all `t > 0` and all `x ∈ L²`. -/
theorem profileSemigroup_exists_besselEnergy_le_nat (hk : ∀ k, ProfileCoefficientBounds k b c)
    (j m : ℕ) :
    ∃ C ω : ℝ, 0 < C ∧ 0 ≤ ω ∧ ∀ t : ℝ≥0, 0 < t → ∀ x : VectorH 3 0,
      besselEnergy ((j : ℝ) + m) (vectorBaseL2 (profileSemigroup 0 b c (hk 0) t x)) ≤
        ENNReal.ofReal (C * (t : ℝ) ^ (-(m : ℝ)) * Real.exp (ω * t)) *
          besselEnergy (j : ℝ) (vectorBaseL2 x) := by
  obtain ⟨C₀, ω₀, hC₀, hG⟩ := profileSemigroup_exists_smoothing j m (hk (j + m)) (hk j)
  have hc := liftConst_pos 3 j (j + m)
  refine ⟨(liftConst 3 j (j + m) * (C₀ + 1)) ^ 2, 2 * |ω₀|, by positivity, by positivity,
    fun t ht x ↦ ?_⟩
  obtain ⟨G, hGcomp, hGnorm⟩ := hG t ht
  have ht' : (0 : ℝ) < t := ht
  -- the lift of the semigroup on `L²`
  have hlift (u : VectorH 3 j) : vectorLowerOrderCLM (Nat.zero_le (j + m)) (G u) =
      profileSemigroup 0 b c (hk 0) t (vectorLowerOrderCLM (Nat.zero_le j) u) := by
    rw [← vectorLowerOrderCLM_profileSemigroup_zero hk j t u, ← hGcomp]
    exact (vectorLowerOrderCLM_trans_apply (Nat.zero_le j) (Nat.le_add_right j m) (G u)).symm
  set K : ℝ := (C₀ + 1) * (t : ℝ) ^ (-((m : ℝ) / 2)) * Real.exp (ω₀ * t) with hK
  have hK0 : 0 < K := by positivity
  have hGK : ‖G‖ ≤ K := hGnorm.trans (by
    rw [hK]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      (Real.exp_pos _).le)
  have h := besselEnergy_le_of_lift (T := fun x ↦ profileSemigroup 0 b c (hk 0) t x) hlift hK0
    hGK x
  rw [Nat.cast_add] at h
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  -- the square of the constant
  have h1 : ((t : ℝ) ^ (-((m : ℝ) / 2))) ^ 2 = (t : ℝ) ^ (-(m : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht'.le]
    congr 1
    push_cast
    ring
  have h2 : Real.exp (ω₀ * t) ^ 2 ≤ Real.exp (2 * |ω₀| * t) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith [le_abs_self ω₀, ht'.le]
  calc (liftConst 3 j (j + m) * K) ^ 2
      = (liftConst 3 j (j + m) * (C₀ + 1)) ^ 2 * (t : ℝ) ^ (-(m : ℝ)) *
          Real.exp (ω₀ * t) ^ 2 := by
        rw [hK, ← h1]
        ring
    _ ≤ (liftConst 3 j (j + m) * (C₀ + 1)) ^ 2 * (t : ℝ) ^ (-(m : ℝ)) *
          Real.exp (2 * |ω₀| * t) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Smoothing of real order for the linearized self-similar semigroup.** Let the transport and
stretching coefficients be bounded with all their derivatives. For all real `0 ≤ σ₁ ≤ σ₂` there
are `C > 0` and `ω ≥ 0` such that, for every `t > 0` and every vector field `x ∈ L²`,

`E_{σ₂}(S(t)x) ≤ C t^{-(σ₂-σ₁)} e^{ωt} E_{σ₁}(x)`,

where `E_σ` is the Sobolev energy of order `σ`, the square of the `H^σ` norm. In norms this is
`‖S(t)x‖_{H^{σ₂}} ≤ C' t^{-(σ₂-σ₁)/2} e^{ωt/2} ‖x‖_{H^{σ₁}}`: the gain of regularity for short
times, at real orders. A field that is not in `H^{σ₁}` is allowed, the right side is then
infinite.

The proof interpolates the estimates at integer orders: the source order by the real method, the
gain by the logarithmic convexity of the energy. -/
theorem profileSemigroup_exists_besselEnergy_le (hk : ∀ k, ProfileCoefficientBounds k b c)
    {σ₁ σ₂ : ℝ} (h₁ : 0 ≤ σ₁) (h₁₂ : σ₁ ≤ σ₂) :
    ∃ C ω : ℝ, 0 < C ∧ 0 ≤ ω ∧ ∀ t : ℝ≥0, 0 < t → ∀ x : VectorH 3 0,
      besselEnergy σ₂ (vectorBaseL2 (profileSemigroup 0 b c (hk 0) t x)) ≤
        ENNReal.ofReal (C * (t : ℝ) ^ (-(σ₂ - σ₁)) * Real.exp (ω * t)) *
          besselEnergy σ₁ (vectorBaseL2 x) := by
  -- the integer parts
  set j : ℕ := ⌊σ₁⌋₊ with hj
  set m : ℕ := ⌊σ₂ - σ₁⌋₊ with hm
  set θ : ℝ := σ₁ - j with hθ
  set η : ℝ := σ₂ - σ₁ - m with hη
  have hd : 0 ≤ σ₂ - σ₁ := by linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    linarith [Nat.floor_le h₁]
  have hθ1 : θ ≤ 1 := by
    rw [hθ]
    linarith [(Nat.lt_floor_add_one σ₁).le]
  have hη0 : 0 ≤ η := by
    rw [hη]
    linarith [Nat.floor_le hd]
  have hη1 : η ≤ 1 := by
    rw [hη]
    linarith [(Nat.lt_floor_add_one (σ₂ - σ₁)).le]
  -- the four corners, with common constants
  obtain ⟨C₀₀, ω₀₀, hC₀₀, hω₀₀, H₀₀⟩ := profileSemigroup_exists_besselEnergy_le_nat hk j m
  obtain ⟨C₁₀, ω₁₀, hC₁₀, hω₁₀, H₁₀⟩ := profileSemigroup_exists_besselEnergy_le_nat hk (j + 1) m
  obtain ⟨C₀₁, ω₀₁, hC₀₁, hω₀₁, H₀₁⟩ := profileSemigroup_exists_besselEnergy_le_nat hk j (m + 1)
  obtain ⟨C₁₁, ω₁₁, hC₁₁, hω₁₁, H₁₁⟩ :=
    profileSemigroup_exists_besselEnergy_le_nat hk (j + 1) (m + 1)
  set C : ℝ := C₀₀ + C₁₀ + C₀₁ + C₁₁ with hC
  set ω : ℝ := ω₀₀ + ω₁₀ + ω₀₁ + ω₁₁ with hω
  have hC0 : 0 < C := by positivity
  refine ⟨C, ω, hC0, by positivity, fun t ht x ↦ ?_⟩
  have ht' : (0 : ℝ) < t := ht
  have hexp (ω' : ℝ) (hω' : ω' ≤ ω) : Real.exp (ω' * t) ≤ Real.exp (ω * t) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hω' ht'.le)
  -- a common bound for a corner
  have hcorner (C' ω' : ℝ) (hC' : 0 < C') (hC'C : C' ≤ C) (hω'0 : 0 ≤ ω') (hω' : ω' ≤ ω)
      (p : ℝ) : ENNReal.ofReal (C' * (t : ℝ) ^ p * Real.exp (ω' * t)) ≤
        ((C * (t : ℝ) ^ p * Real.exp (ω * t)).toNNReal : ℝ≥0∞) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul (mul_le_mul_of_nonneg_right hC'C
      (Real.rpow_nonneg ht'.le _)) (hexp ω' hω') (Real.exp_pos _).le (by positivity))
  set M : ℝ≥0 := (C * (t : ℝ) ^ (-(m : ℝ)) * Real.exp (ω * t)).toNNReal with hM
  set N : ℝ≥0 := (C * (t : ℝ) ^ (-((m : ℝ) + 1)) * Real.exp (ω * t)).toNNReal with hN
  have hMpos : 0 < C * (t : ℝ) ^ (-(m : ℝ)) * Real.exp (ω * t) := by positivity
  have hNpos : 0 < C * (t : ℝ) ^ (-((m : ℝ) + 1)) * Real.exp (ω * t) := by positivity
  have hT : ∀ x y : VectorH 3 0, profileSemigroup 0 b c (hk 0) t (x + y) =
      profileSemigroup 0 b c (hk 0) t x + profileSemigroup 0 b c (hk 0) t y :=
    fun x y ↦ map_add _ x y
  have key := besselEnergy_le_of_four_bounds (T := fun x ↦ profileSemigroup 0 b c (hk 0) t x)
    hT (a := (j : ℝ)) (d := (m : ℝ)) hθ0 hθ1 hη0 hη1
    (fun x ↦ (H₀₀ t ht x).trans (mul_le_mul' (hcorner C₀₀ ω₀₀ hC₀₀ (by rw [hC]; linarith)
      hω₀₀ (by rw [hω]; linarith) _) le_rfl))
    (fun x ↦ by
      have h := H₁₀ t ht x
      rw [Nat.cast_add, Nat.cast_one] at h
      exact h.trans (mul_le_mul' (hcorner C₁₀ ω₁₀ hC₁₀ (by rw [hC]; linarith) hω₁₀
        (by rw [hω]; linarith) _) le_rfl))
    (fun x ↦ by
      have h := H₀₁ t ht x
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc] at h
      exact h.trans (mul_le_mul' (hcorner C₀₁ ω₀₁ hC₀₁ (by rw [hC]; linarith) hω₀₁
        (by rw [hω]; linarith) (-((m : ℝ) + 1))) le_rfl))
    (fun x ↦ by
      have h := H₁₁ t ht x
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one, ← add_assoc] at h
      exact h.trans (mul_le_mul' (hcorner C₁₁ ω₁₁ hC₁₁ (by rw [hC]; linarith) hω₁₁
        (by rw [hω]; linarith) (-((m : ℝ) + 1))) le_rfl)) x
  have e1 : (j : ℝ) + θ = σ₁ := by
    rw [hθ]
    ring
  have e2 : σ₁ + (m : ℝ) + η = σ₂ := by
    rw [hη]
    ring
  rw [e1, e2] at key
  refine key.trans (mul_le_mul' (le_of_eq ?_) le_rfl)
  -- the constant `M^{1-η} N^η`
  have h1η : 0 ≤ 1 - η := by linarith
  have hMc : (M : ℝ≥0∞) = ENNReal.ofReal (C * (t : ℝ) ^ (-(m : ℝ)) * Real.exp (ω * t)) := rfl
  have hNc : (N : ℝ≥0∞) =
      ENNReal.ofReal (C * (t : ℝ) ^ (-((m : ℝ) + 1)) * Real.exp (ω * t)) := rfl
  rw [hMc, hNc, ENNReal.ofReal_rpow_of_pos hMpos, ENNReal.ofReal_rpow_of_pos hNpos,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hMpos.le _)]
  congr 1
  have hE : (0 : ℝ) < Real.exp (ω * t) := Real.exp_pos _
  rw [Real.mul_rpow (by positivity) hE.le, Real.mul_rpow hC0.le (Real.rpow_nonneg ht'.le _),
    Real.mul_rpow (by positivity) hE.le, Real.mul_rpow hC0.le (Real.rpow_nonneg ht'.le _),
    ← Real.rpow_mul ht'.le, ← Real.rpow_mul ht'.le]
  have hCC : C ^ (1 - η) * C ^ η = C := by
    rw [← Real.rpow_add hC0, sub_add_cancel, Real.rpow_one]
  have hEE : Real.exp (ω * t) ^ (1 - η) * Real.exp (ω * t) ^ η = Real.exp (ω * t) := by
    rw [← Real.rpow_add hE, sub_add_cancel, Real.rpow_one]
  have htt : (t : ℝ) ^ (-(m : ℝ) * (1 - η)) * (t : ℝ) ^ (-((m : ℝ) + 1) * η) =
      (t : ℝ) ^ (-(σ₂ - σ₁)) := by
    rw [← Real.rpow_add ht']
    congr 1
    rw [hη]
    ring
  calc C ^ (1 - η) * (t : ℝ) ^ (-(m : ℝ) * (1 - η)) * Real.exp (ω * t) ^ (1 - η) *
        (C ^ η * (t : ℝ) ^ (-((m : ℝ) + 1) * η) * Real.exp (ω * t) ^ η)
      = (C ^ (1 - η) * C ^ η) * ((t : ℝ) ^ (-(m : ℝ) * (1 - η)) *
          (t : ℝ) ^ (-((m : ℝ) + 1) * η)) *
            (Real.exp (ω * t) ^ (1 - η) * Real.exp (ω * t) ^ η) := by ring
    _ = C * (t : ℝ) ^ (-(σ₂ - σ₁)) * Real.exp (ω * t) := by rw [hCC, hEE, htt]

end NavierStokes.Selfsimilar
