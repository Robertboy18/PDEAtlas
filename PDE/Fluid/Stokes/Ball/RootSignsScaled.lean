/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RootSigns

/-!
# Certified signs of the boundary functions at dyadic points of any scale

`rootPointSignsAt E p K l n` decides the signs of `g_l x`, `g_{l+1} x`, the meridional and the
azimuthal boundary function of degree `l` at `x = n / 2 ^ E` from the grid series of
`sphericalBesselNatGridBounds` with precision `p` and `K` terms, exactly as `rootPointSigns` does
at the scale `2 ^ 40`; a sign is `0` when the enclosure does not decide it, and
`rootPointSignsAt_sound` proves every decided sign. Points closer to a root need a finer scale and
more precision than the fixed choice of `rootPointSigns`.
-/

@[expose] public section

open PDE.Analysis.SpecialFunctions Nat

namespace PDE.Fluid.Stokes.Ball

/-- The four signs from the enclosures `I ∋ 2 ^ p σ G_l` and `J ∋ 2 ^ p σ G_{l+1}` at
`x = n / 2 ^ E`. -/
def rootSignsAtOf (E l n : ℕ) (σ : ℤ) (I J : ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (σ * intervalSign I, σ * intervalSign J,
    σ * intervalSign (linBounds ((((l : ℤ) - 1) * (2 * l + 1) * 2 ^ (2 * E) - n * n) *
      (2 * l + 3)) (n * n - l * ((l : ℤ) - 1) * (l + 2) * 2 ^ (2 * E)) I J),
    σ * intervalSign (linBounds (l * (2 * l + 3) * 2 ^ (2 * E)) (-(n * n)) I J))

/-- The signs of `g_l`, `g_{l+1}`, the meridional and the azimuthal boundary function of degree
`l` at `x = n / 2 ^ E`, from the grid series with precision `p` and `K` terms. -/
def rootPointSignsAt (E p K l n : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  if Nat.ble (n * n) (2 ^ (2 * E + 1) * (K + 1) * (2 * l + 2 * K + 3)) then
    match sphericalBesselNatGridBounds p l (n * n) (2 * E + 1) K,
      sphericalBesselNatGridBounds p (l + 1) (n * n) (2 * E + 1) K with
    | (a, b), (c, d) => rootSignsAtOf E l n (parityFactor K) (a, b) (c, d)
  else (0, 0, 0, 0)

/-- Every sign decided by `rootPointSignsAt E p K l n` is the sign of `g_l`, `g_{l+1}`, the
meridional or the azimuthal boundary function at `x = n / 2 ^ E`. -/
theorem rootPointSignsAt_sound (E p K l n : ℕ) :
    ((rootPointSignsAt E p K l n).1 ≠ 0 →
        0 < ((rootPointSignsAt E p K l n).1 : ℝ) * reducedSphericalBesselJ l (n / 2 ^ E)) ∧
      ((rootPointSignsAt E p K l n).2.1 ≠ 0 →
        0 < ((rootPointSignsAt E p K l n).2.1 : ℝ) *
          reducedSphericalBesselJ (l + 1) (n / 2 ^ E)) ∧
      ((rootPointSignsAt E p K l n).2.2.1 ≠ 0 →
        0 < ((rootPointSignsAt E p K l n).2.2.1 : ℝ) *
          boundaryFunction .meridional l (n / 2 ^ E)) ∧
      ((rootPointSignsAt E p K l n).2.2.2 ≠ 0 →
        0 < ((rootPointSignsAt E p K l n).2.2.2 : ℝ) *
          boundaryFunction .azimuthal l (n / 2 ^ E)) := by
  set x : ℝ := n / 2 ^ E with hxdef
  by_cases hble : Nat.ble (n * n) (2 ^ (2 * E + 1) * (K + 1) * (2 * l + 2 * K + 3)) = true
  swap
  · have h0 : rootPointSignsAt E p K l n = (0, 0, 0, 0) := by
      unfold rootPointSignsAt
      simp only [hble, Bool.false_eq_true, ite_false]
    simp [h0]
  set I := sphericalBesselNatGridBounds p l (n * n) (2 * E + 1) K with hIdef
  set J := sphericalBesselNatGridBounds p (l + 1) (n * n) (2 * E + 1) K with hJdef
  have hS : rootPointSignsAt E p K l n = rootSignsAtOf E l n (parityFactor K) I J := by
    unfold rootPointSignsAt
    simp only [hble, ite_true]
    rcases hI : sphericalBesselNatGridBounds p l (n * n) (2 * E + 1) K with ⟨a, b⟩
    rcases hJ : sphericalBesselNatGridBounds p (l + 1) (n * n) (2 * E + 1) K with ⟨c, d⟩
    rw [hIdef, hJdef, hI, hJ]
  rw [hS]
  have hle : n * n ≤ 2 ^ (2 * E + 1) * (K + 1) * (2 * l + 2 * K + 3) :=
    Nat.le_of_ble_eq_true hble
  have hE : (2 : ℝ) ^ (2 * E) = (2 ^ E) ^ 2 := by rw [← pow_mul, mul_comm]
  have hx2 : x ^ 2 = (n * n : ℕ) / 2 ^ (2 * E) := by
    rw [hxdef, hE]; push_cast; ring
  have hx : x ^ 2 / 2 = ((n * n : ℕ) : ℝ) / 2 ^ (2 * E + 1) := by
    rw [hx2, pow_succ]; ring
  have hleR : ((n * n : ℕ) : ℝ) ≤ 2 ^ (2 * E + 1) * (K + 1) * (2 * l + 2 * K + 3) := by
    exact_mod_cast hle
  have hK : x ^ 2 ≤ 2 * (K + 1) * (2 * l + 2 * K + 3) := by
    rw [hx2, div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ (2 * E + 1) = 2 * 2 ^ (2 * E) := by rw [pow_succ]; ring
    rw [this] at hleR
    nlinarith
  have hK' : x ^ 2 ≤ 2 * (K + 1) * (2 * ((l + 1 : ℕ) : ℝ) + 2 * K + 3) := by
    refine hK.trans ?_
    push_cast
    gcongr
    linarith
  obtain ⟨hI₁, hI₂⟩ := sphericalBesselNatGridBounds_sound p l (n * n) (2 * E + 1) K hx hK
  obtain ⟨hJ₁, hJ₂⟩ := sphericalBesselNatGridBounds_sound p (l + 1) (n * n) (2 * E + 1) K hx hK'
  rw [← hIdef] at hI₁ hI₂
  rw [← hJdef] at hJ₁ hJ₂
  set σ : ℝ := (-1) ^ K with hσdef
  have hσc : (parityFactor K : ℝ) = σ := parityFactor_cast K
  set P : ℝ := 2 ^ p with hP
  have hPpos : 0 < P := by positivity
  set D₁ : ℝ := (((2 * l + 1)‼ : ℕ) : ℝ) with hD₁def
  have hD₁ : 0 < D₁ := Nat.cast_pos.2 (Nat.doubleFactorial_pos _)
  have hD₂eq : (((2 * (l + 1) + 1)‼ : ℕ) : ℝ) = (2 * l + 3) * D₁ := by
    rw [show 2 * (l + 1) + 1 = 2 * l + 3 by ring]
    exact doubleFactorial_two_mul_add_three l
  rw [hD₂eq] at hJ₁ hJ₂
  set g₀ := reducedSphericalBesselJ l x
  set g₁ := reducedSphericalBesselJ (l + 1) x
  have hu : (I.1 : ℝ) ≤ P * σ * (D₁ * g₀) ∧ P * σ * (D₁ * g₀) ≤ I.2 :=
    ⟨by linarith [show P * D₁ * (σ * g₀) = P * σ * (D₁ * g₀) by ring],
      by linarith [show P * D₁ * (σ * g₀) = P * σ * (D₁ * g₀) by ring]⟩
  have hv : (J.1 : ℝ) ≤ P * σ * ((2 * l + 3) * D₁ * g₁) ∧
      P * σ * ((2 * l + 3) * D₁ * g₁) ≤ J.2 :=
    have e : P * ((2 * l + 3) * D₁) * (σ * g₁) = P * σ * ((2 * l + 3) * D₁ * g₁) := by ring
    ⟨by linarith, by linarith⟩
  have hD₃ : 0 < (2 * (l : ℝ) + 3) * D₁ * 2 ^ (2 * E) := by positivity
  have hn : ((n : ℝ) * n) = 2 ^ (2 * E) * x ^ 2 := by
    rw [hx2]; field_simp; push_cast; ring
  simp only [rootSignsAtOf, Int.cast_mul]
  rw [hσc]
  refine ⟨fun hne ↦ ?_, fun hne ↦ ?_, fun hne ↦ ?_, fun hne ↦ ?_⟩
  · exact sign_of_interval_mul hPpos hD₁ hu (right_ne_zero_of_mul hne)
  · exact sign_of_interval_mul hPpos (by positivity) hv (right_ne_zero_of_mul hne)
  · have hne' := right_ne_zero_of_mul hne
    set c₁ : ℤ := (((l : ℤ) - 1) * (2 * l + 1) * 2 ^ (2 * E) - n * n) * (2 * l + 3)
    set c₂ : ℤ := n * n - l * ((l : ℤ) - 1) * (l + 2) * 2 ^ (2 * E)
    have hlin := linBounds_sound (c₁ := c₁) (c₂ := c₂) hu hv
    have hid : (c₁ : ℝ) * (P * σ * (D₁ * g₀)) + (c₂ : ℝ) * (P * σ * ((2 * l + 3) * D₁ * g₁)) =
        P * σ * ((2 * l + 3) * D₁ * 2 ^ (2 * E) * boundaryFunction .meridional l x) := by
      simp only [boundaryFunction, c₁, c₂]
      push_cast
      rw [hn]
      ring
    rw [hid] at hlin
    exact sign_of_interval_mul hPpos hD₃ hlin hne'
  · have hne' := right_ne_zero_of_mul hne
    set c₁ : ℤ := l * (2 * l + 3) * 2 ^ (2 * E)
    set c₂ : ℤ := -(n * n)
    have hlin := linBounds_sound (c₁ := c₁) (c₂ := c₂) hu hv
    have hid : (c₁ : ℝ) * (P * σ * (D₁ * g₀)) + (c₂ : ℝ) * (P * σ * ((2 * l + 3) * D₁ * g₁)) =
        P * σ * ((2 * l + 3) * D₁ * 2 ^ (2 * E) * boundaryFunction .azimuthal l x) := by
      simp only [boundaryFunction, c₁, c₂]
      push_cast
      rw [hn]
      ring
    rw [hid] at hlin
    exact sign_of_interval_mul hPpos hD₃ hlin hne'

end PDE.Fluid.Stokes.Ball
