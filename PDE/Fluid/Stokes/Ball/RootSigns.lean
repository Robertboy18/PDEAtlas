/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RootFunctions
public import PDE.Analysis.SpecialFunctions.SphericalBessel.NatGrid

/-!
# Certified signs of the boundary functions at dyadic points

At a point `x = n / 2 ^ 40` the grid series of `sphericalBesselNatGridBounds` encloses
`G_l = (2l + 1)‼ g_l x` and `G_{l+1} = (2l + 3)‼ g_{l+1} x`, scaled by `2 ^ p (-1) ^ K`. The
boundary functions are combinations of the two:

* `(2l + 3)‼ 2 ^ 80 b_Z = l (2l + 3) 2 ^ 80 G_l - n² G_{l+1}`,
* `(2l + 3)‼ 2 ^ 80 b_Y = ((l - 1)(2l + 1) 2 ^ 80 - n²)(2l + 3) G_l + (n² - γ² 2 ^ 80) G_{l+1}`,

with `γ² = l (l - 1)(l + 2)`. `rootPointSigns l n` returns the signs of `j_l x`, `j_{l+1} x`,
the meridional and the azimuthal boundary function at `x`, each `1`, `-1`, or `0` when the
enclosure does not decide it; `rootPointSigns_sound` proves every decided sign. The precision
is `p = 4 ⌊x⌋ / 3 + 64` bits and the series has `K = 5 ⌊x⌋ / 4 + 32` terms.
-/

@[expose] public section

open PDE.Analysis.SpecialFunctions Nat

namespace PDE.Fluid.Stokes.Ball

/-- The grid precision used at the point `n / 2 ^ 40`. -/
def rootGridBits (n : ℕ) : ℕ := 4 * (n >>> 40) / 3 + 64

/-- The number of series terms used at the point `n / 2 ^ 40`. -/
def rootGridTerms (n : ℕ) : ℕ := 5 * (n >>> 40) / 4 + 32

/-- Interval bounds for `c₁ u + c₂ v` from bounds `I ∋ u` and `J ∋ v`. -/
def linBounds (c₁ c₂ : ℤ) (I J : ℤ × ℤ) : ℤ × ℤ :=
  (min (c₁ * I.1) (c₁ * I.2) + min (c₂ * J.1) (c₂ * J.2),
    max (c₁ * I.1) (c₁ * I.2) + max (c₂ * J.1) (c₂ * J.2))

/-- The sign decided by an interval: `1` if it is positive, `-1` if it is negative, `0`
otherwise. -/
def intervalSign (I : ℤ × ℤ) : ℤ :=
  if 0 < I.1 then 1 else if I.2 < 0 then -1 else 0

/-- `linBounds c₁ c₂ I J` contains `c₁ u + c₂ v` for `u ∈ I` and `v ∈ J`. -/
theorem linBounds_sound {c₁ c₂ : ℤ} {I J : ℤ × ℤ} {u v : ℝ} (hu : (I.1 : ℝ) ≤ u ∧ u ≤ I.2)
    (hv : (J.1 : ℝ) ≤ v ∧ v ≤ J.2) :
    ((linBounds c₁ c₂ I J).1 : ℝ) ≤ c₁ * u + c₂ * v ∧
      c₁ * u + c₂ * v ≤ (linBounds c₁ c₂ I J).2 := by
  have key : ∀ (c : ℤ) (K : ℤ × ℤ) (w : ℝ), (K.1 : ℝ) ≤ w → w ≤ K.2 →
      ((min (c * K.1) (c * K.2) : ℤ) : ℝ) ≤ c * w ∧
        c * w ≤ ((max (c * K.1) (c * K.2) : ℤ) : ℝ) := by
    intro c K w h₁ h₂
    push_cast
    rcases le_total 0 (c : ℝ) with hc | hc
    · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left h₁ hc),
        le_max_of_le_right (mul_le_mul_of_nonneg_left h₂ hc)⟩
    · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left h₂ hc),
        le_max_of_le_left (mul_le_mul_of_nonpos_left h₁ hc)⟩
  obtain ⟨a₁, a₂⟩ := key c₁ I u hu.1 hu.2
  obtain ⟨b₁, b₂⟩ := key c₂ J v hv.1 hv.2
  simp only [linBounds]
  push_cast at a₁ a₂ b₁ b₂ ⊢
  constructor <;> linarith

/-- A decided sign of an interval is the sign of each of its points. -/
theorem intervalSign_sound {I : ℤ × ℤ} {w : ℝ} (hw : (I.1 : ℝ) ≤ w ∧ w ≤ I.2)
    (h : intervalSign I ≠ 0) : 0 < (intervalSign I : ℝ) * w := by
  unfold intervalSign at h ⊢
  split_ifs at h ⊢ with h₁ h₂
  · have : (0 : ℝ) < I.1 := by exact_mod_cast h₁
    simp only [Int.cast_one, one_mul]
    linarith [hw.1]
  · have : (I.2 : ℝ) < 0 := by exact_mod_cast h₂
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_pos]
    linarith [hw.2]
  · exact absurd rfl h

/-- `(-1) ^ K` as an integer. -/
def parityFactor (K : ℕ) : ℤ := if K % 2 = 0 then 1 else -1

/-- `parityFactor K` is `(-1) ^ K`. -/
theorem parityFactor_cast (K : ℕ) : (parityFactor K : ℝ) = (-1) ^ K := by
  unfold parityFactor
  rcases Nat.even_or_odd K with he | ho
  · rw [ite_eq_left_iff.mpr (fun h ↦ absurd (Nat.even_iff.mp he) h), he.neg_one_pow]; simp
  · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by rw [Nat.odd_iff.mp ho]; norm_num)),
      ho.neg_one_pow]
    simp

/-- The four signs from the enclosures `I ∋ 2 ^ p σ G_l` and `J ∋ 2 ^ p σ G_{l+1}`. -/
def rootSignsOf (l n : ℕ) (σ : ℤ) (I J : ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (σ * intervalSign I, σ * intervalSign J,
    σ * intervalSign (linBounds ((((l : ℤ) - 1) * (2 * l + 1) * 2 ^ 80 - n * n) * (2 * l + 3))
      (n * n - l * ((l : ℤ) - 1) * (l + 2) * 2 ^ 80) I J),
    σ * intervalSign (linBounds (l * (2 * l + 3) * 2 ^ 80) (-(n * n)) I J))

/-- The signs of `g_l x`, `g_{l+1} x`, the meridional and the azimuthal boundary function of
degree `l` at `x = n / 2 ^ 40`, each decided by the grid series or `0`. -/
def rootPointSigns (l n : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  if Nat.ble (n * n) (2 ^ 81 * (rootGridTerms n + 1) * (2 * l + 2 * rootGridTerms n + 3)) then
    match sphericalBesselNatGridBounds (rootGridBits n) l (n * n) 81 (rootGridTerms n),
      sphericalBesselNatGridBounds (rootGridBits n) (l + 1) (n * n) 81 (rootGridTerms n) with
    | (a, b), (c, d) => rootSignsOf l n (parityFactor (rootGridTerms n)) (a, b) (c, d)
  else (0, 0, 0, 0)

/-- The double factorial `(2l + 3)‼ = (2l + 3) (2l + 1)‼` as reals. -/
theorem doubleFactorial_two_mul_add_three (l : ℕ) :
    (((2 * l + 3)‼ : ℕ) : ℝ) = (2 * l + 3) * ((2 * l + 1)‼ : ℕ) := by
  rw [show 2 * l + 3 = 2 * l + 1 + 2 by ring, Nat.doubleFactorial_add_two]
  push_cast
  ring

/-- A decided interval for `2 ^ p σ w` with `σ = ±1` gives the sign of `w`. -/
theorem sign_of_interval {c : ℤ × ℤ} {P σ w : ℝ} (hP : 0 < P)
    (hw : (c.1 : ℝ) ≤ P * σ * w ∧ P * σ * w ≤ c.2) (hne : intervalSign c ≠ 0) :
    0 < σ * intervalSign c * w := by
  have h := intervalSign_sound hw hne
  have : (intervalSign c : ℝ) * (P * σ * w) = P * (σ * intervalSign c * w) := by ring
  rw [this] at h
  exact (mul_pos_iff_of_pos_left hP).mp h

/-- A decided interval for `2 ^ p σ (a w)` with `a > 0` gives the sign of `w`. -/
theorem sign_of_interval_mul {c : ℤ × ℤ} {P σ a w : ℝ} (hP : 0 < P) (ha : 0 < a)
    (hw : (c.1 : ℝ) ≤ P * σ * (a * w) ∧ P * σ * (a * w) ≤ c.2) (hne : intervalSign c ≠ 0) :
    0 < σ * intervalSign c * w := by
  have h := sign_of_interval hP hw hne
  rw [mul_left_comm] at h
  exact (mul_pos_iff_of_pos_left ha).mp h

/-- Every sign decided by `rootPointSigns l n` is the sign of `g_l`, `g_{l+1}`, the meridional
or the azimuthal boundary function at `x = n / 2 ^ 40`. -/
theorem rootPointSigns_sound (l n : ℕ) :
    ((rootPointSigns l n).1 ≠ 0 →
        0 < ((rootPointSigns l n).1 : ℝ) * reducedSphericalBesselJ l (n / 2 ^ 40)) ∧
      ((rootPointSigns l n).2.1 ≠ 0 →
        0 < ((rootPointSigns l n).2.1 : ℝ) * reducedSphericalBesselJ (l + 1) (n / 2 ^ 40)) ∧
      ((rootPointSigns l n).2.2.1 ≠ 0 →
        0 < ((rootPointSigns l n).2.2.1 : ℝ) * boundaryFunction .meridional l (n / 2 ^ 40)) ∧
      ((rootPointSigns l n).2.2.2 ≠ 0 →
        0 < ((rootPointSigns l n).2.2.2 : ℝ) * boundaryFunction .azimuthal l (n / 2 ^ 40)) := by
  set x : ℝ := n / 2 ^ 40 with hxdef
  set p := rootGridBits n
  set K := rootGridTerms n
  by_cases hble : Nat.ble (n * n) (2 ^ 81 * (K + 1) * (2 * l + 2 * K + 3)) = true
  swap
  · have h0 : rootPointSigns l n = (0, 0, 0, 0) := by
      unfold rootPointSigns
      simp only [K] at hble
      simp only [hble, Bool.false_eq_true, ite_false]
    simp [h0]
  set I := sphericalBesselNatGridBounds p l (n * n) 81 K with hIdef
  set J := sphericalBesselNatGridBounds p (l + 1) (n * n) 81 K with hJdef
  have hS : rootPointSigns l n = rootSignsOf l n (parityFactor K) I J := by
    unfold rootPointSigns
    simp only [K] at hble
    simp only [hble, ite_true]
    rcases hI : sphericalBesselNatGridBounds p l (n * n) 81 K with ⟨a, b⟩
    rcases hJ : sphericalBesselNatGridBounds p (l + 1) (n * n) 81 K with ⟨c, d⟩
    rw [hIdef, hJdef, hI, hJ]
  rw [hS]
  have hle : n * n ≤ 2 ^ 81 * (K + 1) * (2 * l + 2 * K + 3) := Nat.le_of_ble_eq_true hble
  have hx2 : x ^ 2 = (n * n : ℕ) / 2 ^ 80 := by
    rw [hxdef]; push_cast; ring
  have hx : x ^ 2 / 2 = ((n * n : ℕ) : ℝ) / 2 ^ 81 := by
    rw [hx2]; ring
  have hleR : ((n * n : ℕ) : ℝ) ≤ 2 ^ 81 * (K + 1) * (2 * l + 2 * K + 3) := by
    exact_mod_cast hle
  have hK : x ^ 2 ≤ 2 * (K + 1) * (2 * l + 2 * K + 3) := by
    rw [hx2, div_le_iff₀ (by positivity)]
    nlinarith
  have hK' : x ^ 2 ≤ 2 * (K + 1) * (2 * ((l + 1 : ℕ) : ℝ) + 2 * K + 3) := by
    refine hK.trans ?_
    push_cast
    gcongr
    linarith
  obtain ⟨hI₁, hI₂⟩ := sphericalBesselNatGridBounds_sound p l (n * n) 81 K hx hK
  obtain ⟨hJ₁, hJ₂⟩ := sphericalBesselNatGridBounds_sound p (l + 1) (n * n) 81 K hx hK'
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
  have hD₃ : 0 < (2 * (l : ℝ) + 3) * D₁ * 2 ^ 80 := by positivity
  have hn : ((n : ℝ) * n) = 2 ^ 80 * x ^ 2 := by
    rw [hxdef]; ring
  simp only [rootSignsOf, Int.cast_mul]
  rw [hσc]
  refine ⟨fun hne ↦ ?_, fun hne ↦ ?_, fun hne ↦ ?_, fun hne ↦ ?_⟩
  · exact sign_of_interval_mul hPpos hD₁ hu (right_ne_zero_of_mul hne)
  · exact sign_of_interval_mul hPpos (by positivity) hv (right_ne_zero_of_mul hne)
  · have hne' := right_ne_zero_of_mul hne
    have hlin := linBounds_sound (c₁ := (((l : ℤ) - 1) * (2 * l + 1) * 2 ^ 80 - n * n) *
      (2 * l + 3)) (c₂ := n * n - l * ((l : ℤ) - 1) * (l + 2) * 2 ^ 80) hu hv
    have hid : ((((((l : ℤ) - 1) * (2 * l + 1) * 2 ^ 80 - n * n) * (2 * l + 3) : ℤ) : ℝ)) *
        (P * σ * (D₁ * g₀)) + (((n * n - l * ((l : ℤ) - 1) * (l + 2) * 2 ^ 80 : ℤ) : ℝ)) *
        (P * σ * ((2 * l + 3) * D₁ * g₁)) =
        P * σ * ((2 * l + 3) * D₁ * 2 ^ 80 * boundaryFunction .meridional l x) := by
      simp only [boundaryFunction]
      push_cast
      rw [hn]
      ring
    rw [hid] at hlin
    exact sign_of_interval_mul hPpos hD₃ hlin hne'
  · have hne' := right_ne_zero_of_mul hne
    have hlin := linBounds_sound (c₁ := l * (2 * l + 3) * 2 ^ 80) (c₂ := -(n * n)) hu hv
    have hid : (((l * (2 * l + 3) * 2 ^ 80 : ℤ) : ℝ)) * (P * σ * (D₁ * g₀)) +
        (((-(n * n) : ℤ) : ℝ)) * (P * σ * ((2 * l + 3) * D₁ * g₁)) =
        P * σ * ((2 * l + 3) * D₁ * 2 ^ 80 * boundaryFunction .azimuthal l x) := by
      simp only [boundaryFunction]
      push_cast
      rw [hn]
      ring
    rw [hid] at hlin
    exact sign_of_interval_mul hPpos hD₃ hlin hne'

end PDE.Fluid.Stokes.Ball
