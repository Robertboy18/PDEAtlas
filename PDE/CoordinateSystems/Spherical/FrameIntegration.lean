/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.AxisymmetricIntegration
public import PDE.CoordinateSystems.Spherical.Frame
import PDE.CoordinateSystems.Spherical.Axisymmetric

/-!
# Ball integrals of axisymmetric pairings in the spherical frame

For vector fields `u`, `v` equivariant under the rotations about the symmetry axis, the
pairing `⟪u x, v x⟫` is invariant, so its integral over the ball `B(0, R)` reduces to the
meridian half-plane: `2π ∫₀ᴿ ∫₀^π ⟪u, v⟫ (r, θ, 0) r² sin θ dθ dr`. When the fields have
frame coefficients `c`, `d` on the meridian, `u (point r θ 0) = ∑ᵢ c r θ i • frame θ 0 i`, the
pairing is `∑ᵢ cᵢ dᵢ` by orthonormality of the frame (`integral_ball_inner_eq_frame`).

The radial reduction `setIntegral_ball_eq_intervalIntegral` writes a ball integral of an
axisymmetric integrable function with a smooth radial profile `f`,
`r² ∫₀^π F (point r θ 0) sin θ dθ = f r` for `0 < r < R`, as `2π ∫₀ᴿ f`.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open MeasureTheory Set Metric Real
open scoped RealInnerProductSpace

/-- Two functions that agree on `(a, b)` have the same interval integral over `[a, b]`. -/
theorem intervalIntegral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Ioo a b, f x = g x) : ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- The pairing of two equivariant vector fields is invariant under the rotations about the
symmetry axis. -/
theorem isInvariantUnderAxisRotation_inner {u v : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u) (hv : IsEquivariantUnderAxisRotation v) :
    IsInvariantUnderAxisRotation fun x ↦ ⟪u x, v x⟫ := by
  intro φ x
  simp only [hu φ x, hv φ x, inner_axisRotation_axisRotation]

/-- The pairing of two vectors given by coefficients in the orthonormal spherical frame. -/
theorem inner_sum_frame (θ φ : ℝ) (c d : Fin 3 → ℝ) :
    ⟪∑ i, c i • frame θ φ i, ∑ i, d i • frame θ φ i⟫ = ∑ i, c i * d i := by
  rw [(orthonormal_frame θ φ).inner_sum c d Finset.univ]
  simp

/-- The ball integral of an axisymmetric integrable function whose meridian profile
`r² ∫₀^π F (point r θ 0) sin θ dθ` agrees on `(0, R)` with `f`: `∫_{B(0, R)} F = 2π ∫₀ᴿ f`. -/
theorem setIntegral_ball_eq_intervalIntegral {F : ℝ^3 → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hrot : IsInvariantUnderAxisRotation F) (hF : IntegrableOn F (ball 0 R)) (f : ℝ → ℝ)
    (hf : ∀ r ∈ Ioo 0 R, r ^ 2 * ∫ θ in (0 : ℝ)..π, F (point r θ 0) * sin θ = f r) :
    ∫ x in ball (0 : ℝ^3) R, F x = 2 * π * ∫ r in (0 : ℝ)..R, f r := by
  rw [setIntegral_ball_of_axisymmetric hrot hF, intervalIntegral.integral_of_le hR,
    integral_Ioc_eq_integral_Ioo]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
  rw [← hf r hr, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun θ _ ↦ by ring

/-- The ball integral of the pairing of two equivariant vector fields with frame coefficients
`c`, `d` on the meridian: `∫_{B(0, R)} ⟪u, v⟫ = 2π ∫₀ᴿ r² ∫₀^π (∑ᵢ cᵢ dᵢ) sin θ dθ dr`. -/
theorem integral_ball_inner_eq_frame {u v : ℝ^3 → ℝ^3} {R : ℝ} (hR : 0 ≤ R)
    (hu : IsEquivariantUnderAxisRotation u) (hv : IsEquivariantUnderAxisRotation v)
    (hint : IntegrableOn (fun x ↦ ⟪u x, v x⟫) (ball 0 R)) (c d : ℝ → ℝ → Fin 3 → ℝ)
    (hc : ∀ r ∈ Ioo 0 R, ∀ θ ∈ Ioo 0 π, u (point r θ 0) = ∑ i, c r θ i • frame θ 0 i)
    (hd : ∀ r ∈ Ioo 0 R, ∀ θ ∈ Ioo 0 π, v (point r θ 0) = ∑ i, d r θ i • frame θ 0 i) :
    ∫ x in ball (0 : ℝ^3) R, ⟪u x, v x⟫ =
      2 * π * ∫ r in (0 : ℝ)..R, r ^ 2 * ∫ θ in (0 : ℝ)..π, (∑ i, c r θ i * d r θ i) * sin θ :=
  setIntegral_ball_eq_intervalIntegral hR (isInvariantUnderAxisRotation_inner hu hv) hint _
    fun r hr ↦ by
      congr 1
      refine intervalIntegral_congr_Ioo pi_pos.le fun θ hθ ↦ ?_
      rw [hc r hr θ hθ, hd r hr θ hθ, inner_sum_frame]

end PDE.CoordinateSystems.Spherical
