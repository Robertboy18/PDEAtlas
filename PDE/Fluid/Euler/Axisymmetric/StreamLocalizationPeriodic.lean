/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.StreamRegularityPeriodic
public import PDE.Common.Euclidean.CoordinateReflection

/-!
# Periodization of planar functions in the first coordinate

For `F : ℝ² → ℝ` vanishing where `|x₀| > a` with `a < L/2`, the `L`-periodization in the
coordinate `x₀`, `periodizeTangential hL F x = F(x₀ mod L, x₁)` with the representative of `x₀`
in `[-L/2, L/2)`, is `L`-periodic in `x₀` (`periodizeTangential_add`), agrees with `F` near every
point with `|x₀| < L/2` (`periodizeTangential_eventuallyEq`), is as smooth as `F`
(`contDiff_periodizeTangential`) and odd under `x₀ ↦ -x₀` when `F` is
(`periodizeTangential_reflect`). It is `periodizeZ` of the profile with the coordinates
exchanged.

## Main definitions

* `periodizeTangential`: the `L`-periodization `F(x₀ mod L, x₁)` of `F` in the coordinate `x₀`.

## Main results

* `periodizeTangential_add`: the periodization is `L`-periodic in `x₀`.
* `periodizeTangential_of_abs_lt`: it agrees with `F` where `|x₀| < L/2`.
* `periodizeTangential_eventuallyEq`: near every point with `|x₀| < L/2` it is `F`.
* `contDiff_periodizeTangential`: the periodization of a `Cⁿ` function vanishing where
  `|x₀| > a`, `a < L/2`, is `Cⁿ`.
* `periodizeTangential_reflect`: the periodization of a function odd under `x₀ ↦ -x₀` is odd.
-/

@[expose] public section

namespace Euler.Cylinder

open Set Filter PDE.Common
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- The `L`-periodization of `F` in the coordinate `x₀`: `F(x₀ mod L, x₁)` with the
representative of `x₀` in `[-L/2, L/2)`. -/
def periodizeTangential {L : ℝ} (hL : 0 < L) (F : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  F (WithLp.toLp 2 ![toIcoMod hL (-(L / 2)) (x 0), x 1])

variable {L : ℝ} (hL : 0 < L) {F : ℝ^2 → ℝ} {a : ℝ}

/-- The profile of `F` with the coordinates exchanged, `(s, z) ↦ F(z, s)`. -/
private def swapProfile (F : ℝ^2 → ℝ) (q : ℝ × ℝ) : ℝ :=
  F (WithLp.toLp 2 ![q.2, q.1])

/-- The tangential periodization of `F` is the axial periodization of the swapped profile, read at
the swapped point. -/
private theorem periodizeTangential_eq (x : ℝ^2) :
    periodizeTangential hL F x = periodizeZ hL (swapProfile F) (x 1, x 0) := rfl

/-- The periodization is `L`-periodic in `x₀`. -/
theorem periodizeTangential_add (x : ℝ^2) :
    periodizeTangential hL F (x + EuclideanSpace.single 0 L) = periodizeTangential hL F x := by
  simp [periodizeTangential, toIcoMod_add_right]

/-- The periodization agrees with `F` where `|x₀| < L/2`. -/
theorem periodizeTangential_of_abs_lt {x : ℝ^2} (hx : |x 0| < L / 2) :
    periodizeTangential hL F x = F x := by
  simp only [periodizeTangential]
  rw [(toIcoMod_eq_self hL).2 ⟨by linarith [(abs_lt.1 hx).1], by linarith [(abs_lt.1 hx).2]⟩]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Near every point with `|x₀| < L/2` the periodization is `F`. -/
theorem periodizeTangential_eventuallyEq {x : ℝ^2} (hx : |x 0| < L / 2) :
    periodizeTangential hL F =ᶠ[𝓝 x] F := by
  have hopen : IsOpen {y : ℝ^2 | |y 0| < L / 2} :=
    isOpen_lt (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous)
      continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact periodizeTangential_of_abs_lt hL hy

/-- The value of the periodization is a value of `F` at a point with the same second
coordinate. -/
theorem exists_periodizeTangential_eq (x : ℝ^2) :
    ∃ x' : ℝ^2, x' 1 = x 1 ∧ periodizeTangential hL F x = F x' :=
  ⟨WithLp.toLp 2 ![toIcoMod hL (-(L / 2)) (x 0), x 1], by simp, rfl⟩

/-- The periodization of a `Cⁿ` function vanishing where `|x₀| > a`, `a < L/2`, is `Cⁿ`. -/
theorem contDiff_periodizeTangential {n : WithTop ℕ∞} (hF : ∀ x : ℝ^2, a < |x 0| → F x = 0)
    (ha0 : 0 ≤ a) (ha : a < L / 2) (hFc : ContDiff ℝ n F) :
    ContDiff ℝ n (periodizeTangential hL F) := by
  set e : ℝ × ℝ →L[ℝ] ℝ^2 := (pointPairEquiv.symm : ℝ × ℝ →L[ℝ] ℝ^2).comp
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ × ℝ)
  set g : ℝ^2 →L[ℝ] ℝ × ℝ := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ : ℝ × ℝ →L[ℝ] ℝ × ℝ).comp
    (pointPairEquiv : ℝ^2 →L[ℝ] ℝ × ℝ)
  have he : swapProfile F = F ∘ e := by
    funext q
    obtain ⟨s, z⟩ := q
    simp only [swapProfile, e, Function.comp_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk,
      pointPairEquiv_symm_apply]
  have hg : periodizeTangential hL F = periodizeZ hL (swapProfile F) ∘ g := by
    funext x
    simp [periodizeTangential_eq, g, pointPairEquiv_apply]
  have hG : ∀ s z, a < |z| → swapProfile F (s, z) = 0 := fun s z hz ↦
    hF _ (by simpa using hz)
  have hGc : ContDiff ℝ n (swapProfile F) := he ▸ hFc.comp e.contDiff
  rw [hg]
  exact (contDiff_periodizeZ hL hG ha0 ha hGc).comp g.contDiff

/-- The periodization of a function odd under `x₀ ↦ -x₀` and vanishing where `|x₀| > a`,
`a < L/2`, is odd. -/
theorem periodizeTangential_reflect (hF : ∀ x : ℝ^2, a < |x 0| → F x = 0) (ha : a < L / 2)
    (hodd : ∀ x, F (coordinateReflection (0 : Fin 2) x) = -F x) (x : ℝ^2) :
    periodizeTangential hL F (coordinateReflection (0 : Fin 2) x) =
      -periodizeTangential hL F x := by
  have hG : ∀ s z, a < |z| → swapProfile F (s, z) = 0 := fun s z hz ↦
    hF _ (by simpa using hz)
  have hGodd : ∀ s z, swapProfile F (s, -z) = -swapProfile F (s, z) := by
    intro s z
    have h := hodd (WithLp.toLp 2 ![z, s])
    have hpt : coordinateReflection (0 : Fin 2) (WithLp.toLp 2 ![z, s]) =
        (WithLp.toLp 2 ![-z, s] : ℝ^2) := by
      ext i
      fin_cases i <;> simp [coordinateReflection_apply_same]
    rw [hpt] at h
    exact h
  rw [periodizeTangential_eq, periodizeTangential_eq]
  have h0 : (coordinateReflection (0 : Fin 2) x) 0 = -x 0 := coordinateReflection_apply_same _ _
  have h1 : (coordinateReflection (0 : Fin 2) x) 1 = x 1 :=
    coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by decide) x
  rw [h0, h1]
  exact periodizeZ_neg hL hG ha hGodd (x 1) (x 0)

end

end Euler.Cylinder
