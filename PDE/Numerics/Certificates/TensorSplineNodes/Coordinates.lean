/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.TensorSplineNodes.Field
public import PDE.FDeriv.PartialDeriv.WithinExtension
public import PDE.FDeriv.Polar.Profile
public import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# Mixed derivatives as coordinate derivatives in the plane

In the coordinates `E = pointPairEquiv.symm : ℝ × ℝ → ℝ²`, the coordinate
derivatives `∂₀ᵏ ∂₁ˡ h` of a function `h` that is `C^{k + l}` on an open set are the mixed
derivatives `mixedDeriv k l (h ∘ E)` there (`iterate_partialDeriv_eq_mixedDeriv`), and the
iterated partial derivative along any word `w` of length at most the regularity is the mixed
derivative with `w.count 0` derivatives in the first and `w.count 1` in the second variable
(`iteratedPartialDeriv_eq_mixedDeriv`). With `PDE.eqOn_iteratedPartialDerivWithin_of_eqOn` the
same holds for the derivatives within a set of unique differentiability of a function with a
`C^{|w|}` extension near the point (`iteratedPartialDerivWithin_eq_mixedDeriv`), including its
boundary points; for a function that is `C^{|w|}` at the point itself this is
`iteratedPartialDerivWithin_eq_mixedDeriv_of_contDiffAt`, and on the closed upper half-plane
`iteratedPartialDerivWithin_upper_eq_mixedDeriv`.

## Main results

* `iterate_partialDeriv_eq_mixedDeriv`: for `h` that is `C^{k + l}` on an open set containing
  `E (x, y)`, `∂₀ᵏ ∂₁ˡ h (E (x, y)) = mixedDeriv k l (h ∘ E) x y`.
* `iteratedPartialDeriv_eq_mixedDeriv`: for `h` that is `C^{|w|}` near `E (x, y)`, the iterated
  partial derivative along `w` is `mixedDeriv (w.count 0) (w.count 1) (h ∘ E) x y`.
* `iteratedPartialDerivWithin_eq_mixedDeriv`: the same for the derivatives within a set of
  unique differentiability of a function that agrees with a `C^{|w|}` function near the point.
* `iteratedPartialDerivWithin_eq_mixedDeriv_of_contDiffAt`: the same for a function that is
  `C^{|w|}` at the point.
* `iteratedPartialDerivWithin_upper_eq_mixedDeriv`: the same within the closed upper half-plane
  `{z | 0 ≤ z 1}` at points with `y ≥ 0`.
-/

@[expose] public section

open PDE.Common (pointPairEquiv)

namespace CAS.Numerics.TensorSpline

open Filter Set PDE PDE.FDeriv
open scoped Topology

/-- The first coordinate of `E (x, y)` is `x`. -/
theorem pointPair_symm_apply_zero (x y : ℝ) : (pointPairEquiv.symm (x, y)) 0 = x :=
  rfl

/-- The second coordinate of `E (x, y)` is `y`. -/
theorem pointPair_symm_apply_one (x y : ℝ) : (pointPairEquiv.symm (x, y)) 1 = y :=
  rfl

/-- The coordinate line in the first direction through `E (x, y)` passes through `E (t, y)` at
`t`. -/
theorem coordinateLine_zero_pointPair_symm (x y t : ℝ) :
    coordinateLine 0 (pointPairEquiv.symm (x, y)) t =
      pointPairEquiv.symm (t, y) := by
  ext i
  fin_cases i <;> simp [coordinateLine]

/-- The coordinate line in the second direction through `E (x, y)` passes through `E (x, t)` at
`t`. -/
theorem coordinateLine_one_pointPair_symm (x y t : ℝ) :
    coordinateLine 1 (pointPairEquiv.symm (x, y)) t =
      pointPairEquiv.symm (x, t) := by
  ext i
  fin_cases i <;> simp [coordinateLine]

variable {h : ℝ^2 → ℝ} {V : Set (ℝ^2)}

/-- **Coordinate derivatives as mixed derivatives.** For `h` that is `C^{k + l}` on an open set
containing `E (x, y)`, `∂₀ᵏ ∂₁ˡ h (E (x, y)) = mixedDeriv k l (h ∘ E) x y`. -/
theorem iterate_partialDeriv_eq_mixedDeriv (hV : IsOpen V) {k l : ℕ}
    (hh : ContDiffOn ℝ ((k + l : ℕ) : WithTop ℕ∞) h V) {x y : ℝ}
    (hxy : pointPairEquiv.symm (x, y) ∈ V) :
    ((fun g z ↦ (∂[(0 : Fin 2)] g) z)^[k] ((fun g z ↦ (∂[(1 : Fin 2)] g) z)^[l] h))
        (pointPairEquiv.symm (x, y)) =
      mixedDeriv k l (fun a b ↦ h (pointPairEquiv.symm (a, b))) x y := by
  set E := pointPairEquiv.symm
  have hG : ContDiffOn ℝ k ((fun g z ↦ (∂[(1 : Fin 2)] g) z)^[l] h) V := by
    have h' := contDiffOn_iteratedPartialDeriv hV (List.replicate l (1 : Fin 2)) (m := k)
      (by simpa [add_comm] using hh)
    rw [iteratedPartialDeriv_replicate] at h'
    exact h'
  rw [iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at 0 k
    (hG.contDiffAt (hV.mem_nhds hxy))]
  have hline : ((fun g z ↦ (∂[(1 : Fin 2)] g) z)^[l] h) ∘ coordinateLine 0 (E (x, y)) =
      fun t ↦ ((fun g z ↦ (∂[(1 : Fin 2)] g) z)^[l] h) (E (t, y)) := by
    funext t
    simp only [Function.comp_apply, E, coordinateLine_zero_pointPair_symm]
  rw [hline, pointPair_symm_apply_zero]
  unfold mixedDeriv
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hcont : Continuous fun t : ℝ ↦ E (t, y) := by fun_prop
  filter_upwards [hcont.continuousAt.preimage_mem_nhds (hV.mem_nhds hxy)] with t ht
  have hl : ContDiffAt ℝ l h (E (t, y)) :=
    (hh.contDiffAt (hV.mem_nhds ht)).of_le (by exact_mod_cast Nat.le_add_left l k)
  rw [iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at 1 l hl]
  have hline' : h ∘ coordinateLine 1 (E (t, y)) = fun s ↦ h (E (t, s)) := by
    funext s
    simp only [Function.comp_apply, E, coordinateLine_one_pointPair_symm]
  rw [hline', pointPair_symm_apply_one]

/-- **Words of coordinate derivatives as mixed derivatives.** For `h` that is `C^{|w|}` on an
open set containing `E (x, y)`, the iterated partial derivative along `w` at `E (x, y)` is
`mixedDeriv (w.count 0) (w.count 1) (h ∘ E) x y`. -/
theorem iteratedPartialDeriv_eq_mixedDeriv (hV : IsOpen V) (w : List (Fin 2))
    (hh : ContDiffOn ℝ w.length h V) {x y : ℝ}
    (hxy : pointPairEquiv.symm (x, y) ∈ V) :
    iteratedPartialDeriv w h (pointPairEquiv.symm (x, y)) =
      mixedDeriv (w.count 0) (w.count 1)
        (fun a b ↦ h (pointPairEquiv.symm (a, b))) x y := by
  have hp := perm_replicate_count_two w
  rw [eqOn_iteratedPartialDeriv_of_perm hV hp hh hxy, iteratedPartialDeriv_append,
    iteratedPartialDeriv_replicate]
  have hlen : w.length = w.count 0 + w.count 1 := by
    have := hp.length_eq
    simpa using this
  have hh' : ContDiffOn ℝ ((w.count 0 + w.count 1 : ℕ) : WithTop ℕ∞) h V := by
    rwa [← hlen]
  have hfun : (fun y ↦ iteratedPartialDeriv (List.replicate (w.count 1) 1) h y) =
      (fun g z ↦ (∂[(1 : Fin 2)] g) z)^[w.count 1] h := by
    rw [iteratedPartialDeriv_replicate]
  rw [hfun]
  exact iterate_partialDeriv_eq_mixedDeriv hV hh' hxy

/-- **Derivatives within a set as mixed derivatives.** If `f = h` on `s ∩ V`, `V` open, `s` has
unique derivatives and `h` is `C^{|w|}` on `V`, then at every `E (x, y) ∈ s ∩ V` the iterated
partial derivative of `f` within `s` along `w` is `mixedDeriv (w.count 0) (w.count 1) (h ∘ E)`. -/
theorem iteratedPartialDerivWithin_eq_mixedDeriv {f : ℝ^2 → ℝ} {s : Set (ℝ^2)} (hV : IsOpen V)
    (hs : UniqueDiffOn ℝ s) (w : List (Fin 2)) (hh : ContDiffOn ℝ w.length h V)
    (heq : EqOn f h (s ∩ V)) {x y : ℝ}
    (hxy : pointPairEquiv.symm (x, y) ∈ s ∩ V) :
    iteratedPartialDerivWithin w f s (pointPairEquiv.symm (x, y)) =
      mixedDeriv (w.count 0) (w.count 1)
        (fun a b ↦ h (pointPairEquiv.symm (a, b))) x y := by
  rw [eqOn_iteratedPartialDerivWithin_of_eqOn hV hs w hh heq hxy]
  exact iteratedPartialDeriv_eq_mixedDeriv hV w hh hxy.2

/-- **Derivatives within a set of a function `C^{|w|}` at the point.** At a point `E (x, y)` of a
set with unique derivatives where `f` is `C^{|w|}`, the iterated partial derivative of `f` within
the set along `w` is `mixedDeriv (w.count 0) (w.count 1) (f ∘ E) x y`. -/
theorem iteratedPartialDerivWithin_eq_mixedDeriv_of_contDiffAt {f : ℝ^2 → ℝ} {s : Set (ℝ^2)}
    (hs : UniqueDiffOn ℝ s) (w : List (Fin 2)) {x y : ℝ}
    (hf : ContDiffAt ℝ w.length f (pointPairEquiv.symm (x, y)))
    (hxy : pointPairEquiv.symm (x, y) ∈ s) :
    iteratedPartialDerivWithin w f s (pointPairEquiv.symm (x, y)) =
      mixedDeriv (w.count 0) (w.count 1)
        (fun a b ↦ f (pointPairEquiv.symm (a, b))) x y :=
  iteratedPartialDerivWithin_eq_mixedDeriv (isOpen_setOf_contDiffAt w.length) hs w
    (contDiffOn_setOf_contDiffAt w.length) (fun _ _ ↦ rfl) ⟨hxy, hf⟩

/-- **Derivatives within the closed upper half-plane.** For `y ≥ 0` and `f` that is `C^{|w|}` at
`E (x, y)`, the iterated partial derivative of `f` within `{z | 0 ≤ z 1}` along `w` at `E (x, y)`
is `mixedDeriv (w.count 0) (w.count 1) (f ∘ E) x y`. -/
theorem iteratedPartialDerivWithin_upper_eq_mixedDeriv {f : ℝ^2 → ℝ} (w : List (Fin 2)) {x y : ℝ}
    (hy : 0 ≤ y) (hf : ContDiffAt ℝ w.length f (pointPairEquiv.symm (x, y))) :
    iteratedPartialDerivWithin w f {z | 0 ≤ z 1} (pointPairEquiv.symm (x, y)) =
      mixedDeriv (w.count 0) (w.count 1)
        (fun a b ↦ f (pointPairEquiv.symm (a, b))) x y :=
  iteratedPartialDerivWithin_eq_mixedDeriv_of_contDiffAt
    (PDE.Analysis.uniqueDiffOn_coordinateHalfSpace 1) w hf
    (by simpa [pointPair_symm_apply_one] using hy)

end CAS.Numerics.TensorSpline
