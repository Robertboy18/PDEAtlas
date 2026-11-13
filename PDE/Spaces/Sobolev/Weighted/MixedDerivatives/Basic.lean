/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.DerivativeInterpolation
public import PDE.Spaces.Sobolev.Weighted.PlanarReflection
public import PDE.Analysis.Calculus.Deriv.Curried

/-!
# Mixed derivatives and planar reflection

For `f : ℝ → ℝ → ℝ` in the coordinates `(r, z)`, the row `(j, a)` of `f` is
`mixedDerivative2D j a f = ∂_r^a ∂_z^(j - a) f`, the derivative of order `j` with radial exponent
`a : Fin (j + 1)`. We identify the rows with the iterated partial derivatives `iteratedPartialDeriv`
of `y ↦ f (y 0) (y 1)` on `ℝ²`, and we compute the rows of the even reflection
`evenReflection2D f r z = f |r| z`: the row `(j, a)` of the even reflection is the even reflection
of the row `(j, a)` of `f` when `a` is even and its odd reflection when `a` is odd. This holds
almost everywhere for every `f`, and everywhere for a `C^k` function whose rows with odd radial
exponent and order at most `k - 1` vanish on the axis `r = 0`, when `j ≤ k - 1`. We also compute the
first and second partial derivatives of a single row.

## Main results

* `iteratedPartialDeriv_replicate_mixed_eq_mixedIteratedDeriv2D`,
  `iteratedPartialDeriv_canonical_eq_mixedDerivative2D`: for a `C^(q + ℓ)` function on `ℝ²`, the
  iterated partial derivative along the word of `q` radial directions followed by `ℓ` axial
  directions is `∂_r^q ∂_z^ℓ` of the curried function.
* `mixedDerivative2D_evenReflection_ae_eq_parity`: the parity of the rows of an even reflection,
  almost everywhere and with no hypothesis on `f`.
* `mixedDerivative2D_evenReflection_of_finite_parity`: the parity everywhere, for `j ≤ k - 1`, when
  `v` is `C^k` and `∂_r^q ∂_z^ℓ v (0, z) = 0` for odd `q` and `q + ℓ ≤ k - 1`.
* `iteratedPartialDeriv_orderTwo_mixedDerivative_shifted_rows`,
  `iteratedPartialDeriv_orderTwo_mixedDerivative_evenReflection_ae_shifted_rows`: the partial
  derivatives of the row `(m, a)` along `[0]`, `[1]`, `[0, 0]`, `[0, 1]` and `[1, 1]` are the rows
  `(m + 1, a + 1)`, `(m + 1, a)`, `(m + 2, a + 2)`, `(m + 2, a + 1)` and `(m + 2, a)`; everywhere
  for a `C^(m + 2)` function, and almost everywhere for its even reflection when the reflected row
  `(m, a)` is `C²` on the plane.
* `sixShiftedMixedRows_le_Icc_sum`: for nonnegative `R`, the sum of `R` over the row `(m, a)` and
  these five rows is at most the sum of `R` over all rows of orders `m` to `m + 2`.

## How it works

For `r > 0` the even reflection is `f r z` and for `r < 0` it is `f (-r) z`, so for `r < 0`
Mathlib's `iteratedDeriv_comp_neg` gives
`∂_r^a ∂_z^ℓ (evenReflection2D f) r z = (-1)^a ∂_r^a ∂_z^ℓ f (-r) z`
(`SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_neg`). This is the formula (253) in the
proof of Proposition 8 of Duruisseaux, Ganeshram, George and Anandkumar, for `p = 0`. Since the axis
is a null set (`SobolevSpace.Weighted.volume_radialAxis_eq_zero`), it gives the almost-everywhere
parity, `SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_ae_eq_parity`. The everywhere
version applies `SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_finite_mixed_order`,
whose radial `HasDerivAt` hypotheses we derive from `C^k` regularity; the hypothesis `hparity` of
`mixedDerivative2D_evenReflection_of_finite_parity` is the classical form of the trace condition
(249) of that proposition, for `p = 0` and `m = k`. We pass between `iteratedPartialDeriv` and
iterated one-variable derivatives with
`PDE.iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at`. The axial derivative of the row
`(n, a)` is the row `(n + 1, a)` by the symmetry of mixed partial derivatives,
`SobolevSpace.iteratedPartialDeriv_congr_perm_of_contDiff`, which rests on Mathlib's
`ContDiffAt.isSymmSndFDerivAt` and needs `C^(n + 1)` regularity.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.4, Proposition 8,
  (248)-(249) and (253), p. 51, for the even reflection, the trace conditions on the axis and the
  derivatives of the reflection off the axis.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open PDE (coordinateLine iteratedPartialDeriv)
open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology
open PDE.Analysis (derivX derivY derivX_iterate_apply derivY_iterate_apply)

namespace SobolevSpace.Weighted

/-- If `G y = f (y 0) (y 1)` and `G` is differentiable, then `(∂[0] G) y = derivX f (y 0) (y 1)`:
the first partial derivative of `G` is the radial derivative of `f`. -/
theorem partialDeriv_uncurry_eq_derivX
    (f : ℝ → ℝ → ℝ) (G : (ℝ^2) → ℝ)
    (hG : G = fun y ↦ f (y 0) (y 1))
    (hDiff : Differentiable ℝ G) (y : (ℝ^2)) :
    (∂[0] G) y = derivX f (y 0) (y 1) := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 0 y (hDiff y)]
  subst hG
  unfold derivX
  congr 1
  funext s
  simp [coordinateLine]

/-- If `G y = f (y 0) (y 1)` and `G` is differentiable, then `(∂[1] G) y = derivY f (y 0) (y 1)`:
the second partial derivative of `G` is the axial derivative of `f`. -/
theorem partialDeriv_uncurry_eq_derivY
    (f : ℝ → ℝ → ℝ) (G : (ℝ^2) → ℝ)
    (hG : G = fun y ↦ f (y 0) (y 1))
    (hDiff : Differentiable ℝ G) (y : (ℝ^2)) :
    (∂[1] G) y = derivY f (y 0) (y 1) := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 1 y (hDiff y)]
  subst hG
  unfold derivY
  congr 1
  funext s
  simp [coordinateLine]

/-- If `F` is `C^ell` on `ℝ²`, then the iterated partial derivative of `F` along
`List.replicate ell 1` is `mixedIteratedDeriv2D 0 ell f`, the `ell`-th axial derivative of
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`. -/
theorem iteratedPartialDeriv_replicate_axial_eq_mixedIteratedDeriv2D
    (ell : ℕ) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((ell : ℕ) : ℕ∞) F) :
    (fun y ↦ iteratedPartialDeriv (n := 2)
      (List.replicate ell (1 : Fin 2)) F y) =
    fun y ↦ SobolevSpace.Weighted.mixedIteratedDeriv2D 0 ell
      (fun r z ↦ F (EuclideanSpace.single 0 r +
        EuclideanSpace.single 1 z)) (y 0) (y 1) := by
  funext y
  rw [PDE.iteratedPartialDeriv_replicate,
    PDE.iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at 1 ell hF.contDiffAt]
  unfold SobolevSpace.Weighted.mixedIteratedDeriv2D
  rw [iteratedDeriv_zero]
  congr 1
  funext s
  simp only [Function.comp_apply]
  congr 1
  ext i
  fin_cases i <;> simp [coordinateLine]

/-- If `F` is `C^(q + ell)` on `ℝ²`, then the iterated partial derivative of `F` along
`List.replicate q 0 ++ List.replicate ell 1` is `mixedIteratedDeriv2D q ell f`, that is
`∂_r^q ∂_z^ell f`, where `f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`. -/
theorem iteratedPartialDeriv_replicate_mixed_eq_mixedIteratedDeriv2D
    (q ell : ℕ) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((q + ell : ℕ) : ℕ∞) F) :
    (fun y ↦ iteratedPartialDeriv (n := 2)
      (List.replicate q (0 : Fin 2) ++ List.replicate ell (1 : Fin 2)) F y) =
    fun y ↦ SobolevSpace.Weighted.mixedIteratedDeriv2D q ell
      (fun r z ↦ F (EuclideanSpace.single 0 r +
        EuclideanSpace.single 1 z)) (y 0) (y 1) := by
  have haxial := iteratedPartialDeriv_replicate_axial_eq_mixedIteratedDeriv2D ell F
    (hF.of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (Nat.le_add_left ell q))))
  have hreg : ContDiff ℝ ((q : ℕ) : ℕ∞)
      (fun y ↦ iteratedPartialDeriv (n := 2) (List.replicate ell (1 : Fin 2)) F y) := by
    have h := PDE.contDiff_iteratedPartialDeriv_of_le (n := 2) hF
      (List.replicate ell (1 : Fin 2)) (by simp)
    simpa using h
  funext y
  rw [PDE.iteratedPartialDeriv_append, PDE.iteratedPartialDeriv_replicate,
    PDE.iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at 0 q hreg.contDiffAt]
  unfold SobolevSpace.Weighted.mixedIteratedDeriv2D
  congr 1
  funext s
  simp only [Function.comp_apply]
  rw [congrFun haxial (coordinateLine 0 y s)]
  simp [SobolevSpace.Weighted.mixedIteratedDeriv2D, coordinateLine]

/-- The mixed derivative `∂_r^a ∂_z^(j - a) f = derivX^[a] (derivY^[j - a] f)` of order `j`, indexed
by its radial exponent `a : Fin (j + 1)`. -/
def mixedDerivative2D (j : ℕ) (a : Fin (j + 1))
    (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  (derivX^[a.val])
    ((derivY^[j - a.val]) f)

/-- `mixedDerivative2D j a f = mixedIteratedDeriv2D a (j - a) f`. -/
theorem mixedDerivative2D_eq_mixedIteratedDeriv2D
    (j : ℕ) (a : Fin (j + 1)) (f : ℝ → ℝ → ℝ) :
    mixedDerivative2D j a f =
      SobolevSpace.Weighted.mixedIteratedDeriv2D a.val (j - a.val) f := by
  funext r z
  rw [mixedDerivative2D, SobolevSpace.Weighted.mixedIteratedDeriv2D,
    derivX_iterate_apply]
  congr 2
  funext rho
  exact derivY_iterate_apply f (j - a.val) rho z

/-- For every `f`, almost everywhere on `ℝ²` the row `mixedDerivative2D j a (evenReflection2D f)`
equals `evenReflection2D (mixedDerivative2D j a f)` if `a` is even and
`oddReflection2D (mixedDerivative2D j a f)` if `a` is odd. -/
theorem mixedDerivative2D_evenReflection_ae_eq_parity
    (j : ℕ) (a : Fin (j + 1)) (f : ℝ → ℝ → ℝ) :
    (fun y : (ℝ^2) ↦ mixedDerivative2D j a (SobolevSpace.Weighted.evenReflection2D f)
      (y 0) (y 1)) =ᵐ[volume]
      if Even a.val then
        fun y ↦ SobolevSpace.Weighted.evenReflection2D (mixedDerivative2D j a f) (y 0) (y 1)
      else
        fun y ↦ SobolevSpace.Weighted.oddReflection2D (mixedDerivative2D j a f) (y 0) (y 1) := by
  simpa [mixedDerivative2D_eq_mixedIteratedDeriv2D] using
    (SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_ae_eq_parity
      a.val (j - a.val) f)

/-- `mixedDerivative2D_evenReflection_ae_eq_parity` composed with the coordinate swap
`S = radialCoordinateSwap2D`, so that `r` is the last coordinate of `y`. Almost everywhere, with
`g = mixedDerivative2D j b f`, the row `mixedDerivative2D j b (evenReflection2D f)` at `S y` equals
`g` at `S (SobolevSpace.HalfSpace.reflect 2 y)` if the last coordinate of `y` is negative, with a
minus sign if `b` is odd, and `g` at `S y` otherwise. -/
theorem mixedDerivative2D_evenReflection_comp_swap_ae_eq_piecewise
    (j : ℕ) (b : Fin (j + 1)) (f : ℝ → ℝ → ℝ) :
    (fun y : (ℝ^2) ↦ mixedDerivative2D j b (SobolevSpace.Weighted.evenReflection2D f)
      (SobolevSpace.Weighted.radialCoordinateSwap2D y 0)
      (SobolevSpace.Weighted.radialCoordinateSwap2D y 1)) =ᵐ[volume]
      if Even b.val then
        fun y ↦ if y (PDE.Common.lastIndex (n := 2)) < 0 then
          (fun x : (ℝ^2) ↦ mixedDerivative2D j b f (x 0) (x 1))
            (SobolevSpace.Weighted.radialCoordinateSwap2D (SobolevSpace.HalfSpace.reflect 2 y))
        else (fun x : (ℝ^2) ↦ mixedDerivative2D j b f (x 0) (x 1))
          (SobolevSpace.Weighted.radialCoordinateSwap2D y)
      else
        fun y ↦ if y (PDE.Common.lastIndex (n := 2)) < 0 then
          -(fun x : (ℝ^2) ↦ mixedDerivative2D j b f (x 0) (x 1))
            (SobolevSpace.Weighted.radialCoordinateSwap2D (SobolevSpace.HalfSpace.reflect 2 y))
        else (fun x : (ℝ^2) ↦ mixedDerivative2D j b f (x 0) (x 1))
          (SobolevSpace.Weighted.radialCoordinateSwap2D y) := by
  have hp := mixedDerivative2D_evenReflection_ae_eq_parity j b f
  have hc :=
    SobolevSpace.Weighted.radialCoordinateSwap2D_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      hp
  filter_upwards [hc] with y hy
  have heq : mixedDerivative2D j b (SobolevSpace.Weighted.evenReflection2D f)
      (SobolevSpace.Weighted.radialCoordinateSwap2D y 0)
      (SobolevSpace.Weighted.radialCoordinateSwap2D y 1) =
      (if Even b.val then
        fun x : (ℝ^2) ↦
          SobolevSpace.Weighted.evenReflection2D (mixedDerivative2D j b f) (x 0) (x 1)
      else fun x : (ℝ^2) ↦
        SobolevSpace.Weighted.oddReflection2D (mixedDerivative2D j b f) (x 0) (x 1))
        (SobolevSpace.Weighted.radialCoordinateSwap2D y) := by
    simpa [Function.comp_def] using hy
  rw [heq]
  rcases lt_or_ge (y 1) 0 with hyr | hyr <;> by_cases hb : Even b.val <;>
    simp [hb, hyr, hyr.not_gt, abs_of_neg, abs_of_nonneg, SobolevSpace.Weighted.evenReflection2D,
      SobolevSpace.Weighted.oddReflection2D, PDE.Common.lastIndex,
      SobolevSpace.Weighted.radialCoordinateSwap2D_reflect]

/-- If `F` is `C^j` on `ℝ²`, then the iterated partial derivative of `F` along
`List.replicate a 0 ++ List.replicate (j - a) 1` is `mixedDerivative2D j a f`, where
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`. -/
theorem iteratedPartialDeriv_canonical_eq_mixedDerivative2D
    (j : ℕ) (a : Fin (j + 1)) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((j : ℕ) : ℕ∞) F) :
    (fun y ↦ iteratedPartialDeriv (n := 2)
      (List.replicate a.val (0 : Fin 2) ++
        List.replicate (j - a.val) (1 : Fin 2)) F y) =
    fun y ↦ mixedDerivative2D j a
      (fun r z ↦ F (EuclideanSpace.single 0 r +
        EuclideanSpace.single 1 z)) (y 0) (y 1) := by
  have hsum : a.val + (j - a.val) = j := Nat.add_sub_of_le (by omega)
  rw [mixedDerivative2D_eq_mixedIteratedDeriv2D]
  simpa [hsum] using
    (iteratedPartialDeriv_replicate_mixed_eq_mixedIteratedDeriv2D
      a.val (j - a.val) F (by simpa [hsum] using hF))

/-- If `F` is `C^k` on `ℝ²` and `j ≤ k`, then `y ↦ mixedDerivative2D j a f (y 0) (y 1)` is
`C^(k - j)`, where `f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`. -/
theorem contDiff_mixedDerivative2D_uncurry
    (k j : ℕ) (a : Fin (j + 1)) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((k : ℕ) : ℕ∞) F) (hj : j ≤ k) :
    ContDiff ℝ ((k - j : ℕ) : ℕ∞)
      (fun y : (ℝ^2) ↦ mixedDerivative2D j a
        (fun r z ↦ F (EuclideanSpace.single 0 r +
          EuclideanSpace.single 1 z)) (y 0) (y 1)) := by
  let word := List.replicate a.val (0 : Fin 2) ++
    List.replicate (j - a.val) (1 : Fin 2)
  have hwordlen : word.length = j := by
    simp [word]
    omega
  have hreg := PDE.contDiff_iteratedPartialDeriv_of_le
    (n := 2) hF word (by simpa [hwordlen] using hj)
  have hFj : ContDiff ℝ ((j : ℕ) : ℕ∞) F := hF.of_le
    (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hj))
  have heq := iteratedPartialDeriv_canonical_eq_mixedDerivative2D j a F hFj
  rw [← heq]
  simpa [hwordlen] using hreg

/-- If `F` is `C^(s + ell + 1)` on `ℝ²` and
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`, then for all `r` and `z` the
function `ρ ↦ mixedIteratedDeriv2D s ell f ρ z` has derivative
`mixedIteratedDeriv2D (s + 1) ell f r z` at `r`. -/
theorem hasDerivAt_mixedIteratedDeriv2D_radial_of_contDiff
    (s ell : ℕ) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((s + ell + 1 : ℕ) : ℕ∞) F) :
    ∀ r z, HasDerivAt
      (fun rho ↦ SobolevSpace.Weighted.mixedIteratedDeriv2D s ell
        (fun a b ↦ F (EuclideanSpace.single 0 a +
          EuclideanSpace.single 1 b)) rho z)
      (SobolevSpace.Weighted.mixedIteratedDeriv2D (s + 1) ell
        (fun a b ↦ F (EuclideanSpace.single 0 a +
          EuclideanSpace.single 1 b)) r z) r := by
  let f : ℝ → ℝ → ℝ := fun a b ↦
    F (EuclideanSpace.single 0 a + EuclideanSpace.single 1 b)
  let j := s + ell
  let a : Fin (j + 1) := ⟨s, by simp [j]⟩
  let G : (ℝ^2) → ℝ := fun y ↦ mixedDerivative2D j a f (y 0) (y 1)
  have hj : j ≤ s + ell + 1 := by simp [j]
  have hG : ContDiff ℝ 1 G := by
    have h := contDiff_mixedDerivative2D_uncurry
      (s + ell + 1) j a F hF hj
    simpa [j, G, f] using h
  have hGa : G = fun y ↦ SobolevSpace.Weighted.mixedIteratedDeriv2D s ell f (y 0) (y 1) := by
    funext y
    simp [G, a, j, mixedDerivative2D_eq_mixedIteratedDeriv2D]
  intro r z
  have hslice : DifferentiableAt ℝ (fun rho ↦ G
      (EuclideanSpace.single 0 rho + EuclideanSpace.single 1 z)) r := by
    let L : ℝ →L[ℝ] (ℝ^2) :=
      (PiLp.continuousLinearEquiv (p := 2) ℝ
        (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin 2 ↦ ℝ) 0)
    have hL : ∀ rho : ℝ, L rho = EuclideanSpace.single 0 rho := by
      intro rho
      ext i
      fin_cases i <;> simp [L]
    have hpath : DifferentiableAt ℝ (fun rho : ℝ ↦
        (EuclideanSpace.single 0 rho + EuclideanSpace.single 1 z : (ℝ^2))) r := by
      simpa only [hL] using L.differentiable.differentiableAt.add_const
        (EuclideanSpace.single 1 z)
    exact (hG.differentiable (by norm_num)
      (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)).comp r hpath
  have hhas := hslice.hasDerivAt
  rw [hGa] at hhas
  simpa [f, SobolevSpace.Weighted.mixedIteratedDeriv2D, iteratedDeriv_succ] using hhas

/-- Let `v` be `C^k` on `ℝ²`, let
`f r z = v (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)` and assume
`mixedIteratedDeriv2D q ell f 0 z = 0` for all `z` whenever `q` is odd and `q + ell ≤ k - 1`. If
`j ≤ k - 1`, then `mixedDerivative2D j a (evenReflection2D f)` equals
`evenReflection2D (mixedDerivative2D j a f)` if `a` is even and
`oddReflection2D (mixedDerivative2D j a f)` if `a` is odd, everywhere. -/
theorem mixedDerivative2D_evenReflection_of_finite_parity
    (v : (ℝ^2 → ℝ)) (k j : ℕ) (a : Fin (j + 1))
    (hv : ContDiff ℝ ((k : ℕ) : ℕ∞) v) (hj : j ≤ k - 1)
    (hparity : ∀ q ell : ℕ, Odd q → q + ell ≤ k - 1 → ∀ z : ℝ,
      SobolevSpace.Weighted.mixedIteratedDeriv2D q ell
        (fun r z ↦ v (EuclideanSpace.single (0 : Fin 2) r +
          EuclideanSpace.single (1 : Fin 2) z)) 0 z = 0) :
    if Even a.val then
      mixedDerivative2D j a
        (SobolevSpace.Weighted.evenReflection2D (fun r z ↦ v
          (EuclideanSpace.single (0 : Fin 2) r +
            EuclideanSpace.single (1 : Fin 2) z))) =
        SobolevSpace.Weighted.evenReflection2D (mixedDerivative2D j a
          (fun r z ↦ v (EuclideanSpace.single (0 : Fin 2) r +
            EuclideanSpace.single (1 : Fin 2) z)))
    else
      mixedDerivative2D j a
        (SobolevSpace.Weighted.evenReflection2D (fun r z ↦ v
          (EuclideanSpace.single (0 : Fin 2) r +
            EuclideanSpace.single (1 : Fin 2) z))) =
        SobolevSpace.Weighted.oddReflection2D (mixedDerivative2D j a
          (fun r z ↦ v (EuclideanSpace.single (0 : Fin 2) r +
            EuclideanSpace.single (1 : Fin 2) z))) := by
  let f : ℝ → ℝ → ℝ := fun r z ↦ v
    (EuclideanSpace.single (0 : Fin 2) r +
      EuclideanSpace.single (1 : Fin 2) z)
  let q := a.val
  let ell := j - a.val
  have hsum : q + ell = j := by simp [q, ell]; omega
  have hderiv : ∀ s < q, ∀ r z,
      HasDerivAt (fun rho ↦ SobolevSpace.Weighted.mixedIteratedDeriv2D s ell f rho z)
        (SobolevSpace.Weighted.mixedIteratedDeriv2D (s + 1) ell f r z) r := by
    intro s hs r z
    have hord : s + ell + 1 ≤ k := by omega
    simpa [f] using hasDerivAt_mixedIteratedDeriv2D_radial_of_contDiff s ell v
      (hv.of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hord))) r z
  have htrace : ∀ s ≤ q, Odd s → ∀ z,
      SobolevSpace.Weighted.mixedIteratedDeriv2D s ell f 0 z = 0 :=
    fun s hs hodd z ↦ hparity s ell hodd (by omega) z
  have hall := SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_finite_mixed_order
    q ell f hderiv htrace
  simpa [q, ell, f, mixedDerivative2D_eq_mixedIteratedDeriv2D] using hall

/-- If `G y = f (y 0) (y 1)` and `G` is `C²`, then at every `y` the iterated partial derivatives of
`G` along `[]`, `[0]`, `[1]`, `[0, 0]`, `[0, 1]` and `[1, 1]` are
`mixedDerivative2D j a f (y 0) (y 1)` for `(j, a) = (0, 0)`, `(1, 1)`, `(1, 0)`, `(2, 2)`, `(2, 1)`
and `(2, 0)`. -/
theorem iteratedPartialDeriv_orderTwo_eq_mixedDerivative2D
    (f : ℝ → ℝ → ℝ) (G : (ℝ^2) → ℝ)
    (hG : G = fun y ↦ f (y 0) (y 1)) (hC2 : ContDiff ℝ 2 G) :
    ∀ y : (ℝ^2),
      iteratedPartialDeriv (n := 2) [] G y =
          mixedDerivative2D 0 (0 : Fin 1) f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [0] G y =
          mixedDerivative2D 1 ⟨1, by omega⟩ f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [1] G y =
          mixedDerivative2D 1 (0 : Fin 2) f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [0, 0] G y =
          mixedDerivative2D 2 ⟨2, by omega⟩ f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [0, 1] G y =
          mixedDerivative2D 2 ⟨1, by omega⟩ f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [1, 1] G y =
          mixedDerivative2D 2 (0 : Fin 3) f (y 0) (y 1) := by
  have hDiff : Differentiable ℝ G := hC2.differentiable (by norm_num)
  have hr : (fun y ↦ (∂[0] G) y) = fun y ↦ derivX f (y 0) (y 1) :=
    funext fun y ↦ partialDeriv_uncurry_eq_derivX f G hG hDiff y
  have hz : (fun y ↦ (∂[1] G) y) = fun y ↦ derivY f (y 0) (y 1) :=
    funext fun y ↦ partialDeriv_uncurry_eq_derivY f G hG hDiff y
  have hrDiff : Differentiable ℝ (fun y ↦ (∂[0] G) y) :=
    (PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 1) (i := 0) hC2).differentiable
      (by norm_num)
  have hzDiff : Differentiable ℝ (fun y ↦ (∂[1] G) y) :=
    (PDE.contDiff_partialDeriv_of_succ (n := 2) (m := 1) (i := 1) hC2).differentiable
      (by norm_num)
  intro y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [iteratedPartialDeriv, mixedDerivative2D, hG]
  · simpa [iteratedPartialDeriv, mixedDerivative2D] using congrFun hr y
  · simpa [iteratedPartialDeriv, mixedDerivative2D] using congrFun hz y
  · simpa [iteratedPartialDeriv, mixedDerivative2D, Function.iterate_succ_apply'] using
      partialDeriv_uncurry_eq_derivX (derivX f) _ hr hrDiff y
  · simpa [iteratedPartialDeriv, mixedDerivative2D, Function.iterate_succ_apply'] using
      partialDeriv_uncurry_eq_derivX (derivY f) _ hz hzDiff y
  · simpa [iteratedPartialDeriv, mixedDerivative2D, Function.iterate_succ_apply'] using
      partialDeriv_uncurry_eq_derivY (derivY f) _ hz hzDiff y

/-- With radial exponent `0` the row is a pure axial derivative:
`mixedDerivative2D j 0 f = derivY^[j] f`. -/
theorem mixedDerivative2D_zero_axial (j : ℕ) (f : ℝ → ℝ → ℝ) :
    mixedDerivative2D j (0 : Fin (j + 1)) f =
      (derivY^[j]) f := by
  simp [mixedDerivative2D]

/-- `derivY (mixedDerivative2D n 0 f) = mixedDerivative2D (n + 1) 0 f`. -/
theorem derivY_mixedDerivative_zero
    (n : ℕ) (f : ℝ → ℝ → ℝ) :
    derivY (mixedDerivative2D n 0 f) =
      mixedDerivative2D (n + 1) 0 f := by
  simp [mixedDerivative2D, Function.iterate_succ_apply']

/-- `derivX (mixedDerivative2D n a f) = mixedDerivative2D (n + 1) a.succ f`: a radial derivative
raises the order and the radial exponent by one. -/
theorem derivX_mixedDerivative_succ
    (n : ℕ) (a : Fin (n + 1)) (f : ℝ → ℝ → ℝ) :
    derivX (mixedDerivative2D n a f) =
      mixedDerivative2D (n + 1) a.succ f := by
  simp only [mixedDerivative2D, Fin.val_succ]
  have hz : n + 1 - (a.val + 1) = n - a.val := by omega
  have hr : a.val + 1 = Nat.succ a.val := by omega
  rw [hz, hr, Function.iterate_succ_apply']

/-- If `F` is `C^(n + 1)` on `ℝ²` and
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`, then
`derivY (mixedDerivative2D n a f) = mixedDerivative2D (n + 1) a f`, with the same radial exponent
`a` on both sides. -/
theorem derivY_mixedDerivative_of_contDiff
    (n : ℕ) (a : Fin (n + 1)) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) F) :
    derivY (mixedDerivative2D n a
      (fun r z ↦ F (EuclideanSpace.single 0 r +
        EuclideanSpace.single 1 z))) =
      mixedDerivative2D (n + 1) ⟨a.val, by omega⟩
        (fun r z ↦ F (EuclideanSpace.single 0 r +
          EuclideanSpace.single 1 z)) := by
  let f : ℝ → ℝ → ℝ := fun r z ↦
    F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)
  let G : (ℝ^2) → ℝ := fun y ↦ mixedDerivative2D n a f (y 0) (y 1)
  let b : Fin (n + 2) := ⟨a.val, by omega⟩
  let word := List.replicate a.val (0 : Fin 2) ++
    List.replicate (n - a.val) (1 : Fin 2)
  let wordNext := List.replicate b.val (0 : Fin 2) ++
    List.replicate (n + 1 - b.val) (1 : Fin 2)
  have hn : n ≤ n + 1 := by omega
  have hFn : ContDiff ℝ ((n : ℕ) : ℕ∞) F := hF.of_le
    (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hn))
  have hcanon : (fun y ↦ iteratedPartialDeriv (n := 2) word F y) = G := by
    simpa [word, G, f] using
      (iteratedPartialDeriv_canonical_eq_mixedDerivative2D n a F hFn)
  have hG : ContDiff ℝ 1 G := by
    have h := contDiff_mixedDerivative2D_uncurry (n + 1) n a F hF hn
    simpa [G, f] using h
  have hperm : ((1 : Fin 2) :: word).Perm wordNext := by
    rw [List.perm_iff_count]
    intro i
    fin_cases i <;> simp [word, wordNext, b, List.count_replicate]
    all_goals omega
  have hwordlen : ((1 : Fin 2) :: word).length = n + 1 := by
    simp [word]
    omega
  have hFword : ContDiff ℝ
      ((((1 : Fin 2) :: word).length : ℕ) : ℕ∞) F := by
    simpa [hwordlen] using hF
  have hclair : (fun y ↦ iteratedPartialDeriv (n := 2)
      ((1 : Fin 2) :: word) F y) =
      fun y ↦ iteratedPartialDeriv (n := 2) wordNext F y := by
    exact SobolevSpace.iteratedPartialDeriv_congr_perm_of_contDiff hFword hperm
  have hnext := iteratedPartialDeriv_canonical_eq_mixedDerivative2D
    (n + 1) b F hF
  funext r z
  let y : (ℝ^2) := EuclideanSpace.single 0 r + EuclideanSpace.single 1 z
  have hax := partialDeriv_uncurry_eq_derivY
    (mixedDerivative2D n a f) G rfl
    (hG.differentiable (by norm_num)) y
  calc
    derivY (mixedDerivative2D n a f) r z =
        (∂[1] G) y := by simpa [y] using hax.symm
    _ = iteratedPartialDeriv (n := 2) ((1 : Fin 2) :: word) F y := by
      rw [← hcanon]
      rfl
    _ = iteratedPartialDeriv (n := 2) wordNext F y := congrFun hclair y
    _ = mixedDerivative2D (n + 1) b f (y 0) (y 1) := congrFun hnext y
    _ = _ := by simp [b, f, y]

/-- Assume `derivY (mixedDerivative2D m a f) = mixedDerivative2D (m + 1) a f` and that
`z ↦ mixedDerivative2D m a f r z` is differentiable for every `r`. Then at every `(r, z)` with
`r ≠ 0`, `derivY (mixedDerivative2D m a (evenReflection2D f))` equals
`mixedDerivative2D (m + 1) a (evenReflection2D f)`. -/
theorem derivY_mixedDerivative_evenReflection_away_axis
    (m : ℕ) (a : Fin (m + 1)) (f : ℝ → ℝ → ℝ)
    (hax : derivY (mixedDerivative2D m a f) =
      mixedDerivative2D (m + 1) ⟨a.val, by omega⟩ f)
    (hdiff : ∀ r z, DifferentiableAt ℝ (mixedDerivative2D m a f r) z)
    {r z : ℝ} (hr0 : r ≠ 0) :
    derivY (mixedDerivative2D m a (SobolevSpace.Weighted.evenReflection2D f)) r z =
      mixedDerivative2D (m + 1) ⟨a.val, by omega⟩
        (SobolevSpace.Weighted.evenReflection2D f) r z := by
  rcases lt_or_gt_of_ne hr0 with hr | hr
  · have hmfun : mixedDerivative2D m a (SobolevSpace.Weighted.evenReflection2D f) r =
        (-1 : ℝ) ^ a.val • mixedDerivative2D m a f (-r) := by
      funext s
      simpa [mixedDerivative2D_eq_mixedIteratedDeriv2D, smul_eq_mul] using
        (SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_neg a.val (m - a.val) f
          (r := r) (z := s) hr)
    have hnext := SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_neg
      a.val (m + 1 - a.val) f (r := r) (z := z) hr
    rw [derivY, hmfun, deriv_const_smul]
    · rw [show deriv (mixedDerivative2D m a f (-r)) z =
          derivY (mixedDerivative2D m a f) (-r) z by rfl,
        congrFun (congrFun hax (-r)) z]
      simpa [mixedDerivative2D_eq_mixedIteratedDeriv2D,
        Nat.add_sub_of_le (show a.val ≤ m from by omega), smul_eq_mul] using hnext.symm
    · exact hdiff (-r) z
  · have hmfun : mixedDerivative2D m a (SobolevSpace.Weighted.evenReflection2D f) r =
        mixedDerivative2D m a f r := by
      funext s
      simpa [mixedDerivative2D_eq_mixedIteratedDeriv2D] using
        (SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_pos a.val (m - a.val) f
          (r := r) (z := s) hr)
    have hnext := SobolevSpace.Weighted.mixedIteratedDeriv2D_evenReflection_pos
      a.val (m + 1 - a.val) f (r := r) (z := z) hr
    rw [derivY, hmfun]
    rw [show deriv (mixedDerivative2D m a f r) z =
        derivY (mixedDerivative2D m a f) r z by rfl,
      congrFun (congrFun hax r) z]
    simpa [mixedDerivative2D_eq_mixedIteratedDeriv2D,
      Nat.add_sub_of_le (show a.val ≤ m from by omega)] using hnext.symm

/-- Assume `derivY (mixedDerivative2D m a f) = mixedDerivative2D (m + 1) a f` and that
`z ↦ mixedDerivative2D m a f r z` is differentiable for every `r`. Then
`derivY (mixedDerivative2D m a (evenReflection2D f))` equals
`mixedDerivative2D (m + 1) a (evenReflection2D f)` almost everywhere on `ℝ²`. -/
theorem derivY_mixedDerivative_evenReflection_ae
    (m : ℕ) (a : Fin (m + 1)) (f : ℝ → ℝ → ℝ)
    (hax : derivY (mixedDerivative2D m a f) =
      mixedDerivative2D (m + 1) ⟨a.val, by omega⟩ f)
    (hdiff : ∀ r z, DifferentiableAt ℝ (mixedDerivative2D m a f r) z) :
    (fun y : (ℝ^2) ↦ derivY
      (mixedDerivative2D m a (SobolevSpace.Weighted.evenReflection2D f)) (y 0) (y 1)) =ᵐ[volume]
      fun y ↦ mixedDerivative2D (m + 1) ⟨a.val, by omega⟩
        (SobolevSpace.Weighted.evenReflection2D f) (y 0) (y 1) := by
  have haxis : ∀ᵐ y ∂(volume : Measure (ℝ^2)), y 0 ≠ 0 := by
    rw [ae_iff]
    simpa only [Set.mem_ofPred_eq, not_not] using SobolevSpace.Weighted.volume_radialAxis_eq_zero
  filter_upwards [haxis] with y hy
  exact derivY_mixedDerivative_evenReflection_away_axis
    m a f hax hdiff hy

/-- If `F` is `C^(m + 1)` on `ℝ²` and
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`, then for every `r` the slice
`z ↦ mixedDerivative2D m a f r z` is differentiable at every `z`. -/
theorem differentiableAt_mixedDerivative2D_axial_slice_of_contDiff
    (m : ℕ) (a : Fin (m + 1)) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) F) :
    ∀ r z, DifferentiableAt ℝ
      (mixedDerivative2D m a (fun r z ↦ F
        (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)) r) z := by
  let f : ℝ → ℝ → ℝ := fun r z ↦
    F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)
  have hm : m ≤ m + 1 := by omega
  have hA : ContDiff ℝ 1 (fun y : (ℝ^2) ↦
      mixedDerivative2D m a f (y 0) (y 1)) := by
    have h := contDiff_mixedDerivative2D_uncurry (m + 1) m a F hF hm
    simpa [f] using h
  intro r z
  let L : ℝ →L[ℝ] (ℝ^2) :=
    (PiLp.continuousLinearEquiv (p := 2) ℝ
      (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 2 ↦ ℝ) 1)
  have hL : ∀ t : ℝ, L t = EuclideanSpace.single 1 t := by
    intro t
    ext i
    fin_cases i <;> simp [L]
  have hpath : DifferentiableAt ℝ (fun t : ℝ ↦
      (EuclideanSpace.single 0 r + EuclideanSpace.single 1 t : (ℝ^2))) z := by
    simpa only [hL] using L.differentiable.differentiableAt.const_add
      (EuclideanSpace.single 0 r)
  have hc := (hA.differentiable (by norm_num)
    (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)).comp z hpath
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with t
  simp [f]

/-- If `F` is `C^(m + 1)` on `ℝ²` and
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`, then
`derivY (mixedDerivative2D m a (evenReflection2D f))` equals
`mixedDerivative2D (m + 1) a (evenReflection2D f)` almost everywhere on `ℝ²`. -/
theorem derivY_mixedDerivative_evenReflection_ae_of_contDiff
    (m : ℕ) (a : Fin (m + 1)) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) F) :
    (fun y : (ℝ^2) ↦ derivY
      (mixedDerivative2D m a
        (SobolevSpace.Weighted.evenReflection2D (fun r z ↦ F
          (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z))))
      (y 0) (y 1)) =ᵐ[volume]
      fun y ↦ mixedDerivative2D (m + 1) ⟨a.val, by omega⟩
        (SobolevSpace.Weighted.evenReflection2D (fun r z ↦ F
          (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)))
        (y 0) (y 1) := by
  let f : ℝ → ℝ → ℝ := fun r z ↦
    F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)
  have hax := derivY_mixedDerivative_of_contDiff m a F hF
  have hdiff : ∀ r z, DifferentiableAt ℝ (mixedDerivative2D m a f r) z := by
    simpa [f] using
      differentiableAt_mixedDerivative2D_axial_slice_of_contDiff m a F hF
  simpa [f] using
    (derivY_mixedDerivative_evenReflection_ae m a f hax hdiff)

/-- Let `F` be `C^(m + 2)` on `ℝ²`,
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)` and
`G y = mixedDerivative2D m a f (y 0) (y 1)`. At every `y` the iterated partial derivatives of `G`
along `[]`, `[0]`, `[1]`, `[0, 0]`, `[0, 1]` and `[1, 1]` are `mixedDerivative2D j b f (y 0) (y 1)`
for `(j, b) = (m, a)`, `(m + 1, a + 1)`, `(m + 1, a)`, `(m + 2, a + 2)`, `(m + 2, a + 1)` and
`(m + 2, a)`, with the radial exponents added in `ℕ`. -/
theorem iteratedPartialDeriv_orderTwo_mixedDerivative_shifted_rows
    (m : ℕ) (a : Fin (m + 1)) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((m + 2 : ℕ) : ℕ∞) F) :
    let f : ℝ → ℝ → ℝ := fun r z ↦
      F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)
    let G : (ℝ^2) → ℝ := fun y ↦ mixedDerivative2D m a f (y 0) (y 1)
    ∀ y : (ℝ^2),
      iteratedPartialDeriv (n := 2) [] G y =
          mixedDerivative2D m a f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [0] G y =
          mixedDerivative2D (m + 1) ⟨a.val + 1, by omega⟩ f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [1] G y =
          mixedDerivative2D (m + 1) ⟨a.val, by omega⟩ f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [0, 0] G y =
          mixedDerivative2D (m + 2) ⟨a.val + 2, by omega⟩ f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [0, 1] G y =
          mixedDerivative2D (m + 2) ⟨a.val + 1, by omega⟩ f (y 0) (y 1) ∧
      iteratedPartialDeriv (n := 2) [1, 1] G y =
          mixedDerivative2D (m + 2) ⟨a.val, by omega⟩ f (y 0) (y 1) := by
  dsimp only
  let f : ℝ → ℝ → ℝ := fun r z ↦
    F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)
  let G : (ℝ^2) → ℝ := fun y ↦ mixedDerivative2D m a f (y 0) (y 1)
  have hm : m ≤ m + 2 := by omega
  have hG : ContDiff ℝ 2 G := by
    have h := contDiff_mixedDerivative2D_uncurry (m + 2) m a F hF hm
    simpa [G, f] using h
  have hrows := iteratedPartialDeriv_orderTwo_eq_mixedDerivative2D
    (mixedDerivative2D m a f) G rfl hG
  have hFm1 : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) F := hF.of_le
    (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (by omega)))
  have hax0 := derivY_mixedDerivative_of_contDiff m a F hFm1
  let a0 : Fin (m + 2) := ⟨a.val, by omega⟩
  have hax1 := derivY_mixedDerivative_of_contDiff (m + 1) a0 F hF
  intro y
  obtain ⟨h0, hr, hz, hrr, hrz, hzz⟩ := hrows y
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [G, f, mixedDerivative2D, Function.iterate_succ_apply'] using hr
  · calc
      iteratedPartialDeriv (n := 2) [1] G y =
          derivY (mixedDerivative2D m a f) (y 0) (y 1) := by
            simpa [mixedDerivative2D, Function.iterate_succ_apply'] using hz
      _ = mixedDerivative2D (m + 1) ⟨a.val, by omega⟩ f (y 0) (y 1) := by
        simpa [f] using congrFun (congrFun hax0 (y 0)) (y 1)
  · simpa [G, f, mixedDerivative2D, Function.iterate_succ_apply'] using hrr
  · rw [show mixedDerivative2D 2 ⟨1, by omega⟩ (mixedDerivative2D m a f) =
        derivX (derivY (mixedDerivative2D m a f)) by rfl] at hrz
    rw [hax0] at hrz
    simpa [a0, f, derivX_mixedDerivative_succ] using hrz
  · rw [show mixedDerivative2D 2 (0 : Fin 3) (mixedDerivative2D m a f) =
        derivY (derivY (mixedDerivative2D m a f)) by rfl] at hzz
    rw [hax0, hax1] at hzz
    simpa [a0, f] using hzz

/-- Let `F` be `C^(m + 2)` on `ℝ²`, `E = evenReflection2D f` with
`f r z = F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)`, and
`G y = mixedDerivative2D m a E (y 0) (y 1)`, and assume that `G` is `C²`. Almost everywhere on `ℝ²`
the iterated partial derivatives of `G` along `[0]`, `[1]`, `[0, 0]`, `[0, 1]` and `[1, 1]` are
`mixedDerivative2D j b E (y 0) (y 1)` for `(j, b) = (m + 1, a + 1)`, `(m + 1, a)`, `(m + 2, a + 2)`,
`(m + 2, a + 1)` and `(m + 2, a)`, with the radial exponents added in `ℕ`. -/
theorem iteratedPartialDeriv_orderTwo_mixedDerivative_evenReflection_ae_shifted_rows
    (m : ℕ) (a : Fin (m + 1)) (F : (ℝ^2) → ℝ)
    (hF : ContDiff ℝ ((m + 2 : ℕ) : ℕ∞) F)
    (hG : ContDiff ℝ 2 (fun y : (ℝ^2) ↦ mixedDerivative2D m a
      (SobolevSpace.Weighted.evenReflection2D (fun r z ↦ F
        (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z)))
      (y 0) (y 1))) :
    let E := SobolevSpace.Weighted.evenReflection2D (fun r z ↦ F
      (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z))
    let G : (ℝ^2) → ℝ := fun y ↦ mixedDerivative2D m a E (y 0) (y 1)
    (fun y ↦ iteratedPartialDeriv (n := 2) [0] G y) =ᵐ[volume]
      (fun y ↦ mixedDerivative2D (m + 1) ⟨a.val + 1, by omega⟩ E (y 0) (y 1)) ∧
    (fun y ↦ iteratedPartialDeriv (n := 2) [1] G y) =ᵐ[volume]
      (fun y ↦ mixedDerivative2D (m + 1) ⟨a.val, by omega⟩ E (y 0) (y 1)) ∧
    (fun y ↦ iteratedPartialDeriv (n := 2) [0, 0] G y) =ᵐ[volume]
      (fun y ↦ mixedDerivative2D (m + 2) ⟨a.val + 2, by omega⟩ E (y 0) (y 1)) ∧
    (fun y ↦ iteratedPartialDeriv (n := 2) [0, 1] G y) =ᵐ[volume]
      (fun y ↦ mixedDerivative2D (m + 2) ⟨a.val + 1, by omega⟩ E (y 0) (y 1)) ∧
    (fun y ↦ iteratedPartialDeriv (n := 2) [1, 1] G y) =ᵐ[volume]
      (fun y ↦ mixedDerivative2D (m + 2) ⟨a.val, by omega⟩ E (y 0) (y 1)) := by
  dsimp only
  let E := SobolevSpace.Weighted.evenReflection2D (fun r z ↦ F
    (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z))
  let G : (ℝ^2) → ℝ := fun y ↦ mixedDerivative2D m a E (y 0) (y 1)
  have hrows := iteratedPartialDeriv_orderTwo_eq_mixedDerivative2D
    (mixedDerivative2D m a E) G rfl hG
  have hFm1 : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) F := hF.of_le
    (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (by omega)))
  let ar : Fin (m + 2) := ⟨a.val + 1, by omega⟩
  let az : Fin (m + 2) := ⟨a.val, by omega⟩
  have hrfun : (fun y ↦ (∂[0] G) y) =
      fun y ↦ mixedDerivative2D (m + 1) ar E (y 0) (y 1) := by
    funext y
    simpa [G, E, ar, iteratedPartialDeriv, mixedDerivative2D,
      Function.iterate_succ_apply'] using (hrows y).2.1
  have hradDiff : Differentiable ℝ
      (fun y : (ℝ^2) ↦ mixedDerivative2D (m + 1) ar E (y 0) (y 1)) := by
    rw [← hrfun]
    exact (PDE.contDiff_partialDeriv_of_succ
      (n := 2) (m := 1) (i := 0) hG).differentiable (by norm_num)
  have hmixSwap : (fun y ↦ iteratedPartialDeriv (n := 2) [0, 1] G y) =
      fun y ↦ iteratedPartialDeriv (n := 2) [1, 0] G y :=
    SobolevSpace.iteratedPartialDeriv_congr_perm_of_contDiff hG (List.Perm.swap _ _ [])
  have hzrPoint : (fun y ↦ iteratedPartialDeriv (n := 2) [1, 0] G y) =
      fun y ↦ derivY (mixedDerivative2D (m + 1) ar E) (y 0) (y 1) := by
    funext y
    simp only [iteratedPartialDeriv]
    rw [hrfun]
    exact partialDeriv_uncurry_eq_derivY
      (mixedDerivative2D (m + 1) ar E) _ rfl hradDiff y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine .of_forall fun y ↦ ?_
    simpa [G, E, mixedDerivative2D, Function.iterate_succ_apply'] using (hrows y).2.1
  · filter_upwards [derivY_mixedDerivative_evenReflection_ae_of_contDiff m a F hFm1] with y hy
    refine Eq.trans ?_ hy
    simpa [G, E, mixedDerivative2D, Function.iterate_succ_apply'] using (hrows y).2.2.1
  · refine .of_forall fun y ↦ ?_
    simpa [G, E, mixedDerivative2D, Function.iterate_succ_apply'] using (hrows y).2.2.2.1
  · filter_upwards [derivY_mixedDerivative_evenReflection_ae_of_contDiff (m + 1) ar F hF]
      with y hy
    exact (congrFun hmixSwap y).trans ((congrFun hzrPoint y).trans
      (by simpa [E, ar, show m + 1 + 1 = m + 2 by omega] using hy))
  · have haxis : ∀ᵐ y ∂(volume : Measure (ℝ^2)), y 0 ≠ 0 := by
      rw [ae_iff]
      simpa only [Set.mem_ofPred_eq, not_not] using SobolevSpace.Weighted.volume_radialAxis_eq_zero
    have hdiff0 :=
      differentiableAt_mixedDerivative2D_axial_slice_of_contDiff m a F hFm1
    have hdiffz :=
      differentiableAt_mixedDerivative2D_axial_slice_of_contDiff (m + 1) az F hF
    filter_upwards [haxis] with y hy
    have hzzrow := (hrows y).2.2.2.2.2
    rw [show mixedDerivative2D 2 (0 : Fin 3) (mixedDerivative2D m a E) =
        derivY (derivY (mixedDerivative2D m a E)) by rfl] at hzzrow
    rw [hzzrow]
    have hfirst : derivY (mixedDerivative2D m a E) (y 0) =
        mixedDerivative2D (m + 1) az E (y 0) := by
      funext z
      simpa [E, az] using
        (derivY_mixedDerivative_evenReflection_away_axis
          m a (fun r z ↦ F (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z))
          (derivY_mixedDerivative_of_contDiff m a F hFm1)
          hdiff0 hy)
    rw [derivY, hfirst]
    exact derivY_mixedDerivative_evenReflection_away_axis
      (m + 1) az (fun r z ↦ F
        (EuclideanSpace.single 0 r + EuclideanSpace.single 1 z))
      (derivY_mixedDerivative_of_contDiff (m + 1) az F hF)
      hdiffz hy

/-- `derivY (derivY (mixedDerivative2D n 0 f)) = mixedDerivative2D (n + 2) 0 f`. -/
theorem derivY_sq_mixedDerivative_zero
    (n : ℕ) (f : ℝ → ℝ → ℝ) :
    derivY (derivY (mixedDerivative2D n 0 f)) =
      mixedDerivative2D (n + 2) 0 f := by
  simp [mixedDerivative2D, Function.iterate_succ_apply']

/-- `derivX (derivX (mixedDerivative2D n a f)) = mixedDerivative2D (n + 2) a.succ.succ f`. -/
theorem derivX_sq_mixedDerivative_succ
    (n : ℕ) (a : Fin (n + 1)) (f : ℝ → ℝ → ℝ) :
    derivX (derivX (mixedDerivative2D n a f)) =
      mixedDerivative2D (n + 2) a.succ.succ f := by
  simp only [mixedDerivative2D, Fin.val_succ]
  have hz : n + 2 - (a.val + 1 + 1) = n - a.val := by omega
  have hr : a.val + 1 + 1 = Nat.succ (Nat.succ a.val) := by omega
  rw [hz, hr, Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- If `0 ≤ R j b` for all `j` and `b`, then the sum of `R j b` over the six indices `(m, a)`,
`(m + 1, a)`, `(m + 1, a + 1)`, `(m + 2, a)`, `(m + 2, a + 1)` and `(m + 2, a + 2)`, with the radial
exponents added in `ℕ`, is at most `∑ j ∈ Finset.Icc m (m + 2), ∑ b : Fin (j + 1), R j b`. -/
theorem sixShiftedMixedRows_le_Icc_sum
    (m : ℕ) (a : Fin (m + 1))
    (R : ∀ j : ℕ, Fin (j + 1) → ℝ)
    (hR : ∀ j b, 0 ≤ R j b) :
    R m a +
      R (m + 1) ⟨a.val, by omega⟩ +
      R (m + 1) ⟨a.val + 1, by omega⟩ +
      R (m + 2) ⟨a.val, by omega⟩ +
      R (m + 2) ⟨a.val + 1, by omega⟩ +
      R (m + 2) ⟨a.val + 2, by omega⟩ ≤
        ∑ j ∈ Finset.Icc m (m + 2), ∑ b : Fin (j + 1), R j b := by
  have hsub {j : ℕ} (s : Finset (Fin (j + 1))) : ∑ b ∈ s, R j b ≤ ∑ b, R j b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ ↦ hR j i
  have h0 := hsub (j := m) {a}
  have h1 := hsub (j := m + 1) {⟨a.val, by omega⟩, ⟨a.val + 1, by omega⟩}
  have h2 := hsub (j := m + 2) {⟨a.val, by omega⟩, ⟨a.val + 1, by omega⟩, ⟨a.val + 2, by omega⟩}
  rw [Finset.sum_singleton] at h0
  rw [Finset.sum_pair (by simp [Fin.ext_iff])] at h1
  rw [Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_pair (by simp [Fin.ext_iff])] at h2
  have hIcc : Finset.Icc m (m + 2) = {m, m + 1, m + 2} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hIcc, Finset.sum_insert (by simp), Finset.sum_pair (by simp)]
  linarith

end SobolevSpace.Weighted
