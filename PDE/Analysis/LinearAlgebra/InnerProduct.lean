/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import PDE.Analysis.LinearAlgebra.LinearMap
import PDE.Analysis.Normed.YoungSplit

set_option linter.style.header false

/-!
# Inner products and norms of vectors

The lemmas expand the square of the norm of a sum or of a difference, bound an inner product by
norms, and compute norms and inner products in coordinates. The proofs use the Cauchy–Schwarz
inequality, the polarization identities of Mathlib and `nlinarith`.

## Main results

* `PDE.Analysis.exists_bilin_of_bounded_trilinear_form`: Let `E` be a real Hilbert space and
  `β : E → E → E → ℝ` a form that is additive and homogeneous in each of its three arguments, with
  `|β u v ψ| ≤ M * ‖u‖ * ‖v‖ * ‖ψ‖` and `0 ≤ M`. Then there is a continuous bilinear map
  `B : E →L[ℝ] E →L[ℝ] E` such that `inner ℝ (B u v) ψ = β u v ψ` for all `ψ` and
  `‖B u v‖ ≤ M * ‖u‖ * ‖v‖`. For fixed `u` and `v`, `B u v` is the Riesz representative of the
  bounded functional `ψ ↦ β u v ψ`, and bilinearity is checked by pairing with `ψ`.
* `PDE.Analysis.inner_sum_eq_zero_of_tendsto`: In a real inner product space, let sequences
  `a b c r e` satisfy `a n + b n + c n + r n + e n = 0` for all `n`, and let their inner products
  with a fixed vector `z` converge to the inner products of `a₀ b₀ c₀ r₀ e₀` with `z`. Then
  `inner ℝ (a₀ + b₀ + c₀ + r₀ + e₀) z = 0`.
* `PDE.Analysis.mem_of_weak_limit`: A closed convex set `K` in a real Hilbert space contains the
  weak limits of its sequences: if `u n ∈ K` for all `n` and `inner ℝ (u n) y → inner ℝ x y` for
  every `y`, then `x ∈ K`.
* `PDE.Analysis.norm_le_of_add_eq_zero`: In a normed additive group, if `f + c + a + r + e = 0` then
  `‖f‖ ≤ ‖c‖ + ‖a‖ + ‖r‖ + ‖e‖`.
* `PDE.Analysis.norm_smul_sub_smul_le_of_le`: Let `E` be a seminormed space over a normed field `𝕜`,
  with `a`, `a' : 𝕜` and `u`, `u' : E`. If `‖a'‖ ≤ M₁`, `‖u‖ ≤ M₂`, `‖a - a'‖ ≤ L₁ * d` and
  `‖u - u'‖ ≤ L₂ * d`, then `‖a • u - a' • u'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d`.
* `PDE.Analysis.abs_inner_sub_norm_sq_sub_le`: For vectors `a b a' b'` of a real inner product
  space, `|(inner ℝ a b - ‖b‖ ^ 2) - (inner ℝ a' b' - ‖b'‖ ^ 2)| ≤ ‖a - a'‖ * ‖b‖ +
  ‖b - b'‖ * ‖a'‖ + ‖b - b'‖ * ‖b‖ + ‖b - b'‖ * ‖b'‖`.
* `PDE.Analysis.enorm_euclideanSpace_single_one`: The vector
  `EuclideanSpace.single (0 : Fin 3) (1 : ℂ)` of `EuclideanSpace ℂ (Fin 3)` has extended norm
  `‖EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ₑ = 1`.
* `PDE.Analysis.enorm_smul_le_of_abs_le_one`: In a real normed space, if the real number `a`
  satisfies `|a| ≤ 1`, then `‖a • x‖ₑ ≤ ‖x‖ₑ` for every vector `x`.

There are 22 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Topology Filter

namespace PDE.Analysis

/-- For vectors `a b a' b'` of a real inner product space,
`|(inner ℝ a b - ‖b‖ ^ 2) - (inner ℝ a' b' - ‖b'‖ ^ 2)| ≤ ‖a - a'‖ * ‖b‖ + ‖b - b'‖ * ‖a'‖ + ‖b -
b'‖ * ‖b‖ + ‖b - b'‖ * ‖b'‖`. Proof idea: write the difference as four inner products, each with
`a - a'` or `b - b'` as a factor, and apply the Cauchy-Schwarz inequality to each. -/
theorem abs_inner_sub_norm_sq_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b a' b' : E) :
    |(inner ℝ a b - ‖b‖ ^ 2) - (inner ℝ a' b' - ‖b'‖ ^ 2)| ≤
      ‖a - a'‖ * ‖b‖ + ‖b - b'‖ * ‖a'‖ + ‖b - b'‖ * ‖b‖ + ‖b - b'‖ * ‖b'‖ := by
  have e1 : inner ℝ a b - inner ℝ a' b' = inner ℝ (a - a') b + inner ℝ a' (b - b') := by
    rw [inner_sub_left, inner_sub_right]; ring
  have e2 : ‖b‖ ^ 2 - ‖b'‖ ^ 2 = inner ℝ (b - b') b + inner ℝ b' (b - b') := by
    rw [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have i1 := abs_le.mp (abs_real_inner_le_norm (a - a') b)
  have i2 := abs_le.mp (abs_real_inner_le_norm a' (b - b'))
  have i3 := abs_le.mp (abs_real_inner_le_norm (b - b') b)
  have i4 := abs_le.mp (abs_real_inner_le_norm b' (b - b'))
  have n1 : ‖a'‖ * ‖b - b'‖ = ‖b - b'‖ * ‖a'‖ := mul_comm _ _
  have n2 : ‖b'‖ * ‖b - b'‖ = ‖b - b'‖ * ‖b'‖ := mul_comm _ _
  exact abs_le.mpr ⟨by linarith [i1.1, i2.1, i3.2, i4.2], by linarith [i1.2, i2.2, i3.1, i4.1]⟩

/-- The vector `EuclideanSpace.single (0 : Fin 3) (1 : ℂ)` of `EuclideanSpace ℂ (Fin 3)` has
extended norm `‖EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ₑ = 1`. -/
theorem enorm_euclideanSpace_single_one : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ₑ = 1 := by
  rw [← ofReal_norm, PiLp.norm_single]
  simp

/-- In a real normed space, if the real number `a` satisfies `|a| ≤ 1`, then `‖a • x‖ₑ ≤ ‖x‖ₑ` for
every vector `x`. -/
theorem enorm_smul_le_of_abs_le_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {a : ℝ}
    (ha : |a| ≤ 1) (x : X) :
    ‖a • x‖ₑ ≤ ‖x‖ₑ := by
  rw [eNorm_smul]
  calc ‖a‖ₑ * ‖x‖ₑ ≤ 1 * ‖x‖ₑ := by
        gcongr
        rw [Real.eNorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 ha
    _ = ‖x‖ₑ := one_mul _

/-- In `EuclideanSpace ℝ (Fin 3)`, the vector `EuclideanSpace.single i 0` is zero for every index
`i`. -/
theorem euclideanSpace_single_zero (i : Fin 3) : EuclideanSpace.single i (0 : ℝ) = 0 :=
  (PiLp.single_eq_zero_iff 2 i).mpr rfl

/-- Let `E` be a real Hilbert space and `β : E → E → E → ℝ` a form that is additive and homogeneous
in each of its three arguments, with `|β u v ψ| ≤ M * ‖u‖ * ‖v‖ * ‖ψ‖` and `0 ≤ M`. Then there is a
continuous bilinear map `B : E →L[ℝ] E →L[ℝ] E` such that `inner ℝ (B u v) ψ = β u v ψ` for all `ψ`
and `‖B u v‖ ≤ M * ‖u‖ * ‖v‖`. For fixed `u` and `v`, `B u v` is the Riesz representative of the
bounded functional `ψ ↦ β u v ψ`, and bilinearity is checked by pairing with `ψ`. -/
theorem exists_bilin_of_bounded_trilinear_form {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (β : E → E → E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hadd1 : ∀ u u' v ψ, β (u + u') v ψ = β u v ψ + β u' v ψ)
    (hsmul1 : ∀ (c : ℝ) u v ψ, β (c • u) v ψ = c * β u v ψ)
    (hadd2 : ∀ u v v' ψ, β u (v + v') ψ = β u v ψ + β u v' ψ)
    (hsmul2 : ∀ (c : ℝ) u v ψ, β u (c • v) ψ = c * β u v ψ)
    (hadd3 : ∀ u v ψ ψ', β u v (ψ + ψ') = β u v ψ + β u v ψ')
    (hsmul3 : ∀ (c : ℝ) u v ψ, β u v (c • ψ) = c * β u v ψ)
    (hbd : ∀ u v ψ, |β u v ψ| ≤ M * ‖u‖ * ‖v‖ * ‖ψ‖) :
    ∃ B : E →L[ℝ] E →L[ℝ] E, ∀ u v, (∀ ψ, inner ℝ (B u v) ψ = β u v ψ) ∧
      ‖B u v‖ ≤ M * ‖u‖ * ‖v‖ := by
  let L : E → E → E →L[ℝ] ℝ := fun u v ↦
    LinearMap.mkContinuous
      { toFun := β u v
        map_add' := hadd3 u v
        map_smul' := fun c ψ ↦ by simp only [hsmul3, smul_eq_mul, RingHom.id_apply] }
      (M * ‖u‖ * ‖v‖) (fun ψ ↦ by rw [Real.norm_eq_abs]; exact hbd u v ψ)
  let R : E → E → E := fun u v ↦ (InnerProductSpace.toDual ℝ E).symm (L u v)
  have hR : ∀ u v ψ, inner ℝ (R u v) ψ = β u v ψ := fun u v ψ ↦ by
    simp only [R, InnerProductSpace.toDual_symm_apply]
    rfl
  have hRn : ∀ u v, ‖R u v‖ ≤ M * ‖u‖ * ‖v‖ := fun u v ↦ by
    simp only [R, LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  let R₂ : E →ₗ[ℝ] E →ₗ[ℝ] E := LinearMap.mk₂ ℝ R
    (fun u u' v ↦ ext_inner_right ℝ fun ψ ↦ by
      rw [inner_add_left, hR, hR, hR, hadd1])
    (fun c u v ↦ ext_inner_right ℝ fun ψ ↦ by
      rw [real_inner_smul_left, hR, hR, hsmul1])
    (fun u v v' ↦ ext_inner_right ℝ fun ψ ↦ by
      rw [inner_add_left, hR, hR, hR, hadd2])
    (fun c u v ↦ ext_inner_right ℝ fun ψ ↦ by
      rw [real_inner_smul_left, hR, hR, hsmul2])
  refine ⟨LinearMap.mkContinuous₂ R₂ M (fun u v ↦ hRn u v), fun u v ↦ ⟨fun ψ ↦ ?_, ?_⟩⟩
  · exact hR u v ψ
  · exact hRn u v

/-- In a real inner product space, let sequences `a b c r e` satisfy
`a n + b n + c n + r n + e n = 0` for all `n`, and let their inner products with a fixed vector `z`
converge to the inner products of `a₀ b₀ c₀ r₀ e₀` with `z`. Then
`inner ℝ (a₀ + b₀ + c₀ + r₀ + e₀) z = 0`. -/
theorem inner_sum_eq_zero_of_tendsto {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) (a b c r e : ℕ → E) (a₀ b₀ c₀ r₀ e₀ : E)
    (ha : Tendsto (fun n ↦ inner ℝ (a n) z) atTop (𝓝 (inner ℝ a₀ z)))
    (hb : Tendsto (fun n ↦ inner ℝ (b n) z) atTop (𝓝 (inner ℝ b₀ z)))
    (hc : Tendsto (fun n ↦ inner ℝ (c n) z) atTop (𝓝 (inner ℝ c₀ z)))
    (hr : Tendsto (fun n ↦ inner ℝ (r n) z) atTop (𝓝 (inner ℝ r₀ z)))
    (he : Tendsto (fun n ↦ inner ℝ (e n) z) atTop (𝓝 (inner ℝ e₀ z)))
    (h0 : ∀ n, a n + b n + c n + r n + e n = 0) :
    inner ℝ (a₀ + b₀ + c₀ + r₀ + e₀) z = 0 := by
  have hs := (((ha.add hb).add hc).add hr).add he
  have hz : ∀ n, inner ℝ (a n) z + inner ℝ (b n) z + inner ℝ (c n) z + inner ℝ (r n) z
      + inner ℝ (e n) z = 0 := fun n ↦ by
    simp only [← inner_add_left, h0 n, inner_zero_left]
  have h := tendsto_nhds_unique tendsto_const_nhds (hs.congr hz)
  simp only [inner_add_left]
  exact h.symm

/-- A closed convex set `K` in a real Hilbert space contains the weak limits of its sequences: if
`u n ∈ K` for all `n` and `inner ℝ (u n) y → inner ℝ x y` for every `y`, then `x ∈ K`. The proof
separates a point `x ∉ K` from `K` by a continuous linear functional (Hahn-Banach), written as an
inner product with a fixed vector, and gets a contradiction in the limit. -/
theorem mem_of_weak_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (K : Set E) (hK : Convex ℝ K) (hKc : IsClosed K) (u : ℕ → E) (hu : ∀ n, u n ∈ K) (x : E)
    (hx : ∀ y : E, Filter.Tendsto (fun n ↦ inner ℝ (u n) y) Filter.atTop (nhds (inner ℝ x y))) :
    x ∈ K := by
  by_contra hxK
  obtain ⟨f, c, hfx, hfK⟩ := geometric_hahn_banach_point_closed hK hKc hxK
  set z : E := (InnerProductSpace.toDual ℝ E).symm f
  have hz : ∀ a : E, f a = inner ℝ a z := fun a ↦ by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have hge : c ≤ inner ℝ x z :=
    ge_of_tendsto (hx z) (Eventually.of_forall fun n ↦ by
      rw [← hz]; exact (hfK _ (hu n)).le)
  rw [hz] at hfx
  linarith

/-- For complex numbers `X`, `Y` and reals `c`, `s`, `m` with `0 < c`, `s ≠ 0` and
`c ^ 2 + s ^ 2 = 1`,
`(m + 1) * (m + 2) * (c * ‖Y‖ ^ 2) - ((m * c + 2 * c + c ^ 3 / s ^ 2) * ‖Y‖ ^ 2 + (m * s - c ^ 2 /
s) * (2 * inner ℝ Y X)) ≤ c * (‖X‖ ^ 2 + m ^ 2 * ‖Y‖ ^ 2 / c ^ 2)`. With `W = m * s - c ^ 2 /
s`, the right side minus the left side equals `((c * X.re + W * Y.re) ^ 2 + (c * X.im + W * Y.im) ^
2) / c`, which is nonnegative. -/
theorem mul_norm_sq_sub_add_inner_le (X Y : ℂ) (c s m : ℝ) (hc : 0 < c) (hs : s ≠ 0)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (m + 1) * (m + 2) * (c * ‖Y‖ ^ 2) -
        ((m * c + 2 * c + c ^ 3 / s ^ 2) * ‖Y‖ ^ 2 + (m * s - c ^ 2 / s) * (2 * inner ℝ Y X)) ≤
      c * (‖X‖ ^ 2 + m ^ 2 * ‖Y‖ ^ 2 / c ^ 2) := by
  set W : ℝ := m * s - c ^ 2 / s with hW
  have hin : inner ℝ Y X = Y.re * X.re + Y.im * X.im := by
    simp [Complex.inner, mul_comm]
  have hX : ‖X‖ ^ 2 = X.re ^ 2 + X.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hY : ‖Y‖ ^ 2 = Y.re ^ 2 + Y.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hin, hX, hY, ← sub_nonneg]
  have e : c * (X.re ^ 2 + X.im ^ 2 + m ^ 2 * (Y.re ^ 2 + Y.im ^ 2) / c ^ 2) -
      ((m + 1) * (m + 2) * (c * (Y.re ^ 2 + Y.im ^ 2)) -
        ((m * c + 2 * c + c ^ 3 / s ^ 2) * (Y.re ^ 2 + Y.im ^ 2) + W *
            (2 * (Y.re * X.re + Y.im * X.im)))) =
      ((c * X.re + W * Y.re) ^ 2 + (c * X.im + W * Y.im) ^ 2) / c := by
    rw [hW]
    field_simp
    linear_combination (-(m ^ 2 * (Y.re ^ 2 + Y.im ^ 2) * s ^ 2)) * hcs
  rw [e]
  positivity

/-- For vectors `a`, `b` of a real normed space and a real `c`,
`‖a + c • b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * c ^ 2 * ‖b‖ ^ 2`. -/
theorem norm_add_smul_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : E) (c : ℝ) :
    ‖a + c • b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * c ^ 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a (c • b)
  rw [norm_smul, Real.norm_eq_abs] at h
  have h2 : ‖a + c • b‖ ^ 2 ≤ (‖a‖ + |c| * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_abs c, sq_nonneg (‖a‖ - |c| * ‖b‖)]

/-- Let `c` and `v i` for `i : Fin k` be vectors of a real normed space, and `q i` reals with
`|q i| ≤ M` for all `i`. If `‖c‖ ≤ Nc * x` and `‖v i‖ ≤ N i * x` for all `i`, then
`‖c + ∑ i, q i • v i‖ ≤ (Nc + |M| * ∑ i, N i) * x`. The proof is the triangle inequality with
`‖q i • v i‖ ≤ |M| * (N i * x)`. -/
theorem norm_add_sum_smul_le {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E)
    (v : Fin k → E)
    (q : Fin k → ℝ) {M Nc x : ℝ} (N : Fin k → ℝ) (hq : ∀ i, |q i| ≤ M) (hc : ‖c‖ ≤ Nc * x)
    (hv : ∀ i, ‖v i‖ ≤ N i * x) :
    ‖c + ∑ i, q i • v i‖ ≤ (Nc + |M| * ∑ i, N i) * x := by
  have hsum : ‖∑ i, q i • v i‖ ≤ ∑ i, |M| * (N i * x) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul ((hq i).trans (le_abs_self M)) (hv i) (norm_nonneg _) (abs_nonneg _)
  have e : ∑ i, |M| * (N i * x) = |M| * (∑ i, N i) * x := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  calc ‖c + ∑ i, q i • v i‖ ≤ ‖c‖ + ‖∑ i, q i • v i‖ := norm_add_le _ _
    _ ≤ Nc * x + |M| * (∑ i, N i) * x := add_le_add hc (hsum.trans (le_of_eq e))
    _ = (Nc + |M| * ∑ i, N i) * x := by ring

/-- Let `a`, `a'` be vectors of a real normed space and `s`, `s'` reals with `0 ≤ s`, `0 < s'` and
`‖a‖ ≤ s`. Then `‖s⁻¹ • a - s'⁻¹ • a'‖ * s' ≤ ‖a - a'‖ + |s - s'|`. The proof writes
`s⁻¹ • a - s'⁻¹ • a' = s'⁻¹ • (a - a') + (s⁻¹ - s'⁻¹) • a` when `0 < s`, and treats `s = 0`, where
`a = 0`, separately. -/
theorem norm_inv_smul_sub_inv_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a a' : E) {s s' : ℝ}
    (hs : 0 ≤ s) (hs' : 0 < s') (ha : ‖a‖ ≤ s) :
    ‖s⁻¹ • a - s'⁻¹ • a'‖ * s' ≤ ‖a - a'‖ + |s - s'| := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have ha0 : a = 0 := norm_le_zero_iff.mp ha
    subst ha0
    have e : ‖(0 : ℝ)⁻¹ • (0 : E) - s'⁻¹ • a'‖ * s' = ‖a'‖ := by
      rw [smul_zero, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs']
      field_simp
    rw [e, zero_sub, norm_neg]
    linarith [abs_nonneg (0 - s')]
  · have e : s⁻¹ • a - s'⁻¹ • a' = s'⁻¹ • (a - a') + (s⁻¹ - s'⁻¹) • a := by
      rw [smul_sub, sub_smul]
      abel
    have h1 : ‖s'⁻¹ • (a - a')‖ = s'⁻¹ * ‖a - a'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs']
    have h2 : ‖(s⁻¹ - s'⁻¹) • a‖ ≤ |s - s'| / s' := by
      rw [norm_smul, Real.norm_eq_abs]
      have e2 : s⁻¹ - s'⁻¹ = (s' - s) / (s * s') := by
        field_simp
      rw [e2, abs_div, abs_of_pos (mul_pos hpos hs'), abs_sub_comm]
      calc |s - s'| / (s * s') * ‖a‖ ≤ |s - s'| / (s * s') * s := by gcongr
        _ = |s - s'| / s' := by field_simp
    have h3 : ‖s⁻¹ • a - s'⁻¹ • a'‖ ≤ s'⁻¹ * ‖a - a'‖ + |s - s'| / s' := by
      rw [e]
      exact (norm_add_le _ _).trans (by rw [h1]; linarith [h2])
    calc ‖s⁻¹ • a - s'⁻¹ • a'‖ * s' ≤ (s'⁻¹ * ‖a - a'‖ + |s - s'| / s') * s' :=
          mul_le_mul_of_nonneg_right h3 hs'.le
      _ = ‖a - a'‖ + |s - s'| := by field_simp

/-- In a normed additive group, if `f + c + a + r + e = 0` then `‖f‖ ≤ ‖c‖ + ‖a‖ + ‖r‖ + ‖e‖`. -/
theorem norm_le_of_add_eq_zero {E : Type*} [NormedAddCommGroup E] {f c a r e : E}
    (h : f + c + a + r + e = 0) : ‖f‖ ≤ ‖c‖ + ‖a‖ + ‖r‖ + ‖e‖ := by
  have he : f = -(c + a + r + e) := by
    rw [eq_neg_iff_add_eq_zero, ← h]
    abel
  rw [he, norm_neg]
  linarith [norm_add_le (c + a + r) e, norm_add_le (c + a) r, norm_add_le c a]

/-- For real `w` and `x` with `0 ≤ w ≤ 1` and `0 ≤ x ≤ 1`, the pair `(w, x)` has norm at most `1` in
`ℝ × ℝ`. -/
theorem norm_prodMk_le_one_of_le_one {w x : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : ‖((w, x) : ℝ × ℝ)‖ ≤ 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw0, abs_of_nonneg hx0]
  exact max_le hw1 hx1

/-- The pair `(1, 0)` in `ℝ × ℝ`, with the product norm (the maximum of the two absolute values),
has norm at most `1`. -/
theorem norm_prod_one_zero_le_one : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]

/-- The pair `(0, 1)` in `ℝ × ℝ`, with the product norm (the maximum of the two absolute values),
has norm at most `1`. -/
theorem norm_prod_zero_one_le_one : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]

/-- Let `E` be a seminormed space over a normed field `𝕜`, with `a`, `a' : 𝕜` and `u`, `u' : E`. If
`‖a'‖ ≤ M₁`, `‖u‖ ≤ M₂`, `‖a - a'‖ ≤ L₁ * d` and `‖u - u'‖ ≤ L₂ * d`, then
`‖a • u - a' • u'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d`. The proof writes
`a • u - a' • u' = (a - a') • u + a' • (u - u')`. -/
theorem norm_smul_sub_smul_le_of_le {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    {a a' : 𝕜} {u u' : E} {M₁ M₂ L₁ L₂ d : ℝ} (ha' : ‖a'‖ ≤ M₁) (hu : ‖u‖ ≤ M₂)
    (hda : ‖a - a'‖ ≤ L₁ * d) (hdu : ‖u - u'‖ ≤ L₂ * d) :
    ‖a • u - a' • u'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d := by
  have h0 : a • u - a' • u' = (a - a') • u + a' • (u - u') := by
    rw [sub_smul, smul_sub]
    abel
  rw [h0]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  calc ‖a - a'‖ * ‖u‖ + ‖a'‖ * ‖u - u'‖ ≤ L₁ * d * M₂ + M₁ * (L₂ * d) :=
        add_le_add (mul_le_mul hda hu (norm_nonneg _) ((norm_nonneg _).trans hda))
          (mul_le_mul ha' hdu (norm_nonneg _) ((norm_nonneg _).trans ha'))
    _ = _ := by ring

/-- For vectors `f s g k v` of a real inner product space with `s = k`, `g = v` and
`inner ℝ f k = ‖k‖ ^ 2 + (1 / 4) * ‖v‖ ^ 2`, one has `‖s‖ ^ 2 + (1 / 4) * ‖g‖ ^ 2 ≤ inner ℝ f s`. -/
theorem norm_sq_add_le_inner_of_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f s g k v : V) (hs : s = k) (hg : g = v)
    (h : inner ℝ f k = ‖k‖ ^ 2 + (1 / 4 : ℝ) * ‖v‖ ^ 2) :
    ‖s‖ ^ 2 + (1 / 4 : ℝ) * ‖g‖ ^ 2 ≤ inner ℝ f s := by
  subst hs
  subst hg
  exact h.symm.le

/-- For `x` and `y` in a normed additive commutative group,
`‖x - y‖ ^ 6 ≤ 64 * ‖x‖ ^ 6 + 64 * ‖y‖ ^ 6`. The proof uses `‖x - y‖ ≤ 2 * max ‖x‖ ‖y‖` and
`max ‖x‖ ‖y‖ ^ 6 ≤ ‖x‖ ^ 6 + ‖y‖ ^ 6`. -/
theorem norm_sub_pow_six_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x - y‖ ^ 6 ≤ 64 * ‖x‖ ^ 6 + 64 * ‖y‖ ^ 6 := by
  have h1 : ‖x - y‖ ≤ 2 * max ‖x‖ ‖y‖ :=
    (norm_sub_le x y).trans (by linarith [le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖])
  have h2 : ‖x - y‖ ^ 6 ≤ (2 * max ‖x‖ ‖y‖) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) h1 6
  have h3 : max ‖x‖ ‖y‖ ^ 6 ≤ ‖x‖ ^ 6 + ‖y‖ ^ 6 := by
    rcases le_total ‖x‖ ‖y‖ with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg x) 6]
    · rw [max_eq_left h]; linarith [pow_nonneg (norm_nonneg y) 6]
  calc ‖x - y‖ ^ 6 ≤ (2 * max ‖x‖ ‖y‖) ^ 6 := h2
    _ = 64 * max ‖x‖ ‖y‖ ^ 6 := by ring
    _ ≤ 64 * (‖x‖ ^ 6 + ‖y‖ ^ 6) := by linarith
    _ = 64 * ‖x‖ ^ 6 + 64 * ‖y‖ ^ 6 := by ring

/-- Let `u` be a finite set of integers, `f : ℤ → E` a function into a normed additive commutative
group and `w ≥ 0`. If `‖f n‖ ≤ C n * w` for all `n ∈ u`, then
`‖∑ n ∈ u, f n‖ ≤ (∑ n ∈ u, |C n|) * w`. -/
theorem norm_sum_le_sum_abs_mul (u : Finset ℤ) {E : Type*} [NormedAddCommGroup E] (f : ℤ → E)
    (C : ℤ → ℝ) (w : ℝ)
    (hw : 0 ≤ w) (h : ∀ n ∈ u, ‖f n‖ ≤ C n * w) : ‖∑ n ∈ u, f n‖ ≤ (∑ n ∈ u, |C n|) * w := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun n hn ↦ (h n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)

/-- In a real normed space,
`‖∑ i ∈ s, (a i • G i + b i • F i)‖ ≤ ∑ i ∈ s, (|a i| * ‖G i‖ + |b i| * ‖F i‖)` for real
coefficients `a i`, `b i` and vectors `G i`, `F i`, summed over a finite set `s`. -/
theorem norm_sum_smul_add_smul_le {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (a b : ι → ℝ) (G F : ι → V) :
    ‖∑ i ∈ s, (a i • G i + b i • F i)‖ ≤ ∑ i ∈ s, (|a i| * ‖G i‖ + |b i| * ‖F i‖) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  simp only [norm_smul, Real.norm_eq_abs]

/-- In the `L²` product `WithLp 2 (E × E)` of a normed additive group `E` with itself, the norm of
the pair `(a, b)` is at most `‖a‖ + ‖b‖`. This follows from `‖(a, b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2`. -/
theorem norm_toLp_two_prod_le_add {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖WithLp.toLp 2 (a, b)‖ ≤ ‖a‖ + ‖b‖ := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (a, b))
  have h0 : 0 ≤ ‖a‖ := norm_nonneg _
  have h0' : 0 ≤ ‖b‖ := norm_nonneg _
  have h1 : ‖(WithLp.toLp 2 (a, b)).fst‖ = ‖a‖ := rfl
  have h2 : ‖(WithLp.toLp 2 (a, b)).snd‖ = ‖b‖ := rfl
  rw [h1, h2] at hsq
  nlinarith [norm_nonneg (WithLp.toLp 2 (a, b))]

/-- For complex numbers `X`, `Y` and reals `c`, `s`, `m` with `0 < c` and `c ^ 2 + s ^ 2 = 1`,
`m ^ 2 * c * ‖Y‖ ^ 2 - m * s * (2 * inner ℝ Y X) ≤ c * (‖X‖ ^ 2 + m ^ 2 * ‖Y‖ ^ 2 / c ^
2)`. The right side minus the left side equals `((c * X.re + m * s * Y.re) ^ 2 + (c * X.im + m * s *
Y.im) ^ 2) / c`, which is nonnegative. -/
theorem sq_mul_norm_sq_sub_inner_le (X Y : ℂ) (c s m : ℝ) (hc : 0 < c) (hcs : c ^ 2 + s ^ 2 = 1) :
    m ^ 2 * c * ‖Y‖ ^ 2 - m * s * (2 * inner ℝ Y X) ≤ c * (‖X‖ ^ 2 + m ^ 2 * ‖Y‖ ^ 2 / c ^ 2) := by
  have hN : 0 ≤ (c * X.re + m * s * Y.re) ^ 2 + (c * X.im + m * s * Y.im) ^ 2 := by positivity
  have hin : inner ℝ Y X = Y.re * X.re + Y.im * X.im := by
    simp [Complex.inner, mul_comm]
  have hX : ‖X‖ ^ 2 = X.re ^ 2 + X.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hY : ‖Y‖ ^ 2 = Y.re ^ 2 + Y.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hin, hX, hY]
  rw [← sub_nonneg]
  have e : c * (X.re ^ 2 + X.im ^ 2 + m ^ 2 * (Y.re ^ 2 + Y.im ^ 2) / c ^ 2) -
      (m ^ 2 * c * (Y.re ^ 2 + Y.im ^ 2) - m * s * (2 * (Y.re * X.re + Y.im * X.im))) =
      ((c * X.re + m * s * Y.re) ^ 2 + (c * X.im + m * s * Y.im) ^ 2) / c := by
    field_simp
    linear_combination (-(m ^ 2 * (Y.re ^ 2 + Y.im ^ 2))) * hcs
  rw [e]
  positivity

/-- Let `K : ι → κ → ℝ` over finite types have orthonormal columns:
`∑ i, K i p * K i q = if p = q then 1 else 0` for all `p`, `q`. Then for `x z : κ → ℂ`,
`∑ i, (∑ p, (K i p : ℂ) * x p) * conj (∑ q, (K i q : ℂ) * z q) = ∑ p, x p * conj (z
p)`. The proof expands the product, exchanges the sums and collapses the double sum with the
orthonormality relation. -/
theorem sum_mul_conj_of_orthonormal_columns {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (K : ι → κ → ℝ)
    (hK : ∀ p q, ∑ i, K i p * K i q = if p = q then 1 else 0) (x z : κ → ℂ) :
    ∑ i, (∑ p, (K i p : ℂ) * x p) * (starRingEnd ℂ) (∑ q, (K i q : ℂ) * z q) =
      ∑ p, x p * (starRingEnd ℂ) (z p) := by
  simp_rw [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.sum_comm]
  have e : ∀ q, ∑ i, (K i p : ℂ) * x p * ((K i q : ℂ) * (starRingEnd ℂ) (z q)) =
      ((∑ i, K i p * K i q : ℝ) : ℂ) * (x p * (starRingEnd ℂ) (z q)) := by
    intro q
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [e, hK]
  simp only [apply_ite (fun r : ℝ ↦ (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
      one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Let `x : ℕ → E` be a sequence in a real inner product space with `‖x n‖ ≤ B` for all `n`, and
let `D` be a dense set. If `inner ℝ (x n) z → inner ℝ x₀ z` as `n → ∞` for every `z ∈ D`, then the
same holds for every `z : E`. Proof idea: approximate `z` by a point of `D` and use the
Cauchy-Schwarz inequality with the uniform bound on `‖x n‖`. -/
theorem tendsto_inner_of_dense {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : Set E}
    (hD : Dense D) {x : ℕ → E} {x₀ : E} {B : ℝ} (hB : ∀ n, ‖x n‖ ≤ B)
    (h : ∀ z ∈ D, Tendsto (fun n ↦ inner ℝ (x n) z) atTop (nhds (inner ℝ x₀ z))) (z : E) :
    Tendsto (fun n ↦ inner ℝ (x n) z) atTop (nhds (inner ℝ x₀ z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB0 : 0 ≤ B := (norm_nonneg (x 0)).trans (hB 0)
  set K := B + ‖x₀‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨w, hwD, hzw⟩ := hD.exists_dist_lt z (show 0 < ε / (2 * K) by positivity)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (h w hwD) (ε / 2) (by positivity)
  refine ⟨M, fun n hn ↦ ?_⟩
  have h1 := hM n hn
  rw [Real.dist_eq] at h1 ⊢
  rw [dist_eq_norm] at hzw
  have e : inner ℝ (x n) z - inner ℝ x₀ z =
      (inner ℝ (x n) w - inner ℝ x₀ w) + inner ℝ (x n) (z - w) - inner ℝ x₀ (z - w) := by
    rw [inner_sub_right, inner_sub_right]
    ring
  have a1 : |inner ℝ (x n) (z - w)| ≤ B * ‖z - w‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))
  have a2 : |inner ℝ x₀ (z - w)| ≤ ‖x₀‖ * ‖z - w‖ := abs_real_inner_le_norm _ _
  have a3 : (B + ‖x₀‖) * ‖z - w‖ ≤ K * (ε / (2 * K)) := by
    apply mul_le_mul (by linarith) hzw.le (norm_nonneg _) hK0.le
  have a4 : K * (ε / (2 * K)) = ε / 2 := by field_simp
  rw [e]
  calc |inner ℝ (x n) w - inner ℝ x₀ w + inner ℝ (x n) (z - w) - inner ℝ x₀ (z - w)|
      ≤ |inner ℝ (x n) w - inner ℝ x₀ w| + |inner ℝ (x n) (z - w)| + |inner ℝ x₀ (z - w)| := by
        have := abs_sub (inner ℝ (x n) w - inner ℝ x₀ w + inner ℝ (x n) (z - w))
            (inner ℝ x₀ (z - w))
        have := abs_add_le (inner ℝ (x n) w - inner ℝ x₀ w) (inner ℝ (x n) (z - w))
        linarith
    _ < ε := by nlinarith

/-- For complex numbers `w` and `w'` with `w' ≠ 0`, `‖w / ‖w‖ - w' / ‖w'‖‖ * ‖w'‖ ≤ 2 * ‖w - w'‖`,
where the norms in the denominators are coerced to `ℂ`. The case `w = 0` is included. -/
theorem norm_div_norm_sub_div_norm_le (w w' : ℂ) (hw' : w' ≠ 0) :
    ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖ * ‖w'‖ ≤ 2 * ‖w - w'‖ := by
  have e : ∀ z : ℂ, z / (‖z‖ : ℂ) = ‖z‖⁻¹ • z := fun z ↦ by
    rw [Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]
  rw [e, e]
  have h := norm_inv_smul_sub_inv_smul_le (E := ℂ) w w' (norm_nonneg w)
      (norm_pos_iff.mpr hw') le_rfl
  have h2 : |‖w‖ - ‖w'‖| ≤ ‖w - w'‖ := abs_norm_sub_norm_le w w'
  linarith

/-- Weak lower semicontinuity of a sum of squared norms: in a real Hilbert space `E`, let `u n`
converge weakly to `u₀`, that is `inner ℝ (u n) y → inner ℝ u₀ y` for every `y`, and let
`L₀ : E →L[ℝ] F₀` and `L j : E →L[ℝ] F`, `j : Fin 3`, be continuous linear maps into real normed
spaces. If `‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 ≤ c` for all `n`, then
`‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 ≤ c`. The sublevel set of this convex continuous functional is
closed and convex, so it contains the weak limit. -/
theorem quadratic_le_of_weak {E F₀ F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L₀ : E →L[ℝ] F₀) (L : Fin 3 → E →L[ℝ] F) (u : ℕ → E) (u₀ : E)
    (hw : ∀ y, Tendsto (fun n ↦ inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y))) (c : ℝ)
    (hc : ∀ n, ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 ≤ c) :
    ‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 ≤ c := by
  have hQ : ConvexOn ℝ Set.univ
      (fun x ↦ ‖L₀ x‖ ^ 2 + (‖L 0 x‖ ^ 2 + ‖L 1 x‖ ^ 2 + ‖L 2 x‖ ^ 2)) :=
    (convexOn_norm_sq_comp L₀).add
      (((convexOn_norm_sq_comp (L 0)).add (convexOn_norm_sq_comp (L 1))).add
        (convexOn_norm_sq_comp (L 2)))
  have hK := hQ.convex_le c
  have hcl : IsClosed {x ∈ (Set.univ : Set E) |
      ‖L₀ x‖ ^ 2 + (‖L 0 x‖ ^ 2 + ‖L 1 x‖ ^ 2 + ‖L 2 x‖ ^ 2) ≤ c} := by
    simp only [Set.mem_univ, true_and]
    exact isClosed_le (by fun_prop) continuous_const
  have hm := mem_of_weak_limit _ hK hcl u (fun n ↦ ⟨Set.mem_univ _, by
    have := hc n
    simpa only [Fin.sum_univ_three] using this⟩) u₀ hw
  have := hm.2
  simpa only [Fin.sum_univ_three] using this

/-- In a real Hilbert space `E`, let `u n` converge weakly to `u₀` (`inner ℝ (u n) y → inner ℝ u₀ y`
for every `y`), let `κ n → κ₀` in `Fin k → ℝ`, and let `L₀` and `L j`, `j : Fin 3`, be continuous
linear maps from `E` into real normed spaces. If
`√(‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2) ≤ B` for all `n`, then
`√(‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 + ∑ i, κ₀ i ^ 2) ≤ B`. The proof squares the bound, passes to the
limit in `∑ i, κ n i ^ 2`, and applies weak lower semicontinuity of the remaining sum of squared
norms to a tail of the sequence. -/
theorem sqrt_quadratic_le_of_weak {E F₀ F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} (L₀ : E →L[ℝ] F₀) (L : Fin 3 → E →L[ℝ] F) (u : ℕ → E) (u₀ : E)
    (hu : ∀ y, Tendsto (fun n ↦ inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (κ : ℕ → Fin k → ℝ) (κ₀ : Fin k → ℝ) (hκ : Tendsto κ atTop (𝓝 κ₀)) (B : ℝ)
    (hB : ∀ n, Real.sqrt (‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2) ≤ B) :
    Real.sqrt (‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 + ∑ i, κ₀ i ^ 2) ≤ B := by
  have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans (hB 0)
  have hsq : ∀ n, ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2 ≤ B ^ 2 := fun n ↦ by
    have h1 : 0 ≤ ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2 := by positivity
    calc ‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2
        = Real.sqrt (‖L₀ (u n)‖ ^ 2 + ∑ j, ‖L j (u n)‖ ^ 2 + ∑ i, κ n i ^ 2) ^ 2 :=
          (Real.sq_sqrt h1).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hB n) 2
  have hκs : Tendsto (fun n ↦ ∑ i, κ n i ^ 2) atTop (𝓝 (∑ i, κ₀ i ^ 2)) :=
    tendsto_finsetSum _ fun i _ ↦ ((continuous_apply i).tendsto κ₀ |>.comp hκ).pow 2
  have hlim : ‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 ≤ B ^ 2 - ∑ i, κ₀ i ^ 2 := by
    by_contra hcon
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 - (B ^ 2 - ∑ i, κ₀ i ^ 2)) / 2 :=
      ⟨_, rfl⟩
    have hεpos : 0 < ε := by rw [hε]; linarith [not_le.1 hcon]
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hκs.eventually (Ioi_mem_nhds
      (show ∑ i, κ₀ i ^ 2 - ε < ∑ i, κ₀ i ^ 2 by linarith)))
    have hc : ∀ n, ‖L₀ (u (n + N))‖ ^ 2 + ∑ j, ‖L j (u (n + N))‖ ^ 2 ≤
        B ^ 2 - ∑ i, κ₀ i ^ 2 + ε := fun n ↦ by
      have h1 := hsq (n + N)
      have h2 : ∑ i, κ₀ i ^ 2 - ε < ∑ i, κ (n + N) i ^ 2 := hN (n + N) (Nat.le_add_left N n)
      linarith
    have h := quadratic_le_of_weak L₀ L (fun n ↦ u (n + N)) u₀
      (fun y ↦ (hu y).comp (tendsto_add_atTop_nat N)) _ hc
    linarith [not_le.1 hcon]
  calc Real.sqrt (‖L₀ u₀‖ ^ 2 + ∑ j, ‖L j u₀‖ ^ 2 + ∑ i, κ₀ i ^ 2) ≤ Real.sqrt (B ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = B := Real.sqrt_sq hB0

/-- In a seminormed additive commutative group, for all `a`, `b` and every natural number `n`,
`‖a + b‖ ^ n ≤ 2 ^ n * (‖a‖ ^ n + ‖b‖ ^ n)`. The norm of the sum is at most twice the larger
of `‖a‖` and `‖b‖`. -/
theorem norm_add_pow_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) (n : ℕ) :
    ‖a + b‖ ^ n ≤ 2 ^ n * (‖a‖ ^ n + ‖b‖ ^ n) := by
  have hab := norm_add_le a b
  rcases le_total ‖a‖ ‖b‖ with h | h
  · calc ‖a + b‖ ^ n ≤ (2 * ‖b‖) ^ n :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
      _ = 2 ^ n * ‖b‖ ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (‖a‖ ^ n + ‖b‖ ^ n) := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)
  · calc ‖a + b‖ ^ n ≤ (2 * ‖a‖) ^ n :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
      _ = 2 ^ n * ‖a‖ ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (‖a‖ ^ n + ‖b‖ ^ n) := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)

/-- In a seminormed additive commutative group, for all `a`, `b` and every real `δ > 0`,
`‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2`. This is `PDE.norm_sub_sq_le_young` at `-b`.
-/
theorem norm_add_sq_le_young {E : Type*} [SeminormedAddCommGroup E] (a b : E) {δ : ℝ}
    (hδ : 0 < δ) : ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2 := by
  simpa [sub_neg_eq_add, one_div] using PDE.norm_sub_sq_le_young a (-b) hδ

/-- For every index `i` and real `a`, the vector of `ℝ³` with coordinate `i` equal to `a` and the
other coordinates zero is `a` times the vector with coordinate `i` equal to one:
`EuclideanSpace.single i a = a • EuclideanSpace.single i 1`. -/
theorem euclideanSpace_single_eq_smul_single_one (i : Fin 3) (a : ℝ) :
    EuclideanSpace.single i a = a • EuclideanSpace.single i (1 : ℝ) := by
  ext j; by_cases h : j = i <;> simp [h]

end PDE.Analysis
