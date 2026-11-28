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
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Separation.CompletelyRegular
public import PDE.Analysis.Scalar.Inequalities

set_option linter.style.header false

/-!
# Linear and continuous linear maps

The lemmas evaluate compositions and sums of continuous linear maps, bound operator norms, and state
how a linear isometry acts on norms and inner products. The proofs use
`ContinuousLinearMap.le_opNorm`, the extensionality lemmas and `simp`.

## Main results

* `PDE.Analysis.exists_inverse_of_compact_bordered`: Right inverse of a bordered operator
  `Bd z = (z.1 + c z.1 + a z.2, q z.1)` on `H × (Fin k → ℝ)`, with `H` a real Banach space. Suppose
  a subspace `V` of `H` is preserved by `c` and contains the range of `a`, `Pr` maps `H` into `V`
  and fixes `V`, `z ↦ (c (Pr z.1), 0)` is a compact continuous linear map `A`, and
  `z ↦ (a z.2, q (Pr z.1) - z.2)` is a composition `M ∘ S` of continuous linear maps through
  `(Fin k → ℝ) × (Fin k → ℝ)`; if `Bd x = 0` and `x.1 ∈ V` imply `x = 0`, then there is a continuous
  linear `T` with `(T y).1 ∈ V` and `Bd (T y) = y` for every `y` with `y.1 ∈ V`.
* `PDE.Analysis.exists_norm_clm_apply_le_of_tendsto`: A convergent sequence of continuous linear
  maps is uniformly bounded: if `T n → T₀` in `E →L[ℝ] F`, with `E` and `F` real normed spaces, then
  there is `C` with `0 ≤ C` and `‖T n x‖ ≤ C * ‖x‖` for all `n` and `x`.
* `PDE.Analysis.exists_opNorm_le_of_norm_finBasis_le`: Let `E` be a finite-dimensional real normed
  space and `δ > 0`. There is `η > 0` such that every continuous linear map `D` from `E` to a real
  normed space with `‖D (Module.finBasis ℝ E i)‖ ≤ η` for all `i` has `‖D‖ ≤ δ`. One can take
  `η = δ / (K + 1)`, where `K` is the sum of the operator norms of the coordinate functionals of the
  basis.
* `PDE.Analysis.exists_opNorm_le_of_pointwise_bound`: Let `E` be a finite-dimensional real normed
  space, `Y` a real normed space and `g : ℝ → E → Y`, and suppose that for each `e` there are
  `T₀ > 0` and `B` with `‖g T e‖ ≤ B` for `0 < T < T₀`. Then there are `T₁ > 0` and `CJ ≥ 0` such
  that, for `0 < T < T₁`, every continuous linear map `Jt : E →L[ℝ] Y` with `Jt e = g T e` for all
  `e` has `‖Jt‖ ≤ CJ`.
* `PDE.Analysis.isCompactOperator_of_cauchy_subseq`: Sequential criterion for a compact operator:
  let `T : E →L[ℝ] F` be a continuous linear map of real normed spaces with `F` complete. If every
  sequence `f` with `‖f n‖ ≤ 1` has a strictly increasing `φ : ℕ → ℕ` such that `n ↦ T (f (φ n))`
  satisfies the Cauchy condition, then `T` is a compact operator.
* `PDE.Analysis.norm_iterate_linearIsometryEquiv`: Iterates of a linear isometric equivalence
  `e : E ≃ₗᵢ[ℝ] E` of a real seminormed space preserve the norm: `‖e^[j] y‖ = ‖y‖` for every
  `j : ℕ`.
* `PDE.Analysis.opNorm_le_of_symm_of_diag_le`: A symmetric continuous bilinear map
  `K : E →L[ℝ] E →L[ℝ] E` on a real normed space with `‖K u u‖ ≤ D * ‖u‖ ^ 2` for all `u`, where
  `0 ≤ D`, satisfies `‖K‖ ≤ 2 * D`. The polarization identity
  `K (u + v) (u + v) - K (u - v) (u - v) = 4 • K u v` gives `‖K u v‖ ≤ D * (‖u‖ ^ 2 + ‖v‖ ^ 2)`,
  which is then applied to unit vectors.
* `PDE.Analysis.sum_smul_iterate_sub_eq_iterate`: For a linear isometric equivalence
  `e : E ≃ₗᵢ[ℝ] E` of a real seminormed space, the `j`-th iterate is compatible with finite linear
  combinations and differences: `∑ l, c l • e^[j] (y l) - e^[j] z = e^[j] (∑ l, c l • y l - z)`.

There are 47 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace PDE.Analysis

/-- Let `F : Z →L[ℝ] P` be a continuous linear map, `B : P →L[ℝ] P →L[ℝ] P` a symmetric continuous
bilinear map and `t ≠ 0` a real number. If `b = F b0 + B b b + r`,
`w - (2 : ℝ) • B b w - I = t • B w w - t⁻¹ • r + D` and `t • I + t • D = F y`, then
`b + t • w = F (b0 + y) + B (b + t • w) (b + t • w)`. The proof multiplies the equation for `w` by
`t` and expands `B (b + t • w) (b + t • w)` by bilinearity and symmetry. -/
theorem add_smul_eq_apply_add_bilin_self {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : Z →L[ℝ] P) (B : P →L[ℝ] P →L[ℝ] P)
    (hB : ∀ f g, B f g = B g f) (t : ℝ) (ht : t ≠ 0) (b w r I D : P) (b0 y : Z)
    (hb : b = F b0 + B b b + r)
    (hw : w - (2 : ℝ) • B b w - I = t • B w w - t⁻¹ • r + D)
    (hy : t • I + t • D = F y) :
    b + t • w = F (b0 + y) + B (b + t • w) (b + t • w) := by
  have hw' : w = (2 : ℝ) • B b w + I + (t • B w w - t⁻¹ • r + D) := by
    rw [← hw]
    abel
  have hr : t • t⁻¹ • r = r := by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  have e1 : t • w = (2 * t) • B b w + t • I + t • D + (t * t) • B w w - r := by
    calc t • w = t • ((2 : ℝ) • B b w + I + (t • B w w - t⁻¹ • r + D)) := congrArg (t • ·) hw'
      _ = (2 * t) • B b w + t • I + t • D + (t * t) • B w w - r := by
        rw [smul_add, smul_add, smul_add, smul_sub, hr]
        module
  rw [map_add F b0 y, ← hy]
  simp only [map_add, map_smul, add_apply, smul_apply]
  rw [hB w b]
  conv_lhs => rw [hb, e1]
  module

/-- Let `ψ : (ℝ → ℝ) → ℂ` satisfy `ψ (fun r ↦ f r + g r) = ψ f + ψ g` and
`ψ (fun r ↦ a * f r) = a * ψ f` for continuous `f`, `g` and real `a`, and let `c : ℕ → ℕ → ℝ` have
`c j j ≠ 0` for all `j`. If `ψ (fun r ↦ ∑ t ∈ Finset.range (i + 1), c i t * r ^ t) = 0` for all
`i ≤ d`, then `ψ (fun r ↦ r ^ j) = 0` for all `j ≤ d`. Proof idea: strong induction on `j`; the
lower monomials vanish by induction and the leading coefficient `c j j` is nonzero. -/
theorem apply_pow_eq_zero_of_triangular (c : ℕ → ℕ → ℝ) (hc : ∀ j, c j j ≠ 0) (ψ : (ℝ → ℝ) → ℂ)
    (hadd : ∀ f g : ℝ → ℝ, Continuous f → Continuous g → ψ (fun r ↦ f r + g r) = ψ f + ψ g)
    (hsmul : ∀ (a : ℝ) (f : ℝ → ℝ), Continuous f → ψ (fun r ↦ a * f r) = a * ψ f)
    (d : ℕ) (h0 : ∀ i ≤ d, ψ (fun r ↦ ∑ t ∈ Finset.range (i + 1), c i t * r ^ t) = 0) :
    ∀ j ≤ d, ψ (fun r ↦ r ^ j) = 0 := by
  have hzero : ψ (fun _ ↦ 0) = 0 := by
    have := hsmul 0 (fun _ ↦ 0) continuous_const
    simpa using this
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℝ), (∀ t ∈ s, Continuous (f t)) →
      ψ (fun r ↦ ∑ t ∈ s, f t r) = ∑ t ∈ s, ψ (f t) := by
    intro s f
    classical
    refine Finset.induction_on s ?_ ?_
    · intro _; simpa using hzero
    · intro a s ha ih h
      simp only [Finset.sum_insert ha]
      rw [hadd (f a) (fun r ↦ ∑ t ∈ s, f t r) (h a (Finset.mem_insert_self _ _))
        (continuous_finsetSum _ fun t ht ↦ h t (Finset.mem_insert_of_mem ht)),
        ih fun t ht ↦ h t (Finset.mem_insert_of_mem ht)]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have e : (fun r : ℝ ↦ ∑ t ∈ Finset.range (j + 1), c j t * r ^ t) =
        fun r ↦ (∑ t ∈ Finset.range j, c j t * r ^ t) + c j j * r ^ j := by
      funext r; rw [Finset.sum_range_succ]
    have h1 := h0 j hj
    rw [e, hadd (fun r ↦ ∑ t ∈ Finset.range j, c j t * r ^ t) (fun r ↦ c j j * r ^ j)
      (continuous_finsetSum _ fun t _ ↦ continuous_const.mul (continuous_pow t))
      (continuous_const.mul (continuous_pow j)), hsum (Finset.range j) (fun t r ↦ c j t * r ^ t)
      (fun t _ ↦ continuous_const.mul (continuous_pow t))] at h1
    have h2 := hsmul (c j j) (fun r ↦ r ^ j) (continuous_pow j)
    have hz : ∑ t ∈ Finset.range j, ψ (fun r ↦ c j t * r ^ t) = 0 := by
      refine Finset.sum_eq_zero fun t ht ↦ ?_
      have h3 := hsmul (c j t) (fun r ↦ r ^ t) (continuous_pow t)
      rw [h3, ih t (Finset.mem_range.1 ht) (by have := Finset.mem_range.1 ht; omega), mul_zero]
    rw [hz, zero_add, h2] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hc j)

/-- Let `f : E → F` be a map between real normed spaces that is positively homogeneous of degree
`d ≥ 1`: `f (c • x) = c ^ d • f x` for all `c > 0` and all `x`. Then `f 0 = 0`. The proof takes
`c = 2` and `x = 0`, which gives `(2 ^ d - 1) • f 0 = 0`. -/
theorem apply_zero_eq_zero_of_homogeneous_pow {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ} (hd : 1 ≤ d) {f : E → F}
    (hh : ∀ c : ℝ, 0 < c → ∀ x, f (c • x) = c ^ d • f x) : f 0 = 0 := by
  have h := hh 2 (by norm_num) 0
  rw [smul_zero] at h
  have h2 : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have h3 : ((2 : ℝ) ^ d - 1) • f 0 = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h3).resolve_left (by linarith)

/-- For a continuous bilinear map `B : Y →L[ℝ] Y →L[ℝ] Y` on a real normed space,
`B v v - B w w = B (v - w) v + B w (v - w)`. -/
theorem bilin_apply_self_sub_apply_self {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : Y →L[ℝ] Y →L[ℝ] Y) (v w : Y) :
    B v v - B w w = B (v - w) v + B w (v - w) := by
  simp only [map_sub, sub_apply]
  abel

/-- If a continuous linear map `Pu` on a real Banach space is idempotent, `Pu * Pu = Pu`, then
`Pu (Pu x) = Pu x` for every `x`. -/
theorem clm_apply_apply_of_mul_self_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Pu : E →L[ℝ] E} (hP : Pu * Pu = Pu) (x : E) : Pu (Pu x) = Pu x := by
  have h := congrArg (fun T : E →L[ℝ] E ↦ T x) hP
  simpa [mul_apply_eq_comp] using h

/-- If two continuous linear maps `Pu` and `M` on a real Banach space commute, `Pu * M = M * Pu`,
then `Pu (M x) = M (Pu x)` for every `x`. -/
theorem clm_apply_comm_of_mul_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Pu M : E →L[ℝ] E} (hC : Pu * M = M * Pu) (x : E) : Pu (M x) = M (Pu x) := by
  have h := congrArg (fun T : E →L[ℝ] E ↦ T x) hC
  simpa [mul_apply_eq_comp] using h

/-- A continuous linear map `T : E →L[ℝ] F` between real modules with a topology commutes with
finite linear combinations: `T (∑ i, κ i • c i) = ∑ i, κ i • T (c i)` for `κ : Fin k → ℝ` and
`c : Fin k → E`. -/
theorem continuousLinearMap_map_sum_smul {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [AddCommGroup F]
    [Module ℝ F] [TopologicalSpace F] {k : ℕ} (T : E →L[ℝ] F) (κ : Fin k → ℝ) (c : Fin k → E) :
    T (∑ i, κ i • c i) = ∑ i, κ i • T (c i) := by
  simp only [map_sum, map_smul]

/-- For a continuous linear map `L : E →L[ℝ] F` between real normed spaces, the function
`x ↦ ‖L x‖ ^ 2` is convex on the whole space `E`. -/
theorem convexOn_norm_sq_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ConvexOn ℝ Set.univ (fun x ↦ ‖L x‖ ^ 2) := by
  have h1 : ConvexOn ℝ Set.univ (fun x ↦ ‖L x‖) :=
    (convexOn_norm convex_univ).comp_linearMap L.toLinearMap
  exact h1.pow (fun x _ ↦ norm_nonneg _) 2

/-- Let `Pu` and `M` be continuous linear maps on a real Banach space with
`‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖` for all `n : ℕ` and `x`. If `Pu w = w`, `Pu w' = w'` and
`M w = M w'`, then `w = w'`, so `M` is injective on the fixed points of `Pu`. -/
theorem eq_of_apply_eq_of_norm_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Pu M : E →L[ℝ] E} {K r₂ : ℝ}
    (hg : ∀ (n : ℕ) (x : E), ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖)
    {w w' : E} (hw : Pu w = w) (hw' : Pu w' = w') (h : M w = M w') : w = w' := by
  have h1 := hg 1 (w - w')
  simp only [map_sub, hw, hw', pow_one, h, sub_self, norm_zero, mul_zero] at h1
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)

/-- Discrete variation of constants formula: if `B` is a continuous linear map on a real Banach
space and the sequences `w`, `d` satisfy `w (n + 1) = B (w n) + d n` for all `n`, then
`w n = (B ^ n) (w 0) + ∑ m ∈ Finset.range n, (B ^ (n - 1 - m)) (d m)` for all `n`. The proof is by
induction on `n`. -/
theorem eq_pow_apply_add_sum_of_recurrence {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (B : E →L[ℝ] E) (w d : ℕ → E) (h : ∀ n, w (n + 1) = B (w n) + d n) (n : ℕ) :
    w n = (B ^ n) (w 0) + ∑ m ∈ Finset.range n, (B ^ (n - 1 - m)) (d m) := by
  have e1 : ∀ (k : ℕ) (v : E), B ((B ^ k) v) = (B ^ (k + 1)) v := fun k v ↦ by
    rw [pow_succ', mul_apply_eq_comp]
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∑ m ∈ Finset.range n, B ((B ^ (n - 1 - m)) (d m)) =
        ∑ m ∈ Finset.range n, (B ^ (n + 1 - 1 - m)) (d m) :=
      Finset.sum_congr rfl fun m hm ↦ by
        rw [e1, show n - 1 - m + 1 = n + 1 - 1 - m by have := Finset.mem_range.mp hm; omega]
    rw [h n, ih, map_add, map_sum, hsum, e1, Finset.sum_range_succ,
      show n + 1 - 1 - n = 0 by omega, pow_zero, one_apply_eq_self, add_assoc]

/-- A convergent sequence of continuous linear maps is uniformly bounded: if `T n → T₀` in
`E →L[ℝ] F`, with `E` and `F` real normed spaces, then there is `C` with `0 ≤ C` and
`‖T n x‖ ≤ C * ‖x‖` for all `n` and `x`. -/
theorem exists_norm_clm_apply_le_of_tendsto {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : ℕ → E →L[ℝ] F) (T₀ : E →L[ℝ] F)
    (hT : Tendsto T atTop (𝓝 T₀)) : ∃ C, 0 ≤ C ∧ ∀ n x, ‖T n x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC⟩ := hT.norm.bddAbove_range
  exact ⟨max C 0, le_max_right _ _, fun n x ↦
    (T n).le_of_opNorm_le ((hC ⟨n, rfl⟩).trans (le_max_left _ _)) x⟩

/-- Let `E` be a finite-dimensional real normed space and `δ > 0`. There is `η > 0` such that every
continuous linear map `D` from `E` to a real normed space with `‖D (Module.finBasis ℝ E i)‖ ≤ η` for
all `i` has `‖D‖ ≤ δ`. One can take `η = δ / (K + 1)`, where `K` is the sum of the operator norms of
the coordinate functionals of the basis. -/
theorem exists_opNorm_le_of_norm_finBasis_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (δ : ℝ) (hδ : 0 < δ) : ∃ η : ℝ, 0 < η ∧ ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (D : E →L[ℝ] Y), (∀ i, ‖D (Module.finBasis ℝ E i)‖ ≤ η) → ‖D‖ ≤ δ := by
  set bs := Module.finBasis ℝ E
  set Kc := ∑ i, ‖LinearMap.toContinuousLinearMap (bs.coord i)‖
  have hKc0 : 0 ≤ Kc := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  refine ⟨δ / (Kc + 1), div_pos hδ (by linarith), fun Y _ _ D hD ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hδ.le fun e ↦ ?_
  have he : D e = ∑ i, bs.repr e i • D (bs i) := by
    conv_lhs => rw [← bs.sum_repr e]
    rw [map_sum]
    simp only [map_smul]
  have hc : ∀ i, ‖bs.repr e i‖ ≤ ‖LinearMap.toContinuousLinearMap (bs.coord i)‖ * ‖e‖ := fun i ↦ by
    have := (LinearMap.toContinuousLinearMap (bs.coord i)).le_opNorm e
    simpa [Module.Basis.coord_apply] using this
  have hK : Kc * (δ / (Kc + 1)) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  rw [he]
  calc ‖∑ i, bs.repr e i • D (bs i)‖ ≤ ∑ i, ‖bs.repr e i‖ * (δ / (Kc + 1)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hD i) (norm_nonneg _)
    _ ≤ ∑ i, ‖LinearMap.toContinuousLinearMap (bs.coord i)‖ * ‖e‖ * (δ / (Kc + 1)) :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hc i) (by positivity)
    _ = ‖e‖ * (Kc * (δ / (Kc + 1))) := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
    _ ≤ ‖e‖ * δ := mul_le_mul_of_nonneg_left hK (norm_nonneg e)
    _ = δ * ‖e‖ := mul_comm _ _

/-- Let `E` be a finite-dimensional real normed space, `Y` a real normed space and `g : ℝ → E → Y`,
and suppose that for each `e` there are `T₀ > 0` and `B` with `‖g T e‖ ≤ B` for `0 < T < T₀`. Then
there are `T₁ > 0` and `CJ ≥ 0` such that, for `0 < T < T₁`, every continuous linear map
`Jt : E →L[ℝ] Y` with `Jt e = g T e` for all `e` has `‖Jt‖ ≤ CJ`. The proof bounds the operator norm
by the norms of the values on a basis and takes for `T₁` the minimum of `1` and the thresholds `T₀`
of the basis vectors. -/
theorem exists_opNorm_le_of_pointwise_bound {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : ℝ → E → Y)
    (h : ∀ e, ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ B : ℝ, ∀ T, 0 < T → T < T₀ → ‖g T e‖ ≤ B) :
    ∃ T₁ : ℝ, 0 < T₁ ∧
      ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ T, 0 < T → T < T₁ → ∀ Jt : E →L[ℝ] Y, (∀ e, Jt e = g T e) → ‖Jt‖ ≤
      CJ := by
  classical
  let v := Module.finBasis ℝ E
  obtain ⟨C, hC, hv⟩ := v.exists_opNorm_le (F := Y)
  choose T₀ hT₀ B hB using fun i ↦ h (v i)
  let s : Finset ℝ := insert 1 (Finset.univ.image T₀)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs, ?_, C * ∑ i, |B i|, by positivity, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact hT₀ i
  · intro T hT hT1 Jt hJ
    refine hv (by positivity) fun i ↦ ?_
    rw [hJ]
    have hi : s.min' hs ≤ T₀ i := Finset.min'_le _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    calc ‖g T (v i)‖ ≤ B i := hB i T hT (lt_of_lt_of_le hT1 hi)
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ j, |B j| := Finset.single_le_sum (f := fun j ↦ |B j|) (fun j _ ↦ abs_nonneg _)
          (Finset.mem_univ i)

/-- Let `Pu` be a continuous linear map on a real normed space `X` whose range is
finite-dimensional, and let `C'` be a dense submodule of `X`. Then every `v` in the range of `Pu` is
`Pu c` for some `c ∈ C'`. The image of `C'` under `Pu` is a finite-dimensional subspace, hence
closed, and by continuity of `Pu` and density of `C'` its closure contains the range of `Pu`. -/
theorem exists_preimage_of_dense {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Pu : X →L[ℝ] X) (C' : Submodule ℝ X)
    (hfin : FiniteDimensional ℝ (LinearMap.range (Pu : X →ₗ[ℝ] X))) (hd : Dense (C' : Set X))
    (v : X) (hv : v ∈ LinearMap.range (Pu : X →ₗ[ℝ] X)) : ∃ c ∈ C', Pu c = v := by
  have hle : Submodule.map (Pu : X →ₗ[ℝ] X) C' ≤ LinearMap.range (Pu : X →ₗ[ℝ] X) :=
    LinearMap.map_le_range
  have : FiniteDimensional ℝ (Submodule.map (Pu : X →ₗ[ℝ] X) C') :=
    Submodule.finiteDimensional_of_le hle
  have hcl : IsClosed ((Submodule.map (Pu : X →ₗ[ℝ] X) C' : Submodule ℝ X) : Set X) :=
    Submodule.isClosed_of_finiteDimensional _
  obtain ⟨x, rfl⟩ := hv
  have himg : (Pu : X → X) '' (C' : Set X) ⊆
      ((Submodule.map (Pu : X →ₗ[ℝ] X) C' : Submodule ℝ X) : Set X) := by
    rintro _ ⟨c, hc, rfl⟩
    exact Submodule.mem_map_of_mem hc
  have hx : Pu x ∈ ((Submodule.map (Pu : X →ₗ[ℝ] X) C' : Submodule ℝ X) : Set X) :=
    hcl.closure_subset_iff.mpr himg (Pu.continuous.range_subset_closure_image_dense hd ⟨x, rfl⟩)
  obtain ⟨c, hc, hcx⟩ := Submodule.mem_map.mp hx
  exact ⟨c, hc, hcx⟩

/-- Let `g : W →L[ℝ] Y` be injective, `s : W →L[ℝ] V` and `A : V →L[ℝ] Y`, with `V` a real inner
product space, `W` a real Banach space, `Y` a real normed space, and `‖w‖ ≤ ‖g w‖ + ‖s w‖` for all
`w`. If for every `f` in a dense subspace `D` of `V` there is `w` with `g w = A f` and
`‖s w‖ ^ 2 + (1 / 4) * ‖g w‖ ^ 2 ≤ inner ℝ f (s w)`, then there is `T : V →L[ℝ] W` with
`g (T f) = A f` and `‖s (T f)‖ ^ 2 + (1 / 4) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2` for all `f : V`. Proof idea:
on `D` the solution `w` is unique, hence linear in `f`, and `‖w‖ ≤ 3 * ‖f‖`; extend this map by
density and pass both properties to the closure of `D`. -/
theorem exists_solution_map_of_dense_le_inner {V W Y : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : W →L[ℝ] Y) (s : W →L[ℝ] V) (A : V →L[ℝ] Y) (hg : Function.Injective g)
    (hn : ∀ w, ‖w‖ ≤ ‖g w‖ + ‖s w‖) (D : Submodule ℝ V) (hD : Dense (D : Set V))
    (hDu : ∀ f ∈ D, ∃ w : W, g w = A f ∧
      ‖s w‖ ^ 2 + (1 / 4 : ℝ) * ‖g w‖ ^ 2 ≤ inner ℝ f (s w)) :
    ∃ T : V →L[ℝ] W, (∀ f, g (T f) = A f) ∧ ∀ f : V,
      ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  choose U hU hUb using hDu
  have hbd : ∀ f (hf : f ∈ D), ‖s (U f hf)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (U f hf)‖ ^ 2
      ≤ ‖f‖ ^ 2 ∧ ‖s (U f hf)‖ ≤ ‖f‖ ∧ ‖g (U f hf)‖ ≤ 2 * ‖f‖ := fun f hf ↦
    sq_add_le_sq_of_le_mul (norm_nonneg _) _ (real_inner_le_norm _ _) (hUb f hf)
  have hUeq : ∀ (f : D) (w : W), g w = A f → U f f.2 = w := fun f w hw ↦
    hg ((hU f f.2).trans hw.symm)
  let Φ : D →ₗ[ℝ] W :=
    { toFun := fun f ↦ U f f.2
      map_add' := fun f f' ↦ hUeq (f + f') (U f f.2 + U f' f'.2) (by
        rw [map_add, hU, hU, Submodule.coe_add, map_add])
      map_smul' := fun c f ↦ hUeq (c • f) (c • U f f.2) (by
        rw [map_smul, hU, Submodule.coe_smul, map_smul]) }
  have hΦ : ∀ f : D, ‖Φ f‖ ≤ 3 * ‖f‖ := fun f ↦ by
    have h := hbd f f.2
    have := hn (U f f.2)
    change ‖U f f.2‖ ≤ 3 * ‖(f : V)‖
    linarith [h.2.1, h.2.2]
  let Φc : D →L[ℝ] W := Φ.mkContinuous 3 hΦ
  have hdense : DenseRange D.subtypeL := hD.denseRange_val
  have hind : IsUniformInducing D.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  let T : V →L[ℝ] W := Φc.extend D.subtypeL
  have hT : ∀ f : D, T f = U f f.2 := fun f ↦
    ContinuousLinearMap.extend_eq Φc hdense hind f
  have hspec : ∀ f, g (T f) = A f := by
    have heq : (fun f ↦ g (T f)) = fun f ↦ A f := by
      refine hdense.equalizer (g.continuous.comp T.continuous) A.continuous ?_
      funext f
      change g (T f) = A f
      rw [hT]
      exact hU f f.2
    exact fun f ↦ congrFun heq f
  refine ⟨T, hspec, ?_⟩
  have hcl : IsClosed {f : V | ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2} := by
    apply isClosed_le
    · fun_prop
    · fun_prop
  have hsub : (D : Set V) ⊆ {f : V | ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2} :=
    fun f hf ↦ by
      change ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2
      have e : T f = U f hf := hT ⟨f, hf⟩
      rw [e]
      exact (hbd f hf).1
  intro f
  exact (hcl.closure_subset_iff.2 hsub) (hD.closure_eq ▸ Set.mem_univ f)

/-- Let `s` be a dense submodule of a real normed space `E` and `T : s →L[ℝ] F` a continuous linear
map into a real Banach space `F`. The extension of `T` along the inclusion of `s` agrees with `T` on
`s`: `T.extend s.subtypeL x = T ⟨x, hx⟩` for `hx : x ∈ s`. -/
theorem extend_subtypeL_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (s : Submodule ℝ E)
    (hs : Dense (s : Set E)) (T : s →L[ℝ] F) (x : E) (hx : x ∈ s) :
    T.extend s.subtypeL x = T ⟨x, hx⟩ :=
  ContinuousLinearMap.extend_eq T hs.denseRange_val (isUniformInducing_val (s : Set E)) ⟨x, hx⟩

/-- The multiplication map `ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ` is symmetric: it is
equal to its flip. -/
theorem flip_lsmul_real :
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext; simp

/-- Sequential criterion for a compact operator: let `T : E →L[ℝ] F` be a continuous linear map of
real normed spaces with `F` complete. If every sequence `f` with `‖f n‖ ≤ 1` has a strictly
increasing `φ : ℕ → ℕ` such that `n ↦ T (f (φ n))` satisfies the Cauchy condition, then `T` is a
compact operator. The proof shows that the closure of the image of the closed unit ball is
sequentially compact, approximating its points by images `T e` with `‖e‖ ≤ 1`. -/
theorem isCompactOperator_of_cauchy_subseq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : ∀ f : ℕ → E, (∀ n, ‖f n‖ ≤ 1) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖T (f (φ m)) - T (f (φ n))‖ < ε) :
    IsCompactOperator T := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[ℝ] F)
    one_pos).2 ?_
  rw [isCompact_iff_isSeqCompact]
  intro x hx
  have hb : ∀ n, ∃ e ∈ Metric.closedBall (0 : E) 1, dist (x n) (T e) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.1 (hx n) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨e, he, rfl⟩ := hz
    exact ⟨e, he, hd⟩
  choose f hf hfd using hb
  have hf1 : ∀ n, ‖f n‖ ≤ 1 := fun n ↦ by simpa using hf n
  obtain ⟨φ, hφ, hc⟩ := hT f hf1
  have hc' : CauchySeq (fun n ↦ T (f (φ n))) :=
    Metric.cauchySeq_iff.2 fun ε hε ↦ by simpa only [dist_eq_norm] using hc ε hε
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc'
  refine ⟨a, ?_, φ, hφ, ?_⟩
  · exact mem_closure_of_tendsto ha (Eventually.of_forall fun n ↦ ⟨f (φ n), hf (φ n), rfl⟩)
  · have hd : Tendsto (fun n ↦ dist (x (φ n)) (T (f (φ n)))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ ↦ 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hfd (φ n)).le) h0
    exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ dist_triangle _ _ _) (by simpa using hd.add (tendsto_iff_dist_tendsto_zero.1 ha)))

/-- A continuous linear map `T : E →L[ℝ] F` between real normed spaces is a compact operator if, for
every sequence `x` with `‖x n‖ < 1` for all `n`, the sequence `T (x n)` has a convergent
subsequence. Proof idea: the closure of the image of the open unit ball is sequentially compact,
because each of its points is within `1 / (n + 1)` of some `T x` with `‖x‖ < 1`. -/
theorem isCompactOperator_of_exists_subseq_tendsto {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F)
    (h : ∀ x : ℕ → E, (∀ n, ‖x n‖ < 1) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : F, Filter.Tendsto (fun n ↦ T (x (φ n))) Filter.atTop
          (nhds L)) :
    IsCompactOperator T := by
  refine (isCompactOperator_iff_isCompact_closure_image_ball (T : E →ₗ[ℝ] F) zero_lt_one).mpr ?_
  refine IsSeqCompact.isCompact fun u hu ↦ ?_
  have hs : ∀ n, ∃ x : E, ‖x‖ < 1 ∧ dist (u n) (T x) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp (hu n) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨x, hx, rfl⟩ := hb
    exact ⟨x, by simpa using hx, hd⟩
  choose x hx hxd using hs
  obtain ⟨φ, hφ, L, hL⟩ := h x hx
  refine ⟨L, ?_, φ, hφ, ?_⟩
  · refine mem_closure_of_tendsto hL (Filter.Eventually.of_forall fun n ↦ ?_)
    exact ⟨x (φ n), by simpa using hx (φ n), rfl⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    have hε : Filter.Tendsto (fun n ↦ 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hL' := tendsto_iff_dist_tendsto_zero.mp hL
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) (by simpa using hε.add hL')
    exact (dist_triangle _ (T (x (φ n))) L).trans (add_le_add (by
      simpa using (hxd (φ n)).le) le_rfl)

/-- Fredholm alternative: on a real Banach space `F`, if `K : F →L[ℝ] F` is a compact operator and
`1 + K` is injective, then `1 + K` is a unit in the ring of continuous linear maps. The proof
applies the alternative for the compact operator `-K` at `μ = 1`: either `1` is an eigenvalue of
`-K`, which contradicts injectivity, or `1` is in its resolvent set. -/
theorem isUnit_one_add_of_compact_of_injective {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (K : F →L[ℝ] F) (hK : IsCompactOperator K)
    (hinj : Function.Injective ((1 : F →L[ℝ] F) + K)) :
    IsUnit ((1 : F →L[ℝ] F) + K) := by
  have hneg : IsCompactOperator (-K) := hK.neg
  rcases hneg.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℝ)) one_ne_zero with h | h
  · exfalso
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    have h1 : -K x = x := by
      have := hx.apply_eq_smul
      simpa using this
    have h1' : K x = -x := by rw [← neg_neg (K x), h1]
    have h2 : ((1 : F →L[ℝ] F) + K) x = ((1 : F →L[ℝ] F) + K) 0 := by
      simp [h1']
    exact hx.2 (hinj h2)
  · rw [spectrum.mem_resolventSet_iff] at h
    convert h using 1
    rw [Algebra.algebraMap_eq_smul_one, one_smul, sub_neg_eq_add]

/-- If the continuous linear maps `A n : Y →L[ℝ] W` between real normed spaces satisfy `‖A n‖ ≤ C`
for all `n : ℕ`, then for every bounded sequence `g : lp (fun _ : ℕ ↦ Y) ∞` and every `n`,
`‖A n (g n)‖ ≤ C * ‖g‖`. -/
theorem norm_apply_lp_apply_le_mul_norm {Y W : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (A : ℕ → Y →L[ℝ] W) {C : ℝ}
    (hA : ∀ n, ‖A n‖ ≤ C) (g : lp (fun _ : ℕ ↦ Y) ∞) (n : ℕ) : ‖A n (g n)‖ ≤ C * ‖g‖ :=
  ((A n).le_opNorm _).trans (mul_le_mul (hA n) (lp.norm_apply_le_norm ENNReal.top_ne_zero g n)
    (norm_nonneg _) ((norm_nonneg _).trans (hA n)))

/-- For a continuous bilinear map `B : X →L[ℝ] X →L[ℝ] X` on a real inner product space,
`‖B x x - B y y‖ ≤ ‖B‖ * ‖x - y‖ * ‖x‖ + ‖B‖ * ‖y‖ * ‖x - y‖`. -/
theorem norm_bilin_self_sub_self_le_add {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (B : X →L[ℝ] X →L[ℝ] X) (x y : X) :
    ‖B x x - B y y‖ ≤ ‖B‖ * ‖x - y‖ * ‖x‖ + ‖B‖ * ‖y‖ * ‖x - y‖ := by
  have e : B x x - B y y = B (x - y) x + B y (x - y) := by
    simp only [map_sub, sub_apply]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _))

/-- For real normed spaces `E`, `Y`, `Z` and a continuous linear map `D : Y →L[ℝ] Z`, the
composition with the second projection of `E × Y` satisfies
`‖D.comp (ContinuousLinearMap.snd ℝ E Y)‖ ≤ ‖D‖`. -/
theorem norm_comp_snd_le {E Y Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (D : Y →L[ℝ] Z) : ‖D.comp (ContinuousLinearMap.snd ℝ E Y)‖ ≤ ‖D‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have b := ContinuousLinearMap.norm_snd_le ℝ E Y
  calc ‖D‖ * ‖ContinuousLinearMap.snd ℝ E Y‖ ≤ ‖D‖ * 1 :=
           mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = ‖D‖ := mul_one _

/-- For continuous linear maps `x x' : F →L[ℝ] G` and `y y' : E →L[ℝ] F` between real normed spaces,
`‖x.comp y - x'.comp y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖`. -/
theorem norm_comp_sub_comp_le {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (x x' : F →L[ℝ] G) (y y' : E →L[ℝ] F) :
    ‖x.comp y - x'.comp y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖ := by
  have e : x.comp y - x'.comp y' = x.comp (y - y') + (x - x').comp y' := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

/-- Let `Pu` and `M` be continuous linear maps on a real Banach space with
`‖M ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n` for all `n : ℕ`, and let `0 < Θ`. Then
`‖((Θ⁻¹ • M) ^ k) (v - Pu v)‖ ≤ K * (r₁ / Θ) ^ k * ‖v‖` for all `k : ℕ` and `v`. The proof uses
`(Θ⁻¹ • M) ^ k = Θ⁻¹ ^ k • M ^ k` and `(M ^ k) (v - Pu v) = (M ^ k * (1 - Pu)) v`. -/
theorem norm_inv_smul_pow_apply_sub_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Pu M : E →L[ℝ] E} {K r₁ Θ : ℝ} (hΘ : 0 < Θ)
    (hdec : ∀ n : ℕ, ‖M ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n) (k : ℕ) (v : E) :
    ‖((Θ⁻¹ • M) ^ k) (v - Pu v)‖ ≤ K * (r₁ / Θ) ^ k * ‖v‖ := by
  have e : (M ^ k) (v - Pu v) = (M ^ k * (1 - Pu)) v := by
    rw [mul_apply_eq_comp, sub_apply, one_apply_eq_self]
  rw [smul_pow, smul_apply, norm_smul, e,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hΘ.le) _)]
  calc Θ⁻¹ ^ k * ‖(M ^ k * (1 - Pu)) v‖ ≤ Θ⁻¹ ^ k * (K * r₁ ^ k * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((M ^ k * (1 - Pu)).le_of_opNorm_le (hdec k) v)
          (pow_nonneg (inv_nonneg.mpr hΘ.le) _)
    _ = K * (r₁ / Θ) ^ k * ‖v‖ := by rw [div_eq_mul_inv, mul_pow]; ring

/-- For a continuous linear map `T` on a real Banach space with `‖T‖ ≤ q` and `q < 1`,
`‖Ring.inverse (1 - T)‖ ≤ (1 - q)⁻¹`. The inverse is the sum of the geometric series of `T`. -/
theorem norm_inverse_one_sub_le {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (T : F →L[ℝ] F) (q : ℝ) (hT : ‖T‖ ≤ q) (hq : q < 1) :
    ‖Ring.inverse (1 - T)‖ ≤ (1 - q)⁻¹ := by
  have hT1 : ‖T‖ < 1 := hT.trans_lt hq
  rw [← geom_series_eq_inverse T hT1]
  refine (tsum_geometric_le_of_norm_lt_one T hT1).trans ?_
  have h1 : ‖(1 : F →L[ℝ] F)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h2 : (1 - ‖T‖)⁻¹ ≤ (1 - q)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  linarith

/-- For a continuous linear map `A₀ : E →L[ℝ] X` between real normed spaces, a vector `e` and
`n : ℕ`, `‖if n = 0 then A₀ e else 0‖ ≤ ‖A₀ e‖`. -/
theorem norm_ite_apply_zero_le {E : Type} {X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (A₀ : E →L[ℝ] X) (e : E) (n : ℕ) :
    ‖(if n = 0 then A₀ e else 0)‖ ≤ ‖A₀ e‖ := by
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

/-- Iterates of a linear isometric equivalence `e : E ≃ₗᵢ[ℝ] E` of a real seminormed space preserve
the norm: `‖e^[j] y‖ = ‖y‖` for every `j : ℕ`. -/
theorem norm_iterate_linearIsometryEquiv {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] E)
    (j : ℕ) (y : E) : ‖(⇑e)^[j] y‖ = ‖y‖ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', LinearIsometryEquiv.norm_map, ih]

/-- For `u : ℂ` and `v : Fin 3 → ℂ`, scalar multiplication as a continuous bilinear map satisfies
`‖ContinuousLinearMap.lsmul ℝ ℂ u v‖ ≤ ‖u‖ * ‖v‖`. -/
theorem norm_lsmul_apply_le (u : ℂ) (v : Fin 3 → ℂ) :
    ‖ContinuousLinearMap.lsmul ℝ ℂ u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [ContinuousLinearMap.lsmul_apply, norm_smul]

/-- For complex numbers `x`, `x'` and continuous linear maps `y y' : E →L[ℝ] ℂ` on a real normed
space, `‖x • y - x' • y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖`. -/
theorem norm_smul_sub_smul_le_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x x' : ℂ)
    (y y' : E →L[ℝ] ℂ) :
    ‖x • y - x' • y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖ := by
  have e : x • y - x' • y' = x • (y - y') + (x - x') • y' := by
    ext v
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ContinuousLinearMap.opNorm_smul_le _ _
  · exact ContinuousLinearMap.opNorm_smul_le _ _

/-- Let `g : W →L[ℝ] Y` be injective and let `S T : V →L[ℝ] W` satisfy `g (S f) = A f` and
`g (T f) = A f` for all `f`, where `A : V →L[ℝ] Y` and `s : W →L[ℝ] V` are continuous linear maps
between real normed spaces. If `‖s (T f)‖ ^ 2 + (1 / 4) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2` for all `f`, then
`‖s (S f)‖ ^ 2 + (1 / 4) * ‖g (S f)‖ ^ 2 ≤ ‖f‖ ^ 2` for all `f`, because `S f = T f`. -/
theorem norm_sq_add_le_of_injective {V W Y : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedSpace ℝ V]
    (g : W →L[ℝ] Y) (s : W →L[ℝ] V) (A : V →L[ℝ] Y) (hg : Function.Injective g)
    (S T : V →L[ℝ] W) (hS : ∀ f, g (S f) = A f) (hT : ∀ f, g (T f) = A f)
    (hb : ∀ f : V, ‖s (T f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (T f)‖ ^ 2 ≤ ‖f‖ ^ 2) (f : V) :
    ‖s (S f)‖ ^ 2 + (1 / 4 : ℝ) * ‖g (S f)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have e : S f = T f := hg ((hS f).trans (hT f).symm)
  rw [e]
  exact hb f

/-- A symmetric continuous bilinear map `K : E →L[ℝ] E →L[ℝ] E` on a real normed space with
`‖K u u‖ ≤ D * ‖u‖ ^ 2` for all `u`, where `0 ≤ D`, satisfies `‖K‖ ≤ 2 * D`. The polarization
identity `K (u + v) (u + v) - K (u - v) (u - v) = 4 • K u v` gives
`‖K u v‖ ≤ D * (‖u‖ ^ 2 + ‖v‖ ^ 2)`, which is then applied to unit vectors. -/
theorem opNorm_le_of_symm_of_diag_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : E →L[ℝ] E →L[ℝ] E} (hsymm : ∀ u v, K u v = K v u) {D : ℝ}
    (hD : 0 ≤ D) (h : ∀ u, ‖K u u‖ ≤ D * ‖u‖ ^ 2) : ‖K‖ ≤ 2 * D := by
  have hpol : ∀ u v, ‖K u v‖ ≤ D * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    intro u v
    have e : K (u + v) (u + v) - K (u - v) (u - v) = (4 : ℝ) • K u v := by
      simp only [map_add, map_sub, add_apply, sub_apply]
      rw [hsymm v u]
      module
    have h4 : ‖(4 : ℝ) • K u v‖ ≤ ‖K (u + v) (u + v)‖ + ‖K (u - v) (u - v)‖ := by
      rw [← e]
      exact norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at h4
    have h1 := h (u + v)
    have h2 := h (u - v)
    have n1 : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
      nlinarith only [norm_add_le u v, norm_nonneg (u + v), norm_nonneg u, norm_nonneg v,
        sq_nonneg (‖u‖ - ‖v‖)]
    have n2 : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
      nlinarith only [norm_sub_le u v, norm_nonneg (u - v), norm_nonneg u, norm_nonneg v,
        sq_nonneg (‖u‖ - ‖v‖)]
    linarith only [h4, h1, h2, mul_le_mul_of_nonneg_left n1 hD, mul_le_mul_of_nonneg_left n2 hD]
  refine ContinuousLinearMap.opNorm_le_bound₂ K (by positivity) (fun u v ↦ ?_)
  by_cases hu : u = 0
  · rw [hu, map_zero, zero_apply, norm_zero]
    simp only [mul_zero, zero_mul, le_refl]
  by_cases hv : v = 0
  · rw [hv, map_zero, norm_zero]
    simp only [mul_zero, le_refl]
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have e : K u v = (‖u‖ * ‖v‖) • K (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) := by
    simp only [map_smul, smul_apply, smul_smul]
    convert (one_smul ℝ (K u v)).symm using 2
    field_simp
  have nu : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu'.ne']
  have nv : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv'.ne']
  have hb := hpol (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)
  rw [nu, nv] at hb
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc ‖u‖ * ‖v‖ * ‖K (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)‖ ≤ ‖u‖ * ‖v‖ * (D * (1 ^ 2 + 1 ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * D * ‖u‖ * ‖v‖ := by ring

/-- Let `E` and `X` be real Banach spaces, `A : ℕ → E →L[ℝ] X` a sequence of continuous linear maps,
and `T` a continuous linear map from `lp (fun _ : ℕ ↦ E) ∞` to `lp (fun _ : ℕ ↦ X) ∞` with
`T g n = A n (g n)` for all `g` and `n`. Then `‖A n‖ ≤ ‖T‖` for every `n`. The proof applies `T` to
the sequence `lp.single ∞ n y`, whose norm is at most `‖y‖`. -/
theorem opNorm_le_opNorm_of_lp_apply_eq {E : Type} {X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : ℕ → E →L[ℝ] X)
    (T : lp (fun _ : ℕ ↦ E) ∞ →L[ℝ] lp (fun _ : ℕ ↦ X) ∞) (hT : ∀ g n, T g n = A n (g n))
    (n : ℕ) : ‖A n‖ ≤ ‖T‖ := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_
  have h1 : ‖T (lp.single (E := fun _ : ℕ ↦ E) ∞ n y) n‖ ≤
      ‖T (lp.single (E := fun _ : ℕ ↦ E) ∞ n y)‖ :=
    lp.norm_apply_le_norm ENNReal.top_ne_zero _ n
  have h2 : ‖lp.single (E := fun _ : ℕ ↦ E) ∞ n y‖ ≤ ‖y‖ := by
    refine lp.norm_le_of_forall_le (norm_nonneg y) fun i ↦ ?_
    rw [lp.single_apply]
    by_cases h : i = n
    · subst h
      simp
    · simp [h]
  rw [hT, lp.single_apply, Pi.single_eq_same] at h1
  calc ‖A n y‖ ≤ ‖T (lp.single (E := fun _ : ℕ ↦ E) ∞ n y)‖ := h1
    _ ≤ ‖T‖ * ‖lp.single (E := fun _ : ℕ ↦ E) ∞ n y‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ‖y‖ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

/-- A continuous linear map `L : ℝ × ℝ →L[ℝ] ℂ` has operator norm `‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖`.
The proof writes `L v = v.1 • L (1, 0) + v.2 • L (0, 1)` and uses `‖v.1‖ ≤ ‖v‖` and `‖v.2‖ ≤ ‖v‖`.
-/
theorem opNorm_real_prod_le_norm_apply_add (L : ℝ × ℝ →L[ℝ] ℂ) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine L.opNorm_le_bound (by positivity) fun v ↦ ?_
  have hv : L v = v.1 • L (1, 0) + v.2 • L (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have h3 := norm_nonneg (L (1, 0))
  have h4 := norm_nonneg (L (0, 1))
  calc ‖L v‖ ≤ ‖v.1‖ * ‖L (1, 0)‖ + ‖v.2‖ * ‖L (0, 1)‖ := by
        rw [hv, ← norm_smul, ← norm_smul]; exact norm_add_le _ _
    _ ≤ (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖v‖ := by nlinarith

/-- Let `M : ℕ → X →L[ℝ] X` be a sequence of continuous linear maps on a real normed space and
`σ : X ≃ₗᵢ[ℝ] X` a linear isometric equivalence with `σ (M (n + k) x) = M n (σ x)` for all `n` and
`x`. Then `(σ ^ j) (M (k * j + n) x) = M n ((σ ^ j) x)` for all `j`, `n` and `x`. -/
theorem pow_apply_apply_mul_add_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : ℕ → X →L[ℝ] X) (σ : X ≃ₗᵢ[ℝ] X) (k : ℕ)
    (h : ∀ n x, σ (M (n + k) x) = M n (σ x)) (j n : ℕ) (x : X) :
    (σ ^ j) (M (k * j + n) x) = M n ((σ ^ j) x) := by
  induction j generalizing n x with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [show k * (j + 1) + n = (k * j + n) + k by ring, h, ih]

/-- Let `dil, heat : ℝ → E →L[ℝ] E` be families of continuous linear maps on a real normed space
with `(dil μ).comp (heat (μ * t)) = (heat t).comp (dil μ)` for `0 < μ` and `0 ≤ t`,
`heat (s + t) = (heat s).comp (heat t)` for `0 ≤ s` and `0 ≤ t`, and
`dil (μ * ν) = (dil μ).comp (dil ν)` for `0 < μ` and `0 < ν`. Then
`S τ = (dil (Real.exp (-τ))).comp (heat (1 - Real.exp (-τ)))` satisfies
`S (s + τ) = (S s).comp (S τ)` for `0 ≤ s` and `0 ≤ τ`. Proof idea: move `heat (1 - exp (-s))`
across `dil (exp (-τ))` and use `exp (-τ) * (1 - exp (-s)) + (1 - exp (-τ)) = 1 - exp (-(s + τ))`.
-/
theorem rescaled_semigroup_add_of_intertwining {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dil heat : ℝ → E →L[ℝ] E)
    (hDG : ∀ μ t, 0 < μ → 0 ≤ t → (dil μ).comp (heat (μ * t)) = (heat t).comp (dil μ))
    (hH : ∀ s t, 0 ≤ s → 0 ≤ t → heat (s + t) = (heat s).comp (heat t))
    (hD : ∀ μ ν, 0 < μ → 0 < ν → dil (μ * ν) = (dil μ).comp (dil ν))
    (s τ : ℝ) (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    (dil (Real.exp (-(s + τ)))).comp (heat (1 - Real.exp (-(s + τ)))) =
      ((dil (Real.exp (-s))).comp (heat (1 - Real.exp (-s)))).comp
        ((dil (Real.exp (-τ))).comp (heat (1 - Real.exp (-τ)))) := by
  have ha : 0 ≤ 1 - Real.exp (-s) := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hs)
    linarith
  have hb : 0 ≤ 1 - Real.exp (-τ) := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hτ)
    linarith
  have hμ : 0 < Real.exp (-τ) := Real.exp_pos _
  have hsum : Real.exp (-τ) * (1 - Real.exp (-s)) + (1 - Real.exp (-τ)) =
      1 - Real.exp (-(s + τ)) := by
    rw [neg_add, Real.exp_add]
    ring
  have hprod : Real.exp (-s) * Real.exp (-τ) = Real.exp (-(s + τ)) := by
    rw [neg_add, Real.exp_add]
  refine ContinuousLinearMap.ext fun y ↦ ?_
  simp only [ContinuousLinearMap.comp_apply]
  have e1 : heat (1 - Real.exp (-s)) (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y)) =
      dil (Real.exp (-τ)) (heat (Real.exp (-τ) * (1 - Real.exp (-s)))
        (heat (1 - Real.exp (-τ)) y)) :=
    (congrArg (fun L : E →L[ℝ] E ↦ L (heat (1 - Real.exp (-τ)) y))
      (hDG (Real.exp (-τ)) (1 - Real.exp (-s)) hμ ha)).symm
  have e2 : heat (Real.exp (-τ) * (1 - Real.exp (-s))) (heat (1 - Real.exp (-τ)) y) =
      heat (1 - Real.exp (-(s + τ))) y := by
    rw [← hsum, hH _ _ (mul_nonneg hμ.le ha) hb, ContinuousLinearMap.comp_apply]
  have e3 : ∀ z : E, dil (Real.exp (-s)) (dil (Real.exp (-τ)) z) =
      dil (Real.exp (-(s + τ))) z := fun z ↦ by
    rw [← hprod, hD _ _ (Real.exp_pos _) hμ, ContinuousLinearMap.comp_apply]
  rw [e1, e2, e3]

/-- For a linear isometric equivalence `e : E ≃ₗᵢ[ℝ] E` of a real seminormed space, the `j`-th
iterate is compatible with finite linear combinations and differences:
`∑ l, c l • e^[j] (y l) - e^[j] z = e^[j] (∑ l, c l • y l - z)`. -/
theorem sum_smul_iterate_sub_eq_iterate {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] E)
    (j : ℕ) {m : ℕ} (c : Fin m → ℝ) (y : Fin m → E) (z : E) :
    ∑ l, c l • (⇑e)^[j] (y l) - (⇑e)^[j] z = (⇑e)^[j] (∑ l, c l • y l - z) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ← ih, map_sub, map_sum, map_smul]

/-- Let `Λ τ : Z →L[ℝ] X` be continuous linear maps between real normed spaces such that `τ ↦ Λ τ ζ`
is continuous on `Ioi 0` for every `ζ`. If along a filter `l` one has `τ x → τ₀` with `0 < τ₀`,
`z x → z₀`, and eventually `‖Λ (τ x)‖ ≤ B`, then `Λ (τ x) (z x) → Λ τ₀ z₀` along `l`. Proof idea:
`Λ (τ x) z₀ → Λ τ₀ z₀` by continuity, and `‖Λ (τ x) (z x) - Λ (τ x) z₀‖ ≤ B * ‖z x - z₀‖ → 0`. -/
theorem tendsto_apply_of_continuousOn_of_norm_le {Z : Type} {X : Type} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup X] [NormedSpace ℝ X] (Λ : ℝ → Z →L[ℝ] X)
    (hΛc : ∀ ζ, ContinuousOn (fun τ ↦ Λ τ ζ) (Ioi 0))
    {α : Type} {l : Filter α} {τ : α → ℝ} {z : α → Z} {τ₀ : ℝ} {z₀ : Z} {B : ℝ}
    (h₀ : 0 < τ₀) (hτ : Tendsto τ l (𝓝 τ₀)) (hz : Tendsto z l (𝓝 z₀))
    (hB : ∀ᶠ x in l, ‖Λ (τ x)‖ ≤ B) :
    Tendsto (fun x ↦ Λ (τ x) (z x)) l (𝓝 (Λ τ₀ z₀)) := by
  have h1 : Tendsto (fun x ↦ Λ (τ x) z₀) l (𝓝 (Λ τ₀ z₀)) :=
    ((hΛc z₀).continuousAt (Ioi_mem_nhds h₀)).tendsto.comp hτ
  have hbd : ∀ᶠ x in l, ‖Λ (τ x) (z x) - Λ (τ x) z₀‖ ≤ B * ‖z x - z₀‖ := by
    filter_upwards [hB] with x hx
    rw [← map_sub]
    exact ((Λ (τ x)).le_opNorm _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hlim : Tendsto (fun x ↦ B * ‖z x - z₀‖) l (𝓝 0) := by
    have hz' : Tendsto (fun x ↦ ‖z x - z₀‖) l (𝓝 0) := by
      simpa using (hz.sub_const z₀).norm
    simpa using hz'.const_mul B
  simpa using (squeeze_zero_norm' hbd hlim).add h1

/-- If two continuous linear maps `Pu` and `M` on a real Banach space commute, `Pu * M = M * Pu`,
then `Pu` commutes with every power of `M` pointwise: `Pu ((M ^ n) x) = (M ^ n) (Pu x)` for all
`n : ℕ` and `x`. -/
theorem clm_apply_pow_comm_of_mul_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Pu M : E →L[ℝ] E} (hC : Pu * M = M * Pu) (n : ℕ) (x : E) :
    Pu ((M ^ n) x) = (M ^ n) (Pu x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, clm_apply_comm_of_mul_comm hC]

/-- Injective compact perturbation of an isomorphism: let `L₀ : E ≃L[ℝ] F` be a continuous linear
equivalence of real Banach spaces and `C : E →L[ℝ] F` with `C ∘ L₀.symm` a compact operator. If
`L₀ + C` is injective, then there is a continuous linear equivalence `e : E ≃L[ℝ] F` with
`e x = L₀ x + C x` for all `x`. The proof applies the Fredholm alternative to `1 + C ∘ L₀.symm` on
`F`. -/
theorem exists_equiv_of_injective_add_compact {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L₀ : E ≃L[ℝ] F) (C : E →L[ℝ] F)
    (hC : IsCompactOperator (C.comp (L₀.symm : F →L[ℝ] E)))
    (hinj : Function.Injective ((L₀ : E →L[ℝ] F) + C)) :
    ∃ e : E ≃L[ℝ] F, ∀ x, e x = L₀ x + C x := by
  set K : F →L[ℝ] F := C.comp (L₀.symm : F →L[ℝ] E) with hKdef
  have hK : ∀ y, ((1 : F →L[ℝ] F) + K) y = ((L₀ : E →L[ℝ] F) + C) (L₀.symm y) := by
    intro y
    simp [K]
  have hinjK : Function.Injective ((1 : F →L[ℝ] F) + K) := by
    intro y₁ y₂ hy
    rw [hK, hK] at hy
    exact L₀.symm.injective (hinj hy)
  have hu := isUnit_one_add_of_compact_of_injective K hC hinjK
  refine ⟨L₀.trans (ContinuousLinearEquiv.unitsEquiv ℝ F hu.unit), fun x ↦ ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.unitsEquiv_apply, IsUnit.unit_spec,
    hK, ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- Let `Pu` and `M` be continuous linear maps on a real Banach space with `Pu * Pu = Pu`, and
suppose every `y` in the range of `Pu` is `M x` for some `x` in the range of `Pu`. Then for every
`z` there is `w` with `Pu w = w` and `M w = Pu z`. -/
theorem exists_fixed_apply_eq_of_surjOn_range {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Pu M : E →L[ℝ] E} (hP : Pu * Pu = Pu)
    (hs : ∀ y ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), ∃ x ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), M x = y)
    (z : E) : ∃ w, Pu w = w ∧ M w = Pu z := by
  obtain ⟨x, hx, hMx⟩ := hs (Pu z) (LinearMap.mem_range.mpr ⟨z, rfl⟩)
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hx
  refine ⟨x, ?_, hMx⟩
  rw [← hv]
  exact clm_apply_apply_of_mul_self_eq hP v

/-- Right inverse of a bordered operator `Bd z = (z.1 + c z.1 + a z.2, q z.1)` on `H × (Fin k → ℝ)`,
with `H` a real Banach space. Suppose a subspace `V` of `H` is preserved by `c` and contains the
range of `a`, `Pr` maps `H` into `V` and fixes `V`, `z ↦ (c (Pr z.1), 0)` is a compact continuous
linear map `A`, and `z ↦ (a z.2, q (Pr z.1) - z.2)` is a composition `M ∘ S` of continuous linear
maps through `(Fin k → ℝ) × (Fin k → ℝ)`; if `Bd x = 0` and `x.1 ∈ V` imply `x = 0`, then there is a
continuous linear `T` with `(T y).1 ∈ V` and `Bd (T y) = y` for every `y` with `y.1 ∈ V`. The proof
shows that `1 + A + M ∘ S` is the identity plus a compact operator, is injective, and agrees with
`Bd` at every `z` whose image has first component in `V`, and then inverts it by the Fredholm
alternative. -/
theorem exists_inverse_of_compact_bordered {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] {k : ℕ}
    (V : Submodule ℝ H) (Bd A : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ)))
    (M : ((Fin k → ℝ) × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ)))
    (S : (H × (Fin k → ℝ)) →L[ℝ] ((Fin k → ℝ) × (Fin k → ℝ))) (hA : IsCompactOperator A)
    (c : H → H) (a : (Fin k → ℝ) → H) (q : H → (Fin k → ℝ)) (Pr : H → H)
    (hA1 : ∀ z, (A z).1 = c (Pr z.1)) (hA2 : ∀ z, (A z).2 = 0)
    (hB1 : ∀ z, (M (S z)).1 = a z.2) (hB2 : ∀ z, (M (S z)).2 = q (Pr z.1) - z.2)
    (hBd1 : ∀ z, (Bd z).1 = z.1 + c z.1 + a z.2) (hBd2 : ∀ z, (Bd z).2 = q z.1)
    (hc : ∀ g ∈ V, c g ∈ V) (ha : ∀ κ, a κ ∈ V) (hP1 : ∀ x, Pr x ∈ V) (hP2 : ∀ x ∈ V, Pr x = x)
    (hinj : ∀ x, x.1 ∈ V → Bd x = 0 → x = 0) :
    ∃ T : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ)), ∀ y, y.1 ∈ V → (T y).1 ∈ V ∧ Bd (T y) = y := by
  have hB : IsCompactOperator (M.comp S) := (isCompactOperator_of_locallyCompactSpace_dom
      S).clm_comp M
  set K := A + M.comp S with hKdef
  have hK : IsCompactOperator K := by
    rw [hKdef, FunLike.coe_add]
    exact hA.add hB
  have hform1 : ∀ z, (((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z).1 =
      z.1 + (c (Pr z.1) + a z.2) := fun z ↦ by
    simp [hKdef, hA1, hB1]
  have hform2 : ∀ z, (((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z).2 =
      q (Pr z.1) := fun z ↦ by
    simp [hKdef, hA2, hB2]
  have hfix : ∀ z, (((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z).1 ∈ V →
      z.1 ∈ V ∧ Bd z = ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) z := by
    intro z hz
    rw [hform1] at hz
    have hmem : z.1 ∈ V :=
      (Submodule.add_mem_iff_left _ (Submodule.add_mem _ (hc _ (hP1 z.1)) (ha _))).1 hz
    have hPr : Pr z.1 = z.1 := hP2 _ hmem
    refine ⟨hmem, Prod.ext ?_ ?_⟩
    · rw [hBd1, hform1, hPr, add_assoc]
    · rw [hBd2, hform2, hPr]
  have hinj' : Function.Injective ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) := by
    intro x y hxy
    have hz : ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨hm, hb⟩ := hfix (x - y) (by rw [hz]; exact Submodule.zero_mem _)
    exact sub_eq_zero.1 (hinj _ hm (hb.trans hz))
  obtain ⟨u, hu⟩ := isUnit_one_add_of_compact_of_injective K hK hinj'
  have hT : ∀ y, ((1 : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) + K) ((↑u⁻¹ :
      (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) y) = y := fun y ↦ by
    rw [← hu]
    change ((u : (H × (Fin k → ℝ)) →L[ℝ] (H × (Fin k → ℝ))) * ↑u⁻¹) y = y
    rw [Units.mul_inv]
    rfl
  refine ⟨↑u⁻¹, fun y hy ↦ ?_⟩
  obtain ⟨hm, hb⟩ := hfix _ (by rw [hT]; exact hy)
  exact ⟨hm, hb.trans (hT y)⟩

/-- For a continuous bilinear map `B : Y →L[ℝ] Y →L[ℝ] Y` on a real normed space and vectors with
`‖v‖ ≤ r` and `‖w‖ ≤ r`, `‖B v v - B w w‖ ≤ 2 * ‖B‖ * r * ‖v - w‖`. The proof uses
`B v v - B w w = B (v - w) v + B w (v - w)`. -/
theorem norm_bilin_self_sub_self_le_mul {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : Y →L[ℝ] Y →L[ℝ] Y) (v w : Y) {r : ℝ} (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖B v v - B w w‖ ≤ 2 * ‖B‖ * r * ‖v - w‖ := by
  rw [bilin_apply_self_sub_apply_self]
  have h1 := B.le_opNorm₂ (v - w) v
  have h2 := B.le_opNorm₂ w (v - w)
  have hB := norm_nonneg B
  have hd := norm_nonneg (v - w)
  calc ‖B (v - w) v + B w (v - w)‖ ≤ ‖B (v - w) v‖ + ‖B w (v - w)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖v - w‖ * ‖v‖ + ‖B‖ * ‖w‖ * ‖v - w‖ := add_le_add h1 h2
    _ ≤ ‖B‖ * ‖v - w‖ * r + ‖B‖ * r * ‖v - w‖ := by gcongr
    _ = 2 * ‖B‖ * r * ‖v - w‖ := by ring

/-- If the continuous linear maps `B n : X →L[ℝ] X` on a real normed space satisfy `‖B n‖ ≤ C` for
all `n : ℕ`, with `0 ≤ C`, then for every bounded sequence `g : lp (fun _ : ℕ ↦ X) ∞` and every
`n`, `‖if n = 0 then 0 else B (n - 1) (g (n - 1))‖ ≤ C * ‖g‖`. -/
theorem norm_ite_zero_apply_lp_pred_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : ℕ → X →L[ℝ] X) {C : ℝ} (hB : ∀ n, ‖B n‖ ≤ C) (hC : 0 ≤ C)
    (g : lp (fun _ : ℕ ↦ X) ∞) (n : ℕ) :
    ‖(if n = 0 then 0 else B (n - 1) (g (n - 1)))‖ ≤ C * ‖g‖ := by
  split_ifs
  · rw [norm_zero]
    exact mul_nonneg hC (norm_nonneg _)
  · exact norm_apply_lp_apply_le_mul_norm B hB g (n - 1)

/-- Fredholm alternative for a compact operator `K` on a real Banach space `X`: if `x + K x = 0`
implies `x = 0`, then for every `y` there is `x` with `x + K x = y`. Proof idea: an injective
compact perturbation of the identity is a continuous linear equivalence. -/
theorem exists_add_apply_eq_of_isCompactOperator {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] (K : X →L[ℝ] X)
    (hK : IsCompactOperator K) (hinj : ∀ x, x + K x = 0 → x = 0) : ∀ y, ∃ x, x + K x = y := by
  have hi : Function.Injective (((ContinuousLinearEquiv.refl ℝ X : X ≃L[ℝ] X) : X →L[ℝ] X) + K) :=
      by
    intro x x' hxx
    have h0 : (x - x') + K (x - x') = 0 := by
      have hxx' : x + K x = x' + K x' := hxx
      rw [map_sub, show x - x' + (K x - K x') = (x + K x) - (x' + K x') by abel, hxx', sub_self]
    exact sub_eq_zero.mp (hinj _ h0)
  obtain ⟨e, he⟩ := exists_equiv_of_injective_add_compact (ContinuousLinearEquiv.refl ℝ X) K
    (by simpa using hK) hi
  intro y
  refine ⟨e.symm y, ?_⟩
  have h := he (e.symm y)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Let `Pu` and `M` be continuous linear maps on a real Banach space with `Pu * Pu = Pu`, `0 ≤ K`,
`0 < r₂` and `‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖` for all `n : ℕ` and `x`, and suppose every
`y` in the range of `Pu` is `M x` for some `x` in the range of `Pu`. Then there is a continuous
linear map `N` with `Pu (N z) = N z` and `M (N z) = Pu z` for all `z`. The value `N z` is the unique
fixed point of `Pu` that `M` sends to `Pu z`, uniqueness gives linearity, and the bound with `n = 1`
gives `‖N z‖ ≤ K * r₂⁻¹ * ‖Pu‖ * ‖z‖`. -/
theorem exists_clm_right_inverse_on_range {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Pu M : E →L[ℝ] E} {K r₂ : ℝ} (hP : Pu * Pu = Pu)
    (hg : ∀ (n : ℕ) (x : E), ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖)
    (hs : ∀ y ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), ∃ x ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), M x = y)
    (hK : 0 ≤ K) (hr₂ : 0 < r₂) :
    ∃ N : E →L[ℝ] E, (∀ z, Pu (N z) = N z) ∧ ∀ z, M (N z) = Pu z := by
  choose f hf using exists_fixed_apply_eq_of_surjOn_range hP hs
  let L : E →ₗ[ℝ] E :=
    { toFun := f
      map_add' := fun a b ↦ by
        refine eq_of_apply_eq_of_norm_le hg (hf (a + b)).1 ?_ ?_
        · rw [map_add, (hf a).1, (hf b).1]
        · rw [(hf (a + b)).2, map_add, map_add, (hf a).2, (hf b).2]
      map_smul' := fun t a ↦ by
        refine eq_of_apply_eq_of_norm_le hg (hf (t • a)).1 ?_ ?_
        · rw [RingHom.id_apply, map_smul, (hf a).1]
        · rw [(hf (t • a)).2, RingHom.id_apply, map_smul, map_smul, (hf a).2] }
  refine ⟨L.mkContinuous (K * r₂⁻¹ * ‖Pu‖) fun z ↦ ?_, fun z ↦ (hf z).1, fun z ↦ (hf z).2⟩
  change ‖f z‖ ≤ K * r₂⁻¹ * ‖Pu‖ * ‖z‖
  have h1 := hg 1 (f z)
  rw [(hf z).1, pow_one, pow_one, (hf z).2] at h1
  calc ‖f z‖ ≤ K * r₂⁻¹ * ‖Pu z‖ := h1
    _ ≤ K * r₂⁻¹ * (‖Pu‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (Pu.le_opNorm z) (mul_nonneg hK (inv_nonneg.mpr hr₂.le))
    _ = K * r₂⁻¹ * ‖Pu‖ * ‖z‖ := by ring

/-- Let `B : Y →L[ℝ] Y →L[ℝ] Y` be a continuous bilinear map on a real Banach space and `y` a vector
with `8 * ‖B‖ * ‖y‖ ≤ 1`. Then there is `v` with `‖v‖ ≤ 2 * ‖y‖` and `v = y + B v v`. The map
`v ↦ y + B v v` sends the closed ball of radius `2 * ‖y‖` around `0` to itself and is a contraction
with constant `1 / 2` there, so the Banach fixed point theorem applies. -/
theorem exists_eq_add_bilin_self_of_small {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y]
    (B : Y →L[ℝ] Y →L[ℝ] Y) (y : Y) (hy : 8 * ‖B‖ * ‖y‖ ≤ 1) :
    ∃ v : Y, ‖v‖ ≤ 2 * ‖y‖ ∧ v = y + B v v := by
  have hB := norm_nonneg B
  have hy0 := norm_nonneg y
  have maps : ∀ v : Y, ‖v‖ ≤ 2 * ‖y‖ → ‖y + B v v‖ ≤ 2 * ‖y‖ := by
    intro v hv
    have h1 : ‖B v v‖ ≤ ‖B‖ * (2 * ‖y‖) * (2 * ‖y‖) :=
      (B.le_opNorm₂ v v).trans (by gcongr)
    have h2 := mul_le_mul_of_nonneg_right hy hy0
    calc ‖y + B v v‖ ≤ ‖y‖ + ‖B v v‖ := norm_add_le _ _
      _ ≤ 2 * ‖y‖ := by nlinarith
  let S := Metric.closedBall (0 : Y) (2 * ‖y‖)
  have memS : ∀ v : Y, v ∈ S ↔ ‖v‖ ≤ 2 * ‖y‖ := fun v ↦ mem_closedBall_zero_iff
  let f : S → S := fun v ↦ ⟨y + B v v, (memS _).2 (maps v ((memS _).1 v.2))⟩
  have hf : ContractingWith 2⁻¹ f := by
    refine ⟨two_inv_lt_one, LipschitzWith.of_dist_le_mul fun a b ↦ ?_⟩
    have ha := (memS _).1 a.2
    have hb := (memS _).1 b.2
    have key := norm_bilin_self_sub_self_le_mul B a b ha hb
    have hab : dist a b = ‖(a : Y) - b‖ := by rw [Subtype.dist_eq, dist_eq_norm]
    have hfab : dist (f a) (f b) = ‖B a a - B b b‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      simp only [f, add_sub_add_left_eq_sub]
    rw [hfab, hab]
    have hd := norm_nonneg ((a : Y) - b)
    have h3 := mul_le_mul_of_nonneg_right hy hd
    push_cast
    nlinarith
  have : Nonempty S := ⟨⟨0, (memS _).2 (by simp)⟩⟩
  have : CompleteSpace S := Metric.isClosed_closedBall.completeSpace_coe
  let vfix : S := ContractingWith.fixedPoint (α := S) f hf
  have hfix : f vfix = vfix := hf.fixedPoint_isFixedPt
  exact ⟨vfix, (memS _).1 vfix.2, (congrArg Subtype.val hfix).symm⟩

/-- For a continuous linear map `T` on a real Banach space with `‖T‖ < 1`,
`Ring.inverse (1 - T) (x - T x) = x` for every `x`. -/
theorem inverse_one_sub_apply_sub {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (T : F →L[ℝ] F) (hT : ‖T‖ < 1) (x : F) :
    Ring.inverse (1 - T) (x - T x) = x := by
  have h := congrArg (fun f : F →L[ℝ] F ↦ f x)
    (Ring.inverse_mul_cancel (1 - T) (isUnit_one_sub_of_norm_lt_one hT))
  simpa using h

/-- A continuous real-linear map `L : ℝ × ℝ → ℂ` satisfies
`L (x, y) = x * L (1, 0) + y * L (0, 1)` for all real `x`, `y`. -/
theorem clm_apply_prodMk_eq_mul_add_mul (L : ℝ × ℝ →L[ℝ] ℂ) (x y : ℝ) :
    L (x, y) = (x : ℂ) * L (1, 0) + (y : ℂ) * L (0, 1) := by
  have e : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  rw [e, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- In a monoid with zero, if `c` is a unit and `c * b = 1`, then `Ring.inverse c = b`. -/
theorem inverse_eq_of_mul_eq_one {R : Type*} [MonoidWithZero R] {c b : R} (hc : IsUnit c)
    (hcb : c * b = 1) : Ring.inverse c = b := by
  calc Ring.inverse c = Ring.inverse c * (c * b) := by rw [hcb, mul_one]
    _ = b := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hc, one_mul]

/-- For continuous linear maps on bounded sequences in `Y`, let `Op g n = A n (g n)`,
`Sh g n = if n = 0 then 0 else B (g (n - 1))` and `Sd e n = if n = 0 then G e else 0`. If
`R g = (e, h)` satisfies `h n - A n (h n) - (if n = 0 then G e else B (h (n - 1))) = g n` for
all `g`, `n`, then `(snd - Sh ∘ snd - Sd ∘ fst - Op ∘ snd) ∘ R` is the identity. -/
theorem lp_comp_eq_id_of_recurrence {W Y : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Sh Op : lp (fun _ : ℕ ↦ Y) ∞ →L[ℝ] lp (fun _ : ℕ ↦ Y) ∞)
    (Sd : W →L[ℝ] lp (fun _ : ℕ ↦ Y) ∞)
    (R : lp (fun _ : ℕ ↦ Y) ∞ →L[ℝ] W × lp (fun _ : ℕ ↦ Y) ∞)
    (A : ℕ → Y →L[ℝ] Y) (B : Y →L[ℝ] Y) (G : W →L[ℝ] Y)
    (hOp : ∀ g n, Op g n = A n (g n))
    (hSh : ∀ g n, Sh g n = if n = 0 then 0 else B (g (n - 1)))
    (hSd : ∀ e n, Sd e n = if n = 0 then G e else 0)
    (hR : ∀ g n, (R g).2 n - A n ((R g).2 n) -
      (if n = 0 then G (R g).1 else B ((R g).2 (n - 1))) = g n) :
    ContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ W (lp (fun _ : ℕ ↦ Y) ∞) -
      Sh.comp (ContinuousLinearMap.snd ℝ W (lp (fun _ : ℕ ↦ Y) ∞)) -
      Sd.comp (ContinuousLinearMap.fst ℝ W (lp (fun _ : ℕ ↦ Y) ∞)) -
      Op.comp (ContinuousLinearMap.snd ℝ W (lp (fun _ : ℕ ↦ Y) ∞))) R =
      ContinuousLinearMap.id ℝ _ := by
  refine ContinuousLinearMap.ext fun g ↦ lp.ext (funext fun n ↦ ?_)
  have h := hR g n
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, sub_apply,
    lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    hOp, hSh, hSd]
  rw [← h]
  by_cases hn : n = 0
  · simp only [hn, ite_true]
    abel
  · simp only [hn, ite_false]
    abel

/-- For a continuous linear map `T` on a real Banach space with `‖T‖ < 1` and every `y`, the vector
`x = Ring.inverse (1 - T) y` satisfies `x - T x = y`. The map `1 - T` is a unit, so
`(1 - T) * Ring.inverse (1 - T) = 1`. -/
theorem inverse_one_sub_apply_sub_apply_inverse {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (T : F →L[ℝ] F) (hT : ‖T‖ < 1) (y : F) :
    Ring.inverse (1 - T) y - T (Ring.inverse (1 - T) y) = y := by
  have h := congrArg (fun f : F →L[ℝ] F ↦ f y)
    (Ring.mul_inverse_cancel (1 - T) (isUnit_one_sub_of_norm_lt_one hT))
  simpa using h

/-- Let `Λ τ : Z →L[ℝ] XT` and `G : XT →L[ℝ] Y` be continuous linear maps of real normed spaces
with `‖G‖ ≤ M` and `‖Λ τ‖ ≤ K * τ ^ (-(3 / 4))` for `0 < τ ≤ 1`, and let `K, M, Cw, Cx ≥ 0`.
If `w : ℝ`, `‖w‖ ≤ Cw`, `‖z‖ ≤ Cx` and `0 < v ≤ τ ≤ 1`, then
`‖w • G (Λ τ z)‖ ≤ Cw * M * K * Cx * v ^ (-(3 / 4))`, since `τ ^ (-(3 / 4)) ≤ v ^ (-(3 / 4))`. -/
theorem norm_smul_apply_apply_le_mul_rpow {Z : Type} {XT : Type} {Y : Type} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z]
    [NormedAddCommGroup XT] [NormedSpace ℝ XT] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        (Λ : ℝ → Z →L[ℝ] XT) (G : XT →L[ℝ] Y) {K M Cw Cx : ℝ} (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hCw : 0 ≤ Cw) (hCx : 0 ≤ Cx) (hG : ‖G‖ ≤ M)
    (hb : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ K * τ ^ (-(3 / 4 : ℝ))) {w : ℝ} {z : Z} (hw : ‖w‖ ≤ Cw)
    (hz : ‖z‖ ≤ Cx) {τ v : ℝ} (hv : 0 < v) (hvτ : v ≤ τ) (hτ1 : τ ≤ 1) :
    ‖w • G (Λ τ z)‖ ≤ Cw * M * K * Cx * v ^ (-(3 / 4 : ℝ)) := by
  have hτ0 : 0 < τ := lt_of_lt_of_le hv hvτ
  have hr : τ ^ (-(3 / 4 : ℝ)) ≤ v ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hv hvτ (by norm_num)
  have hΛ : ‖Λ τ z‖ ≤ K * τ ^ (-(3 / 4 : ℝ)) * Cx :=
    ((Λ τ).le_opNorm z).trans (mul_le_mul (hb τ hτ0 hτ1) hz (norm_nonneg _) (by positivity))
  have hGz : ‖G (Λ τ z)‖ ≤ M * (K * τ ^ (-(3 / 4 : ℝ)) * Cx) :=
    (G.le_opNorm _).trans (mul_le_mul hG hΛ (norm_nonneg _) hM)
  rw [norm_smul]
  calc ‖w‖ * ‖G (Λ τ z)‖ ≤ Cw * (M * (K * τ ^ (-(3 / 4 : ℝ)) * Cx)) :=
        mul_le_mul hw hGz (norm_nonneg _) hCw
    _ ≤ Cw * (M * (K * v ^ (-(3 / 4 : ℝ)) * Cx)) := by gcongr
    _ = Cw * M * K * Cx * v ^ (-(3 / 4 : ℝ)) := by ring

/-- In a ring, let `u * v = 1` and `v * u = 1`, and let `B` and `u * B * v` be units. Then
`Ring.inverse (u * B * v) = u * Ring.inverse B * v`. The product of `u * B * v` with the right
side is one. -/
theorem inverse_mul_mul_eq_mul_inverse_mul {R : Type*} [Ring R] (u v B : R) (huv : u * v = 1)
    (hvu : v * u = 1)
    (hB : IsUnit B) (hc : IsUnit (u * B * v)) :
    Ring.inverse (u * B * v) = u * Ring.inverse B * v := by
  apply inverse_eq_of_mul_eq_one hc
  have : u * B * v * (u * Ring.inverse B * v) = u * (B * (v * u) * Ring.inverse B) * v := by
    simp only [mul_assoc]
  rw [this, hvu, mul_one, Ring.mul_inverse_cancel _ hB, mul_one, huv]

/-- In a normed ring with `‖1‖ ≤ 1`, if `1 - x` is a unit and `‖x‖ ≤ 1 / 4`, then
`‖Ring.inverse (1 - x)‖ ≤ 4 / 3`. -/
theorem norm_inverse_one_sub_le_four_thirds {R : Type*} [NormedRing R] (h1 : ‖(1 : R)‖ ≤ 1) {x : R}
    (hu : IsUnit (1 - x)) (hx : ‖x‖ ≤ 1 / 4) : ‖Ring.inverse (1 - x)‖ ≤ 4 / 3 := by
  have hy : (1 - x) * Ring.inverse (1 - x) = 1 := Ring.mul_inverse_cancel _ hu
  rw [sub_mul, one_mul] at hy
  have hy' := sub_eq_iff_eq_add.mp hy
  have hle : ‖Ring.inverse (1 - x)‖ ≤ 1 + ‖x‖ * ‖Ring.inverse (1 - x)‖ := by
    calc ‖Ring.inverse (1 - x)‖ = ‖1 + x * Ring.inverse (1 - x)‖ := by rw [← hy']
      _ ≤ ‖(1 : R)‖ + ‖x * Ring.inverse (1 - x)‖ := norm_add_le _ _
      _ ≤ 1 + ‖x‖ * ‖Ring.inverse (1 - x)‖ := add_le_add h1 (norm_mul_le _ _)
  have h0 := norm_nonneg (Ring.inverse (1 - x))
  nlinarith

end PDE.Analysis
