/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.SpaceTime.TimeBasis

/-!
# Space-time fields on time blocks

A `BlockField B E` is a field `t ↦ ∑ᵢ bᵢ(τₘ(t)) cₘᵢ` on consecutive time blocks
`[sₘ, sₘ₊₁]`, `m < M`, with the polynomial basis `B` in the local time
`τₘ(t) = lo + (t - sₘ) / kₘ`, `kₘ = (sₘ₊₁ - sₘ) / (hi - lo)`, and coefficients `cₘᵢ` in any real
vector space `E` (spatial fields, states of several components, or tables of node values). The
field `value` is the numerical part of an approximate space-time solution: it is used on
`[s₀, T)`, `T = s_M` the stopping time, and set to zero for `t ≥ T`, as in Chen and Hou, Part I,
Section 4.2.5 and Part II, Section 3.5.

* `blockDeriv m t = ∑ⱼ bⱼ(τₘ(t)) dₘⱼ` with `dₘⱼ = kₘ⁻¹ ∑ᵢ D i j cₘᵢ` is the time derivative on the
  open block (`hasDerivAt_value`, `deriv_value`), and `timeDeriv` the piecewise derivative.
* `residualCoeff π L m j = π dₘⱼ - L cₘⱼ`: for linear maps `π, L : E → E'` the residual
  `π (∂ₜ value) - L value` on the open block `m` is `∑ⱼ bⱼ(τₘ(t)) residualCoeff π L m j`
  (`map_blockDeriv_sub_map_blockValue`). For the Taylor basis of Part II (3.31) these are
  `C_{j+1}·V / k - 𝓛(C_j·V)` and `-𝓛(C_3·V)` (`derivCoeff_taylor`).
* `endTrace = F(T⁻)`, the last block at the stopping time, and `jump = -endTrace`, the jump
  `F(T) - F(T⁻)` at the stopping time (`tendsto_value_stop`). With exact agreement of
  consecutive blocks at their common boundary (`IsContinuous`) the field is the primitive of
  `timeDeriv` up to this one jump:
  `φ(value τ) = φ(value s₀) + ∫_{s₀}^τ φ(timeDeriv) + 1_{T ≤ τ} φ(jump)`
  (`map_value_eq_add_integral`), the integrated form of `∂ₜ F = timeDeriv + jump δ_T` of Part II
  (3.35)-(3.36) and of Part I, Section 4.2.5, footnote 32. Continuity on `[s₀, T)` follows
  (`continuousOn_value`).

Calculus is done after a linear map `φ : E →ₗ[ℝ] G` into a normed space (an evaluation at a
point, a component, a strain functional), so `E` needs no topology.

## Main definitions

* `BlockField`: a field on consecutive time blocks with the coefficients of a basis on each block.
* `BlockField.value`: the stopped field, the polynomial of block `m` on `[sₘ, sₘ₊₁)` and zero
  from the stopping time on.
* `BlockField.timeDeriv`: the piecewise time derivative.
* `BlockField.IsContinuous`: consecutive blocks agree at their common boundary.

## Main results

* `BlockField.hasDerivAt_value_of_notMem`: off the block boundaries `φ ∘ value` has the
  derivative `φ ∘ timeDeriv`.
* `BlockField.map_blockDeriv_sub_map_blockValue`: on block `m`,
  `π (∂ₜ F) - L F = ∑ⱼ bⱼ(τₘ(t)) (π dₘⱼ - L cₘⱼ)`.
* `BlockField.derivCoeff_taylor`: for the Taylor basis `dₘⱼ = kₘ⁻¹ cₘ,ⱼ₊₁` and `dₘ,ₙ₋₁ = 0`.
* `BlockField.tendsto_value_stop`: the left limit of the field at the stopping time is the end
  trace.
* `BlockField.map_value_eq_add_integral`: for `τ ≥ s₀`,
  `φ(value τ) = φ(value s₀) + ∫_{s₀}^τ φ(timeDeriv) + 1_{T ≤ τ} φ(jump)`.
* `BlockField.integrableOn_map_timeDeriv`: `φ ∘ timeDeriv` is integrable on every `[a, b]`.
* `BlockField.continuousOn_value`: the field is continuous on `[s₀, T)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Sections
  4.2.4-4.2.5, (4.19)-(4.22) and footnote 32.
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Sections 3.4-3.5,
  (3.31) and (3.35)-(3.36).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.SpaceTime

open Finset Set Filter MeasureTheory
open scoped Topology

variable {n : ℕ} {B : TimeBasis n} {E E' G : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup E'] [Module ℝ E']

/-- A field on the consecutive time blocks `[start m, start (m + 1)]`, `m < count`, with the
coefficients `coeff m i` of the basis `B` on block `m`. -/
structure BlockField (B : TimeBasis n) (E : Type*) where
  /-- The number of blocks. -/
  count : ℕ
  /-- The block boundaries. -/
  start : ℕ → ℝ
  /-- The coefficients of the basis functions on each block. -/
  coeff : ℕ → Fin n → E

namespace BlockField

variable (F : BlockField B E)

/-- The time scale `kₘ = (sₘ₊₁ - sₘ) / (hi - lo)` of block `m`: `dt = kₘ dτ`. -/
noncomputable def scale (m : ℕ) : ℝ :=
  (F.start (m + 1) - F.start m) / (B.hi - B.lo)

/-- The local time `τₘ(t) = lo + (t - sₘ) / kₘ` of block `m`. -/
noncomputable def localTime (m : ℕ) (t : ℝ) : ℝ :=
  B.lo + (t - F.start m) / F.scale m

/-- The polynomial of block `m`, `∑ᵢ bᵢ(τₘ(t)) cₘᵢ`, at any time `t`. -/
noncomputable def blockValue (m : ℕ) (t : ℝ) : E :=
  ∑ i, B.eval i (F.localTime m t) • F.coeff m i

/-- The coefficients `dₘⱼ = kₘ⁻¹ ∑ᵢ D i j cₘᵢ` of the time derivative of block `m`. -/
noncomputable def derivCoeff (m : ℕ) (j : Fin n) : E :=
  (F.scale m)⁻¹ • ∑ i, (B.derivMatrix i j : ℝ) • F.coeff m i

/-- The time derivative `∑ⱼ bⱼ(τₘ(t)) dₘⱼ` of the polynomial of block `m`. -/
noncomputable def blockDeriv (m : ℕ) (t : ℝ) : E :=
  ∑ j, B.eval j (F.localTime m t) • F.derivCoeff m j

/-- The stopping time `T = s_M`. -/
def stop : ℝ :=
  F.start F.count

/-- The field: the polynomial of block `m` on `[sₘ, sₘ₊₁)`, zero before `s₀` and from the
stopping time on. -/
noncomputable def value (t : ℝ) : E :=
  ∑ m ∈ range F.count, if F.start m ≤ t ∧ t < F.start (m + 1) then F.blockValue m t else 0

/-- The piecewise time derivative: the derivative of the polynomial on each open block, zero at the
block boundaries and outside `(s₀, T)`. -/
noncomputable def timeDeriv (t : ℝ) : E :=
  ∑ m ∈ range F.count, if F.start m < t ∧ t < F.start (m + 1) then F.blockDeriv m t else 0

/-- The end trace `F(T⁻)`: the polynomial of the last block at the stopping time. The stopped
field itself vanishes at `T`, so quantities at the stop (such as `F_end(T) = D² F(T⁻)(0)` of
Part II, Section 3.5) are taken from this trace. It is meaningful for a nonempty field
(`0 < count`), which every theorem about it assumes. -/
noncomputable def endTrace : E :=
  F.blockValue (F.count - 1) F.stop

/-- The jump `F(T) - F(T⁻) = -F(T⁻)` at the stopping time. -/
noncomputable def jump : E :=
  -F.endTrace

/-- The residual coefficients `π dₘⱼ - L cₘⱼ` for linear maps `π` (the time derivative as an
element of `E'`) and `L` (the operator). -/
noncomputable def residualCoeff (π L : E →ₗ[ℝ] E') (m : ℕ) (j : Fin n) : E' :=
  π (F.derivCoeff m j) - L (F.coeff m j)

/-- The block boundaries increase. -/
def IsOrdered : Prop :=
  ∀ m < F.count, F.start m < F.start (m + 1)

/-- Consecutive blocks agree at their common boundary. -/
def IsContinuous : Prop :=
  ∀ m, m + 1 < F.count → F.blockValue m (F.start (m + 1)) = F.blockValue (m + 1) (F.start (m + 1))

/-! ### Local time and boundary values -/

variable {F}

omit [AddCommGroup E] [Module ℝ E] in
/-- The time scale `kₘ` of a block of an ordered field over a sound basis is positive. -/
theorem scale_pos (hB : B.Sound) (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count) :
    0 < F.scale m :=
  div_pos (sub_pos.2 (hF m hm)) (sub_pos.2 (by exact_mod_cast hB.lo_lt_hi))

omit [AddCommGroup E] [Module ℝ E] in
variable (F) in
/-- At the start `sₘ` of block `m` the local time is the left end `lo` of the reference interval. -/
theorem localTime_start (m : ℕ) : F.localTime m (F.start m) = B.lo := by
  simp [localTime]

omit [AddCommGroup E] [Module ℝ E] in
/-- At the end `sₘ₊₁` of a block of an ordered field over a sound basis the local time is the
right end `hi` of the reference interval. -/
theorem localTime_end (hB : B.Sound) (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count) :
    F.localTime m (F.start (m + 1)) = B.hi := by
  have h₁ : F.start (m + 1) - F.start m ≠ 0 := (sub_pos.2 (hF m hm)).ne'
  have h₂ : (B.hi : ℝ) - B.lo ≠ 0 := (sub_pos.2 (by exact_mod_cast hB.lo_lt_hi)).ne'
  simp only [localTime, scale]
  field_simp
  ring

omit [AddCommGroup E] [Module ℝ E] in
/-- On its block the local time lies in the reference interval. -/
theorem localTime_mem_Icc (hB : B.Sound) (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count) {t : ℝ}
    (ht : t ∈ Icc (F.start m) (F.start (m + 1))) : F.localTime m t ∈ Icc (B.lo : ℝ) B.hi := by
  have hk := scale_pos hB hF hm
  constructor
  · simp only [localTime]
    have : 0 ≤ (t - F.start m) / F.scale m := div_nonneg (sub_nonneg.2 ht.1) hk.le
    linarith
  · rw [← localTime_end hB hF hm]
    simp only [localTime]
    gcongr
    exact ht.2

variable (F) in
/-- At its start the polynomial of block `m` is `∑ᵢ bᵢ(lo) cₘᵢ`. -/
theorem blockValue_start (m : ℕ) :
    F.blockValue m (F.start m) = ∑ i, (B.startValue i : ℝ) • F.coeff m i := by
  simp [blockValue, localTime_start, TimeBasis.eval_lo]

/-- At its end the polynomial of a block of an ordered field over a sound basis is
`∑ᵢ bᵢ(hi) cₘᵢ`. -/
theorem blockValue_end (hB : B.Sound) (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count) :
    F.blockValue m (F.start (m + 1)) = ∑ i, (B.endValue i : ℝ) • F.coeff m i := by
  simp [blockValue, localTime_end hB hF hm, TimeBasis.eval_hi]

/-- Continuity in terms of the end values of the basis: `∑ᵢ bᵢ(hi) cₘᵢ = ∑ᵢ bᵢ(lo) cₘ₊₁ᵢ`. -/
theorem isContinuous_of_endValue (hB : B.Sound) (hF : F.IsOrdered)
    (h : ∀ m, m + 1 < F.count →
      ∑ i, (B.endValue i : ℝ) • F.coeff m i = ∑ i, (B.startValue i : ℝ) • F.coeff (m + 1) i) :
    F.IsContinuous := fun m hm ↦ by
  rw [blockValue_end hB hF (by omega), h m hm, ← blockValue_start]

omit [AddCommGroup E] [Module ℝ E] in
/-- The block boundaries of an ordered field are monotone up to the stopping time. -/
theorem start_le_start (hF : F.IsOrdered) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.count) :
    F.start i ≤ F.start j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (hF j (by omega)).le

omit [AddCommGroup E] [Module ℝ E] in
/-- The block boundaries of an ordered field are strictly increasing up to the stopping time. -/
theorem start_lt_start (hF : F.IsOrdered) {i j : ℕ} (hij : i < j) (hj : j ≤ F.count) :
    F.start i < F.start j :=
  (hF i (by omega)).trans_le (start_le_start hF hij hj)

/-! ### The field on a block -/

/-- On `[sₘ, sₘ₊₁)` the field is the polynomial of block `m`. -/
theorem value_eq (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count) {t : ℝ}
    (ht : t ∈ Ico (F.start m) (F.start (m + 1))) : F.value t = F.blockValue m t := by
  rw [value, Finset.sum_eq_single m]
  · exact ite_eq_left ht
  · intro m' hm' hne
    rw [ite_eq_right]
    rintro ⟨h₁, h₂⟩
    rcases lt_or_gt_of_ne hne with h | h
    · have := start_le_start hF (show m' + 1 ≤ m by omega) hm.le
      linarith [ht.1]
    · have := start_le_start hF (show m + 1 ≤ m' by omega)
        (Finset.mem_range.1 hm').le
      linarith [ht.2]
  · intro h
    exact absurd (Finset.mem_range.2 hm) h

/-- On the open block `(sₘ, sₘ₊₁)` the piecewise time derivative is the derivative of the polynomial
of block `m`. -/
theorem timeDeriv_eq (hF : F.IsOrdered) {m : ℕ} (hm : m < F.count) {t : ℝ}
    (ht : t ∈ Ioo (F.start m) (F.start (m + 1))) : F.timeDeriv t = F.blockDeriv m t := by
  rw [timeDeriv, Finset.sum_eq_single m]
  · exact ite_eq_left ht
  · intro m' hm' hne
    rw [ite_eq_right]
    rintro ⟨h₁, h₂⟩
    rcases lt_or_gt_of_ne hne with h | h
    · have := start_le_start hF (show m' + 1 ≤ m by omega) hm.le
      linarith [ht.1]
    · have := start_le_start hF (show m + 1 ≤ m' by omega)
        (Finset.mem_range.1 hm').le
      linarith [ht.2]
  · intro h
    exact absurd (Finset.mem_range.2 hm) h

/-- The field vanishes from the stopping time `T` on. -/
theorem value_eq_zero_of_stop_le (hF : F.IsOrdered) {t : ℝ} (ht : F.stop ≤ t) :
    F.value t = 0 := by
  refine Finset.sum_eq_zero fun m hm ↦ ite_eq_right ?_
  have := start_le_start hF (show m + 1 ≤ F.count by have := Finset.mem_range.1 hm; omega)
    le_rfl
  rintro ⟨-, h⟩
  exact absurd (h.trans_le this) (not_lt.2 ht)

/-- The piecewise time derivative vanishes from the stopping time `T` on. -/
theorem timeDeriv_eq_zero_of_stop_le (hF : F.IsOrdered) {t : ℝ} (ht : F.stop ≤ t) :
    F.timeDeriv t = 0 := by
  refine Finset.sum_eq_zero fun m hm ↦ ite_eq_right ?_
  have := start_le_start hF (show m + 1 ≤ F.count by have := Finset.mem_range.1 hm; omega)
    le_rfl
  rintro ⟨-, h⟩
  exact absurd (h.trans_le this) (not_lt.2 ht)

/-- The field vanishes before the first boundary `s₀`. -/
theorem value_eq_zero_of_lt_start (hF : F.IsOrdered) {t : ℝ} (ht : t < F.start 0) :
    F.value t = 0 := by
  refine Finset.sum_eq_zero fun m hm ↦ ite_eq_right ?_
  have := start_le_start hF (Nat.zero_le m) (Finset.mem_range.1 hm).le
  rintro ⟨h, -⟩
  linarith

/-- The piecewise time derivative vanishes up to the first boundary `s₀`. -/
theorem timeDeriv_eq_zero_of_le_start (hF : F.IsOrdered) {t : ℝ} (ht : t ≤ F.start 0) :
    F.timeDeriv t = 0 := by
  refine Finset.sum_eq_zero fun m hm ↦ ite_eq_right ?_
  have := start_le_start hF (Nat.zero_le m) (Finset.mem_range.1 hm).le
  rintro ⟨h, -⟩
  linarith

omit [AddCommGroup E] [Module ℝ E] in
/-- Every time in `[s₀, T)` lies in a block. -/
theorem exists_mem_Ico {t : ℝ} (h₀ : F.start 0 ≤ t) (hT : t < F.stop) :
    ∃ m < F.count, t ∈ Ico (F.start m) (F.start (m + 1)) := by
  have hc : 0 < F.count := by
    rcases Nat.eq_zero_or_pos F.count with h | h
    · simp only [stop, h] at hT
      linarith
    · exact h
  have hex : ∃ m, m < F.count ∧ t < F.start (m + 1) :=
    ⟨F.count - 1, by omega, by rwa [Nat.sub_add_cancel hc]⟩
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rwa [h]
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel h] at hmin
    have hlt : Nat.find hex - 1 < F.count := by have := (Nat.find_spec hex).1; omega
    exact not_lt.1 fun h' ↦ hmin ⟨hlt, h'⟩

/-! ### Derivatives after a linear map -/

variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A linear map `φ` applied to the polynomial of a block is `∑ᵢ bᵢ(τₘ(t)) φ(cₘᵢ)`. -/
theorem map_blockValue (φ : E →ₗ[ℝ] G) (m : ℕ) (t : ℝ) :
    φ (F.blockValue m t) = ∑ i, B.eval i (F.localTime m t) • φ (F.coeff m i) := by
  simp [blockValue, map_sum, map_smul]

omit [AddCommGroup E] [Module ℝ E] in
variable (F) in
/-- The local time `τₘ` has derivative `kₘ⁻¹`. -/
theorem hasDerivAt_localTime (m : ℕ) (t : ℝ) :
    HasDerivAt (F.localTime m) (F.scale m)⁻¹ t := by
  have h := (((hasDerivAt_id t).sub_const (F.start m)).div_const (F.scale m)).const_add
    (B.lo : ℝ)
  convert h using 1
  · funext x
    rfl
  · rw [one_div]

/-- The polynomial of a block, after a linear map `φ`, is continuous in time. -/
theorem continuous_map_blockValue (φ : E →ₗ[ℝ] G) (m : ℕ) :
    Continuous fun t ↦ φ (F.blockValue m t) := by
  simp only [map_blockValue]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact ((B.continuous_eval i).comp
    (continuous_iff_continuousAt.2 fun t ↦ (F.hasDerivAt_localTime m t).continuousAt)).smul
      continuous_const

/-- **The derivative of a block.** The time derivative of `φ ∘ blockValue m` is
`φ ∘ blockDeriv m`. -/
theorem hasDerivAt_map_blockValue (hB : B.Sound) (φ : E →ₗ[ℝ] G) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s ↦ φ (F.blockValue m s)) (φ (F.blockDeriv m t)) t := by
  simp only [map_blockValue]
  have h : HasDerivAt (fun s ↦ ∑ i, B.eval i (F.localTime m s) • φ (F.coeff m i))
      (∑ i, ((∑ j, (B.derivMatrix i j : ℝ) * B.eval j (F.localTime m t)) * (F.scale m)⁻¹) •
        φ (F.coeff m i)) t :=
    HasDerivAt.fun_sum fun i _ ↦
      (((hB.hasDerivAt i _).comp t (F.hasDerivAt_localTime m t))).smul_const _
  convert h using 1
  simp only [blockDeriv, derivCoeff, map_sum, map_smul, Finset.smul_sum, smul_smul,
    Finset.sum_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  ring

/-- On an open block the field has the derivative of the block. -/
theorem hasDerivAt_value (hB : B.Sound) (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G) {m : ℕ}
    (hm : m < F.count) {t : ℝ} (ht : t ∈ Ioo (F.start m) (F.start (m + 1))) :
    HasDerivAt (fun s ↦ φ (F.value s)) (φ (F.timeDeriv t)) t := by
  rw [timeDeriv_eq hF hm ht]
  refine (F.hasDerivAt_map_blockValue hB φ m t).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [value_eq hF hm ⟨hs.1.le, hs.2⟩]

omit [AddCommGroup E] [Module ℝ E] in
/-- The block boundaries form a finite set of times. -/
theorem finite_start_image (F : BlockField B E) : (F.start '' Set.Iic F.count).Finite :=
  (Set.finite_Iic _).image _

/-- **The derivative off the block boundaries.** At every time that is not a block boundary,
`φ ∘ value` has the derivative `φ ∘ timeDeriv`; before `s₀` and after `T` both vanish. -/
theorem hasDerivAt_value_of_notMem (hB : B.Sound) (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G) {t : ℝ}
    (ht : t ∉ F.start '' Set.Iic F.count) :
    HasDerivAt (fun s ↦ φ (F.value s)) (φ (F.timeDeriv t)) t := by
  have hne : ∀ m ≤ F.count, t ≠ F.start m := fun m hm h ↦ ht ⟨m, hm, h.symm⟩
  rcases lt_or_gt_of_ne (hne 0 (Nat.zero_le _)) with h₀ | h₀
  · rw [timeDeriv_eq_zero_of_le_start hF h₀.le, map_zero]
    refine (hasDerivAt_const t (0 : G)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h₀] with s hs
    rw [value_eq_zero_of_lt_start hF hs, map_zero]
  rcases lt_or_gt_of_ne (hne F.count le_rfl) with hT | hT
  · obtain ⟨m, hm, hmem⟩ := exists_mem_Ico h₀.le hT
    exact hasDerivAt_value hB hF φ hm ⟨lt_of_le_of_ne hmem.1 (hne m hm.le).symm, hmem.2⟩
  · rw [timeDeriv_eq_zero_of_stop_le hF hT.le, map_zero]
    refine (hasDerivAt_const t (0 : G)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hT] with s hs
    rw [value_eq_zero_of_stop_le hF hs.le, map_zero]

/-- **The pointwise derivative.** At every time that is not a block boundary, Lean's `deriv` of
`φ ∘ value` is `φ ∘ timeDeriv`. The exceptional set does not depend on `φ`, so for evaluations
at spatial points it is one finite set of times for all points. -/
theorem deriv_value (hB : B.Sound) (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G) {t : ℝ}
    (ht : t ∉ F.start '' Set.Iic F.count) :
    deriv (fun s ↦ φ (F.value s)) t = φ (F.timeDeriv t) :=
  (hasDerivAt_value_of_notMem hB hF φ ht).deriv

/-! ### Residuals -/

variable (F) in
/-- **The residual of a block in the basis.** On block `m`,
`π (∂ₜ F) - L F = ∑ⱼ bⱼ(τₘ(t)) (π dₘⱼ - L cₘⱼ)`. -/
theorem map_blockDeriv_sub_map_blockValue (π L : E →ₗ[ℝ] E') (m : ℕ) (t : ℝ) :
    π (F.blockDeriv m t) - L (F.blockValue m t) =
      ∑ j, B.eval j (F.localTime m t) • F.residualCoeff π L m j := by
  simp [blockDeriv, blockValue, residualCoeff, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]

/-- For the Taylor basis `bᵢ = τⁱ / i!` the derivative coefficients are the shifted coefficients:
`dₘⱼ = kₘ⁻¹ cₘ,ⱼ₊₁` and `dₘ,ₙ₋₁ = 0`, so the residual coefficients are those of Part II (3.31),
`C_{j+1}·V / k - 𝓛(C_j·V)` and `-𝓛(C_3·V)`. -/
theorem derivCoeff_taylor {r : ℚ} (F : BlockField (taylor n r) E) (m : ℕ) (j : Fin n) :
    F.derivCoeff m j =
      (F.scale m)⁻¹ • if h : (j : ℕ) + 1 < n then F.coeff m ⟨(j : ℕ) + 1, h⟩ else 0 := by
  rw [derivCoeff]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, h⟩]
    · simp [taylor]
    · intro i _ hi
      have : (j : ℕ) + 1 ≠ i := fun h' ↦ hi (Fin.ext h'.symm)
      simp [taylor, this]
    · simp
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    have : (j : ℕ) + 1 ≠ i := by have := i.isLt; omega
    simp [taylor, this]

/-- The field vanishes from the stopping time on. -/
theorem continuousOn_value_Ici (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G) :
    ContinuousOn (fun t ↦ φ (F.value t)) (Ici F.stop) :=
  continuousOn_const.congr fun t ht ↦ by
    simp only
    rw [value_eq_zero_of_stop_le hF ht, map_zero]

/-- **The left limit at the stopping time** is the end trace, so the jump `F(T) - F(T⁻)` is
`jump`. -/
theorem tendsto_value_stop (hF : F.IsOrdered) (hpos : 0 < F.count) (φ : E →ₗ[ℝ] G) :
    Tendsto (fun t ↦ φ (F.value t)) (𝓝[<] F.stop) (𝓝 (φ F.endTrace)) := by
  have hl : F.count - 1 < F.count := by omega
  have hs : F.start (F.count - 1 + 1) = F.stop := by rw [Nat.sub_add_cancel hpos]; rfl
  have hlt : F.start (F.count - 1) < F.stop := hs ▸ hF _ hl
  refine ((F.continuous_map_blockValue φ _).tendsto _).mono_left nhdsWithin_le_nhds
    |>.congr' ?_
  filter_upwards [Ico_mem_nhdsLT hlt] with t ht
  rw [value_eq hF hl (hs ▸ ht)]

/-! ### The integrated form with the jump at the stopping time -/

/-- The piecewise time derivative, after a linear map `φ`, is interval integrable on every
interval. -/
theorem intervalIntegrable_map_timeDeriv (φ : E →ₗ[ℝ] G) (a b : ℝ) :
    IntervalIntegrable (fun r ↦ φ (F.timeDeriv r)) volume a b := by
  have h : (fun r ↦ φ (F.timeDeriv r)) = ∑ m ∈ range F.count,
      (Set.Ioo (F.start m) (F.start (m + 1))).indicator (fun s ↦ φ (F.blockDeriv m s)) := by
    funext r
    simp only [timeDeriv, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    by_cases hr : F.start m < r ∧ r < F.start (m + 1)
    · rw [ite_eq_left hr, indicator_of_mem (show r ∈ Set.Ioo _ _ from hr)]
    · rw [ite_eq_right hr, map_zero, indicator_of_notMem (show r ∉ Set.Ioo _ _ from hr)]
  rw [h]
  refine IntervalIntegrable.sum _ fun m _ ↦ ?_
  have hc : Continuous fun s ↦ φ (F.blockDeriv m s) := by
    simp only [blockDeriv, map_sum, map_smul]
    exact continuous_finsetSum _ fun j _ ↦ ((B.continuous_eval j).comp
      (continuous_iff_continuousAt.2 fun t ↦ (F.hasDerivAt_localTime m t).continuousAt)).smul
        continuous_const
  rw [intervalIntegrable_iff]
  exact (hc.integrableOn_uIcc.mono_set Set.uIoc_subset_uIcc).indicator measurableSet_Ioo

variable [CompleteSpace G]

omit [CompleteSpace G] in
/-- The piecewise time derivative, after a linear map `φ`, is integrable on every `[a, b]`. -/
theorem integrableOn_map_timeDeriv (φ : E →ₗ[ℝ] G) (a b : ℝ) :
    IntegrableOn (fun r ↦ φ (F.timeDeriv r)) (Icc a b) := by
  rcases le_or_gt a b with h | h
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le h).1
      (F.intervalIntegrable_map_timeDeriv φ a b)
  · rw [Icc_eq_empty (not_le.2 h)]
    exact integrableOn_empty

/-- The fundamental theorem on part of one block. -/
theorem integral_map_timeDeriv_block (hB : B.Sound) (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G)
    {m : ℕ} (hm : m < F.count) {τ : ℝ} (hτ : τ ∈ Icc (F.start m) (F.start (m + 1))) :
    ∫ r in F.start m..τ, φ (F.timeDeriv r) =
      φ (F.blockValue m τ) - φ (F.blockValue m (F.start m)) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1
    (F.continuous_map_blockValue φ m).continuousOn (fun x hx ↦ ?_)
    (F.intervalIntegrable_map_timeDeriv φ _ _)
  rw [timeDeriv_eq hF hm ⟨hx.1, hx.2.trans_le hτ.2⟩]
  exact F.hasDerivAt_map_blockValue hB φ m x

/-- For a continuous ordered field and `m < count`,
`∫_{s₀}^{sₘ} φ(timeDeriv) = φ(blockValue m sₘ) - φ(blockValue 0 s₀)`. -/
theorem integral_map_timeDeriv_start (hB : B.Sound) (hF : F.IsOrdered) (hc : F.IsContinuous)
    (φ : E →ₗ[ℝ] G) {m : ℕ} (hm : m < F.count) :
    ∫ r in F.start 0..F.start m, φ (F.timeDeriv r) =
      φ (F.blockValue m (F.start m)) - φ (F.blockValue 0 (F.start 0)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (F.intervalIntegrable_map_timeDeriv φ _ _) (F.intervalIntegrable_map_timeDeriv φ _ _),
      ih (by omega), integral_map_timeDeriv_block hB hF φ (by omega)
        ⟨(hF m (by omega)).le, le_rfl⟩, hc m hm]
    abel

/-- **The integrated form with the jump.** For `τ ≥ s₀`,
`φ(value τ) = φ(value s₀) + ∫_{s₀}^τ φ(timeDeriv) + 1_{T ≤ τ} φ(jump)`: the field is the primitive
of its piecewise derivative on `[s₀, T)` and drops to zero at `T` by the jump. These are the
fields of `HasDerivWithJump` (with `s₀ = 0`). -/
theorem map_value_eq_add_integral (hB : B.Sound) (hF : F.IsOrdered) (hc : F.IsContinuous)
    (hpos : 0 < F.count) (φ : E →ₗ[ℝ] G) {τ : ℝ} (hτ : F.start 0 ≤ τ) :
    φ (F.value τ) = φ (F.value (F.start 0)) + (∫ r in F.start 0..τ, φ (F.timeDeriv r)) +
      if F.stop ≤ τ then φ F.jump else 0 := by
  have h₀ : F.value (F.start 0) = F.blockValue 0 (F.start 0) :=
    value_eq hF hpos ⟨le_rfl, hF 0 hpos⟩
  rcases lt_or_ge τ F.stop with hT | hT
  · obtain ⟨m, hm, hmem⟩ := exists_mem_Ico hτ hT
    rw [ite_eq_right (not_le.2 hT), add_zero, value_eq hF hm hmem, h₀,
      ← intervalIntegral.integral_add_adjacent_intervals
        (F.intervalIntegrable_map_timeDeriv φ _ (F.start m))
        (F.intervalIntegrable_map_timeDeriv φ _ _),
      integral_map_timeDeriv_start hB hF hc φ hm,
      integral_map_timeDeriv_block hB hF φ hm ⟨hmem.1, hmem.2.le⟩]
    abel
  · have hl : F.count - 1 < F.count := by omega
    have hs : F.start (F.count - 1 + 1) = F.stop := by rw [Nat.sub_add_cancel hpos]; rfl
    have hzero : ∫ r in F.stop..τ, φ (F.timeDeriv r) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : G)), intervalIntegral.integral_zero]
      intro r hr
      rw [Set.uIcc_of_le hT] at hr
      simp [timeDeriv_eq_zero_of_stop_le hF hr.1]
    rw [ite_eq_left hT, value_eq_zero_of_stop_le hF hT, map_zero, h₀,
      ← intervalIntegral.integral_add_adjacent_intervals
        (F.intervalIntegrable_map_timeDeriv φ _ F.stop)
        (F.intervalIntegrable_map_timeDeriv φ _ _), hzero, add_zero, ← hs,
      ← intervalIntegral.integral_add_adjacent_intervals
        (F.intervalIntegrable_map_timeDeriv φ _ (F.start (F.count - 1)))
        (F.intervalIntegrable_map_timeDeriv φ _ _),
      integral_map_timeDeriv_start hB hF hc φ hl,
      integral_map_timeDeriv_block hB hF φ hl ⟨(hF _ hl).le, le_rfl⟩, jump, endTrace, map_neg, hs]
    abel

/-- **The integrated form from time zero.** With `s₀ = 0`, for `τ ≥ 0`,
`φ(value τ) = φ(value 0) + ∫₀^τ φ(timeDeriv) + 1_{T ≤ τ} φ(jump)`; together with
`integrableOn_map_timeDeriv` these are the two fields of `HasDerivWithJump`. -/
theorem map_value_eq_add_integral_zero (hB : B.Sound) (hF : F.IsOrdered) (hc : F.IsContinuous)
    (hpos : 0 < F.count) (h₀ : F.start 0 = 0) (φ : E →ₗ[ℝ] G) {τ : ℝ} (hτ : 0 ≤ τ) :
    φ (F.value τ) = φ (F.value 0) + (∫ r in (0 : ℝ)..τ, φ (F.timeDeriv r)) +
      if F.stop ≤ τ then φ F.jump else 0 := by
  have := map_value_eq_add_integral hB hF hc hpos φ (τ := τ) (h₀ ▸ hτ)
  rwa [h₀] at this

/-- The field is continuous on `[s₀, T)`. -/
theorem continuousOn_value (hB : B.Sound) (hF : F.IsOrdered) (hc : F.IsContinuous)
    (φ : E →ₗ[ℝ] G) : ContinuousOn (fun t ↦ φ (F.value t)) (Ico (F.start 0) F.stop) := by
  rcases Nat.eq_zero_or_pos F.count with h | hpos
  · intro t ht
    have : F.stop = F.start 0 := by simp [stop, h]
    exact absurd ht.2 (not_lt.2 (this ▸ ht.1))
  have hprim : ContinuousOn (fun τ ↦ ∫ r in F.start 0..τ, φ (F.timeDeriv r))
      (Icc (F.start 0) F.stop) := by
    have := intervalIntegral.continuousOn_primitive_interval'
      (F.intervalIntegrable_map_timeDeriv φ (F.start 0) F.stop)
      (show F.start 0 ∈ Set.uIcc (F.start 0) F.stop from Set.left_mem_uIcc)
    rwa [Set.uIcc_of_le (show F.start 0 ≤ F.stop from start_le_start hF (Nat.zero_le _) le_rfl)]
      at this
  have hcont : ContinuousOn (fun τ ↦ φ (F.value (F.start 0)) +
      ∫ r in F.start 0..τ, φ (F.timeDeriv r)) (Icc (F.start 0) F.stop) :=
    continuousOn_const.add hprim
  refine (hcont.mono Ico_subset_Icc_self).congr fun t ht ↦ ?_
  rw [map_value_eq_add_integral hB hF hc hpos φ ht.1, ite_eq_right (not_le.2 ht.2), add_zero]

end BlockField

end CAS.Numerics.SpaceTime
