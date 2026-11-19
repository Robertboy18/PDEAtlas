/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.SpaceTime.Integrals
public import PDE.Analysis.Evolution.ODE.Linear.Scalar.Stopped

/-!
# Block fields with analytic corrections

Chen and Hou, Part II, Sections 3.3-3.5, correct the numerical solution `Ŵ⁽¹⁾` of each mode by
`a(t) ∘ χ_{·2} = ∑ₗ aₗ(t) vₗ`, fixed fields `vₗ` with scalar coefficients that solve the
correction ODE `a' = M a - F_ext` exactly for all times (Part II (3.21), (3.33)), and stop the
numerical part at `T`. With a block field `F` for `Ŵ⁽¹⁾` this is the corrected field
`U(t) = F(t) + ∑ₗ aₗ(t) vₗ` (`BlockField.corrected`), the `raw` plus `tail` of a mode. The
triangular system (3.21) is diagonal in `ã₁ = a₁ + κ a₂` (3.32), and
`a₁ v₁ + a₂ v₂ = ã₁ v₁ + a₂ (v₂ - κ v₁)` (`smul_add_smul_eq_triangular`): the corrected field is
written with the diagonal coefficients, each of which solves its own scalar equation.

## Main definitions

* `BlockField.corrected`: the corrected field `U(t) = F(t) + ∑ₗ aₗ(t) vₗ`.
* `BlockField.correctedResidual`: the residual `π (∂ₜ U) - L U` of the corrected field.

## Main results

* `hasDerivWithJump_map_value`, `hasDerivWithJump_deriv_map_value`: the stopped block field is a
  primitive with the jump `-F(T⁻)`, with its piecewise derivative or with Lean's `deriv`.
* `hasDerivWithJump_map_corrected`, `hasDerivWithJump_deriv_map_corrected`: the corrected field
  is a primitive with the combined jump `F(T) - F(T⁻) + ∑ₗ Jₗ vₗ`; in Part II this is
  `-(Ŵ⁽¹⁾(T⁻) - D² Ŵ⁽¹⁾(T⁻)(0) ∘ χ_{·2})`, (3.36), and its cancellation is kept by bounding the
  combination as one element. `deriv_map_corrected`: off one finite set of times, independent of
  the linear map (so of the spatial point), Lean's `deriv` is the chosen derivative.
* `correctedResidual_eq_add`, `map_timeDeriv_sub_map_value_sub_sum_eq`,
  `lintegral_correctedResidual_le`: when the coefficients solve `aₗ' = cₗ aₗ - gₗ` with
  forcings `gₗ` that are scalar block fields on the blocks of `F` (in Part II,
  `F_i = D_i² (∂ₜ - 𝓛) Ŵ⁽¹⁾(0)` with coefficients `D_i² rₘⱼ(0)`), the residual of `U` on block `m`
  is `∑ⱼ bⱼ(τ) (rₘⱼ - ∑ₗ ρₘₗⱼ π vₗ) + ∑ₗ aₗ(t) (cₗ π vₗ - L vₗ)` and
  `∫ N(residual) ≤ ∑ₘ kₘ ∑ⱼ (∫|bⱼ|) N(rₘⱼ - ∑ₗ ρₘₗⱼ π vₗ) + ∑ₗ N(cₗ π vₗ - L vₗ) ∫ |aₗ|`. This is
  the residual for the whole operator `L`; Part II (3.24)-(3.29) further splits `L` into its
  numerical, nonlocal and profile-error parts (`I_{i,N}`, `I_{i,e}`, `I_{i,ē}`, `J₁`), which a
  consumer obtains by applying the theorem to each part. The corrections persist after the
  stopping time, where only the second sum remains.
* `hasDerivWithJump_stoppedDuhamel_value`, `hasDerivWithJump_deriv_stoppedDuhamel_value`,
  `lintegral_enorm_stoppedDuhamel_value_le`: the coefficient of a block-field forcing.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Sections 3.3-3.5,
  (3.21)-(3.36).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.SpaceTime

open Finset Set Filter MeasureTheory PDE.Analysis.Evolution
open scoped Topology ENNReal

variable {n r : ℕ} {B : TimeBasis n} {E E' G : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup E'] [Module ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace BlockField

variable {F : BlockField B E}

/-- The field, after a linear map `φ`, is interval integrable on every interval. -/
theorem intervalIntegrable_map_value (φ : E →ₗ[ℝ] G) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ φ (F.value t)) volume a b := by
  have h : (fun t ↦ φ (F.value t)) = ∑ m ∈ range F.count,
      (Set.Ico (F.start m) (F.start (m + 1))).indicator (fun s ↦ φ (F.blockValue m s)) := by
    funext t
    simp only [value, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    by_cases ht : F.start m ≤ t ∧ t < F.start (m + 1)
    · rw [ite_eq_left ht, indicator_of_mem (show t ∈ Set.Ico _ _ from ht)]
    · rw [ite_eq_right ht, map_zero, indicator_of_notMem (show t ∉ Set.Ico _ _ from ht)]
  rw [h]
  refine IntervalIntegrable.sum _ fun m _ ↦ ?_
  rw [intervalIntegrable_iff]
  exact ((F.continuous_map_blockValue φ m).integrableOn_uIcc.mono_set
    Set.uIoc_subset_uIcc).indicator measurableSet_Ico

/-- Off the block boundaries the field is continuous. -/
theorem continuousAt_map_value_of_notMem (hB : B.Sound) (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G)
    {t : ℝ} (ht : t ∉ F.start '' Set.Iic F.count) :
    ContinuousAt (fun s ↦ φ (F.value s)) t :=
  (hasDerivAt_value_of_notMem hB hF φ ht).continuousAt

variable [CompleteSpace G]

/-- **The stopped block field is a primitive with the jump `-F(T⁻)`.** -/
theorem hasDerivWithJump_map_value (hB : B.Sound) (hF : F.IsOrdered) (hc : F.IsContinuous)
    (hpos : 0 < F.count) (h₀ : F.start 0 = 0) (φ : E →ₗ[ℝ] G) :
    HasDerivWithJump (fun t ↦ φ (F.value t)) (fun t ↦ φ (F.timeDeriv t)) F.stop (φ F.jump) where
  integrableOn τ := F.integrableOn_map_timeDeriv φ 0 τ
  eq_add _ hτ := map_value_eq_add_integral_zero hB hF hc hpos h₀ φ hτ

/-- The same with Lean's `deriv` of `t ↦ φ (F.value t)` in place of the mapped `timeDeriv`. -/
theorem hasDerivWithJump_deriv_map_value (hB : B.Sound) (hF : F.IsOrdered)
    (hc : F.IsContinuous) (hpos : 0 < F.count) (h₀ : F.start 0 = 0) (φ : E →ₗ[ℝ] G) :
    HasDerivWithJump (fun t ↦ φ (F.value t)) (fun t ↦ deriv (fun s ↦ φ (F.value s)) t)
      F.stop (φ F.jump) :=
  (hasDerivWithJump_map_value hB hF hc hpos h₀ φ).congr_of_countable F.finite_start_image.countable
    fun _ _ ht ↦ (hasDerivAt_value_of_notMem hB hF φ ht).deriv.symm

/-! ### Corrected fields -/

/-- The corrected field `U(t) = F(t) + ∑ₗ aₗ(t) vₗ`. -/
noncomputable def corrected (F : BlockField B E) (a : Fin r → ℝ → ℝ) (v : Fin r → E) (t : ℝ) :
    E :=
  F.value t + ∑ l, a l t • v l

/-- The derivative `timeDeriv + ∑ₗ aₗ' vₗ` of the corrected field. -/
noncomputable def correctedDeriv (F : BlockField B E) (a' : Fin r → ℝ → ℝ) (v : Fin r → E)
    (t : ℝ) : E :=
  F.timeDeriv t + ∑ l, a' l t • v l

omit [CompleteSpace G] in
/-- A linear map `φ` applied to the corrected field is `φ(F(t)) + ∑ₗ aₗ(t) φ(vₗ)`. -/
theorem map_corrected (φ : E →ₗ[ℝ] G) (a : Fin r → ℝ → ℝ) (v : Fin r → E) (t : ℝ) :
    φ (F.corrected a v t) = φ (F.value t) + ∑ l, a l t • φ (v l) := by
  simp [corrected, map_add, map_sum, map_smul]

omit [CompleteSpace G] in
/-- A linear map `φ` applied to the derivative of the corrected field is
`φ(timeDeriv t) + ∑ₗ aₗ'(t) φ(vₗ)`. -/
theorem map_correctedDeriv (φ : E →ₗ[ℝ] G) (a' : Fin r → ℝ → ℝ) (v : Fin r → E) (t : ℝ) :
    φ (F.correctedDeriv a' v t) = φ (F.timeDeriv t) + ∑ l, a' l t • φ (v l) := by
  simp [correctedDeriv, map_add, map_sum, map_smul]

omit [CompleteSpace G] in
/-- `correctedDeriv` is the derivative of the corrected field at every time off the block
boundaries at which the coefficients have the derivatives `aₗ'`. -/
theorem hasDerivAt_map_corrected (hB : B.Sound) (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G)
    {a a' : Fin r → ℝ → ℝ} {t : ℝ} (ht : t ∉ F.start '' Set.Iic F.count)
    (hda : ∀ l, HasDerivAt (a l) (a' l t) t) (v : Fin r → E) :
    HasDerivAt (fun s ↦ φ (F.corrected a v s)) (φ (F.correctedDeriv a' v t)) t := by
  simp only [map_corrected, map_correctedDeriv]
  exact (hasDerivAt_value_of_notMem hB hF φ ht).add
    (HasDerivAt.fun_sum fun l _ ↦ (hda l).smul_const (φ (v l)))

omit [CompleteSpace G] in
/-- **Lean's derivative of the corrected field** is `correctedDeriv` at every time off the block
boundaries at which the coefficients have the derivatives `aₗ'`; the exceptional set does not
depend on `φ`. -/
theorem deriv_map_corrected (hB : B.Sound) (hF : F.IsOrdered) (φ : E →ₗ[ℝ] G)
    {a a' : Fin r → ℝ → ℝ} {t : ℝ} (htF : t ∉ F.start '' Set.Iic F.count)
    (hda : ∀ l, HasDerivAt (a l) (a' l t) t)
    (v : Fin r → E) :
    deriv (fun s ↦ φ (F.corrected a v s)) t = φ (F.correctedDeriv a' v t) :=
  (hasDerivAt_map_corrected hB hF φ htF hda v).deriv

/-- **The corrected field is a primitive with the combined jump** `F(T) - F(T⁻) + ∑ₗ Jₗ vₗ` when
every coefficient is a primitive with the jump `Jₗ` at the stopping time of `F`. -/
theorem hasDerivWithJump_map_corrected (hB : B.Sound) (hF : F.IsOrdered) (hc : F.IsContinuous)
    (hpos : 0 < F.count) (h₀ : F.start 0 = 0) (φ : E →ₗ[ℝ] G) {a a' : Fin r → ℝ → ℝ}
    {J : Fin r → ℝ} (ha : ∀ l, HasDerivWithJump (a l) (a' l) F.stop (J l)) (v : Fin r → E) :
    HasDerivWithJump (fun t ↦ φ (F.corrected a v t)) (fun t ↦ φ (F.correctedDeriv a' v t))
      F.stop (φ (F.jump + ∑ l, J l • v l)) := by
  have hsum := hasDerivWithJump_sum_smul Finset.univ (fun _ ↦ (1 : ℝ))
    (G := fun l t ↦ a l t • φ (v l)) (G' := fun l t ↦ a' l t • φ (v l))
    (J := fun l ↦ J l • φ (v l)) fun l _ ↦ (ha l).smul_const (φ (v l))
  simp only [one_smul] at hsum
  have h := (hasDerivWithJump_map_value hB hF hc hpos h₀ φ).add hsum
  simp only [← map_corrected, ← map_correctedDeriv] at h
  simpa [map_add, map_sum, map_smul] using h

/-- The corrected field with Lean's `deriv`, when the coefficients are differentiable with the
derivatives `aₗ'` at the positive times off a countable set `C`. -/
theorem hasDerivWithJump_deriv_map_corrected (hB : B.Sound) (hF : F.IsOrdered)
    (hc : F.IsContinuous) (hpos : 0 < F.count) (h₀ : F.start 0 = 0) (φ : E →ₗ[ℝ] G)
    {a a' : Fin r → ℝ → ℝ} {J : Fin r → ℝ} (ha : ∀ l, HasDerivWithJump (a l) (a' l) F.stop (J l))
    {C : Set ℝ} (hC : C.Countable) (hda : ∀ l t, 0 < t → t ∉ C → HasDerivAt (a l) (a' l t) t)
    (v : Fin r → E) :
    HasDerivWithJump (fun t ↦ φ (F.corrected a v t))
      (fun t ↦ deriv (fun s ↦ φ (F.corrected a v s)) t) F.stop
      (φ (F.jump + ∑ l, J l • v l)) := by
  refine (hasDerivWithJump_map_corrected hB hF hc hpos h₀ φ ha v).congr_of_countable
    (hC.union F.finite_start_image.countable) fun t ht htC ↦ ?_
  simp only [mem_union, not_or] at htC
  exact (deriv_map_corrected hB hF φ htC.2 (fun l ↦ hda l t ht htC.1) v).symm

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] in
/-- **The triangular correction with diagonal coefficients.** If `a₁ = ã₁ - κ a₂`, then
`a₁ v₁ + a₂ v₂ = ã₁ v₁ + a₂ (v₂ - κ v₁)`. -/
theorem smul_add_smul_eq_triangular {a₁ a₂ b₁ κ : ℝ} (h : a₁ = b₁ - κ * a₂) (v₁ v₂ : E) :
    a₁ • v₁ + a₂ • v₂ = b₁ • v₁ + a₂ • (v₂ - κ • v₁) := by
  subst h
  module

/-! ### The residual of a corrected field -/

/-- The residual `π (∂ₜ U) - L U` of the corrected field. -/
noncomputable def correctedResidual (π L : E →ₗ[ℝ] E') (F : BlockField B E)
    (a a' : Fin r → ℝ → ℝ) (v : Fin r → E) (t : ℝ) : E' :=
  π (F.correctedDeriv a' v t) - L (F.corrected a v t)

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] in
/-- The residual split into the block part and the corrections, for coefficients solving
`aₗ' = cₗ aₗ - gₗ`. -/
theorem correctedResidual_eq_add (π L : E →ₗ[ℝ] E') {a a' : Fin r → ℝ → ℝ} {c : Fin r → ℝ}
    {g : Fin r → ℝ → ℝ} (ha' : ∀ l t, a' l t = c l * a l t - g l t) (v : Fin r → E) (t : ℝ) :
    F.correctedResidual π L a a' v t =
      (π (F.timeDeriv t) - L (F.value t) - ∑ l, g l t • π (v l)) +
        ∑ l, a l t • (c l • π (v l) - L (v l)) := by
  simp only [correctedResidual, correctedDeriv, corrected, ha', map_add, map_sum, map_smul]
  have h : ∀ l, (c l * a l t - g l t) • π (v l) =
      -(g l t • π (v l)) + a l t • (c l • π (v l)) := fun l ↦ by module
  simp only [h, smul_sub, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  abel

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] in
/-- **The residual on a block in coefficient form.** If the forcings are scalar block fields
`g l` on the blocks of `F`, then on block `m` the residual without the correction terms is
`∑ⱼ bⱼ(τ) (rₘⱼ - ∑ₗ ρₘₗⱼ π vₗ)`. -/
theorem map_timeDeriv_sub_map_value_sub_sum_eq (hF : F.IsOrdered) (π L : E →ₗ[ℝ] E')
    {g : Fin r → BlockField B ℝ} (hg : ∀ l, (g l).start = F.start) (v : Fin r → E) {m : ℕ}
    (hm : m < F.count) {t : ℝ} (ht : t ∈ Ioo (F.start m) (F.start (m + 1)))
    (hgc : ∀ l, (g l).count = F.count) :
    π (F.timeDeriv t) - L (F.value t) - ∑ l, (g l).value t • π (v l) =
      ∑ j, B.eval j (F.localTime m t) •
        (F.residualCoeff π L m j - ∑ l, (g l).coeff m j • π (v l)) := by
  have hgF : ∀ l, (g l).IsOrdered := fun l k hk ↦ by
    rw [hg l]
    exact hF k (hgc l ▸ hk)
  have hloc : ∀ l, (g l).localTime m = F.localTime m := fun l ↦ by
    funext s
    simp [localTime, scale, hg l]
  have hgv : ∀ l, (g l).value t = ∑ j, B.eval j (F.localTime m t) * (g l).coeff m j := fun l ↦ by
    rw [value_eq (hgF l) (hgc l ▸ hm) (by rw [hg l]; exact ⟨ht.1.le, ht.2⟩), blockValue,
      hloc l]
    simp
  rw [timeDeriv_eq hF hm ht, value_eq hF hm ⟨ht.1.le, ht.2⟩,
    map_blockDeriv_sub_map_blockValue]
  simp only [hgv, Finset.sum_smul, smul_sub, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] in
/-- **The time integral of the residual of a corrected field.** -/
theorem lintegral_correctedResidual_le (hB : B.Sound) (hF : F.IsOrdered) (π L : E →ₗ[ℝ] E')
    {a a' : Fin r → ℝ → ℝ} {c : Fin r → ℝ} {g : Fin r → BlockField B ℝ}
    (hg : ∀ l, (g l).start = F.start) (hgc : ∀ l, (g l).count = F.count)
    (ha' : ∀ l t, a' l t = c l * a l t - (g l).value t) (v : Fin r → E) {N : E' → ℝ≥0∞}
    (h0 : N 0 = 0) (hadd : ∀ x y, N (x + y) ≤ N x + N y)
    (hsmul : ∀ (s : ℝ) x, N (s • x) ≤ ‖s‖ₑ * N x)
    (hmeas : ∀ l, AEMeasurable (a l) (volume.restrict (Ioi (F.start 0)))) :
    ∫⁻ t in Ioi (F.start 0), N (F.correctedResidual π L a a' v t) ≤
      ∑ m ∈ range F.count, ENNReal.ofReal (F.scale m) * ∑ j, ENNReal.ofReal (B.absIntegral j) *
          N (F.residualCoeff π L m j - ∑ l, (g l).coeff m j • π (v l)) +
        ∑ l, N (c l • π (v l) - L (v l)) * ∫⁻ t in Ioi (F.start 0), ‖a l t‖ₑ := by
  have hgF : ∀ l, (g l).IsOrdered := fun l k hk ↦ by
    rw [hg l]
    exact hF k (hgc l ▸ hk)
  simp only [correctedResidual_eq_add π L ha' v]
  refine (lintegral_add_sum_smul_le h0 hadd hsmul _ _ Finset.univ a (fun l _ ↦ hmeas l)
    _).trans (add_le_add ?_ le_rfl)
  refine lintegral_le_of_blocks hB hF (fun m hm t ht ↦ ?_) fun t ht ↦ ?_
  · rw [map_timeDeriv_sub_map_value_sub_sum_eq hF π L hg v hm ht hgc]
    exact le_sum_enorm_mul h0 hadd hsmul _ _ _
  · have hgs : ∀ l, (g l).value t = 0 := fun l ↦
      value_eq_zero_of_stop_le (hgF l) (by simp only [stop, hgc l, hg l]; exact ht.le)
    simp [timeDeriv_eq_zero_of_stop_le hF ht.le, value_eq_zero_of_stop_le hF ht.le, hgs, h0]

/-! ### Correction coefficients with block-field forcings -/

/-- With a forcing that is a scalar block field stopped at `T`, the derivative of the stopped
Duhamel solution is `c a - g`. -/
theorem stoppedDuhamelDeriv_value {g : BlockField B ℝ} (hg : g.IsOrdered) (c a₀ J t : ℝ) :
    stoppedDuhamelDeriv c a₀ g.stop J g.value t =
      c * stoppedDuhamel c a₀ g.stop J g.value t - g.value t := by
  rw [stoppedDuhamelDeriv]
  by_cases ht : t < g.stop
  · rw [ite_eq_left ht]
  · rw [ite_eq_right ht, value_eq_zero_of_stop_le hg (not_lt.1 ht)]

/-- A scalar block field is interval integrable on `[0, T]`. -/
theorem intervalIntegrable_value_stop {g : BlockField B ℝ} :
    IntervalIntegrable g.value volume 0 g.stop :=
  g.intervalIntegrable_map_value LinearMap.id 0 g.stop

/-- An ordered scalar block field over a sound basis is continuous at every time of `(0, T)` that is
not a block boundary. -/
theorem continuousAt_value_of_mem_Ioo_diff {g : BlockField B ℝ} (hB : B.Sound)
    (hg : g.IsOrdered) : ∀ t ∈ Ioo 0 g.stop \ (g.start '' Set.Iic g.count),
      ContinuousAt g.value t :=
  fun _ ht ↦ g.continuousAt_map_value_of_notMem hB hg LinearMap.id ht.2

/-- **The correction coefficient of a block-field forcing** `g` stopped at `T = g.stop > 0` is a
primitive with the jump `J` of `c a - g`. -/
theorem hasDerivWithJump_stoppedDuhamel_value {g : BlockField B ℝ} (hB : B.Sound)
    (hg : g.IsOrdered) (hT : 0 < g.stop) (c a₀ J : ℝ) :
    HasDerivWithJump (stoppedDuhamel c a₀ g.stop J g.value)
      (stoppedDuhamelDeriv c a₀ g.stop J g.value) g.stop J :=
  hasDerivWithJump_stoppedDuhamel hT intervalIntegrable_value_stop
    g.finite_start_image.countable (continuousAt_value_of_mem_Ioo_diff hB hg)

/-- The same with Lean's `deriv`. -/
theorem hasDerivWithJump_deriv_stoppedDuhamel_value {g : BlockField B ℝ} (hB : B.Sound)
    (hg : g.IsOrdered) (hT : 0 < g.stop) (c a₀ J : ℝ) :
    HasDerivWithJump (stoppedDuhamel c a₀ g.stop J g.value)
      (fun t ↦ deriv (stoppedDuhamel c a₀ g.stop J g.value) t) g.stop J :=
  hasDerivWithJump_deriv_stoppedDuhamel hT intervalIntegrable_value_stop
    g.finite_start_image.countable (continuousAt_value_of_mem_Ioo_diff hB hg)

/-- For `c < 0`, `∫₀^∞ |a| ≤ (|a(0)| + ∫₀^T |g| + |J|) / |c|`. -/
theorem lintegral_enorm_stoppedDuhamel_value_le {g : BlockField B ℝ} (hB : B.Sound)
    (hg : g.IsOrdered) (hT : 0 < g.stop) {c : ℝ} (hc : c < 0) (a₀ J : ℝ) :
    ∫⁻ t in Ioi 0, ‖stoppedDuhamel c a₀ g.stop J g.value t‖ₑ ≤
      ENNReal.ofReal ((|a₀| + (∫ s in (0 : ℝ)..g.stop, |g.value s|) + |J|) / -c) :=
  lintegral_enorm_stoppedDuhamel_le hc hT intervalIntegrable_value_stop
    g.finite_start_image.countable (continuousAt_value_of_mem_Ioo_diff hB hg)

end BlockField

end CAS.Numerics.SpaceTime
