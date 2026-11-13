/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
import Mathlib.Analysis.ODE.ExistUnique
import PDE.Analysis.Evolution.ODE.FiniteContinuation

/-!
# Gelfand Galerkin existence

On a finite-dimensional trial space `S` of a Gelfand triple `V ↪ H`, the projected equation

`⟪ι u'(t), ι v⟫_H + B(t)(u(t), v) = ℓ(t)(v)` for all `v ∈ S`

determines `u'(t)` uniquely, because the pivot mass form is positive definite on `S`.
Inverting the mass operator turns it into the affine ODE `u' = F(t, u)`. If `B` and `ℓ` are
continuous and bounded on `[a, b]`, Picard–Lindelöf on the cells of a fine arithmetic
partition gives local solutions that glue to a classical solution on all of `[a, b]`, for
every initial value. For a time-independent form and a continuous load, the affine linear
ODE theory gives the solution directly.
-/

@[expose] public section

noncomputable section


open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
section GelfandGalerkinMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Picard–Lindelöf for the nonautonomous Galerkin system on one interval: if
`‖M_S⁻¹‖ (M_ℓ + M_B (‖u₀‖ + R)) ≤ L` and `L (b - a) ≤ R`, there is a classical solution on
`[a, b]` with `u(a) = u₀`. -/
private theorem exists_gelfandGalerkin_nonauto_on_Icc_of_bounds
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell R L : NNReal)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (u₀ : S)
    (hL : ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ((Mell : ℝ) + (MB : ℝ) * (‖u₀‖ + (R : ℝ))) ≤ L)
    (htime : (L : ℝ) * (b - a) ≤ R) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (du t) (Set.Icc a b) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          B t (u t : V) (v : V) = ell t (v : V)) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  have hPL : IsPicardLindelof (gelfandGalerkinVectorField T S B ell)
      (tmin := a) (tmax := b) ⟨a, le_rfl, hab⟩ u₀ R 0 L
      (gelfandGalerkinLipschitzBound T S MB) := by
    refine ⟨fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x _ y _ ↦ ?_,
      fun x _ ↦ continuousOn_gelfandGalerkinVectorField T S hBcont hellcont continuousOn_const,
      fun t ht x hx ↦ ?_, ?_⟩
    · rw [dist_eq_norm, dist_eq_norm]
      calc _ ≤ ‖gelfandGalerkinOperator T S (B t)‖ * ‖x - y‖ :=
            norm_gelfandGalerkinVectorField_sub_le T S B ell t x y
        _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * (MB : ℝ) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right ((norm_gelfandGalerkinOperator_le T S (B t)).trans
            (mul_le_mul_of_nonneg_left (hBnorm t ht) (by positivity))) (norm_nonneg _)
    · have hx := norm_le_of_mem_closedBall hx
      have := hellnorm t ht
      have := hBnorm t ht
      refine (norm_gelfandGalerkinVectorField_le T S B ell t x).trans (le_trans ?_ hL)
      gcongr
    · simpa [max_eq_left (sub_nonneg.mpr hab)] using htime
  obtain ⟨u, hu₀, hu⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨u, fun t ↦ gelfandGalerkinVectorField T S B ell t (u t), hu₀, hu,
    continuousOn_gelfandGalerkinVectorField T S hBcont hellcont (HasDerivWithinAt.continuousOn hu),
    fun t _ v ↦ gelfandGalerkinVectorField_equation T S B ell t (u t) v⟩

/-- If `d ∈ S` satisfies `⟪ι d, ι v⟫_H + B(t)(u, v) = ℓ(t)(v)` for every `v ∈ S`, then
`d` is the mass-inverted vector field `F(t, u)`. -/
theorem gelfandGalerkin_derivative_eq_vectorField
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u d : S)
    (hd : ∀ v : S,
      inner ℝ (T.inclusion (d : V)) (T.inclusion (v : V)) +
        B t (u : V) (v : V) = ell t (v : V)) :
    d = gelfandGalerkinVectorField T S B ell t u := by
  let z : S := d - gelfandGalerkinVectorField T S B ell t u
  have hzH : T.inclusion (z : V) = 0 := inner_self_eq_zero.mp <| by
    change inner ℝ (T.inclusion ((d - gelfandGalerkinVectorField T S B ell t u : S) : V))
      (T.inclusion (z : V)) = 0
    simp only [Submodule.coe_sub, map_sub, inner_sub_left]
    linarith [hd z, gelfandGalerkinVectorField_equation T S B ell t u z]
  exact sub_eq_zero.mp (Subtype.ext (T.injective (hzH.trans (map_zero _).symm)))

/--
Galerkin existence on a finite interval. If `B` and `ℓ` are continuous on `[a, b]` with
`‖B(t)‖ ≤ MB` and `‖ℓ(t)‖ ≤ Mell`, then for every `u₀ ∈ S` the nonautonomous Galerkin system
has a classical solution on `[a, b]` with `u(a) = u₀`, continuous derivative, and the
projected equation at every time.

For the proof, write `q` for the norm of the inverse trial mass map. The vector field has
affine growth

`‖F(t,x)‖ ≤ q * Mell + (q * MB) * ‖x‖`.

Choose a finite arithmetic partition whose cell length `d` satisfies
`d * (q * Mell) ≤ 1/4` and `d * (q * MB) ≤ 1/4`.  At a cell beginning at
`x`, use Picard radius `R = 1 + ‖x‖` and the corresponding affine speed
bound.  The two quarter bounds imply `L*d ≤ R`, independently of `x`.
Consequently every endpoint can be continued for one more cell, and
`exists_ode_solution_Icc_of_partition` glues the finitely many solutions.
-/
theorem exists_gelfandGalerkin_nonauto_on_Icc
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (u₀ : S) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (du t) (Set.Icc a b) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          B t (u t : V) (v : V) = ell t (v : V)) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  let q : ℝ := ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖
  have hq : 0 ≤ q := norm_nonneg ((trialMassEquiv T S).symm.toContinuousLinearMap : S →L[ℝ] S)
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  -- a partition of `[a, b]` into `N` cells of length `d`, with `d q Mell, d q MB ≤ 1/4`
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (1 + 4 * (1 + q * Mell + q * MB) * (b - a))
  have hbase : 0 ≤ 4 * (1 + q * Mell + q * MB) * (b - a) := by positivity
  have hNreal : 0 < (N : ℝ) := by linarith
  let d : ℝ := (b - a) / N
  have hd : 0 ≤ d := div_nonneg hlen hNreal.le
  have hNd : (N : ℝ) * d = b - a := by
    dsimp only [d]
    field_simp
  have hdm : d * (q * Mell) ≤ 1 / 4 := by
    dsimp only [d]
    rw [div_mul_eq_mul_div, div_le_iff₀ hNreal]
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + q * MB) hlen]
  have hdk : d * (q * MB) ≤ 1 / 4 := by
    dsimp only [d]
    rw [div_mul_eq_mul_div, div_le_iff₀ hNreal]
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + q * Mell) hlen]
  obtain ⟨u, hu₀, hu⟩ := exists_ode_solution_Icc_of_partition
    (gelfandGalerkinVectorField T S B ell) hd N (Nat.cast_pos.mp hNreal)
    (by rw [hNd]; ring : a + (N : ℝ) * d = b) u₀ fun n hn x ↦ by
      -- on each cell, Picard radius `R = 1 + ‖x‖` and the affine speed bound `L`
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hn
      have hsub : Icc (a + n * d) (a + ((n + 1 : ℕ) : ℝ) * d) ⊆ Icc a b :=
        Icc_subset_Icc (le_add_of_nonneg_right (mul_nonneg n.cast_nonneg hd))
          (by linarith [mul_le_mul_of_nonneg_right hn' hd])
      let R : NNReal := ⟨1 + ‖x‖, by positivity⟩
      let L : NNReal := ⟨q * ((Mell : ℝ) + (MB : ℝ) * (‖x‖ + (R : ℝ))), by positivity⟩
      have htime : (L : ℝ) * (a + ((n + 1 : ℕ) : ℝ) * d - (a + n * d)) ≤ R := by
        change q * ((Mell : ℝ) + (MB : ℝ) * (‖x‖ + (1 + ‖x‖))) *
          (a + ((n + 1 : ℕ) : ℝ) * d - (a + n * d)) ≤ 1 + ‖x‖
        push_cast
        linarith [norm_nonneg x, mul_le_mul_of_nonneg_right hdk
          (by positivity : (0 : ℝ) ≤ ‖x‖ + (1 + ‖x‖))]
      obtain ⟨u, du, hu₀, hdu, -, heq⟩ := exists_gelfandGalerkin_nonauto_on_Icc_of_bounds
        T S B ell (by push_cast; linarith) (hBcont.mono hsub) (hellcont.mono hsub) MB Mell R L
        (fun t ht ↦ hBnorm t (hsub ht)) (fun t ht ↦ hellnorm t (hsub ht)) x le_rfl htime
      exact ⟨u, hu₀, fun t ht ↦ (hdu t ht).congr_deriv
        (gelfandGalerkin_derivative_eq_vectorField T S B ell t (u t) (du t) (heq t ht))⟩
  exact ⟨u, fun t ↦ gelfandGalerkinVectorField T S B ell t (u t), hu₀, hu,
    continuousOn_gelfandGalerkinVectorField T S hBcont hellcont (HasDerivWithinAt.continuousOn hu),
    fun t _ v ↦ gelfandGalerkinVectorField_equation T S B ell t (u t) v⟩

/-- For a time-independent form `B` and a load `ℓ` continuous on `[a, b]`, the Galerkin
system on `S` has a solution on `[a, b]` with `u(a) = u₀`, a derivative at every time of
`[a, b]`, and the projected equation `⟪ι u'(t), ι v⟫_H + B(u(t), v) = ℓ(t)(v)`. -/
theorem exists_gelfandGalerkin_on_Icc
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b) (hell : ContinuousOn ell (Set.Icc a b))
    (u₀ : S) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b, HasDerivAt u (du t) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          B (u t : V) (v : V) = ell t (v : V)) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  obtain ⟨u, hu₀, hu⟩ := exists_affineLinearEvolution_on_Icc (gelfandGalerkinOperator T S B)
    (gelfandGalerkinForcing T S ell) hab
    ((trialMassEquiv T S).symm.continuous.comp_continuousOn
      ((InnerProductSpace.toDual ℝ S).symm.continuous.comp_continuousOn
        (continuousOn_restrictFunctional S hell))) ⟨a, le_rfl, hab⟩ u₀
  have hdu (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt u (gelfandGalerkinVectorField T S (fun _ ↦ B) ell t (u t)) t := by
    simpa [gelfandGalerkinVectorField, gelfandGalerkinForcing, gelfandGalerkinOperator, map_sub]
      using hu t ht
  exact ⟨u, _, hu₀, hdu, continuousOn_gelfandGalerkinVectorField T S continuousOn_const hell
      fun t ht ↦ (hdu t ht).continuousAt.continuousWithinAt,
    fun t _ v ↦ gelfandVectorField_equation T S B (ell t) (u t) v⟩

end GelfandGalerkinMass

end Galerkin

end PDE.Analysis.Evolution
