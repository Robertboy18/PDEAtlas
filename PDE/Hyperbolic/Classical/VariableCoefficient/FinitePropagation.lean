/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Energy.Vanishing
public import PDE.Analysis.Calculus.Eikonal.Properness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite propagation for variable nondivergence waves

The coefficients are autonomous symmetric `C¹` matrix entries with a
uniform lower ellipticity bound. The eikonal function is continuous, `C¹`
off its center, and has compact closed sublevels for radii `0 < r < T`. These geometric
hypotheses do not involve the solution.

The proof derives weighted energy decay, its zero initial limit, Grönwall,
and pointwise vanishing from the classical equation. The resulting
cone includes its positive-time lateral boundary and terminal vertex.

This follows Evans, §7.2.4, Theorem 8, with compactness of the eikonal sublevels as a hypothesis.
The last theorem derives that compactness from an at-most-quadratic upper bound on the principal
matrix, using the eikonal equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.4, equations (75)-(76), Theorem 8 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology

variable {n : ℕ}

/-- Zero initial data force the time derivative to vanish inside each eikonal cone. -/
theorem time_derivative_eq_zero_on_compact_sublevels {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {q : ℝ^n → ℝ}
    (hq : Continuous q) (hqnonneg : ∀ x, 0 ≤ q x) (hqd : ∀ x, q x ≠ 0 → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, q x ≠ 0 → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {T : ℝ}
    (hK : ∀ r ∈ Ioo 0 T, IsCompact {x | q x ≤ r}) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hpde : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hpos : ∀ x, q x < T → u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x, q x < T → derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) {t : ℝ}
    (ht : 0 < t) {x : ℝ^n} (hx : q x < T - t) :
    (∂[0] u) (timeSpaceCons t x) = 0 := by
  obtain ⟨r, hxr, hrT⟩ := exists_between (show q x + t < T by linarith)
  have htr : t < r := (le_add_of_nonneg_left (hqnonneg x)).trans_lt hxr
  let ε := (r - t) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr htr)
  have htε : t ∈ Ioo 0 (r - ε) := ⟨ht, by dsimp [ε]; linarith⟩
  have hKr := hK r ⟨ht.trans htr, hrT⟩
  have henergy := weighted_energy_eq_zero ha hsymm hθ hell hq hqd heik hrT hε hKr
    hu hu₀ hpde hpos hvel htε
  have hup (y : ℝ^n) : ContDiffAt ℝ 2 u (timeSpaceCons t y) :=
    hu.contDiffAt ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
      (by simpa using ht))
  have hzero := energyDensity_eq_zero_of_weighted_energy_eq_zero ha
    (quadratic_nonneg_of_elliptic hθ hell) hq hε ht hKr hup henergy
      (x := x) (by linarith)
  exact time_derivative_eq_zero_of_energyDensity_eq_zero
    (quadratic_nonneg_of_elliptic hθ hell) hzero

/-- Full pointwise finite propagation on compact eikonal sublevels, including positive-time
lateral boundary points. Every energy and initial-limit step is proved from the data. -/
theorem finite_propagation_on_compact_sublevels {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {q : ℝ^n → ℝ}
    (hq : Continuous q) (hqnonneg : ∀ x, 0 ≤ q x) (hqd : ∀ x, q x ≠ 0 → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, q x ≠ 0 → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {T : ℝ}
    (hK : ∀ r ∈ Ioo 0 T, IsCompact {x | q x ≤ r}) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hpde : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hpos : ∀ x, q x < T → u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x, q x < T → derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) {t : ℝ}
    (ht : 0 < t) {x : ℝ^n} (hx : q x ≤ T - t) :
    u (timeSpaceCons t x) = 0 := by
  let path : ℝ → ℝ := fun s ↦ u (timeSpaceCons s x)
  have hline : Continuous (fun s ↦ timeSpaceCons (n := n) s x) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hc : ContinuousOn path (Icc 0 t) :=
    hu₀.continuousOn.comp hline.continuousOn (fun _ hs ↦ by simpa using hs.1)
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt path 0 s := by
    intro s hs
    have hxs : q x < T - s := hx.trans_lt (sub_lt_sub_left hs.2 T)
    have hz := time_derivative_eq_zero_on_compact_sublevels ha hsymm hθ hell
      hq hqnonneg hqd heik hK hu hu₀ hpde hpos hvel hs.1 hxs
    have hup : ContDiffAt ℝ 2 u (timeSpaceCons s x) :=
      hu.contDiffAt ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
        (by simpa using hs.1))
    exact (PDE.hasDerivAt_timeSpaceCons u s x
      (hup.differentiableAt (by norm_num))).congr_deriv hz
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le hc hd
    (IntervalIntegrable.zero : IntervalIntegrable (0 : ℝ → ℝ) volume 0 t)
  have heq : path t = path 0 := sub_eq_zero.mp (by simpa using hFTC.symm)
  exact heq.trans (hpos x (hx.trans_lt (sub_lt_self T ht)))

/-- The entire eikonal cone and its terminal vertex for variable principal coefficients.
Continuity and compact inner sublevels are explicit additional geometric hypotheses. -/
theorem finite_propagation_eikonal_cone {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {q : ℝ^n → ℝ}
    {c : ℝ^n} (hq : Continuous q) (hqc : q c = 0) (hqpos : ∀ x, x ≠ c → 0 < q x)
    (hqd : ∀ x, x ≠ c → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, x ≠ c → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {T : ℝ} (hT : 0 < T)
    (hK : ∀ r ∈ Ioo 0 T, IsCompact {x | q x ≤ r}) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hpde : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hpos : ∀ x, q x < T → u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x, q x < T → derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    (∀ t ∈ Ico 0 T, ∀ x, q x < T - t → u (timeSpaceCons t x) = 0) ∧ u (timeSpaceCons T c) = 0 := by
  have hqnonneg (x : ℝ^n) : 0 ≤ q x := by
    by_cases hx : x = c
    · simp [hx, hqc]
    · exact (hqpos x hx).le
  have hc (x : ℝ^n) (hx : q x ≠ 0) : x ≠ c := by
    rintro rfl
    exact hx hqc
  have hvanish {t : ℝ} (ht : 0 < t) {x : ℝ^n} (hx : q x ≤ T - t) : u (timeSpaceCons t x) = 0 :=
    finite_propagation_on_compact_sublevels ha hsymm hθ hell
      hq hqnonneg (fun x hx ↦ hqd x (hc x hx)) (fun x hx ↦ heik x (hc x hx))
      hK hu hu₀ hpde hpos hvel ht hx
  constructor
  · intro t ht x hx
    rcases ht.1.eq_or_lt with ht0 | ht0
    · subst t
      exact hpos x (by simpa using hx)
    · exact hvanish ht0 hx.le
  · exact hvanish hT (by simp [hqc])

/-- At-most-quadratic growth of the principal matrix implies finite propagation on the
entire eikonal cone and at its terminal vertex. Compactness of its inner sublevels is
derived from the matrix bound and eikonal identity. -/
theorem finite_propagation_of_quadratic_growth {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (hsymm : ∀ x i j, a x i j = a x j i) {θ : ℝ}
    (hθ : 0 < θ) (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) {C : ℝ}
    (hC : 0 < C) {c : ℝ^n}
    (hupper : ∀ x (v : ℝ^n), (∑ i, ∑ j, a x i j * v i * v j) ≤ C ^ 2 * (1 + ‖x - c‖ ^ 2) * ‖v‖ ^ 2)
    {q : ℝ^n → ℝ} (hq : Continuous q) (hqc : q c = 0) (hqpos : ∀ x, x ≠ c → 0 < q x)
    (hqd : ∀ x, x ≠ c → ContDiffAt ℝ 1 q x)
    (heik : ∀ x, x ≠ c → ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1) {T : ℝ} (hT : 0 < T)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hpde : ∀ t : ℝ, 0 < t → ∀ x, q x < T - t → waveOperator a u (timeSpaceCons t x) = 0)
    (hpos : ∀ x, q x < T → u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x, q x < T → derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    (∀ t ∈ Ico 0 T, ∀ x, q x < T - t → u (timeSpaceCons t x) = 0) ∧ u (timeSpaceCons T c) = 0 :=
  finite_propagation_eikonal_cone ha hsymm hθ hell hq hqc hqpos hqd heik hT
    (fun r _ ↦ Eikonal.isCompact_sublevel_of_matrix_eikonal hC hupper hq hqc hqpos
      (fun x hx ↦ (hqd x hx).differentiableAt_one) heik r) hu hu₀ hpde hpos hvel

end WaveEquation.VariableCoefficient
