/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Rearrangement.DifferenceEnergy
public import PDE.Analysis.Rearrangement.Symmetrization
import Mathlib.Analysis.Convex.Continuous
import PDE.Analysis.Convex.Real.TwoPoint

/-!
# The Pólya–Szegő inequality

Making a function radial and nonincreasing, without changing its distribution, does not raise
its Dirichlet energy `∫ |∇u|^p`. We prove it for every nonnegative Lipschitz function `u` with
compact support on a finite-dimensional real inner product space and every `p ≥ 1`:
there is a radial nonincreasing `v` with the same Lipschitz constant, bound and support radius,
with `∫ g (v)⁺ = ∫ g (u)⁺` for every continuous `g` with `g 0 = 0`, and with
`∫ |∇v|^p ≤ ∫ |∇u|^p`. On a nontrivial space `v` is the symmetric decreasing rearrangement of
`u` (`ofReal_eq_symmDecr`). The inequality for functions of `W^{1,p}` is not stated here. The
sharp Sobolev inequality needs only the Lipschitz case. It is proved from
`exists_radial_lintegral_fderiv_le` and Bliss's inequality, and reaches Sobolev functions by
density (`SobolevSpace.Inequalities.eLpNorm_le_sharpSobolevConstant_mul_eLpNorm_fderiv`).

## Main results

* `Polarized.lintegral_comp_eq`, `Polarized.diffEnergy_le`: finitely many polarizations of a
  measurable function preserve its distribution and do not raise its difference energy.
* `lintegral_comp_eq_of_mem_closure`, `diffEnergy_le_of_mem_closure`: the same for pointwise
  limits of iterated polarizations of a function of the Lipschitz class.
* `exists_radial_lintegral_fderiv_le`: the Pólya–Szegő inequality. Here `∇` is the Fréchet
  derivative, which exists almost everywhere.

## How it works

`exists_radial_antitone` gives a radial nonincreasing `v` that is a uniform limit of iterated
polarizations `w_k` of `u`. For a continuous `g` with `g 0 = 0`, each `∫ g (w_k)` equals
`∫ g (u)`, because polarization is a rearrangement (`lintegral_comp_polarize`). The `w_k` are
bounded and vanish outside one ball, so dominated convergence gives `∫ g (v) = ∫ g (u)`. For a
convex cost `j ≥ 0` each difference energy of `w_k` is at most that of `u`
(`diffEnergy_polarize_le`), and Fatou's lemma gives the same for `v`. With the cost
`s ↦ |c s|^p` at the scale `1 / c`, the difference energies of `u` and of `v` are `c⁻ⁿ` times
integrals that converge, as `c → ∞`, to one constant times `∫ |∇u|^p` and `∫ |∇v|^p`
(`diffEnergy_eq_smul`, `tendsto_lintegral_diffQuotient`). The inequality passes to the limit.

## References

* G. Pólya and G. Szegő, *Isoperimetric Inequalities in Mathematical Physics*, Annals of
  Mathematics Studies 27, Princeton University Press, 1951: the inequality.
* F. Brock and A. Yu. Solynin, "An approach to symmetrization via polarization",
  *Trans. Amer. Math. Soc.* 352 (2000), 1759-1796: the rearrangement as a limit of iterated
  polarizations. <https://doi.org/10.1090/S0002-9947-99-02558-1>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped ENNReal NNReal Topology

namespace PDE.Analysis.Rearrangement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {L : ℝ≥0} {R M : ℝ} {u v w : E → ℝ}

/-! ## Finitely many polarizations -/

omit [FiniteDimensional ℝ E] in
/-- The iterated polarizations of a measurable function are measurable. -/
theorem Polarized.measurable (hu : Measurable u) (h : Polarized u w) : Measurable w := by
  induction h with
  | refl => exact hu
  | step a _ ih => exact ih.polarize a

/-- Iterated polarizations of a measurable function are rearrangements:
`∫ ψ (w x) dx = ∫ ψ (u x) dx` for every measurable `ψ`. -/
theorem Polarized.lintegral_comp_eq (hu : Measurable u) (h : Polarized u w) {ψ : ℝ → ℝ≥0∞}
    (hψ : Measurable ψ) : ∫⁻ x, ψ (w x) = ∫⁻ x, ψ (u x) := by
  induction h with
  | refl => rfl
  | step a hw ih => rw [lintegral_comp_polarize a (hw.measurable hu) hψ, ih]

/-- Iterated polarizations of a measurable function do not increase the difference energy with
a convex cost. -/
theorem Polarized.diffEnergy_le (hu : Measurable u) (h : Polarized u w) {j : ℝ → ℝ}
    (hj : ConvexOn ℝ univ j) (hj0 : ∀ s, 0 ≤ j s) (t : ℝ) :
    diffEnergy j t w ≤ diffEnergy j t u := by
  induction h with
  | refl => exact le_rfl
  | step a hw ih => exact (diffEnergy_polarize_le hj hj0 t a (hw.measurable hu)).trans ih

/-! ## Limits of iterated polarizations -/

/-- **The limit has the distribution of `u`.** For a pointwise limit `v` of iterated
polarizations of `u` and a continuous `g` with `g 0 = 0`, `∫ g (v x) dx = ∫ g (u x) dx`, where
negative values of `g` count as `0`. -/
theorem lintegral_comp_eq_of_mem_closure (hu : u ∈ lipClass L R M)
    (hv : v ∈ closure {w | Polarized u w}) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : g 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (g (v x)) = ∫⁻ x, ENNReal.ofReal (g (u x)) := by
  obtain ⟨w, hw, hwv⟩ := exists_seq_polarized_tendsto hu hv
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc 0 M))
  have hlim : Tendsto (fun k ↦ ∫⁻ x, ENNReal.ofReal (g (w k x))) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (g (v x)))) := by
    refine tendsto_lintegral_of_dominated_convergence
      ((closedBall (0 : E) R).indicator fun _ ↦ ENNReal.ofReal C)
      (fun k ↦ (ENNReal.continuous_ofReal.comp
        (hg.comp ((hw k).mem_lipClass hu).1.continuous)).measurable)
      (fun k ↦ Eventually.of_forall fun x ↦ ?_) ?_ (Eventually.of_forall fun x ↦ ?_)
    · have hk := (hw k).mem_lipClass hu
      change ENNReal.ofReal (g (w k x)) ≤ _
      by_cases hx : x ∈ closedBall (0 : E) R
      · rw [indicator_of_mem hx]
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC _ (hk.2.1 x)))
      · rw [indicator_of_notMem hx, hk.2.2 x (by simpa using hx), hg0, ENNReal.ofReal_zero]
    · rw [lintegral_indicator_const measurableSet_closedBall]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
    · exact (ENNReal.continuous_ofReal.tendsto _).comp ((hg.tendsto _).comp (hwv x))
  have hconst (k : ℕ) : ∫⁻ x, ENNReal.ofReal (g (w k x)) = ∫⁻ x, ENNReal.ofReal (g (u x)) :=
    (hw k).lintegral_comp_eq hu.1.continuous.measurable (ψ := fun s ↦ ENNReal.ofReal (g s))
      (ENNReal.measurable_ofReal.comp hg.measurable)
  simp only [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm

/-- **The limit has at most the difference energy of `u`**, for every convex cost `j ≥ 0` and
every scale, by Fatou's lemma. -/
theorem diffEnergy_le_of_mem_closure (hu : u ∈ lipClass L R M)
    (hv : v ∈ closure {w | Polarized u w}) {j : ℝ → ℝ} (hj : ConvexOn ℝ univ j)
    (hj0 : ∀ s, 0 ≤ j s) (t : ℝ) : diffEnergy j t v ≤ diffEnergy j t u := by
  obtain ⟨w, hw, hpt⟩ := exists_seq_polarized_tendsto hu hv
  have hjc : Continuous j := continuousOn_univ.mp (hj.continuousOn isOpen_univ)
  have hne (x y : E) : nearWeight t x y ≠ ∞ := by
    unfold nearWeight
    split_ifs <;> simp
  calc diffEnergy j t v
      = ∫⁻ z : E × E, liminf (fun k ↦ nearWeight t z.1 z.2 *
          ENNReal.ofReal (j (w k z.1 - w k z.2))) atTop ∂((volume : Measure E).prod volume) := by
        refine lintegral_congr fun z ↦ ?_
        have h : Tendsto (fun k ↦ nearWeight t z.1 z.2 * ENNReal.ofReal (j (w k z.1 - w k z.2)))
            atTop (𝓝 (nearWeight t z.1 z.2 * ENNReal.ofReal (j (v z.1 - v z.2)))) :=
          ENNReal.Tendsto.const_mul ((ENNReal.continuous_ofReal.tendsto _).comp
            ((hjc.tendsto _).comp ((hpt z.1).sub (hpt z.2)))) (Or.inr (hne _ _))
        exact h.liminf_eq.symm
    _ ≤ liminf (fun k ↦ diffEnergy j t (w k)) atTop :=
        lintegral_liminf_le fun k ↦ measurable_diffEnergy_integrand hjc.measurable t
          ((hw k).mem_lipClass hu).1.continuous.measurable
    _ ≤ liminf (fun _ : ℕ ↦ diffEnergy j t u) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k ↦
          (hw k).diffEnergy_le hu.1.continuous.measurable hj hj0 t)
    _ = diffEnergy j t u := liminf_const _

/-! ## The inequality -/

/-- **The Pólya–Szegő inequality.** Let `u` be `L`-Lipschitz on a finite-dimensional real
inner product space, with values in `[0, M]`, and zero outside the closed ball of radius `R`.
Then there is a function `v` with the same three properties such that

* `v y ≤ v x` whenever `|x| ≤ |y|` (so `v` is radial and nonincreasing in `|x|`);
* `∫ g (v x)⁺ dx = ∫ g (u x)⁺ dx` for every continuous `g` with `g 0 = 0`, where the positive
  part means that negative values of `g` count as `0`;
* `∫ ‖∇v‖^p ≤ ∫ ‖∇u‖^p` for every `p ≥ 1`.

The function `v` is a limit of iterated polarizations of `u`. On a nontrivial space it is the
symmetric decreasing rearrangement of `u` (`ofReal_eq_symmDecr`). The gradient energies are
compared through the difference energies, which polarization does not increase and which
converge to the gradient energies. -/
theorem exists_radial_lintegral_fderiv_le (hu : u ∈ lipClass L R M) :
    ∃ v ∈ lipClass (E := E) L R M, (∀ x y : E, ‖x‖ ≤ ‖y‖ → v y ≤ v x) ∧
      (∀ g : ℝ → ℝ, Continuous g → g 0 = 0 →
        ∫⁻ x, ENNReal.ofReal (g (v x)) = ∫⁻ x, ENNReal.ofReal (g (u x))) ∧
      ∀ p : ℝ, 1 ≤ p → ∫⁻ x, ‖fderiv ℝ v x‖ₑ ^ p ≤ ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ p := by
  obtain ⟨v, hv, hrad⟩ := exists_radial_antitone hu
  have hvK := mem_lipClass_of_mem_closure hu hv
  refine ⟨v, hvK, hrad, fun g hg hg0 ↦ lintegral_comp_eq_of_mem_closure hu hv hg hg0,
    fun p hp ↦ ?_⟩
  have hp0 : 0 < p := by linarith
  obtain ⟨c, hc0, hctop, hc⟩ := exists_lintegral_closedBall_abs_rpow_eq (E := E) hp0
  -- the scaled difference energies converge to `c ∫ ‖∇w‖^p`
  have hlim {w : E → ℝ} (hw : w ∈ lipClass L R M) :
      Tendsto (fun k : ℕ ↦ ∫⁻ x, ∫⁻ z in closedBall (0 : E) 1,
          ENNReal.ofReal (|((k : ℝ) + 1) * (w x - w (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p)) atTop
        (𝓝 (c * ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p)) := by
    have h := tendsto_lintegral_diffQuotient hw.1 hw.2.2 hp0
    have e : ∫⁻ x, ∫⁻ z in closedBall (0 : E) 1, ENNReal.ofReal (|fderiv ℝ w x z| ^ p) =
        c * ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p := by
      rw [← lintegral_const_mul' _ _ hctop]
      refine lintegral_congr fun x ↦ ?_
      rw [hc, ← ofReal_norm (fderiv ℝ w x),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (fderiv ℝ w x)) hp0.le]
    rwa [e] at h
  -- at each scale the energy of `v` is at most that of `u`
  have hle (k : ℕ) : ∫⁻ x, ∫⁻ z in closedBall (0 : E) 1,
        ENNReal.ofReal (|((k : ℝ) + 1) * (v x - v (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p) ≤
      ∫⁻ x, ∫⁻ z in closedBall (0 : E) 1,
        ENNReal.ofReal (|((k : ℝ) + 1) * (u x - u (x + ((k : ℝ) + 1)⁻¹ • z))| ^ p) := by
    have hk : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    have hjm : Measurable fun s : ℝ ↦ |((k : ℝ) + 1) * s| ^ p :=
      ((continuous_const.mul continuous_id).abs.rpow_const fun _ ↦ Or.inr hp0.le).measurable
    have h := diffEnergy_le_of_mem_closure hu hv (Real.convexOn_abs_mul_rpow ((k : ℝ) + 1) hp)
      (fun s ↦ Real.rpow_nonneg (abs_nonneg _) p) ((k : ℝ) + 1)⁻¹
    rw [diffEnergy_eq_smul hjm hk hvK.1.continuous.measurable,
      diffEnergy_eq_smul hjm hk hu.1.continuous.measurable] at h
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (pow_pos hk _)).ne'
      ENNReal.ofReal_ne_top).mp h
  exact (ENNReal.mul_le_mul_iff_right hc0 hctop).mp
    (le_of_tendsto_of_tendsto' (hlim hvK) (hlim hu) hle)

end PDE.Analysis.Rearrangement
