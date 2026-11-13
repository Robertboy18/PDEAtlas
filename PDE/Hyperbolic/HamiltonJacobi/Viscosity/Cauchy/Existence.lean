/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Cauchy.Modulus
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.Construction
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialComparison

/-!
# Whole-space nonconvex Hamilton–Jacobi Cauchy existence

Perron's method constructs a solution for bounded Lipschitz initial data and
an autonomous continuous Hamiltonian bounded on the ball of possible spatial
gradients. The barriers and translation estimates supply continuity and the
initial trace. A Lipschitz extension gives an everywhere-defined representative;
the equation and uniqueness concern nonnegative time.

For a globally Lipschitz Hamiltonian the barrier speed is explicitly
`|H 0| + Lip(H) * Lip(g)`. The Hamiltonian need not be convex. Compactness of the
gradient ball also gives existence for every continuous autonomous Hamiltonian, with
Lipschitz initial data.

Ishii introduced Perron's method for viscosity solutions of Hamilton–Jacobi equations. The
solution is the maximal subsolution of Theorem 4.1 in Crandall, Ishii and Lions, between the
barriers `g ± C t`. Its continuity comes from the translation estimates, not from comparison.

## References

* H. Ishii, *Perron's method for Hamilton-Jacobi equations*, Duke Math. J. 55 (1987), 369-384.
  <https://doi.org/10.1215/S0012-7094-87-05521-9>
* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992), 1-67, §4, Theorem 4.1.
  <https://doi.org/10.1090/S0273-0979-1992-00266-5>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Cauchy

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Perron existence with an explicit bound for the Hamiltonian on the ball
of test gradients. The resulting function is globally Lipschitz, solves the
equation at positive times, and attains the datum with a uniform linear rate. -/
theorem exists_viscosityInitialSolution_of_bound {H g : E → ℝ} {K C : NNReal} (hH : Continuous H)
    (hg : LipschitzWith K g) (hgb : Bornology.IsBounded (range g))
    (hHC : ∀ p, ‖p‖ ≤ K → |H p| ≤ C) :
    ∃ v : E × ℝ → ℝ, IsViscosityInitialSolution (fun p _ ↦ H p) g v ∧ LipschitzWith (K + C) v ∧
      ∀ z : E × ℝ, 0 ≤ z.2 → |v z - g z.1| ≤ (C : ℝ) * z.2 := by
  let l : E × ℝ → ℝ := fun z ↦ g z.1 - (C : ℝ) * z.2
  let b : E × ℝ → ℝ := fun z ↦ g z.1 + (C : ℝ) * z.2
  have hl : Continuous l := (hg.continuous.comp continuous_fst).sub
    (continuous_const.mul continuous_snd)
  have hb : Continuous b := (hg.continuous.comp continuous_fst).add
    (continuous_const.mul continuous_snd)
  have hlsub := isSpatialViscositySubsolution_lower_barrier hg hHC
  have hbsuper := isSpatialViscositySupersolution_upper_barrier hg hHC
  have hjoint : Continuous (fun q : E × E ↦ H q.1) := hH.comp continuous_fst
  obtain ⟨u, hu, husub, hub, hmax⟩ := Perron.exists_greatest_subsolution_between
    hjoint hl.continuousOn.upperSemicontinuousOn hlsub hb.continuousOn.upperSemicontinuousOn
    (fun z hz ↦ by linarith [mul_nonneg C.coe_nonneg (le_of_lt hz)])
  have hLip : LipschitzOnWith (K + C) u positiveTimeDomain :=
    lipschitzOnWith_of_greatest_subsolution hg C.coe_nonneg hlsub hu husub hub hmax
  have hcont := hLip.continuousOn
  have hbound : ∀ z ∈ positiveTimeDomain,
      IsBoundedUnder (· ≥ ·) (𝓝[positiveTimeDomain] z) u := by
    intro z hz
    refine ⟨l z - 1, ?_⟩
    change ∀ᶠ y in 𝓝[positiveTimeDomain] z, l z - 1 ≤ u y
    filter_upwards [hl.continuousOn.lowerSemicontinuousOn z hz (l z - 1) (by linarith),
      self_mem_nhdsWithin] with y hy hyU
    exact hy.le.trans (hub y hyU).1
  have husuper := Perron.isSpatialViscositySupersolution_liminf_of_maximal
    hjoint hu husub hbound hb.continuousOn.lowerSemicontinuousOn hbsuper (fun z hz ↦ (hub z hz).2)
    (fun w hw hwsub hwb ↦ hmax w hw hwsub
      (fun z hz ↦ ⟨(hub z hz).1.trans (hwb z hz).1, (hwb z hz).2⟩))
  have hliminf : EqOn (fun z ↦ liminf u (𝓝[positiveTimeDomain] z)) u positiveTimeDomain :=
    fun z hz ↦ haveI := nhdsWithin_neBot_of_mem hz; (hcont z hz).liminf_eq
  obtain ⟨v, hv, huv⟩ := hLip.extend_real
  have hvsol : IsSpatialViscositySolution (fun p _ ↦ H p) positiveTimeDomain v :=
    ⟨husub.congr huv, husuper.congr (hliminf.trans huv)⟩
  have hlv : ∀ z ∈ closure (positiveTimeDomain (E := E)), l z ≤ v z :=
    closure_minimal (t := {z | l z ≤ v z})
      (fun z hz ↦ by change l z ≤ v z; rw [← huv hz]; exact (hub z hz).1)
      (isClosed_le hl hv.continuous)
  have hvb : ∀ z ∈ closure (positiveTimeDomain (E := E)), v z ≤ b z :=
    closure_minimal (t := {z | v z ≤ b z})
      (fun z hz ↦ by change v z ≤ b z; rw [← huv hz]; exact (hub z hz).2)
      (isClosed_le hv.continuous hb)
  have hclosure : closure (positiveTimeDomain (E := E)) = {z : E × ℝ | 0 ≤ z.2} := by
    rw [show positiveTimeDomain (E := E) = univ ×ˢ Ioi 0 from univ_prod.symm, closure_prod_eq,
      closure_univ, closure_Ioi, univ_prod]
    rfl
  have htrace : ∀ z : E × ℝ, 0 ≤ z.2 → |v z - g z.1| ≤ (C : ℝ) * z.2 := by
    intro z hz
    have hz' : z ∈ closure (positiveTimeDomain (E := E)) := by rwa [hclosure]
    exact abs_le.mpr ⟨by have := hlv z hz'; dsimp [l] at this; linarith,
      by have := hvb z hz'; dsimp [b] at this; linarith⟩
  have hinit : ∀ x : E, v (x, 0) = g x := fun x ↦ by
    simpa only [mul_zero, abs_nonpos_iff, sub_eq_zero] using htrace (x, 0) le_rfl
  have hslabs : IsBoundedUniformContinuousOnSlabs v := by
    intro T hT
    refine ⟨?_, hv.uniformContinuous.uniformContinuousOn⟩
    obtain ⟨B, hB⟩ := hgb.exists_norm_le
    apply (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := B + (C : ℝ) * T)).subset
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hB (g z.1) (mem_range_self z.1), htrace z hz.1, norm_sub_norm_le (v z) (g z.1),
      Real.norm_eq_abs (v z - g z.1), mul_le_mul_of_nonneg_left hz.2 C.coe_nonneg]
  exact ⟨v, ⟨hslabs, hvsol, hinit⟩, hv, htrace⟩

/-- A globally Lipschitz autonomous Hamiltonian, with no convexity assumption,
has a viscosity Cauchy solution for bounded Lipschitz data. Its time-zero error
is bounded by `(|H 0| + Lip(H) * Lip(g)) * t` uniformly in space. -/
theorem exists_viscosityInitialSolution_of_lipschitz {H g : E → ℝ} {L K : NNReal}
    (hH : LipschitzWith L H) (hg : LipschitzWith K g) (hgb : Bornology.IsBounded (range g)) :
    ∃ v : E × ℝ → ℝ, IsViscosityInitialSolution (fun p _ ↦ H p) g v ∧
      LipschitzWith (K + (‖H 0‖₊ + L * K)) v ∧
      ∀ z : E × ℝ, 0 ≤ z.2 → |v z - g z.1| ≤ (|H 0| + (L : ℝ) * K) * z.2 := by
  refine exists_viscosityInitialSolution_of_bound hH.continuous hg hgb fun p hp ↦ ?_
  have h := hH.norm_sub_le p 0
  simp only [sub_zero, Real.norm_eq_abs] at h
  change |H p| ≤ |H 0| + (L : ℝ) * K
  linarith [abs_sub_abs_le_abs_sub (H p) (H 0), mul_le_mul_of_nonneg_left hp L.coe_nonneg]

/-- Continuity of the autonomous Hamiltonian already suffices for bounded
Lipschitz data: compactness bounds `H` on the ball of possible test gradients.
The barrier speed, solution, Lipschitz modulus, and initial trace are constructed. -/
theorem exists_viscosityInitialSolution_of_continuous {H g : E → ℝ} {K : NNReal} (hH : Continuous H)
    (hg : LipschitzWith K g) (hgb : Bornology.IsBounded (range g)) :
    ∃ C : NNReal, ∃ v : E × ℝ → ℝ, IsViscosityInitialSolution (fun p _ ↦ H p) g v ∧
      LipschitzWith (K + C) v ∧ ∀ z : E × ℝ, 0 ≤ z.2 → |v z - g z.1| ≤ (C : ℝ) * z.2 := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) (K : ℝ)).exists_bound_of_continuousOn
    hH.continuousOn
  have hnonneg : 0 ≤ C := (norm_nonneg (H 0)).trans (hC 0 (by simp))
  refine ⟨⟨C, hnonneg⟩, ?_⟩
  refine exists_viscosityInitialSolution_of_bound hH hg hgb fun p hp ↦ ?_
  change |H p| ≤ C
  simpa only [Real.norm_eq_abs] using hC p (by simpa using hp)

/-- The constructed Cauchy solution is unique among all solutions bounded
and uniformly continuous on finite slabs, not merely among Lipschitz ones. -/
theorem exists_unique_viscosityInitialSolution_of_lipschitz {H g : E → ℝ} {L K : NNReal}
    (hH : LipschitzWith L H) (hg : LipschitzWith K g) (hgb : Bornology.IsBounded (range g)) :
    ∃ u : E × ℝ → ℝ, IsViscosityInitialSolution (fun p _ ↦ H p) g u ∧ ∀ v : E × ℝ → ℝ,
      IsViscosityInitialSolution (fun p _ ↦ H p) g v → EqOn u v {z : E × ℝ | 0 ≤ z.2} := by
  obtain ⟨u, hu, _, _⟩ := exists_viscosityInitialSolution_of_lipschitz hH hg hgb
  exact ⟨u, hu, fun _ hv ↦ hu.eqOn_of_initial_eq hv hH.continuous⟩

/-- Existence and uniqueness on a prescribed finite slab. A competing solution
only needs the equation and bounded uniform continuity on that slab; it need
not have any continuation beyond the terminal time. -/
theorem exists_unique_on_closedTimeSlab_of_continuous {H g : E → ℝ} {K : NNReal} {T : ℝ}
    (hH : Continuous H) (hg : LipschitzWith K g) (hgb : Bornology.IsBounded (range g))
    (hT : 0 < T) :
    ∃ u : E × ℝ → ℝ, IsViscosityInitialSolution (fun p _ ↦ H p) g u ∧
      ∀ v : E × ℝ → ℝ,
        IsSpatialViscositySolution (fun p _ ↦ H p) (openTimeSlab T) v →
        Bornology.IsBounded (v '' closedTimeSlab T) →
        UniformContinuousOn v (closedTimeSlab T) →
        (∀ x : E, v (x, 0) = g x) → EqOn u v (closedTimeSlab T) := by
  obtain ⟨C, u, hu, _, _⟩ := exists_viscosityInitialSolution_of_continuous hH hg hgb
  refine ⟨u, hu, fun v hv hvb hvc hinit z hz ↦ ?_⟩
  have hforward : openTimeSlab T ⊆ positiveTimeDomain (E := E) := fun _ hw ↦ hw.1
  apply le_antisymm
  · exact hu.2.1.1.le_of_initial_le_on_slab hv.2 hforward Subset.rfl hH
      (hu.1 T hT) ⟨hvb, hvc⟩ (fun x ↦ by rw [hu.initial_eq, hinit]) hT hz
  · exact hv.1.le_of_initial_le_on_slab hu.2.1.2 Subset.rfl hforward hH
      ⟨hvb, hvc⟩ (hu.1 T hT) (fun x ↦ by rw [hu.initial_eq, hinit]) hT hz

end HamiltonJacobi.Cauchy
