/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.VectorForms
public import PDE.Analysis.Evolution.Integrated.WeakEquation
public import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition
import PDE.Analysis.Evolution.Galerkin.Semilinear.GloballyLipschitz
import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial

/-!
# Integrated solutions of finite-component reaction-diffusion

For `uₜ - Δu = f(u)` with `u : Ω → ℝ^m` in `H¹₀(Ω; ℝ^m)` and a globally Lipschitz reaction `f`,
pointwise application of `f` is an `L`-Lipschitz map of the vector-valued `L²` pivot with affine
growth (`lipschitzWith_reactionLp`, `norm_reactionLp_le`). The Galerkin theorem for globally
Lipschitz reactions, run on the spectral trial system of the spatial inclusion, gives a unique
integrated solution on every finite time interval (`existsUnique_integrated`), and the Gelfand
evolution theorem supplies its weak derivative in `L²(H⁻¹)` and a continuous representative on the
closed interval (`exists_evolution_of_integrated`). The weak formulation is in `ReactionDiffusion`.

The two bounds are the `L²` forms of the hypothesis (3) and the growth bound (4) of Evans's §9.2.1,
Example 1. Evans proves existence by a contraction argument instead, in the proof of his Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.1, Example 1 (Reaction-diffusion equations), (2)-(7),
  p. 535, and Theorem 2 (Existence) and its proof, (8)-(14), pp. 536-537.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal InnerProductSpace

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace ReactionDiffusion

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {f : (ℝ^m) → (ℝ^m)} {L : ℝ≥0}

local notation "𝓥" => H¹₀(Ω; ℝ^m)
local notation "μ" => domainMeasure n Ω
local notation "ν" => volume.restrict (Ioc a b)
local notation "Pivot" => Lp (ℝ^m) 2 μ

/-- A bounded spatial domain makes the reaction offset square integrable. -/
theorem memLp_reaction (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    (q : Pivot) : MemLp (fun x ↦ f (q x)) 2 μ := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hΩbounded
  exact hf.comp_memLp_of_memLp_const (memLp_const (f 0)) (Lp.memLp q)

/-- Pointwise application of the reaction on the vector-valued `L²` pivot. -/
def reactionLp (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f) :
    Pivot → Pivot :=
  Lp.superposition (fun _ ↦ f) (memLp_reaction hΩbounded hf)

/-- The reaction's `L²` representative agrees with its pointwise spatial expression. -/
theorem reactionLp_apply_ae (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    (q : Pivot) :
    reactionLp hΩbounded hf q =ᵐ[μ] fun x ↦ f (q x) :=
  Lp.coeFn_superposition _ _ q

/-- Superposition by `f` is `L`-Lipschitz on `L²`, with no dimension factor. -/
theorem lipschitzWith_reactionLp
    (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f) :
    LipschitzWith L (reactionLp hΩbounded hf) :=
  hf.lipschitzWith_superposition _

/-- The constant function `f 0` has `L²` norm `√(μ univ) * ‖f 0‖`. -/
theorem norm_reactionLp_zero
    (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f) :
    ‖reactionLp hΩbounded hf 0‖ = Real.sqrt (μ univ).toReal * ‖f 0‖ := by
  have hae : reactionLp hΩbounded hf 0 =ᵐ[μ] fun _ ↦ f 0 := by
    filter_upwards [reactionLp_apply_ae hΩbounded hf 0, Lp.coeFn_zero (ℝ^m) 2 μ]
      with x hx hzero
    simpa only [hzero, Pi.zero_apply] using hx
  have hs : ‖reactionLp hΩbounded hf 0‖ ^ 2 = (μ univ).toReal * ‖f 0‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    calc
      _ = ∫ _x, ‖f 0‖ ^ 2 ∂μ := integral_congr_ae (hae.fun_comp fun z ↦ ‖z‖ ^ 2)
      _ = _ := by simp [smul_eq_mul, measureReal_def]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [hs, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]

/-- The reaction superposition has affine growth: `‖R q‖ ≤ L‖q‖ + √(μ univ)‖f 0‖`. -/
theorem norm_reactionLp_le
    (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f) (q : Pivot) :
    ‖reactionLp hΩbounded hf q‖ ≤
      L * ‖q‖ + Real.sqrt (μ univ).toReal * ‖f 0‖ := by
  have h := (lipschitzWith_reactionLp hΩbounded hf).dist_le_mul q 0
  rw [dist_zero_right, dist_eq_norm] at h
  calc
    _ ≤ ‖reactionLp hΩbounded hf q - reactionLp hΩbounded hf 0‖ +
        ‖reactionLp hΩbounded hf 0‖ := norm_le_norm_sub_add _ _
    _ ≤ L * ‖q‖ + ‖reactionLp hΩbounded hf 0‖ := add_le_add h le_rfl
    _ = _ := by rw [norm_reactionLp_zero hΩbounded hf]

/-- The dual reaction pairing is the spatial integral against the vector value. -/
theorem reactionLp_dual_apply
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    (q : Pivot) (v : 𝓥) :
    (gelfandTriple hΩopen).pivotToDual (reactionLp hΩbounded hf q) v =
      ∫ x, inner ℝ (f (q x)) (toLp v x) ∂μ := by
  rw [GelfandTriple.pivotToDual_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reactionLp_apply_ae hΩbounded hf q] with x hx
  rw [hx]
  rfl

/-- The reaction-diffusion equation has a unique integrated solution on every finite
interval, for arbitrary `L²` initial data. -/
theorem existsUnique_integrated
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hab : a < b) (hf : LipschitzWith L f) (g : Pivot) :
    ∃! u : Lp 𝓥 2 ν,
      IsGelfandIntegratedWeakSolution (gelfandTriple hΩopen)
        (fun _ ↦ vectorDirichletForm)
        (fun t ↦ (gelfandTriple hΩopen).pivotToDual
          (reactionLp hΩbounded hf (toLp (u t)))) u g := by
  let : MeasurableSpace 𝓥 := borel _
  let : BorelSpace 𝓥 := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ 𝓥) := borel _
  let : BorelSpace (StrongDual ℝ 𝓥) := ⟨rfl⟩
  apply IsGelfandIntegratedWeakSolution.existsUnique_of_lipschitz_reaction
    (gelfandTriple hΩopen)
    (spectralTrialSystem m hΩopen hΩbounded)
    (fun _ ↦ vectorDirichletForm) (theta := 1) (gamma := 1) hab zero_lt_one
    (fun _ ↦ aestronglyMeasurable_const) 1
    (Filter.Eventually.of_forall fun _ ↦ norm_vectorDirichletForm_le)
    _ (reactionLp hΩbounded hf) (lipschitzWith_reactionLp hΩbounded hf) g
  filter_upwards with t v
  simpa only [one_mul, gelfandTriple_inclusion_apply] using
    (vectorDirichletForm_garding v).le

/-- The reaction along an energy trajectory belongs to the dual-valued time `L²` space. -/
def reactionForcingLp
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    (u : Lp 𝓥 2 ν) : Lp (StrongDual ℝ 𝓥) 2 ν :=
  let T := gelfandTriple hΩopen
  let R := reactionLp hΩbounded hf
  let hmem (w : Lp Pivot 2 ν) : MemLp (fun t ↦ R (w t)) 2 ν :=
    (lipschitzWith_reactionLp hΩbounded hf).comp_memLp_of_memLp_const
      (memLp_const (R 0)) (Lp.memLp w)
  T.pivotToDual.compLpL 2 ν
    (Lp.superposition (fun _ ↦ R) hmem (T.inclusion.compLpL 2 ν u))

/-- The time forcing agrees with the reaction on one full-measure set of times. -/
theorem reactionForcingLp_apply_ae
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    (u : Lp 𝓥 2 ν) :
    reactionForcingLp hΩopen hΩbounded hf u =ᵐ[ν]
      fun t ↦ (gelfandTriple hΩopen).pivotToDual
        (reactionLp hΩbounded hf (toLp (u t))) := by
  let T := gelfandTriple (m := m) hΩopen
  let R := reactionLp hΩbounded hf
  let hmem (w : Lp Pivot 2 ν) : MemLp (fun t ↦ R (w t)) 2 ν :=
    (lipschitzWith_reactionLp hΩbounded hf).comp_memLp_of_memLp_const
      (memLp_const (R 0)) (Lp.memLp w)
  let J := T.inclusion.compLpL 2 ν
  let N := Lp.superposition (fun _ ↦ R) hmem
  filter_upwards [T.pivotToDual.coeFn_compLpL (N (J u)),
    Lp.coeFn_superposition (fun _ ↦ R) hmem (J u),
    T.inclusion.coeFn_compLpL u] with t hQ hN hJ
  change reactionForcingLp hΩopen hΩbounded hf u t = _ at hQ
  change N (J u) t = _ at hN
  change J u t = _ at hJ
  rw [hQ, hN, hJ]
  rfl

/-- The `L²` reaction forcing gives a continuous pivot evolution and its dual residual. -/
theorem exists_evolution_reactionForcingLp
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    {u : Lp 𝓥 2 ν} {g : Pivot}
    (hu : IsGelfandIntegratedWeakSolution (gelfandTriple hΩopen)
      (fun _ ↦ vectorDirichletForm) (fun t ↦ reactionForcingLp hΩopen hΩbounded hf u t) u g) :
    ∃ d : Lp (StrongDual ℝ 𝓥) 2 ν,
      ∃ E : ContinuousPivotEvolutionOn (gelfandTriple hΩopen)
          (fun t ↦ u t) (fun t ↦ d t) a b,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u d ∧
        E.representative a = g ∧
        ∀ᵐ t ∂ν, d t = reactionForcingLp hΩopen hΩbounded hf u t -
          vectorDirichletForm (u t) := by
  let : MeasurableSpace 𝓥 := borel _
  let : BorelSpace 𝓥 := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ 𝓥) := borel _
  let : BorelSpace (StrongDual ℝ 𝓥) := ⟨rfl⟩
  have hbound : ∀ᵐ _t ∂ν, ‖vectorDirichletForm (n := n) (m := m) (Ω := Ω)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun _ ↦ norm_vectorDirichletForm_le
  exact hu.exists_continuousPivotEvolutionOn_initial_L2
    (T := gelfandTriple hΩopen)
    (B := fun _ ↦ vectorDirichletForm (n := n) (m := m) (Ω := Ω))
    (ell := reactionForcingLp hΩopen hΩbounded hf u)
    (fun _ ↦ aestronglyMeasurable_const) 1
    hbound hu.interval_nonempty

/-- The reaction forcing yields an `L²` dual residual and a continuous pivot evolution. -/
theorem exists_evolution_residual
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    {u : Lp 𝓥 2 ν} {g : Pivot}
    (hu : IsGelfandIntegratedWeakSolution (gelfandTriple hΩopen)
      (fun _ ↦ vectorDirichletForm)
      (fun t ↦ (gelfandTriple hΩopen).pivotToDual
        (reactionLp hΩbounded hf (toLp (u t)))) u g) :
    ∃ d : Lp (StrongDual ℝ 𝓥) 2 ν,
      ∃ E : ContinuousPivotEvolutionOn (gelfandTriple hΩopen)
          (fun t ↦ u t) (fun t ↦ d t) a b,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u d ∧
        E.representative a = g ∧
        ∀ᵐ t ∂ν, d t = (gelfandTriple hΩopen).pivotToDual
          (reactionLp hΩbounded hf (toLp (u t))) -
            vectorDirichletForm (u t) := by
  have hload := reactionForcingLp_apply_ae hΩopen hΩbounded hf u
  obtain ⟨d, E, hd, hEa, hres⟩ := exists_evolution_reactionForcingLp hΩopen hΩbounded hf
    (hu.congr_forcing_ae hload.symm)
  refine ⟨d, E, hd, hEa, ?_⟩
  filter_upwards [hres, hload] with t ht hlt
  exact ht.trans (congrArg (fun q : StrongDual ℝ 𝓥 ↦ q - vectorDirichletForm (u t)) hlt)

/-- Every integrated solution has a weak time derivative, a continuous trace on the closed
interval, and satisfies the full-gradient weak equation for almost every time. -/
theorem exists_evolution_of_integrated
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (hf : LipschitzWith L f)
    {u : Lp 𝓥 2 ν} {g : Pivot}
    (hu : IsGelfandIntegratedWeakSolution (gelfandTriple hΩopen)
      (fun _ ↦ vectorDirichletForm)
      (fun t ↦ (gelfandTriple hΩopen).pivotToDual
        (reactionLp hΩbounded hf (toLp (u t)))) u g) :
    ∃ d : Lp (StrongDual ℝ 𝓥) 2 ν,
      ∃ E : ContinuousPivotEvolutionOn (gelfandTriple hΩopen)
          (fun t ↦ u t) (fun t ↦ d t) a b,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u d ∧
        E.representative a = g ∧
        ∀ᵐ t ∂ν, ∀ v : 𝓥,
          d t v + (∫ x, ∑ i : Fin m, ∑ j : Fin n,
            ∇ (u t) x (finProdFinEquiv (i, j)) *
              ∇ v x (finProdFinEquiv (i, j)) ∂μ) =
            ∫ x, inner ℝ (f (toLp (u t) x))
              (toLp v x) ∂μ := by
  obtain ⟨d, E, hd, hEa, hres⟩ := exists_evolution_residual hΩopen hΩbounded hf hu
  refine ⟨d, E, hd, hEa, ?_⟩
  filter_upwards [hres] with t ht v
  rw [← vectorDirichletForm_eq_integral,
    ← reactionLp_dual_apply hΩopen hΩbounded hf]
  have heq := congrArg (fun q : StrongDual ℝ 𝓥 ↦ q v) ht
  simp only [sub_apply] at heq
  exact (eq_sub_iff_add_eq).mp heq

end ReactionDiffusion
