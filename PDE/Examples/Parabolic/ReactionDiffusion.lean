/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Semilinear.ReactionDiffusion
import CAS.ExactTactic

/-!
# Weak solutions of Lipschitz reaction–diffusion systems

The system `uₜ - Δu = f(u)` for `u : Ω → ℝ^m` with zero boundary values has a unique weak
solution in the Gelfand triple `H¹₀ ⊆ L² ⊆ H⁻¹` for every globally Lipschitz `f`, every
bounded open `Ω`, every finite time interval and every `L²` initial value. The examples
specialize this to a coupled affine reaction with a nonzero constant term, scaled by any
real factor, and to a coupled reaction built from absolute values, which is not
differentiable at zero. The last two theorems give the continuous evolution for
energy-space initial data, in general and in dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal InnerProductSpace

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace PDE.Examples.ReactionDiffusion

/-- The first component responds to the second, and the second responds to the first. -/
def coupledLinear : (ℝ^2) →L[ℝ] (ℝ^2) :=
  ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 (1 : ℝ))).comp
    (EuclideanSpace.proj 1)) -
  2 • ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 1 (1 : ℝ))).comp
    (EuclideanSpace.proj 0))

/-- A concrete coupled reaction with a nonzero constant forcing. -/
def coupledAffine (z : ℝ^2) : ℝ^2 :=
  coupledLinear z + WithLp.toLp 2 ![1, 3]

/-- The coordinate equations are `f₀(z)=z₁+1` and `f₁(z)=-2z₀+3`. -/
theorem coupledAffine_coordinates (z : ℝ^2) :
    coupledAffine z = WithLp.toLp 2 ![z 1 + 1, -2 * z 0 + 3] := by
  ext i
  fin_cases i
  · simp [coupledAffine, coupledLinear]
  · have h : -(z 0 * 2) + 3 = -2 * z 0 + 3 := by cas
    simpa [coupledAffine, coupledLinear] using h

/-- The affine map is globally Lipschitz with the norm of its linear part. -/
theorem lipschitzWith_coupledAffine : LipschitzWith ‖coupledLinear‖₊ coupledAffine := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [coupledAffine, dist_add_right] using coupledLinear.lipschitzWith.dist_le_mul x y

/-- The reaction does not vanish at zero. -/
theorem coupledAffine_zero : coupledAffine 0 = WithLp.toLp 2 ![1, 3] := by
  simp [coupledAffine]

/-- A nonsmooth component map with opposite signs on its two absolute values. -/
def signedAbsoluteValue (z : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 ![|z 0|, -|z 1|]

/-- The absolute-value part is nonexpansive in the Euclidean norm. -/
theorem lipschitzWith_signedAbsoluteValue : LipschitzWith 1 signedAbsoluteValue := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  change (|x 0| - |y 0|) ^ 2 + (-|x 1| - -|y 1|) ^ 2 ≤
    (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2
  have hnorm (s t : ℝ) : (|s| - |t|) ^ 2 ≤ (s - t) ^ 2 := by
    have h : dist ‖s‖ ‖t‖ ≤ dist s t := by
      simpa using (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).dist_le_mul s t
    have hs := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr h
    simpa only [Real.dist_eq, Real.norm_eq_abs, sq_abs] using hs
  have hsign : (-|x 1| - -|y 1|) ^ 2 = (|x 1| - |y 1|) ^ 2 := by cas
  rw [hsign]
  exact add_le_add (hnorm _ _) (hnorm _ _)

/-- Swapping the two components is an isometry that couples the equations. -/
def swapComponents (z : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 ![z 1, z 0]

/-- The cross-component linear term does not enlarge distances. -/
theorem lipschitzWith_swapComponents : LipschitzWith 1 swapComponents := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  change (x 1 - y 1) ^ 2 + (x 0 - y 0) ^ 2 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2
  exact (add_comm _ _).le

/-- A coupled reaction that is neither linear nor smooth at zero. -/
def coupledNonsmooth (z : ℝ^2) : ℝ^2 :=
  signedAbsoluteValue z + swapComponents z + WithLp.toLp 2 ![1, 3]

/-- The nonsmooth, coupled reaction is globally `2`-Lipschitz. -/
theorem lipschitzWith_coupledNonsmooth : LipschitzWith 2 coupledNonsmooth := by
  have h := lipschitzWith_signedAbsoluteValue.add lipschitzWith_swapComponents
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [coupledNonsmooth, dist_add_right, one_add_one_eq_two] using h.dist_le_mul x y

/-- Arbitrary reaction scaling is allowed, with its derived finite Lipschitz constant. -/
theorem lipschitzWith_scaled_coupledAffine (c : ℝ) :
    LipschitzWith (‖c‖₊ * ‖coupledLinear‖₊) (fun z ↦ c • coupledAffine z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← smul_sub, norm_smul]
  exact (mul_le_mul_of_nonneg_left
    (lipschitzWith_coupledAffine.dist_le_mul x y) (norm_nonneg c)).trans_eq (mul_assoc _ _ _).symm

local notation "Ω₁" => Metric.ball (0 : ℝ^1) 1
local notation "μ₁" => domainMeasure 1 Ω₁
local notation "ν₁" => volume.restrict (Ioc (0 : ℝ) 100)
local notation "V₁" => H¹₀(Ω₁; ℝ^2)

/-- Constant `L²` initial data on the unit ball. -/
def ballInitialData {m : ℕ} (q : ℝ^m) : Lp (ℝ^m) 2 μ₁ :=
  let := isFiniteMeasure_domainMeasure_of_isBounded (Metric.isBounded_ball : Bornology.IsBounded Ω₁)
  (memLp_const q).toLp (fun _ ↦ q)

/-- The initial class has the stated pointwise value almost everywhere. -/
theorem ballInitialData_apply_ae {m : ℕ} (q : ℝ^m) :
    ballInitialData q =ᵐ[μ₁] fun _ ↦ q := by
  unfold ballInitialData
  exact MemLp.coeFn_toLp _

/-- Nonzero constant data remain nonzero as a pivot class on this domain. -/
theorem ballInitialData_ne_zero {m : ℕ} {q : ℝ^m} (hq : q ≠ 0) :
    ballInitialData q ≠ 0 := by
  have hmeasure : μ₁ ≠ 0 := by
    intro h
    have heq := congrArg (fun μ : Measure (ℝ^1) ↦ μ univ) h
    have hpos := Metric.measure_ball_pos (volume : Measure (ℝ^1)) 0 (by norm_num : (0 : ℝ) < 1)
    exact hpos.ne' (by simpa using heq)
  let : NeZero μ₁ := ⟨hmeasure⟩
  intro h
  have hae := (ballInitialData_apply_ae q).symm.trans
    (h ▸ (Lp.coeFn_zero (ℝ^m) 2 μ₁))
  exact hq hae.exists.choose_spec

/-- The coupled affine PDE allows any real scaling, a long fixed interval, and nonzero pivot
initial data. Its conclusion gives a unique weak solution. -/
theorem existsUnique_weakSolution_scaled_coupledAffine (c : ℝ) :
    ∃! u : Lp V₁ 2 ν₁,
      ∃ d : Lp (StrongDual ℝ V₁) 2 ν₁, ∃ w : ℝ → Lp (ℝ^2) 2 μ₁,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple Metric.isOpen_ball) u d ∧
        ContinuousOn w (Icc 0 100) ∧
        w =ᵐ[ν₁] (fun t ↦ toLp (u t)) ∧
        w 0 = ballInitialData (WithLp.toLp 2 ![2, -1]) ∧
        ∀ᵐ t ∂ν₁, ∀ v : V₁,
          d t v + (∫ x, ∑ i : Fin 2, ∑ j : Fin 1,
            ∇ (u t) x (finProdFinEquiv (i, j)) *
              ∇ v x (finProdFinEquiv (i, j)) ∂μ₁) =
            ∫ x, inner ℝ (c • coupledAffine (toLp (u t) x))
              (toLp v x) ∂μ₁ := by
  exact _root_.ReactionDiffusion.existsUnique_weakSolution Metric.isOpen_ball
    Metric.isBounded_ball (by norm_num) (lipschitzWith_scaled_coupledAffine c)
    (ballInitialData (WithLp.toLp 2 ![2, -1]))

/-- The nonsmooth coupled map also gives the weak PDE, with no differentiability premise
on the reaction and no restriction on the finite time interval. -/
theorem existsUnique_weakSolution_coupledNonsmooth {a b : ℝ} (hab : a < b) (q : ℝ^2) :
    ∃! u : Lp V₁ 2 (volume.restrict (Ioc a b)),
      ∃ d : Lp (StrongDual ℝ V₁) 2 (volume.restrict (Ioc a b)),
      ∃ w : ℝ → Lp (ℝ^2) 2 μ₁,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple Metric.isOpen_ball) u d ∧
        ContinuousOn w (Icc a b) ∧
        w =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ toLp (u t)) ∧
        w a = ballInitialData q ∧
        ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V₁,
          d t v + (∫ x, ∑ i : Fin 2, ∑ j : Fin 1,
            ∇ (u t) x (finProdFinEquiv (i, j)) *
              ∇ v x (finProdFinEquiv (i, j)) ∂μ₁) =
            ∫ x, inner ℝ (coupledNonsmooth (toLp (u t) x))
              (toLp v x) ∂μ₁ :=
  _root_.ReactionDiffusion.existsUnique_weakSolution Metric.isOpen_ball Metric.isBounded_ball hab
    lipschitzWith_coupledNonsmooth (ballInitialData q)

/-- Energy-space initial data give a continuous pivot evolution, including
both endpoint traces and the integrated dual derivative on every subinterval. -/
theorem exists_evolution {n m : ℕ} {Ω : Set (ℝ^n)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b) {f : (ℝ^m) → (ℝ^m)} {L : ℝ≥0} (hf : LipschitzWith L f)
    (g₀ : H¹₀(Ω; ℝ^m)) :
    ∃ u : Lp (H¹₀(Ω; ℝ^m)) 2 (volume.restrict (Ioc a b)),
      ∃ d : Lp (StrongDual ℝ (H¹₀(Ω; ℝ^m))) 2 (volume.restrict (Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn (gelfandTriple hΩopen)
          (fun t ↦ u t) (fun t ↦ d t) a b,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u d ∧
        E.representative a = toLp g₀ := by
  obtain ⟨u, d, E, hd, hEa, _⟩ :=
    _root_.ReactionDiffusion.exists_evolution hΩopen hΩbounded hab hf g₀
  exact ⟨u, d, E, hd, hEa⟩

/-- The construction also gives a scalar evolution in zero spatial dimension. -/
theorem exists_evolution_zero_dimension {a b : ℝ} (hab : a < b)
    (g₀ : H¹₀((univ : Set (ℝ^0)); ℝ^1)) :
    ∃ u : Lp (H¹₀((univ : Set (ℝ^0)); ℝ^1)) 2 (volume.restrict (Ioc a b)),
      ∃ d : Lp (StrongDual ℝ (H¹₀((univ : Set (ℝ^0)); ℝ^1))) 2
          (volume.restrict (Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn (gelfandTriple isOpen_univ)
          (fun t ↦ u t) (fun t ↦ d t) a b,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple isOpen_univ) u d ∧
        E.representative a = toLp g₀ := by
  have hbounded : Bornology.IsBounded (univ : Set (ℝ^0)) := isCompact_univ.isBounded
  exact exists_evolution isOpen_univ hbounded hab LipschitzWith.id g₀

end PDE.Examples.ReactionDiffusion
