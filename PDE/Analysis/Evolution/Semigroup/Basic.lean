/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Strongly continuous semigroups

Operator semigroups in the sense of Evans §7.4.1, on a real normed space. A strongly continuous
semigroup consists of bounded linear operators `T(t)`, for nonnegative time, satisfying

* `T(0) = I`;
* `T(s + t) = T(s) T(t)`;
* `t ↦ T(t)x` is continuous for every vector `x`.

These are Evans's conditions (4)-(6), and `IsContraction` is his condition (7),
`‖T(t)‖ ≤ 1`. Evans works on a Banach space throughout; here completeness is assumed only by
the results that need it.

Strong continuity is encoded using Mathlib's topology of pointwise convergence
on continuous linear maps, `E →Lₚₜ[ℝ] E`; operator-norm continuity is not
assumed. This distinction is essential for unbounded infinitesimal generators.

Mathlib's pointwise-convergence synonym does not carry the composition
`Monoid` instance of continuous linear endomorphisms. The definition therefore
stores the algebraic monoid homomorphism and the continuity of its canonical
map separately, avoiding a project-wide orphan instance on a Mathlib type.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, definitions of semigroups and contraction semigroups,
  (4)-(7), pp. 434-435. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A strongly continuous one-parameter semigroup of bounded linear operators. -/
structure StronglyContinuousSemigroup where
  /-- The operator semigroup, with additive time represented multiplicatively. -/
  toMonoidHom : Multiplicative NNReal →* (E →L[ℝ] E)
  /-- The operator semigroup is continuous in the topology of pointwise convergence. -/
  continuous_toPointwise :
    Continuous fun t ↦
      ContinuousLinearMap.toPointwiseConvergenceCLM ℝ (RingHom.id ℝ) E E (toMonoidHom t)

namespace StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : CoeFun (StronglyContinuousSemigroup E)
    (fun _ ↦ NNReal → E →L[ℝ] E) :=
  ⟨fun T t ↦ T.toMonoidHom (Multiplicative.ofAdd t)⟩

/-- Two strongly continuous semigroups are equal when their operators agree at every time. -/
@[ext]
theorem ext {T S : StronglyContinuousSemigroup E}
    (h : ∀ t, T t = S t) :
    T = S := by
  cases T with
  | mk T hTcontinuous =>
      cases S with
      | mk S hScontinuous =>
          have hTS : T = S := by
            apply MonoidHom.ext
            intro t
            simpa using h t.toAdd
          subst S
          rfl

/-- The time-zero operator is the identity. -/
theorem map_zero (T : StronglyContinuousSemigroup E) :
    T 0 = ContinuousLinearMap.id ℝ E := by
  simpa only [ofAdd_zero, ContinuousLinearMap.one_def] using T.toMonoidHom.map_one

/-- Evolution through `s + t` is composition of the evolutions through `t` and then `s`. -/
theorem map_add (T : StronglyContinuousSemigroup E) (s t : NNReal) :
    T (s + t) = (T s).comp (T t) := by
  simpa only [ofAdd_add, ContinuousLinearMap.mul_def] using
    T.toMonoidHom.map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

/-- The semigroup acts as the identity at time zero. -/
theorem map_zero_apply (T : StronglyContinuousSemigroup E) (x : E) :
    T 0 x = x := by
  rw [T.map_zero]
  rfl

/-- Acting for time `s + t` is the same as acting for `t` and then for `s`. -/
theorem map_add_apply (T : StronglyContinuousSemigroup E) (s t : NNReal) (x : E) :
    T (s + t) x = T s (T t x) := by
  rw [T.map_add]
  rfl

/-- Time evolutions commute, as a consequence of the additive
parameterization of the semigroup. -/
theorem map_comm (T : StronglyContinuousSemigroup E) (s t : NNReal) :
    (T s).comp (T t) = (T t).comp (T s) := by
  rw [← T.map_add, ← T.map_add, add_comm]

/-- Semigroup operators at different times commute on every vector. -/
theorem map_apply_comm (T : StronglyContinuousSemigroup E) (s t : NNReal) (x : E) :
    T s (T t x) = T t (T s x) := by
  rw [← T.map_add_apply, ← T.map_add_apply, add_comm]

/-- The orbit of `x` under a strongly continuous semigroup. -/
def orbit (T : StronglyContinuousSemigroup E) (x : E) : NNReal → E :=
  fun t ↦ T t x

/-- The orbit `t ↦ T(t) x` is continuous for every initial vector `x`. -/
theorem continuous_orbit (T : StronglyContinuousSemigroup E) (x : E) :
    Continuous (T.orbit x) := by
  exact
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℝ) E x).continuous.comp
      T.continuous_toPointwise

/-- Every orbit is continuous at each nonnegative time. -/
theorem continuousAt_orbit (T : StronglyContinuousSemigroup E) (x : E) (t : NNReal) :
    ContinuousAt (T.orbit x) t :=
  (T.continuous_orbit x).continuousAt

/-- Shifting an orbit by `t` is the orbit starting from `T(t)x`. -/
theorem orbit_add (T : StronglyContinuousSemigroup E) (x : E) (s t : NNReal) :
    T.orbit x (s + t) = T.orbit (T t x) s :=
  T.map_add_apply s t x

/-- The norm of a strongly continuous orbit varies continuously in time. -/
theorem continuous_norm_orbit (T : StronglyContinuousSemigroup E) (x : E) :
    Continuous fun t ↦ ‖T.orbit x t‖ :=
  (T.continuous_orbit x).norm

/-- The distance between two strongly continuous orbits varies continuously in time. -/
theorem continuous_dist_orbit (T : StronglyContinuousSemigroup E) (x y : E) :
    Continuous fun t ↦ dist (T.orbit x t) (T.orbit y t) :=
  (T.continuous_orbit x).dist (T.continuous_orbit y)

/-- Strong continuity makes the semigroup operators uniformly bounded on each
compact time interval. -/
theorem exists_norm_le_on_Icc [CompleteSpace E]
    (T : StronglyContinuousSemigroup E) (t : NNReal) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : NNReal) t, ‖T s‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    banach_steinhaus (g := fun s : Set.Icc (0 : NNReal) t ↦ T s) fun x ↦ by
      obtain ⟨M, hM⟩ :=
        isCompact_Icc.bddAbove_image (T.continuous_norm_orbit x).continuousOn
      refine ⟨M, fun s ↦ hM ?_⟩
      exact ⟨s, s.property, rfl⟩
  refine ⟨C, ?_, fun s hs ↦ hC ⟨s, hs⟩⟩
  exact (norm_nonneg (T 0)).trans (hC ⟨0, by simp⟩)

/-- A semigroup is contractive when every time evolution has operator norm at most one. -/
def IsContraction (T : StronglyContinuousSemigroup E) : Prop :=
  ∀ t, ‖T t‖ ≤ 1

namespace IsContraction

variable {T : StronglyContinuousSemigroup E}

/-- A contraction semigroup does not increase the norm of a vector. -/
theorem norm_apply_le (hT : T.IsContraction) (t : NNReal) (x : E) :
    ‖T t x‖ ≤ ‖x‖ := by
  simpa using (T t).le_of_opNorm_le (hT t) x

/-- A contraction semigroup does not increase the distance between two vectors. -/
theorem dist_apply_le (hT : T.IsContraction) (t : NNReal) (x y : E) :
    dist (T t x) (T t y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← (T t).map_sub]
  exact hT.norm_apply_le t (x - y)

/-- Each operator in a contraction semigroup is `1`-Lipschitz. -/
theorem lipschitzWith_one (hT : T.IsContraction) (t : NNReal) :
    LipschitzWith 1 (T t) :=
  ContinuousLinearMap.lipschitzWith_of_opNorm_le (hT t)

/-- Advancing a contraction-semigroup orbit can only decrease its norm. -/
theorem norm_orbit_add_le (hT : T.IsContraction) (s t : NNReal) (x : E) :
    ‖T (s + t) x‖ ≤ ‖T t x‖ := by
  rw [T.map_add_apply]
  exact hT.norm_apply_le s (T t x)

/-- Advancing two contraction-semigroup orbits can only decrease their distance. -/
theorem dist_orbit_add_le (hT : T.IsContraction) (s t : NNReal) (x y : E) :
    dist (T (s + t) x) (T (s + t) y) ≤ dist (T t x) (T t y) := by
  rw [T.map_add_apply, T.map_add_apply]
  exact hT.dist_apply_le s (T t x) (T t y)

/-- The norm of every contraction-semigroup orbit is nonincreasing in time. -/
theorem antitone_norm_orbit (hT : T.IsContraction) (x : E) :
    Antitone fun t ↦ ‖T.orbit x t‖ := by
  intro s t hst
  change ‖T t x‖ ≤ ‖T s x‖
  calc
    ‖T t x‖ = ‖T ((t - s) + s) x‖ := by rw [tsub_add_cancel_of_le hst]
    _ ≤ ‖T s x‖ := hT.norm_orbit_add_le (t - s) s x

/-- Distances between two contraction-semigroup orbits are nonincreasing in time. -/
theorem antitone_dist_orbit (hT : T.IsContraction) (x y : E) :
    Antitone fun t ↦ dist (T.orbit x t) (T.orbit y t) := by
  intro s t hst
  change dist (T t x) (T t y) ≤ dist (T s x) (T s y)
  calc
    dist (T t x) (T t y) =
        dist (T ((t - s) + s) x) (T ((t - s) + s) y) := by
          rw [tsub_add_cancel_of_le hst]
    _ ≤ dist (T s x) (T s y) := hT.dist_orbit_add_le (t - s) s x y

end IsContraction

/-- The constant identity evolution is a strongly continuous semigroup. -/
def identity : StronglyContinuousSemigroup E where
  toMonoidHom :=
    { toFun := fun _ ↦ ContinuousLinearMap.id ℝ E
      map_one' := rfl
      map_mul' := by
        intro s t
        ext x
        rfl }
  continuous_toPointwise := continuous_const

/-- The identity semigroup fixes every vector at every time. -/
@[simp]
theorem identity_apply (t : NNReal) (x : E) :
    identity (E := E) t x = x :=
  rfl

/-- The constant identity semigroup is contractive. -/
theorem identity_isContraction :
    (identity (E := E)).IsContraction := by
  intro t
  exact ContinuousLinearMap.norm_id_le

end StronglyContinuousSemigroup

end PDE.Analysis.Evolution
