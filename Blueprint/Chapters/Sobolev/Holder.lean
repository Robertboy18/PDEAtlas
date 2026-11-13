/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Sobolev.Core
import PDE.Spaces.Holder.Exponent
import PDE.Spaces.Holder.On

/-!
# Hölder spaces

Classical Hölder exponents and the domain-restricted
$`C^{0,\gamma}` Banach space.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Hölder Spaces" =>

Hölder spaces record a quantitative form of continuity:
$`|f(x)-f(y)|` is controlled by a power $`d(x,y)^\gamma`. They are the natural
target of Morrey's supercritical Sobolev embeddings and the regularity class
in which many compactness and nonlinear arguments recover pointwise control.

For example, on $`[0,1]`,

$$`
|\sqrt{x}-\sqrt{y}|\leq |x-y|^{1/2}.
`

Thus $`f(x)=\sqrt{x}` is Hölder with exponent $`1/2` and constant one.
It is not Lipschitz there, because
$`|f(x)-f(0)|/|x-0|=x^{-1/2}` is unbounded as $`x\downarrow0`.
The exponent describes how quickly oscillation shrinks with distance; it
does not assert that a classical derivative exists or is bounded. A Hölder
seminorm also ignores additive constants, which is why the bounded Hölder
norm includes the size of the function itself.

Three layers must be kept separate. Mathlib's `HolderWith C γ f` is a
quantitative predicate with a specified constant $`C`; `MemHolder γ f` says
that some finite constant works; and `HolderSpace.C0GammaOn Ω γ` is the
completed normed space used as a target of Sobolev embeddings. The first two
layers and the least-constant construction come from Mathlib; PDEAtlas adds
only the completed space of bounded real-valued Hölder functions.

The domain parameter $`\Omega` is an arbitrary metric type. For a geometric
set $`\Omega\subseteq X`, one takes the subtype with its inherited metric; no
openness, measurability, Euclidean structure, or boundedness of the set is
needed to define the space. The functions themselves are required to be
bounded. Thus, on an unbounded domain this is the bounded Hölder space, not the
space of all Hölder functions.

Unlike a Sobolev graph space, this type stores an actual pointwise
representative. Equality is pointwise, evaluation is meaningful at every
point, and restriction is literal function restriction. A later Morrey
embedding therefore has two obligations: construct an element of this
representative space and prove that it agrees almost everywhere with the
original Sobolev coordinate.

:::group "sobolev.holder"
Hölder spaces
:::

# Exponents and Quantitative Hölder Control

:::definition "sobolev.holder.exponent" (parent := "sobolev.holder") (lean := "HolderSpace.Exponent, HolderSpace.Exponent.coe_one")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "254-255"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
`HolderSpace.Exponent` records the classical range
$`0<\gamma\leq 1` as a nonnegative real together with proofs of both
inequalities. Keeping the range in the type prevents every analytic theorem
from repeating the same side conditions.

The endpoint $`\gamma=1` is included and is available as the numeral `1`; it
is exactly the Lipschitz case. The exponent $`\gamma=0` is excluded, so every
exponent of this type gives continuity and not only an oscillation bound.
:::

:::definition "sobolev.holder.quantitative" (parent := "sobolev.holder") (lean := "HolderWith, MemHolder, nnHolderNorm") (uses := "sobolev.holder.exponent")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "254-255"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For metric spaces $`X,Y`, a map $`f:X\to Y` satisfies
`HolderWith C γ f` when

$$`
d_Y(f(x),f(y))\leq C\,d_X(x,y)^\gamma
\qquad\text{for every }x,y\in X.
`

`MemHolder γ f` means that such a finite nonnegative constant $`C` exists.
For a function satisfying this predicate, Mathlib's `nnHolderNorm γ f` is the
least admissible nonnegative Hölder constant and is itself admissible.
PDEAtlas uses this least constant as its Hölder seminorm.
:::

# The Completed Hölder Space

:::definition "sobolev.holder.c0gamma" (parent := "sobolev.holder") (lean := "HolderSpace.C0GammaOn, HolderSpace.C0GammaOn.ext, HolderSpace.C0GammaOn.continuous") (uses := "sobolev.holder.exponent, sobolev.holder.quantitative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "254-255"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Let $`\Omega` be a metric type and let $`0<\gamma\leq1`.
`HolderSpace.C0GammaOn Ω γ` consists of:

1. a bounded continuous function $`f:\Omega\to\mathbb R`; and
2. evidence that $`f` has a finite $`\gamma`-Hölder constant.

The first item supplies the uniform norm and global boundedness. The second
supplies quantitative regularity. Extensionality is pointwise: two elements
are equal exactly when their values agree at every point of $`\Omega`.

There is no almost-everywhere quotient. This is the target in which Morrey
theory records the continuous representative selected from a
Sobolev equivalence class.
:::

The structure certifies only that some Hölder constant is finite. Estimates
need a definite number attached to $`f`, and Mathlib's least admissible
constant supplies it without any new construction.

:::definition "sobolev.holder.seminorm" (parent := "sobolev.holder") (lean := "HolderSpace.C0GammaOn.holderSeminorm, HolderSpace.C0GammaOn.holderWith") (uses := "sobolev.holder.c0gamma, sobolev.holder.quantitative")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "254-255"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
For $`f\in C^{0,\gamma}(\Omega)`, the bundled seminorm is exactly

$$`
[f]_{C^{0,\gamma}(\Omega)}
  = \operatorname{nnHolderNorm}(\gamma,f).
`

This least constant is nonnegative and satisfies the pointwise estimate:

$$`
|f(x)-f(y)|
  \leq [f]_{C^{0,\gamma}(\Omega)}\,d(x,y)^\gamma.
`

Thus later estimates can bound the seminorm once and immediately recover the
corresponding pointwise modulus of continuity.
:::

Adding the uniform norm to the seminorm turns it into a norm: the seminorm
alone vanishes on constants, while the uniform norm alone forgets the modulus
of continuity. Completeness of the sum norm is what makes the space a
legitimate target for bounded embedding operators.

:::theorem "sobolev.holder.banach" (parent := "sobolev.holder") (lean := "HolderSpace.C0GammaOn.norm_def, HolderSpace.C0GammaOn.norm_toBoundedContinuousFunction_le, HolderSpace.C0GammaOn.holderSeminorm_le_norm, HolderSpace.C0GammaOn.instCompleteSpace") (uses := "sobolev.holder.seminorm")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "254-255"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
The real vector space `HolderSpace.C0GammaOn Ω γ` carries the norm

$$`
\|f\|_{C^{0,\gamma}(\Omega)}
  = \sup_{x\in\Omega}|f(x)|
    + [f]_{C^{0,\gamma}(\Omega)}.
`

Both summands are bounded by the full norm, and this norm makes the space
complete. Hence `C0GammaOn Ω γ` is a real Banach space for every metric type
$`\Omega`.
:::

:::proof "sobolev.holder.banach"
The triangle and scalar laws combine the corresponding laws for bounded
continuous functions with Mathlib's subadditivity and homogeneity of
`nnHolderNorm`.

For completeness, let $`f_j` be Cauchy in the displayed norm. The uniform
parts are Cauchy in the Banach space of bounded continuous functions, so they
converge uniformly to a bounded continuous function $`f`. A tail of the
sequence lies within distance one of a fixed term. Passing the pointwise
difference estimate to the uniform limit shows that this term minus $`f` is
$`\gamma`-Hölder, hence so is the limit. Repeating this with smaller tolerances makes $`f_j-f`
small in Hölder seminorm as well as uniformly, hence convergence in the
full norm.
:::

# Canonical Bounded Operators

:::definition "sobolev.holder.observation_operators" (parent := "sobolev.holder") (lean := "HolderSpace.C0GammaOn.toBoundedContinuousFunctionCLM, HolderSpace.C0GammaOn.toBoundedContinuousFunctionCLM_apply, HolderSpace.C0GammaOn.evalCLM, HolderSpace.C0GammaOn.evalCLM_apply, HolderSpace.C0GammaOn.norm_apply_le") (uses := "sobolev.holder.banach")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "254-255"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
There are canonical norm-at-most-one continuous linear maps

$$`
C^{0,\gamma}(\Omega)\longrightarrow C_b(\Omega),
\qquad f\longmapsto f,
`

and, for every $`x\in\Omega`,

$$`
\operatorname{ev}_x:C^{0,\gamma}(\Omega)\longrightarrow\mathbb R,
\qquad f\longmapsto f(x).
`

The estimates are immediate from the uniform-norm term:

$$`
\|f\|_\infty\leq\|f\|_{C^{0,\gamma}},
\qquad
|f(x)|\leq\|f\|_{C^{0,\gamma}}.
`

Later proofs use these maps to extract uniform or pointwise information from
a Hölder-space element.
:::

:::definition "sobolev.holder.restriction" (parent := "sobolev.holder") (lean := "HolderSpace.C0GammaOn.restrict, HolderSpace.C0GammaOn.restrict_apply, HolderSpace.C0GammaOn.norm_restrict_le, HolderSpace.C0GammaOn.restrictCLM, HolderSpace.C0GammaOn.restrictCLM_apply") (uses := "sobolev.holder.banach")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "254-255"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`S\subseteq Z` is a metric subspace, literal restriction defines a
continuous linear contraction

$$`
C^{0,\gamma}(Z)\longrightarrow C^{0,\gamma}(S),
\qquad f\longmapsto f|_S.
`

Restriction preserves every admissible Hölder constant, so neither the
uniform norm nor the least Hölder seminorm can increase:

$$`
\|f|_S\|_{C^{0,\gamma}(S)}
  \leq \|f\|_{C^{0,\gamma}(Z)}.
`

No measurability or extension hypothesis is involved. This is ordinary
pointwise restriction of continuous representatives, not the restriction
operator on Sobolev equivalence classes.
:::

# Interface with Morrey Embedding

The bounded Morrey embedding operator lands in `C0GammaOn`; composing with
the observation maps gives pointwise bounds, while `restrictCLM` transfers a
global representative to a domain. A separate almost-everywhere theorem
relates the selected continuous representative to the original Sobolev base
coordinate.
