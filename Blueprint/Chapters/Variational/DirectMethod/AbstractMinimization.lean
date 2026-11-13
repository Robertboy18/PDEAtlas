/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Variational.DirectMethod.WeakCompactness
import PDE.CalculusOfVariations.ConvexIntegral

/-!
# Abstract minimization by the direct method

Existence from bounded sublevels or coercivity, weak lower semicontinuity for
convex functionals, and uniqueness under strict convexity.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Abstract Minimization" =>

:::theorem "methods.direct_method.bounded_sublevel" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.exists_global_minimizer_of_weak_lowerSemicontinuous_of_bounded_sublevel") (uses := "analysis.weak_compactness.bounded_closed")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-471"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A weakly lower-semicontinuous real functional on a complete real Hilbert
space attains a global minimum if the sublevel through some supplied
$`x_0\in H` is norm bounded:

$$`
\{x\in H:J(x)\leq J(x_0)\}
\quad\text{is norm bounded}.
`

Then there is $`u\in H` such that $`J(u)\leq J(v)` for every $`v\in H`.
This is the compactness-plus-liminf core of the direct method.
:::

:::proof "methods.direct_method.bounded_sublevel" (uses := "analysis.weak_compactness.bounded_closed")
The sublevel through $`x_0` is weakly closed by lower semicontinuity, weakly
compact by boundedness, and nonempty because it contains $`x_0`. The
functional therefore attains a minimum there. That minimum is at most
$`J(x_0)`, while every point outside the sublevel has larger energy, so the
constrained minimum is global.
:::

The bounded-sublevel hypothesis must be checked at a specific point $`x_0`;
coercivity removes that bookkeeping.

:::theorem "methods.direct_method.coercive" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.exists_global_minimizer_of_weak_lowerSemicontinuous_of_coercive")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-471"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
If $`J:H\to\mathbb R` is weakly lower semicontinuous and coercive,

$$`
\lVert x\rVert\longrightarrow\infty
\quad\Longrightarrow\quad J(x)\longrightarrow\infty,
`

then $`J` has a global minimizer.
:::

:::proof "methods.direct_method.coercive" (uses := "methods.direct_method.bounded_sublevel")
Coercivity makes the sublevel through the origin norm bounded. Apply the
bounded-sublevel direct-method theorem to that nonempty sublevel.
:::

Both existence theorems assume lower semicontinuity for the weak topology, a
hypothesis that is awkward to verify directly because weakly convergent nets
need not converge in norm. Convexity is the standard way to obtain it from the
norm topology.

:::theorem "methods.direct_method.convex_weak_lsc" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.lowerSemicontinuous_weakSpace_of_convex")
%%%
source := {
  document := "evans-pde"
  spans := #[
    {
      page := "467-470"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    },
    {
      page := "723"
      text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
    }
  ]
}
%%%
Every convex real functional on a real normed space that is lower semicontinuous in norm
is lower semicontinuous for the weak topology:

$$`
x_\alpha\rightharpoonup x
\quad\Longrightarrow\quad
J(x)\leq\liminf_\alpha J(x_\alpha).
`

This is the functional-analytic step behind Evans's integral-functional
argument.
:::

:::proof "methods.direct_method.convex_weak_lsc"
For every real $`a`, the sublevel $`\{x:J(x)\leq a\}` is convex because
$`J` is convex and norm closed because $`J` is norm lower semicontinuous. A
norm-closed convex set is weakly closed by Hahn–Banach separation. Thus every
sublevel is weakly closed, which is equivalent to lower semicontinuity of
$`J` in the weak topology.
:::

Combined with the coercive existence theorem, this criterion removes the weak
topology from the hypotheses. Completeness of $`H` is still required, since
the weak compactness theorem uses it.

:::theorem "methods.direct_method.convex_minimizer" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.exists_global_minimizer_of_convex_lowerSemicontinuous_of_coercive")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "465-471"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
A convex functional on a complete real Hilbert space has a global minimizer
if it is lower semicontinuous in norm and coercive:

$$`
\exists u\in H,\qquad J(u)=\inf_{v\in H}J(v).
`
:::

:::proof "methods.direct_method.convex_minimizer" (uses := "methods.direct_method.coercive, methods.direct_method.convex_weak_lsc")
Convexity and norm lower semicontinuity give weak lower semicontinuity. The
coercive direct method theorem then supplies a minimizer.
:::

Convexity alone leaves room for a whole convex set of minimizers, as a constant
functional shows. Strict convexity excludes this: the midpoint of two distinct
minimizers would have strictly smaller energy.

:::theorem "methods.direct_method.unique_minimizer" (parent := "methods.direct_method") (lean := "PDE.CalculusOfVariations.existsUnique_global_minimizer_of_strictConvex_lowerSemicontinuous_of_coercive")
%%%
source := {
  document := "evans-pde"
  spans := #[{
    page := "471-472"
    text := some { path := "Blueprint/Sources/Evans.md", startLine := 1, endLine := 9 }
  }]
}
%%%
Strict convexity upgrades the direct-method conclusion to a unique global
minimizer:

$$`
\exists!\,u\in H,\qquad \forall v\in H,\ J(u)\leq J(v).
`
:::

:::proof "methods.direct_method.unique_minimizer" (uses := "methods.direct_method.convex_weak_lsc")
Strict convexity supplies convexity, so the argument with closed convex sublevel sets
gives weak lower semicontinuity. The weak direct method gives existence, and
strict convexity identifies any two global minimizers.
:::
