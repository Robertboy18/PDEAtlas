/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoManual.Bibliography

/-!
# Bibliography entries

This module registers the books and research articles cited inline by the
Blueprint: textbook references for the chapters and the primary articles behind
particular theorems. Local provenance records for structured theorem-card
annotations remain in `Blueprint/Sources`; the entries below provide ordinary
scholarly citations beside the relevant mathematical claims. Verso's
bibliography knows articles, proceedings, theses and arXiv preprints, so books
are recorded as articles whose journal field names the series and publisher.
-/

open Verso
open Verso.Genre
open Verso.Genre.Manual

namespace Blueprint.Bibliography

/-- Banach's paper on abstract spaces and integral equations. -/
@[bib "banach-1922"]
def banach1922 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := .concat #[
      inlines!"Sur les opérations dans les ensembles abstraits et leur ",
      inlines!"application aux équations intégrales"
    ]
  , authors := #[inlines!"Stefan Banach"]
  , journal := inlines!"Fundamenta Mathematicae"
  , year := 1922
  , month := none
  , volume := inlines!"3"
  , number := inlines!"1"
  , pages := some (133, 181)
  , url := some "https://eudml.org/doc/213289"
  }

/-- Schauder's fixed-point theorem in function spaces. -/
@[bib "schauder-1930"]
def schauder1930 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Der Fixpunktsatz in Funktionalräumen"
  , authors := #[inlines!"Juliusz Schauder"]
  , journal := inlines!"Studia Mathematica"
  , year := 1930
  , month := none
  , volume := inlines!"2"
  , number := inlines!"1"
  , pages := some (171, 180)
  , url :=
      some <|
        "https://www.impan.pl/en/publishing-house/journals-and-series/" ++
        "studia-mathematica/all/2/1/92886/der-fixpunktsatz-in-funktionalraumen"
  }

/-- Minty's paper on monotone operators in Hilbert space. -/
@[bib "minty-1962"]
def minty1962 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Monotone (nonlinear) operators in Hilbert space"
  , authors := #[inlines!"George J. Minty"]
  , journal := inlines!"Duke Mathematical Journal"
  , year := 1962
  , month := none
  , volume := inlines!"29"
  , number := inlines!"3"
  , pages := some (341, 346)
  , url := some "https://projecteuclid.org/euclid.dmj/1077470178"
  }

/-- Browder's variational treatment of quasilinear elliptic problems. -/
@[bib "browder-1963"]
def browder1963 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := .concat #[
      inlines!"Variational boundary value problems for quasi-linear elliptic ",
      inlines!"equations of arbitrary order"
    ]
  , authors := #[inlines!"Felix E. Browder"]
  , journal := inlines!"Proceedings of the National Academy of Sciences"
  , year := 1963
  , month := none
  , volume := inlines!"50"
  , number := inlines!"1"
  , pages := some (31, 37)
  , url := some "https://doi.org/10.1073/pnas.50.1.31"
  }

/-- Leray's whole-space viscous-fluid paper. -/
@[bib "leray-1934"]
def leray1934 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Sur le mouvement d'un liquide visqueux emplissant l'espace"
  , authors := #[inlines!"Jean Leray"]
  , journal := inlines!"Acta Mathematica"
  , year := 1934
  , month := none
  , volume := inlines!"63"
  , number := inlines!""
  , pages := some (193, 248)
  , url :=
      some <|
        "https://projecteuclid.org/journals/acta-mathematica/volume-63/" ++
        "issue-none/Sur-le-mouvement-dun-liquide-visqueux-emplissant-lespace/" ++
        "10.1007/BF02547354.full"
  }

/-- Caffarelli, Kohn, and Nirenberg on Navier–Stokes partial regularity. -/
@[bib "caffarelli-kohn-nirenberg-1982"]
def caffarelliKohnNirenberg1982 :
    Verso.Genre.Manual.Bibliography.Citable := .article
  { title :=
      inlines!"Partial regularity of suitable weak solutions of the Navier–Stokes equations"
  , authors :=
      #[inlines!"Luis Caffarelli", inlines!"Robert Kohn", inlines!"Louis Nirenberg"]
  , journal := inlines!"Communications on Pure and Applied Mathematics"
  , year := 1982
  , month := none
  , volume := inlines!"35"
  , number := inlines!"6"
  , pages := some (771, 831)
  , url := some "https://onlinelibrary.wiley.com/doi/10.1002/cpa.3160350604"
  }

/-- Serrin's treatment of the Navier–Stokes initial-value problem. -/
@[bib "serrin-1962"]
def serrin1962 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title :=
      inlines!"On the interior regularity of weak solutions of the Navier–Stokes equations"
  , authors := #[inlines!"James Serrin"]
  , journal := inlines!"Archive for Rational Mechanics and Analysis"
  , year := 1962
  , month := none
  , volume := inlines!"9"
  , number := inlines!""
  , pages := some (187, 195)
  , url := some "https://link.springer.com/article/10.1007/BF00253344"
  }

/-- Escauriaza, Seregin, and Šverák's Navier–Stokes regularity criterion. -/
@[bib "escauriaza-seregin-sverak-2003"]
def escauriazaSereginSverak2003 :
    Verso.Genre.Manual.Bibliography.Citable := .article
  { title :=
      inlines!"L₃,∞-solutions of Navier–Stokes equations and backward uniqueness"
  , authors :=
      #[inlines!"Luis Escauriaza", inlines!"Gregory Seregin", inlines!"Vladimir Šverák"]
  , journal := inlines!"Russian Mathematical Surveys"
  , year := 2003
  , month := none
  , volume := inlines!"58"
  , number := inlines!"2"
  , pages := some (211, 250)
  , url :=
      some "https://iopscience.iop.org/article/10.1070/RM2003v058n02ABEH000609"
  }

/-- Ukhovskii and Yudovich on axially symmetric fluid flows. -/
@[bib "ukhovskii-yudovich-1968"]
def ukhovskiiYudovich1968 :
    Verso.Genre.Manual.Bibliography.Citable := .article
  { title := .concat #[
      inlines!"Axially symmetric flows of ideal and viscous fluids ",
      inlines!"filling the whole space"
    ]
  , authors := #[inlines!"M. R. Ukhovskii", inlines!"V. I. Yudovich"]
  , journal := inlines!"Journal of Applied Mathematics and Mechanics"
  , year := 1968
  , month := none
  , volume := inlines!"32"
  , number := inlines!"1"
  , pages := some (52, 62)
  , url := some "https://doi.org/10.1016/0021-8928(68)90147-0"
  }

/-- Di Nezza, Palatucci, and Valdinoci on fractional Sobolev spaces. -/
@[bib "di-nezza-palatucci-valdinoci-2012"]
def diNezzaPalatucciValdinoci2012 :
    Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Hitchhiker's guide to the fractional Sobolev spaces"
  , authors := #[
      inlines!"Eleonora Di Nezza",
      inlines!"Giampiero Palatucci",
      inlines!"Enrico Valdinoci"
    ]
  , journal := inlines!"Bulletin des Sciences Mathématiques"
  , year := 2012
  , month := none
  , volume := inlines!"136"
  , number := inlines!"5"
  , pages := some (521, 573)
  , url := some "https://doi.org/10.1016/j.bulsci.2011.12.004"
  }

/-- The second edition of Evans, used for the book's main PDE sequence and coverage map. -/
@[bib "evans-2010"]
def evans2010 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Partial Differential Equations, Second Edition"
  , authors := #[inlines!"Lawrence C. Evans"]
  , journal := inlines!"Graduate Studies in Mathematics, American Mathematical Society"
  , year := 2010
  , month := none
  , volume := inlines!"19"
  , number := inlines!""
  , pages := none
  , url := some "https://www.ams.org/bookpages/gsm-19-r"
  }

/-- Cambridge records print publication in 2001; the existing citation ID is retained. -/
@[bib "majda-bertozzi-2002"]
def majdaBertozzi2002 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Vorticity and Incompressible Flow"
  , authors := #[inlines!"Andrew J. Majda", inlines!"Andrea L. Bertozzi"]
  , journal := inlines!"Cambridge Texts in Applied Mathematics, Cambridge University Press"
  , year := 2001
  , month := none
  , volume := inlines!"27"
  , number := inlines!""
  , pages := none
  , url := some "https://doi.org/10.1017/CBO9780511613203"
  }

/-- Volume I of Lions and Magenes, cited for boundary-value and evolution-space theory. -/
@[bib "lions-magenes-1972"]
def lionsMagenes1972 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Non-Homogeneous Boundary Value Problems and Applications, Volume I"
  , authors := #[inlines!"Jacques-Louis Lions", inlines!"Enrico Magenes"]
  , journal := inlines!"Grundlehren der mathematischen Wissenschaften, Springer"
  , year := 1972
  , month := none
  , volume := inlines!"181"
  , number := inlines!""
  , pages := none
  , url := some "https://doi.org/10.1007/978-3-642-65161-8"
  }

/-- Temam's Navier–Stokes reference in its AMS Chelsea edition. -/
@[bib "temam-2001"]
def temam2001 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Navier–Stokes Equations: Theory and Numerical Analysis"
  , authors := #[inlines!"Roger Temam"]
  , journal := inlines!"AMS Chelsea Publishing, American Mathematical Society"
  , year := 2001
  , month := none
  , volume := inlines!"343"
  , number := inlines!""
  , pages := none
  , url := some "https://bookstore.ams.org/chel-343-h"
  }

/-- Springer's record dates volume 146 to 1986; the existing citation ID is retained. -/
@[bib "simon-1987"]
def simon1987 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Compact sets in the space Lᵖ(0,T;B)"
  , authors := #[inlines!"Jacques Simon"]
  , journal := inlines!"Annali di Matematica Pura ed Applicata"
  , year := 1986
  , month := none
  , volume := inlines!"146"
  , number := inlines!""
  , pages := some (65, 96)
  , url := some "https://doi.org/10.1007/BF01762360"
  }

/-- Marcus and Mizel on absolute continuity and Sobolev mappings. -/
@[bib "marcus-mizel-1972"]
def marcusMizel1972 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Absolute continuity on tracks and mappings of Sobolev spaces"
  , authors := #[inlines!"Moshe Marcus", inlines!"Victor J. Mizel"]
  , journal := inlines!"Archive for Rational Mechanics and Analysis"
  , year := 1972
  , month := none
  , volume := inlines!"45"
  , number := inlines!""
  , pages := some (294, 320)
  , url := some "https://doi.org/10.1007/BF00251378"
  }

/-- Crandall and Lions on viscosity solutions of Hamilton–Jacobi equations. -/
@[bib "crandall-lions-1983"]
def crandallLions1983 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Viscosity solutions of Hamilton–Jacobi equations"
  , authors := #[inlines!"Michael G. Crandall", inlines!"Pierre-Louis Lions"]
  , journal := inlines!"Transactions of the American Mathematical Society"
  , year := 1983
  , month := none
  , volume := inlines!"277"
  , number := inlines!"1"
  , pages := some (1, 42)
  , url := some "https://doi.org/10.1090/S0002-9947-1983-0690039-8"
  }

/-- Chen and Hou on nearly self-similar Boussinesq and Euler blowup. -/
@[bib "chen-hou-2022"]
def chenHou2022 : Verso.Genre.Manual.Bibliography.Citable := .arXiv
  { title := .concat #[
      inlines!"Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler ",
      inlines!"equations with smooth data I: Analysis"
    ]
  , authors := #[inlines!"Jiajie Chen", inlines!"Thomas Y. Hou"]
  , year := 2022
  , id := "2210.07191"
  }

/-- Hou, Wang, and Yang's numerical validation framework and unforced nonuniqueness result. -/
@[bib "hou-wang-yang-2025"]
def houWangYang2025 : Verso.Genre.Manual.Bibliography.Citable := .arXiv
  { title := .concat #[
      inlines!"Nonuniqueness of Leray–Hopf solutions to the unforced incompressible ",
      inlines!"3D Navier–Stokes Equation"
    ]
  , authors := #[inlines!"Thomas Hou", inlines!"Yixuan Wang", inlines!"Changhe Yang"]
  , year := 2025
  , id := "2509.25116"
  }

/-- Moore's reference on interval analysis. -/
@[bib "moore-1966"]
def moore1966 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Interval Analysis"
  , authors := #[inlines!"Ramon E. Moore"]
  , journal := inlines!"Prentice-Hall Series in Automatic Computation"
  , year := 1966
  , month := none
  , volume := inlines!"Prentice-Hall"
  , number := inlines!""
  , pages := none
  , url := none
  }

/-- Neumaier's reference on interval methods for systems of equations. -/
@[bib "neumaier-1990"]
def neumaier1990 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Interval Methods for Systems of Equations"
  , authors := #[inlines!"Arnold Neumaier"]
  , journal := inlines!"Encyclopedia of Mathematics and its Applications, Cambridge University Press"
  , year := 1990
  , month := none
  , volume := inlines!"37"
  , number := inlines!""
  , pages := none
  , url := some "https://doi.org/10.1017/CBO9780511526473"
  }

/-- Mathlib's architecture and community organization. -/
@[bib "mathlib-2020"]
def mathlib2020 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"The Lean mathematical library"
  , authors := #[inlines!"The mathlib Community"]
  , journal := .concat #[
      inlines!"Proceedings of the 9th ACM SIGPLAN International Conference ",
      inlines!"on Certified Programs and Proofs"
    ]
  , year := 2020
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := some (367, 381)
  , url := some "https://doi.org/10.1145/3372885.3373824"
  }

/-- Tao's teaching companion documents its transition from textbook definitions to Mathlib. -/
@[bib "tao-analysis-2026"]
def taoAnalysis2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Lean formalization of Analysis I"
  , authors := #[inlines!"Terence Tao", inlines!"Analysis contributors"]
  , journal := inlines!"Software repository, inspected 17 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/teorth/analysis/tree/" ++
      "245b2e16e2501170cd3d2c234edf74d298dbdc60"
  }

/-- Tau Ceti's library and review model, at the inspected September snapshot. -/
@[bib "tauceti-2026"]
def tauCeti2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Tau Ceti"
  , authors := #[inlines!"Tau Ceti contributors"]
  , journal := inlines!"Software repository, inspected 16 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/TauCetiProject/TauCeti/tree/" ++
      "0ce0e8862fb5aeb94a921ab5dc54e2fce17c2d0b"
  }

/-- The PDE roadmap describes targets, not a completed-theorem inventory. -/
@[bib "tauceti-pde-roadmap-2026"]
def tauCetiPdeRoadmap2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Tau Ceti Roadmap: Partial Differential Equations"
  , authors := #[inlines!"Tau Ceti Roadmap contributors"]
  , journal := inlines!"Project roadmap, inspected 4 October 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/TauCetiProject/TauCetiRoadmap/blob/" ++
      "ce57cca0e3bb6a449a7e320b0844bf750b20969c/TauCetiRoadmap/PDE/README.md"
  }

/-- The De Giorgi–Nash–Moser formalization and its analytic scope. -/
@[bib "armstrong-kempe-2026"]
def armstrongKempe2026 : Verso.Genre.Manual.Bibliography.Citable := .arXiv
  { title := inlines!"Formalization of De Giorgi–Nash–Moser Theory in Lean"
  , authors := #[inlines!"Scott Armstrong", inlines!"Julia Kempe"]
  , year := 2026
  , id := "2604.05984"
  }

/-- The uniformly elliptic, isotropic public comparison theorem and scope map. -/
@[bib "armstrong-kuusi-coarsegraining-2026"]
def armstrongKuusiCoarseGraining2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"CoarseGraining: Coarse-Graining Theory for Elliptic Equations"
  , authors := #[inlines!"Scott Armstrong", inlines!"Tuomo Kuusi"]
  , journal := inlines!"Lean formalization, inspected 16 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/scottnarmstrong/CoarseGraining/tree/" ++
      "28ca42c02fd286c8f63a45be3344f6f82d026db3"
  }

/-- The model-conditional formalization of Armstrong–Bou-Rabee–Kuusi's paper. -/
@[bib "armstrong-kuusi-superdiffusion-2026"]
def armstrongKuusiSuperdiffusion2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := .concat #[
      inlines!"Superdiffusion: a Lean formalization of superdiffusion and ",
      inlines!"anomalous regularization in self-similar random incompressible flows"
    ]
  , authors := #[inlines!"Scott Armstrong", inlines!"Tuomo Kuusi"]
  , journal := inlines!"Lean formalization, inspected 16 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/scottnarmstrong/Superdiffusion/tree/" ++
      "0aca1d55e9ed3ea20ab874f08fe245da77aebfbd"
  }

/-- Uda's exact public weak-solution contract, including its test-class limits. -/
@[bib "uda-leray-hopf-2026"]
def udaLerayHopf2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"leray-hopf: Exact claims and scope"
  , authors := #[inlines!"Tomoki Uda"]
  , journal := inlines!"Lean formalization, inspected 16 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/uda-lab/leray-hopf/blob/" ++
      "e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc/docs/claims-and-scope.md"
  }

/-- The expanded Lewis–Wu interface paper; the 2017 predecessor is by Lewis alone. -/
@[bib "lewis-wu-2021"]
def lewisWu2021 : Verso.Genre.Manual.Bibliography.Citable := .arXiv
  { title := inlines!"A bi-directional extensible interface between Lean and Mathematica"
  , authors := #[inlines!"Robert Y. Lewis", inlines!"Minchao Wu"]
  , year := 2021
  , id := "2101.07758"
  }

/-- Released verified computational algebra libraries and Mathlib correspondence layers. -/
@[bib "hex-2026"]
def hex2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Hex: Verified computational algebra in Lean 4"
  , authors := #[inlines!"Hex contributors"]
  , journal := inlines!"Software repository, inspected 16 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/leanprover/hex/tree/" ++
      "b1bbb21e49afaad67dc36df58f5821205c999705"
  }

/-- A verified PDE numerical program with method and roundoff error bounds. -/
@[bib "boldo-et-al-wave-2013"]
def boldoEtAlWave2013 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := .concat #[
      inlines!"Wave Equation Numerical Resolution: ",
      inlines!"a Comprehensive Mechanized Proof of a C Program"
    ]
  , authors := #[
      inlines!"Sylvie Boldo", inlines!"François Clément",
      inlines!"Jean-Christophe Filliâtre", inlines!"Micaela Mayero",
      inlines!"Guillaume Melquiond", inlines!"Pierre Weis"
    ]
  , journal := inlines!"Journal of Automated Reasoning"
  , year := 2013
  , month := none
  , volume := inlines!"50"
  , number := inlines!"4"
  , pages := some (423, 456)
  , url := some "https://doi.org/10.1007/s10817-012-9255-4"
  }

/-- The primary documentation of Rocq's Interval library. -/
@[bib "rocq-interval-2026"]
def rocqInterval2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Interval Package for Rocq"
  , authors := #[inlines!"Guillaume Melquiond", inlines!"Interval contributors"]
  , journal := inlines!"Software documentation, accessed 16 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://coqinterval.gitlabpages.inria.fr/"
  }

/-- LeanCert's supported certificates and explicit kernel/native evaluation modes. -/
@[bib "leancert-2026"]
def leanCert2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"LeanCert: Certified numerics for Lean 4"
  , authors := #[inlines!"LeanCert contributors"]
  , journal := inlines!"Software repository, inspected 16 September 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/alerad/leancert/tree/" ++
      "4ea18bb66dfcd7f18f260bc25302400f5a3cafd7"
  }

/-- The July 2024 question, existing-analysis pointers, and replies about developing PDEs. -/
@[bib "george-pde-zulip-2024"]
def georgePdeZulip2024 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Formalization of PDEs in Lean?"
  , authors := #[inlines!"Robert Joseph George", inlines!"Lean Zulip contributors"]
  , journal := inlines!"Lean Zulip, general stream, 14–16 July 2024"
  , year := 2024
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://leanprover-community.github.io/archive/stream/113488-general/topic/" ++
      "Formalization.20of.20PDEs.20in.20Lean.3F.html"
  }

/-- The inclusion engine and dyadic family at LeanPDE's pinned Mathlib revision. -/
@[bib "mathlib-inclusion-2026"]
def mathlibInclusion2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"inclusion: Extensible enclosure computation in Mathlib"
  , authors := #[inlines!"David Ledvinka", inlines!"Mathlib contributors"]
  , journal := inlines!"Mathlib source at the v4.35.0 release"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/leanprover-community/mathlib4/tree/" ++
      "56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Tactic/Inclusion"
  }

/-- Proposed canonical univariate polynomials; the PR was open on 2 October 2026. -/
@[bib "mathlib-sparsepoly-2026"]
def mathlibSparsePoly2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"SparsePoly: A computable univariate polynomial"
  , authors := #[inlines!"Michail Karatarakis"]
  , journal := inlines!"Mathlib pull request 41339, inspected 2 October 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://github.com/leanprover-community/mathlib4/pull/41339"
  }

/-- Proposed canonical multivariate polynomials; the PR was open on 2 October 2026. -/
@[bib "mathlib-mvsparsepoly-2026"]
def mathlibMvSparsePoly2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"MvSparsePoly: A computable multivariate polynomial"
  , authors := #[inlines!"Michail Karatarakis"]
  , journal := inlines!"Mathlib pull request 41350, inspected 2 October 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://github.com/leanprover-community/mathlib4/pull/41350"
  }

/-- Proposed quotient search with a checked identity; open on 2 October 2026. -/
@[bib "mathlib-poly-dvd-cert-2026"]
def mathlibPolyDvdCert2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"poly_dvd_cert: Certificate-based polynomial divisibility"
  , authors := #[inlines!"Michail Karatarakis"]
  , journal := inlines!"Mathlib pull request 41347, inspected 2 October 2026"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://github.com/leanprover-community/mathlib4/pull/41347"
  }

/-- FloatLib at the revision SymLean pins, including its real interval semantics. -/
@[bib "floatlib-2026"]
def floatLib2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"FloatLib: Executable numerical representations and correctness proofs"
  , authors := #[inlines!"Robert Joseph George", inlines!"Will Adkisson",
      inlines!"Anima Anandkumar"]
  , journal := inlines!"Software repository"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/lean-dojo/FloatLib/tree/" ++
      "0fe4f0496153a1a494115af1fbcb825069cb4017"
  }

/-- An inspected TorchLean revision using FloatLib in another Lean development. -/
@[bib "torchlean-2026"]
def torchLean2026 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"TorchLean"
  , authors := #[inlines!"TorchLean contributors"]
  , journal := inlines!"Software repository"
  , year := 2026
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some <|
      "https://github.com/lean-dojo/TorchLean/tree/" ++
      "b266059680757d2b25ac1b463cddcf5cee0a070e"
  }

/-- Classical elliptic equations and Green functions. -/
@[bib "gilbarg-trudinger-2001"]
def gilbargTrudinger2001 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Elliptic Partial Differential Equations of Second Order"
  , authors := #[inlines!"David Gilbarg", inlines!"Neil S. Trudinger"]
  , journal := inlines!"Classics in Mathematics, Springer"
  , year := 2001
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://link.springer.com/book/10.1007/978-3-642-61798-0"
  }

/-- Functional analysis and the variational treatment of PDE. -/
@[bib "brezis-2011"]
def brezis2011 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Functional Analysis, Sobolev Spaces and Partial Differential Equations"
  , authors := #[inlines!"Haim Brezis"]
  , journal := inlines!"Universitext, Springer"
  , year := 2011
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://link.springer.com/book/10.1007/978-0-387-70914-7"
  }

/-- Sobolev spaces and their embedding theorems. -/
@[bib "adams-fournier-2003"]
def adamsFournier2003 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Sobolev Spaces, second edition"
  , authors := #[inlines!"Robert A. Adams", inlines!"John J. F. Fournier"]
  , journal := inlines!"Pure and Applied Mathematics, Academic Press"
  , year := 2003
  , month := none
  , volume := inlines!"140"
  , number := inlines!""
  , pages := none
  , url := some "https://www.sciencedirect.com/bookseries/pure-and-applied-mathematics/vol/140/suppl/C"
  }

/-- The classical geometric treatment of partial differential equations. -/
@[bib "courant-hilbert-1962"]
def courantHilbert1962 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Methods of Mathematical Physics, Volume II: Partial Differential Equations"
  , authors := #[inlines!"Richard Courant", inlines!"David Hilbert"]
  , journal := inlines!"Interscience"
  , year := 1962
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://onlinelibrary.wiley.com/doi/book/10.1002/9783527617234"
  }

/-- Gaussian bounds for uniformly parabolic fundamental solutions. -/
@[bib "aronson-1967"]
def aronson1967 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Bounds for the fundamental solution of a parabolic equation"
  , authors := #[inlines!"D. G. Aronson"]
  , journal := inlines!"Bulletin of the American Mathematical Society"
  , year := 1967
  , month := none
  , volume := inlines!"73"
  , number := inlines!""
  , pages := some (890, 896)
  , url := some "https://doi.org/10.1090/S0002-9904-1967-11830-5"
  }

/-- The viscosity-solution reference used in the Hamilton–Jacobi discussion. -/
@[bib "crandall-ishii-lions-1992"]
def crandallIshiiLions1992 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"User's guide to viscosity solutions of second order partial differential equations"
  , authors := #[inlines!"Michael G. Crandall", inlines!"Hitoshi Ishii", inlines!"Pierre-Louis Lions"]
  , journal := inlines!"Bulletin of the American Mathematical Society"
  , year := 1992
  , month := none
  , volume := inlines!"27"
  , number := inlines!""
  , pages := some (1, 67)
  , url := some "https://www.ams.org/bull/1992-27-01/S0273-0979-1992-00266-5/"
  }

/-- Type-II blowup for an energy-supercritical nonlinear heat equation. -/
@[bib "collot-2017"]
def collot2017 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Nonradial type II blow up for the energy-supercritical semilinear heat equation"
  , authors := #[inlines!"Charles Collot"]
  , journal := inlines!"Analysis & PDE"
  , year := 2017
  , month := none
  , volume := inlines!"10"
  , number := inlines!""
  , pages := some (127, 252)
  , url := some "https://msp.org/apde/2017/10-1/p04.xhtml"
  }

/-- The broader theory of elementary symbolic integration. -/
@[bib "risch-1969"]
def risch1969 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"The problem of integration in finite terms"
  , authors := #[inlines!"Robert H. Risch"]
  , journal := inlines!"Transactions of the American Mathematical Society"
  , year := 1969
  , month := none
  , volume := inlines!"139"
  , number := inlines!""
  , pages := some (167, 189)
  , url := some "https://www.ams.org/tran/1969-139-00/S0002-9947-1969-0237477-8/"
  }

/-- Algorithms for integration of transcendental expressions. -/
@[bib "bronstein-2005"]
def bronstein2005 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Symbolic Integration I: Transcendental Functions, second edition"
  , authors := #[inlines!"Manuel Bronstein"]
  , journal := inlines!"Algorithms and Computation in Mathematics, Springer"
  , year := 2005
  , month := none
  , volume := inlines!"1"
  , number := inlines!""
  , pages := none
  , url := some "https://link.springer.com/book/10.1007/b138171"
  }

/-- Taylor models in verified ODE integration. -/
@[bib "berz-makino-1998"]
def berzMakino1998 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := .concat #[
      inlines!"Verified integration of ODEs and flows using differential algebraic methods on ",
      inlines!"high-order Taylor models"
    ]
  , authors := #[inlines!"Martin Berz", inlines!"Kyoko Makino"]
  , journal := inlines!"Reliable Computing"
  , year := 1998
  , month := none
  , volume := inlines!"4"
  , number := inlines!""
  , pages := some (361, 369)
  , url := some "https://bt.pa.msu.edu/cgi-bin/display.pl?name=BM98"
  }

/-- Taylor models and validated functional inclusion methods. -/
@[bib "makino-berz-2003"]
def makinoBerz2003 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Taylor models and other validated functional inclusion methods"
  , authors := #[inlines!"Kyoko Makino", inlines!"Martin Berz"]
  , journal := inlines!"International Journal of Pure and Applied Mathematics"
  , year := 2003
  , month := none
  , volume := inlines!"4"
  , number := inlines!""
  , pages := some (379, 456)
  , url := some "https://bt.pa.msu.edu/pub/papers/TMIJPAM03.pdf"
  }

/-- Exact and multiple-precision arithmetic. -/
@[bib "brent-zimmermann-2010"]
def brentZimmermann2010 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Modern Computer Arithmetic"
  , authors := #[inlines!"Richard P. Brent", inlines!"Paul Zimmermann"]
  , journal := inlines!"Cambridge Tracts in Applied Mathematics, Cambridge University Press"
  , year := 2010
  , month := none
  , volume := inlines!"18"
  , number := inlines!""
  , pages := none
  , url := some "https://maths-people.anu.edu.au/~brent/pub/pub237.html"
  }

/-- The original memoir on real-root counting. -/
@[bib "sturm-1835"]
def sturm1835 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Mémoire sur la résolution des équations numériques"
  , authors := #[inlines!"Charles Sturm"]
  , journal := .concat #[
      inlines!"Mémoires présentés par divers savants à l'Académie royale des sciences de ",
      inlines!"l'Institut de France"
    ]
  , year := 1835
  , month := none
  , volume := inlines!"6"
  , number := inlines!""
  , pages := some (271, 318)
  , url := none
  }

/-- A formal construction of real algebraic numbers in Coq. -/
@[bib "cohen-2012"]
def cohen2012 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Construction of real algebraic numbers in Coq"
  , authors := #[inlines!"Cyril Cohen"]
  , journal := inlines!"ITP 2012, Lecture Notes in Computer Science, Springer"
  , year := 2012
  , month := none
  , volume := inlines!"7406"
  , number := inlines!""
  , pages := some (67, 82)
  , url := some "https://link.springer.com/chapter/10.1007/978-3-642-32347-8_6"
  }

/-- Verified univariate real arithmetic using Sturm sequences. -/
@[bib "eberl-2015"]
def eberl2015 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"A decision procedure for univariate real arithmetic with Sturm's theorem in Isabelle/HOL"
  , authors := #[inlines!"Manuel Eberl"]
  , journal := inlines!"CPP 2015, ACM"
  , year := 2015
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , pages := none
  , url := some "https://www21.in.tum.de/~eberlm/sturm.pdf"
  }

/-- Decision procedures justified by reflection. -/
@[bib "boutin-1997"]
def boutin1997 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Using reflection to build efficient and certified decision procedures"
  , authors := #[inlines!"Samuel Boutin"]
  , journal := inlines!"TACS 1997, Lecture Notes in Computer Science, Springer"
  , year := 1997
  , month := none
  , volume := inlines!"1281"
  , number := inlines!""
  , pages := some (515, 529)
  , url := some "https://link.springer.com/chapter/10.1007/BFb0014565"
  }

/-- A reflected ring procedure in Coq. -/
@[bib "gregoire-mahboubi-2005"]
def gregoireMahboubi2005 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Proving Equalities in a Commutative Ring Done Right in Coq"
  , authors := #[inlines!"Benjamin Grégoire", inlines!"Assia Mahboubi"]
  , journal := inlines!"TPHOLs 2005, Lecture Notes in Computer Science, Springer"
  , year := 2005
  , month := none
  , volume := inlines!"3603"
  , number := inlines!""
  , pages := none
  , url := some "https://link.springer.com/chapter/10.1007/11541868_7"
  }

/-- Proved nonlinear inequalities through sums of squares. -/
@[bib "harrison-2007"]
def harrison2007 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Verifying Nonlinear Real Formulas Via Sums of Squares"
  , authors := #[inlines!"John Harrison"]
  , journal := inlines!"TPHOLs 2007, Lecture Notes in Computer Science, Springer"
  , year := 2007
  , month := none
  , volume := inlines!"4732"
  , number := inlines!""
  , pages := some (102, 118)
  , url := some "https://link.springer.com/chapter/10.1007/978-3-540-74591-4_9"
  }

/-- Numerical bounds obtained through checked computation. -/
@[bib "melquiond-2008"]
def melquiond2008 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Proving Bounds on Real-Valued Functions with Computations"
  , authors := #[inlines!"Guillaume Melquiond"]
  , journal := inlines!"IJCAR 2008, Lecture Notes in Computer Science, Springer"
  , year := 2008
  , month := none
  , volume := inlines!"5195"
  , number := inlines!""
  , pages := some (2, 17)
  , url := some "https://inria.hal.science/inria-00333090/document"
  }

/-- The implementation and design of Lean 4. -/
@[bib "de-moura-ullrich-2021"]
def deMouraUllrich2021 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"The Lean 4 Theorem Prover and Programming Language"
  , authors := #[inlines!"Leonardo de Moura", inlines!"Sebastian Ullrich"]
  , journal := inlines!"CADE 28, Lecture Notes in Computer Science, Springer"
  , year := 2021
  , month := none
  , volume := inlines!"12699"
  , number := inlines!""
  , pages := some (625, 635)
  , url := some "https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37"
  }

/-- Keller–Segel blowup with logistic damping in 3D; the parabolic chapter uses its scaling. -/
@[bib "liu-wang-zhou-2025"]
def liuWangZhou2025 : Verso.Genre.Manual.Bibliography.Citable := .arXiv
  { title := .concat #[
      inlines!"Finite time blowup for Keller-Segel equation with logistic damping ",
      inlines!"in three dimensions"
    ]
  , authors := #[inlines!"Jiaqi Liu", inlines!"Yixuan Wang", inlines!"Tao Zhou"]
  , year := 2025
  , id := "2504.12231v2"
  }

/-- The February 2021 revision of the 2019 De Gregorio preprint used by the chapter. -/
@[bib "chen-hou-huang-2019"]
def chenHouHuang2019 : Verso.Genre.Manual.Bibliography.Citable := .arXiv
  { title := inlines!"On the Finite Time Blowup of the De Gregorio Model for the 3D Euler Equations"
  , authors := #[inlines!"Jiajie Chen", inlines!"Thomas Y. Hou", inlines!"De Huang"]
  , year := 2021
  , id := "1905.06387v3"
  }

/-- Lax's entropy conditions for hyperbolic systems. -/
@[bib "lax-1957"]
def lax1957 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Hyperbolic systems of conservation laws II"
  , authors := #[inlines!"Peter D. Lax"]
  , journal := inlines!"Communications on Pure and Applied Mathematics"
  , year := 1957
  , month := none
  , volume := inlines!"10"
  , number := inlines!"4"
  , pages := some (537, 566)
  , url := some "https://doi.org/10.1002/cpa.3160100406"
  }

/-- Kružkov's entropy solutions and $`L^1` contraction for scalar laws. -/
@[bib "kruzkov-1970"]
def kruzkov1970 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"First order quasilinear equations in several independent variables"
  , authors := #[inlines!"S. N. Kružkov"]
  , journal := inlines!"Mathematics of the USSR-Sbornik"
  , year := 1970
  , month := none
  , volume := inlines!"10"
  , number := inlines!"2"
  , pages := some (217, 243)
  , url := some "https://doi.org/10.1070/SM1970v010n02ABEH002156"
  }

/-- Gidas, Ni, and Nirenberg's symmetry theorem by moving planes. -/
@[bib "gidas-ni-nirenberg-1979"]
def gidasNiNirenberg1979 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Symmetry and related properties via the maximum principle"
  , authors := #[inlines!"B. Gidas", inlines!"Wei-Ming Ni", inlines!"L. Nirenberg"]
  , journal := inlines!"Communications in Mathematical Physics"
  , year := 1979
  , month := none
  , volume := inlines!"68"
  , number := inlines!"3"
  , pages := some (209, 243)
  , url := some "https://doi.org/10.1007/BF01221125"
  }

/-- Taylor and Green's decaying vortex. -/
@[bib "taylor-green-1937"]
def taylorGreen1937 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Mechanism of the production of small eddies from large ones"
  , authors := #[inlines!"G. I. Taylor", inlines!"A. E. Green"]
  , journal := inlines!"Proceedings of the Royal Society of London, Series A"
  , year := 1937
  , month := none
  , volume := inlines!"158"
  , number := inlines!"895"
  , pages := some (499, 521)
  , url := some "https://doi.org/10.1098/rspa.1937.0036"
  }

/-- Kovasznay's exact steady wake. -/
@[bib "kovasznay-1948"]
def kovasznay1948 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Laminar flow behind a two-dimensional grid"
  , authors := #[inlines!"L. I. G. Kovasznay"]
  , journal := inlines!"Mathematical Proceedings of the Cambridge Philosophical Society"
  , year := 1948
  , month := none
  , volume := inlines!"44"
  , number := inlines!"1"
  , pages := some (58, 62)
  , url := some "https://doi.org/10.1017/S0305004100023999"
  }

/-- Luo and Hou's computed axisymmetric Euler singularity. -/
@[bib "luo-hou-2014"]
def luoHou2014 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Potentially singular solutions of the 3D axisymmetric Euler equations"
  , authors := #[inlines!"Guo Luo", inlines!"Thomas Y. Hou"]
  , journal := inlines!"Proceedings of the National Academy of Sciences"
  , year := 2014
  , month := none
  , volume := inlines!"111"
  , number := inlines!"36"
  , pages := some (12968, 12973)
  , url := some "https://doi.org/10.1073/pnas.1405238111"
  }

/-- Kufner and Opic's conditions for well-defined weighted Sobolev spaces. -/
@[bib "kufner-opic-1984"]
def kufnerOpic1984 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"How to define reasonably weighted Sobolev spaces"
  , authors := #[inlines!"Alois Kufner", inlines!"Bohumír Opic"]
  , journal := inlines!"Commentationes Mathematicae Universitatis Carolinae"
  , year := 1984
  , month := none
  , volume := inlines!"25"
  , number := inlines!"3"
  , pages := some (537, 554)
  , url := some "https://dml.cz/handle/10338.dmlcz/106324"
  }

/-- Oleinik's one-sided entropy condition for convex scalar laws. -/
@[bib "oleinik-1957"]
def oleinik1957 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Discontinuous solutions of non-linear differential equations"
  , authors := #[inlines!"O. A. Oleinik"]
  , journal := inlines!"Uspekhi Matematicheskikh Nauk; English translation in American Mathematical Society Translations, Series 2, volume 26 (1963), 95–172"
  , year := 1957
  , month := none
  , volume := inlines!"12"
  , number := inlines!"3"
  , pages := some (3, 73)
  , url := some "https://doi.org/10.1090/trans2/026/05"
  }

end Blueprint.Bibliography
