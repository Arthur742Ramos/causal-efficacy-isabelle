# Foundations and Limits of Essentially Ordered Causal Regress Arguments

Authors: Arthur F. Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz.

This AFP-style Isabelle/HOL development studies what follows from explicit
dependency premises in Thomistic causal-regress arguments.  Its central result
is a disciplined separation of foundation principles that are often conflated:
acyclicity, well-foundedness, chain termination, local foundation, global
foundation, and full grounding of a target set.  The research layer additionally
proves exact premise-factorisation and deletion certificates for the
Romero--Pérez and Cohoe-style packages, and supplies a bounded cycle analyzer
with kernel-checked finite return-path certificates.

The project is deliberately modest about its conclusion.  It proves
first-member and first-cause results inside the supplied dependency structure;
it does not prove that the structure describes reality, and it does not identify
any formal first cause with God.  It deliberately does not formalize the First
or Third Ways: substantive treatments would require richer act/potency and
modal semantics.  The AFP contribution is the relation/foundation interface,
the implication-and-separation atlas, the executable finite checker, and the
exact Second-Way comparison layer.

## Theory map

- Dependency_Structures.thy: carrier-restricted immediate dependence,
  transitive ancestry, grounding, independence, first members, and foundation
  sets.
- Foundation_Principles.thy: acyclicity, well-foundedness, explicit chain
  termination, local/global foundation, and plural full grounding.
- Foundation_Implications.thy: positive implication theorems, finite
  equivalences, and the bundled foundation implication atlas.
- Foundation_Separations.thy: integer predecessor, pedestal, rooted-cycle, and
  paired finite countermodels separating the principles, including the
  incomparability of foundation and acyclicity on arbitrary carriers.
- Finite_Foundation_Checker.thy: executable finite relation representation,
  bounded reachability, exact independent-root certificates, concrete failure
  witnesses, correctness theorems, and regression examples.
- Finite_Foundation_Analysis.thy: executable cycle certificates and a
  certified finite profile linking five declarative properties to two
  executable tests: acyclicity, well-foundedness, and chain termination share
  the cycle test, while local and global foundation share the foundation test.
- Second_Way_Reconstructions.thy: relationally operative Cohoe-style essential
  ordering explication, Romero--Pérez-style well-founded reconstruction, and a
  comparison/separation package.
- Premise_Minimality.thy: literal factorisation of the two premise packages
  and individually verified countermodels deleting existence, carrier
  membership, predecessor coverage, well-foundedness, essential ordering, full
  foundation, singleton endpoint, full nonemptiness, and full ancestry.  The
  Romero--Pérez deletions all refute one fixed combined conclusion.  It also
  proves that Cohoe's separate carrier premise is redundant once essential
  ordering is stated carrier-restrictively.
- Thomistic_Causal_Arguments.thy: umbrella session entry point.

The entry is self-contained: its definitions, theorem statements, proofs,
examples, and explanatory document are contained in the AFP session and its
document files.  blueprint.md records the theorem dependency DAG and the
deliberate scope boundary; it is project metadata rather than a mathematical
dependency of the session.

## Build

From this directory:

    isabelle build -D . Thomistic_Causal_Arguments

For a faster proof-only check while editing:

    isabelle build -o document=false -D . Thomistic_Causal_Arguments

The repository-level tools/build.ps1 and tools/audit.ps1 provide the canonical
AFP-oriented build and archive-readiness checks when invoked from the monorepo
root.
