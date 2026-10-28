# Determination patterns in infinite dependency models

Isabelle/HOL sources for normalized monotone Boolean dependency mechanisms,
contextual determination, source-sharing synthesis and representation tests.
The release extends the public AFP entry `Thomistic_Causal_Arguments` in
separate sessions. The original AFP sources are included unchanged.

## Reproduce

Use **Isabelle2025-2** and Python 3.8 or later:

```sh
ISABELLE=/path/to/Isabelle2025-2/bin/isabelle bash build.sh
```

The script checks all extension sessions and runs finite regression programs.
`-o document_variants=` suppresses AFP document generation without changing
its original ROOT or disabling proof checking. The tests use labelled graphs
on 0–3 vertices, including loops; they are not proofs for infinite carriers.

`SOURCE-SHA256SUMS` identifies the release files. Use the immutable Git commit
of the release, not a moving branch, when citing a particular source snapshot.
`VERIFICATION.md` gives checked scope and exact session dependencies.

## Main results

- Exact realization of forced-on, forced-off and ambiguous regions on an
  arbitrary carrier, with every listed input functionally relevant.
- Exact attainable determinate-region criterion, independent of root context
  as a family of realizable regions (not a quantifier exchange for mechanisms).
- Active unconditionally determinate targets belong to the least solution and
  have finite paths from active roots inside the forced-on region.
- Unrestricted context-uniform synthesis iff every node has root ancestry;
  the selected-parent copying construction uses classical HOL choice.
- Relevant uniform synthesis on source-labelled infinite spines iff every tail
  repeats a source label; arbitrary hard link clamps preserve its uniqueness.
- A fully relevant majority/copy expansion preserves projection behavior under
  original-link interventions, but not arbitrary interventions on added copies.
- A credited specialization of established grounded-fixed-point theory.

The general results impose no finite-carrier or finite-parent hypothesis.
Relevance means possible influence at some formal input, not influence in every
context or on configurations satisfying every other equation. All Boolean root
contexts are admitted. General relevant uniform synthesis on arbitrary graphs
and arbitrary solution-set realization are not claimed.

## Source map

| Directory | Session | Role |
|---|---|---|
| sources/Thomistic_Causal_Arguments | Thomistic_Causal_Arguments | Public relational baseline |
| extensions | Causal_Efficacy_Extension | Mechanisms and source-on classification |
| ancillary | Causal_Efficacy_Ancestors | Target ancestral-cone equivalence |
| revision-extras | Causal_Efficacy_Revision | Single parents, copying, observations, boundaries |
| context-extension | Causal_Efficacy_Contexts | Arbitrary root contexts and uniform guarantees |
| determination-extension | Causal_Efficacy_Determination | Attained determination bounds and unrestricted synthesis |
| grounded-extension | Causal_Efficacy_Grounded | Credited groundedness specialization |
| source-sharing | Source_Sharing_Spines | Exact infinite-family relevant synthesis |
| copy-majority | Copy_Majority_Representation | Representation/intervention preservation test |
| pattern-extension | Causal_Efficacy_Patterns | Complete determination-pattern realization |

## License and attribution

Extensions are distributed under BSD-3-Clause; the bundled AFP baseline retains
its original BSD notice in `sources/AFP-LICENSE.txt`. See `ATTRIBUTION.md` for
baseline authorship, public-source provenance and mathematical antecedents.
This repository contains formal source and tests, not the manuscript, literature
full texts, private reviews or development transcripts. Formal checking is not
an endorsement of philosophical interpretation or a claim of exhaustive novelty.
