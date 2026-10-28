# Verification scope

Toolchain: **Isabelle2025-2**, standard Isabelle/HOL. Original public AFP sources are unchanged. Extensions use ordinary proof checking, with no `sorry`, `oops`, added axioms, or quick-and-dirty mode. The source manifest identifies the exact files; the immutable repository commit identifies the public release.

## Build

```sh
ISABELLE=/path/to/Isabelle2025-2/bin/isabelle bash build.sh
```

The script checks `Causal_Efficacy_Patterns`, `Source_Sharing_Spines` and `Copy_Majority_Representation`, including all dependencies. `document_variants=` disables document generation only. Python 3.8+ runs the finite regressions. Successful checking establishes the formal statements under their hypotheses, not novelty, metaphysical adequacy or acceptance by a journal.

The complete source-only build and all three included regression programs completed successfully with the stated toolchain. All nine extension theories were checked; the inventory contains 254 named lemma/theorem declarations.

## Dependencies

`Thomistic_Causal_Arguments` → `Causal_Efficacy_Extension` → `Causal_Efficacy_Ancestors` → `Causal_Efficacy_Revision` → `Causal_Efficacy_Contexts`.

Determination, groundedness, source-sharing and copy-majority sessions import the contextual development. The final pattern session imports determination and groundedness. The script lists all required directories explicitly. `NAMED-RESULTS.txt` is an audit inventory; declaration counts are not counts of substantive new theorems.

## Principal checked statements

- `exact_relevant_pattern_realization`: arbitrary carrier, partition C=L∪Z∪Q into pairwise disjoint sets, legal active-root set U. Existence of an admissible fully relevant mechanism with least solution L and greatest C−Z is equivalent to the root statuses, internal finite paths in L/Z and an internal Q-parent condition. `realized_pattern_necessary` does not assume relevance.
- `exact_relevant_region_realization` and `exact_region_realization`: precisely the K containing all roots, internally root-reachable within K, and closed under the universal-parent operator. `attainable_regions_context_independent` compares existential families at two contexts; witnesses may differ.
- `shared_spine_attainable_initial_segments`: on the shared-source spine, attainable determinate sets are all vertices or the source plus a finite initial segment of links.
- `active_determinate_internal_root_path`: a node active in an actual fixed solution and agreeing across all unconditioned solutions has a finite path from an active root entirely inside the least solution. Whole-model unconditioned uniqueness implies leastness.
- `contextual_grounded_fixed_iff_least`: credited groundedness specialization at arbitrary legal root contexts; see `ATTRIBUTION.md` for prior mathematics.
- `relevant_labelled_spine_synthesis_iff`: one relevant mechanism succeeds at every source context exactly when every tail repeats a source label. This is a fixed-signature infinite family, not arbitrary-graph relevant synthesis.
- `copy_majority_all_contexts`, `carrier_expanded_solution_bridge`, `original_link_interventions_unique`: copy/majority expansion of the projection model, with arbitrary original-link hard clamps. `copy_interventions_nonunique` uses an infinite clamp of all added copies; unrestricted new-variable interventions are not preserved.

General carrier results require neither finite carriers nor finite parent sets. Roots retain their vertices and edges when their values change. Relevance means possible local input influence, not influence on every equation-compatible configuration. Empty carriers are permitted. Parent-copy uniform synthesis uses classical HOL choice; the explicit pattern witness does not select parents simultaneously.

## Independent finite regressions

The pattern program enumerates all 531 labelled directed graphs on 0–3 vertices, including loops. It checks 758 graph/context pairs, 42,943 admissible profile/context cases (8,040 fully relevant), 19,918 candidate partitions, 1,116 realized patterns with fully relevant constructed witnesses, and 4,165 graph/subset region-criterion cases. Local functions are all monotone Boolean truth tables rejecting empty input and accepting full input at nonroots. Root values are fixed separately. Every Boolean assignment is tested for fixedness independently of least/greatest bottom/top iteration. Input relevance is tested on every possible parent-input configuration.

These bounded tests are regression evidence, not proofs for infinite carriers. The included mathematical sources are authoritative for exact theorem assumptions. No classification of all solution sets, independent variation of ambiguous variables, general causal abstraction, or actual causation is asserted.
