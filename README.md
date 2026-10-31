# Counterexamples to a spectral short-cycle statement

Authors:
- Alex Chan — Harvard University and NBER
- Weilin Meng — Harvard Business School
- Kurt Sweat — UT Southwestern Medical Center

## Verified result

Charbit.lean verifies a twelve-vertex loopless oriented graph with
no nonempty closed directed walk of length at most five and complex
adjacency spectral radius strictly greater than 12/5.

It also verifies a displayed directed six-cycle.

The theorem is Charbit.counterexample. Its only axioms are the
standard Lean foundations propext, Classical.choice, and Quot.sound.

The full parameter classification is not yet formalized.

## Reproduce the verification

Use the Lean version specified in lean-toolchain, then run:

    lake update
    lake exe cache get
    lake build
    lake env lean Verify.lean

## Attribution

The construction is a directed cycle of transitive tournaments.
The four-class construction appears in Chudnovsky, Seymour and
Sullivan, Cycles in dense digraphs, Combinatorica 28 (2008), 1–18.
The general family is attributed to Hompe's 2019 thesis in Section 2
of Aharoni et al., Nonuniform Degrees and Rainbow Versions of the
Caccetta–Häggkvist Conjecture, SIAM Journal on Discrete Mathematics
37 (2023), 1704–1714.

Priority for the spectral application remains under investigation.
