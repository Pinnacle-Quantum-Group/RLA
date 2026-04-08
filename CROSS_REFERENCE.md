# Cross-Reference: Lemma Derivation Mapping

The complete lemma derivation mapping for the PQG framework is maintained in:

**Repository:** [pinnacle-quantum-group/rssn](https://github.com/pinnacle-quantum-group/rssn)
**Branch:** `claude/lemma-derivation-mapping-WrwCv`

## RLA-Specific Results

| Theorem | Status | Key Lemmas |
|---------|--------|------------|
| RLA T2 (Graded Lie Algebra) | **TIGHT** | Jacobi via dα=0 cancellation |
| RLA T5 (Representation) | **TIGHT** | Leibniz expansion + weight collection |
| RLA T7 (Conservation) | **TIGHT** | Noether + weighted Lie derivative |
| RLA P8 (Witt Limit) | **TIGHT** | λ in R interpolates discrete grading |
| RLA L3 (Scaled Commutator) | **TIGHT** | Direct Leibniz computation |

## RLA's Critical Cross-Framework Role

RLA is the **most rigorous** document in the PQG framework -- all results are TIGHT with full proofs in appendices.

RLA provides the geometric backbone via Bridge Lemmas:
- **B.1:** RSSN D_k(n) = discrete evaluation of RLA scale field D
- **B.2:** RSSN operators correspond to graded Lie derivatives
- The scale field D and 1-form α = d(ln D) encode the density gradient

## Publication Note

RLA is recommended as a **parallel Phase 1 publication** -- it is self-contained, requires no other PQG frameworks, and enables Bridge B.1 which connects everything else.

## Test Suite

Bridge lemma tests (RLA connection): `rssn/tests/test_bridge_lemmas.py`
