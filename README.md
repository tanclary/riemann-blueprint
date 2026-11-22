# Distilling & Shrinking the 17.37M-Line Riemann Hypothesis Proof

**By Tanner Clary ([@tanclary](https://github.com/tanclary)) & Gemini 4 Carbon** · November 2026

On November 20, 2026, Levent Alpöge and Claude released a formal Lean 4 proof of the Riemann Hypothesis (and Dirichlet GRH) spanning **175,187 `.lean` files** and **17,374,215 lines of code**. Because naive natural-language translation exceeded 250,000 pages and static module `import` graphs touch 99.8% of the repository, two questions remained open:

1. **How much of the 17.37M lines is genuine mathematical content versus AI bloat?**
2. **What is the actual human-readable architecture of the proof?**

We treated the proof like a compiler IR problem: joining all 175,187 source files against MIT's 61.5 GB `lean4export` kernel DAG (`1,065,214,335` expression nodes, `1,484,733` kernel declarations), running **exact kernel reachability + proof-irrelevant `Prop`/`Def` Common Subexpression Elimination (CSE)**, verifying the shrunk kernel export end-to-end in Lean FRO's verified Rust kernel (`con-ron --compare` in `--verified` mode), and computing the **Lengauer–Tarjan Dominator Tree** to isolate the exact load-bearing choke-point theorems.

---

## Headline Results

| Stage | `.lean` Files | Source Decls | Source Lines | Kernel Fold Records | Delta vs Raw |
| :--- | ---: | ---: | ---: | ---: | ---: |
| **Raw Archive (`alpo.ge`)** | 175,187 | 1,061,425 | 17,374,215 | 1,468,418 | — |
| **Static `import` Reachability** | 174,767 | ~1,059,000 | 17,330,139 | — | -0.25% LOC |
| **Pass 1: Exact Kernel Reachability** | 146,134 | 744,681 | 10,604,250 *(in decls)* | — | -16.6% files |
| **Pass 2: Call-Site `Def` + `Prop` CSE** | 105,044 | 642,843 | 10,406,044 *(per-file)* | **1,167,754** | **-40.0% files / -20.5% kernel** |
| **Pass 3: Namespace-Coalesced Clean Repo** | 105,044 *(logical)* | 642,843 | **9,282,866** | **1,167,754** | **-46.6% LOC (-8.09M lines)** |
| **Human Blueprint ([`Blueprint.lean`](Blueprint.lean))** | 1 | 35 *(spine)* | **245** | — | 6-Act human spine |

### Key Findings

1. **Static `import` graphs are an illusion (-71.9% import edges eliminated):** `Main` transitively imports 174,767 of 175,187 files only because AI generation left massive unused import walls (`RiemannHypothesisOfEveryCharacter.lean` has **208 `import` lines** above a 20-line Mathlib proof). Kernel reachability + transitive import reduction cuts project import edges from `719,897` down to `202,054` (`-71.9%`) and drops **70,143 entire `.lean` files (`-40.0%`)**.
2. **Proof-Irrelevant `Prop` CSE (`-300,664` kernel fold records, verified by `con-ron`):** Because Lean's `Prop` is definitionally proof-irrelevant, any two `thm` declarations with identical `(levelParams, type_ie)` are interchangeable at every call site. Across parallel sub-tasks, the raw proof contained **241,514 redundant project theorems** (including **66,548 lemmas already in Mathlib / Lean Core**) plus **9,918 byte-identical `def`s**. Rewriting call sites and garbage-collecting dead records drops `1,468,418` fold records to `1,167,754` (`-20.48%`), verified from scratch by `con-ron --jobs=64 --compare` (`exit 0`, `--verified` mode) against MIT's unmodified `challenge.ndjson`.
3. **Why the remaining ~9.28M lines is still huge: ~110 classical 20th-century theorems proved from scratch.** Lengauer–Tarjan dominator analysis on `EveryCharacterOfLiteratureOfVWin.lean` exposed that the proof explicitly defines `GlobalTheory.Published.*` slots for **~110 famous 1960–2020 theorems** absent from Mathlib—including **Hironaka's Embedded Resolution of Singularities in char 0 (`44,031 LOC`)**, **Toroidal Compactifications of Shimura Varieties & Log Kodaira–Spencer (`124,353 LOC`)**, **Moriwaki Arakelov Bigness**, **Bhatt–Scholze Crystalline Lattices**, **Casselman–Wallach**, **Harish-Chandra Discrete Series**, and **Siegel–Weil**—and proves every single one from first principles so `#print axioms` stays pure `[propext, Classical.choice, Quot.sound]`.

---

## The 6-Act Human Blueprint ([`Blueprint.lean`](Blueprint.lean))

1. **Act I — Functional Equation Reflection (`20 LOC`):** Specializes `EveryCharacter` (`L(χ, s) ≠ 0` for `Re(s) > 1/2`) to `χ = 1 mod 1` and reflects across `Re(s) = 1/2` via `completedRiemannZeta_one_sub`.
2. **Act II — Cyclic Landau–de la Vallée Poussin Positivity (`168k LOC`):** Embeds any primitive character `ψ` into its cyclic subgroup `Λ = ⟨ψ⟩` of order `o` and forms a weighted prime-power sum `Λ.Gm(y)` with coset weights `4/(3o+1)` on `A₀` and `3/(3o+1)` off `A₀` (generalizing `3 + 4 cos θ ≥ 0`). By Landau's oscillation theorem at `la = 3/2`, a one-sided dyadic window bound on `Λ.Gm(y)` forces `L(ψ, s) ≠ 0` for `Re(s) > 1/2`.
3. **Act III — Character-Cut-Out CM Fields & Selmer/Sha Window `VWin` (`486k LOC`):** Cuts out abelian subfields `E ↪ ℚ(ζ_N)` by `ψ` and auxiliary Jacobi symbols mod `(q, d)` (`q ≡ 3 mod 8`, `d ≡ 7 mod 16`, `q ∣ d+1`) and bounds Selmer/Sha lengths `VVle(E, ⌊x^401⌋, √exp(x^ε))` via Kato's Euler system (`103k LOC`), `Sp₄`/`U(3)` modularity (`96k LOC`), Taylor–Wiles patching, and Base Change (`66k LOC`).
4. **Act IV — Chained Theta Lifts & Weight-One Galois Reps (`535k LOC`):** Substitutes for Stepanov's function-field derivatives over `ℤ` by chaining definite unitary theta lifts `U(n) → U(d)` (`TLiftK`, `31k LOC`) and constructing weight-one Galois representations (`Row0b IsRecT`) via Kodaira–Spencer isomorphisms, Harris–Taylor models, and crystalline towers (`429k LOC`) + local Langlands (`RecTExists`).
5. **Act V — Definite-Side Theta Matching, Carrier Gap & Moriwaki Covolumes (`4.54M LOC`):** Applies the regularized Siegel–Weil second-term identity, Howe duality, and Rallis inner-product formulas on unitary towers to get `O(x^(-1+ε))` coset equidistribution (`Shares`), while Moriwaki Arakelov bigness (`724k LOC`) bounds tower covolumes.
6. **Act VI — Classical 20th-Century Literature Library (`~1.81M+ LOC`):** Self-contained Lean 4 proofs of Hironaka, toroidal compactifications, Bhatt–Scholze, Casselman–Wallach, Harish-Chandra, Siegel–Weil, Artin reciprocity, and Poitou–Tate.

---

## Machine-Verified `con-ron` Receipt

Full log in [`data/con_ron_receipt.log`](data/con_ron_receipt.log):

```text
con-ron: accepted 51692 declarations, 5 axioms justified by the solution solution_shrunk.ndjson (1167754 declarations accepted) (--verified)
con-ron: theorem riemannHypothesis justified by the solution
con-ron: theorem riemannZeta_eq_zero_re justified by the solution
con-ron: theorem LFunction_ne_zero_of_half_lt_re justified by the solution
con-ron: theorem LFunction_eq_zero_re justified by the solution
con-ron: theorem LFunction_eq_zero_re_of_isPrimitive justified by the solution
```

---

## Repository Contents & Reproduction

- [`Blueprint.lean`](Blueprint.lean) — Human-readable 6-Act Lean 4 architectural spine with exact theorem signatures and Lengauer–Tarjan dominated LOC weights.
- [`docs/index.html`](docs/index.html) — Standalone interactive `pprof`-style Dominator Flamegraph, 6-Act walkthrough, and shrink waterfall explorer (GitHub Pages ready).
- [`data/dom_top300.tsv`](data/dom_top300.tsv) — Top 300 Lengauer–Tarjan dominator choke-points across the cleaned proof DAG.
- [`tools/`](tools/) — Five C++20 compiler/graph passes (`index_lean_tar.cpp`, `extract_dag.cpp`, `dominators.cpp`, `compact_repo.cpp`, `rewrite_export.cpp`).
- [`scripts/reproduce.sh`](scripts/reproduce.sh) — End-to-end download, SHA-256 verification, DAG extraction, dominator analysis, and `solution_shrunk.ndjson` generation (~25 GB RAM, Linux x86_64/aarch64).

```bash
chmod +x scripts/reproduce.sh
./scripts/reproduce.sh ./work
```

## License

MIT License · Copyright (c) 2026 Tanner Clary. Original Riemann Hypothesis Lean formalization by Levent Alpöge and Claude (`alpo.ge`); independent baseline export by Andrew Sutherland (MIT); `con-ron` verifier by the Lean FRO.
