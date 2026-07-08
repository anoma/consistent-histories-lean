# Consistent Histories in Lean 4

A complete Lean 4 formalization of the paper *Consistent histories: enforcing
linearity and excluding double-spending amongst collaborating controllers* by
Murdoch J. Gabbay and Isaac Sheff ([doi:10.5281/zenodo.21074395](https://doi.org/10.5281/zenodo.21074395)).
This repository contains mechanically
verified proofs of the paper's development — from the algebra of *located
semilattices with Cut* through to its two main safety results.

## What's in this repository?

The formalization follows the paper section by section:

- **Located semilattices (Section 2)**: bounded semilattices and top-trees,
  contradiction and consistency, located semilattices and their per-controller
  fibers, and worked examples (Examples 2.3.2–2.3.7) — three-valued logic, the
  "exponential cake", paper-scissors-stone, a bureaucracy, and closure operators.
- **Located semilattices with Cut (Section 3)**: flags and flag-sets, the
  cutting flag-set (`nextindex`/`cutme`/`cutyou`) and scope-extrusion, a proof
  that such a structure exists (Proposition 3.3.1) and a many-controller product
  model, and a more realistic *inductive construction* shown to be a located
  semilattice (Proposition 3.4.5).
- **Paths and circuits (Section 4)**: prepaths, paths and derivations with their
  five derivation rules, initial prefixes, and circuits / circuit-derivations
  and their (in)consistency.
- **Properties of paths and circuits (Section 5)**: ⋈-persistence, flag nesting
  and affine cuts, "inactive if and only if cut", matryoshka cut geometry, and
  (in)compatible cuts — culminating in the **main safety theorem** (Theorem
  5.6.2): *an inconsistent index in a circuit-derivation implies an active
  inconsistent index*.
- **A stronger safety property (Section 6)**: the `C`-closure of a set of times,
  chains of cuts, and **absolute consistency** (Theorem 6.4.3): *an inconsistent
  circuit-derivation has an inconsistent `C`-closure of its active times* — a
  consistency check needing no trust assumptions.
- **Alternative presentation (Section 7)**: attestations `Y ⇛ X`, examples and
  non-examples, separating/monotone attestations, and the alternative
  located-semilattice(-with-Cut) definitions.
- **Conclusions (Section 8)**: design-alternative witnesses, e.g. that
  attestation need not be transitive (§8.2.3).

Every numbered paper item is cross-referenced to its Lean declaration in
[FORMALIZATION_MAP.md](FORMALIZATION_MAP.md), linked to the exact file and line.

### Repository structure

The library is organized by *role*: `Foundation` holds reusable definitions and
general laws, `Models` holds concrete constructions and examples, `Routes` holds
the downstream results built on the foundations, and `AlternativePresentation`
and `PaperTargets` hold the Section 7–8 material.

```
ConsistentHistories/
├── Foundation/                       # reusable definitions, structures, and laws
│   ├── LocatedSemilattices/
│   │   ├── TopTrees.lean             # §2.1  bounded semilattices, contradiction, top-trees
│   │   └── Basic.lean                # §2.2  located semilattices, CTime, attestation
│   ├── Cut/
│   │   ├── Flags.lean                # §3.1  flags and flag-sets
│   │   └── Structure.lean            # §3.2  located semilattices with Cut; scope-extrusion
│   └── Paths/
│       ├── Basic.lean                # §4.1  prepaths, paths, derivations, inactive indices
│       └── InitialPrefixes.lean      # §4.2  initial prefixes; "times increase"
├── Models/                           # concrete examples, models, construction packages
│   ├── Introduction.lean             # §1.2  the exponential-cake narrative (Example 1.2.1)
│   ├── LocatedSemilattices/Examples/
│   │   ├── ThreeValued.lean          # §2.3  Examples 2.3.2–2.3.3 (three-valued logic)
│   │   ├── CakeFigure.lean           # §2.3  Example 2.3.4 (the cake as a located semilattice)
│   │   ├── GamePlay.lean             # §2.3  Example 2.3.5 (paper-scissors-stone)
│   │   ├── Bureaucracy.lean          # §2.3  Example 2.3.6 (the bureaucracy)
│   │   └── ClosureSystem.lean        # §2.3  Example 2.3.7 (closure operators)
│   └── Cut/
│       ├── Consistency.lean          # §3.3  consistency models (Prop 3.3.1, Def 3.3.2)
│       ├── InductiveConstruction.lean      # §3.4  the inductive construction
│       └── InductiveConstructionLaws.lean  # §3.4  Prop 3.4.5 (it is a located semilattice)
├── Routes/                           # downstream results built on the foundations
│   ├── Paths/Circuits/               # §4.3  circuits and circuit-derivations
│   │   ├── Circuit.lean
│   │   ├── CutPrefixData.lean
│   │   ├── CutPrefixWitness.lean
│   │   └── CircuitDerivation.lean
│   ├── PathProperties/               # §5    properties of paths and circuits
│   │   ├── CutmePersistence.lean     # §5.1  ⋈ persistence
│   │   ├── FlagNesting.lean          # §5.2  flag nesting and affine cuts
│   │   ├── InactiveCuts.lean         # §5.3  inactive if and only if cut
│   │   ├── Matryoshka.lean           # §5.4  matryoshka cut geometry
│   │   ├── Compatibility.lean        # §5.5  (in)compatible cuts
│   │   └── MainResult.lean           # §5.6  MAIN RESULT: Theorem 5.6.2
│   └── StrongerSafety/               # §6    a stronger safety property
│       ├── Closure.lean              # §6.2  C-closure of a set of times
│       ├── Chains.lean               # §6.3  chains of cuts
│       └── Absolute.lean             # §6.4  absolute consistency: Theorem 6.4.3
├── AlternativePresentation/          # §7    alternative presentation via attestations
│   ├── Attestation.lean              #       Definition 7.2; examples; separating/monotone
│   ├── Semitopology.lean             #       Example 7.4(5) (semitopology attestation)
│   ├── Cutting.lean                  #       cutting-flag machinery (Definition 7.7)
│   ├── AlternativeLocatedSemilattice.lean   # Definitions 7.6 and 7.7
│   └── DegenerateAlternativeCutExample.lean # Remark 7.8 and a worked example
└── PaperTargets/
    └── Conclusions.lean              # §8    e.g. attestation need not be transitive (§8.2.3)
```

See [FORMALIZATION_MAP.md](FORMALIZATION_MAP.md) for the detailed mapping between
paper items and their Lean declarations.

## Installation

### Prerequisites

You need:

1. **Lean 4** — a theorem prover and functional programming language.
2. **elan** — the Lean version manager (it installs the exact Lean version this
   project uses, `leanprover/lean4:v4.28.0`).
3. **lake** — Lean's build tool (installed together with Lean).

This project is self-contained: it has no external library dependencies, so
building it only requires the Lean toolchain itself.

### Step-by-step installation (for paper readers new to Lean)

#### 1. Install elan (Lean version manager)

On Linux/macOS:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

On Windows, download and run
[elan-init.exe](https://github.com/leanprover/elan/releases).

After installation, restart your terminal or run:

```bash
source ~/.profile   # or source ~/.bashrc
```

#### 2. Clone this repository

```bash
git clone https://github.com/anoma/consistent-histories-lean.git
cd contForm
```

(Or unpack the zip archive of this repository, if you downloaded it from a DOI
or other source.)

#### 3. Build and verify the proofs

```bash
lake build
```

This builds the project **and verifies all proofs**. It will:

- automatically install the correct Lean version (`v4.28.0`) via elan on first run;
- compile the library — about 40 Lean files, 44 build jobs.

**What to expect during the build:**

- The one-time Lean toolchain download is a few hundred megabytes; after that
  the project itself has no dependencies to fetch.
- You'll see progress lines like `✔ [40/44] Built ConsistentHistories.Models ...` as
  modules are compiled. The main safety proofs are in the
  `ConsistentHistories.Routes.PathProperties` (Theorem 5.6.2) and
  `ConsistentHistories.Routes.StrongerSafety` (Theorem 6.4.3) modules.
- A clean build takes on the order of a minute or two on a typical machine.
  Subsequent builds are much faster.

**If the build completes without errors, all proofs are mechanically verified
correct** — the repository contains no `sorry` or `admit`.

#### 4. (Optional) Install VS Code with the Lean 4 extension

For the best experience viewing and stepping through proofs:

1. Install [Visual Studio Code](https://code.visualstudio.com/).
2. Open this repository in VS Code by running `code .` from the terminal in the
   repository directory.
3. Install the "Lean 4" extension:
   - Click the "Extensions" icon in the VS Code sidebar (or press
     Ctrl+Shift+X / Cmd+Shift+X).
   - Search for "Lean 4".
   - Install the extension published by "leanprover" (the official extension
     from the Lean development team; see the
     [official Lean installation page](https://lean-lang.org/install/)).
4. Open any `.lean` file (e.g. `ConsistentHistories.lean`) to see syntax highlighting and
   proof states.

## How to explore the formalization

### For paper readers

If you're reading the paper and want to see how something is formalized:

1. Open [FORMALIZATION_MAP.md](FORMALIZATION_MAP.md).
2. Find the numbered item from the paper (e.g. "Theorem 5.6.2").
3. Follow the link to the exact Lean declaration, file, and line.

For example, the main safety theorem (Theorem 5.6.2) is
`inconsistentIndex_implies_activeInconsistentIndex` in
`ConsistentHistories/Routes/PathProperties/MainResult.lean`, and the absolute-consistency
theorem (Theorem 6.4.3) is `inconsistentCircuit_implies_cClosure_inconsistent`
in `ConsistentHistories/Routes/StrongerSafety/Absolute.lean`.

### In VS Code

1. Open a `.lean` file (e.g. `ConsistentHistories.lean`).
2. Click anywhere in a proof.
3. The "Lean Infoview" panel shows the proof state at that point.
4. Hover over identifiers to see their types.
5. Ctrl+click (or Cmd+click) on a name to jump to its definition.

## License

This work is licensed under [CC-BY 4.0](LICENSE).
