# The Cube-Root Phenomenon in Online Carpooling

The three main theorems—**Theorems 1.1, 1.2, and 1.3**—are formalized in Lean.

[Paper](https://arxiv.org/abs/2609.21348v1) by Nikhil Bansal, Milind Prabhu,
Sahil Singla, and Siddharth M. Sundaram.

## Explore the proof

View the [interactive Lean proof dependency graph](https://milind-prabhu.github.io/online-carpooling-lean/).
Click the image below to open it, then select a theorem or lemma to see its Lean
statement, proof, and dependencies. Use the view menu to explore different parts
of the proof.

[![Lean proof dependency graph](blueprint/generated/Online_Carpooling_Dependency_Graph.svg)](https://milind-prabhu.github.io/online-carpooling-lean/)

## Build and verify

Install [elan](https://github.com/leanprover/elan), clone this repository, and run:

```bash
bash bootstrap.sh
bash check.sh
```

The project pins Lean 4.24.0 and mathlib 4.24.0. The check builds the proofs and
runs the axiom audit. [Build status](https://github.com/milind-prabhu/online-carpooling-lean/actions/workflows/lean.yml).

See the [formalization notes](FORMALIZATION.md) for precise theorem statements,
assumptions, and correspondence with the paper.

This formalization was achieved using **ChatGPT-6 Astra**.
