# Online carpooling proof blueprint

Open the [interactive proof graph](https://milind-prabhu.github.io/online-carpooling-lean/), or open `generated/Online_Carpooling_Blueprint.html` locally in a browser. The file is self-contained and works offline. It includes an overview, three proof-specific views, and all 420 explicitly named declarations. Hover over a node for a larger, plain-language summary; click for its compiled Lean statement, source, displayed prerequisites and consequences. The same summary appears on keyboard focus. Summaries are maintained in `descriptions.json` and explain the declarations; the compiled Lean statements remain authoritative. The minimal toolbar provides proof views and search; drag to pan and scroll to zoom. A details panel opens only after selecting a declaration, with its proof under “Lean proof.”

The visual convention follows the [Polynomial Freiman–Ruzsa blueprint](https://teorth.github.io/pfr/blueprint/dep_graph_document.html): ellipses for theorems and lemmas, boxes for definitions, with double borders identifying the four main theorem declarations. The interactive graph uses neutral colors with a subtle green accent for the main theorems; the static exports use green for checked declarations. This is an independent standalone renderer, rather than a deployment of Lean Blueprint.

## Rebuild

From the project root, with the pinned Lean/mathlib environment and Graphviz installed:

```sh
python3 blueprint/index_sources.py
lake env lean blueprint/Extract.lean
python3 blueprint/build_graph.py
```

The extractor reads `ConstantInfo.getUsedConstantsAsSet` from the compiled environment: references in declaration types and proof/definition terms. It exports generated and private project helpers as well as source-named declarations. Source indexing determines which names to expose and supplies source excerpts; it does not determine dependency arrows.

An arrow points from prerequisite to result. For each view, paths through omitted project helpers are collapsed until another displayed declaration is reached. Transitive reduction removes redundant arrows in acyclic views. `generated/graph_data.json` records a witnessed compiled dependency path for every retained arrow. Source-named declarations are all matched to compiled constants. The full view is the full **source-named project** graph, rather than all generated constants or the whole mathlib graph.

Every displayed declaration belongs to the successfully checked project; this does not mean axiom-free mathematics. `Audit.lean` contains 84 transitive axiom audits, whose output in `VERIFICATION.txt` uses only `propext`, `Classical.choice`, and `Quot.sound`. The exact finite hypotheses and conclusions are shown on click. Some general corollaries accept guarantees as hypotheses, so the graph can have disconnected nodes even when they are mathematically applied together.

The overview is also provided as SVG, PDF, and PNG. The theorem proofs are unchanged by this visualization.
