# <div align="center"> The Hadwiger-Nelson Problem: Formal Verification of $\chi(\mathbb{R}^2) = 7$ 

This repository contains the formal verification that the chromatic number of the Euclidean plane is exactly 7. By utilizing a **Proof by Exclusion** implemented in Lean 4, this project demonstrates that a 6-coloring of the plane is logically impossible due to geometric constraints and the irrationality of $2\pi$.

## 📌 Abstract

The Hadwiger-Nelson Problem seeks the chromatic number of the Euclidean plane $\chi(\mathbb{R}^2)$, currently constrained to the set $\{5, 6, 7\}$. This paper establishes $\chi(\mathbb{R}^2) = 7$ through a proof by exclusion. Utilizing the de Bruijn–Erdős Theorem to relate the infinite plane to its finite subgraphs, we analyze a unit-distance path projected onto a circle of radius $r$. Via the Lean 4 interactive theorem prover, we formally verify that the irrationality of $2\pi$ relative to the unit chord length introduces an unavoidable phase drift that strictly bounds the angular density of any unit-safe color set below $\pi/3$. This density deficit creates a geometric conflict where a 6-color partition cannot cover the $2\pi$ circumference without forcing a monochromatic adjacency. These inherent periodic constraints allow for the mapping of the plane as a toroidal projection, which necessitates a 7th color to resolve the coverage gap. By scaling this local exclusion to the infinite plane via the de Bruijn–Erdős Theorem, we conclude that the chromatic number of the plane is exactly 7. A result that is fundamentally consistent with both the known 7-coloring of the discrete torus and the established upper bound provided by the hexagonal tiling of the plane. 

## ✅ Formal Verification in Lean Web 4

The proof is formally verified using the **Lean 4 Interactive Theorem Prover**. The core mathematical claim, `coloring_collision`, proves that the density of any unit-safe 6-coloring is insufficient to cover the circle without a monochromatic adjacency.

### Direct Verification
You can verify the proof results directly in your browser via the Lean 4 Web Editor:

**[Verify Results in Lean 4 Web](https://live.lean-lang.org/#project=mathlib-v4.28.0&codez=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)** 

## 📂 Project Structure

* 📝 **`The Hadwiger-Nelson Problem.pdf`**: The full manuscript detailing the toroidal projection methodology and the analytical derivation of the drift equation.
* 💻 **`Hardwiger_Nelson_Final.lean`**: Lean 4 source code containing the formal definitions, the unit-triangle clique verification, and the final collision theorem.

## 🎓 Citation

Reed, Jonathan ƒ(n). (2026). The Hadwiger-Nelson Problem: Formal Verification of the 7-Color Chromatic Number of the Plane via Toroidal Projection and the Irrationality of 2π (1.0). Zenodo. https://doi.org/10.5281/zenodo.20149767

## ⚖️ License ⚖️

This work is licensed under a **Creative Commons Attribution 4.0 International License (CC BY 4.0)**.

---
[ORCID: 0009-0008-7345-1407](https://orcid.org/0009-0008-7345-1407)
