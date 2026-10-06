# An audit of `coloring_collision`

This note, the file `Coloring_Collision_Audit.lean` and the directory `comparator-audit/` are additions by a reader of this repository. They are not part of the original work. Every original file is unchanged, with two exceptions: `lakefile.lean` gains five lines at its end so that `lake build` also compiles the new file, and `README.md` gains one notice at its top that points here.

**In one sentence:** `coloring_collision` assumes the bound it needs, and that bound is false.

`Coloring_Collision_Audit.lean` imports `Hadwiger_Nelson_Final` unchanged and proves four things, with no `sorry` and on Lean's three standard axioms:

- **(a) The theorem applies to nothing.** For every radius r ≥ 0, no six-colouring of the circle satisfies the hypothesis `h_safe` (`Audit.hypothesis_never_holds`). The six classes cover the circle, so their angular measures add up to at least 2π, while `coloring_collision` itself says the total would be below 2π.
- **(b) The assumed bound is false.** `SafeDensity` says that a set with no two points at distance 1 has angular measure below π/3. At radius 1/4 the whole circle is such a set, and its measure is 2π (`Audit.density_bound_false_at_quarter`). At the paper's radius 1/√3 an arc of 120° is such a set, and its measure is at least 2π/3 (`Audit.density_bound_false_at_inv_sqrt_three`).
- **(c) The theorem uses no geometry.** It follows in one line from "six numbers, each below π/3, add up to less than 2π" (`Audit.headline_from_six_numbers`).
- **(d) Three colours suffice on the circle of radius 1/√3.** Three arcs of 120° are a proper colouring of it (`Audit.threeArcs`).

One exception, stated for completeness: for r < 0 the set `Circle r` is empty, and the empty colouring does satisfy `h_safe` (`Audit.emptyColouring_meets_hypothesis`). Nothing is coloured there.

None of the repository's Lean files states anything about the plane: there is no graph, no chromatic number and no contradiction. So χ(ℝ²) = 7 is not among the statements Lean has checked here. And by (b), the density bound that the argument rests on is false, at the paper's own radius among others.

## Check it

In the repository's root, with the Lean version it pins (v4.28.0):

    lake exe cache get
    lake build

The build prints one line for each result, and each line ends `[propext, Classical.choice, Quot.sound]`.

## With the comparator

`comparator-audit/` has the same shape as `comparator/` and the same versions (v4.34.0). Its `Challenge.lean` copies the repository's definitions unchanged and states (a), and (b) at radius 1/4; its `Solution.lean` proves them, using the repository's own `coloring_collision`. In that directory, `lake exe cache get`, then `lake build`, then the comparator tool on `comparator.json`: it answers "Your solution is okay!".
