# lattice-system

A Lean 4 + mathlib project for formalizing theorems about general
lattice models. The project subsumes and generalizes the earlier
[ising-model](https://github.com/phasetr/ising-model) project, with
the current focus on finite-volume quantum spin systems and the
longer-term goal of covering Hubbard / BCS, CAR-algebraic fermion
lattice systems, and eventually lattice QCD.

## About this project

This repository is written by a programmer without an academic
position, whose interests lie in non-relativistic quantum field theory
and rigorous statistical mechanics. Continuing a long-standing interest
in mathematical physics from my student days, and combined with the
goal of improving my technical skills as a programmer, I maintain
`lattice-system` as a personal hobby project to become proficient in
Lean 4 by formalizing results around lattice models.

The intended scope is finite-volume results in the first instance and,
more gradually, the infinite-volume / algebraic formulations described
in the project page. This project is not intended to interfere with
the work of researchers in the field, and if any overlap arises I am
happy to coordinate accordingly.

## Formalization status

All theorems are formally proved with **zero `sorry`**.

For the complete list of formalized theorems, the phase-by-phase
progress table, and the primary textbook references used at each step,
see the
**[project page](https://phasetr.github.io/lattice-system/)**.

## Documentation

- Project page: [https://phasetr.github.io/lattice-system/](https://phasetr.github.io/lattice-system/)
- API documentation (doc-gen4): [https://phasetr.github.io/lattice-system/docs/](https://phasetr.github.io/lattice-system/docs/)

Mathematical documentation for the formalized proofs is in `tex/` as
LaTeX source files. To compile:

```sh
cd tex
latexmk -lualatex -f -interaction=nonstopmode proof-guide.tex
```

Requires a TeX Live installation with LuaLaTeX. PDFs are not committed
to the repository.

| File                  | Description                                       |
|-----------------------|---------------------------------------------------|
| `tex/proof-guide.tex` | Mathematical walkthrough of the formalized proofs |

## Related projects and references

- Tasaki, H., *Physics and Mathematics of Quantum Many-Body Systems* — [Springer](https://link.springer.com/book/10.1007/978-3-030-41265-4)
- Nielsen, M. A. and Chuang, I. L., *Quantum Computation and Quantum Information* — [Cambridge UP](https://www.cambridge.org/highereducation/books/quantum-computation-and-quantum-information/01E10196D0A682A6AEFFEA52D53BE9AE)
- Araki, H. and Moriya, H., *Equilibrium Statistical Mechanics of Fermion Lattice Systems*, Rev. Math. Phys. 15 (2003), 93-198 — [World Scientific](https://www.worldscientific.com/doi/10.1142/S0129055X03001606)
- Bru, J.-B. and de Siqueira Pedra, W., *C\*-Algebras and Mathematical Foundations of Quantum Statistical Mechanics: An Introduction* — [Springer](https://link.springer.com/book/10.1007/978-3-031-28949-1)
- Tasaki, H., *From Nagaoka's Ferromagnetism to Flat-Band Ferromagnetism and Beyond* (1998) — [arXiv:cond-mat/9712219](https://arxiv.org/abs/cond-mat/9712219)
- Simon, B., *The Statistical Mechanics of Lattice Gases, Vol. I* — [Princeton UP](https://press.princeton.edu/books/hardcover/9780691636436/the-statistical-mechanics-of-lattice-gases-volume-i)
- Friedli, S. and Velenik, Y., *Statistical Mechanics of Lattice Systems: A Concrete Mathematical Introduction* — [Cambridge UP](https://www.unige.ch/math/folks/velenik/smbook/)
- Glimm, J. and Jaffe, A., *Quantum Physics: A Functional Integral Point of View* — [Springer](https://link.springer.com/book/10.1007/978-1-4612-4728-9)
- Fernández, R., Fröhlich, J., and Sokal, A. D., *Random Walks, Critical Phenomena, and Triviality in Quantum Field Theory* — [Springer](https://link.springer.com/book/10.1007/978-3-662-02866-7)
- Aarts, G., *Introductory lectures on lattice QCD at nonzero baryon number* (2015) — [arXiv:1512.05145](https://arxiv.org/abs/1512.05145)
- [phasetr/ising-model](https://github.com/phasetr/ising-model) — Upstream project; this repository reuses its conventions and infrastructure.
- [leanprover-community/physlib](https://github.com/leanprover-community/physlib) — A physics library in Lean 4.
- [YaelDillies/gibbs-measure](https://github.com/YaelDillies/gibbs-measure) — Lean 4 formalization project on Gibbs measures (classical).

## Learning resources

- [Lean by Example](https://lean-ja.github.io/lean-by-example/)
- [The Mechanics of Proof (Math 2001)](https://hrmacbeth.github.io/math2001/) by Heather Macbeth
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/index.html)

## Build

```sh
lake build
```

Uses Lean 4.29.0 and Mathlib `v4.29.0` (see `lean-toolchain` and
`lakefile.toml`).
