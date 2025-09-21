# LEANearized Radii Polynomial — Blueprint ( <img src="assets/lean_logo.png" alt="LEAN" style="vertical-align:top;"> + `leanblueprint` )

This repository contains a **Lean blueprint** for the theorem
**Radii Polynomials in Finite Dimensions**.

> Proof flow at a glance:  
> data → Newton map \(T = x - A f(x)\) → a‑priori bounds \((Y_0, Z_0, Z_2)\) → radii polynomial \(p(r)\) → derivative bound → fixed‑point radii lemma → main theorem (existence, uniqueness, nondegeneracy).

---

**How to modify *.tex*+*.lean***
> run `make` in the root directory before committing

---

## TeX file structure 
### Where to edit

The LaTeX source for the blueprint lives under the `blueprint/src` directory. Major files and folders:

- `blueprint/src/content.tex` — main content entry point that pulls together sections and structure for the blueprint output (PDE+dependency graph).
- `blueprint/src/Sections/` — chapter folders. Each chapter (Ch0, Ch1, ...) contains the section `.tex` files.
- `blueprint/src/web.tex` — web-specific entry point that controls the HTML blueprint pages and web metadata.
- `blueprint/src/print.tex` — top-level entry point for printable/PDF outputs; 

Say to edit Chapter 1, Section 1, open:

`blueprint/src/Sections/Ch1/1-1-ContractionMapping.tex`

Make your edits there, then run `make` from the repository root to rebuild the blueprint pages.


### Macros

Reusable LaTeX macros live in `blueprint/src/macros`. These define commands and presentation differences used by the blueprint outputs:

- `blueprint/src/macros/common.tex` — shared macros and notation used across web/print versions. 
- `blueprint/src/macros/print.tex` — rules and commands used when producing printable/PDF outputs. In usual cases, this file should be minimal.
- `blueprint/src/macros/web.tex` — web-specific tweaks for the HTML blueprint pages. In usual cases, this file should be minimal.


## Live blueprint page

- **Blueprint (HTML):** https://IlPreteRosso.github.io/LEANearized-RadiiPolynomial  

## Acknowledgments

Built with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint), a plasTeX plugin for planning and tracking Lean formalization projects.

---
