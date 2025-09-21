<img src="assets/lean_logo-grey.svg" alt="LEAN"> 

# LEANearized Radii Polynomial — A LEAN Blueprint 

### Live blueprint page

- https://IlPreteRosso.github.io/LEANearized-RadiiPolynomial  

This repository contains a **Lean blueprint** for the theorem
**Radii Polynomials in Finite Dimensions**.

> Proof flow at a glance:  
> data → Newton map \(T = x - A f(x)\) → a‑priori bounds \((Y_0, Z_0, Z_2)\) → radii polynomial \(p(r)\) → derivative bound → fixed‑point radii lemma → main theorem (existence, uniqueness, nondegeneracy).

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

---

## LaTeX ↔ LEAN workflow

When writing the blueprint `.tex` files you link LaTeX statements (theorems, definitions, lemmas, etc.) to Lean objects using the `\lean{}` handle. The handle must name an existing *true* declaration in LEAN so `leanblueprint` can build the dependency graph.

Example

```tex
\begin{theorem}[Mean Value Theorem]\label{thm:MVT}
	\lean{RP.MeanValueTheorem}
	Let $g:\mathbb R^n\to\mathbb R$ be $C^1$. For all $x,y\in\mathbb R^n$ there exists $t\in(0,1)$ such that
	\[
		g(x)-g(y)=\nabla g\bigl(y+t(x-y)\bigr)\cdot (x-y).
	\]
\end{theorem}
```

Here `\lean{RP.MeanValueTheorem}` is a handle that points to the Lean declaration named `RP.MeanValueTheorem` in the LEAN sources.


```lean
namespace RP

/-- Mean Value Theorem (placeholder). -/
theorem MeanValueTheorem : True := True.intro

end RP
```

Rules and best practices
- Every `\lean{...}` handle used in the `.tex` files must reference an existing Lean object (fully qualified when in a namespace). If the object doesn't exist the blueprint check will fail.
- Placeholders are fine while writing the blueprint: it's common to add a temporary `theorem ... : True := True.intro` so the dependency graph and checks succeed. Replace placeholders with real statements/proofs as you formalize.
- Lean sources for the blueprint live under `LEAN-modules/`. Update or add files there when you introduce new handles in the `.tex` files.
- After editing `.tex` or `LEAN-modules/`, run `make` at the repository root to rebuild the blueprint pages and run the checks (the `make` recipe invokes the plasTeX/leanblueprint pipeline).

If you ever need help locating the Lean declaration for a LaTeX handle, search the `LEAN-modules/` folder for the name (e.g. `grep -R "MeanValueTheorem" LEAN-modules`).

---

## Acknowledgments

Built with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint), a plasTeX plugin for planning and tracking Lean formalization projects.


