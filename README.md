
# LEANearized Radii Polynomial — Blueprint (Lean + `leanblueprint`)

This repository contains a compact **Lean blueprint** for the theorem often called
**Radii polynomials in finite dimensions** (Section 2.4). It is organized so that
Patrick Massot’s `leanblueprint` can render (i) a human‑readable web version of the LaTeX
and (ii) an **interactive dependency‑graph flowchart** that mirrors the proof plan via
`\uses{...}` annotations.

> Proof flow at a glance:  
> data → Newton map \(T = x - A f(x)\) → a‑priori bounds \((Y_0, Z_0, Z_2)\) → radii polynomial \(p(r)\) → derivative bound → fixed‑point radii lemma → main theorem (existence, uniqueness, nondegeneracy).

---

## Live blueprint pages

- **Blueprint (HTML):** https://IlPreteRosso.github.io/LEANearized-RadiiPolynomial  

## Acknowledgments

Built with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint), a plasTeX plugin for planning and tracking Lean formalization projects.
The proof‑plan here follows the standard “radii polynomials in finite dimensions” framework (Section 2.4).

---
