<img src="assets/lean_logo-grey.svg" alt="LEAN"> 

# Radii Polynomial — A LEAN Blueprint Project 

### Live blueprint page

- https://IlPreteRosso.github.io/LEANearized-RadiiPolynomial  

This repository contains a **Lean blueprint** for the theorem
**Radii Polynomials in General Banach Spaces**.

> Proof flow at a glance:  
> data → Newton map \(T = x - A f(x)\) → a‑priori bounds \((Y_0, Z_0, Z_2)\) → radii polynomial \(p(r)\) → derivative bound → fixed‑point radii lemma → main theorem (existence, uniqueness, nondegeneracy).

## Directory Structure

This project have the following structure:

```
RadiiPolynomial/                    
├── lakefile.toml                   
├── Main.lean                       
├── makefile                        
├── RadiiPolynomial/               
│   └── RadiiPolyGeneral.lean     
└── blueprint/                               
    └── src/                       
        ├── content.tex            
        ├── macros/                
        │   └── common.tex         # LaTeX macros (leanblueprint standard)
        └── Sections/              
            ├── Ch0/               
            │   ├── Abstract.tex
            │   └── Notations.tex
            ├── Ch2/               
            │   ├── 2-1-ContractionMapping.tex
            │   ├── 2-2-MeanValue.tex
            │   ├── 2-3-Newton.tex
            │   └── 2-4-RadiiPolynomialsFD.tex
            └── Ch7/               
                ├── 7-6-RadiiPolynomialBanach.tex
                └── 7-7-Example.tex
```

---

### Macros

Reusable LaTeX macros live in `blueprint/src/macros`. These define commands and presentation differences used by the blueprint outputs:

- `blueprint/src/macros/common.tex` — shared macros and notation used across web/print versions. 
- `blueprint/src/macros/print.tex` — rules and commands used when producing printable/PDF outputs. In usual cases, this file should be minimal.
- `blueprint/src/macros/web.tex` — web-specific tweaks for the HTML blueprint pages. In usual cases, this file should be minimal.

---

## LaTeX ↔ LEAN 

### Lean Label Commands

- `\lean{declaration_name}` - Links to the Lean declaration
- `\leanok` - Marks that the formalization is complete
- `\uses{label1, label2}` - Indicates dependencies on other results
- `\label{latex_label}` - Standard LaTeX label for cross-references

When writing the blueprint `.tex` files you link LaTeX statements (theorems, definitions, lemmas, etc.) to LEAN declaration using the `\lean{}` handle. The handle must name an existing *true* declaration in LEAN so the `checkdecls` in `leanblueprint` can build the dependency graph.

### Example

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
-- ...
```

Rules and best practices
- Every `\lean{...}` handle used in the `.tex` files must reference an existing Lean object (fully qualified when in a namespace). If the object doesn't exist the blueprint check will fail.
- Placeholders are fine while writing the blueprint: it's common to add a temporary `theorem ... : True := True.intro` so the dependency graph and checks succeed. Replace placeholders with real statements/proofs as you formalize.
- Lean sources for the blueprint live under `RadiiPolynomial/`. Update or add files there when you introduce new handles in the `.tex` files.
- After editing `.tex` files, push to GitHub to trigger the CI workflow, or run `leanblueprint web` locally to preview changes.

If you ever need help locating the Lean declaration for a LaTeX handle, search the `RadiiPolynomial/` folder for the name (e.g. `grep -R "MeanValueTheorem" RadiiPolynomial/`).

---

## InfoView setup

Configure the the LEAN version for VS Code Lean extension (InfoView), to check required version (in currently installed toolchains) run:

```sh
cat .lake/packages/mathlib/lean-toolchain
```

Set the VS Code Lean toolchain to that version (for example `v4.26.0-rc1`) in the extension settings or via the InfoView selector. 

---

## CI/CD Workflow

The project uses GitHub Actions to automatically build and deploy the blueprint. The workflow is defined in `.github/workflows/blueprint.yml`.

### Workflow Structure

The workflow runs as a **single sequential job** with optimized caching:

```
┌─────────────────────────────────────────────┐
│              build_project                  │
│                                             │
│  1. Free disk space                         │
│  2. Build Lean project                      │
│  3. Build API documentation (cached)        │
│  4. Build blueprint (PDF + web)             │
│  5. Check declarations                      │
│  6. Build Jekyll site                       │
│  7. Deploy to GitHub Pages                  │
└─────────────────────────────────────────────┘
```

### Key Features

1. **Aggressive caching**: 
   - Lake build artifacts (`.lake/packages`, `.lake/build/lib`, `.lake/build/ir`)
   - Mathlib API documentation (skips rebuilding ~10GB of docs)
2. **Disk space optimization**: Removes unused pre-installed software (~15GB freed)
3. **Single job simplicity**: Easier to debug, no artifact passing overhead

### Build Times

| Scenario | Approximate Time |
|----------|------------------|
| First run (cold cache) | ~15-20 min |
| Subsequent runs (warm cache) | ~8-12 min |

### Local Development

To build the blueprint locally:

```bash
# Install leanblueprint (in a Python virtual environment)
python3 -m venv env
source env/bin/activate
pip install leanblueprint

# Build PDF
leanblueprint pdf

# Build web version
leanblueprint web

# Check declarations
lake exe checkdecls blueprint/lean_decls
```

### What to Commit

The following are **generated files** and should NOT be committed (add to `.gitignore`):

```
blueprint/web/
blueprint/print/
blueprint/lean_decls
```

These are rebuilt by CI on every push. Only commit the source `.tex` files in `blueprint/src/`.

---

## Additional Resources

- [Leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint)
- [Lean 4 documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 documentation](https://leanprover-community.github.io/mathlib4_docs/)