<img src="assets/lean_logo-grey.svg" alt="LEAN"> 

# Radii Polynomial — A LEAN Blueprint Project 

### Live blueprint page 

- https://IlPreteRosso.github.io/LEANearized-RadiiPolynomial  

This repository contains a **Lean 4 blueprint** for the 
**Radii Polynomial Method in Banach Spaces**, including a complete formalization 
of Example 7.7 (analytic square root via computer-assisted proof).

> **Proof flow at a glance:**  
> data → Newton map $T = x - A f(x)$ → a-priori bounds $(Y_0, Z_0, Z_2)$ → radii polynomial $p(r)$ → derivative bound → fixed-point radii lemma → main theorem (existence, uniqueness, nondegeneracy).

## Directory Structure

```
RadiiPolynomial/                    
├── lakefile.toml                   
├── Main.lean                       
├── makefile                        
├── RadiiPolynomial/               
│   ├── RadiiPolyGeneral.lean       # General radii polynomial theorems
│   └── TaylorODE/                  # Example 7.7: Square root formalization
│       ├── ScaledReal.lean         # PosReal, scaled real numbers
│       ├── lpWeighted.lean         # Weighted ℓᵖ spaces (ℓ¹_ν)
│       ├── CauchyProduct.lean      # Cauchy product (convolution)
│       ├── FrechetCauchyProduct.lean  # Fréchet derivative of squaring
│       ├── OperatorNorm.lean       # Block diagonal operators
│       ├── Example_7_7.lean        # Main theorem setup and bounds
│       ├── Computable.lean         # Decidable rational arithmetic
│       ├── Example_7_7_Dyadic.lean # Concrete verification (native_decide)
│       └── Example_7_7_Analytic.lean  # Power series semantics
└── blueprint/                               
    └── src/                       
        ├── content.tex            
        ├── macros/                
        │   ├── common.tex          # Shared LaTeX macros
        │   ├── print.tex           # Print-specific macros
        │   └── web.tex             # Web-specific macros
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
                └── 7-7-Example.tex    # Example 7.7 blueprint
```

---

## Example 7.7: Analytic Square Root

The formalization proves existence of an analytic branch of $\sqrt{\lambda}$ near $\lambda_0 > 0$:

1. **Coefficient space:** Work in weighted $\ell^1_\nu$ with Cauchy product
2. **Fixed-point equation:** $F(\tilde{a}) = \tilde{a} \star \tilde{a} - c = 0$
3. **Bound verification:** $Y_0, Z_0, Z_2$ bounds via rational/dyadic arithmetic
4. **Radii polynomial:** $p(r_0) < 0$ verified by `native_decide`
5. **Semantic bridge:** 
   - Formal level: $\ell^1_\nu \hookrightarrow \mathbb{R}[\![X]\!]$ (PowerSeries)
   - Analytic level: Mertens' theorem shows $\text{eval}(\tilde{a}, z)^2 = \lambda_0 + z$
6. **Branch selection:** IVT argument proves $\text{eval}(\tilde{a}, \lambda - \lambda_0) = \sqrt{\lambda}$

---

## LaTeX ↔ Lean Linking

Link LaTeX statements to Lean declarations using:

| Command | Purpose |
|---------|---------|
| `\lean{declaration_name}` | Links to Lean declaration |
| `\leanok` | Marks formalization complete |
| `\uses{label1, label2}` | Declares dependencies |
| `\label{latex_label}` | Standard LaTeX cross-reference |

**Example:**
```tex
\begin{theorem}[Existence of fixed point]\label{thm:example_7_7_existence}
  \lean{Example_7_7.example_7_7_main_theorem}
  \leanok
  \uses{lem:radii_poly_neg,def:F_map}
  There exists unique $\tilde{a} \in \ell^1_\nu$ with $F(\tilde{a}) = 0$.
\end{theorem}
```

Every `\lean{...}` handle must reference an existing Lean declaration. Run `lake exe checkdecls blueprint/lean_decls` to verify.

---

## Building

```bash
# Build Lean project
lake build

# Check blueprint declarations
lake exe checkdecls blueprint/lean_decls

# Build blueprint (requires leanblueprint)
make
```

---

## Additional Resources

- [Leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint)
- [Lean 4 documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 documentation](https://leanprover-community.github.io/mathlib4_docs/)