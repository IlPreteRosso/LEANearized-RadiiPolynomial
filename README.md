# Radii Polynomial — A Lean 4 Blueprint Project

**Live blueprint:** https://IlPreteRosso.github.io/LEANearized-RadiiPolynomial

This repository formalizes the **Radii Polynomial Method** for computer-assisted proofs
in Banach spaces, including a complete worked example (Section 7.7: analytic square root).

---

## Project Directory 

```
RadiiPolynomial/
├── lakefile.toml
├── makefile
├── RadiiPolynomial/
│   ├── Basic.lean                    # Core utilities
│   ├── RadiiPolyGeneral.lean         # Theorems 2.4.1, 2.4.2, 7.6.1, 7.6.2
│   └── TaylorODE/                    # Chapter 7: Infinite-dimensional theory
│       ├── ScaledReal.lean           # Scaled fiber type for weighted norms
│       ├── lpWeighted.lean           # Weighted ℓᵖ spaces, Banach algebra (§7.4)
│       ├── CauchyProduct.lean        # Cauchy product ring structure
│       ├── FrechetCauchyProduct.lean # Fréchet derivatives (Thm 7.4.7)
│       ├── OperatorNorm.lean         # Operator norms, Prop 7.3.13-14
│       ├── Example_7_7.lean          # Main example: x² = λ
│       ├── Example_7_7_Analytic.lean # Power series interpretation
│       └── Example_7_7_Dyadic.lean   # Computable bound verification
└── blueprint/
    ├── web.toml
    ├── lean_decls
    └── src/
        ├── content.tex
        ├── macros/
        │   └── common.tex
        └── Sections/
            ├── Ch2/
            │   ├── 2-1-ContractionMapping.tex
            │   ├── 2-2-MeanValue.tex
            │   ├── 2-3-Newton.tex
            │   └── 2-4-RadiiPolynomialsFD.tex
            └── Ch7/
                ├── 7-4-WeightedL1BanachAlgebra.tex
                ├── 7-6-RadiiPolynomialBanach.tex
                └── 7-7-Example.tex
```

---

## Core Theory Files

| File | Content | Reference |
|------|---------|-----------|
| `lpWeighted.lean` | Weighted ℓ¹_ν as commutative Banach algebra | §7.4, Def 7.4.1 |
| `CauchyProduct.lean` | Ring axioms via PowerSeries transport | §7.4, Def 7.4.2 |
| `FrechetCauchyProduct.lean` | D(a·b) = a·Db + Da·b | Thm 7.4.7 |
| `OperatorNorm.lean` | Block-diagonal operator bounds | Prop 7.3.13-14 |
| `RadiiPolyGeneral.lean` | Radii polynomial theorems | Thm 2.4.2, 7.6.2 |

### Banach Algebra Structure (Definition 7.4.1)

The file `lpWeighted.lean` establishes ℓ¹_ν as a commutative Banach algebra:

| Axiom | Equation | Lean Instance |
|-------|----------|---------------|
| Associativity | (7.11) | `instRing.mul_assoc` |
| Distributivity | (7.12) | `instRing.left_distrib`, `right_distrib` |
| Scalar compatibility | (7.13) | `instIsScalarTower`, `instSMulCommClass` |
| Submultiplicativity | (7.14) | `instNormedRing.norm_mul_le` |
| Commutativity | | `instCommRing.mul_comm` |
| Unit element | | `instNormOneClass` |
| ℝ-algebra | | `instAlgebra`, `instNormedAlgebra` |

---

## Example 7.7 Workflow

The formalization follows this pipeline:

1. **Coefficient space:** Work in weighted ℓ¹_ν with Cauchy product
2. **Fixed-point equation:** F(ã) = ã ⋆ ã − c = 0
3. **Bound verification:** Y₀, Z₀, Z₂ bounds via rational/dyadic arithmetic
4. **Radii polynomial:** p(r₀) < 0 verified by `native_decide`
5. **Semantic bridge:** ℓ¹_ν ↪ PowerSeries ℝ, then Mertens' theorem
6. **Branch selection:** IVT argument proves eval(ã, λ−λ₀) = √λ

---

## LaTeX ↔ Lean Linking

| Command | Purpose |
|---------|---------|
| `\lean{decl_name}` | Links to Lean declaration |
| `\leanok` | Marks formalization complete |
| `\uses{label1, label2}` | Declares dependencies |

**Example:**
```latex
\begin{theorem}[Submultiplicativity]\label{thm:norm_mul_le}
  \lean{l1Weighted.norm_mul_le}
  \leanok
  \uses{def:l1Weighted,def:CauchyProduct}
  For $a, b \in \ell^1_\nu$: $\|a \star b\| \leq \|a\| \cdot \|b\|$.
\end{theorem}
```

Run `lake exe checkdecls blueprint/lean_decls` to verify all `\lean{...}` references.

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

## References

- [Leanblueprint documentation](https://github.com/PatrickMassot/leanblueprint)
- [Mathlib4 documentation](https://leanprover-community.github.io/mathlib4_docs/)
- Textbook: *Radii Polynomial Approach* (Chapters 2 and 7)