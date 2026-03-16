## Lorenz IVP — Export validated certificate for Lean
# N=30, ν=3/20, x₀=(1,0,0), L=3
#
# Outputs: Numbers.lean with
#   - ā coefficients as exact ℚ arrays
#   - A^(N) blocks as sparse ℚ column arrays
#   - DF^(N) blocks as sparse ℚ column arrays (for defect computation)
#   - Rigorous upper bounds Y₀, Z₀, Z₁, Z₂

using Pkg; Pkg.activate(".")
using RadiiPolynomial, IntervalArithmetic, LinearAlgebra, Printf

const σ_f, ρ_f, β_f = 10.0, 28.0, 8/3
const N  = 30
const ν_f = 0.15
const r★  = 0.1
const Ld  = 3
const M   = 2
const x0  = [1.0, 0.0, 0.0]

# ── 1. Exact rational Taylor recursion ──────────────────────────────────────
σ_r = BigInt(10) // 1;  ρ_r = BigInt(28) // 1;  β_r = BigInt(8) // 3
x0_r = [BigInt(1)//1, BigInt(0)//1, BigInt(0)//1]

a_exact = Array{Rational{BigInt}}(undef, Ld, N+1)
a_exact[:, 1] = x0_r
for k in 0:N-1
    cp13 = sum(a_exact[1, m+1] * a_exact[3, k-m+1] for m in 0:k)
    cp12 = sum(a_exact[1, m+1] * a_exact[2, k-m+1] for m in 0:k)
    a_exact[1, k+2] = σ_r * (a_exact[2, k+1] - a_exact[1, k+1]) // (k+1)
    a_exact[2, k+2] = (ρ_r * a_exact[1, k+1] - a_exact[2, k+1] - cp13) // (k+1)
    a_exact[3, k+2] = (-β_r * a_exact[3, k+1] + cp12) // (k+1)
end
a = Float64.(a_exact)

println("=== Exact ā computed (F(ā)=0 exactly) ===")
for j in 1:Ld
    wn = sum(abs(a[j,k+1]) * ν_f^k for k in 0:N)
    @printf("‖ā_%d‖_{1,ν} = %.6e\n", j, wn)
end

# ── 2. Build DF^(N) and approximate inverse (Float64) ──────────────────────
# Dφ sequences (derivative of nonlinearity)
Dφ = zeros(Ld, Ld, N+1)
Dφ[1,1,1] = -σ_f; Dφ[1,2,1] = σ_f
Dφ[2,1,:] .= -a[3,1:N+1]; Dφ[2,1,1] += ρ_f; Dφ[2,2,1] = -1.0; Dφ[2,3,:] .= -a[1,1:N+1]
Dφ[3,1,:] .= a[2,1:N+1]; Dφ[3,2,:] .= a[1,1:N+1]; Dφ[3,3,1] = -β_f

# Exact rational Dφ
Dφ_r = Array{Rational{BigInt}}(undef, Ld, Ld, N+1)
fill!(Dφ_r, 0//1)
Dφ_r[1,1,1] = -σ_r; Dφ_r[1,2,1] = σ_r
for k in 0:N; Dφ_r[2,1,k+1] = -a_exact[3,k+1]; end; Dφ_r[2,1,1] += ρ_r
Dφ_r[2,2,1] = -1//1
for k in 0:N; Dφ_r[2,3,k+1] = -a_exact[1,k+1]; end
for k in 0:N; Dφ_r[3,1,k+1] = a_exact[2,k+1]; end
for k in 0:N; Dφ_r[3,2,k+1] = a_exact[1,k+1]; end
Dφ_r[3,3,1] = -β_r

# Assemble DF as flat matrix
nt = Ld*(N+1)
DF = zeros(nt, nt)
for j in 1:Ld, jp in 1:Ld, k in 0:N
    row = (j-1)*(N+1)+k+1
    if k == 0
        jp == j && (DF[row, (jp-1)*(N+1)+1] = 1.0)
    else
        jp == j && (DF[row, (jp-1)*(N+1)+k+1] = Float64(k))
        for m in 0:min(k-1,N)
            idx = k-1-m; idx <= N && (DF[row, (jp-1)*(N+1)+m+1] = -Dφ[j,jp,idx+1])
        end
    end
end

# Exact rational DF blocks: DF_block[j,jp] is (N+1)×(N+1)
DF_block = Array{Matrix{Rational{BigInt}}}(undef, Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    blk = zeros(Rational{BigInt}, N+1, N+1)
    for k in 0:N
        if k == 0
            jp == j && (blk[1, 1] = 1//1)
        else
            jp == j && (blk[k+1, k+1] = k//1)
            for m in 0:min(k-1,N)
                idx = k-1-m
                idx <= N && (blk[k+1, m+1] = -Dφ_r[j,jp,idx+1])
            end
        end
    end
    DF_block[j,jp] = blk
end

# Weighted inverse
wr = [ν_f^k for j in 1:Ld for k in 0:N]
wc = [ν_f^(-k) for j in 1:Ld for k in 0:N]
DF_w = Diagonal(wr) * DF * Diagonal(wc)
A_w = inv(DF_w)
A_N = Diagonal(wc) * A_w * Diagonal(wr)

@printf("cond(DF_w) = %.4e\n", cond(DF_w, 1))

# Extract A^(N) blocks and rationalize
A_block = Array{Matrix{Rational{BigInt}}}(undef, Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    blk = zeros(Rational{BigInt}, N+1, N+1)
    for i in 0:N, k in 0:N
        v = A_N[(j-1)*(N+1)+i+1, (jp-1)*(N+1)+k+1]
        if abs(v) > 1e-300  # skip true zeros
            blk[i+1, k+1] = rationalize(BigInt, v, tol=eps(v))
        end
    end
    A_block[j,jp] = blk
end

# ── 3. Interval arithmetic bounds ──────────────────────────────────────────
println("\n=== Interval arithmetic bounds ===")
a_iv = interval.(a); AN_iv = interval.(A_N)
ν_iv = interval(ν_f); σ_iv = interval(σ_f); ρ_iv = interval(ρ_f)
β_iv = interval(8)/interval(3)

MN = M * N
phi_iv = fill(interval(0), Ld, MN+1)
for k in 0:MN
    lin1 = (k <= N) ? σ_iv*(a_iv[2,k+1]-a_iv[1,k+1]) : interval(0)
    lin2 = (k <= N) ? (ρ_iv*a_iv[1,k+1]-a_iv[2,k+1]) : interval(0)
    lin3 = (k <= N) ? (-β_iv*a_iv[3,k+1]) : interval(0)
    cp13 = sum(a_iv[1,m+1]*a_iv[3,k-m+1] for m in max(0,k-N):min(k,N); init=interval(0))
    cp12 = sum(a_iv[1,m+1]*a_iv[2,k-m+1] for m in max(0,k-N):min(k,N); init=interval(0))
    phi_iv[1,k+1] = lin1; phi_iv[2,k+1] = lin2-cp13; phi_iv[3,k+1] = lin3+cp12
end

F_iv = fill(interval(0), Ld, N+1)
for k in 1:N, j in 1:Ld; F_iv[j,k+1] = interval(k)*a_iv[j,k+1]-phi_iv[j,k]; end
F_vec_iv = fill(interval(0), nt)
for j in 1:Ld, k in 0:N; F_vec_iv[(j-1)*(N+1)+k+1] = F_iv[j,k+1]; end
AF_iv = AN_iv * F_vec_iv

# Y₀
Y0_comp = [begin
    fin = sum(abs(AF_iv[(j-1)*(N+1)+k+1])*ν_iv^k for k in 0:N; init=interval(0))
    tail = ν_iv*sum(abs(phi_iv[j,k+1])/interval(k+1)*ν_iv^k for k in N:MN; init=interval(0))
    fin + tail
end for j in 1:Ld]
Y0_ub = maximum(sup.(Y0_comp))

# Z₀
DF_iv = interval.(DF)
B_iv = interval.(Matrix(I(nt))) - AN_iv * DF_iv
Z0_ub = maximum(
    sum(maximum(sup(sum(abs(B_iv[(j-1)*(N+1)+k+1,(jp-1)*(N+1)+kp+1])*ν_iv^k
        for k in 0:N; init=interval(0))/ν_iv^kp) for kp in 0:N) for jp in 1:Ld)
    for j in 1:Ld)

# Z₁
Dφ_iv = interval.(Dφ)
Z1_ub = sup(ν_iv/interval(N+1)) * maximum(
    sum(sup(sum(abs(Dφ_iv[j,jp,k+1])*ν_iv^k for k in 0:N; init=interval(0))) for jp in 1:Ld)
    for j in 1:Ld)

# Z₂
ā_norms_iv = [sup(sum(abs(a_iv[l,k+1])*ν_iv^k for k in 0:N; init=interval(0))) for l in 1:Ld]
K_mat = zeros(Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    mc = maximum(sup(sum(abs(AN_iv[(j-1)*(N+1)+k+1,(jp-1)*(N+1)+kp+1])*ν_iv^k
        for k in 0:N; init=interval(0))/ν_iv^kp) for kp in 0:N)
    K_mat[j,jp] = max(mc, j == jp ? 1.0/(N+1) : 0.0)
end

function compute_zeta(j, m, jp, r)
    z = 0.0
    if j == 2  # α=(1,0,1)
        α = [1,0,1]; v = α[jp] * (α[m] - (jp == m ? 1 : 0))
        if v != 0
            p = 1.0
            for l in 1:Ld; e = α[l]-(jp == l ? 1 : 0)-(m == l ? 1 : 0); e > 0 && (p *= (ā_norms_iv[l]+r)^e); end
            z += v * p
        end
    end
    if j == 3  # α=(1,1,0)
        α = [1,1,0]; v = α[jp] * (α[m] - (jp == m ? 1 : 0))
        if v != 0
            p = 1.0
            for l in 1:Ld; e = α[l]-(jp == l ? 1 : 0)-(m == l ? 1 : 0); e > 0 && (p *= (ā_norms_iv[l]+r)^e); end
            z += v * p
        end
    end
    return z
end

Z2_ub = ν_f * maximum(
    sum(begin s = 0.0
        for mp in 1:Ld; zs = sum(compute_zeta(mp, m, jp, r★) for m in 1:Ld); s += K_mat[j,mp]*zs; end; s
    end for jp in 1:Ld)
    for j in 1:Ld)

# Radii polynomial
b_val = Z0_ub + Z1_ub - 1.0
disc = b_val^2 - 4*Z2_ub*Y0_ub
r_minus = (-b_val - sqrt(disc)) / (2*Z2_ub)

@printf("Y₀ ≤ %.10e\n", Y0_ub)
@printf("Z₀ ≤ %.10e\n", Z0_ub)
@printf("Z₁ ≤ %.10e\n", Z1_ub)
@printf("Z₂ ≤ %.10e\n", Z2_ub)
@printf("Z₀+Z₁-1 = %.10e\n", b_val)
@printf("r₋ ≈ %.6e\n", r_minus)

# Simple rational upper bounds (2 sig figs, rounded up)
function ceil_sig(x, digits=2)
    x <= 0 && return 0.0
    e = floor(Int, log10(x)) - digits + 1
    return ceil(x / 10.0^e) * 10.0^e
end
Y0_q = ceil_sig(Y0_ub);  Z0_q = ceil_sig(Z0_ub)
Z1_q = ceil_sig(Z1_ub);  Z2_q = ceil_sig(Z2_ub)

# Verify with rational bounds
b_q = Z0_q + Z1_q - 1.0
disc_q = b_q^2 - 4*Z2_q*Y0_q
r_q = (-b_q - sqrt(disc_q)) / (2*Z2_q)
@printf("\nRational bounds: Y₀≤%.2e, Z₀≤%.2e, Z₁≤%.2e, Z₂≤%.2e → r₋≈%.2e\n",
    Y0_q, Z0_q, Z1_q, Z2_q, r_q)

# ── 4. Export to Lean ───────────────────────────────────────────────────────
println("\n=== Exporting to Lean ===")

outpath = joinpath(@__DIR__, "..", "RadiiPolynomial", "Example83", "Numbers.lean")
mkpath(dirname(outpath))

# Helper: format rational for Lean
function lean_rat(r::Rational{BigInt})
    r == 0 && return "0"
    d = denominator(r)
    n = numerator(r)
    d == 1 && return "$n"
    return "($n : ℚ) / $d"
end

# Sparse column format: for block (l,j), return Array of (col_index, Array ℚ)
# where only non-zero columns are stored
function sparse_cols(blk::Matrix{Rational{BigInt}})
    result = Tuple{Int, Vector{Rational{BigInt}}}[]
    nrow, ncol = size(blk)
    for c in 1:ncol
        col = blk[:, c]
        if any(!=(0//1), col)
            push!(result, (c-1, col))  # 0-indexed
        end
    end
    return result
end

open(outpath, "w") do io
    println(io, "import Mathlib.Data.Rat.Defs")
    println(io, "")
    println(io, "/-! ## Example 8.3: Lorenz IVP certificate numbers")
    println(io, "")
    println(io, "Generated by `julia/lorenz_ivp_export.jl`.")
    println(io, "Parameters: σ=10, ρ=28, β=8/3, x₀=(1,0,0), N=$N, ν=3/20, r*=$(r★)")
    println(io, "-/")
    println(io, "")
    println(io, "namespace Example83")
    println(io, "")

    # ā coefficients per component
    for j in 1:Ld
        println(io, "/-- ā component $(j-1): Taylor coefficients (modes 0..$(N)) -/")
        println(io, "def abar_$(j-1) : Array ℚ := #[")
        for k in 0:N
            comma = k < N ? "," : ""
            println(io, "  $(lean_rat(a_exact[j, k+1]))$comma")
        end
        println(io, "]")
        println(io, "")
    end

    # A^(N) and DF^(N) in block-column format
    # For each block (l,j), store columns as Array (Array ℚ)
    # The Lean pipeline uses: A.finBlock l j i k = (matCols j k).getD i 0
    # So matCols maps column index k to an Array ℚ of length N+1

    println(io, "/-- A^(N) inverse: block (l,j) column data.")
    println(io, "   `A_col l j k` returns column k of block (l,j) as Array ℚ.")
    println(io, "   Zero columns are omitted (getD returns 0). -/")

    for l in 1:Ld, j in 1:Ld
        scols = sparse_cols(A_block[l, j])
        println(io, "def A_col_$(l-1)_$(j-1) (k : ℕ) : Array ℚ :=")
        if isempty(scols)
            println(io, "  #[]")
        else
            println(io, "  match k with")
            for (ci, col) in scols
                # Find last non-zero entry to trim trailing zeros
                last_nz = findlast(!=(0//1), col)
                trimmed = col[1:last_nz]
                print(io, "  | $ci => #[")
                for (idx, v) in enumerate(trimmed)
                    idx > 1 && print(io, ", ")
                    print(io, lean_rat(v))
                end
                println(io, "]")
            end
            println(io, "  | _ => #[]")
        end
        println(io, "")
    end

    # DF^(N) blocks similarly
    println(io, "/-- DF^(N) derivative: block (l,j) column data. -/")
    for l in 1:Ld, j in 1:Ld
        scols = sparse_cols(DF_block[l, j])
        println(io, "def DF_col_$(l-1)_$(j-1) (k : ℕ) : Array ℚ :=")
        if isempty(scols)
            println(io, "  #[]")
        else
            println(io, "  match k with")
            for (ci, col) in scols
                last_nz = findlast(!=(0//1), col)
                trimmed = col[1:last_nz]
                print(io, "  | $ci => #[")
                for (idx, v) in enumerate(trimmed)
                    idx > 1 && print(io, ", ")
                    print(io, lean_rat(v))
                end
                println(io, "]")
            end
            println(io, "  | _ => #[]")
        end
        println(io, "")
    end

    # Dispatcher: A_col (l j : Fin L) (k : ℕ)
    println(io, "def A_col (l j : Fin 3) (k : ℕ) : Array ℚ :=")
    println(io, "  match l.val, j.val with")
    for l in 0:Ld-1, j in 0:Ld-1
        println(io, "  | $l, $j => A_col_$(l)_$(j) k")
    end
    println(io, "  | _, _ => #[]")
    println(io, "")

    println(io, "def DF_col (l j : Fin 3) (k : ℕ) : Array ℚ :=")
    println(io, "  match l.val, j.val with")
    for l in 0:Ld-1, j in 0:Ld-1
        println(io, "  | $l, $j => DF_col_$(l)_$(j) k")
    end
    println(io, "  | _, _ => #[]")
    println(io, "")

    # Bounds
    function to_lean_bound(x)
        x <= 0 && return "0"
        e = -floor(Int, log10(x)) + 1
        num = ceil(Int, x * 10^e)
        return "$num / $(BigInt(10)^e)"
    end

    println(io, "/-- Rigorous upper bounds for the radii polynomial -/")
    println(io, "def Y₀_bound : ℚ := $(to_lean_bound(Y0_q))")
    println(io, "def Z₀_bound : ℚ := $(to_lean_bound(Z0_q))")
    println(io, "def Z₁_bound : ℚ := $(to_lean_bound(Z1_q))")
    println(io, "def Z₂_bound : ℚ := $(to_lean_bound(Z2_q))")
    println(io, "")
    println(io, "end Example83")
end

# Statistics
total_A_entries = sum(
    sum(count(!=(0//1), col) for (_, col) in sparse_cols(A_block[l,j]); init=0)
    for l in 1:Ld, j in 1:Ld)
total_DF_entries = sum(
    sum(count(!=(0//1), col) for (_, col) in sparse_cols(DF_block[l,j]); init=0)
    for l in 1:Ld, j in 1:Ld)

lines = countlines(outpath)
@printf("Written %d lines to Numbers.lean\n", lines)
@printf("A^(N) non-zero entries: %d / %d (%.1f%%)\n", total_A_entries, (N+1)^2*Ld^2, 100*total_A_entries/((N+1)^2*Ld^2))
@printf("DF^(N) non-zero entries: %d / %d\n", total_DF_entries, (N+1)^2*Ld^2)
println("Done!")
