## Lorenz IVP — Example 8.3
# Compute validated orbit segments for the Lorenz system using Taylor methods.
# Reference: Section 8.2–8.3
#
# Pipeline: floats for ā and A^(N), interval arithmetic for rigorous bounds,
# then rationalize upper bounds for Lean export.

using Pkg
Pkg.activate(".")
using RadiiPolynomial, IntervalArithmetic, LinearAlgebra, Printf

# ── 1. Parameters ───────────────────────────────────────────────────────────
const σ_f, ρ_f, β_f = 10.0, 28.0, 8/3
const N  = 200          # Taylor order
const ν_f = 0.15        # weight = radius of convergence
const r★  = 0.1         # r* for Z₂
const Ld  = 3           # system dimension (L)
const M   = 2           # polynomial degree of Lorenz

# Initial condition
const x0 = [1.0, 0.0, 0.0]

# ── 2. Taylor recursion (Float64) ───────────────────────────────────────────
a = zeros(Ld, N+1)
a[:, 1] = x0

for k in 0:N-1
    cp13 = sum(a[1, m+1] * a[3, k-m+1] for m in 0:k)
    cp12 = sum(a[1, m+1] * a[2, k-m+1] for m in 0:k)
    a[1, k+2] = σ_f * (a[2, k+1] - a[1, k+1]) / (k+1)
    a[2, k+2] = (ρ_f * a[1, k+1] - a[2, k+1] - cp13) / (k+1)
    a[3, k+2] = (-β_f * a[3, k+1] + cp12) / (k+1)
end

println("=== Taylor coefficients (first 6 + last) ===")
for n in 0:5
    @printf("a_%d = [%.8e, %.8e, %.8e]\n", n, a[1,n+1], a[2,n+1], a[3,n+1])
end
@printf("a_%d = [%.4e, %.4e, %.4e]\n", N, a[1,N+1], a[2,N+1], a[3,N+1])

# Weighted norms (float)
for j in 1:Ld
    wn = sum(abs(a[j, k+1]) * ν_f^k for k in 0:N)
    @printf("‖ā_%d‖_{1,ν} = %.6e\n", j, wn)
end

# ── 3. Build DF^(N) and approximate inverse (Float64) ──────────────────────
# D_{j'}φ_j(ā) for Lorenz
Dφ = zeros(Ld, Ld, N+1)
Dφ[1, 1, 1] = -σ_f;  Dφ[1, 2, 1] = σ_f
Dφ[2, 1, :] .= -a[3, 1:N+1];  Dφ[2, 1, 1] += ρ_f
Dφ[2, 2, 1] = -1.0;  Dφ[2, 3, :] .= -a[1, 1:N+1]
Dφ[3, 1, :] .= a[2, 1:N+1];  Dφ[3, 2, :] .= a[1, 1:N+1];  Dφ[3, 3, 1] = -β_f

n_total = Ld * (N + 1)
DF = zeros(n_total, n_total)
for j in 1:Ld, jp in 1:Ld, k in 0:N
    row = (j-1)*(N+1) + k + 1
    if k == 0
        jp == j && (DF[row, (jp-1)*(N+1)+1] = 1.0)
    else
        jp == j && (DF[row, (jp-1)*(N+1)+k+1] = Float64(k))
        for m in 0:min(k-1, N)
            idx = k - 1 - m
            idx <= N && (DF[row, (jp-1)*(N+1)+m+1] = -Dφ[j, jp, idx+1])
        end
    end
end

# Weighted scaling: D_w = diag(ν^k) · DF · diag(ν^{-m})
w_row = zeros(n_total); w_col = zeros(n_total)
for j in 1:Ld, k in 0:N
    idx = (j-1)*(N+1) + k + 1
    w_row[idx] = ν_f^k;  w_col[idx] = ν_f^(-k)
end
DF_w = Diagonal(w_row) * DF * Diagonal(w_col)
@printf("cond(DF_weighted, 1) ≈ %.4e\n", cond(DF_w, 1))

# Float inverse
A_w = inv(DF_w)
A_N = Diagonal(w_col) * A_w * Diagonal(w_row)

# Quick check in weighted norm
B_w = I(n_total) - A_w * DF_w
@printf("‖I - A_w·DF_w‖₁ = %.4e  (weighted float check)\n", opnorm(B_w, 1))

# ── 4. Interval arithmetic: rigorous bounds ────────────────────────────────
println("\n=== Interval arithmetic validation ===")

# Promote ā and A^(N) to intervals
a_iv  = interval.(a)
AN_iv = interval.(A_N)
ν_iv  = interval(ν_f)
σ_iv  = interval(σ_f)
ρ_iv  = interval(ρ_f)
β_iv  = interval(8) / interval(3)  # exact

# --- φ(ā) up to mode M*N = 2N ---
MN = M * N
phi_iv = fill(interval(0), Ld, MN+1)
for k in 0:MN
    # Linear parts (only for k ≤ N)
    lin1 = (k <= N) ? σ_iv * (a_iv[2, k+1] - a_iv[1, k+1]) : interval(0)
    lin2 = (k <= N) ? (ρ_iv * a_iv[1, k+1] - a_iv[2, k+1]) : interval(0)
    lin3 = (k <= N) ? (-β_iv * a_iv[3, k+1]) : interval(0)
    # Cauchy products
    cp13 = sum(a_iv[1, m+1] * a_iv[3, k-m+1] for m in max(0,k-N):min(k,N); init=interval(0))
    cp12 = sum(a_iv[1, m+1] * a_iv[2, k-m+1] for m in max(0,k-N):min(k,N); init=interval(0))
    phi_iv[1, k+1] = lin1
    phi_iv[2, k+1] = lin2 - cp13
    phi_iv[3, k+1] = lin3 + cp12
end

# --- F(ā) residual ---
F_iv = fill(interval(0), Ld, N+1)
for k in 1:N, j in 1:Ld
    F_iv[j, k+1] = interval(k) * a_iv[j, k+1] - phi_iv[j, k]
end

# F_vec for matrix multiply
F_vec_iv = fill(interval(0), n_total)
for j in 1:Ld, k in 0:N
    F_vec_iv[(j-1)*(N+1)+k+1] = F_iv[j, k+1]
end

# A^(N) · F(ā) in intervals
AF_iv = AN_iv * F_vec_iv

# --- Y₀ (interval) ---
println("--- Y₀ ---")
Y0_iv = fill(interval(0), Ld)
for j in 1:Ld
    # Finite part: Σ_k |AF(ā)_{j,k}| · ν^k
    fin = sum(abs(AF_iv[(j-1)*(N+1)+k+1]) * ν_iv^k for k in 0:N; init=interval(0))
    # Tail part: ν · Σ_{k=N}^{MN} (1/(k+1)) |φ_j(ā)_k| · ν^k
    tail = ν_iv * sum(abs(phi_iv[j, k+1]) / interval(k+1) * ν_iv^k for k in N:MN; init=interval(0))
    Y0_iv[j] = fin + tail
    @printf("Y₀^(%d) ∈ [%.6e, %.6e]\n", j, inf(Y0_iv[j]), sup(Y0_iv[j]))
end
Y0_ub = maximum(sup.(Y0_iv))
@printf("Y₀ ≤ %.6e\n", Y0_ub)

# --- Z₀ (interval) ---
println("\n--- Z₀ ---")
# B = I - A^(N) · DF^(N) in intervals
DF_iv = interval.(DF)
B_iv = interval.(Matrix(I(n_total))) - AN_iv * DF_iv

Z0_block = fill(interval(0), Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    max_col = interval(0)
    for kp in 0:N
        col_sum = sum(abs(B_iv[(j-1)*(N+1)+k+1, (jp-1)*(N+1)+kp+1]) * ν_iv^k for k in 0:N; init=interval(0))
        col_sum = col_sum / ν_iv^kp
        max_col = IntervalArithmetic.hull(max_col, col_sum)
    end
    Z0_block[j, jp] = max_col
end
Z0_row_iv = [sum(Z0_block[j, :]) for j in 1:Ld]
Z0_ub = maximum(sup.(Z0_row_iv))
@printf("Z₀ ≤ %.6e\n", Z0_ub)

# --- Z₁ (interval) ---
println("\n--- Z₁ ---")
Dφ_iv = interval.(Dφ)
Z1_block = fill(interval(0), Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    Z1_block[j, jp] = sum(abs(Dφ_iv[j, jp, k+1]) * ν_iv^k for k in 0:N; init=interval(0))
end
Z1_row_iv = [sum(Z1_block[j, :]) for j in 1:Ld]
Z1_ub = sup(ν_iv / interval(N+1) * interval(maximum(sup.(Z1_row_iv))))
@printf("Z₁ ≤ %.6e\n", Z1_ub)

# --- Z₂ (interval) ---
println("\n--- Z₂ ---")
# K_{j,j'} = max{ max_{k'} (1/ν^{k'}) Σ_k |A^(N)_{j,j'}_{k,k'}| ν^k,  δ/(N+1) }
K_iv = fill(interval(0), Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    max_col = interval(0)
    for kp in 0:N
        col_sum = sum(abs(AN_iv[(j-1)*(N+1)+k+1, (jp-1)*(N+1)+kp+1]) * ν_iv^k for k in 0:N; init=interval(0))
        col_sum = col_sum / ν_iv^kp
        max_col = IntervalArithmetic.hull(max_col, col_sum)
    end
    tail = (j == jp) ? interval(1) / interval(N+1) : interval(0)
    K_iv[j, jp] = IntervalArithmetic.hull(max_col, tail)
end

# ā norms (interval)
ā_norms_iv = [sum(abs(a_iv[l, k+1]) * ν_iv^k for k in 0:N; init=interval(0)) for l in 1:Ld]

# ζ_{j,m,j'}(r*) for Lorenz (M=2, bilinear: x₁x₃ in φ₂, x₁x₂ in φ₃)
function compute_zeta_iv(j, m, jp, r)
    total = interval(0)
    # α = (1,0,1), j=2, c=-1
    if j == 2
        α = [1, 0, 1]
        val = α[jp] * (α[m] - (jp == m ? 1 : 0))
        if val != 0
            prod_term = interval(1)
            for l in 1:Ld
                e = α[l] - (jp == l ? 1 : 0) - (m == l ? 1 : 0)
                e > 0 && (prod_term *= (ā_norms_iv[l] + interval(r))^e)
                e < 0 && (prod_term = interval(0))
            end
            total += interval(val) * prod_term
        end
    end
    # α = (1,1,0), j=3, c=+1
    if j == 3
        α = [1, 1, 0]
        val = α[jp] * (α[m] - (jp == m ? 1 : 0))
        if val != 0
            prod_term = interval(1)
            for l in 1:Ld
                e = α[l] - (jp == l ? 1 : 0) - (m == l ? 1 : 0)
                e > 0 && (prod_term *= (ā_norms_iv[l] + interval(r))^e)
                e < 0 && (prod_term = interval(0))
            end
            total += interval(val) * prod_term
        end
    end
    return total
end

Z2_block = fill(interval(0), Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    s = interval(0)
    for mp in 1:Ld
        zeta_sum = sum(compute_zeta_iv(mp, m, jp, r★) for m in 1:Ld; init=interval(0))
        s += K_iv[j, mp] * zeta_sum
    end
    Z2_block[j, jp] = s
end
Z2_row_iv = [sum(Z2_block[j, :]) for j in 1:Ld]
Z2_ub = sup(ν_iv * interval(maximum(sup.(Z2_row_iv))))
@printf("Z₂ ≤ %.6e\n", Z2_ub)

# ── 5. Radii polynomial check ──────────────────────────────────────────────
println("\n=== Radii polynomial (using interval upper bounds) ===")
@printf("Y₀ ≤ %.10e\n", Y0_ub)
@printf("Z₀ ≤ %.10e\n", Z0_ub)
@printf("Z₁ ≤ %.10e\n", Z1_ub)
@printf("Z₂ ≤ %.10e\n", Z2_ub)

b_val = Z0_ub + Z1_ub - 1.0
@printf("Z₀ + Z₁ - 1 ≤ %.10e\n", b_val)

disc = b_val^2 - 4 * Z2_ub * Y0_ub
@printf("Discriminant ≥ %.10e\n", disc)

if disc > 0 && b_val < 0
    r_minus = (-b_val - sqrt(disc)) / (2 * Z2_ub)
    r_plus  = (-b_val + sqrt(disc)) / (2 * Z2_ub)
    @printf("r₋ ≈ %.10e\n", r_minus)
    @printf("r₊ ≈ %.10e\n", r_plus)

    # Pick r₀ slightly above r₋
    r0 = r_minus * 2  # generous pick
    p_r0 = Z2_ub * r0^2 + b_val * r0 + Y0_ub
    @printf("p(r₀=%.2e) = %.6e  (should be < 0)\n", r0, p_r0)

    if p_r0 < 0 && r0 < r★
        println("✓ VALIDATED!")
        @printf("  Proven: ∃ ã with ‖ã-ā‖ ≤ %.2e solving Lorenz IVP for t ∈ (%.2f, %.2f)\n", r0, -ν_f, ν_f)
    end
else
    println("✗ FAILED")
end

# ── 6. Rational upper bounds for Lean ───────────────────────────────────────
println("\n=== Rational upper bounds for Lean export ===")

# Round up to simple rationals
function rationalize_ub(x::Float64; digits=3)
    # Round up to `digits` significant figures
    if x == 0.0; return 0 // 1; end
    e = floor(Int, log10(abs(x))) - digits + 1
    mantissa = ceil(Int, x / 10.0^e)
    return mantissa // (10^(-e))  # may need adjustment for sign of e
end

# Simpler: just print as "numerator // denominator" with generous rounding
println("-- Use these in Lean certificate --")
@printf("Y₀_ub : ℚ := %d / 10^%d  -- %.2e\n",
    ceil(Int, Y0_ub * 1e17), 17, Y0_ub)
@printf("Z₀_ub : ℚ := %d / 10^%d  -- %.2e\n",
    ceil(Int, Z0_ub * 1e14), 14, Z0_ub)
@printf("Z₁_ub : ℚ := %d / 10^%d  -- %.2e\n",
    ceil(Int, Z1_ub * 1e3), 3, Z1_ub)
@printf("Z₂_ub : ℚ := %d / 10^%d  -- %.2e\n",
    ceil(Int, Z2_ub * 10), 1, Z2_ub)

println("\nDone!")
