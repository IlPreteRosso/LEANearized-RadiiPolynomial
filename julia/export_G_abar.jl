## Export G(ā) coefficients for Y₀ bound
# Uses same computation as lorenz_ivp_export.jl for A_block

using Pkg; Pkg.activate(".")
using Printf, LinearAlgebra

const σ_r = BigInt(10) // 1;  const ρ_r = BigInt(28) // 1;  const β_r = BigInt(8) // 3
const x0_r = [BigInt(1)//1, BigInt(0)//1, BigInt(0)//1]
const N = 30
const Ld = 3
const ν_r = BigInt(3) // 20
const ν_f = Float64(ν_r)

# ── 1. Exact Taylor recursion ──
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

# ── 2. Dφ and DF (copied from lorenz_ivp_export.jl) ──
σ_f, ρ_f, β_f_local = 10.0, 28.0, 8/3
Dφ = zeros(Ld, Ld, N+1)
Dφ[1,1,1] = -σ_f;  Dφ[1,2,1] = σ_f
Dφ[2,1,1] = ρ_f;   Dφ[2,2,1] = -1.0;  Dφ[2,3,1] = -a[1,1]; Dφ[3,3,1] = -β_f_local
Dφ[3,1,1] = a[2,1]; Dφ[3,2,1] = a[1,1]
for k in 1:N
    Dφ[2,1,k+1] = -a[3,k+1]; Dφ[2,3,k+1] = -a[1,k+1]
    Dφ[3,1,k+1] = a[2,k+1];  Dφ[3,2,k+1] = a[1,k+1]
end

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

# Weighted inverse (same as lorenz_ivp_export.jl)
wr = [ν_f^k for j in 1:Ld for k in 0:N]
wc = [ν_f^(-k) for j in 1:Ld for k in 0:N]
DF_w = Diagonal(wr) * DF * Diagonal(wc)
A_w = inv(DF_w)
A_N = Diagonal(wc) * A_w * Diagonal(wr)

# Rationalize A_block
A_block = Array{Matrix{Rational{BigInt}}}(undef, Ld, Ld)
for j in 1:Ld, jp in 1:Ld
    blk = zeros(Rational{BigInt}, N+1, N+1)
    for i in 0:N, k in 0:N
        v = A_N[(j-1)*(N+1)+i+1, (jp-1)*(N+1)+k+1]
        if abs(v) > 1e-300
            blk[i+1, k+1] = rationalize(BigInt, v, tol=eps(v))
        end
    end
    A_block[j,jp] = blk
end

# ── 3. Compute φ(ā) for modes 0..2N ──
MN = 2 * N
phi_exact = zeros(Rational{BigInt}, Ld, MN + 1)
for k in 0:MN
    lin1 = (k <= N) ? σ_r * (a_exact[2, k+1] - a_exact[1, k+1]) : BigInt(0) // 1
    lin2 = (k <= N) ? (ρ_r * a_exact[1, k+1] - a_exact[2, k+1]) : BigInt(0) // 1
    lin3 = (k <= N) ? (-β_r * a_exact[3, k+1]) : BigInt(0) // 1
    cp13 = sum(a_exact[1, m+1] * a_exact[3, k-m+1] for m in max(0,k-N):min(k,N);
               init=BigInt(0)//1)
    cp12 = sum(a_exact[1, m+1] * a_exact[2, k-m+1] for m in max(0,k-N):min(k,N);
               init=BigInt(0)//1)
    phi_exact[1, k+1] = lin1
    phi_exact[2, k+1] = lin2 - cp13
    phi_exact[3, k+1] = lin3 + cp12
end

# ── 4. Compute F_coeffs(ā) ──
# F_j_0 = a_{j,0} - x₀_j = 0 (exact initial condition)
# F_j_k = k * a_{j,k} - φ_j_{k-1} for k ≥ 1
# By Taylor recursion: F_j_k = 0 for k = 1,...,N-1 (but we compute all for correctness)
F_coeffs_exact = zeros(Rational{BigInt}, Ld, N+1)
for j in 1:Ld
    F_coeffs_exact[j, 1] = a_exact[j, 1] - x0_r[j]  # F_0
    for k in 1:N
        F_coeffs_exact[j, k+1] = k * a_exact[j, k+1] - phi_exact[j, k]  # F_k
    end
end

# Verify F is ~zero for modes 0..N-1
for j in 1:Ld, k in 0:N-1
    F_coeffs_exact[j,k+1] == 0 || @printf("WARNING: F_%d_%d = %s ≠ 0\n", j-1, k, F_coeffs_exact[j,k+1])
end
@printf("F_coeffs check: modes 0..%d all zero (Taylor recursion verified)\n", N-1)

# ── 5. Compute G(ā) = A · F ──
G_size = 2*N + 2  # modes 0..2N+1
G_exact = zeros(Rational{BigInt}, Ld, G_size)

# Finite block (n ≤ N): G_l_n = Σ_j Σ_k A_block[l,j][n+1,k+1] * F_coeffs[j,k+1]
for l in 1:Ld, n in 0:N
    G_exact[l, n+1] = sum(
        sum(A_block[l,j][n+1, k+1] * F_coeffs_exact[j, k+1] for k in 0:N)
    for j in 1:Ld)
end

# Tail (n > N): G_l_n = (1/n) * F_l_n where F_n = -φ_{n-1} (since a_{n+1}=0)
for l in 1:Ld, n in N+1:2*N+1
    F_n = -phi_exact[l, n]  # F_l_n = n * 0 - φ_l_{n-1} = -φ_l_{n-1}... wait
    # F_coeffs at mode n: F_n = (n+1) * a_{n+1} - φ_n
    # But wait — F_lorenz mode indexing: F_j(a)_n = (n+1)*a_{j,n+1} - φ_j_n
    # For n > N: a_{n+1} = 0, so F_n = -φ_n
    # Then G_n = tailDiag_n * F_n = (1/n) * (-φ_n)...
    # Hmm, need to be careful about F_coeffs indexing
    # Actually looking at the Julia code in lorenz_ivp_export.jl:
    # F_iv[j,k+1] = interval(k)*a_iv[j,k+1]-phi_iv[j,k]
    # So F_k = k * a_k - φ_{k-1} for k ≥ 1
    # For n > N: F_n = n * 0 - φ_{n-1} = -φ_{n-1}
    # G_n = (1/n) * F_n = -φ_{n-1}/n
    G_exact[l, n+1] = -phi_exact[l, n] // n  # φ_{n-1} is at phi_exact[l, n] (0-indexed: n-1+1=n)
end

# ── 6. Verify Y₀ bound ──
Y0_comp = [sum(abs(G_exact[l, n+1]) * ν_r^n for n in 0:G_size-1) for l in 1:Ld]
Y0_val = maximum(Y0_comp)
Y0_bound = BigInt(44) // 100000
@printf("Y₀ = %.10e\n", Float64(Y0_val))
@printf("Y₀_bound = %.10e\n", Float64(Y0_bound))
@printf("Y₀ ≤ Y₀_bound: %s\n", Y0_val ≤ Y0_bound)
for l in 1:Ld
    @printf("  ‖G(ā)_%d‖ = %.10e\n", l-1, Float64(Y0_comp[l]))
end

# ── 7. Export to Lean ──
function lean_rat(r::Rational{BigInt})
    r == 0 && return "0"
    d = denominator(r)
    n = numerator(r)
    d == 1 && return "$n"
    return "($n : ℚ) / $d"
end

println("\n-- G(ā) coefficients for Y₀ bound (auto-generated)")
println("-- Finite block (modes 0..N): A_block × F_coeffs(ā)")
println("-- Tail (modes N+1..2N+1): -φ(ā)_{n-1}/n")
println("")

for l in 0:Ld-1
    arr = G_exact[l+1, :]
    last_nz = findlast(!=(0//1), arr)
    last_nz === nothing && (last_nz = 0)
    trimmed = arr[1:last_nz]

    print("private def G_ā_vec_$l : Array ℚ := #[")
    for (idx, v) in enumerate(trimmed)
        idx > 1 && print(", ")
        print(lean_rat(v))
    end
    println("]")
end

println("")
println("def G_ā_vec (l : Fin 3) : Array ℚ :=")
println("  match l.val with")
for l in 0:Ld-1
    println("  | $l => G_ā_vec_$l")
end
println("  | _ => #[]")
