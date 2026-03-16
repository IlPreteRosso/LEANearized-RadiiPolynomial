## Lorenz IVP — sweep N to find minimum that validates
using Pkg; Pkg.activate(".")
using RadiiPolynomial, IntervalArithmetic, LinearAlgebra, Printf

const σ_f, ρ_f, β_f = 10.0, 28.0, 8/3
const ν_f = 0.15
const r★  = 0.1
const Ld  = 3
const M   = 2

function validate_lorenz(N; x0=[1.0, 0.0, 0.0], verbose=false)
    # Taylor recursion
    a = zeros(Ld, N+1); a[:, 1] = x0
    for k in 0:N-1
        cp13 = sum(a[1, m+1] * a[3, k-m+1] for m in 0:k)
        cp12 = sum(a[1, m+1] * a[2, k-m+1] for m in 0:k)
        a[1, k+2] = σ_f * (a[2, k+1] - a[1, k+1]) / (k+1)
        a[2, k+2] = (ρ_f * a[1, k+1] - a[2, k+1] - cp13) / (k+1)
        a[3, k+2] = (-β_f * a[3, k+1] + cp12) / (k+1)
    end

    # DF
    Dφ = zeros(Ld, Ld, N+1)
    Dφ[1,1,1] = -σ_f; Dφ[1,2,1] = σ_f
    Dφ[2,1,:] .= -a[3,1:N+1]; Dφ[2,1,1] += ρ_f; Dφ[2,2,1] = -1.0; Dφ[2,3,:] .= -a[1,1:N+1]
    Dφ[3,1,:] .= a[2,1:N+1]; Dφ[3,2,:] .= a[1,1:N+1]; Dφ[3,3,1] = -β_f

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

    # Weighted inverse
    wr = [ν_f^k for j in 1:Ld for k in 0:N]
    wc = [ν_f^(-k) for j in 1:Ld for k in 0:N]
    DF_w = Diagonal(wr) * DF * Diagonal(wc)
    A_w = inv(DF_w)
    A_N = Diagonal(wc) * A_w * Diagonal(wr)

    # Interval bounds
    a_iv = interval.(a); AN_iv = interval.(A_N); ν_iv = interval(ν_f)
    σ_iv = interval(σ_f); ρ_iv = interval(ρ_f); β_iv = interval(8)/interval(3)

    # φ(ā)
    MN = M*N
    phi_iv = fill(interval(0), Ld, MN+1)
    for k in 0:MN
        lin1 = (k<=N) ? σ_iv*(a_iv[2,k+1]-a_iv[1,k+1]) : interval(0)
        lin2 = (k<=N) ? (ρ_iv*a_iv[1,k+1]-a_iv[2,k+1]) : interval(0)
        lin3 = (k<=N) ? (-β_iv*a_iv[3,k+1]) : interval(0)
        cp13 = sum(a_iv[1,m+1]*a_iv[3,k-m+1] for m in max(0,k-N):min(k,N); init=interval(0))
        cp12 = sum(a_iv[1,m+1]*a_iv[2,k-m+1] for m in max(0,k-N):min(k,N); init=interval(0))
        phi_iv[1,k+1] = lin1; phi_iv[2,k+1] = lin2-cp13; phi_iv[3,k+1] = lin3+cp12
    end

    # F(ā)
    F_iv = fill(interval(0), Ld, N+1)
    for k in 1:N, j in 1:Ld; F_iv[j,k+1] = interval(k)*a_iv[j,k+1]-phi_iv[j,k]; end
    F_vec = fill(interval(0), nt)
    for j in 1:Ld, k in 0:N; F_vec[(j-1)*(N+1)+k+1] = F_iv[j,k+1]; end
    AF_iv = AN_iv * F_vec

    # Y₀
    Y0_ub = maximum(
        sup(sum(abs(AF_iv[(j-1)*(N+1)+k+1])*ν_iv^k for k in 0:N; init=interval(0))
          + ν_iv*sum(abs(phi_iv[j,k+1])/interval(k+1)*ν_iv^k for k in N:MN; init=interval(0)))
        for j in 1:Ld)

    # Z₀
    DF_iv = interval.(DF); B_iv = interval.(Matrix(I(nt))) - AN_iv*DF_iv
    Z0_ub = maximum(
        sum(maximum(sup(sum(abs(B_iv[(j-1)*(N+1)+k+1,(jp-1)*(N+1)+kp+1])*ν_iv^k for k in 0:N; init=interval(0))/ν_iv^kp) for kp in 0:N)
            for jp in 1:Ld)
        for j in 1:Ld)

    # Z₁
    Dφ_iv = interval.(Dφ)
    Z1_ub = sup(ν_iv/interval(N+1)) * maximum(
        sum(sup(sum(abs(Dφ_iv[j,jp,k+1])*ν_iv^k for k in 0:N; init=interval(0))) for jp in 1:Ld)
        for j in 1:Ld)

    # Z₂ (simplified for Lorenz bilinear)
    ā_norms = [sup(sum(abs(a_iv[l,k+1])*ν_iv^k for k in 0:N; init=interval(0))) for l in 1:Ld]
    K = zeros(Ld, Ld)
    for j in 1:Ld, jp in 1:Ld
        mc = maximum(sup(sum(abs(AN_iv[(j-1)*(N+1)+k+1,(jp-1)*(N+1)+kp+1])*ν_iv^k for k in 0:N; init=interval(0))/ν_iv^kp) for kp in 0:N)
        K[j,jp] = max(mc, j==jp ? 1.0/(N+1) : 0.0)
    end
    # For Lorenz: ζ = 1 for the cross terms, 0 otherwise (bilinear, degree 2)
    # φ₂ has -x₁x₃: D²₁₃=D²₃₁=-1; φ₃ has x₁x₂: D²₁₂=D²₂₁=+1
    Z2_ub = ν_f * maximum(
        sum(begin
            s = 0.0
            for mp in 1:Ld
                zs = 0.0
                for m in 1:Ld
                    # compute_zeta(mp, m, jp, r★)
                    z = 0.0
                    if mp == 2  # α=(1,0,1)
                        α = [1,0,1]; v = α[jp] * (α[m] - (jp == m ? 1 : 0))
                        if v != 0
                            p = 1.0
                            for l in 1:Ld
                                e = α[l] - (jp == l ? 1 : 0) - (m == l ? 1 : 0)
                                e > 0 && (p *= (ā_norms[l] + r★)^e)
                            end
                            z += v * p
                        end
                    end
                    if mp == 3  # α=(1,1,0)
                        α = [1,1,0]; v = α[jp] * (α[m] - (jp == m ? 1 : 0))
                        if v != 0
                            p = 1.0
                            for l in 1:Ld
                                e = α[l] - (jp == l ? 1 : 0) - (m == l ? 1 : 0)
                                e > 0 && (p *= (ā_norms[l] + r★)^e)
                            end
                            z += v * p
                        end
                    end
                    zs += z
                end
                s += K[j,mp] * zs
            end
            s
        end for jp in 1:Ld)
        for j in 1:Ld)

    b_val = Z0_ub + Z1_ub - 1.0
    disc = b_val^2 - 4*Z2_ub*Y0_ub
    ok = disc > 0 && b_val < 0
    r_minus = ok ? (-b_val - sqrt(disc))/(2*Z2_ub) : NaN

    if verbose
        @printf("  Y₀=%.2e  Z₀=%.2e  Z₁=%.4f  Z₂=%.2f  b=%.4f  r₋=%.2e\n",
                Y0_ub, Z0_ub, Z1_ub, Z2_ub, b_val, r_minus)
    end
    return ok, Y0_ub, Z0_ub, Z1_ub, Z2_ub, r_minus
end

println("Sweeping N values...")
for N in [5, 10, 15, 20, 25, 30, 40, 50]
    ok, Y0, Z0, Z1, Z2, rm = validate_lorenz(N; verbose=false)
    status = ok ? "✓" : "✗"
    @printf("N=%3d: %s  Y₀=%.2e  Z₀=%.2e  Z₁=%.4f  Z₂=%.2f  r₋=%.2e  (size=%d)\n",
            N, status, Y0, Z0, Z1, Z2, rm, 3*(N+1))
end
