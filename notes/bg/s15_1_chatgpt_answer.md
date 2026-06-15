# ChatGPT (Pro 拡張) answer — BG Lemma 15.1 per-conjunct reconstruction

(Lane G, 2026-06-15. odd-order project, thinking 14m48s. **Verified — solid; conjunct 8 K≠1 is the intricate part.**)

Standing: N := M_σ. M = KUN, K∩UN=1, U∩N=1, prime supports disjoint (Hall). All conjuncts split on K=⊥ vs K≠⊥.

## Per-conjunct plan (verified)

1. **M ≤ N_G(U⊔M_σ)**: K=⊥ ⟹ U⊔M_σ = M (M=UN) ⟹ trivially normal. K≠⊥ ⟹ U⊔M_σ = M' (Thm 14.7(h): M'=UN) ⟹ M'◁M. (K=⊥ branch must NOT use Thm 14.7.)
2. **IsCyclic K**: K=⊥ trivial. K≠⊥: Thm 14.7(d) (Z=K×K* cyclic ⟹ K cyclic, subgroup of cyclic).
3. **M_σ ≤ M'**: Thm 10.2(c) directly.
4. **M'' ≤ M_σ**: Cor 12.10(b) ((M/M_σ)' abelian) + M_σ≤M' ⟹ π(M')=(M/M_σ)' abelian ⟹ [M',M']≤M_σ ⟹ M''≤M_σ. (quotient algebra)
5. **K≠⊥ package**: M'=U⊔M_σ (Thm 14.7(h)); U abelian (U≅M'/M_σ via 2nd iso, M'/M_σ abelian by Cor 12.10b); IsComplement' (Thm 14.7(h): M=KM', K∩M'=1); coprime (Hall: π(K)⊆κ, π(M')=π(UN)⊆(κ∪σ)ᶜ∪σ, disjoint from κ).
6. **X cyclic τ₂ / 𝓜(C_G(X))={M}**: ∃1≠c∈C_N(X). For 1≠x∈X (σ'-elt, X≤U): Cor 14.3 ⟹ π(x)⊆κ or τ₂; κ impossible (U is (κ∪σ)ᶜ-Hall) ⟹ π(X)⊆τ₂. X≤ Hall τ₂, abelian by Cor 12.10(b) ⟹ X abelian. If X non-cyclic: some Sylow non-cyclic ⟹ ∃A∈ℰ_p²(X)⊆ℰ_p²(U), c∈C_N(X)≤C_N(A)≠1, contradicting Thm 12.5(d) (C_{M_σ}(A)=1 ∀A∈ℰ_p²(U)). ⟹ X cyclic. Then C_G(X)=C_G(gen), Cor 14.3 cyclic case ⟹ 𝓜(C_G(X))={M}.
   - Needs std finite-abelian lemmas: abelian non-cyclic ⟹ ∃ℰ_p² (rank-2 Sylow); subgroup of abelian is abelian.
7. **⟨C_U(x)|x∈M_σ#⟩ abelian**: K=⊥ ⟹ U=E (the §12 complement), Thm 12.12(a) gives abelian A_0 ≥ all C_E(x). K≠⊥ ⟹ U abelian (conj 5) ⟹ join of subgroups of abelian is abelian.
8. **U_0 Frobenius (U≠⊥)**: K=⊥ ⟹ Thm 12.12(b) gives E_0 (=U_0). **K≠⊥ (INTRICATE, the real work)**: U abelian; for p∉τ₂ Sylow S_p acts FPF on M_σ (else conj 6 ⟹ p∈τ₂); for p∈τ₂ replace S_p by cyclic Z_p of full exponent with C_{M_σ}(Ω₁(Z_p))=1 (the C_E(S)=E case of Thm 12.12; rank-2 S=Y×Z, |Y|≤|Z|, Z cyclic, Ω₁(Z)=A_1 from Thm 12.5(f)). U_0 = (∏_{p∉τ₂} S_p)(∏_{p∈τ₂} Z_p); exp(U_0)=exp(U); every 1≠u∈U_0 has C_{M_σ}(u)=1 (via a Sylow component, FPF or Ω₁ argument) ⟹ U_0 M_σ Frobenius kernel M_σ. **U_0 ≠ U in general — componentwise.**

## Verification verdict
Logic sound throughout (cite §14 Thm14.7/Cor14.3 + §12 Cor12.10/Thm12.5/Thm12.12 + §10 Thm10.2, all + light glue). conjuncts 1-7 moderate; **conjunct 8 K≠⊥ is the intricate one** (componentwise Frobenius construction + Thm 12.5(f) Ω₁ + Thm 12.12 C_E(S)=E case). No BG-specific reconstruction gap — the terse steps are standard group theory.

## Formalization plan
Subagent (like Cor 15.5): formalize the 8 conjuncts citing the deps (§14 sorried-citeable, §12/§10 formalized). Expect conjunct 8 K≠⊥ to possibly resist → isolate as one named sorry if so (still 7/8 progress). Verify deps exist: Cor 14.3, Thm 12.12(a)(b), Thm 12.5(d)(f) citeable.
