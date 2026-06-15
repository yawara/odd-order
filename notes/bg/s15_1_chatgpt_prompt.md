# ChatGPT (Pro 拡張) prompt — BG Lemma 15.1 full proof reconstruction

(Lane G, 2026-06-15. odd-order project. Verify before formalizing.)

---

(This odd-order project has the Bender-Glauberman textbook "Local Analysis for the Odd Order Theorem" (LMS LNS 188, 1994) as a PDF. Please consult it directly — Lemma 15.1 (statement L4166, proof L4174), and the cited results: Theorem 14.7, Corollary 14.3, Corollary 12.10, Theorem 12.5, Theorem 12.12, Theorem 10.2 — to ground and verify.)

I am formalizing BG Lemma 15.1 in Lean 4 and need its proof reconstructed in FULL rigorous detail. The textbook proof is very terse (cites Thm 14.7(d)(h), Cor 12.10(b), Thm 10.2(c), Cor 14.3, Thm 12.5(d), Thm 12.12(d)(e), with phrases like "obvious from the very short and easy argument"), so I need each step made explicit and mapped to which cited result discharges it.

SETUP. G minimal simple of odd order; M maximal. σ(M)/τ₁/τ₂/τ₃ partition π(M); M_σ = normal Hall σ-subgroup; M' = derived; M_F = max nilpotent normal Hall; κ(M) the kappa prime set, K a Hall κ(M)-subgroup, U a Hall (κ∪σ)ᶜ-subgroup (so M = K U M_σ); τ₂(M) = rank-2 primes outside σ.

LEMMA 15.1 (BG, the 5 parts):
(a) UM_σ ◁ M = KUM_σ, K is cyclic, M_σ ⊆ M', and M'/M_σ is abelian.
(b) If K ≠ 1, then M' = UM_σ and U is abelian.
(c) If X is a nonidentity subgroup of U with C_{M_σ}(X) ≠ 1, then 𝓜(C_G(X)) = {M} and X is a cyclic τ₂(M)-subgroup.
(d) ⟨ C_U(x) | x ∈ M_σ# ⟩ is abelian.
(e) If U ≠ 1, then U contains a subgroup U_0 of the same exponent as U such that U_0 M_σ is a Frobenius group with kernel M_σ.

BG proof, verbatim: "By Theorem 14.7(d) and (h), K is cyclic and if K ≠ 1, then M' = UM_σ. By Corollary 12.10(b), (M/M_σ)' is abelian and, by Theorem 10.2(c), M_σ ⊆ M'. This proves (a) and (b). By Corollary 14.3, the group X in (c) must be a τ₂(M)-group and we have 𝓜(C_G(X)) = {M} if X is cyclic. Since M has an abelian Hall τ₂(M)-subgroup by Corollary 12.10(b) and, because C_{M_σ}(A) = 1 for every A ∈ ℰ_p²(U) by Theorem 12.5(d), X is indeed cyclic. In Theorem 12.12, (d) and (e) have been proved under the assumption that κ(M) is empty, i.e., K = 1. If K ≠ 1, then U is abelian by (b). In this case (d) is trivial and (e) is obvious from the very short and easy argument in the proof of Theorem 12.12 that deals with the case that C_E(S) = E."

THE LEAN CONJUNCTS I must produce (theorem `typeP_auxiliary_structure`, hypotheses: M maximal, hK: K.subgroupOf M is a Hall κ(M)-subgroup, hKstar: Kstar = M_σ ⊓ C_G(K), hU: U.subgroupOf M is a Hall (κ∪σ)ᶜ-subgroup):
1. M ≤ N_G(U ⊔ M_σ).
2. IsCyclic K.
3. M_σ ≤ M' (derivedInG M).
4. M'' (derivedInG (derivedInG M)) ≤ M_σ.
5. K ≠ 1 → (M' = U ⊔ M_σ ∧ U abelian ∧ IsComplement' (M'.subgroupOf M) (K.subgroupOf M) ∧ Coprime |M'.subgroupOf M| |K.subgroupOf M|).
6. ∀ X ≤ U, X ≠ 1, M_σ ⊓ C_G(X) ≠ 1 → (𝓜(C_G(X)) = {M} ∧ IsCyclic X ∧ π(X) ⊆ τ₂(M)).
7. ⟨C_U(x) | x ∈ M_σ#⟩ abelian (encoded as `centralizerGeneratedBySigma M U` abelian).
8. U ≠ 1 → ∃ U_0 ≤ U, exponent U_0 = exponent U, U_0 M_σ Frobenius with kernel M_σ.

QUESTIONS (please address each Lean conjunct):
A. Conjunct 1 (M ≤ N_G(U ⊔ M_σ)): UM_σ ◁ M from M = KUM_σ — why is UM_σ normal? (M_σ ◁ M; U normalizes M_σ; K normalizes UM_σ since M' = UM_σ when K≠1, but conjunct 1 has no K≠1 guard — what is the argument when K = 1, i.e. M = UM_σ?)
B. Conjuncts 3,4 (M_σ ⊆ M', M'' ⊆ M_σ): from Thm 10.2(c) and Cor 12.10(b) ((M/M_σ)' abelian ⟹ M'' ⊆ M_σ). Confirm.
C. Conjunct 5 (K≠1 ⟹ M'=UM_σ, U abelian, complement/coprime): from Thm 14.7(d)(h) (M'=UM_σ) + (b)'s U abelian + the κ/κ' Hall complement. Spell out the IsComplement'/coprime part.
D. Conjunct 6 (X cyclic τ₂, 𝓜(C_G(X))={M}): the Cor 14.3 + Cor 12.10(b) (abelian Hall τ₂) + Thm 12.5(d) (C_{M_σ}(A)=1 for A∈ℰ_p²(U)) argument for cyclicity. Make explicit why C_{M_σ}(A)=1 forces X cyclic.
E. Conjuncts 7,8 (d),(e): the reduction to Thm 12.12(d)(e) (proved for K=1) and, for K≠1, U abelian ⟹ (d) trivial, (e) from the "C_E(S)=E" case of Thm 12.12. Make the K≠1 argument explicit (what is U_0?).

Please give the complete rigorous chain for each conjunct, citing the exact result and making every "follows directly"/"obvious" step explicit. Flag any genuine gap. I will verify before formalizing.
