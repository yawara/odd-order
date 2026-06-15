# ChatGPT prompt — BG Corollary 15.4 elided last step (π(H) ⊆ σ(M))

(Lane G, 2026-06-15. Submitted via Chrome MCP. Verify every step before formalizing.)

---

I am formalizing Bender-Glauberman, "Local Analysis for the Odd Order Theorem" (LMS LNS 188, 1994) in Lean 4. I am stuck on the elided last step of the proof of Corollary 15.4 and need it reconstructed rigorously.

SETUP. G is a minimal simple group of odd order (the Feit-Thompson minimal counterexample); every proper subgroup is solvable. 𝓜 is the set of maximal subgroups and 𝓜(K) the set of maximal subgroups containing K. For M ∈ 𝓜, σ(M) is a set of primes and M_σ is the normal Hall σ(M)-subgroup of M. The primes π(M) dividing |M| are partitioned as σ(M) ⊔ τ₁(M) ⊔ τ₂(M) ⊔ τ₃(M), where (writing r_p for p-rank and M' for the derived subgroup):
  τ₁(M) = { p ∉ σ(M) : p does not divide |M'| and r_p(M) = 1 },
  τ₂(M) = { p ∉ σ(M) : r_p(M) = 2 },
  τ₃(M) = { p ∉ σ(M) : p divides |M'| and r_p(M) = 1 }.
So every prime p ∉ σ(M) has r_p(M) ∈ {1, 2}, and the rank-1 ones split into τ₁ (not in M') and τ₃ (in M').

I MAY CITE Corollary 15.3(a): if H is a nonidentity Hall subgroup of M_σ, then C_M(H) = C_{M_σ}(H) · X, where X is a cyclic τ₂(M)-subgroup.

GOAL (Corollary 15.4): if H is a nonidentity nilpotent Hall subgroup of G, then a maximal subgroup M can be chosen so that H ⊆ M_σ.

BG's proof, verbatim: "Let S be a nonidentity Sylow subgroup of H and M ∈ 𝓜(N_G(S)). Then S ⊆ M_σ and Corollary 15.3(a), applied with S in place of H, shows that M_σ contains every Sylow subgroup of M that lies in C_M(S). Thus H ⊆ M_σ because H is nilpotent."

WHAT I HAVE FORMALIZED. Let p be a prime dividing |H|, S = a Sylow p-subgroup of H, and M ∈ 𝓜(N_G(S)). I proved S ⊆ M_σ (hence p ∈ σ(M)). Since H is nilpotent, H = S × R with R the (normal) Hall p'-subgroup of H, and R ≤ C_H(S) ≤ C_G(S) ≤ N_G(S) ≤ M, so R ≤ C_M(S). Because H is a Hall subgroup of G, for each prime q dividing |H| the Sylow q-subgroup H_q of H is a full Sylow q-subgroup of G, hence a full Sylow q-subgroup of M once H_q ≤ M. For q ≠ p we have H_q ≤ R ≤ C_M(S).

WHERE I AM STUCK. I need: every such H_q is contained in M_σ (equivalently π(H) ⊆ σ(M)). Using Cor 15.3(a) with S: C_M(S) = C_{M_σ}(S) · X with X cyclic τ₂(M). Note C_{M_σ}(S) = C_G(S) ⊓ M_σ is normal in C_M(S) = C_G(S) ⊓ M (since M_σ ◁ M), and C_M(S)/C_{M_σ}(S) is a section of the cyclic τ₂-group X. So:
  - If q ∈ σ(M): H_q (full Sylow q of M, q ∈ σ) lies in the normal Hall σ-subgroup M_σ. Done.
  - If q ∉ σ(M): H_q maps into the cyclic τ₂-quotient C_M(S)/C_{M_σ}(S); if that image were nontrivial then H_q would have a nontrivial cyclic quotient by H_q ⊓ C_{M_σ}(S). I can show: if q ∈ τ₂(M) then r_q(M) = 2, so the full Sylow q-subgroup H_q is non-cyclic, but it would have to embed into the cyclic X — contradiction; hence q ∉ τ₂.
  - BUT I cannot exclude q ∈ τ₁(M) or q ∈ τ₃(M): there r_q(M) = 1, the Sylow q of M is cyclic, q ∉ σ(M), and such an H_q could lie in the "X-direction" of C_M(S), which is NOT contained in M_σ. Then H ⊄ M_σ, contradicting the corollary.

MY QUESTIONS.
1. What is the precise argument that "M_σ contains every Sylow subgroup of M that lies in C_M(S)"? In particular, how are the τ₁(M) and τ₃(M) primes excluded among the q dividing |H| (q ≠ p)?
2. Equivalently: why does a nilpotent Hall subgroup H of G satisfy π(H) ⊆ σ(M) for this particular M ∈ 𝓜(N_G(S))? Which earlier BG results force every prime of H into σ(M)? (Candidates I am aware of: the σ/τ structure of §12, Cor 15.3, Theorem 14.4 / the R(x) structure for elements of σ-length one, Lemma 12.2 "a nonidentity p-subgroup X ≤ M with M* ∈ 𝓜(N_G(X)) has p ∈ σ(M*) ∪ τ₂(M*)".)
3. Please give the complete rigorous chain at the level of detail needed to formalize it, stating exactly which hypotheses (H nilpotent, H Hall of G, the choice of M via S) are used where.

Please be precise about the finite group theory. I will verify every step before formalizing.
