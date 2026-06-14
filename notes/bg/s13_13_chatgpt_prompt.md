# ChatGPT prompt — elided steps in BG Lemma 13.13 (Lean formalization)

> 用途: Chrome MCP で §13 chat の follow-up に投入 (B method, backtick-free) → 検証 → Lean 化。
> 背景: 13.12 完成後、13.13 (最後の §13 lemma) の省略 (P∈E₁/E₃ WLOG, E\*⊇PQ) で要再構成。

---

This is a follow-up in the same chat (Theorem 13.10 / Lemma 13.12 reconstructions). Same standing
notation (G minimal simple odd; M maximal; M_σ = O_{σ(M)}(M); E a fixed Hall complement to M_σ in
M with Hall τ_i-pieces E₁, E₂, E₃; ℰ_p^k = elementary abelian p-subgroups of order p^k). I just
finished formalizing Lemma 13.12; now I need Lemma 13.13.

**Lemma 13.13.** Suppose p ∈ τ₁(M) ∪ τ₃(M), P ∈ ℰ_p¹(E), and C_{M_σ}(P) ≠ 1. Then for every
M* ∈ ℳ(N_G(P)) we have p ∈ σ(M*).

Book's proof (verbatim): *By Lemma 12.2, p ∈ σ(M*) ∪ τ₂(M*). Suppose p ∈ τ₂(M*). We will obtain a
contradiction. Choose q ∈ π(C_{M_σ}(P)) and Q ∈ ℰ_q¹(C_{M_σ}(P)). By Theorem 13.9, q ∉ σ(M*). Let
E* be a complement of M*_σ in M* that contains PQ. Take A ∈ ℰ_p²(E*). By Corollary 12.6(a), A ◁ E*
and P ⊆ A. We can assume that P lies in E₁ or in E₃. If P ⊆ E₃, then parts (a) and (c) of
Corollary 13.11 show that E₁ ≠ 1 and C_{M_σ}(P) = C_{M_σ}(E₁) because 1 ⊂ Q ⊆ C_{M_σ}(P). Therefore,
in any case, we have C_G(Q) ⊆ M by Lemma 13.6, and this implies that A ⊄ C_{E*}(Q) because
r_p(M) = 1. Therefore, by Corollary 12.10(c), q ∈ τ₁(M*) and P = C_A(Q). Consequently, by Lemma
13.12 applied to M*, C_{M*_σ}(Q) = 1, and Corollary 12.9(c) then yields N_G(P) ⊄ M*, contradicting
M* ∈ ℳ(N_G(P)).*

Repo forms (where the elisions bite for Lean):
- **Lemma 13.6** (mine) requires its prime subgroup P' to satisfy 1 ⊂ P' ⊆ E₁ (the τ₁-Hall piece),
  q ∈ σ(M), X ∈ ℰ_q¹(C_{M_σ}(P')); conclusion ℳ(C_G(X)) = {M}.
- **Cor 13.11** (just proved): E₃ ≠ 1 and E₃ not regular on M_σ ⟹ (a) E₁ ≠ 1; (b) E = E₁E₃;
  (c) E prime on M_σ; (d) every prime-order X ≤ E is normal in E.
- **Cor 12.10(c)**: (need exact hypotheses) yields q ∈ τ₁(M*) and P = C_A(Q) in the configuration above.
- **Cor 12.9(c)**: (need exact hypotheses) yields N_G(P) ⊄ M*.
- **Theorem 13.9**: M* ∈ ℳ not conjugate to M ⟹ σ(M) ∩ σ(M*) = ∅ (used to get q ∉ σ(M*)).
- **Lemma 12.2(b)**: for p ∈ τ₁(M) ∪ τ₃(M), nonidentity p-subgroup X, M* ∈ ℳ(N_G(X)) ⟹
  p ∈ σ(M*) ∪ τ₂(M*) and M* not conjugate to M.
- I can build a SubgroupESetup for M* with its M*_σ-complement E* chosen to contain a prescribed
  σ(M*)'-subgroup (so E* ⊇ P; can I also force E* ⊇ Q, i.e. E* ⊇ PQ?).

Please reconstruct precisely, naming each result and verifying its hypotheses:

1. **"We can assume P lies in E₁ or in E₃."** Is this a case split on p ∈ τ₁(M) vs p ∈ τ₃(M) with
   P conjugated (Hall conjugacy in E) into E₁ resp. E₃? Give the exact mechanism. In particular, for
   the eventual application of Lemma 13.6 (which needs the prime subgroup inside E₁), what subgroup
   plays the role of "P' ⊆ E₁"?

2. **The p ∈ τ₃ branch via Cor 13.11.** Spell out: why does P ⊆ E₃ let us invoke 13.11(a),(c)?
   (We need E₃ ≠ 1 and E₃ not regular on M_σ to even apply 13.11 — where do those come from? Note
   1 ⊂ Q ⊆ C_{M_σ}(P) shows C_{M_σ}(P) ≠ 1; how does that give E₃ non-regular on M_σ?) Then how does
   C_{M_σ}(P) = C_{M_σ}(E₁) let us apply Lemma 13.6 with an E₁-line P' so that Q ∈ ℰ_q¹(C_{M_σ}(P'))
   and conclude C_G(Q) ⊆ M? (And in the p ∈ τ₁ branch, P itself is the E₁-line.)

3. **E* ⊇ PQ.** Why can the M*_σ-complement E* be chosen to contain both P and Q? (P is a
   σ(M*)'-subgroup since... ; Q is a q-subgroup with q ∉ σ(M*) by Thm 13.9, so Q is also σ(M*)'; and
   PQ is a {p,q}-subgroup — is it abelian / is PQ a σ(M*)'-subgroup so Hall's theorem places it in a
   complement E*?) Confirm P, Q commute (both ≤ C_{M_σ}(P)? no — P need not centralize itself's
   centralizer; clarify whether Q ≤ C_G(P) so PQ is a subgroup of order pq).

4. **A ⊄ C_{E*}(Q) from C_G(Q) ⊆ M and r_p(M) = 1.** Spell out: A ∈ ℰ_p²(E*) with P ⊆ A; if
   A ⊆ C_{E*}(Q) then A ⊆ C_G(Q) ⊆ M, giving a rank-2 elementary abelian p-subgroup of M, contra
   r_p(M) = 1 (since p ∈ τ₁ ∪ τ₃ ⟹ r_p(M) = 1). Confirm this is the argument.

5. **Cor 12.10(c) and Cor 12.9(c).** State the exact hypotheses each needs in this configuration
   (q ∈ τ₂(M*)? p ∈ ? , A ∈ ℰ_p²(E*), Q, A ⊄ C_{E*}(Q), …) and how they yield, respectively,
   "q ∈ τ₁(M*) and P = C_A(Q)" and "N_G(P) ⊄ M*". Then the final contradiction with M* ∈ ℳ(N_G(P)).

For each WLOG / conjugation step say whether it is genuine Hall conjugacy (in E or in M*) and what
exactly is conjugated. Be explicit and name every result.
