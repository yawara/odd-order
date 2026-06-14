# ChatGPT prompt — elided steps in Bender–Glauberman **Lemma 13.12** (for Lean formalization)

> 用途: Chrome MCP 経由で ChatGPT に投入 (13.10 と同じ §13 chat の follow-up) → 厳密検証 → Lean 化。
> 背景: Lane F /loop。13.7-13.11 完成後、13.12 の formalization-relevant な省略で詰まった。
> 焦点: repo の補題が「E₁ = Hall τ₁-piece」を明示的に要求する点と BG の暗黙の WLOG の整合。

---

This is a follow-up in the same chat as the Theorem 13.10 reconstruction. Same standing
notation (G minimal simple odd; M maximal; M_σ = O_{σ(M)}(M); E a fixed Hall complement to
M_σ in M with Hall τ_i-pieces E₁, E₂, E₃; ℰ_p^k = elementary abelian p-subgroups of order p^k).

I am formalizing **Bender–Glauberman Lemma 13.12** in Lean and need a fully rigorous,
step-by-step reconstruction of the *elided* points below. State exactly which result is used and
verify each hypothesis; I translate line-by-line.

**Lemma 13.12.** Suppose p ∈ τ₁(M), P ∈ ℰ_p¹(E), q ∈ τ₂(M), A ∈ ℰ_q²(E), and C_A(P) ≠ 1.
Then C_{M_σ}(P) = 1.

The book's proof (verbatim): *Suppose C_{M_σ}(P) ≠ 1. Then A ◁ E and P ⊄ C_E(A) by Corollary
12.6(a) and (e). Therefore Y = C_A(P) has order q. By Theorem 13.4, 1 ⊂ C_{M_σ}(P) ⊆ C_{M_σ}(Y).
Therefore, by Corollary 12.6(c), ℳ(C_G(Y)) = {M}. For M\* ∈ ℳ(N_G(A)) we have q ∈ σ(M\*) and
p ∈ τ₁(M\*) ∪ τ₂(M\*) by Lemma 12.11. Suppose p ∈ τ₂(M\*). Then, by Corollary 12.6(c) applied to
M\*, ℳ(C_G(P)) = {M\*} because 1 ⊂ C_A(P) ⊆ C_{M\*_σ}(P). Hence 1 ⊂ C_G(P) ∩ M_σ ⊆ M\* ∩ M_σ,
contrary to Theorem 12.5(e). Thus p ∈ τ₁(M\*). Since Y ∈ ℰ_q¹(C_{M\*_σ}(P)), it follows from
Lemma 13.6 applied to M\* that ℳ(C_G(Y)) = {M\*}, a contradiction.*

The exact forms I have formalized (these pin down where I'm stuck):
- **Cor 12.6(e)** in my repo reads: *every x ∈ C_{E₁}(A) with x ≠ 1 has C_{M_σ}(x) = 1* — note
  it is stated for **E₁** (the Hall τ₁-piece), not for all of C_E(A).
- **Lemma 13.6** in my repo *requires its prime-p subgroup to satisfy P ≤ E₁* (the τ₁-piece):
  signature is (1 ⊂ P ⊆ E₁, q ∈ σ(M), X ∈ ℰ_q¹(C_{M_σ}(P) ⊓ …), S a Sylow q of M_σ) ⟹
  ℳ(C_G(X)) = {M}.
- **Cor 12.6(c)**: for X ∈ ℰ¹(A) with C_{M_σ}(X) ≠ 1, ℳ(C_G(X)) = {M}.
- **Thm 12.5(e)**: for M\* ∈ ℳ(A) with M\* ≠ M, M_σ ∩ M\* = 1.
- **Lemma 12.11**: for M\* ∈ ℳ(N_G(A)): (a) τ₂(M)-primes lie in σ(M\*) − β(M\*); (b) the primes
  of |E / C_E(A)| lie in τ₁(M\*) ∪ τ₂(M\*).
- I can obtain a Hall complement / SubgroupESetup for **any** maximal subgroup, including M\*
  (with the complement chosen to contain a prescribed σ'-subgroup).

**Please reconstruct precisely:**

1. **P ⊄ C_E(A).** The book derives this from 12.6(a),(e). My 12.6(e) is about C_{**E₁**}(A).
   So: is P ∈ ℰ_p¹(E) with p ∈ τ₁(M) **always inside E₁** in this lemma (i.e. should the hypothesis
   really be P ⊆ E₁, or is P conjugate into E₁ without loss)? Give the exact argument: assuming
   C_{M_σ}(P) ≠ 1, why is P ⊄ C_E(A)? (If P ⊆ C_E(A) led to C_{M_σ}(P) = 1, spell out via which
   elements and which form of 12.6(e), and whether P ⊆ E₁ is needed.)

2. **|Y| = q.** Confirm: A ≅ (ℤ/q)², P acts coprimely (p ≠ q), C_A(P) ≠ 1 and P ⊄ C_E(A)
   (so C_A(P) ⊊ A) ⟹ |C_A(P)| = q. State the coprime-action fact used.

3. **Case p ∈ τ₂(M\*) — applying 12.6(c) to M\*.** This needs a p²-elementary-abelian A\* inside
   **M\*'s Hall complement E\*** with P ⊆ A\*. Concretely: (i) why is P inside a Hall complement E\*
   of M\*_σ (rather than inside M\*_σ)? (ii) given p ∈ τ₂(M\*), how do I get A\* ∈ ℰ_p²(E\*) with
   P ⊆ A\* (so that 12.6(c)/M\* applies to the line P)? (iii) then why does ℳ(C_G(P)) = {M\*}
   give 1 ⊂ C_G(P) ∩ M_σ ⊆ M\* ∩ M_σ, and how exactly does Thm 12.5(e) (with M\* ∈ ℳ(A), M\* ≠ M)
   contradict it?

4. **Case p ∈ τ₁(M\*) — applying 13.6 to M\*.** My 13.6 requires **P ⊆ E₁\*** (M\*'s τ₁-piece).
   Since p ∈ τ₁(M\*) and P ∈ ℰ_p¹, is P ⊆ E₁\* automatic (choose E\* ⊇ P, then the τ₁-line P lands
   in the Hall τ₁-piece) or conjugate-into-E₁\*? Give the precise justification, and confirm
   Y ∈ ℰ_q¹(C_{M\*_σ}(P)) with q ∈ σ(M\*) so that 13.6/M\* yields ℳ(C_G(Y)) = {M\*}, contradicting
   ℳ(C_G(Y)) = {M}.

For each WLOG / "P lies in E₁"-type step, state whether it is a genuine conjugation WLOG (and by
what — Hall conjugacy in E or in M\*) or whether 13.12 is only ever invoked with P ⊆ E₁ already.
Be explicit and name every result used.
