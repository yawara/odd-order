# ChatGPT (Pro 拡張) prompt — BG Corollary 15.5 full proof reconstruction

(Lane G, 2026-06-15. odd-order project. Verify every step before formalizing.)

---

(This odd-order project has the Bender-Glauberman textbook "Local Analysis for the Odd Order Theorem" (LMS LNS 188, 1994) uploaded as a PDF. Please consult it directly — Corollary 15.5, Lemma 15.1, Theorem 15.2, Corollary 15.3, and the σ/τ-partition definitions in Section 12 — to ground and verify your answer.)

I am formalizing BG Corollary 15.5 in Lean 4 and need its proof reconstructed in FULL rigorous detail. The textbook proof is essentially one line ("follow directly from Lemma 15.1(a) ... and from Theorem 15.2(g) and Corollary 15.3(a) ..."), so I need the elided reasoning made explicit.

SETUP. G is a minimal simple group of odd order; proper subgroups are solvable. For a maximal M: σ(M) is a prime set; M_σ is the normal Hall σ(M)-subgroup; M' the derived subgroup; F(M) the Fitting subgroup; M_F the (unique maximal) nilpotent normal Hall subgroup of M. π(M) = σ(M) ⊔ τ₁(M) ⊔ τ₂(M) ⊔ τ₃(M); τ₂(M) = primes p ∉ σ(M) with p-rank r_p(M) = 2. K is the Hall κ(M)-subgroup (M is type P iff κ(M) nonempty, i.e. K ≠ 1).

COROLLARY 15.5 (BG). Let H = M_F and Y = O_{σ(M)'}(F(M)). Then
 (a) Y is a cyclic τ₂(M)-subgroup of F(M);
 (b) M'' ⊆ F(M) = C_M(M_F)·M_F = F(M_σ) × Y;
 (c) M_F ⊆ M' and M'/M_F is nilpotent;
 (d) if K ≠ 1, then F(M) ⊆ M'.

BG proof, verbatim: "Parts (a), (b), and (c) follow directly from Lemma 15.1(a) if H = M_σ and from Theorem 15.2(g) and Corollary 15.3(a) if H ≠ M_σ. If K ≠ 1, then M_σ ⊆ M' and M/M' ≅ K by Lemma 15.1(a) and (b). Since K is a τ₂(M)'-group by definition (see Section 14), M' contains Y. Thus (d) follows."

WHAT I NEED FORMALIZED (the exact Lean conjuncts; please address each):
 1. Y cyclic; π(Y) ⊆ τ₂(M); Y ⊆ F(M).
 2. M'' ⊆ F(M).
 3. F(M) = (C_M(M_F)) · M_F   [as subgroups: F(M) = (C_M(M_F) ⊓ M) ⊔ M_F].
 4. F(M) = F(M_σ) · Y, with F(M_σ) ⊓ Y = 1 and [F(M_σ), Y] = 1 (i.e. internal direct product F(M_σ) × Y).
 5. M_F ⊆ M'.
 6. ¬(M type F) (i.e. K ≠ 1) → F(M) ⊆ M'.
 7. Corollary: M_F cyclic → F(M) cyclic.

MY QUESTIONS.
A. The DECOMPOSITION F(M) = F(M_σ) × Y. F(M) is nilpotent, so F(M) = O_{σ(M)}(F(M)) × O_{σ(M)'}(F(M)) = O_σ(F(M)) × Y. Why is O_σ(F(M)) = F(M_σ)? And why is Y = O_{σ'}(F(M)) cyclic with π(Y) ⊆ τ₂(M) (rather than τ₁/τ₃)? Please give the argument in BOTH cases (H = M_σ, i.e. M_σ nilpotent; and H ≠ M_σ, i.e. M_σ not nilpotent) and say exactly which conjuncts of Lemma 15.1(a) / Theorem 15.2(g) / Corollary 15.3(a) are used.
B. Why F(M) = C_M(M_F)·M_F? (Is this because M_F ⊇ a self-centralizing nilpotent normal subgroup, so C_M(M_F) ⊆ F(M) and F(M) = C_M(M_F)·M_F?)
C. Why M'' ⊆ F(M) and M_F ⊆ M'?
D. For (d): the step "K is a τ₂(M)'-group ⟹ M' ⊇ Y" — please justify (why does M/M' ≅ K being a τ₂'-group force the τ₂-group Y into M').
E. Corollary 7 (M_F cyclic ⟹ F(M) cyclic): from F(M) = F(M_σ) × Y with both factors cyclic and coprime orders — but only when M_σ nilpotent (F(M_σ) = M_σ = M_F); please confirm the argument and the M_σ-not-nilpotent case (where M_F is non-cyclic, making it vacuous).

Please give the complete rigorous chain at the level of detail needed to formalize, citing which earlier BG results are used at each step. I will verify every step before formalizing.
