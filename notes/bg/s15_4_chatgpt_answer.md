# ChatGPT (Pro 拡張) answer — BG Cor 15.4 elided last step

(Lane G, 2026-06-15. odd-order project, thinking 8m52s. **Verified rigorous** before formalizing.)

## Resolution of the gap (my error corrected)

My obstruction ("q ∈ τ₁/τ₃ could let H_q sit in the X-direction") was **wrong**. The key fact I
underused: in Cor 15.3(a), `X` is not a general σ(M)′-complement — it is a **cyclic τ₂(M)-subgroup**.

So with `L = S` (a Hall {p}-subgroup of M_σ), `A := C_{M_σ}(S) = C_G(S) ⊓ M_σ`:
- `A ⊴ C_M(S)` (since `M_σ ⊴ M`).
- `C_M(S) = A·X` (Cor 15.3a) ⟹ `C_M(S)/A ≅ X/(X∩A)` is **cyclic and a τ₂(M)-group**
  (its order is a τ₂-number).

**Key lemma** ("M_σ contains every Sylow of M lying in C_M(S)"). Let `Q` be a Sylow `q`-subgroup of
`M` with `Q ≤ C_M(S)`. Then `Q ≤ M_σ`:
- `q ∈ σ(M)`: immediate — `M_σ` is the normal Hall σ(M)-subgroup, contains every σ-Sylow of M.
- `q ∉ σ(M)`: `A ≤ M_σ` is a σ-group ⟹ `Q ∩ A = 1` ⟹ the quotient map embeds `Q ↪ C_M(S)/A`
  (a cyclic τ₂-group). Then `q ∣ |C_M(S)/A|`, a τ₂-number, so `q ∈ τ₂(M)`.
  - If `q ∈ τ₁ ∪ τ₃`: impossible — a nontrivial `q`-group cannot embed into a τ₂-group
    (`q ∉ τ₂`, disjoint prime sets). **This is exactly where τ₁/τ₃ are excluded.**
  - If `q ∈ τ₂`: the embedding forces `Q` cyclic; but `q ∈ τ₂ ⟹ r_q(M) = 2 ⟹` the full Sylow
    `q`-subgroup of M is non-cyclic. **Contradiction.**
  - Hence `q ∉ σ(M)` is impossible, so `q ∈ σ(M)`, giving `Q ≤ M_σ`.

**No hidden use of Theorem 14.4 or R(x).** Ingredients = def of σ(M), the §12 σ/τ-partition,
`M_σ` normal Hall σ(M)-subgroup, and Cor 15.3(a). (Lemma 12.2 is background only.)

## Full Cor 15.4 proof (reconstructed)

`H` nonidentity nilpotent Hall subgroup of `G`.
1. Pick `p ∈ π(H)`, `S ∈ Syl_p(H)`, `M ∈ ℳ(N_G(S))`.
2. `H` Hall of `G` ⟹ `S` is a full Sylow `p` of `G`; `N_G(S) ≤ M` ⟹ `S` Sylow `p` of `M`,
   `p ∈ σ(M)`, `S ≤ M_σ`.  **[= our `sylow_le_Msigma_of_normalizer_le`]**
3. For each `q ∈ π(H)`, `H_q ∈ Syl_q(H)`:
   - `q = p`: `H_q = S ≤ M_σ`.
   - `q ≠ p`: nilpotence ⟹ `[H_q, S] = 1` (Sylows of nilpotent group are normal; normal subgroups
     of coprime order commute) ⟹ `H_q ≤ C_H(S) ≤ C_G(S) ≤ N_G(S) ≤ M`. `H` Hall ⟹ `H_q` full
     Sylow `q` of `G`, hence of `M`; and `H_q ≤ C_M(S)`. **Key lemma ⟹ `H_q ≤ M_σ`.**
4. `H` nilpotent ⟹ `H` is the product of its Sylow subgroups ⟹ `H ≤ M_σ`.
   **[= our `eq_top_of_forall_sylow_le` applied inside ↥H, or: every Sylow of ↥H ≤ M_σ.subgroupOf H]**

## Formalization plan (Lean)

- Cite `mf_hall_centralizer_control` (Cor 15.3a, sorried) for `C_M(S) = C_{M_σ}(S) ⊔ X`,
  `X` cyclic, `π(X) ⊆ τ₂ M`.
- New leaf lemma `sylow_le_Msigma_of_le_centralizer_sylow` (the **Key lemma**): `Q` Sylow `q` of `M`,
  `Q ≤ C_M(S) ⊓ M`, using Cor 15.3a + `Q ∩ M_σ = 1` (coprime) + embed into cyclic τ₂ quotient.
  Friction: build `C_M(S)/C_{M_σ}(S)` is a τ₂-group; `Q ↪` it; rank-2 vs cyclic.
- Nilpotent facts: `IsNilpotent ↥H` ⟹ Sylows normal (`isNilpotent_iff_forall_sylow_normal`),
  coprime normal commute, `H_q ≤ C_H(S)`.
- Assembly: steps 1-4 with our two helpers. Subtype juggling for Sylow-of-↥H ↔ Sylow-of-G.
- ⟹ `nilpotent_hall_embeds_in_msigma` sorry-free, depending only on sorried Cor 15.3a.
