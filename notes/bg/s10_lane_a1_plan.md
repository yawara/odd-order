# Lane A1 (S10_LocalLemmas) 実行プラン (2026-06-07)

worktree `/home/ywr/odd-order-bg-s10-leaves`, branch `bg-s10-leaves`, `ODD_ISSUE_BASE=2000`。
対象 = `OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmas.lean` の 7 sorry。

## ⚠ 依存の実態 (BG 原文を読んで判明 — 当初の docstring ベース map は楽観的すぎた)

| leaf | BG# | 実依存 | A1 で独立に可? |
|---|---|---|---|
| `sigma_complement_rank_le_one` | 10.11(a)(b)(c) | (a) Thm 4.20+base; **(b) Prop 10.10 (spine!)**; (c)←(b) | ✗ (b)(c) が spine 待ち |
| `sigma_complement_commutator_cyclic_normal` | 10.11(d) | **Thm 3.7** + (c) + coprime 分解 | △ (c) 経由で spine、ただし下記参照 |
| `disjoint_of_not_conj` | 10.12 | Uniqueness Thm (§9, 証明済) | ○ だが **MISSING_PAGE (PDF p.92)** 要読込 |
| `centralizer_isUniquelyMaximal_of_two_le_rank` | 10.3 | Uniqueness | **MISSING_PAGE (p.87)** |
| `pRank_eq_two_of_normalizer_le` | 10.5 | §7 Prop 7.5 等 | **MISSING_PAGE (p.87)** |
| `alpha_criterion` | 10.4(a)(c) | (a) def+§4; (c) Thm 5.3/ideal | **MISSING_PAGE (p.87)** |
| `nonabelian_pSubgroup_rankTwo_elemAbelian_structure` | 10.13 | p-群構造 | **MISSING_PAGE (p.79)**, 末尾のみ mmd L2890 |

**教訓**: §10 leaf は spine (Prop 10.10/Cor 10.7) と絡む or MISSING_PAGE。当初の「6-7 完全独立」は誤り。

## 最良ターゲット: 10.11(d) `sigma_complement_commutator_cyclic_normal` (Thm 3.7 シナジー)

BG 原文 (L2856 proof (d)): 「K₀=[K,P], K=K₀×C_K(P) (K abelian p'-group), P が K₀M_σ に作用し
C_{K₀M_σ}(P)=C_{K₀}(P)C_{M_σ}(P)=1。**∴ Theorem 3.7 で K₀M_σ nilpotent**。ゆえに K₀ は M_σ を
中心化し、(c) より K₀ は M の cyclic normal 部分群」。

### Lean 実装レシピ (推定 ~120-150 行)
1. **coprime 分解** `K = C_K(P) × [K,P]`: `OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp`
   (P:=K abelian, K:=P acting; `hK_norm` = P ≤ N(K) from `hPN`; coprime = |P|=p ∤ |K| (K is p'));
   返り値 `(C_K(P) ⊓ K) ⊓ ⁅K,P⁆ = ⊥ ∧ (C_K(P)⊓K) ⊔ ⁅K,P⁆ = K`。
2. **K₀:=⁅K,P⁆ の基本性質**: ≤K (P normalizes K), ≤M', p'-group, abelian (≤K)。
   `C_{K₀}(P) = K₀ ⊓ C_K(P) = ⊥` (decomp の交わり)。
3. **N:=K₀ ⊔ M_σ の FPF**: `C_N(P)=⊥`。coprime action で C of product = product of C's
   (`C_{K₀}(P)=⊥` + `C_{M_σ}(P)=⊥` from `hCP`)。要: P normalizes N (P≤M≤N(M_σ), P normalizes K₀),
   disjoint(N,P) (N is p', P is p), |P|=p prime (`hP : P∈ℰ_p¹` → card=p), IsSolvable ↥N (≤M proper)。
4. **Thm 3.7 適用**: `OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree`
   (N:=K₀M_σ, R:=P) → `Group.IsNilpotent ↥(K₀ ⊔ M_σ)`。
5. **K₀ centralizes M_σ** (infra 全て特定済・未知ゼロ): nilpotent K₀M_σ で K₀ (σ' Hall) と
   M_σ (σ Hall) は coprime。M_σ ⊴ N は自明 (M_σ⊴M⊇N)。K₀ ⊴ N は nilpotent から:
   `OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent` (各 Sylow 正規) → σ'-Sylow 積 = K₀ 正規、
   or `Sylow.directProductOfNormal` (nilpotent → Sylow 直積) で σ'-Hall=K₀ を取り出す。
   両正規 + disjoint (K₀⊓M_σ=⊥, coprime order) →
   `Subgroup.commute_of_normal_of_disjoint` で `⁅K₀,M_σ⁆=⊥` (or `commutator_le_inf` で
   ⁅K₀,M_σ⁆≤K₀⊓M_σ=⊥)。⇒ K₀ ≤ C_G(M_σ)。
6. **cyclic normal**: `sigma_complement_rank_le_one hG hM hKM hKpi` の (c) (= `C_K(M_σ)⊓M'` cyclic
   normal Z) を cite。K₀ ≤ C_K(M_σ) (step5) ∧ K₀ ≤ M' → K₀ ≤ Z。subgroup of cyclic = cyclic;
   cyclic の subgroup は characteristic → Z⊴M ⇒ K₀⊴M。
   ⇒ **10.11(d) は 10.11(c) + Thm 3.7 に還元** (c が landing すれば完全 discharge)。

### 注意
- `sigma_complement_rank_le_one` (c) を cite する = (d) 本体は sorry-free だが推移的に (c)=sorry に依存。
  これは正当な還元 (scaffold-sorry-free ≠ proved の原則下、(d)→(c)+Thm3.7 の reduction は実内容)。
- step 5 の nilpotent-Hall-normal が mathlib に無ければ自作 (中規模)。ここが最大の未知。

## MISSING_PAGE 系 (10.3/10.4/10.5/10.12/10.13)
PDF `references/bg/local-analysis.pdf` の該当ページを `Read pages=N` で読込 (book p.87/p.92/p.79;
PDF page offset 要校正)。10.12 は Cor 11.4 を解除する高価値だが Uniqueness 経由の本格証明。

## 推奨着手順
1. 10.11(d) (Thm 3.7 シナジー, infra 既存) ← step5 の nilpotent-Hall だけ確認すれば最短
2. 10.12 (PDF 読込 → Uniqueness 証明, 高価値)
3. 残 MISSING_PAGE は PDF 読込後
